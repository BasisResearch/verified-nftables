(** * Semantics: the meaning of both languages as packet -> verdict.

    Both the declarative DSL and the bytecode are given the *same* observable
    semantics — a function from a packet to the verdict the base chain produces —
    so "semantics preserving" is a literal equality of these functions. *)

From Stdlib Require Import List NArith Bool Lia.
From Nft Require Import Bytes Packet Verdict Syntax Bytecode.
Import ListNotations.
(* [String] is left UNimported (it shadows List's [concat]/[length]); the chain
   environment uses the qualified [String.string] / [String.eqb]. *)

(** ** Declarative semantics. *)

Definition apply_transform (t : transform) (d : data) : data :=
  match t with
  | TBitAnd mask xor    => data_bitops d mask xor
  | TShift shl amt     => data_shift shl amt d
  | TByteorder h sz len => data_byteorder h sz len d
  | TJhash l s m o      => data_jhash l s m o d
  end.

Definition apply_transforms (ts : list transform) (d : data) : data :=
  fold_left (fun acc t => apply_transform t acc) ts d.

(** ** SYN-proxy.

    A `synproxy` statement is NOT verdict-neutral.  The kernel
    (net/netfilter/nft_synproxy.c, nft_synproxy_do_eval / nft_synproxy_eval_v4):

      - a NON-TCP packet sets the verdict to NFT_BREAK (line 117): the rule does
        NOT apply — exactly the behaviour of a transport-base payload load on a
        packet without an L4 header.  We therefore tie synproxy's applicability to
        the loadability of the TCP-flags byte (a [PTransport] load): a non-TCP /
        non-L4 / fragmented packet makes it unloadable, so the rule is skipped.

      - a TCP packet whose SYN or ACK flag is set is the packet synproxy is
        written to catch: the kernel STOPS chain traversal here — NF_STOLEN for a
        SYN (line 61: the SYN is answered with a syncookie SYN+ACK and consumed) or
        a valid 3WHS ACK (line 67), NF_DROP for a rejected ACK / bad checksum /
        unparseable header (lines 69/122/130/135).  Every one of these STOPS
        traversal and discards the packet from this hook's decision; the official
        docs corroborate (doc/statements.txt:55: "reject and synproxy internally
        issue a drop verdict at the end of their respective actions").  We model
        this control-flow outcome — the packet never reaches the chain policy or a
        later rule — as the terminal verdict [Drop] (the syncookie/seq side effect
        of STOLEN is below the model's single-packet resolution, exactly as
        Reject's ICMP and Queue's hand-off are).

      - a TCP packet with neither SYN nor ACK (e.g. a bare RST) leaves the verdict
        untouched: an implicit NFT_CONTINUE.  We model this as a transparent
        fall-through (the rule applies but contributes no verdict).

    [synproxy_flags] reads the 1-byte TCP-flags field (transport offset 13, where
    [Syntax.FTcpFlags] reads); [synproxy_stops] is the SYN|ACK (= 0x12) test that
    decides "terminal stop" vs "continue". *)
Definition synproxy_flags (p : packet) : data := read_payload PTransport 13 1 p.

(** Whether a synproxy statement's TCP-flags load succeeds (i.e. the packet has a
    parsed, non-fragmented TCP header).  A failure is the kernel's NFT_BREAK for a
    non-TCP packet: the rule does not apply. *)
Definition synproxy_loadable (p : packet) : bool := read_payload_ok PTransport 13 1 p.

(** Whether synproxy STOPS chain traversal on this packet: true iff a SYN or ACK
    flag is set (0x02 | 0x10 = 0x12). *)
Definition synproxy_stops (p : packet) : bool :=
  match synproxy_flags p with
  | b :: _ => negb (Nat.eqb (Nat.land b 18) 0)
  | [] => false
  end.

(** Whether every field in a list is loadable on a packet. *)
Definition fields_loadable (fs : list field) (p : packet) : bool :=
  forallb (fun f => field_loadable f p) fs.

(** Whether all the fields a match condition reads are loadable.  A match whose
    load BREAKs (a too-short / fragmented / no-L4 transport header) does NOT
    apply — the rule is skipped — so the match must evaluate to [false]
    regardless of any negation.  This is the soundness fix: a failed load can
    never make a negated condition spuriously true. *)
Definition match_loadable (m : matchcond) (p : packet) : bool :=
  match m with
  | MEq  f _ | MNeq f _ | MRange f _ _ _ | MMasked f _ _ _ _
  | MCmp f _ _ | MTransform f _ _ _ | MSetT f _ _ _ | MRangeT f _ _ _ _ =>
      field_loadable f p
  | MConcatSet fields _ _ => fields_loadable fields p
  | MConcatSetT elems _ _ => fields_loadable (map fst elems) p
  | MLimit _ | MQuota _ | MConnlimit _ => true
  end.

(** ** The rate-limiter token bucket (kernel net/netfilter/nft_limit.c).

    The kernel limiter is a genuine time-based token bucket.  At load time
    (nft_limit_init) it precomputes, from the configured rate / unit / burst:
      nsecs       = unit * NSEC_PER_SEC          (the time window in ns)
      cost (pkts) = nsecs / rate                 (ns "charged" per packet)
      cost (bytes)= nsecs * skb->len / rate      (ns charged per byte of the skb)
      tokens_max  = (nsecs / rate) * burst                         (packet mode)
                  = nsecs * (rate + burst) / rate                  (byte mode)
    and at run time (nft_limit_eval):
      tokens = stored + (now - last)             (REFILL by elapsed wall-clock)
      tokens = min(tokens, tokens_max)           (cap at the burst-derived max)
      delta  = tokens - cost
      delta >= 0  ->  store delta, PASS  (return invert)
      delta <  0  ->  store tokens, FAIL (return !invert)

    We model the bucket TOKEN STATE in [e_limit] (a [nat], in the kernel's ns
    unit, but with the common NSEC_PER_SEC factor RESCALED OUT — it divides both
    the cost and the cap and the elapsed term identically, so the pass predicate
    [cost <= min(stored,max)] is unchanged by the rescaling, and the numbers stay
    in [nat] range).  Elapsed wall-clock time is abstracted to +0 WITHIN one
    traversal (back-to-back packets in one ktime), exactly as documented for the
    consuming-bucket model; what this fix adds is that the per-packet COST and the
    bucket CAP are now genuine functions of [ls_rate]/[ls_unit]/[ls_burst] (and,
    in byte mode, the packet length), so distinct rates give distinct verdicts and
    the parameters are no longer inert.

    [ls_unit] is the DSL unit ENUM (0=second 1=minute 2=hour 3=day 4=week, the
    parser's encoding), which [lim_window] converts to the kernel's window length
    in SECONDS (second=1, minute=60, hour=3600, day=86400, week=604800) — i.e. the
    kernel's [nsecs = unit*NSEC_PER_SEC] with the common NSEC_PER_SEC factor
    RESCALED to [lim_SCALE] (so 1/minute genuinely costs 60x a 1/second packet but
    the numbers stay tractable in unary [nat]).  [lim_SCALE] divides cost AND cap
    AND the (abstracted) elapsed refill identically, so the pass predicate
    [cost <= min(stored,max)] is unchanged by it; it is kept at 1 here (the time
    granularity is one unit-window — a per-second-or-coarser bucket — consistent
    with the elapsed-time-refill abstraction; a rate finer than the window's
    second count shares a token within the window).  The essential fix is that the
    per-packet COST and the bucket CAP are now genuine functions of
    [ls_rate]/[ls_unit]/[ls_burst] (and the packet length in byte mode), so e.g.
    1/second, 1/minute and 1/hour give DIFFERENT verdicts at the same bucket
    level — the parameters are no longer inert. *)
Definition lim_SCALE : nat := 1.
Definition lim_unit_secs (u : nat) : nat :=
  match u with
  | 0 => 1 | 1 => 60 | 2 => 3600 | 3 => 86400 | _ => 604800
  end.
Definition lim_window (spec : limit_spec) : nat :=
  lim_unit_secs (ls_unit spec) * lim_SCALE.

(** The rate, guaranteed positive (nft_limit_init rejects rate == 0). *)
Definition lim_rate (spec : limit_spec) : nat := Nat.max 1 (ls_rate spec).

(** Per-evaluation cost charged to the bucket: [window/rate] in packet mode,
    [window * len / rate] in byte mode (len = the packet's [meta len]).  Mirrors
    nft_limit_pkts_eval (priv->cost = div64_u64(nsecs, rate)) and
    nft_limit_bytes_eval (cost = div64_u64(nsecs * skb->len, rate)). *)
Definition lim_cost (p : packet) (spec : limit_spec) : nat :=
  let r := lim_rate spec in
  if ls_bytes spec
  then Nat.div (lim_window spec * N.to_nat (data_to_N (pkt_meta p MKlen))) r
  else Nat.div (lim_window spec) r.

(** The bucket capacity (tokens_max).  Packet mode: [(window/rate) * burst];
    byte mode: [window * (rate + burst) / rate].  Mirrors nft_limit_init. *)
Definition lim_max (spec : limit_spec) : nat :=
  let r := lim_rate spec in
  if ls_bytes spec
  then Nat.div (lim_window spec * (r + ls_burst spec)) r
  else Nat.div (lim_window spec) r * ls_burst spec.

(** The token count available to THIS evaluation: the stored bucket [e_limit]
    capped at [lim_max] (elapsed-time refill abstracted to +0 in a traversal). *)
Definition lim_avail (p : packet) (spec : limit_spec) : nat :=
  Nat.min (e_limit (pkt_env p) spec) (lim_max spec).

(** The non-inverted "under / not exceeded" test: PASS iff the available tokens
    cover the cost ([delta = tokens - cost >= 0]).  This is the value nft_limit_eval
    returns BEFORE XOR-ing the invert bit. *)
Definition lim_under (p : packet) (spec : limit_spec) : bool :=
  Nat.leb (lim_cost p spec) (lim_avail p spec).

(** Per-evaluation byte cost charged to a `quota`: the packet's [meta len], i.e.
    the kernel's [skb->len] (nft_overquota: [consumed += skb->len]).  This is the
    same length expression that byte-mode [lim_cost] uses. *)
Definition quota_cost (p : packet) : nat :=
  N.to_nat (data_to_N (pkt_meta p MKlen)).

(** The non-inverted "under / not over quota" test.  With [e_quota] tracking the
    REMAINING bytes ([quota - consumed]), the kernel's post-add state is
    [consumed' = consumed + skb->len] and it BREAKs iff [consumed' > quota].  In
    remaining terms that is PASS iff [consumed + cost <= quota], i.e. iff
    [cost <= remaining] — a packet landing exactly on the quota still passes.
    Mirrors [lim_under]'s [Nat.leb cost avail]. *)
Definition quota_under (p : packet) (spec : quota_spec) : bool :=
  Nat.leb (quota_cost p) (e_quota (pkt_env p) spec).

(** The list of distinct connection flow-ids counted for a `connlimit` instance
    AFTER (idempotently) accounting for the current packet's connection
    [pkt_flow p].  Mirrors the kernel nft_connlimit_do_eval:
    [nf_conncount_add_skb] adds the skb's connection tuple to [priv->list], but
    returns -EEXIST (and does NOT grow the list) when the connection is already
    counted.  So re-adding an existing flow is a no-op (dedup), and the resulting
    [count = priv->list->count] is the number of DISTINCT live connections. *)
Definition connlimit_after (e : env) (spec : connlimit_spec) (flow : data) : list data :=
  if data_mem flow (e_connlimit e spec) then e_connlimit e spec
  else flow :: e_connlimit e spec.

(** The connection COUNT a `connlimit` reads = number of distinct flows after the
    idempotent insert (kernel [count = READ_ONCE(priv->list->count)]). *)
Definition connlimit_count (p : packet) (spec : connlimit_spec) : nat :=
  List.length (connlimit_after (pkt_env p) spec (pkt_flow p)).

(** The non-inverted "under / not over the connection limit" test.  The kernel
    BREAKs iff [(count > limit) ^ invert] (nft_connlimit.c:47, STRICT >), so the
    non-inverted PASS test is [count <= limit], i.e. [negb (limit < count)].
    Because a packet of an ALREADY-counted connection does not grow [count], ANY
    number of packets of ONE connection read the SAME count and a `connlimit N`
    with [N >= 1] never throttles a single connection; and [count <= N] permits up
    to N+1 distinct connections (count breaks only at N+1 > N). *)
Definition connlimit_under (p : packet) (spec : connlimit_spec) : bool :=
  negb (Nat.ltb (cl_count spec) (connlimit_count p spec)).

(** The unguarded comparison body of a match (the original semantics). *)
Definition eval_matchcond_body (m : matchcond) (p : packet) : bool :=
  match m with
  | MEq  f v => data_eqb (List.firstn (List.length v) (field_value f p)) v
  | MNeq f v => negb (data_eqb (List.firstn (List.length v) (field_value f p)) v)
  | MRange f neg lo hi =>
      eval_range (if neg then CNe else CEq) (field_value f p) lo hi
  | MMasked f neg mask xor v =>
      eval_cmp (if neg then CNe else CEq) (data_bitops (field_value f p) mask xor) v
  | MCmp f op v => eval_cmp op (field_value f p) v
  | MConcatSet fields neg name =>
      (* membership of the concatenated key in the *named* set, whose contents are
         read from the runtime environment [pkt_env p], not inlined in the rule.
         A concatenated set is NFT_SET_CONCAT: the kernel matches EACH FIELD
         against its OWN [lo,hi] independently (the set is the cross-product of
         the per-field intervals, NOT one flat lexicographic interval over the
         concatenation).  So we pass the per-field value list to
         [concat_set_mem], which splits each stored element's bound by the
         per-field widths and tests every field separately.  For a single field
         this coincides with the old flat [set_mem] ([concat_set_mem_single]). *)
      xorb neg (concat_set_mem (map (fun f => field_value f p) fields)
                         (e_set (pkt_env p) name))
  | MTransform f ts op v =>
      eval_cmp op (apply_transforms ts (field_value f p)) v
  | MSetT f ts neg name =>
      xorb neg (set_mem (apply_transforms ts (field_value f p))
                         (e_set (pkt_env p) name))
  | MRangeT f ts neg lo hi =>
      eval_range (if neg then CNe else CEq) (apply_transforms ts (field_value f p)) lo hi
  (* Each limiter carries an "over"/invert bit (bit 0 of its flags field).  The
     kernel XORs the under/not-exceeded test with that bit:
       nft_limit.c:48,52  (returns [invert] when tokens remain, [!invert] when
                           exhausted; the caller BREAKs on a true return),
       nft_quota.c:43     [if (nft_overquota(...) ^ nft_quota_invert(priv)) BREAK],
       nft_connlimit.c:47 [if ((count > limit) ^ priv->invert) BREAK].
     Our underlying oracle ([0 < remaining]) is the non-inverted "under" test
     (match iff NOT exceeded); the over-bit flips it so an inverted limiter
     matches iff the resource is EXCEEDED. *)
  | MLimit spec =>
      xorb (Nat.eqb (Nat.land (ls_flags spec) 1) 1) (lim_under p spec)
  | MQuota spec =>
      xorb (Nat.eqb (Nat.land (q_flags spec) 1) 1) (quota_under p spec)
  | MConnlimit spec =>
      xorb (Nat.eqb (Nat.land (cl_flags spec) 1) 1) (connlimit_under p spec)
  | MConcatSetT elems neg name =>
      (* like [MConcatSet] but each element is transformed before concatenation;
         contents read from the named set in [pkt_env p].  Per-field membership
         (cross-product of per-field intervals), as for [MConcatSet]. *)
      xorb neg (concat_set_mem
        (map (fun fe => apply_transforms (snd fe) (field_value (fst fe) p)) elems)
        (e_set (pkt_env p) name))
  end.

(** A match condition: [false] (does not apply) if its load breaks, else the
    ordinary comparison. *)
Definition eval_matchcond (m : matchcond) (p : packet) : bool :=
  andb (match_loadable m p) (eval_matchcond_body m p).

(** A `notrack` statement: force this packet's conntrack state to IP_CT_UNTRACKED for
    the rest of its traversal, so a LATER `ct state` read returns
    NF_CT_STATE_UNTRACKED_BIT (handled in [Syntax.do_load]'s [LCt CKstate] case).
    Mirrors the kernel nft_notrack_eval (net/netfilter/nft_ct.c):

      ct = nf_ct_get(pkt->skb, &ctinfo);
      // Previously seen (loopback or untracked)?  Ignore.
      if (ct || ctinfo == IP_CT_UNTRACKED)
          return;                            // <-- NO-OP when an entry exists
      nf_ct_set(skb, ct, IP_CT_UNTRACKED);

    The kernel only latches IP_CT_UNTRACKED when there is NO conntrack entry yet
    (ct == NULL).  On a packet that ALREADY has an entry ([pkt_ct_present = true],
    e.g. an ESTABLISHED flow), `notrack` does NOTHING: a later `ct state` read sees
    the entry's REAL state, not the UNTRACKED bit.  We mirror this by leaving the
    packet UNCHANGED when [pkt_ct_present p = true].  Only when there is no entry
    ([pkt_ct_present = false]) does [pkt_untracked] flip to [true]; every other
    packet component — including the per-packet [pkt_ct] oracle and the shared env —
    is preserved, so that a `ct mark`/other-key read is unaffected.  This is the
    per-packet-traversal state both the DSL ([body_writes]/[rule_applies_walk]) and
    the VM ([run_rule_writes]/[run_rule]) apply on [SNotrack]/[INotrack], keeping the
    two in lock-step. *)
Definition set_untracked (p : packet) : packet :=
  if pkt_ct_present p then p
  else with_pkt_untracked p true.

(** Update the SHARED `numgen inc` counter [e_numgen] for instance [spec]: INCREMENT
    it by one, leaving every other instance's counter — and every other env
    component — unchanged.  Mirrors the kernel's atomic_cmpxchg advancing the
    instance's [atomic_t *counter] by one per evaluation (nft_ng_inc_gen). *)
Definition env_numgen_upd (e : env) (spec : numgen_spec) : env :=
  with_e_numgen e
    (fun s => if numgen_eqb spec s then S (e_numgen e s) else e_numgen e s).

(** Update the SHARED rate-limiter token bucket [e_limit] for instance [spec] on
    packet [p], EXACTLY as the kernel nft_limit_eval does (elapsed refill +0):
      cap   = min(stored, lim_max spec)         (the burst-derived bucket cap)
      delta = cap - lim_cost p spec
      delta >= 0 -> store delta (PASS, consume the cost)
      delta <  0 -> store cap   (EXHAUSTED, the level after capping is kept)
    Every other instance's bucket — and every other env component — is preserved.
    The new level is therefore a genuine function of [ls_rate]/[ls_unit]/[ls_burst]
    (and the packet length in byte mode), not a fixed decrement-by-one. *)
Definition lim_newtokens (p : packet) (spec : limit_spec) : nat :=
  let cap := lim_avail p spec in
  if Nat.leb (lim_cost p spec) cap then cap - lim_cost p spec else cap.

Definition env_limit_upd (p : packet) (spec : limit_spec) : env :=
  let e := pkt_env p in
  with_e_limit e
    (fun s => if limit_eqb spec s then lim_newtokens p spec else e_limit e s).

(** Update the SHARED quota counter [e_quota] for instance [spec] on packet [p]:
    CONSUME the packet's byte length ([quota_cost p], = skb->len) UNCONDITIONALLY
    (the kernel nft_overquota accumulates skb->len on every evaluation, regardless
    of whether the rule passes).  With [e_quota] holding the REMAINING bytes, the
    consumption is a saturating subtraction of the cost (nat truncates at 0 once the
    quota is fully spent).  Mirrors byte-mode [limit] ([env_limit_upd], which
    likewise takes [p] and charges [lim_cost p]). *)
Definition env_quota_upd (p : packet) (spec : quota_spec) : env :=
  let e := pkt_env p in
  with_e_quota e
    (fun s => if quota_eqb spec s then e_quota e s - quota_cost p else e_quota e s).

(** Update the SHARED connlimit connection set [e_connlimit] for instance [spec] on
    packet [p]: IDEMPOTENTLY insert the packet's connection [pkt_flow p] into the
    instance's set of distinct counted flows (the kernel nft_connlimit_do_eval:
    [nf_conncount_add_skb] adds the skb's connection tuple, but is a no-op — returns
    -EEXIST — when that connection is already counted).  So a SECOND packet of an
    already-counted connection does NOT change the set (no double-counting), which is
    why one connection can never exhaust a `connlimit`.  Every other instance's set —
    and every other env component — is preserved. *)
Definition env_connlimit_upd (p : packet) (spec : connlimit_spec) : env :=
  let e := pkt_env p in
  with_e_connlimit e
    (fun s => if connlimit_eqb spec s
              then connlimit_after e spec (pkt_flow p)
              else e_connlimit e s).

(** Advance the shared `numgen inc` counter once: the side effect of EVALUATING a
    `numgen inc` expression.  The value the eval RETURNS is read by [do_load] BEFORE
    this from [e_numgen]; [set_numgen] then bumps the counter so the NEXT evaluation
    (this rule's later firing, threaded within the rule, or — through the
    cross-packet env threading by [run_rule_writes]/[body_writes] — the next packet's
    firing) reads the successor.  `numgen random` (ng_random = true) has no counter,
    so it is a no-op.  Only [pkt_env]'s [e_numgen] changes; every other packet/env
    component is preserved, so all loadability predicates are invariant under it and
    the DSL/VM stay in lock-step. *)
Definition set_numgen (p : packet) (spec : numgen_spec) : packet :=
  if ng_random spec then p else with_pkt_env p (env_numgen_upd (pkt_env p) spec).

(** [set_numgen] only changes [pkt_env]'s [e_numgen]; it leaves payload / meta / ct /
    flow / oracle components intact.  Hence loadability predicates and every read
    EXCEPT a `numgen inc` load are invariant under it. *)
Lemma read_payload_ok_numgen : forall b o l p spec,
  read_payload_ok b o l (set_numgen p spec) = read_payload_ok b o l p.
Proof. intros. unfold set_numgen. destruct (ng_random spec); reflexivity. Qed.

(** UPDATE a `limit` token bucket on EVERY evaluation of the limiter on packet [p],
    exactly as the kernel nft_limit_eval (it writes `tokens` on both the pass and the
    exhausted branch — see [env_limit_upd]/[lim_newtokens]).  Only [pkt_env]'s
    [e_limit] changes; every other packet/env component is preserved, so all
    loadability predicates are invariant and the DSL/VM stay lock-step. *)
Definition set_limit (p : packet) (spec : limit_spec) : packet :=
  with_pkt_env p (env_limit_upd p spec).

(** CONSUME the packet's byte length ([quota_cost p], = skb->len) from a `quota`
    UNCONDITIONALLY (the kernel accumulates skb->len on every evaluation). *)
Definition set_quota (p : packet) (spec : quota_spec) : packet :=
  with_pkt_env p (env_quota_upd p spec).

(** ACCOUNT for the packet's connection in a `connlimit` instance: IDEMPOTENTLY insert
    [pkt_flow p] into the instance's distinct-connection set on EVERY evaluation (the
    kernel nft_connlimit_do_eval always calls [nf_conncount_add_skb] before reading the
    count, regardless of whether the rule passes; re-adding a counted connection is the
    -EEXIST no-op).  Only [pkt_env]'s [e_connlimit] changes; every other packet/env
    component is preserved, so loadability predicates are invariant and the DSL/VM stay
    lock-step. *)
Definition set_connlimit (p : packet) (spec : connlimit_spec) : packet :=
  with_pkt_env p (env_connlimit_upd p spec).

Lemma read_payload_ok_limit : forall b o l p spec,
  read_payload_ok b o l (set_limit p spec) = read_payload_ok b o l p.
Proof. reflexivity. Qed.
Lemma read_payload_ok_quota : forall b o l p spec,
  read_payload_ok b o l (set_quota p spec) = read_payload_ok b o l p.
Proof. reflexivity. Qed.
Lemma read_payload_ok_connlimit : forall b o l p spec,
  read_payload_ok b o l (set_connlimit p spec) = read_payload_ok b o l p.
Proof. reflexivity. Qed.

(** The cross-packet `numgen inc` COUNTER ADVANCE of running a rule's bytecode: each
    incremental [INumgen] the program contains advances the instance's shared counter
    once (the kernel's per-evaluation atomic increment).  This is applied by the
    MUTATION evaluators ([run_program_mut]/[run_program_mut_env]) to the packet a rule
    leaves, so the NEXT packet of the traversal reads the successor numgen value —
    threaded through [pkt_env] exactly like a dynset/ct/nat env write.  Keeping the
    advance OUT of the per-instruction [run_rule_writes] preserves the load-fields
    lock-step; a `numgen inc` is a verdict-/register effect within a rule, its counter
    bump a cross-packet effect.  (A real ruleset contains no [INumgen]
    ([numgen_free_prog]), so the sweep is the identity there and the compiler's
    mutation correctness is unaffected.) *)
Definition numgen_sweep_prog (is : list instr) (p : packet) : packet :=
  fold_left (fun q i => match i with INumgen spec _ => set_numgen q spec | _ => q end) is p.

(** Whether a program contains NO incremental [INumgen] (so [numgen_sweep_prog] is the
    identity).  Holds for every compiled real ruleset (numgen has no DSL/parser
    surface). *)
Definition numgen_free_prog (is : list instr) : bool :=
  forallb (fun i => match i with INumgen spec _ => ng_random spec | _ => true end) is.

Lemma numgen_sweep_prog_id : forall is p,
  numgen_free_prog is = true -> numgen_sweep_prog is p = p.
Proof.
  intros is. unfold numgen_sweep_prog, numgen_free_prog.
  induction is as [| i is IH]; intros p H; [reflexivity|].
  cbn [forallb] in H. apply Bool.andb_true_iff in H. destruct H as [Hi Hrest].
  cbn [fold_left]. destruct i; try (apply IH; exact Hrest).
  (* INumgen: ng_random forces set_numgen = identity *)
  unfold set_numgen. rewrite Hi. apply IH; exact Hrest.
Qed.

(** The cross-rule/cross-packet CONSUMPTION of a rule's `limit`/`quota`/`connlimit`
    matches.  Mirroring [numgen_sweep_prog], this advances (depletes) each limiter
    the rule's bytecode evaluates, applied by the MUTATION evaluators
    ([run_program_mut]/[run_program_mut_env]) to the packet a rule leaves, so the
    NEXT packet of the traversal reads the depleted bucket and can get a DIFFERENT
    verdict — which is the entire purpose of a rate limit.  Keeping the consumption
    OUT of the per-instruction [run_rule_writes] preserves the load-fields/match
    lock-step (the verdict side reads the bucket deterministically; the consumption
    is a cross-rule/cross-packet effect, the same documented intra-rule scoping as
    `numgen inc`).  The fold is over the running packet, so a second limiter in the
    same rule sees the first one's consumption (the kernel runs limiters
    left-to-right against the running token state). *)
Definition limit_sweep_prog (is : list instr) (p : packet) : packet :=
  fold_left (fun q i => match i with
                        | ILimit spec => set_limit q spec
                        | IQuota spec => set_quota q spec
                        | IConnlimit spec => set_connlimit q spec
                        | _ => q
                        end) is p.

(** The DSL analogue: consume the same limiters by walking a rule body's matches.  A
    `limit`/`quota`/`connlimit` is the matchcond [MLimit]/[MQuota]/[MConnlimit]. *)
Definition limit_sweep_body (body : list body_item) (p : packet) : packet :=
  fold_left (fun q it => match it with
                         | BMatch (MLimit spec)    => set_limit q spec
                         | BMatch (MQuota spec)    => set_quota q spec
                         | BMatch (MConnlimit spec) => set_connlimit q spec
                         | _ => q
                         end) body p.

(** Whether a program contains NO limiter instruction (so [limit_sweep_prog] is the
    identity).  Used to discharge limiter-neutral programs in the same shape as
    [numgen_free_prog]. *)
Definition limit_free_prog (is : list instr) : bool :=
  forallb (fun i => match i with ILimit _ | IQuota _ | IConnlimit _ => false | _ => true end) is.

Lemma limit_sweep_prog_id : forall is p,
  limit_free_prog is = true -> limit_sweep_prog is p = p.
Proof.
  intros is. unfold limit_sweep_prog, limit_free_prog.
  induction is as [| i is IH]; intros p H; [reflexivity|].
  cbn [forallb] in H. apply Bool.andb_true_iff in H. destruct H as [Hi Hrest].
  cbn [fold_left]. destruct i; try discriminate Hi; apply IH; exact Hrest.
Qed.

(** Whether a rule body contains NO `limit`/`quota`/`connlimit` match (so the DSL
    [limit_sweep_body] is the identity — a rule that does no rate limiting threads its
    writes unchanged, exactly as before this fix).  Every existing example/Gen ruleset
    EXCEPT the limit cases satisfies this. *)
Definition limit_free_body (body : list body_item) : bool :=
  forallb (fun it => match it with
                     | BMatch (MLimit _) | BMatch (MQuota _) | BMatch (MConnlimit _) => false
                     | _ => true
                     end) body.

Lemma limit_sweep_body_id : forall body p,
  limit_free_body body = true -> limit_sweep_body body p = p.
Proof.
  intros body. unfold limit_sweep_body, limit_free_body.
  induction body as [| it body IH]; intros p H; [reflexivity|].
  cbn [forallb] in H. apply Bool.andb_true_iff in H. destruct H as [Hi Hrest].
  cbn [fold_left]. destruct it as [m | s]; [destruct m | ];
    try discriminate Hi; apply IH; exact Hrest.
Qed.

(** [set_untracked] only flips [pkt_untracked]; it leaves every payload / meta /
    env / oracle component intact.  Hence every loadability predicate (which reads
    only payload geometry) is invariant under it, and [field_value]/[eval_matchcond]
    change ONLY for a `ct state` read.  These invariance facts let the correctness
    proof thread [set_untracked] past a [notrack] on both the DSL and the VM side
    without disturbing the loadability/synproxy bookkeeping. *)
(** [set_untracked] preserves EVERY packet component the loadability / value
    predicates read — it only ever flips [pkt_untracked] (and only on a no-entry
    packet).  These per-projection equalities drive the invariance facts below
    uniformly, regardless of whether the [pkt_ct_present p] guard fires. *)
Lemma set_untracked_proj : forall p,
  pkt_env (set_untracked p) = pkt_env p /\
  pkt_meta (set_untracked p) = pkt_meta p /\
  pkt_have_l2 (set_untracked p) = pkt_have_l2 p /\
  pkt_have_l4 (set_untracked p) = pkt_have_l4 p /\
  pkt_fragoff (set_untracked p) = pkt_fragoff p /\
  pkt_eh (set_untracked p) = pkt_eh p /\
  pkt_lh (set_untracked p) = pkt_lh p /\
  pkt_nh (set_untracked p) = pkt_nh p /\
  pkt_th (set_untracked p) = pkt_th p /\
  pkt_ih (set_untracked p) = pkt_ih p /\
  pkt_tnl (set_untracked p) = pkt_tnl p /\
  pkt_inner (set_untracked p) = pkt_inner p /\
  pkt_ct_present (set_untracked p) = pkt_ct_present p /\
  pkt_flow (set_untracked p) = pkt_flow p.
Proof.
  intros p. destruct (pkt_ct_present p) eqn:E;
    unfold set_untracked, with_pkt_untracked; rewrite E;
    repeat split; rewrite ?E; reflexivity.
Qed.

(** [base_bytes] reads only the per-layer header projections, all preserved by
    [set_untracked], so the byte string a base exposes is unchanged. *)
Lemma base_bytes_untracked : forall b p,
  base_bytes b (set_untracked p) = base_bytes b p.
Proof. intros. unfold set_untracked. destruct (pkt_ct_present p); reflexivity. Qed.

Lemma read_payload_ok_untracked : forall b o l p,
  read_payload_ok b o l (set_untracked p) = read_payload_ok b o l p.
Proof. intros. unfold set_untracked. destruct (pkt_ct_present p); reflexivity. Qed.

Lemma synproxy_loadable_untracked : forall p,
  synproxy_loadable (set_untracked p) = synproxy_loadable p.
Proof. intros. unfold set_untracked. destruct (pkt_ct_present p); reflexivity. Qed.

Lemma synproxy_stops_untracked : forall p,
  synproxy_stops (set_untracked p) = synproxy_stops p.
Proof. intros. unfold set_untracked. destruct (pkt_ct_present p); reflexivity. Qed.

(** A field's load succeeds on [set_untracked p] iff it does on [p]: the only
    state-dependent leaf is the conntrack-entry presence ([LCt _ => pkt_ct_present]),
    which [set_untracked] preserves; every other leaf reads payload geometry only. *)
Lemma load_ok_untracked : forall ld p,
  load_ok ld (set_untracked p) = load_ok ld p.
Proof.
  intros ld p.
  destruct (set_untracked_proj p) as (Henv & Hmeta & Hl2 & Hl4 & Hfr & Heh & Hlh & Hnh
    & Hth & Hih & Htnl & Hinner & Hctp & Hflow).
  destruct ld; cbn [load_ok]; try reflexivity.
  - (* LCt k *) destruct k; try reflexivity; rewrite Hctp; reflexivity.
  - (* LExthdr ... present *)
    match goal with
    | |- (if ?b then _ else _) = _ => destruct b; [reflexivity|]
    end.
    unfold exthdr_present. rewrite Heh. reflexivity.
  - (* LPayload b o l *) apply read_payload_ok_untracked.
Qed.

Lemma field_loadable_untracked : forall f p,
  field_loadable f (set_untracked p) = field_loadable f p.
Proof. intros. unfold field_loadable. apply load_ok_untracked. Qed.

Lemma fields_loadable_untracked : forall fs p,
  fields_loadable fs (set_untracked p) = fields_loadable fs p.
Proof.
  intros fs p. unfold fields_loadable. induction fs as [| f fs IH]; [reflexivity|].
  cbn [forallb]. rewrite field_loadable_untracked, IH. reflexivity.
Qed.

(** Whether a body contains a `notrack` statement (the latch source).  When [false]
    the [set_untracked] threading in [rule_applies_walk] never fires, so the walk is
    exactly the original [forallb eval_matchcond (body_matches …)] over [p]. *)
Definition body_has_notrack (body : list body_item) : bool :=
  existsb (fun it => match it with BStmt SNotrack => true | _ => false end) body.


(** [set_untracked] is idempotent — it only ever forces the latch to [true]. *)
Lemma set_untracked_idem : forall p,
  set_untracked (set_untracked p) = set_untracked p.
Proof.
  intros p. destruct (pkt_ct_present p) eqn:E.
  - assert (set_untracked p = p) as Heq by (unfold set_untracked; rewrite E; reflexivity).
    rewrite Heq. exact Heq.
  - remember (set_untracked p) as q eqn:Hq.
    assert (pkt_ct_present q = false) as Hf
      by (rewrite Hq; unfold set_untracked, with_pkt_untracked; rewrite E; reflexivity).
    unfold set_untracked at 1. rewrite Hf.
    rewrite Hq. unfold set_untracked. rewrite E. reflexivity.
Qed.

(** [match_loadable] reads only payload geometry, so it is invariant under the
    latch flip. *)
Lemma match_loadable_untracked : forall m p,
  match_loadable m (set_untracked p) = match_loadable m p.
Proof.
  intros m p. destruct m; cbn [match_loadable];
    try apply field_loadable_untracked; try reflexivity;
    apply fields_loadable_untracked.
Qed.

(** Whether a rule's body contains a SYN-proxy statement that STOPS traversal on
    this packet (a TCP packet with SYN or ACK set; see [synproxy_stops]).  Such a
    synproxy is a terminal action — it short-circuits the verdict map / terminal —
    so it is checked first in [outcome].  (A synproxy whose flags-load BREAKs makes
    the whole rule unloadable, so it never reaches here; a non-stopping synproxy is
    transparent.) *)
Definition body_synproxy_stops (body : list body_item) (p : packet) : bool :=
  existsb (fun it => match it with
                     | BStmt (SSynproxy _ _) => synproxy_stops p
                     | _ => false
                     end) body.

(** A rule applies when all its match conditions hold (empty = matches all).
    Statements are walked in ORDER: a SYN-proxy statement that STOPS traversal
    (see [synproxy_stops]) short-circuits — any match positioned AFTER it is
    unreachable (the kernel has already STOLEN/DROPped the packet), so the
    remaining matches vacuously pass; a match positioned BEFORE a stopping synproxy
    still gates whether the synproxy runs at all (a failing earlier match BREAKs
    the rule first).  Every other statement is verdict-neutral.  When the body has
    no stopping synproxy this is exactly [forallb eval_matchcond (body_matches …)]
    (proved as [rule_applies_no_synproxy]). *)
Fixpoint rule_applies_walk (body : list body_item) (p : packet) : bool :=
  match body with
  | [] => true
  | BMatch m :: rest => eval_matchcond m p && rule_applies_walk rest p
  | BStmt (SSynproxy _ _) :: rest =>
      if synproxy_stops p then true else rule_applies_walk rest p
  (* `notrack` forces IP_CT_UNTRACKED for the rest of THIS rule's traversal ONLY
     WHEN no conntrack entry exists yet — exactly nft_notrack_eval's
     `if (ct || ctinfo == IP_CT_UNTRACKED) return;` guard (it is a NO-OP on a
     packet that already has an entry, e.g. an ESTABLISHED flow).  [set_untracked]
     encodes that guard ([pkt_ct_present p = true] => unchanged), so a LATER
     `ct state` MATCH in the SAME rule reads the entry's REAL state on a tracked
     packet and NF_CT_STATE_UNTRACKED_BIT only on a no-entry packet (kernel runs a
     rule's expressions left-to-right: nft_notrack_eval may set the untracked latch,
     a subsequent nft_ct_get_eval NFT_CT_STATE observes the result).  We thread
     [set_untracked] into the rest of the walk so the model is faithful for the
     intra-rule `notrack; ct state untracked accept` idiom on a no-entry packet.
     [set_untracked] preserves every loadability/synproxy predicate (it only flips
     [pkt_untracked], and only on a no-entry packet), so the VM stays in lock-step
     (the compiled [INotrack] threads the same [set_untracked]). *)
  | BStmt SNotrack :: rest => rule_applies_walk rest (set_untracked p)
  | BStmt _ :: rest => rule_applies_walk rest p
  end.
Definition rule_applies (r : rule) (p : packet) : bool :=
  rule_applies_walk (r_body r) p.

(** When the body contains no stopping synproxy AND no `notrack` (so the
    [set_untracked] threading never fires), [rule_applies_walk] is exactly
    [forallb eval_matchcond] over the body's matches against the ORIGINAL [p]. *)
Lemma rule_applies_walk_no_synproxy : forall body p,
  body_synproxy_stops body p = false ->
  body_has_notrack body = false ->
  rule_applies_walk body p = forallb (fun m => eval_matchcond m p) (body_matches body).
Proof.
  induction body as [| it body IH]; intros p Hsp Hnt; [reflexivity|].
  assert (Hcons : forall it0 b, body_synproxy_stops (it0 :: b) p =
            (match it0 with BStmt (SSynproxy _ _) => synproxy_stops p | _ => false end)
            || body_synproxy_stops b p) by reflexivity.
  assert (Hntcons : forall it0 b, body_has_notrack (it0 :: b) =
            (match it0 with BStmt SNotrack => true | _ => false end)
            || body_has_notrack b) by reflexivity.
  rewrite Hcons in Hsp. rewrite Hntcons in Hnt. destruct it as [m | s].
  - cbn [orb] in Hsp, Hnt. cbn [rule_applies_walk body_matches flat_map app forallb].
    rewrite IH by assumption. reflexivity.
  - destruct s; cbn [orb] in Hsp, Hnt; cbn [rule_applies_walk body_matches flat_map app];
      try (apply IH; assumption); try discriminate Hnt.
    (* SSynproxy: the [orb] head is [synproxy_stops p]; Hsp forces it false *)
    destruct (synproxy_stops p) eqn:Hs;
      [discriminate Hsp | apply IH; assumption].
Qed.

(** ** Whole-rule loadability.

    A payload load that BREAKs (NFT_BREAK) anywhere in a rule — in a match, a
    statement operand, the verdict-map key, or the terminal operand — makes the
    kernel abandon the rule (the rule produces no verdict; traversal continues to
    the next rule).  Because the break wins regardless of where it occurs, the
    rule's outcome depends only on whether ANYTHING in it breaks: we collect every
    field the rule loads into [rule_loadable] and skip the rule when it is [false]
    (so the verdict does not depend on the interleaved match/statement order). *)

(** Fields a value source loads. *)
Definition vsrc_loadable (vs : vsrc) (p : packet) : bool :=
  match vs with
  | VImm _ => true
  | VField f _ => field_loadable f p
  | VMap fields _ _ => fields_loadable fields p
  | VHash fields _ _ _ _ => fields_loadable fields p
  | VOr srcs _ => fields_loadable (map fst srcs) p
  | VMapT elems _ => fields_loadable (map fst elems) p
  | VHashMap fields _ _ _ _ _ => fields_loadable fields p
  end.

Definition stmt_loadable (s : stmt) (p : packet) : bool :=
  match s with
  | SMangle vs _ _ _ _ _ _ => vsrc_loadable vs p
  | SMetaSet _ vs => vsrc_loadable vs p
  | SCtSet _ vs => vsrc_loadable vs p
  | SCtSetDir _ _ vs => vsrc_loadable vs p
  | SDynset _ _ keyfs dataf => fields_loadable (keyfs ++ dataf) p
  | SObjrefMap keyfs _ => fields_loadable keyfs p
  | SDynsetImm _ _ keyfs _ => fields_loadable keyfs p
  | SExthdrWrite vs _ _ _ _ => vsrc_loadable vs p
  | SDupSrc src _ _ => vsrc_loadable src p
  | SSynproxy _ _ => synproxy_loadable p   (* non-TCP / non-L4 => NFT_BREAK (rule skipped) *)
  | SCounter _ _ | SNotrack | SLog _ | SObjref _ _
  | SLast _ | SExthdrReset _ _ | SDup _ _ => true
  end.

Definition body_item_loadable (it : body_item) (p : packet) : bool :=
  match it with
  | BMatch m => match_loadable m p
  | BStmt s => stmt_loadable s p
  end.

(** A value source reads only fields (payload geometry) plus immediates, all
    invariant under the latch flip. *)
Lemma vsrc_loadable_untracked : forall vs p,
  vsrc_loadable vs (set_untracked p) = vsrc_loadable vs p.
Proof.
  intros vs p. destruct vs; cbn [vsrc_loadable];
    try reflexivity;
    try apply field_loadable_untracked; apply fields_loadable_untracked.
Qed.

(** Statement / body-item loadability read only payload geometry, so they too are
    invariant under the latch flip ([set_untracked]). *)
Lemma stmt_loadable_untracked : forall s p,
  stmt_loadable s (set_untracked p) = stmt_loadable s p.
Proof.
  intros s p. destruct s; cbn [stmt_loadable];
    try reflexivity;
    try apply vsrc_loadable_untracked;
    try apply fields_loadable_untracked;
    apply synproxy_loadable_untracked.
Qed.

Lemma body_item_loadable_untracked : forall it p,
  body_item_loadable it (set_untracked p) = body_item_loadable it p.
Proof.
  intros it p. destruct it as [m | s];
    [apply match_loadable_untracked | apply stmt_loadable_untracked].
Qed.

Definition vmap_loadable (ov : option vmap_spec) (p : packet) : bool :=
  match ov with
  | None => true
  | Some vm => match vm_keyf vm with
               | Some (f, _) => field_loadable f p
               | None => fields_loadable (vm_fields vm) p
               end
  end.

Definition terminal_loadable (r : rule) (p : packet) : bool :=
  match r_nat r with
  | Some n => match nat_src n with
              | Some vs => vsrc_loadable vs p
              | None => match nat_map n with
                        | Some (fields, _, _) => fields_loadable fields p
                        | None => match nat_field n with
                                  | Some (f, _) => field_loadable f p
                                  | None => true
                                  end
                        end
              end
  | None =>
  match r_tproxy r with
  | Some _ => true
  | None =>
  match r_fwd r with
  | Some w => vsrc_loadable (fwd_dev w) p
  | None =>
  match r_queue r with
  | Some q => vsrc_loadable (q_num q) p
  | None => true
  end end end end.

(** ** Named sets and maps as DECLARED objects.

    A set/map is not just a name with abstract contents: it is a *declaration* —
    a named list of elements.  A set's elements are intervals [lo,hi] (exact =
    [x,x], CIDR = [lo,hi]); a verdict map's are key->verdict; a value map's are
    key->value.  [set_decls] is what a table declares; [env_with_sets] turns those
    declarations into the evaluation environment the rule lookups read, so
    `lookup @s` reads exactly the elements DECLARED for [s].  This ties the
    membership semantics to the declared object: change the declaration and the
    lookup sees the change (witnessed in semtest). *)
Record set_decls : Type := {
  sd_sets  : list (String.string * list (data * data));     (* set name -> interval elements *)
  sd_vmaps : list (String.string * list (data * data * verdict));  (* verdict-map name -> [lo,hi]-key entries *)
  sd_maps  : list (String.string * list (data * data));     (* value-map name -> entries *)
}.
Fixpoint assoc_str {A} (n : String.string) (l : list (String.string * A)) (d : A) : A :=
  match l with
  | [] => d
  | (k, v) :: r => if String.eqb n k then v else assoc_str n r d
  end.
(** Build the lookup environment from a table's set/map declarations (the other
    state — routes, limiters — is carried from a base environment). *)
Definition env_with_sets (base : env) (d : set_decls) : env :=
  {| e_set  := fun n => assoc_str n (sd_sets d)  (e_set base n);
     e_vmap := fun n => assoc_str n (sd_vmaps d) (e_vmap base n);
     e_map  := fun n => assoc_str n (sd_maps d)  (e_map base n);
     e_routes := e_routes base; e_rt := e_rt base;
     e_ifaddrs := e_ifaddrs base; e_ifaddrs6 := e_ifaddrs6 base;
     e_limit := e_limit base; e_quota := e_quota base; e_connlimit := e_connlimit base;
     e_ct := e_ct base; e_nat := e_nat base; e_numgen := e_numgen base |}.

(** A declared set's elements are exactly what `lookup @n` reads. *)
Lemma e_set_declared : forall base d n,
  e_set (env_with_sets base d) n = assoc_str n (sd_sets d) (e_set base n).
Proof. reflexivity. Qed.

(** The verdict contribution of a list of post-outcome ([r_after]) statements,
    walked left-to-right exactly as the VM runs them on a [Continue] fall-through:
    a SYN-proxy whose flags-load BREAKs (non-TCP) abandons the rule ([None]); one
    that STOPS (SYN/ACK) is terminal [Some Drop]; an ordinary statement whose
    operand load BREAKs also abandons the rule ([None]); otherwise we proceed.
    (Only synproxy is verdict-bearing; every other statement is verdict-neutral, so
    the only [Some] this produces is the synproxy [Drop].)  [r_after] never carries
    a synproxy after lowering — this keeps the per-rule equation faithful even for
    a hand-built rule that puts one there. *)
Fixpoint stmts_after_outcome (ss : list stmt) (p : packet) : option verdict :=
  match ss with
  | [] => None
  | SSynproxy _ _ :: rest =>
      if synproxy_loadable p
      then (if synproxy_stops p then Some Drop else stmts_after_outcome rest p)
      else None
  | s :: rest => if stmt_loadable s p then stmts_after_outcome rest p else None
  end.

(** [stmts_after_outcome] reads only loadability / synproxy (all invariant under the
    latch flip), so it is invariant under [set_untracked].  This lets a [notrack] in
    [r_after] thread [set_untracked] on the VM side without changing the verdict. *)
Lemma stmts_after_outcome_untracked : forall ss p,
  stmts_after_outcome ss (set_untracked p) = stmts_after_outcome ss p.
Proof.
  induction ss as [| s ss IH]; intro p; [reflexivity|].
  destruct s; cbn [stmts_after_outcome];
    rewrite ?stmt_loadable_untracked, ?synproxy_loadable_untracked,
            ?synproxy_stops_untracked, ?IH; reflexivity.
Qed.

(** The *value* a value-source computes into register 1 — the operand of a
    set/mangle/NAT statement.  This is the value-level meaning the verdict proof
    previously delegated to the corpus; [run_vsrc_value] (in Correct) proves the
    compiled operand leaves exactly this in reg 1, which is the foundation for
    modelling mutation (Phase B): a `meta mark set vs` writes [eval_vsrc vs p].
    (Defined to mirror the bytecode, incl. its simplifications — faithfulness of
    e.g. jhash-over-concatenation to the kernel is a separate, Phase-D, matter.) *)
Definition eval_vsrc (vs : vsrc) (p : packet) : data :=
  match vs with
  | VImm v      => v
  | VField f ts => apply_transforms ts (field_value f p)
  | VMap fields ts name =>
      let key := match fields with
                 | [] => apply_transforms ts []
                 | f0 :: frest =>
                     List.concat (apply_transforms ts (field_value f0 p)
                                  :: map (fun f => field_value f p) frest)
                 end in
      map_lookup_data key (e_map (pkt_env p) name)
  | VHash fields len seed modulus offset =>
      data_jhash len seed modulus offset
        (match fields with [] => [] | f0 :: _ => field_value f0 p end)
  | VOr srcs final =>
      match srcs with
      | [] => []
      | base :: rest =>
          apply_transforms final
            (fold_left
               (fun acc e => data_or acc (apply_transforms (snd e) (field_value (fst e) p)))
               rest (apply_transforms (snd base) (field_value (fst base) p)))
      end
  | VMapT elems name =>
      map_lookup_data
        (List.concat (map (fun fe => apply_transforms (snd fe) (field_value (fst fe) p)) elems))
        (e_map (pkt_env p) name)
  | VHashMap fields len seed modulus offset name =>
      map_lookup_data
        (data_jhash len seed modulus offset
           (match fields with [] => [] | f0 :: _ => field_value f0 p end))
        (e_map (pkt_env p) name)
  end.

(** Look up a key in a verdict map's entries.  Each entry carries a closed
    interval KEY [lo,hi]: the kernel verdict-map set is the rbtree type
    NFT_SET_INTERVAL | NFT_SET_MAP (net/netfilter/nft_set_rbtree.c), so a vmap
    key may be a range/prefix and the lookup is an interval search returning the
    associated verdict of the FIRST entry whose interval contains [key]
    (lo <= key <= hi, big-endian via [data_in_iv]).  A POINT key is stored as the
    degenerate [k,k]: [data_in_iv k (k,k) = true] and only [key=k] matches (by
    [data_le_antisym]), so point vmaps are unchanged.  This mirrors the named-set
    [set_mem]/[data_in_iv] interval test — closing the set/vmap asymmetry. *)
Fixpoint assoc_verdict (key : data) (entries : list (data * data * verdict)) : option verdict :=
  match entries with
  | [] => None
  | (lo, hi, v) :: rest =>
      if data_in_iv key (lo, hi) then Some v else assoc_verdict key rest
  end.

(** The terminal outcome of a rule once any verdict map has fallen through: a
    [nat]/[tproxy]/[fwd]/[queue] side effect accepts, otherwise the static
    verdict ([Continue] = fall through). *)
Definition terminal_outcome (r : rule) (p : packet) : option verdict :=
  match r_nat r with
  | Some _ => Some Accept   (* NAT is terminal accept (translation is a side effect) *)
  | None =>
  match r_tproxy r with
  | Some _ => Some Accept   (* tproxy is terminal accept (redirect is a side effect) *)
  | None =>
  match r_fwd r with
  | Some _ => Some Accept   (* fwd is terminal accept (forward is a side effect) *)
  | None =>
  match r_queue r with
  | Some _ => Some Accept   (* queue is terminal accept (hand-off is a side effect) *)
  | None => match r_verdict r with
            (* a [Continue] verdict falls through to the post-outcome statements;
               a SYN-proxy among them is the only verdict-bearing one (terminal
               Drop), otherwise the fall-through continues ([None]). *)
            | Continue => stmts_after_outcome (r_after r) p
            | v => Some v
            end
  end
  end
  end
  end.

(** A rule's outcome (when it applies): a [Some v] (verdict reached) or [None]
    (fall through).  A SYN-proxy stop in the body is the terminal action (the
    packet is consumed/dropped at this hook — see [synproxy_stops]); otherwise a
    verdict map is evaluated first: a hit gives its verdict, a miss falls through
    to the terminal outcome (so a rule may carry both a vmap and a trailing
    redirect/masquerade). *)
(** The verdict-map / terminal part of a rule's outcome (the part the compiled
    [compile_end] realises): a vmap hit gives its verdict, a miss falls through to
    the terminal.  This is the outcome IGNORING any body synproxy. *)
Definition outcome_core (r : rule) (p : packet) : option verdict :=
  match r_vmap r with
  | Some vm =>
      let key := match vm_keyf vm with
                 | Some (f, ts) => apply_transforms ts (field_value f p)
                 | None => List.concat (map (fun f => field_value f p) (vm_fields vm))
                 end in
      match assoc_verdict key (e_vmap (pkt_env p) (vm_name vm)) with
      | Some v => Some v
      | None   => terminal_outcome r p
      end
  | None => terminal_outcome r p
  end.

(** The packet the rule's TERMINAL/verdict-map part (its [outcome_core]) sees: when
    the rule applies, every body item — including any [notrack] — was reached, so a
    `notrack` in the body has latched IP_CT_UNTRACKED before the terminal runs.  As
    [set_untracked] only flips the (monotone, idempotent) [pkt_untracked] latch,
    threading it through the whole body collapses to: untracked iff the body has a
    [notrack].  This is exactly what the VM's [run_rule] sees after threading
    [set_untracked] past [INotrack] into the compiled terminal/vmap tail. *)
Definition body_thread (body : list body_item) (p : packet) : packet :=
  if body_has_notrack body then set_untracked p else p.

Definition outcome (r : rule) (p : packet) : option verdict :=
  if body_synproxy_stops (r_body r) p then Some Drop
  else outcome_core r (body_thread (r_body r) p).

(** ** Whole-rule loadability (NFT_BREAK reachability).

    A payload load that BREAKs (NFT_BREAK) anywhere the rule actually EVALUATES
    makes the kernel abandon the rule (no verdict; traversal continues).  This
    mirrors exactly what the compiled bytecode executes (and breaks on), in order:
      - every body item (matches + statements) is evaluated, so all must load;
      - the verdict-map key (if any) is loaded; on a HIT the rule's verdict is
        fixed and nothing after the [IVmap] runs (so the terminal/[r_after] need
        not load); on a MISS the terminal is evaluated;
      - on the terminal: a side-effect terminal (nat/tproxy/fwd/queue) loads its
        operand then accepts (so [r_after] never runs); a static *terminal*
        verdict stops too; only a [Continue] fall-through runs [r_after].
    [rule_loadable] is [false] exactly when some load on this evaluated path
    breaks; [eval_rules] then skips the rule, matching the VM (which breaks at
    that load and falls through to the next rule). *)

(** Loadability of the part that runs AFTER the verdict map misses: the terminal,
    and — only on a [Continue] fall-through — the post-outcome statements. *)
Definition tail_loadable (r : rule) (p : packet) : bool :=
  terminal_loadable r p &&
  (match terminal_outcome r p with
   | None => forallb (fun s => stmt_loadable s p) (r_after r)  (* fall-through: r_after runs *)
   | Some _ => true                                            (* terminal: r_after skipped *)
   end).

(** Loadability of a rule's outcome computation (verdict map then terminal),
    mirroring [outcome]'s evaluation order. *)
Definition end_loadable (r : rule) (p : packet) : bool :=
  match r_vmap r with
  | Some vm =>
      vmap_loadable (r_vmap r) p &&
      (let key := match vm_keyf vm with
                  | Some (f, ts) => apply_transforms ts (field_value f p)
                  | None => List.concat (map (fun f => field_value f p) (vm_fields vm))
                  end in
       match assoc_verdict key (e_vmap (pkt_env p) (vm_name vm)) with
       | Some _ => true              (* vmap HIT: terminal/r_after unreachable *)
       | None   => tail_loadable r p (* vmap MISS: terminal runs *)
       end)
  | None => tail_loadable r p
  end.

(** Loadability of a body, walked left-to-right: every item must load, but a
    SYN-proxy that STOPS traversal makes every later item UNREACHABLE (the kernel
    has already STOLEN/DROPped), so those need not load — exactly mirroring the VM,
    which returns the synproxy verdict and never executes the rest.  With no
    stopping synproxy this is [forallb body_item_loadable] (the prior model). *)
Fixpoint body_loadable_walk (body : list body_item) (p : packet) : bool :=
  match body with
  | [] => true
  | BStmt (SSynproxy _ _) :: rest =>
      synproxy_loadable p &&
      (if synproxy_stops p then true else body_loadable_walk rest p)
  | it :: rest => body_item_loadable it p && body_loadable_walk rest p
  end.

(** A rule is loadable when its body loads (up to any stopping SYN-proxy) AND —
    unless a body SYN-proxy STOPS traversal (in which case the verdict-map /
    terminal / [r_after] are unreachable, exactly like a vmap HIT) — the end part
    loads too. *)
(** With no stopping synproxy in the body, [body_loadable_walk] collapses to
    [forallb body_item_loadable] (every item is required to load, as before). *)
Lemma body_loadable_walk_no_synproxy : forall body p,
  body_synproxy_stops body p = false ->
  body_loadable_walk body p = forallb (fun it => body_item_loadable it p) body.
Proof.
  induction body as [| it body IH]; intro p; [reflexivity|].
  assert (Hcons : body_synproxy_stops (it :: body) p =
            (match it with BStmt (SSynproxy _ _) => synproxy_stops p | _ => false end)
            || body_synproxy_stops body p) by reflexivity.
  rewrite Hcons. destruct it as [m | s].
  - cbn [orb body_loadable_walk forallb]. intro H. rewrite IH by exact H. reflexivity.
  - destruct s; cbn [body_loadable_walk forallb body_item_loadable stmt_loadable];
      try (cbn [orb]; intro H; rewrite IH by exact H; reflexivity).
    (* SSynproxy: non-stopping; [body_item_loadable] is [synproxy_loadable] *)
    destruct (synproxy_stops p) eqn:Hs; cbn [orb];
      [discriminate | intro H; rewrite IH by exact H; reflexivity].
Qed.

(** [body_synproxy_stops] and [body_loadable_walk] read only [synproxy_stops] /
    loadability, both invariant under the latch flip, so they are invariant under
    [set_untracked].  This lets the correctness proof carry the loadability /
    synproxy bookkeeping unchanged across a [notrack]'s [set_untracked]. *)
Lemma body_synproxy_stops_untracked : forall body p,
  body_synproxy_stops body (set_untracked p) = body_synproxy_stops body p.
Proof.
  intros body p. unfold body_synproxy_stops. induction body as [| it b IH]; [reflexivity|].
  cbn [existsb]. rewrite IH. destruct it as [m | s]; [reflexivity|].
  destruct s; rewrite ?synproxy_stops_untracked; reflexivity.
Qed.

Lemma body_loadable_walk_untracked : forall body p,
  body_loadable_walk body (set_untracked p) = body_loadable_walk body p.
Proof.
  intros body p. induction body as [| it b IH]; [reflexivity|].
  destruct it as [m | s].
  - cbn [body_loadable_walk]. rewrite body_item_loadable_untracked, IH. reflexivity.
  - destruct s; cbn [body_loadable_walk];
      try (rewrite body_item_loadable_untracked, IH; reflexivity).
    (* SSynproxy *)
    rewrite synproxy_loadable_untracked, synproxy_stops_untracked, IH. reflexivity.
Qed.

(** The END (verdict-map / terminal) part is reached AFTER the body, so — like
    [outcome_core] — it sees the body-threaded packet: a `notrack` in the body has
    latched IP_CT_UNTRACKED, which a vmap KEY that reads `ct state` would observe.
    The VM threads the same [set_untracked] into the compiled tail, so end-loadability
    is taken at [body_thread (r_body r) p] on both sides. *)
Definition rule_loadable (r : rule) (p : packet) : bool :=
  body_loadable_walk (r_body r) p &&
  (if body_synproxy_stops (r_body r) p then true
   else end_loadable r (body_thread (r_body r) p)).

(** Evaluate a rule list.  [None] means "fell through every rule"; [Some v]
    means a terminal verdict [v] was reached.  A [Continue] verdict on an
    applicable rule simply proceeds, exactly like a non-applicable rule. *)
Fixpoint eval_rules (rs : list rule) (p : packet) : option verdict :=
  match rs with
  | [] => None
  | r :: rest =>
      if rule_loadable r p && rule_applies r p then
        match outcome r p with
        | Some v => if terminal v then Some v else eval_rules rest p
        | None   => eval_rules rest p
        end
      else eval_rules rest p
  end.

Definition eval_chain (c : chain) (p : packet) : verdict :=
  match eval_rules (c_rules c) p with
  | Some v => v
  | None   => c_policy c
  end.

(** ** Jump-freedom: the exact domain on which [eval_rules]/[eval_chain] are
    FAITHFUL.

    [eval_rules] has NO chain environment, so when a rule's realised outcome on
    [p] is a [Jump]/[Goto]/[Return] it can only treat it as a non-terminal
    fall-through ([terminal (Jump _) = false]) — i.e. it silently ignores the
    control transfer.  That is unfaithful to netfilter (nf_tables_core.c: a JUMP
    runs the target chain, resuming the caller on return; a GOTO tail-calls it; a
    RETURN pops to the caller).  The faithful interpreter is the environment-aware
    [eval_rules_j]/[eval_table] below.

    [outcome_jumpfree r p] holds exactly when the rule's realised outcome on [p]
    is NOT a control-transfer verdict; [rules_jumpfree]/[chain_jumpfree] lift it to
    a rule list / chain.  On this domain — and only on it — the cheap
    environment-free [eval_chain] coincides with the faithful [eval_table] (see
    [eval_rules_jumpfree_eq_j] / [eval_chain_eq_table_jumpfree] in Correct.v). *)
Definition outcome_jumpfree (r : rule) (p : packet) : bool :=
  match outcome r p with
  | Some (Jump _) | Some (Goto _) | Some Return => false
  | _ => true
  end.

Definition rules_jumpfree (rs : list rule) (p : packet) : bool :=
  forallb (fun r => outcome_jumpfree r p) rs.

Definition chain_jumpfree (c : chain) (p : packet) : bool :=
  rules_jumpfree (c_rules c) p.

(** ** Bytecode VM semantics. *)

(** Run one rule's program over a register file.  [None] means a [cmp] failed
    (the rule does not apply, like netfilter "breaking" out of the rule);
    [Some v] means an [immediate] set verdict [v]. *)
Fixpoint run_rule (rf : regfile) (is : rule_prog) (p : packet) : option verdict :=
  match is with
  | [] => None
  | IMetaLoad k dst :: rest =>
      run_rule (set_reg rf dst (pkt_meta p k)) rest p
  | ICtLoad k dst :: rest =>
      (* identical to [do_load (LCt k)]: a writable/persistent key reads the SHARED
         flow-keyed conntrack table, a read-only key the per-packet oracle, EXCEPT
         a `ct state` read after a `notrack` returns NF_CT_STATE_UNTRACKED_BIT.  A
         conntrack load on a packet with NO entry ([pkt_ct_present = false]) BREAKs the
         rule for EVERY key except [CKstate] (kernel nft_ct.c:81-82 `if (ct == NULL)
         goto err`); gate on the same [load_ok] predicate the DSL uses so DSL/VM stay
         in lock-step. *)
      if load_ok (LCt k) p
      then run_rule (set_reg rf dst (do_load (LCt k) p)) rest p
      else None
  | IRtLoad k dst :: rest =>
      run_rule (set_reg rf dst (e_rt (pkt_env p) k)) rest p
  | ISocketLoad k dst :: rest =>
      run_rule (set_reg rf dst (pkt_sock p k)) rest p
  | INumgen spec dst :: rest =>
      (* `numgen inc` reads the SHARED counter value (= [do_load (LNumgen spec) p],
         deterministic from [e_numgen]) into the dreg.  The VERDICT pass reads but
         does NOT advance the counter (it threads no packet); the COUNTER ADVANCE
         (the cross-packet round-robin) is applied on the WRITE pass
         [run_rule_writes]/[body_writes] and threaded to the next packet by
         [run_program_mut_env]/[eval_chain_mut_env] — exactly like a `ct`/`nat`/dynset
         env write.  Reading [do_load] keeps this lock-step with the DSL [outcome]. *)
      run_rule (set_reg rf dst (do_load (LNumgen spec) p)) rest p
  | IOsf dst :: rest =>
      run_rule (set_reg rf dst (pkt_osf p)) rest p
  | IExthdrLoad ep h o l pr dst :: rest =>
      (* A VALUE load (pr=false) of an ABSENT extension-header / TCP-option /
         SCTP-chunk makes the kernel set NFT_BREAK (nft_exthdr_*_eval err path).
         An EXISTENCE load (pr=true) never breaks (stores 0 under F_PRESENT).
         Gate on the same predicate the DSL's [load_ok] uses. *)
      if load_ok (LExthdr ep h o l pr) p
      then run_rule (set_reg rf dst (pkt_eh p ep h o l pr)) rest p
      else None
  | IFibLoad sel res dst :: rest =>
      run_rule (set_reg rf dst (lpm_fib (e_routes (pkt_env p)) (pkt_fibkey p sel) res)) rest p
  | ICtDirLoad key dir dst :: rest =>
      run_rule (set_reg rf dst (pkt_ctdir p key dir)) rest p
  | IXfrmLoad dir sp key dst :: rest =>
      run_rule (set_reg rf dst (pkt_xfrm p dir sp key)) rest p
  | ITunnelLoad key dst :: rest =>
      run_rule (set_reg rf dst (pkt_tunnel p key)) rest p
  | ISymhash m o dst :: rest =>
      run_rule (set_reg rf dst (pkt_symhash p m o)) rest p
  | IInnerLoad t h fl desc _ dst :: rest =>
      run_rule (set_reg rf dst (pkt_inner p t h fl desc)) rest p
  | IPayloadLoad b o l dst :: rest =>
      (* A payload read that runs off the end of the header (or a transport read on
         a fragment / no-L4 packet) makes the kernel set the verdict to NFT_BREAK,
         i.e. the rule does NOT match.  Model that as breaking the rule here
         ([None]), rather than loading a truncated value. *)
      if read_payload_ok b o l p
      then run_rule (set_reg rf dst (read_payload b o l p)) rest p
      else None
  | ICmp op src v :: rest =>
      if eval_cmp op (rf src) v then run_rule rf rest p else None
  | IRange op src lo hi :: rest =>
      if eval_range op (rf src) lo hi then run_rule rf rest p else None
  | IBitwise dst src mask xor :: rest =>
      run_rule (set_reg rf dst (data_bitops (rf src) mask xor)) rest p
  | IBitwiseOr dst src1 src2 :: rest =>
      run_rule (set_reg rf dst (data_or (rf src1) (rf src2))) rest p
  | IBitShift dst src shl amt :: rest =>
      run_rule (set_reg rf dst (data_shift shl amt (rf src))) rest p
  | IByteorder dst src h sz len :: rest =>
      run_rule (set_reg rf dst (data_byteorder h sz len (rf src))) rest p
  | IJhash dst src l s m o :: rest =>
      run_rule (set_reg rf dst (data_jhash l s m o (rf src))) rest p
  | ILookup srcs name neg :: rest =>
      (* set membership: contents read from the named set in [pkt_env p].  Each
         source register holds one concatenated field's value, so [map rf srcs]
         is the per-field value list; [concat_set_mem] tests each field against
         its own per-field interval (NFT_SET_CONCAT cross-product semantics). *)
      if xorb neg (concat_set_mem (map rf srcs) (e_set (pkt_env p) name))
      then run_rule rf rest p else None
  | IVmap srcs name :: rest =>
      (* a verdict map: a hit terminates with that verdict; a miss falls through
         to the rest (e.g. a trailing redirect/masquerade), exactly as nft does.
         Entries are read by [name] from [pkt_env p]. *)
      match assoc_verdict (List.concat (map rf srcs)) (e_vmap (pkt_env p) name) with
      | Some v => Some v
      | None   => run_rule rf rest p
      end
  | IImmediateData dst v :: rest =>
      run_rule (set_reg rf dst v) rest p
  (* Set/mangle: verdict-neutral.  The written value (the operand register) is a
     packet/meta/ct side effect outside the single-packet verdict model, so it is
     dropped here.  The proof therefore certifies these statements preserve the
     verdict; that the emitted bytecode writes the *right* value is covered by the
     differential corpus, not by Rocq. *)
  | IPayloadWrite _ _ _ _ _ _ _ :: rest => run_rule rf rest p
  | IMetaSet _ _ :: rest => run_rule rf rest p
  | ICtSet _ _ :: rest => run_rule rf rest p
  | ILookupVal keys name dreg :: rest =>
      run_rule (set_reg rf dreg (map_lookup_data (List.concat (map rf keys))
                                                 (e_map (pkt_env p) name))) rest p
  | INat _ _ _ _ _ _ _ :: _ => Some Accept   (* terminal *)
  | ITproxy _ _ _ :: _ => Some Accept        (* terminal redirect *)
  | IFwd _ _ _ :: _ => Some Accept           (* terminal forward *)
  | IQueueSreg _ _ _ :: _ => Some Accept     (* terminal queue *)
  | ILimit spec :: rest =>
      (* the limit instruction carries NFT_LIMIT_F_INV (bit 0 of ls_flags); the
         kernel BREAKs iff [under_test ^ invert].  Continue iff [match] = the
         negation, i.e. iff the matchcond body is true. *)
      if xorb (Nat.eqb (Nat.land (ls_flags spec) 1) 1) (lim_under p spec)
      then run_rule rf rest p else None
  | IQuota spec :: rest =>
      if xorb (Nat.eqb (Nat.land (q_flags spec) 1) 1) (quota_under p spec)
      then run_rule rf rest p else None
  | IConnlimit spec :: rest =>
      if xorb (Nat.eqb (Nat.land (cl_flags spec) 1) 1) (connlimit_under p spec)
      then run_rule rf rest p else None
  | ICounter _ _ :: rest => run_rule rf rest p   (* verdict-neutral *)
  (* `notrack` is verdict-neutral but forces IP_CT_UNTRACKED for the rest of this
     rule's traversal: thread [set_untracked] so a later [ICtLoad CKstate] reads
     the untracked bit (lock-step with [rule_applies_walk]'s [SNotrack]). *)
  | INotrack :: rest      => run_rule rf rest (set_untracked p)
  | ILog _ :: rest        => run_rule rf rest p
  | IObjref _ _ :: rest   => run_rule rf rest p   (* verdict-neutral *)
  | ISynproxy _ _ :: rest =>
      (* SYN-proxy: a non-TCP packet BREAKs the rule (NFT_BREAK); a TCP packet with
         SYN or ACK set STOPS traversal (NF_STOLEN/NF_DROP, modelled as terminal
         Drop); any other TCP packet falls through (NFT_CONTINUE).  See
         [synproxy_loadable]/[synproxy_stops]. *)
      if synproxy_loadable p
      then (if synproxy_stops p then Some Drop else run_rule rf rest p)
      else None
  | ILast _ :: rest       => run_rule rf rest p
  | IDynset _ _ _ _ _ :: rest => run_rule rf rest p   (* verdict-neutral *)
  | IExthdrReset _ _ :: rest => run_rule rf rest p (* verdict-neutral *)
  | IDup _ _ :: rest      => run_rule rf rest p   (* verdict-neutral *)
  | IObjrefMap _ _ :: rest => run_rule rf rest p  (* verdict-neutral *)
  | ICtSetDir _ _ _ :: rest => run_rule rf rest p (* verdict-neutral *)
  | IExthdrWrite _ _ _ _ _ :: rest => run_rule rf rest p (* verdict-neutral *)
  | IReject t c :: _ => Some (Reject t c)
  | IQueue lo hi b f :: _ => Some (Queue lo hi b f)
  | IImmediate v :: _ => Some v
  end.

(** Run a base chain's program: ordered per-rule programs, each from a fresh
    (empty) register file, stopping at the first terminal verdict. *)
Fixpoint run_program (prog : program) (p : packet) : option verdict :=
  match prog with
  | [] => None
  | rp :: rest =>
      match run_rule empty_rf rp p with
      | Some v => if terminal v then Some v else run_program rest p
      | None   => run_program rest p
      end
  end.

Definition run_chain (prog : program) (policy : verdict) (p : packet) : verdict :=
  match run_program prog p with
  | Some v => v
  | None   => policy
  end.

(** ** Phase B: in-traversal mutation (meta/ct set visible to later rules).

    A `meta mark set X` does not change *this* rule's verdict, but it mutates the
    packet's metadata that a *later* rule reads.  Modelling this requires threading
    a mutated packet across rules.  We do so additively, leaving the verdict-only
    semantics above intact: [run_rule_writes] is the VM's meta/ct effect over a
    rule's bytecode (mirrors [run_rule] but returns the mutated packet), [dsl_writes]
    is the declarative effect, and [eval_chain_mut]/[run_chain_mut] thread them. *)

Definition meta_eq_dec : forall a b : meta_key, {a = b} + {a <> b}.
Proof. decide equality. Defined.
Definition ct_eq_dec : forall a b : ct_key, {a = b} + {a <> b}.
Proof. decide equality. Defined.
Definition meta_eqb (a b : meta_key) : bool := if meta_eq_dec a b then true else false.
Definition ct_eqb (a b : ct_key) : bool := if ct_eq_dec a b then true else false.

(** Update one metadata / conntrack key, leaving every other field of the packet
    (incl. the named-set environment) unchanged. *)
Definition set_meta (p : packet) (k : meta_key) (v : data) : packet :=
  with_pkt_meta p (fun k' => if meta_eqb k k' then v else pkt_meta p k').
(** Update the SHARED, flow-keyed conntrack table [e_ct] of an env: write [v] at
    flow [fl], key [k], leaving every other (flow,key) entry — and every other env
    component — unchanged.  This is the env analogue of [env_set_upd]/[env_map_upd]
    for the conntrack-entry state, mirroring the kernel's
    WRITE_ONCE(ct->mark/secmark, v) into the entry [nf_ct_get(skb)] selects. *)
Definition env_ct_upd (e : env) (fl : data) (k : ct_key) (v : data) : env :=
  with_e_ct e
    (fun fl' k' =>
       if andb (data_eqb fl fl') (ct_eqb k k') then v else e_ct e fl' k').

(** Update the SHARED, flow-keyed NAT-mapping table [e_nat] of an env: STORE the
    established translation [m] at flow [fl], leaving every other flow's mapping —
    and every other env component — unchanged.  This is the env analogue of
    [env_ct_upd] for the NAT tuple, mirroring the kernel's
    nf_conntrack_alter_reply / store-into-conntrack-entry in [nf_nat_setup_info]
    that records the translation on the FIRST (unconfirmed) packet of a flow. *)
Definition env_nat_upd (e : env) (fl : data)
                       (m : option data * option data * option nat * option data) : env :=
  with_e_nat e (fun fl' => if data_eqb fl fl' then Some m else e_nat e fl').

(** Set a conntrack key.  The value is stored into the SHARED, flow-keyed
    conntrack table [e_ct] at THIS packet's flow ([pkt_flow]), so a later packet of
    the same flow reads it back via [do_load]'s [LCt] case — the cross-packet
    conntrack-entry persistence the kernel implements with
    WRITE_ONCE(ct->mark)/READ_ONCE(ct->mark) on the entry [nf_ct_get(skb)] selects.
    The kernel only ever lets a rule WRITE the persistent keys ([ct_writable]:
    mark/label); a read-only key has no setter, so a [set_ct] on one would never be
    emitted by the parser — but routing it through the same flow table (rather than a
    dead per-packet oracle) keeps the write faithful and the DSL/VM in lock-step.

    KERNEL GUARD (nft_ct.c:288-290, nft_ct_set_eval):
    [ct = nf_ct_get(skb, &ctinfo); if (ct == NULL || nf_ct_is_template(ct)) return;]
    — the SET is a NO-OP when the packet has no conntrack entry.  So we gate the
    write on [pkt_ct_present p]: an entryless packet's `ct mark/label set` leaves
    [e_ct] (and the whole packet) unchanged, exactly mirroring the Round-1 [notrack]
    fix that gated [set_untracked] on the dual guard.  This rules out the
    cross-packet bug where a later same-flow entry-bearing packet would read back a
    mark the kernel never wrote. *)
Definition set_ct (p : packet) (k : ct_key) (v : data) : packet :=
  if pkt_ct_present p then with_pkt_env p (env_ct_upd (pkt_env p) (pkt_flow p) k v)
  else p.

(** Overwrite [len] bytes at offset [off] of a byte list (a header), keeping the
    rest — the payload-write primitive. *)
Definition splice (l : list byte) (off len : nat) (v : data) : list byte :=
  firstn off l ++ v ++ skipn (off + len) l.

(** Rewrite [len] bytes of the network header at [off] to [v], leaving every
    other packet component intact — the address-NAT write primitive shared by
    source- and destination-NAT.  Callers pass the family-dependent
    ([off],[len]) of the address slot, so the kernel's [NF_NAT_MANIP_{SRC,DST}]
    over the right geometry (32-bit IPv4 vs 128-bit IPv6 — netlink_linearize.c
    [nat_addrlen]) is modelled exactly, with the header length preserved
    ([splice]'s [len] = the family addr length). *)
Definition set_nh_field (p : packet) (off len : nat) (v : data) : packet :=
  with_pkt_nh p (splice (pkt_nh p) off len v).

(** Rewrite [len] bytes of the TRANSPORT header at [off] to [v], leaving every
    other packet component intact — the L4-port-NAT write primitive.  This is the
    transport-header analogue of [set_nh_field]: the kernel's
    [nf_nat_proto.c]/[tcp_manip_pkt] writes the new port into the TCP/UDP header
    (`*portptr = newport`) while [set_nh_field] handled the L3 address.  Callers
    pass the L4 port slot ([FThSport] @0 len 2 / [FThDport] @2 len 2). *)
Definition set_th_field (p : packet) (off len : nat) (v : data) : packet :=
  with_pkt_th p (splice (pkt_th p) off len v).

(** Source-port-NAT a packet: rewrite the L4 SOURCE port ([FThSport] = transport
    bytes 0..1) to [v].  This is the port half of a `snat ... :PORT` /
    `masquerade to :PORT` (kernel [NF_NAT_MANIP_SRC] proto). *)
Definition set_sport (p : packet) (v : data) : packet := set_th_field p 0 2 v.

(** Destination-port-NAT a packet: rewrite the L4 DESTINATION port ([FThDport] =
    transport bytes 2..3) to [v].  This is the port half of a `dnat to A:PORT` /
    `redirect to :PORT` (kernel [NF_NAT_MANIP_DST] proto: `*portptr = newport`,
    nf_nat_proto.c:163-172). *)
Definition set_dport (p : packet) (v : data) : packet := set_th_field p 2 2 v.

(** KNOWN APPROXIMATION (below resolution): the L4 (TCP/UDP) CHECKSUM is NOT
    updated by [set_sport]/[set_dport] (the PORT-driven part).  The kernel's
    [tcp_manip_pkt]/[udp_manip_pkt] run
    [inet_proto_csum_replace2(&hdr->check, oldport, newport)] (nf_nat_proto.c:177/57)
    for the port change too; modelling THAT faithfully would need the new port's
    contribution folded into the same slot.  CRUCIALLY, [set_sport]/[set_dport]
    only ever splice the 2-byte PORT slot, so the model NEVER PROVES the L4
    checksum is unchanged across a PORT rewrite that the kernel would update — it
    simply does not assert anything about those bytes.

    By contrast the ADDRESS-driven part of the L4 checksum IS modelled (below,
    [set_l4_csum_addr] threaded into [set_saddr]/[set_daddr]): the L4 (TCP/UDP)
    checksum covers the IPv4/IPv6 pseudo-header, which includes the L3 addresses,
    so a `dnat`/`snat` that changes ONLY the address still changes the L4 checksum
    in real nftables — [nf_nat_ipv4_manip_pkt] ALWAYS runs [l4proto_manip_pkt]
    (which calls [nf_csum_update] -> [inet_proto_csum_replace4(check,...,oldip,newip)])
    BEFORE the address splice (nf_nat_proto.c:324,177,417), INDEPENDENT of any port
    change.  Leaving the L4 checksum byte-for-byte stale after an address-only
    rewrite was a reachable CERTIFIED falsehood (the model could prove the TCP
    checksum unchanged), so the address part is now folded in, exactly like the
    IPv4 L3 header checksum (bytes 10..11, [set_nh_addr_ip4]). *)

(** The (offset, length) of the L4 (TCP/UDP) checksum slot inside the transport
    header, chosen by the L4 protocol number ([pkt_meta MKl4proto], read via
    [FMetaL4proto] = a 1-byte string): TCP (6) keeps its checksum at transport
    bytes 16..17 (`struct tcphdr.check`), UDP (17) at 6..7 (`struct udphdr.check`).
    Any other protocol (no L4 checksum the kernel's [l4proto_manip_pkt] would
    fix — ICMP/GRE/…) yields [None], so the address rewrite leaves the transport
    header untouched (the kernel's `default: return true` of [l4proto_manip_pkt]).

    The boolean is the checksum's MANDATORY flag: TCP (6) always carries a checksum
    (the field is mandatory, do_csum is implicitly true in [tcp_manip_pkt]), so it
    is [true]; UDP (17) MAY disable its checksum by leaving the field zero (RFC 768,
    legal for IPv4), and [udp_manip_pkt] passes `do_csum = !!hdr->check` — the
    checksum is updated ONLY when the existing field is non-zero — so it is [false].
    A zero UDP checksum ("checksum disabled") must be left byte-for-byte zero. *)
Definition l4_csum_slot (l4proto : data) : option (nat * nat * bool) :=
  match l4proto with
  | p :: nil =>
      if Nat.eqb p 6 then Some (16, 2, true)        (* IPPROTO_TCP -> tcphdr.check @16, mandatory *)
      else if Nat.eqb p 17 then Some (6, 2, false)  (* IPPROTO_UDP -> udphdr.check  @6,  optional *)
      else None
  | _ => None
  end.

(** Whenever [l4_csum_slot] returns a slot, it starts at offset >= 6 (TCP @16,
    UDP @6) and has length 2 — so it lies strictly after the L4 PORT slots and
    the checksum is a 2-byte field. *)
Lemma l4_csum_slot_geom : forall l4 coff clen mand,
  l4_csum_slot l4 = Some (coff, clen, mand) -> 6 <= coff /\ clen = 2.
Proof.
  intros l4 coff clen mand H. unfold l4_csum_slot in H.
  destruct l4 as [|p [|b rest]]; try discriminate.
  destruct (Nat.eqb p 6); [injection H as <- <- _; split; lia|].
  destruct (Nat.eqb p 17); [injection H as <- <- _; split; lia| discriminate].
Qed.

(** Update the L4 (TCP/UDP) checksum for an L3-ADDRESS change [old -> new] (the
    pseudo-header that the L4 checksum covers includes the addresses), mirroring
    [nf_csum_update] -> [inet_proto_csum_replace4(check, skb, oldip, newip, true)]
    (nf_nat_proto.c:417).  Applies ONLY when (a) the kernel actually has an L4
    header to fix ([pkt_have_l4 p], i.e. NFT_PKTINFO_L4PROTO was set — the same
    flag [read_payload_ok] gates a transport load on), (b) the L4 protocol has a
    checksum slot ([l4_csum_slot] = Some), and (c) the transport header is long
    enough to hold that slot.  Otherwise the transport header is left unchanged
    (the kernel's `if (hdrsize < sizeof hdr) return true;` / unknown-proto
    fall-through).  [old]/[new] are the address byte strings (4 bytes for IPv4,
    16 for IPv6); [csum_update_field] folds every 16-bit word of the delta into
    the slot, the RFC-1624 incremental update the kernel performs word by word. *)
Definition set_l4_csum_addr (p : packet) (old new : data) : packet :=
  match l4_csum_slot (pkt_meta p MKl4proto) with
  | Some (coff, clen, mand) =>
      if andb (pkt_have_l4 p) (Nat.leb (coff + clen) (List.length (pkt_th p)))
      then let ck0 := slice (pkt_th p) coff clen in
           (* UDP (mand=false) with a zero checksum field is "checksum disabled"
              (RFC 768); [udp_manip_pkt] passes do_csum = !!hdr->check and guards
              the whole update under `if (do_csum)`, leaving a zero checksum zero.
              TCP (mand=true) always updates. *)
           if andb (negb mand) (N.eqb (data_to_N ck0) 0)
           then p
           else let ck1 := csum_update_field ck0 old new in
                set_th_field p coff clen ck1
      else p
  | None => p
  end.

(** [set_l4_csum_addr] leaves the network header (and the L4 PORT slots 0..1/2..3,
    disjoint from the TCP @16 / UDP @6 checksum slots) untouched: it only ever
    splices the 2-byte checksum slot of the transport header. *)
Lemma set_l4_csum_addr_nh : forall p old new,
  pkt_nh (set_l4_csum_addr p old new) = pkt_nh p.
Proof.
  intros p old new. unfold set_l4_csum_addr.
  destruct (l4_csum_slot (pkt_meta p MKl4proto)) as [[[coff clen] mand]|]; [|reflexivity].
  destruct (pkt_have_l4 p && Nat.leb (coff + clen) (List.length (pkt_th p)));
    [|reflexivity].
  destruct (negb mand && N.eqb (data_to_N (slice (pkt_th p) coff clen)) 0);
    reflexivity.
Qed.

(** [set_l4_csum_addr] preserves the LENGTH of the transport header: the only
    write is a [splice] of a 2-byte checksum into a slot the guard proved fits,
    and [splice] preserves length when the spliced region lies within bounds. *)
Lemma set_l4_csum_addr_th_len : forall p old new,
  List.length (pkt_th (set_l4_csum_addr p old new)) = List.length (pkt_th p).
Proof.
  intros p old new. unfold set_l4_csum_addr.
  destruct (l4_csum_slot (pkt_meta p MKl4proto)) as [[[coff clen] mand]|] eqn:Hslot;
    [|reflexivity].
  destruct (pkt_have_l4 p && Nat.leb (coff + clen) (List.length (pkt_th p))) eqn:Hg;
    [|reflexivity].
  destruct (negb mand && N.eqb (data_to_N (slice (pkt_th p) coff clen)) 0);
    [reflexivity|].
  apply andb_true_iff in Hg as [_ Hlen]. apply PeanoNat.Nat.leb_le in Hlen.
  apply l4_csum_slot_geom in Hslot as [_ Hclen]. subst clen.
  cbn [set_th_field with_pkt_th pkt_th]. unfold splice.
  rewrite !length_app, length_firstn, length_skipn.
  rewrite csum_update_field_length. lia.
Qed.

(** The (offset, length) of the L3 source / destination address slot for a NAT
    [family] ("ip" = IPv4: src @12 len 4 / dst @16 len 4, where [FIp4Saddr] /
    [FIp4Daddr] read; "ip6" = IPv6: src @8 len 16 / dst @24 len 16, where
    [FIp6Saddr] / [FIp6Daddr] read).  The kernel chooses 32 vs 128 bits by family
    ([nat_addrlen], netlink_linearize.c:1237). *)
Definition saddr_slot (family : String.string) : nat * nat :=
  if String.eqb family nat_fam_ip6 then (8, 16) else (12, 4).
Definition daddr_slot (family : String.string) : nat * nat :=
  if String.eqb family nat_fam_ip6 then (24, 16) else (16, 4).

(** The IPv4 header checksum field lives at network-header bytes 10..11.  After a
    NAT address rewrite the kernel does NOT leave it stale: [nf_nat_ipv4_manip_pkt]
    (nf_nat_proto.c:329-333) calls [csum_replace4(&iph->check, old_addr, new_addr)]
    — an RFC-1624 incremental update — in the SAME step as writing the new address.
    [ip_check_off]/[ip_check_len] name that slot; [set_ip_check] splices the
    incrementally-updated 2-byte checksum (computed from the old/new address words)
    into it, modelling [csum_replace4].  IPv6 has NO L3 header checksum, so only the
    IPv4 family updates it. *)
Definition ip_check_off : nat := 10.
Definition ip_check_len : nat := 2.

(** Rewrite [len] bytes of the network header at [off] to [v] AND incrementally
    update the IPv4 header checksum (bytes 10..11) for the change from the OLD
    bytes at that slot to [v] — the address-NAT write primitive that mirrors the
    kernel's combined `iph->daddr = ...; csum_replace4(&iph->check, old, new)`.
    The old field is read from the (pre-write) network header; the new checksum is
    [csum_update_field] over (old field, new field).  Only the address slot is
    touched besides the checksum, so the header length is preserved. *)
Definition set_nh_addr_ip4 (p : packet) (off len : nat) (v : data) : packet :=
  let nh   := pkt_nh p in
  let old  := slice nh off len in
  let nh1  := splice nh off len v in
  let ck0  := slice nh1 ip_check_off ip_check_len in
  let ck1  := csum_update_field ck0 old v in
  let nh2  := splice nh1 ip_check_off ip_check_len ck1 in
  with_pkt_nh p nh2.

(** [set_nh_addr_ip4] leaves the transport header untouched. *)
Lemma set_nh_addr_ip4_th : forall p off len v,
  pkt_th (set_nh_addr_ip4 p off len v) = pkt_th p.
Proof. reflexivity. Qed.

(** Splicing [w] (|w|=2) at offset 10 and then reading [len] bytes at [off] with
    [off >= 12] returns the same bytes as reading [off]/[len] from the unspliced
    list (the checksum slot 10..11 is disjoint from an address slot at >= 12). *)
Lemma slice_splice_after : forall l w off len,
  List.length w = ip_check_len ->
  ip_check_off + ip_check_len <= off ->
  slice (splice l ip_check_off ip_check_len w) off len = slice l off len.
Proof.
  intros l w off len Hw Hoff. unfold slice, splice, ip_check_off, ip_check_len in *.
  assert (Hcase : 10 <= List.length l \/ List.length l < 10) by lia.
  destruct Hcase as [Hlong|Hshort].
  2:{ (* l too short: firstn 10 l = l, skipn 12 l = [], so splice = l ++ w *)
    rewrite (firstn_all2 l) by lia. rewrite (skipn_all2 l) by lia.
    rewrite app_nil_r.
    rewrite (skipn_all2 (l ++ w)) by (rewrite length_app; lia).
    rewrite (skipn_all2 l) by lia.
    cbn [firstn]. reflexivity. }
  assert (Hf10 : List.length (firstn 10 l) = 10) by (rewrite firstn_length_le; lia).
  rewrite skipn_app, Hf10.
  rewrite (skipn_all2 (firstn 10 l)) by (rewrite Hf10; lia). cbn [app].
  rewrite skipn_app, Hw.
  rewrite (skipn_all2 w) by lia.
  cbn [app].
  rewrite skipn_skipn.
  replace (off - 10 - 2 + (10 + 2)) with off by lia.
  reflexivity.
Qed.

(** Source-NAT a packet: rewrite its source address (the [saddr_slot] for the
    NAT [family]) to [v].  This is the data-plane effect a `snat`/`masquerade`
    performs; [set_saddr "ip" p (e_ifaddr (pkt_env p) oifname)] realises
    `masquerade` = "use the IP of the interface the packet exits".  For IPv4 the
    IP header checksum is incrementally updated ([set_nh_addr_ip4], mirroring
    [csum_replace4]); IPv6 has no L3 checksum so it is a bare slot splice. *)
Definition set_saddr (family : String.string) (p : packet) (v : data) : packet :=
  let '(off, len) := saddr_slot family in
  let old := slice (pkt_nh p) off len in
  let p1 :=
    if String.eqb family nat_fam_ip6 then set_nh_field p off len v
    else set_nh_addr_ip4 p off len v in
  set_l4_csum_addr p1 old v.

(** Destination-NAT a packet: rewrite its destination address (the [daddr_slot]
    for the NAT [family]) to [v].  This is the data-plane effect a
    `dnat`/`redirect` performs — the kernel `nft_nat` applies [NF_NAT_MANIP_DST]
    from [NFTNL_EXPR_NAT_REG_ADDR_MIN] (netlink_linearize.c:1304), and
    [nf_nat_ipv4_manip_pkt] also runs [csum_replace4] on the IPv4 header checksum. *)
Definition set_daddr (family : String.string) (p : packet) (v : data) : packet :=
  let '(off, len) := daddr_slot family in
  let old := slice (pkt_nh p) off len in
  let p1 :=
    if String.eqb family nat_fam_ip6 then set_nh_field p off len v
    else set_nh_addr_ip4 p off len v in
  set_l4_csum_addr p1 old v.

(** Reading a slot [poff..poff+plen) that ends at or before the splice offset
    [soff] (i.e. [poff + plen <= soff]) is unaffected by [splice l soff slen w]
    — the spliced region lies strictly after the read.  Used to show the L4 PORT
    slots (0..1 / 2..3) survive the L4-checksum splice (TCP @16 / UDP @6). *)
Lemma slice_splice_before : forall l w soff slen poff plen,
  poff + plen <= soff ->
  soff <= List.length l ->
  slice (splice l soff slen w) poff plen = slice l poff plen.
Proof.
  intros l w soff slen poff plen Hle Hsoff. unfold slice, splice.
  (* The read [poff..poff+plen) lies inside [firstn soff l]: reduce both sides
     to a read of that prefix.  Key: firstn (poff+plen) commutes with the splice
     because poff+plen <= soff <= |firstn soff l ++ ...|. *)
  rewrite (firstn_skipn_comm plen poff).
  rewrite (firstn_skipn_comm plen poff l).
  f_equal.
  (* firstn (poff+plen) (firstn soff l ++ w ++ ...) = firstn (poff+plen) l *)
  rewrite firstn_app, firstn_length_le by lia.
  replace (poff + plen - soff) with 0 by lia. cbn [firstn]. rewrite app_nil_r.
  rewrite firstn_firstn. f_equal. lia.
Qed.

(** [set_l4_csum_addr] preserves the L4 PORT slots: reading any [poff..poff+plen)
    with [poff + plen <= 6] (covers sport @0..1 and dport @2..3) returns the same
    bytes — the checksum splice (TCP @16 / UDP @6) lies after the ports. *)
Lemma slice_set_l4_csum_addr_port : forall p old new poff plen,
  poff + plen <= 6 ->
  slice (pkt_th (set_l4_csum_addr p old new)) poff plen = slice (pkt_th p) poff plen.
Proof.
  intros p old new poff plen Hle. unfold set_l4_csum_addr.
  destruct (l4_csum_slot (pkt_meta p MKl4proto)) as [[[coff clen] mand]|] eqn:Hslot;
    [|reflexivity].
  destruct (pkt_have_l4 p && Nat.leb (coff + clen) (List.length (pkt_th p))) eqn:Hg;
    [|reflexivity].
  destruct (negb mand && N.eqb (data_to_N (slice (pkt_th p) coff clen)) 0);
    [reflexivity|].
  cbn [set_th_field pkt_th].
  apply andb_true_iff in Hg as [_ Hlen]. apply PeanoNat.Nat.leb_le in Hlen.
  (* coff is 16 (TCP) or 6 (UDP); poff+plen <= 6 <= coff, and coff <= |pkt_th| *)
  apply l4_csum_slot_geom in Hslot as [Hge Hclen]. subst clen.
  apply slice_splice_before; lia.
Qed.

(** [set_saddr]/[set_daddr] preserve the L4 PORT slots (sport @0..1, dport @2..3):
    the address rewrite + L4-checksum update only ever touch the network header,
    the IPv4 header checksum, and the L4 CHECKSUM slot (TCP @16 / UDP @6) — never
    the ports.  (Below the resolution where the kernel ALSO folds the port change
    into the L4 checksum, see [set_sport]/[set_dport]'s note: the model's NAT-addr
    rewrite leaves the port bytes themselves byte-for-byte, which is faithful.) *)
Lemma set_saddr_th_port : forall fam p v poff plen,
  poff + plen <= 6 ->
  slice (pkt_th (set_saddr fam p v)) poff plen = slice (pkt_th p) poff plen.
Proof.
  intros fam p v poff plen Hle. unfold set_saddr.
  destruct (saddr_slot fam) as [off len].
  rewrite slice_set_l4_csum_addr_port by lia.
  destruct (String.eqb fam nat_fam_ip6); reflexivity.
Qed.
Lemma set_daddr_th_port : forall fam p v poff plen,
  poff + plen <= 6 ->
  slice (pkt_th (set_daddr fam p v)) poff plen = slice (pkt_th p) poff plen.
Proof.
  intros fam p v poff plen Hle. unfold set_daddr.
  destruct (daddr_slot fam) as [off len].
  rewrite slice_set_l4_csum_addr_port by lia.
  destruct (String.eqb fam nat_fam_ip6); reflexivity.
Qed.

(** [set_saddr]/[set_daddr] preserve the LENGTH of the transport header (the
    address splice never touches [pkt_th]; the L4-checksum splice is in-bounds). *)
Lemma set_saddr_th_len : forall fam p v,
  List.length (pkt_th (set_saddr fam p v)) = List.length (pkt_th p).
Proof.
  intros fam p v. unfold set_saddr. destruct (saddr_slot fam) as [off len].
  rewrite set_l4_csum_addr_th_len.
  destruct (String.eqb fam nat_fam_ip6); reflexivity.
Qed.
Lemma set_daddr_th_len : forall fam p v,
  List.length (pkt_th (set_daddr fam p v)) = List.length (pkt_th p).
Proof.
  intros fam p v. unfold set_daddr. destruct (daddr_slot fam) as [off len].
  rewrite set_l4_csum_addr_th_len.
  destruct (String.eqb fam nat_fam_ip6); reflexivity.
Qed.

(** Reading the network-header bytes [off..off+len) back after an IPv4 address
    rewrite at the SAME slot [off]/[len] (with [off >= 12], i.e. either the source
    @12 or destination @16 slot, disjoint from the checksum @10..11) yields [v] —
    the address survives, the checksum update doesn't disturb it. *)
Lemma slice_set_nh_addr_ip4_same : forall p off len v,
  12 <= off ->
  List.length v = len ->
  off + len <= List.length (pkt_nh p) ->
  slice (pkt_nh (set_nh_addr_ip4 p off len v)) off len = v.
Proof.
  intros p off len v Hoff Hv Hlen.
  unfold set_nh_addr_ip4; cbn [with_pkt_nh pkt_nh].
  rewrite slice_splice_after
    by (unfold ip_check_off, ip_check_len; try apply csum_update_field_length; lia).
  unfold slice, splice.
  assert (Hf : List.length (firstn off (pkt_nh p)) = off)
    by (apply firstn_length_le; lia).
  rewrite skipn_app, Hf.
  rewrite (skipn_all2 (firstn off (pkt_nh p))) by (rewrite Hf; lia). cbn [app].
  replace (off - off) with 0 by lia. rewrite skipn_O.
  rewrite firstn_app. rewrite Hv. replace (len - len) with 0 by lia.
  rewrite firstn_O, app_nil_r.
  apply firstn_all2. lia.
Qed.

(** The network header after [set_saddr]/[set_daddr] is EXACTLY the address-splice
    result: the trailing L4-checksum update ([set_l4_csum_addr]) touches only the
    transport header.  So a network-header read back through the full NAT rewrite
    is the read back through the inner splice. *)
Lemma set_saddr_nh : forall fam p v,
  pkt_nh (set_saddr fam p v)
    = (let '(off, len) := saddr_slot fam in
       if String.eqb fam nat_fam_ip6 then pkt_nh (set_nh_field p off len v)
       else pkt_nh (set_nh_addr_ip4 p off len v)).
Proof.
  intros fam p v. unfold set_saddr. destruct (saddr_slot fam) as [off len].
  rewrite set_l4_csum_addr_nh.
  destruct (String.eqb fam nat_fam_ip6); reflexivity.
Qed.
Lemma set_daddr_nh : forall fam p v,
  pkt_nh (set_daddr fam p v)
    = (let '(off, len) := daddr_slot fam in
       if String.eqb fam nat_fam_ip6 then pkt_nh (set_nh_field p off len v)
       else pkt_nh (set_nh_addr_ip4 p off len v)).
Proof.
  intros fam p v. unfold set_daddr. destruct (daddr_slot fam) as [off len].
  rewrite set_l4_csum_addr_nh.
  destruct (String.eqb fam nat_fam_ip6); reflexivity.
Qed.

(** IPv4 source/destination address read-back through the FULL NAT rewrite
    (address splice + L3 checksum update + L4 checksum update): the address slot
    survives byte-for-byte. *)
Lemma slice_set_saddr_ip4_same : forall p v,
  16 <= List.length (pkt_nh p) -> List.length v = 4 ->
  slice (pkt_nh (set_saddr nat_fam_ip4 p v)) 12 4 = v.
Proof.
  intros p v Hlen Hv. rewrite set_saddr_nh. change (saddr_slot nat_fam_ip4) with (12, 4).
  change (String.eqb nat_fam_ip4 nat_fam_ip6) with false; cbv iota.
  apply slice_set_nh_addr_ip4_same; lia.
Qed.
Lemma slice_set_daddr_ip4_same : forall p v,
  20 <= List.length (pkt_nh p) -> List.length v = 4 ->
  slice (pkt_nh (set_daddr nat_fam_ip4 p v)) 16 4 = v.
Proof.
  intros p v Hlen Hv. rewrite set_daddr_nh. change (daddr_slot nat_fam_ip4) with (16, 4).
  change (String.eqb nat_fam_ip4 nat_fam_ip6) with false; cbv iota.
  apply slice_set_nh_addr_ip4_same; lia.
Qed.

(** ** Dynamic sets: the `dynset` feedback loop (`add`/`update`/`delete @s {key}`).

    Unlike a meta/ct set (which mutates a packet field), a dynset mutates the
    NAMED SET STATE in the environment, so a *later* rule's `lookup @s` observes
    the element this rule inserted (or removed) — the whole point of dynamic sets
    (per-key rate limiting, learning sets, …).  [env_set_upd] applies that effect
    to the env: `add`/`update` prepend the exact interval [key,key] (so [set_mem]
    on [key] now succeeds — exact element, cf. the set/interval model), `delete`
    drops the exact [key,key] elements.  Every other component of the env (maps,
    routes, limiters) and of the packet is unchanged. *)
Definition env_set_upd (e : env) (op name : String.string) (key : data) : env :=
  with_e_set e
    (fun n =>
       if String.eqb n name
       then if String.eqb op op_delete
            then filter (fun lh => negb (andb (data_eqb (fst lh) key) (data_eqb (snd lh) key)))
                        (e_set e n)
            else (key, key) :: e_set e n
       else e_set e n).

Definition set_env_dynset (p : packet) (op name : String.string) (key : data) : packet :=
  with_pkt_env p (env_set_upd (pkt_env p) op name key).

(** The map analogue: a `dynset` whose target is a MAP (`add @m {key : data}`)
    learns the entry [key -> data] in the named value-map [e_map], so a later
    `@m`-keyed lookup (map value / verdict map) sees it.  add/update prepend the
    entry (so [map_lookup_data] finds the freshest first), delete drops entries
    with that key. *)
Definition env_map_upd (e : env) (op name : String.string) (key dat : data) : env :=
  with_e_map e
    (fun n =>
       if String.eqb n name
       then if String.eqb op op_delete
            then filter (fun kv => negb (data_eqb (fst kv) key)) (e_map e n)
            else (key, dat) :: e_map e n
       else e_map e n).

Definition set_env_dynset_map (p : packet) (op name : String.string) (key dat : data) : packet :=
  with_pkt_env p (env_map_upd (pkt_env p) op name key dat).

(** The VM's meta/ct effect of running one rule's bytecode: mirrors [run_rule]'s
    register threading, but instead of a verdict it returns the packet with the
    [IMetaSet]/[ICtSet] writes applied (in execution order; a write only happens
    once the matches before it have passed — a failed cmp/lookup/limit returns the
    packet unchanged, exactly as the verdict run breaks). *)
Fixpoint run_rule_writes (rf : regfile) (is : list instr) (p : packet) : packet :=
  match is with
  | [] => p
  | IMetaLoad k dst :: rest => run_rule_writes (set_reg rf dst (pkt_meta p k)) rest p
  | ICtLoad k dst :: rest =>
      (* a conntrack load on a no-entry packet ([pkt_ct_present = false]) breaks the
         rule for every key except [CKstate] (NFT_BREAK): no later statement runs and
         the packet is returned unchanged — mirrors [run_rule] and the payload guard. *)
      if load_ok (LCt k) p
      then run_rule_writes (set_reg rf dst (do_load (LCt k) p)) rest p
      else p
  | IRtLoad k dst :: rest => run_rule_writes (set_reg rf dst (e_rt (pkt_env p) k)) rest p
  | ISocketLoad k dst :: rest => run_rule_writes (set_reg rf dst (pkt_sock p k)) rest p
  | INumgen spec dst :: rest =>
      (* per-instruction: verdict-/packet-neutral (reads the shared counter value).
         The cross-packet counter ADVANCE is applied by [numgen_sweep_prog] at the
         mutation-evaluator boundary, so the per-instruction write lock-step (and the
         whole load-fields machinery) is preserved. *)
      run_rule_writes (set_reg rf dst (do_load (LNumgen spec) p)) rest p
  | IOsf dst :: rest => run_rule_writes (set_reg rf dst (pkt_osf p)) rest p
  | IExthdrLoad ep h o l pr dst :: rest =>
      (* a VALUE load of an absent exthdr/option breaks the rule (NFT_BREAK): no
         later statement runs, the packet is returned unchanged — mirrors
         [run_rule] and the payload guard below. *)
      if load_ok (LExthdr ep h o l pr) p
      then run_rule_writes (set_reg rf dst (pkt_eh p ep h o l pr)) rest p
      else p
  | IFibLoad sel res dst :: rest => run_rule_writes (set_reg rf dst (lpm_fib (e_routes (pkt_env p)) (pkt_fibkey p sel) res)) rest p
  | ICtDirLoad key dir dst :: rest => run_rule_writes (set_reg rf dst (pkt_ctdir p key dir)) rest p
  | IXfrmLoad dir sp key dst :: rest => run_rule_writes (set_reg rf dst (pkt_xfrm p dir sp key)) rest p
  | ITunnelLoad key dst :: rest => run_rule_writes (set_reg rf dst (pkt_tunnel p key)) rest p
  | ISymhash m o dst :: rest => run_rule_writes (set_reg rf dst (pkt_symhash p m o)) rest p
  | IInnerLoad t h fl desc _ dst :: rest =>
      run_rule_writes (set_reg rf dst (pkt_inner p t h fl desc)) rest p
  | IPayloadLoad b o l dst :: rest =>
      (* a broken payload read breaks the rule (NFT_BREAK): no later statement in
         this rule runs, so the packet is returned unchanged — mirrors [run_rule]. *)
      if read_payload_ok b o l p
      then run_rule_writes (set_reg rf dst (read_payload b o l p)) rest p
      else p
  | ICmp op src v :: rest => if eval_cmp op (rf src) v then run_rule_writes rf rest p else p
  | IRange op src lo hi :: rest => if eval_range op (rf src) lo hi then run_rule_writes rf rest p else p
  | IBitwise dst src mask xor :: rest => run_rule_writes (set_reg rf dst (data_bitops (rf src) mask xor)) rest p
  | IBitwiseOr dst src1 src2 :: rest => run_rule_writes (set_reg rf dst (data_or (rf src1) (rf src2))) rest p
  | IBitShift dst src shl amt :: rest => run_rule_writes (set_reg rf dst (data_shift shl amt (rf src))) rest p
  | IByteorder dst src h sz len :: rest => run_rule_writes (set_reg rf dst (data_byteorder h sz len (rf src))) rest p
  | IJhash dst src l s m o :: rest => run_rule_writes (set_reg rf dst (data_jhash l s m o (rf src))) rest p
  | ILookup srcs name neg :: rest =>
      if xorb neg (concat_set_mem (map rf srcs) (e_set (pkt_env p) name))
      then run_rule_writes rf rest p else p
  | IVmap srcs name :: rest =>
      match assoc_verdict (List.concat (map rf srcs)) (e_vmap (pkt_env p) name) with
      | Some _ => p   (* terminal verdict: traversal stops, no later-rule effect *)
      | None   => run_rule_writes rf rest p
      end
  | IImmediateData dst v :: rest => run_rule_writes (set_reg rf dst v) rest p
  | IPayloadWrite _ _ _ _ _ _ _ :: rest => run_rule_writes rf rest p
  | IMetaSet k src :: rest => run_rule_writes rf rest (set_meta p k (rf src))
  | ICtSet k src :: rest => run_rule_writes rf rest (set_ct p k (rf src))
  | ILookupVal keys name dreg :: rest =>
      run_rule_writes (set_reg rf dreg (map_lookup_data (List.concat (map rf keys))
                                                        (e_map (pkt_env p) name))) rest p
  | INat _ _ _ _ _ _ _ :: _ => p
  | ITproxy _ _ _ :: _ => p
  | IFwd _ _ _ :: _ => p
  | IQueueSreg _ _ _ :: _ => p
  | ILimit spec :: rest => if xorb (Nat.eqb (Nat.land (ls_flags spec) 1) 1) (lim_under p spec) then run_rule_writes rf rest p else p
  | IQuota spec :: rest => if xorb (Nat.eqb (Nat.land (q_flags spec) 1) 1) (quota_under p spec) then run_rule_writes rf rest p else p
  | IConnlimit spec :: rest => if xorb (Nat.eqb (Nat.land (cl_flags spec) 1) 1) (connlimit_under p spec) then run_rule_writes rf rest p else p
  | ICounter _ _ :: rest => run_rule_writes rf rest p
  | INotrack :: rest => run_rule_writes rf rest (set_untracked p)
  | ILog _ :: rest => run_rule_writes rf rest p
  | IObjref _ _ :: rest => run_rule_writes rf rest p
  | ISynproxy _ _ :: rest =>
      (* mirrors [run_rule]: a non-TCP packet breaks the rule, a SYN/ACK packet
         stops traversal (terminal) — either way no later statement in this rule
         runs, so the packet is returned unchanged; other TCP packets fall through. *)
      if synproxy_loadable p
      then (if synproxy_stops p then p else run_rule_writes rf rest p)
      else p
  | ILast _ :: rest => run_rule_writes rf rest p
  | IDynset op name keyregs None _ :: rest =>
      (* pure-set dynset: insert/remove the concatenated key in the named set, so a
         LATER rule's lookup sees it (the dynamic-set feedback loop). *)
      run_rule_writes rf rest (set_env_dynset p op name (List.concat (map rf keyregs)))
  | IDynset op name keyregs (Some dreg) true :: rest =>
      (* map dynset whose data is a packet field: learn key -> data in the map. *)
      run_rule_writes rf rest (set_env_dynset_map p op name (List.concat (map rf keyregs)) (rf dreg))
  | IDynset _ _ _ (Some _) false :: rest => run_rule_writes rf rest p   (* immediate-data dynset: env-neutral *)
  | IExthdrReset _ _ :: rest => run_rule_writes rf rest p
  | IDup _ _ :: rest => run_rule_writes rf rest p
  | IObjrefMap _ _ :: rest => run_rule_writes rf rest p
  | ICtSetDir _ _ _ :: rest => run_rule_writes rf rest p
  | IExthdrWrite _ _ _ _ _ :: rest => run_rule_writes rf rest p
  | IReject _ _ :: _ => p
  | IQueue _ _ _ _ :: _ => p
  | IImmediate _ :: _ => p
  end.

(** Is a value-source "simple" (immediate or field)?  These are exactly the
    operands for which the proof establishes value-correctness ([eval_vsrc] =
    the register the bytecode leaves), so the mutation theorem is stated for
    rules whose set-statement operands are simple — the common `meta mark set
    <const>` / `ct mark set <field>` shapes, incl. the set-then-match bug. *)
Definition simple_vsrc (vs : vsrc) : bool :=
  match vs with
  | VImm _ | VField _ _ => true
  | VMap (_ :: _) _ _ => true               (* nonempty-key value map (any key transform) *)
  | VMapT _ _ => true                       (* transformed-concat value map *)
  | VHash (_ :: _) _ _ _ _ => true          (* jhash of a (nonempty) source *)
  | VHashMap (_ :: _) _ _ _ _ _ => true     (* jhash then value-map lookup *)
  | VOr (_ :: _) _ => true                  (* OR-fold of (nonempty) sources *)
  | _ => false   (* only degenerate empty-field operands (which read an incoming
                    register) remain out of scope *)
  end.
(** A body is "simple" for the mutation theorem when every statement is a meta/ct
    set with a simple operand (matches are unrestricted).  Other statements in the
    same rule are out of scope (their value semantics are not modelled). *)
(** A body is well-formed for the mutation theorem when every meta/ct *set*
    statement carries a non-degenerate operand ([simple_vsrc]); ALL other
    statements (mangle, NAT, dup, counter, log, dynset, exthdr, objref, …) and
    all matches are unrestricted — they are packet-neutral for meta/ct and so are
    threaded through verbatim.  (The only exclusion is a malformed zero-field
    jhash/map/or operand, which no real ruleset produces.) *)
Definition simple_body (body : list body_item) : bool :=
  forallb (fun it => match it with
                     | BStmt (SMetaSet _ vs) | BStmt (SCtSet _ vs) => simple_vsrc vs
                     | _ => true
                     end) body.
Definition simple_writes (r : rule) : bool := simple_body (r_body r).

(** The declarative meta/ct effect of one rule's body, processed left-to-right
    exactly as the kernel executes it: a [set] writes [eval_vsrc vs] against the
    packet mutated so far (so a later operand sees an earlier write); a match that
    fails stops execution, keeping the writes made *before* it (statements before a
    failing match still ran).  This mirrors [run_rule_writes] on the compiled body. *)
Fixpoint body_writes (body : list body_item) (p : packet) : packet :=
  match body with
  | [] => p
  | BMatch m :: rest => if eval_matchcond m p then body_writes rest p else p
  (* A mutating statement whose operand load BREAKs (unloadable payload) stops the
     rule's execution before its write, exactly as [run_rule_writes] breaks at the
     operand's [IPayloadLoad] — so no write happens and the packet is returned. *)
  | BStmt (SMetaSet k vs) :: rest =>
      if vsrc_loadable vs p then body_writes rest (set_meta p k (eval_vsrc vs p)) else p
  | BStmt (SCtSet k vs)   :: rest =>
      if vsrc_loadable vs p then body_writes rest (set_ct p k (eval_vsrc vs p)) else p
  | BStmt (SDynset op name keyfs nil) :: rest =>
      (* pure-set dynset: insert/remove the concatenated key in the named set, so a
         later rule's [lookup @name] observes it (cf. [run_rule_writes]'s IDynset). *)
      if fields_loadable keyfs p
      then body_writes rest (set_env_dynset p op name
                               (List.concat (map (fun f => field_value f p) keyfs)))
      else p
  | BStmt (SDynset op name keyfs (d :: ds)) :: rest =>
      (* map dynset with a field-valued data: learn key -> (first data field) in the
         named map.  (Only the first data field is recorded; the corpus never emits a
         multi-field map data, and BOTH sides record exactly this, so DSL = VM.) *)
      if fields_loadable (keyfs ++ d :: ds) p
      then body_writes rest (set_env_dynset_map p op name
                               (List.concat (map (fun f => field_value f p) keyfs))
                               (field_value d p))
      else p
  (* SYN-proxy is meta/ct- and env-neutral, but it BREAKs the rule on a non-TCP
     packet and STOPS (terminal) on a SYN/ACK packet — either way no later
     statement runs (cf. [run_rule_writes]'s ISynproxy); other TCP packets fall
     through. *)
  | BStmt (SSynproxy _ _) :: rest =>
      if synproxy_loadable p
      then (if synproxy_stops p then p else body_writes rest p)
      else p
  (* `notrack` forces the packet's conntrack state to IP_CT_UNTRACKED for the rest of
     this traversal, so a LATER `ct state` read (in this rule or a subsequent rule of
     the same traversal, threaded by [eval_rules_mut]) returns
     NF_CT_STATE_UNTRACKED_BIT (kernel nft_notrack_eval + nft_ct_get_eval).  Mirrors
     [run_rule_writes]'s [INotrack]. *)
  | BStmt SNotrack :: rest => body_writes rest (set_untracked p)
  (* every OTHER statement is meta/ct- and env-neutral, but it still LOADS its
     operand fields; an unloadable load BREAKs the rule (so no later statement
     runs), exactly as [run_rule_writes] breaks at that operand's payload load. *)
  | BStmt s :: rest => if stmt_loadable s p then body_writes rest p else p
  end.
Definition dsl_writes (r : rule) (p : packet) : packet := body_writes (r_body r) p.

(** The full cross-rule effect of running a rule [r] on packet [p] in mutation mode:
    its meta/ct/env writes ([dsl_writes]) AND the depletion of every `limit`/`quota`/
    `connlimit` token bucket it evaluates ([limit_sweep_body]).  The next rule — and,
    through [pkt_env], the next packet of the traversal — observes both, so a rate
    limit actually limits later packets.  (The limit sweep reads/writes only
    [e_limit]/[e_quota]/[e_connlimit], which [dsl_writes] never touches, so the two
    compose order-independently for those fields.) *)
Definition dsl_step (r : rule) (p : packet) : packet :=
  limit_sweep_body (r_body r) (dsl_writes r p).

(** A limit-free rule's [dsl_step] is just its [dsl_writes] (no limiter consumption);
    so every existing rate-limit-free proof about [dsl_writes]/[eval_chain_trace]
    carries over unchanged. *)
Lemma dsl_step_limit_free : forall r p,
  limit_free_body (r_body r) = true -> dsl_step r p = dsl_writes r p.
Proof. intros r p H. unfold dsl_step. apply limit_sweep_body_id, H. Qed.

(** Mutation-aware rule-list evaluation: every non-terminal rule threads its
    writes to the rest, so a later rule observes an earlier `set` (the write
    happens whether or not the rule's verdict matched — a non-applicable rule
    still ran the statements up to its failing match). *)
Fixpoint eval_rules_mut (rs : list rule) (p : packet) : option verdict :=
  match rs with
  | [] => None
  | r :: rest =>
      if rule_loadable r p && rule_applies r p then
        match outcome r p with
        | Some v => if terminal v then Some v else eval_rules_mut rest (dsl_step r p)
        | None   => eval_rules_mut rest (dsl_step r p)
        end
      else eval_rules_mut rest (dsl_step r p)
  end.

Fixpoint run_program_mut (prog : program) (p : packet) : option verdict :=
  match prog with
  | [] => None
  | rp :: rest =>
      (* the packet a rule LEAVES carries its [run_rule_writes] meta/ct/env writes, its
         `numgen inc` counter advance ([numgen_sweep_prog]), AND the depletion of every
         `limit`/`quota`/`connlimit` bucket it evaluated ([limit_sweep_prog]); the next
         rule (and, through the env, the next packet) sees all three. *)
      let p' := limit_sweep_prog rp (numgen_sweep_prog rp (run_rule_writes empty_rf rp p)) in
      match run_rule empty_rf rp p with
      | Some v => if terminal v then Some v else run_program_mut rest p'
      | None   => run_program_mut rest p'
      end
  end.

Definition eval_chain_mut (c : chain) (p : packet) : verdict :=
  match eval_rules_mut (c_rules c) p with Some v => v | None => c_policy c end.
Definition run_chain_mut (prog : program) (policy : verdict) (p : packet) : verdict :=
  match run_program_mut prog p with Some v => v | None => policy end.

(** ** Cross-packet persistence of learned state.

    A `dynset` learns an element into a named set; that learning must persist to
    the NEXT packet (per-source rate limiting, learning sets, …).  Within one
    packet [eval_rules_mut]/[run_program_mut] thread the mutated packet (hence its
    [pkt_env]) across rules; to thread it across PACKETS we expose the final
    environment.  [eval_rules_mut_env]/[run_program_mut_env] mirror the verdict
    evaluators but also return the env left after the chain ran (the shared
    set/map/limiter state, NOT the per-packet meta/ct fields, which are local to
    each packet).  On a terminal verdict the env still reflects the writes the
    final rule's body made before the verdict. *)
Fixpoint eval_rules_mut_env (rs : list rule) (p : packet) : option verdict * env :=
  match rs with
  | [] => (None, pkt_env p)
  | r :: rest =>
      if rule_loadable r p && rule_applies r p then
        match outcome r p with
        | Some v => if terminal v then (Some v, pkt_env (dsl_step r p))
                    else eval_rules_mut_env rest (dsl_step r p)
        | None   => eval_rules_mut_env rest (dsl_step r p)
        end
      else eval_rules_mut_env rest (dsl_step r p)
  end.

Fixpoint run_program_mut_env (prog : program) (p : packet) : option verdict * env :=
  match prog with
  | [] => (None, pkt_env p)
  | rp :: rest =>
      let p' := limit_sweep_prog rp (numgen_sweep_prog rp (run_rule_writes empty_rf rp p)) in
      match run_rule empty_rf rp p with
      | Some v => if terminal v then (Some v, pkt_env p')
                  else run_program_mut_env rest p'
      | None   => run_program_mut_env rest p'
      end
  end.

(** Run a base chain in mutation mode, returning the verdict AND the env the chain
    leaves (with any dynset-learned elements), so a packet sequence can thread it. *)
Definition eval_chain_mut_env (c : chain) (p : packet) : verdict * env :=
  match eval_rules_mut_env (c_rules c) p with (Some v, e) => (v, e) | (None, e) => (c_policy c, e) end.
Definition run_chain_mut_env (prog : program) (policy : verdict) (p : packet) : verdict * env :=
  match run_program_mut_env prog p with (Some v, e) => (v, e) | (None, e) => (policy, e) end.

(** ** Whole-chain packet trace.

    [eval_rules_mut] already threads the *mutated* packet from each rule to the
    next (a `meta`/`ct` `set` or dynset is visible downstream); it just returns the
    verdict.  To follow a packet ACROSS chains/hooks (e.g. a mark set in the
    prerouting chain that the postrouting chain reads — the kernel carries it on
    the skb) we also need the packet the chain LEAVES, not only its env.
    [eval_rules_trace]/[eval_chain_trace] mirror the mutation evaluators exactly
    but return [(verdict, final packet)]: every rule contributes [dsl_writes],
    matched or not, and a terminal verdict still records the writes its body made
    before the verdict.  [eval_chain_trace_verdict] proves the verdict component is
    identical to the verified [eval_chain_mut], so this only EXPOSES the packet the
    mutation semantics was already threading — it adds no new behaviour. *)
(** The target ADDRESS operand of a NAT statement — the value the kernel loads
    into [NFTNL_EXPR_NAT_REG_ADDR_MIN] (register 1) and applies as the new
    source/destination address.  This mirrors exactly the register-1 operand the
    compiler emits ([compile_terminal]) and the loadability discipline
    ([terminal_loadable]): an explicit value source ([nat_src]), else a named-map
    lookup ([nat_map]), else a (transformed) packet field ([nat_field]), else the
    immediate destined for register 1 ([nat_imms]). *)
Definition nat_addr (ns : nat_spec) (p : packet) : data :=
  match nat_src ns with
  | Some vs => eval_vsrc vs p
  | None =>
  match nat_map ns with
  | Some (fields, ts, name) =>
      map_lookup_data
        (match fields with
         | [] => apply_transforms ts []
         | f0 :: frest =>
             List.concat (apply_transforms ts (field_value f0 p)
                          :: map (fun f => field_value f p) frest)
         end)
        (e_map (pkt_env p) name)
  | None =>
  match nat_field ns with
  | Some (f, ts) => apply_transforms ts (field_value f p)
  | None => match nat_addr_imm ns with Some v => v | None => [] end
  end end end.

(** The data-plane effect of a terminal NAT rule on the packet, dispatched on
    [nat_kind]:
    - "masq": source-NAT the IPv4 source to the EXIT interface's address
      ([e_ifaddr] keyed by the output-interface name) — masquerade.
    - "snat": source-NAT the IPv4 source to the target operand ([nat_addr]).
    - "dnat": destination-NAT the IPv4 destination to the target operand —
      the kernel's [NF_NAT_MANIP_DST] from [NFTNL_EXPR_NAT_REG_ADDR_MIN].
    - "redir": destination-NAT the IPv4 destination to the INBOUND interface's
      local address (redirect = DNAT to the box itself).
    The address geometry is FAMILY-DEPENDENT ([nat_family]): "ip" rewrites the
    32-bit IPv4 slot, "ip6" the 128-bit IPv6 slot (the kernel picks 32 vs 128
    bits by family — [nat_addrlen], netlink_linearize.c:1237).  masq/redir carry
    [nat_family] = "" (their family is implicit in the chain); [nat_addrfamily]
    normalises "" to "ip" so the legacy IPv4 behaviour is preserved while "ip6"
    is honoured.  Only the address rewrite is modelled; the protocol-PORT range
    ([nat_pmin]/[nat_pmax]) is a separate obligation.  An unrecognised kind
    leaves the packet unchanged. *)
Definition nat_addrfamily (ns : nat_spec) : String.string :=
  if String.eqb (nat_family ns) nat_fam_ip6 then nat_fam_ip6
  else if String.eqb (nat_family ns) nat_fam_inet then nat_fam_inet
  else nat_fam_ip4.

(** The PACKET's L3 protocol family — exactly the bit [nft_pf(pkt)] encodes — read
    from the [meta nfproto] byte: NFPROTO_IPV6 = 10 -> "ip6", everything else (incl.
    NFPROTO_IPV4 = 2) -> "ip".  This is what the kernel's [nft_masq_inet_eval]
    `switch (nft_pf(pkt))` dispatches on. *)
Definition pkt_l3_family (p : packet) : String.string :=
  if N.eqb (data_to_N (pkt_meta p MKnfproto)) 10 then nat_fam_ip6 else nat_fam_ip4.

(** The L3 NAT address family to USE for [p]: for a STATIC family ("ip"/"ip6", e.g.
    an `ip`/`ip6` table or an explicit-literal snat/dnat) the rule's own family; for
    the RUNTIME-DISPATCHED [nat_fam_inet] (an inet-table masquerade/redirect/snat-by-
    iface, which sees both protocols) the PACKET's L3 family ([pkt_l3_family]).  This
    is the precise model of the kernel's runtime `switch (nft_pf(pkt))`: an IPv6
    packet through an inet-table masquerade gets the 16-byte IPv6 geometry + IPv6
    interface address, an IPv4 packet the 4-byte IPv4 geometry — instead of a single
    statically-pinned family that corrupts the other protocol. *)
Definition nat_addrfamily_pkt (ns : nat_spec) (p : packet) : String.string :=
  if String.eqb (nat_addrfamily ns) nat_fam_inet then pkt_l3_family p
  else nat_addrfamily ns.

(** The netfilter hook a base chain is attached to.  This is the SAME [hook_id]
    used by the hook-registration metadata below ([hooked_chain]); it is named
    here because the data-plane NAT effect ([apply_nat]) is hook-dependent — the
    kernel core branches on [hooknum] (e.g. [nf_nat_redirect_ipv4]). *)
Inductive hook_id : Type :=
| Hprerouting | Hinput | Hforward | Houtput | Hpostrouting | Hingress.
Definition hook_eqb (a b : hook_id) : bool :=
  match a, b with
  | Hprerouting, Hprerouting | Hinput, Hinput | Hforward, Hforward
  | Houtput, Houtput | Hpostrouting, Hpostrouting | Hingress, Hingress => true
  | _, _ => false
  end.

(** The loopback destination the kernel forces for an OUTPUT-hooked `redirect`
    ("local packets: make them go to loopback", [nf_nat_redirect_ipv4] /
    [nf_nat_redirect_ipv6]): IPv4 = INADDR_LOOPBACK = 127.0.0.1, IPv6 = ::1. *)
Definition loopback_ip4 : data := [127; 0; 0; 1].
Definition loopback_ip6 : data := [0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;1].
Definition loopback_addr (family : String.string) : data :=
  if String.eqb family nat_fam_ip6 then loopback_ip6 else loopback_ip4.

(** The destination a `redirect` rewrites to, which is HOOK-DEPENDENT exactly as
    the kernel core [nf_nat_redirect_ipv4]/[nf_nat_redirect_ipv6] (branch on
    [hooknum]): at [Houtput] (NF_INET_LOCAL_OUT) local packets are forced to the
    loopback address (127.0.0.1 / ::1); otherwise (PRE_ROUTING) the new
    destination is the inbound interface's primary address.  [nft_redir_validate]
    permits only these two hooks. *)
Definition redir_daddr (h : hook_id) (fam : String.string) (p : packet) : data :=
  match h with
  | Houtput => loopback_addr fam
  | _ => e_ifaddr (pkt_env p) (field_value FMetaIifname p)
  end.

(** The SOURCE address a `masquerade` rewrites to: the exit interface's primary
    address, chosen by family exactly as the kernel dispatches masquerade BY FAMILY
    (nft_masq.c:113-121 branches NFPROTO_IPV4 -> nf_nat_masquerade_ipv4 vs
    NFPROTO_IPV6 -> nf_nat_masquerade_ipv6).  An IPv4 masquerade writes the 4-byte
    [e_ifaddr]; an IPv6 masquerade writes the 16-byte [e_ifaddr6] (the kernel
    computes it via ipv6_dev_get_saddr — a DIFFERENT, 128-bit value, not the IPv4
    address).  Keyed by the exit-interface name ([FMetaOifname]). *)
Definition masq_saddr (fam : String.string) (p : packet) : data :=
  if String.eqb fam nat_fam_ip6
  then e_ifaddr6 (pkt_env p) (field_value FMetaOifname p)
  else e_ifaddr  (pkt_env p) (field_value FMetaOifname p).

(** The L4 port the kernel writes is [min_proto.all] of the NAT range, loaded as a
    big-endian 16-bit value from the proto-min register ([nft_nat_setup_proto],
    nft_nat.c:57-60).  In the model the operand is [nat_pmin]; encode it as the
    2-byte big-endian port the transport header carries. *)
Definition nat_port_bytes (pmin : nat) : data := N_to_data 2 (N.of_nat pmin).

(** Apply the L4 PORT half of a NAT effect, mirroring the kernel
    [nft_nat_setup_proto]: the port rewrite happens ONLY when the proto-min
    register is set (`if (priv->sreg_proto_min)`, nft_nat.c:120) — in the model,
    when [nat_pmin ns = Some pmin].  A SOURCE NAT (snat/masquerade) rewrites the
    L4 SOURCE port ([set_sport]); a DESTINATION NAT (dnat/redirect) the L4
    DESTINATION port ([set_dport]) — exactly the [NF_NAT_MANIP_{SRC,DST}] split of
    [tcp_manip_pkt] (nf_nat_proto.c).  Address-only NAT ([nat_pmin] = None) leaves
    the port byte-for-byte unchanged. *)
(** REGISTER-FREE / bug-fixed: the port is the VALUE [lo] (a 2-byte port operand),
    not [nat_port_bytes] of a register index (the old [nat_pmin] conflated the two).
    A concat-map port ([NXmap_port]) is a runtime map value, not statically modelled. *)
Definition apply_nat_port (is_src : bool) (ns : nat_spec) (p : packet) : packet :=
  match nat_extra ns with
  | NXimm _ (Some lo) _ => if is_src then set_sport p lo else set_dport p lo
  | _ => p
  end.

(** Whether the NAT spec carries an L3 ADDRESS operand — i.e. whether the kernel
    sets [priv->sreg_addr_min] (NFTNL_EXPR_NAT_REG_ADDR_MIN).  The address rewrite
    in [nft_nat_eval] is gated EXACTLY on this register being present
    (`if (priv->sreg_addr_min)`, nft_nat.c:114) and is INDEPENDENT of the proto
    (port) register (`if (priv->sreg_proto_min)`, nft_nat.c:120).  A PORT-ONLY NAT
    (`dnat to :80`, `snat to :1024`) sets only the proto register, so the kernel
    rewrites ONLY the L4 port and leaves the L3 destination/source address
    byte-for-byte UNCHANGED.  An address operand is present iff [nat_addr] has a
    source: an explicit value source ([nat_src]), a named-map lookup ([nat_map]),
    a packet field ([nat_field]), or a register-1 immediate ([nat_imms]). *)
Definition nat_has_addr (ns : nat_spec) : bool :=
  match nat_src ns, nat_map ns, nat_field ns with
  | None, None, None => match nat_addr_imm ns with Some _ => true | None => false end
  | _, _, _ => true
  end.

(** The data-plane NAT effect of a terminal rule at hook [h].  Only [redir] is
    hook-dependent (see [redir_daddr]); masq/snat/dnat are hook-invariant.  Each
    kind first performs its L3 address rewrite ([set_saddr]/[set_daddr]) — but ONLY
    when an address operand is present ([nat_has_addr], the kernel's
    `if (priv->sreg_addr_min)` guard, nft_nat.c:114); a port-only snat/dnat
    therefore preserves the L3 address — and then, when a port operand is present
    ([nat_pmin] = Some), the L4 port rewrite ([apply_nat_port], the independent
    `if (priv->sreg_proto_min)` guard, nft_nat.c:120).  masquerade always derives
    its source address from the exit interface and redirect from the inbound
    interface / loopback, so both always carry an (implicit) address operand and
    their address rewrite is unconditional, matching [nft_masq]/[nft_redir] which
    always set up the address.  The kernel applies both the addr and the proto
    range in a single [nf_nat_setup_info]. *)
(** Whether a NAT kind is a SOURCE NAT ([NF_NAT_MANIP_SRC]: snat/masquerade — the
    L3 SOURCE address + L4 SOURCE port are rewritten) versus a DESTINATION NAT
    ([NF_NAT_MANIP_DST]: dnat/redirect).  This is fixed by the rule's [nat_kind],
    independent of the flow. *)
Definition nat_is_src (ns : nat_spec) : bool :=
  String.eqb (nat_kind ns) nat_masq_kind || String.eqb (nat_kind ns) nat_snat_kind.

(** The L3 ADDRESS the operand evaluates to, i.e. the value the kernel loads into
    [NAT_REG_ADDR_MIN] on the unconfirmed packet to build the new tuple — or [None]
    when the spec carries no address operand (a port-only snat/dnat, the kernel's
    `if (priv->sreg_addr_min)` guard being false, nft_nat.c:114).  masquerade derives
    its source from the exit interface, redirect from the inbound interface/loopback,
    so both always carry an (implicit) address.  This is the ONLY part of the NAT
    effect that re-reads the current packet, so it is exactly what must be FROZEN at
    the flow's first packet. *)
Definition nat_operand_addr (h : hook_id) (ns : nat_spec) (p : packet) : option data :=
  if String.eqb (nat_kind ns) nat_masq_kind
  then Some (masq_saddr (nat_addrfamily_pkt ns p) p)
  else if String.eqb (nat_kind ns) nat_redir_kind
  then Some (redir_daddr h (nat_addrfamily_pkt ns p) p)
  else if String.eqb (nat_kind ns) nat_snat_kind
       || String.eqb (nat_kind ns) nat_dnat_kind
  then if nat_has_addr ns then Some (nat_addr ns p) else None
  else None.

(** Apply a (possibly absent) L4 PORT translation [port_opt] to packet [p],
    rewriting the SOURCE port for a source NAT or the DESTINATION port for a
    destination NAT — the value-level analogue of [apply_nat_port] that takes the
    stored port directly instead of re-reading [nat_pmin]. *)
Definition apply_nat_port_val (is_src : bool) (port_opt : option nat) (p : packet) : packet :=
  match port_opt with
  | Some pmin =>
      if is_src then set_sport p (nat_port_bytes pmin)
                else set_dport p (nat_port_bytes pmin)
  | None => p
  end.

(** Apply an ESTABLISHED translation [(orig_addr_opt, new_addr_opt, port_opt)] to
    packet [p] for a NAT of kind [ns], in the conntrack DIRECTION-AWARE way the
    kernel's [nf_nat_packet]/[nf_nat_manip_pkt] does (net/netfilter/nf_nat_core.c):

    - ORIGINAL direction ([pkt_ctdir_orig p = true]): apply the manip FORWARD.
      Rewrite the L3 address of the manip slot (SOURCE for a source NAT, DESTINATION
      for a destination NAT) to [new_addr_opt], then the L4 port of that slot to
      [port_opt].  This is the translation the rule established on packet 1, reused
      verbatim on every later confirmed ORIGINAL-direction packet (it never re-reads
      the rule operand).

    - REPLY direction ([pkt_ctdir_orig p = false]): apply the INVERSE manip.  The
      kernel inverts the manip target for reply packets
      (`if (dir == IP_CT_DIR_REPLY) statusbit ^= IPS_NAT_MASK`), so a source NAT
      un-rewrites the reply's DESTINATION and a destination NAT un-rewrites the
      reply's SOURCE — restoring the ORIGINAL (pre-NAT) address [orig_addr_opt] that
      the peer originally addressed.  (A dnat's reply has its SOURCE = the dnat target
      un-DNAT'd back to [orig_addr]; its DESTINATION is left untouched.)  The L4 PORT
      is ALSO un-rewritten on reply when a port operand was present: the kernel's
      [nf_nat_manip_pkt(REPLY)] inverts the maniptype and writes the reply tuple's
      port into the OPPOSITE slot ([tcp_manip_pkt]/[__udp_manip_pkt]:
      `*portptr = newport`, nf_nat_proto.c), so a dnat reply has its SOURCE port
      restored to the connection's original (pre-DNAT) destination port, and an snat
      reply has its DESTINATION port restored to the original source port.  The
      stored [orig_port_opt] is exactly that original port; it is [None] when the
      forward NAT carried no port operand (then the reply leaves the port unchanged,
      matching the kernel's `if (priv->sreg_proto_min)` guard being false). *)
Definition apply_nat_tuple (ns : nat_spec) (p : packet)
                           (m : option data * option data * option nat * option data) : packet :=
  let fam := nat_addrfamily_pkt ns p in
  let is_src := nat_is_src ns in
  let '(orig_addr_opt, new_addr_opt, port_opt, orig_port_opt) := m in
  if pkt_ctdir_orig p then
    (* forward (original direction): rewrite the manip slot to the NAT target *)
    let p1 := match new_addr_opt with
              | Some a => if is_src then set_saddr fam p a else set_daddr fam p a
              | None => p
              end in
    apply_nat_port_val is_src port_opt p1
  else
    (* reply direction: un-NAT the OPPOSITE slot back to the original address AND,
       when a port operand was present, restore that slot's PORT to the original.
       The maniptype is inverted exactly as nf_nat_manip_pkt(REPLY): a SOURCE NAT
       un-rewrites the reply's DESTINATION (addr + port), a DESTINATION NAT the
       reply's SOURCE. *)
    let p1 := match orig_addr_opt with
              | Some o => if is_src then set_daddr fam p o else set_saddr fam p o
              | None => p
              end in
    match orig_port_opt with
    | Some op => if is_src then set_dport p1 op else set_sport p1 op
    | None => p1
    end.

(** Replace packet [p]'s environment with the flow-keyed NAT mapping [m] STORED at
    [p]'s flow ([env_nat_upd]).  Every set_*/address rewrite preserves [pkt_env], so
    this records the established translation into the shared, threaded env exactly
    where the kernel writes it into the conntrack entry. *)
Definition store_nat_mapping (p : packet) (m : option data * option data * option nat * option data) : packet :=
  with_pkt_env p (env_nat_upd (pkt_env p) (pkt_flow p) m).

(** The data-plane NAT effect of a terminal rule at hook [h], now FLOW-STATEFUL,
    mirroring [nf_nat_setup_info]/[nft_nat_eval]:

    - On the FIRST (unconfirmed) packet of a flow ([e_nat (pkt_flow p) = None]) the
      kernel computes the new tuple from the rule operand (get_unique_tuple,
      nf_nat_core.c:796), STORES it in the conntrack entry (nf_conntrack_alter_reply,
      :803), and applies the rewrite.  The model mirrors this: it evaluates
      [nat_operand_addr]/[nat_pmin] from the CURRENT packet, applies the tuple
      ([apply_nat_tuple]) AND stores it into the shared, flow-keyed [e_nat]
      ([store_nat_mapping]).

    - On every LATER (confirmed) packet of the SAME flow ([e_nat (pkt_flow p) =
      Some m]) the kernel returns NF_ACCEPT from nf_nat_setup_info WITHOUT
      recomputing (nf_nat_core.c:778-780), and the rewrite comes from the STORED
      tuple [m] (nf_nat_manip_pkt).  The model mirrors this: it applies [m] verbatim
      ([apply_nat_tuple]) and does NOT re-read the operand — so two same-flow packets
      with different saddrs both get the translation chosen on packet 1.

    This is the exact analogue of the Round-1 conntrack-mark fix, now for the NAT
    tuple.  The verdict side is untouched (NAT is terminal-Accept), so
    [compile_chain_correct] is unaffected. *)

(** The ORIGINAL (pre-NAT) address of the slot a NAT of kind [ns] rewrites — read
    from the CURRENT packet before any rewrite: the SOURCE slot for a source NAT
    ([nat_is_src]: snat/masquerade), the DESTINATION slot for a destination NAT
    (dnat/redirect).  This is the address the kernel records as the OTHER tuple of
    the conntrack entry (nf_conntrack_alter_reply), so a reply-direction packet can
    be un-NAT'd back to it (the reply's opposite slot is restored to this value). *)
Definition nat_orig_addr (ns : nat_spec) (p : packet) : data :=
  let fam := nat_addrfamily_pkt ns p in
  let '(off, len) := if nat_is_src ns then saddr_slot fam else daddr_slot fam in
  slice (pkt_nh p) off len.

(** The ORIGINAL (pre-NAT) L4 PORT of the slot a NAT of kind [ns] rewrites — read
    from the CURRENT packet's transport header before any rewrite: the SOURCE port
    (transport bytes 0..1) for a source NAT ([nat_is_src]: snat/masquerade), the
    DESTINATION port (bytes 2..3) for a destination NAT (dnat/redirect).  Stored
    ONLY when a port operand is present ([nat_pmin ns = Some _], the kernel's
    `if (priv->sreg_proto_min)` guard, nft_nat.c:120) — otherwise [None], so the
    reply leaves the port byte-for-byte unchanged.  This is the port half of the
    reply tuple the kernel records (nf_conntrack_alter_reply), un-rewritten onto
    the OPPOSITE slot of a reply-direction packet (mirroring nf_nat_manip_pkt's
    inverted maniptype). *)
(** The port operand as a NUMBER, for the flow tuple (register-free; the source
    carries the port as a 2-byte VALUE in [nat_extra], decoded here). *)
Definition nat_port_num (ns : nat_spec) : option nat :=
  match nat_extra ns with
  | NXimm _ (Some lo) _ => Some (N.to_nat (data_to_N lo))
  | _ => None
  end.
Definition nat_orig_port (ns : nat_spec) (p : packet) : option data :=
  match nat_port_num ns with
  | Some _ =>
      if nat_is_src ns
      then Some (slice (pkt_th p) 0 2)   (* source NAT: original SOURCE port *)
      else Some (slice (pkt_th p) 2 2)   (* dest   NAT: original DEST   port *)
  | None => None
  end.
Definition apply_nat (h : hook_id) (r : rule) (p : packet) : packet :=
  match r_nat r with
  | Some ns =>
      match e_nat (pkt_env p) (pkt_flow p) with
      | Some m =>
          (* confirmed flow: reuse the stored tuple (direction-aware), do NOT re-read
             the operand *)
          apply_nat_tuple ns p m
      | None =>
          (* No mapping established yet.  The kernel establishes the NAT tuple only on
             the connection's ORIGINAL-direction packet (nf_nat_setup_info runs on the
             unconfirmed, original-direction skb).  A reply-direction packet with no
             established mapping is NOT translated. *)
          if pkt_ctdir_orig p then
            (* first packet of the flow (original direction): capture the original
               address, compute the tuple, apply it FORWARD, and STORE it *)
            let m := (Some (nat_orig_addr ns p), nat_operand_addr h ns p, nat_port_num ns,
                      nat_orig_port ns p) in
            store_nat_mapping (apply_nat_tuple ns p m) m
          else
            p
      end
  | None => p
  end.

(** The kernel's NAT CORE DROPS a packet when the interface it must take an
    address FROM has no usable address — a data-plane drop that has NO control-plane
    (compiler) analogue, so it lives only in the trace evaluator.  Two cases mirror
    the kernel exactly:

    - [redirect] (nf_nat_redirect_ipv4/ipv6): at the OUTPUT hook the new destination
      is always the loopback address (`newdst.ip = htonl(INADDR_LOOPBACK)`), so it
      NEVER drops there.  At PRE_ROUTING the new destination is the inbound device's
      primary address; if that is empty (`if (!newdst.ip) return NF_DROP;`,
      nf_nat_redirect.c:71-74) the packet is DROPPED.

    - [masquerade] (nf_nat_masquerade_ipv4/ipv6): the new source is the exit
      interface's selected address (inet_select_addr / ipv6_dev_get_saddr); if that
      is empty (`if (!newsrc) { ...; return NF_DROP; }`, nf_nat_masquerade.c:54-58;
      the IPv6 path likewise `return NF_DROP` on nat_ipv6_dev_get_saddr<0,
      nf_nat_masquerade.c:254-256) the packet is DROPPED.

    Like the kernel, this only fires when the NAT tuple is COMPUTED — i.e. on the
    FIRST (unconfirmed) ORIGINAL-direction packet of the flow ([apply_nat]'s
    [e_nat ... = None] && [pkt_ctdir_orig] branch).  On a confirmed/reply packet the
    stored tuple is reused with no recompute (nf_nat_setup_info returns NF_ACCEPT
    early, nf_nat_core.c:778-780), so no drop.  Address-carrying snat/dnat never hit
    this path (their operand is an explicit value/map/field, not an interface
    address), so [nat_drops] is false for them. *)
Definition nat_iface_addr_absent (h : hook_id) (ns : nat_spec) (p : packet) : bool :=
  if String.eqb (nat_kind ns) nat_masq_kind
  then match masq_saddr (nat_addrfamily_pkt ns p) p with [] => true | _ => false end
  else if String.eqb (nat_kind ns) nat_redir_kind
  then match h with
       | Houtput => false   (* loopback: never empty, never drops *)
       | _ => match redir_daddr h (nat_addrfamily_pkt ns p) p with [] => true | _ => false end
       end
  else false.

Definition nat_drops (h : hook_id) (r : rule) (p : packet) : bool :=
  match r_nat r with
  | Some ns =>
      match e_nat (pkt_env p) (pkt_flow p) with
      | Some _ => false                                  (* confirmed flow: reuse stored tuple, no recompute *)
      | None => pkt_ctdir_orig p && nat_iface_addr_absent h ns p
      end
  | None => false
  end.

(** [eval_rules_trace]/[eval_chain_trace] take the netfilter hook [h] the base
    chain is attached to, because the data-plane NAT effect at a terminal verdict
    ([apply_nat]) is hook-dependent (an OUTPUT-hooked `redirect` rewrites the
    destination to loopback, not the inbound-interface address), and because the NAT
    core can DROP a packet whose interface has no usable address ([nat_drops]). *)
Fixpoint eval_rules_trace (h : hook_id) (rs : list rule) (p : packet) : option verdict * packet :=
  match rs with
  | [] => (None, p)
  | r :: rest =>
      if rule_loadable r p && rule_applies r p then
        match outcome r p with
        | Some v => if terminal v then
                      (* The NAT core DROPS (returns NF_DROP, overriding the rule's
                         stated verdict) when the interface it must take an address
                         from has no usable address ([nat_drops]); the drop happens
                         BEFORE the address is spliced, so the packet is left
                         unrewritten.  Otherwise the rule's verdict stands and the
                         NAT rewrite is applied. *)
                      if nat_drops h r (dsl_step r p)
                      then (Some Drop, dsl_step r p)
                      else (Some v, apply_nat h r (dsl_step r p))
                    else eval_rules_trace h rest (dsl_step r p)
        | None   => eval_rules_trace h rest (dsl_step r p)
        end
      else eval_rules_trace h rest (dsl_step r p)
  end.

Definition eval_chain_trace (h : hook_id) (c : chain) (p : packet) : verdict * packet :=
  match eval_rules_trace h (c_rules c) p with
  | (Some v, q) => (v, q) | (None, q) => (c_policy c, q) end.

(** When does the trace traversal reach a NAT-drop?  This Fixpoint mirrors
    [eval_rules_trace] step-for-step and is [true] exactly when the rule that
    delivers the terminal verdict is a [nat_drops] rule — i.e. when the data-plane
    NAT core overrides the verdict to [Drop].  It is the precise hypothesis under
    which the trace verdict equals the (control-plane) [eval_rules_mut] verdict. *)
Fixpoint trace_nat_drops (h : hook_id) (rs : list rule) (p : packet) : bool :=
  match rs with
  | [] => false
  | r :: rest =>
      if rule_loadable r p && rule_applies r p then
        match outcome r p with
        | Some v => if terminal v then nat_drops h r (dsl_step r p)
                    else trace_nat_drops h rest (dsl_step r p)
        | None   => trace_nat_drops h rest (dsl_step r p)
        end
      else trace_nat_drops h rest (dsl_step r p)
  end.

(** The trace verdict equals the verified [eval_rules_mut] verdict EXCEPT when the
    data-plane NAT core fires a drop ([trace_nat_drops]); in that case the trace
    verdict is [Some Drop], faithfully overriding the rule's stated verdict exactly
    as the kernel's NF_DROP overrides the rule outcome.  This replaces the old
    UNCONDITIONAL equality, which is now genuinely false in the model: the kernel
    DROPS a redirect/masquerade whose interface has no usable address even though
    the rule's stated verdict is Accept. *)
Lemma eval_rules_trace_verdict : forall h rs p,
  fst (eval_rules_trace h rs p)
    = (if trace_nat_drops h rs p then Some Drop else eval_rules_mut rs p).
Proof.
  induction rs as [|r rest IH]; intros p; simpl; [reflexivity|].
  destruct (rule_loadable r p && rule_applies r p).
  - destruct (outcome r p) as [v|]; [|auto].
    destruct (terminal v); [|auto].
    destruct (nat_drops h r (dsl_step r p)); reflexivity.
  - auto.
Qed.

(** Specialisation: when no NAT-drop fires, the trace verdict is exactly the
    verified [eval_rules_mut] verdict — the original (now conditional) equality. *)
Corollary eval_rules_trace_verdict_no_drop : forall h rs p,
  trace_nat_drops h rs p = false ->
  fst (eval_rules_trace h rs p) = eval_rules_mut rs p.
Proof.
  intros h rs p Hnd. rewrite eval_rules_trace_verdict, Hnd. reflexivity.
Qed.

Lemma eval_chain_trace_verdict : forall h c p,
  fst (eval_chain_trace h c p)
    = (if trace_nat_drops h (c_rules c) p then Drop else eval_chain_mut c p).
Proof.
  intros h c p. unfold eval_chain_trace, eval_chain_mut.
  pose proof (eval_rules_trace_verdict h (c_rules c) p) as Hv.
  destruct (eval_rules_trace h (c_rules c) p) as [[v|] q];
    simpl in Hv;
    destruct (trace_nat_drops h (c_rules c) p).
  - inversion Hv; reflexivity.
  - rewrite <- Hv; reflexivity.
  - discriminate Hv.
  - destruct (eval_rules_mut (c_rules c) p); [discriminate Hv | reflexivity].
Qed.

Corollary eval_chain_trace_verdict_no_drop : forall h c p,
  trace_nat_drops h (c_rules c) p = false ->
  fst (eval_chain_trace h c p) = eval_chain_mut c p.
Proof.
  intros h c p Hnd. rewrite eval_chain_trace_verdict, Hnd. reflexivity.
Qed.

(** Run a whole chain on a packet and return the packet it leaves (the
    [eval_chain_trace] packet component) — the input to the next chain/hook. *)
Definition chain_out (h : hook_id) (c : chain) (p : packet) : packet := snd (eval_chain_trace h c p).

(** A packet sequence threaded through a shared, learning environment: each packet
    is evaluated against the current [e], and the env it LEAVES (learned sets/maps)
    seeds the next packet.  This is [seq_eval]'s analogue where the state update is
    the chain's own dynset learning, not an external [step] keyed on the verdict —
    so a later packet's `lookup @s` observes what an earlier packet's `add @s`
    learned. *)
Fixpoint seq_eval_env (ev : env -> packet -> verdict * env)
    (e : env) (packets : list packet) : list verdict :=
  match packets with
  | [] => []
  | p :: ps => let '(v, e') := ev e p in v :: seq_eval_env ev e' ps
  end.

(** ** Multi-chain control flow: jump / goto / return + user-defined chains.

    A [jump n] calls chain [n] and *resumes* the caller after it (on the callee's
    fall-through or a [return]); a [goto n] tail-calls [n] and does NOT resume; a
    [return] pops to the caller.  A terminal verdict (accept/drop/reject/queue)
    reached anywhere stops the whole traversal.  Recursion through the named chain
    environment is not structurally terminating (nft rejects jump loops), so the
    interpreters are *fuel-bounded*; the correctness theorem holds for every fuel. *)

Fixpoint chain_lookup (cs : list (String.string * chain)) (n : String.string) : option chain :=
  match cs with
  | [] => None
  | (m, ch) :: rest => if String.eqb n m then Some ch else chain_lookup rest n
  end.

Fixpoint prog_lookup (cs : list (String.string * program)) (n : String.string) : option program :=
  match cs with
  | [] => None
  | (m, prg) :: rest => if String.eqb n m then Some prg else prog_lookup rest n
  end.

(** DSL semantics under a chain environment [cs] (the user-defined chains). *)
Fixpoint eval_rules_j (fuel : nat) (cs : list (String.string * chain))
                      (rs : list rule) (p : packet) : option verdict :=
  match fuel with
  | O => None
  | S fuel' =>
    match rs with
    | [] => None
    | r :: rest =>
      if rule_loadable r p && rule_applies r p then
        match outcome r p with
        | None => eval_rules_j fuel' cs rest p
        | Some Return => None
        | Some (Jump n) =>
            match chain_lookup cs n with
            | Some ch => match eval_rules_j fuel' cs (c_rules ch) p with
                         | Some v => Some v
                         | None   => eval_rules_j fuel' cs rest p
                         end
            | None => eval_rules_j fuel' cs rest p
            end
        | Some (Goto n) =>
            match chain_lookup cs n with
            | Some ch => eval_rules_j fuel' cs (c_rules ch) p
            | None    => None
            end
        | Some Continue => eval_rules_j fuel' cs rest p
        | Some v => Some v
        end
      else eval_rules_j fuel' cs rest p
    end
  end.

Definition eval_table (fuel : nat) (cs : list (String.string * chain))
                      (base : chain) (p : packet) : verdict :=
  match eval_rules_j fuel cs (c_rules base) p with
  | Some v => v
  | None   => c_policy base
  end.

(** Bytecode VM under a compiled chain environment [cs]; mirrors [eval_rules_j]. *)
Fixpoint run_rules_j (fuel : nat) (cs : list (String.string * program))
                     (prog : program) (p : packet) : option verdict :=
  match fuel with
  | O => None
  | S fuel' =>
    match prog with
    | [] => None
    | rp :: rest =>
      match run_rule empty_rf rp p with
      | None => run_rules_j fuel' cs rest p
      | Some Return => None
      | Some (Jump n) =>
          match prog_lookup cs n with
          | Some prg => match run_rules_j fuel' cs prg p with
                        | Some v => Some v
                        | None   => run_rules_j fuel' cs rest p
                        end
          | None => run_rules_j fuel' cs rest p
          end
      | Some (Goto n) =>
          match prog_lookup cs n with
          | Some prg => run_rules_j fuel' cs prg p
          | None     => None
          end
      | Some Continue => run_rules_j fuel' cs rest p
      | Some v => Some v
      end
    end
  end.

Definition run_table (fuel : nat) (cs : list (String.string * program))
                     (base : program) (policy : verdict) (p : packet) : verdict :=
  match run_rules_j fuel cs base p with
  | Some v => v
  | None   => policy
  end.

(** ** Multi-table / multi-hook dispatch (netfilter verdict combination).

    At one hook the registered base chains across all tables run in priority
    order.  Selecting and ordering the base chains for a hook is the control
    plane's job; here we model the *data-plane* traversal over an already
    (hook,priority)-ordered list of (chain-env, base-chain) pairs: a base chain
    that ACCEPTs (or falls through to an accept policy) lets the packet proceed to
    the NEXT base chain, while DROP/REJECT/QUEUE is terminal — exactly how
    netfilter propagates a verdict across the chains at a hook.  If every base
    chain accepts, the packet is accepted. *)
Definition base_continues (v : verdict) : bool :=
  match v with Accept | Continue => true | _ => false end.

Fixpoint eval_ruleset (fuel : nat)
    (bases : list (list (String.string * chain) * chain)) (p : packet) : verdict :=
  match bases with
  | [] => Accept
  | (cs, base) :: rest =>
      let v := eval_table fuel cs base p in
      if base_continues v then eval_ruleset fuel rest p else v
  end.

Fixpoint run_ruleset (fuel : nat)
    (bases : list (list (String.string * program) * (program * verdict))) (p : packet) : verdict :=
  match bases with
  | [] => Accept
  | (cs, (base, policy)) :: rest =>
      let v := run_table fuel cs base policy p in
      if base_continues v then run_ruleset fuel rest p else v
  end.

(** ** Hook registration: which base chains are active at which hook, and in what
    priority order.  This is *separate* metadata from a chain's rules (a base
    chain is `type filter hook input priority 0`), so we model it as a tagged list
    rather than fields on [chain] — the engine then filters by hook and sorts by
    priority to obtain the ordered base-chain list [eval_ruleset] traverses.
    [hook_id]/[hook_eqb] are defined above (near [apply_nat], which is itself
    hook-dependent). *)
Record hooked_chain : Type := {
  hc_hook : hook_id;
  hc_prio : nat;
  hc_env  : list (String.string * chain);  (* the jump-target chains in its table *)
  hc_base : chain;
}.

Fixpoint insert_hc (x : hooked_chain) (l : list hooked_chain) : list hooked_chain :=
  match l with
  | [] => [x]
  | y :: ys => if Nat.leb (hc_prio x) (hc_prio y) then x :: y :: ys else y :: insert_hc x ys
  end.
Fixpoint sort_hc (l : list hooked_chain) : list hooked_chain :=
  match l with [] => [] | x :: xs => insert_hc x (sort_hc xs) end.

(** The ordered (env, base-chain) list active at hook [h]: the registered base
    chains for [h], ascending by priority (lower priority runs first). *)
Definition select_hook (rs : list hooked_chain) (h : hook_id)
  : list (list (String.string * chain) * chain) :=
  map (fun hc => (hc_env hc, hc_base hc))
      (sort_hc (filter (fun hc => hook_eqb (hc_hook hc) h) rs)).

(** Full ruleset evaluation at a hook: select+order the base chains, then dispatch. *)
Definition eval_hook (fuel : nat) (rs : list hooked_chain) (h : hook_id) (p : packet) : verdict :=
  eval_ruleset fuel (select_hook rs h) p.

(** ** Stateful accumulation across a packet sequence.

    Evaluate a packet against a *given* shared environment, overriding the
    packet's own [pkt_env] (limiter/quota/conntrack/set state is shared, not
    per-packet). *)
Definition set_env (p : packet) (e : env) : packet :=
  with_pkt_env p e.

(** Run a sequence of packets against a shared, evolving environment [e]: each
    packet is evaluated by [ev] against the current [e], then [step] updates [e]
    from the verdict (e.g. decrement a rate limiter's remaining tokens on accept).
    So a later packet observes the accumulated state — the cross-packet behaviour
    a per-packet oracle could not express.  Generic in [ev] so the DSL and the VM
    share it (only the per-packet evaluator differs). *)
Fixpoint seq_eval (ev : env -> packet -> verdict) (step : verdict -> env -> env)
    (e : env) (packets : list packet) : list verdict :=
  match packets with
  | [] => []
  | p :: ps => let v := ev e p in v :: seq_eval ev step (step v e) ps
  end.
