(** * Semantics: the meaning of both languages as packet -> verdict.

    Both the declarative DSL and the bytecode are given the *same* observable
    semantics — a function from a packet to the verdict the base chain produces —
    so "semantics preserving" is a literal equality of these functions.

    ** Evaluator matrix: ONE unified semantics; every other entry point is a
    proven projection of it.

    THE semantics of a ruleset is the UNIFIED evaluator pair
    (§ "The unified semantics", end of this file):

      DSL: eval_rules_u / eval_table_u / eval_ruleset_u / eval_hook_u
      VM:  run_rules_u  / run_table_u  / run_ruleset_u

    a single fuel-bounded fold, evaluated AT a netfilter hook [h] (§ Section
    AtHook), that BOTH threads every state effect — packet
    meta/ct writes, dynset env writes, the notrack latch, limiter/quota/
    connlimit consumption, the VM `numgen inc` counter advance, AND the
    data-plane NAT effect of a dnat/snat/masquerade/redirect terminal (the
    packet rewrite + the flow-keyed [e_nat] tuple store/reuse and the
    no-usable-address NF_DROP, applied AT the terminal the walk actually
    reached — a vmap HIT never runs it: outcome provenance is the fold's
    structure) — each effect applied
    AT its body/instruction position inside the break-aware per-rule fold
    [rule_step] / [run_rule_step], so a limiter after a failing match is NOT
    consumed — kernel NFT_BREAK order — AND follows control flow
    (jump/goto/return, user-defined
    chains, multi-chain and hook/priority dispatch), with cross-packet env
    carry ([seq_eval_env] over [eval_hook_env_u]).  A jumped-to chain sees
    the caller's accumulated writes, a rule inside it sees its own intra-rule
    writes, and the callee's writes persist back into the resuming caller
    (witness pins: Regression/Setread_UnderJump.v).  Mutation x jump/goto is
    JOINTLY verified at this evaluator: compiler correctness is
    [Correct.compile_table_u_correct] / [compile_ruleset_u_correct] /
    [compile_hook_u_correct] / [compile_seq_hook_correct].

    Every OTHER rule-list entry point is a PROJECTION of the unified fold,
    licensed by a coincidence theorem on the sub-domain where it PROVABLY
    agrees — never an independent semantics for a rule to be evaluated
    through.  An input outside an evaluator's licensed sub-domain must be run
    on the unified evaluator (or an evaluator whose license covers it):

      projection            | licensed sub-domain          | coincidence theorem
      ----------------------+------------------------------+--------------------
      eval_rules_j /        | write-free rules everywhere  | eval_rules_u_writefree /
        eval_table          | ([rule_writefree]: no meta/  | eval_table_u_writefree
                            | ct set, dynset, notrack,     |
                            | limiter/quota/connlimit);    |
                            | OR limiter-tolerant configs  | eval_rules_u_limiter_tolerant /
                            | ([rule_limiter_tol]: only    | eval_table_u_limiter_tolerant
                            | writes are one-limiter rules;| (VERDICT projection only —
                            | § Projection 1b)             | the bucket IS depleted)
      eval_ruleset /        | write-free bases             | eval_ruleset_u_writefree /
        eval_hook           | ([bases_writefree]); OR one  | eval_hook_u_writefree /
                            | limiter-tolerant base at the | eval_hook_u_limiter_tolerant_1
                            | hook                         |
      eval_rules /          | write-free + jump-free       | eval_rules_u_writefree +
        eval_chain          | (entry-state-free syntactic  | Correct.eval_rules_jumpfree_eq_j
                            | form: chain_jumpfree_syn,    | / Correct.eval_chain_writefree_
                            | rules_jumpfree_syn_sound)    |   jumpfree_syn_proj
      eval_rules_mut_st /   | transfer-free rules          | eval_rules_u_mut_st_proj /
        eval_chain_mut_st   | ([rule_plain]: no realisable | eval_table_u_mut_st_proj
        (full state; _mut / | jump/goto/return under the   | (whole-triple equality;
        _env project it)    | run's verdict maps)          | _mut/_env: eval_rules_u_mut_proj)
      rule_applies(_walk) / | write-free rule (no mut stmt,| rule_step_mutfree
        outcome/rule_loadable  no limiter match, no NAT    |
                            | terminal)                    |
      rule_applies_walk     | body_purewalk bodies (con-   | rule_purewalk_ok (the walk =
        (notrack ADMITTED)  | sume-free matches, non-mut   | break/no-break projection of
                            | stmts, notrack allowed) that | body_step; its set_untracked
                            | load (body_loadable_walk)    | threading is body_step's own)
      run_rule/run_program  | no_writes programs (no mut/  | Correct.run_rule_step_no_writes
                            | limiter/inc-numgen instr)    |
      run_rules_j/run_table | compiled write-free chains   | Correct.run_table_writefree_compiled
      (seq_eval — RETIRED: the external-step sequence stratum; the sequence
       semantics is [seq_eval_env] over [eval_hook_env_u] — see § Stateful
       accumulation)

    Within the flat mutation strand every evaluator consumes ONE step function
    per side — [rule_step] (DSL) / [run_rule_step empty_rf] (VM), each
    returning (guarded verdict, state left).  [eval_rules_mut_st] exports that
    fold IN FULL — verdict and the exact (env, packet) left — and the _mut /
    _mut_env evaluators are its projections ([eval_rules_mut_env_st],
    [eval_rules_mut_env_fst] / [run_program_mut_env_fst]), so their compiler
    proofs are derived, not re-proved.  (The historical [dsl_rule_step]/[vm_rule_step] boundary
    wrappers — the fold plus a whole-body limiter/numgen sweep — are RETIRED:
    with the consumption evaluated in-fold they were identical to the folds,
    see THEOREMS.md § strata retirements.)

    STRUCTURAL GUARANTEE (M6): exactly ONE recursive rule-list/jump traversal
    exists per side — the Fixpoints [eval_rules_u] and [run_rules_u].  Every
    other evaluator above is a NON-RECURSIVE Definition (stdlib fold /
    nat_rect on the fuel) with [_nil]/[_cons] (or [_0]/[_S]) unfolding
    equations restating the historical recursion verbatim, and the flat
    [_mut]/[_mut_env] forms are projections BY DEFINITION of the one
    full-state fold per side ([eval_rules_mut_st]/[run_program_mut_st]).
    Fuel adequacy is stated at the unified semantics too
    ([eval_rules_u_fuel_indep]), not only at the pure projection. *)

From Stdlib Require Import String List NArith ZArith Bool Lia.
From Nft Require Import Bytes Packet Verdict Syntax Bytecode.
Import ListNotations.
(* [String] is imported FIRST so that [List] (imported after it) re-shadows the
   names they share ([concat]/[length]) — the body below always means the List
   ones.  The import exists only for the ["…"%string] literals of the fuel-probe
   counterexample ([eval_rules_j_not_naively_monotone]); everything else uses
   the qualified [String.string] / [String.eqb]. *)

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
    tractable).  NOTE on "range": Rocq's [nat] is unbounded, so no arithmetic
    here can overflow IN THE PROOFS.  The extracted OCaml realises [nat] as a
    63-bit native int (ExtrOcamlNatInt — see the classification comment in
    Compiler/Extract.v), so the EXTRACTED [lim_cost]/[lim_max] products
    ([lim_window] <= 604800 times rate+burst) are only faithful while
    rate+burst stays below 2^62 / 604800; the untrusted frontend therefore
    bounds the user-controlled [ls_rate]/[ls_burst] at parse time
    (extracted/parser.mly, `scaled_or_reject`) and rejects larger rates
    loudly.  Elapsed wall-clock time is abstracted to +0 WITHIN one
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
  then Nat.div (lim_window spec * N.to_nat (data_to_N (read_meta p MKlen))) r
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
Definition lim_avail (e : env) (p : packet) (spec : limit_spec) : nat :=
  Nat.min (e_limit e spec) (lim_max spec).

(** The non-inverted "under / not exceeded" test: PASS iff the available tokens
    cover the cost ([delta = tokens - cost >= 0]).  This is the value nft_limit_eval
    returns BEFORE XOR-ing the invert bit. *)
Definition lim_under (e : env) (p : packet) (spec : limit_spec) : bool :=
  Nat.leb (lim_cost p spec) (lim_avail e p spec).

(** Per-evaluation byte cost charged to a `quota`: the packet's [meta len], i.e.
    the kernel's [skb->len] (nft_overquota: [consumed += skb->len]).  This is the
    same length expression that byte-mode [lim_cost] uses. *)
Definition quota_cost (p : packet) : nat :=
  N.to_nat (data_to_N (read_meta p MKlen)).

(** The non-inverted "under / not over quota" test.  With [e_quota] tracking the
    REMAINING bytes ([quota - consumed]), the kernel's post-add state is
    [consumed' = consumed + skb->len] and it BREAKs iff [consumed' > quota].  In
    remaining terms that is PASS iff [consumed + cost <= quota], i.e. iff
    [cost <= remaining] — a packet landing exactly on the quota still passes.
    Mirrors [lim_under]'s [Nat.leb cost avail]. *)
Definition quota_under (e : env) (p : packet) (spec : quota_spec) : bool :=
  Nat.leb (quota_cost p) (e_quota e spec).

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
Definition connlimit_count (e : env) (p : packet) (spec : connlimit_spec) : nat :=
  List.length (connlimit_after e spec (pkt_flow p)).

(** The non-inverted "under / not over the connection limit" test.  The kernel
    BREAKs iff [(count > limit) ^ invert] (nft_connlimit.c:47, STRICT >), so the
    non-inverted PASS test is [count <= limit], i.e. [negb (limit < count)].
    Because a packet of an ALREADY-counted connection does not grow [count], ANY
    number of packets of ONE connection read the SAME count and a `connlimit N`
    with [N >= 1] never throttles a single connection; and [count <= N] permits up
    to N+1 distinct connections (count breaks only at N+1 > N). *)
Definition connlimit_under (e : env) (p : packet) (spec : connlimit_spec) : bool :=
  negb (Nat.ltb (cl_count spec) (connlimit_count e p spec)).

(** The unguarded comparison body of a match (the original semantics). *)
Definition eval_matchcond_body (m : matchcond) (e : env) (p : packet) : bool :=
  match m with
  (* [MEq]/[MNeq] are the kernel cmp operator itself ([eval_cmp CEq]/[CNe],
     nft_cmp_eval's memcmp over the cmp value's length): exact equality for a
     full-width immediate, the kernel's short-value prefix compare otherwise.
     The SURFACE distinction (typed equality vs CIDR vs wildcard) lives in the
     typed layer (Surface.Typed.txmatch), whose elaboration picks the shape. *)
  | MEq  f v => eval_cmp CEq (field_value f e p) v
  | MNeq f v => eval_cmp CNe (field_value f e p) v
  | MRange f neg lo hi =>
      eval_range (if neg then CNe else CEq) (field_value f e p) lo hi
  | MMasked f op mask xor v =>
      eval_cmp op (data_bitops (field_value f e p) mask xor) v
  | MCmp f op v => eval_cmp op (field_value f e p) v
  | MConcatSet fields neg name =>
      (* membership of the concatenated key in the *named* set, whose contents are
         read from the runtime environment [e], not inlined in the rule.
         A concatenated set is NFT_SET_CONCAT: the kernel matches EACH FIELD
         against its OWN [lo,hi] independently (the set is the cross-product of
         the per-field intervals, NOT one flat lexicographic interval over the
         concatenation).  So we pass the per-field value list to
         [concat_set_mem], which splits each stored element's bound by the
         per-field widths and tests every field separately.  For a single field
         this coincides with the old flat [set_mem] ([concat_set_mem_single]). *)
      xorb neg (concat_set_mem (map (fun f => field_value f e p) fields)
                         (e_set e name))
  | MTransform f ts op v =>
      eval_cmp op (apply_transforms ts (field_value f e p)) v
  | MSetT f ts neg name =>
      xorb neg (set_mem (apply_transforms ts (field_value f e p))
                         (e_set e name))
  | MRangeT f ts neg lo hi =>
      eval_range (if neg then CNe else CEq) (apply_transforms ts (field_value f e p)) lo hi
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
      xorb (Nat.eqb (Nat.land (ls_flags spec) 1) 1) (lim_under e p spec)
  | MQuota spec =>
      xorb (Nat.eqb (Nat.land (q_flags spec) 1) 1) (quota_under e p spec)
  | MConnlimit spec =>
      xorb (Nat.eqb (Nat.land (cl_flags spec) 1) 1) (connlimit_under e p spec)
  | MConcatSetT elems neg name =>
      (* like [MConcatSet] but each element is transformed before concatenation;
         contents read from the named set in [e].  Per-field membership
         (cross-product of per-field intervals), as for [MConcatSet]. *)
      xorb neg (concat_set_mem
        (map (fun fe => apply_transforms (snd fe) (field_value (fst fe) e p)) elems)
        (e_set e name))
  end.

(** A match condition: [false] (does not apply) if its load breaks, else the
    ordinary comparison. *)
Definition eval_matchcond (m : matchcond) (e : env) (p : packet) : bool :=
  andb (match_loadable m p) (eval_matchcond_body m e p).

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
    packet component — including the shared env and its flow-keyed [e_ct] table —
    is preserved, so that a `ct mark`/other-key read is unaffected.  This is the
    per-packet-traversal state both the DSL ([body_step]) and
    the VM ([run_rule_step]) apply on [SNotrack]/[INotrack], keeping the
    two in lock-step. *)
Definition set_untracked (p : packet) : packet :=
  if pkt_ct_present p then p
  else with_pkt_untracked p true.

(** Update the SHARED `numgen inc` counter [e_numgen] for instance [spec]: INCREMENT
    it by one, leaving every other instance's counter — and every other env
    component — unchanged.  Mirrors the kernel's atomic_cmpxchg advancing the
    instance's [atomic_t *counter] by one per evaluation (nft_ng_inc_gen).

    [e_numgen spec] (Packet.v) denotes the COUNT of evaluations the instance has
    performed so far: the kernel stores the last returned [nval]; the model stores
    the eval count [c], from which the kernel's stored value is recovered as
    [c mod modulus].  Each `numgen inc` expression has its OWN counter, keyed by
    [numgen_spec] (nft_ng_inc_init allocates one per expression).  A load reads
    [(e_numgen spec mod ng_mod spec) + ng_offset spec] (big-endian, 4 bytes) and
    this update then makes the NEXT evaluation — this packet's later firing or the
    next packet's — read the successor: successive evals are round-robin
    0,1,…,N-1,0,….  The increment is threaded across packets by
    [run_rule_step]/[body_step] exactly like the dynset/ct/nat env writes.
    ONLY the incremental generator (ng_random = false) uses [e_numgen]; the RANDOM
    generator (nft_ng_random_gen: get_random_u32) is the genuine per-packet oracle
    [pkt_numgen]. *)
Definition env_numgen_upd (e : env) (spec : numgen_spec) : env :=
  with_e_numgen e
    (fun s => if numgen_eqb spec s then S (e_numgen e s) else e_numgen e s).

(** Update the SHARED rate-limiter token bucket [e_limit] for instance [spec] on
    packet [p].  The UPDATE FORMULA is exactly the kernel nft_limit_eval's
    (elapsed refill +0):
      cap   = min(stored, lim_max spec)         (the burst-derived bucket cap)
      delta = cap - lim_cost p spec
      delta >= 0 -> store delta (PASS, consume the cost)
      delta <  0 -> store cap   (EXHAUSTED, the level after capping is kept)
    Every other instance's bucket — and every other env component — is preserved.
    The new level is therefore a genuine function of [ls_rate]/[ls_unit]/[ls_burst]
    (and the packet length in byte mode), not a fixed decrement-by-one.
    WHEN this update is invoked is kernel-exact too: the per-rule folds
    ([body_step]/[run_rule_step]) apply it at the limiter's own body /
    instruction position, so a limiter after a failing match (which the kernel
    NFT_BREAKs past before nft_limit_eval) is never evaluated and never
    consumes (pinned in Regression/Known_Infidelities.v § repaired entry 1). *)
Definition lim_newtokens (e : env) (p : packet) (spec : limit_spec) : nat :=
  let cap := lim_avail e p spec in
  if Nat.leb (lim_cost p spec) cap then cap - lim_cost p spec else cap.

Definition env_limit_upd (e : env) (p : packet) (spec : limit_spec) : env :=
  with_e_limit e
    (fun s => if limit_eqb spec s then lim_newtokens e p spec else e_limit e s).

(** Update the SHARED quota counter [e_quota] for instance [spec] on packet [p]:
    CONSUME the packet's byte length ([quota_cost p], = skb->len) UNCONDITIONALLY
    (the kernel nft_overquota accumulates skb->len on every evaluation, regardless
    of whether the rule passes).  With [e_quota] holding the REMAINING bytes, the
    consumption is a saturating subtraction of the cost (nat truncates at 0 once the
    quota is fully spent).  Mirrors byte-mode [limit] ([env_limit_upd], which
    likewise takes [p] and charges [lim_cost p]). *)
Definition env_quota_upd (e : env) (p : packet) (spec : quota_spec) : env :=
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
Definition env_connlimit_upd (e : env) (p : packet) (spec : connlimit_spec) : env :=
  with_e_connlimit e
    (fun s => if connlimit_eqb spec s
              then connlimit_after e spec (pkt_flow p)
              else e_connlimit e s).

(** Advance the shared `numgen inc` counter once: the side effect of EVALUATING a
    `numgen inc` expression.  The value the eval RETURNS is read by [do_load] BEFORE
    this from [e_numgen]; [set_numgen] then bumps the counter so the NEXT evaluation
    (this rule's later firing, threaded within the rule, or — through the
    cross-packet env threading by [run_rule_step]/[body_step] — the next packet's
    firing) reads the successor.  `numgen random` (ng_random = true) has no counter,
    so it is a no-op.  Only [e_numgen] changes; every other env component is
    preserved — and the packet is untouched by construction (the setter is a pure
    env update), so all loadability predicates are trivially invariant and the
    DSL/VM stay in lock-step. *)
Definition set_numgen (e : env) (spec : numgen_spec) : env :=
  if ng_random spec then e else env_numgen_upd e spec.

(** UPDATE a `limit` token bucket for one evaluation of the limiter on packet [p]
    — the kernel nft_limit_eval writes `tokens` on both the pass and the exhausted
    branch (see [env_limit_upd]/[lim_newtokens]).  Only [e_limit] changes; every
    other env component is preserved and the packet is untouched.  Invoked once
    per EVALUATION, exactly like the kernel: the folds apply it at the
    limiter's own position ([match_consume]/[run_rule_step]'s [ILimit]), so an
    unreached limiter consumes nothing. *)
Definition set_limit (e : env) (p : packet) (spec : limit_spec) : env :=
  env_limit_upd e p spec.

(** CONSUME the packet's byte length ([quota_cost p], = skb->len) from a `quota`
    UNCONDITIONALLY (the kernel accumulates skb->len on every evaluation). *)
Definition set_quota (e : env) (p : packet) (spec : quota_spec) : env :=
  env_quota_upd e p spec.

(** ACCOUNT for the packet's connection in a `connlimit` instance: IDEMPOTENTLY insert
    [pkt_flow p] into the instance's distinct-connection set on EVERY evaluation (the
    kernel nft_connlimit_do_eval always calls [nf_conncount_add_skb] before reading the
    count, regardless of whether the rule passes; re-adding a counted connection is the
    -EEXIST no-op).  Only [e_connlimit] changes; every other env component is
    preserved and the packet is untouched. *)
Definition set_connlimit (e : env) (p : packet) (spec : connlimit_spec) : env :=
  env_connlimit_upd e p spec.

(** Whether a program contains NO incremental [INumgen].  Holds for every
    compiled real ruleset (numgen has no DSL/parser surface); the domain on
    which [run_rule_step]'s in-fold counter advance never fires. *)
Definition numgen_free_prog (is : list instr) : bool :=
  forallb (fun i => match i with INumgen spec _ => ng_random spec | _ => true end) is.

(** ** Source-side numgen-freedom (definition in IR/Syntax.v).

    [numgen_free_prog] above is a BYTECODE predicate; its source-AST twin
    [rule_numgen_free] lives in IR/Syntax.v (next to the rule record), where
    the LOWERING gates on it fail-loud ([Lower.LEnumgen]) — so the compiler
    theorems' [rule_numgen_free] hypothesis is discharged for every
    frontend-emitted program ([Lower_Proofs.lower_ruleset_numgen_free]).
    [Correct.numgen_free_compile_rule] proves the two predicates agree
    exactly: [numgen_free_prog (compile_rule r) = rule_numgen_free r]. *)

(** The env consumption of EVALUATING one match condition — the kernel writes
    a `limit`/`quota`/`connlimit`'s shared bucket on every evaluation of the
    expression, pass or fail (nft_limit_eval stores `tokens` on both branches;
    nft_overquota accumulates skb->len unconditionally; nft_connlimit always
    nf_conncount_add_skb's the tuple).  Every other match reads only.  The
    per-rule folds apply this AT the match's position ([body_step]), so a
    limiter after a failing match — which the kernel NFT_BREAKs past before
    ever evaluating it — consumes NOTHING.  The verdict test itself
    ([eval_matchcond]) reads the PRE-write bucket, exactly the kernel's
    read-tokens-then-store order. *)
Definition match_consume (m : matchcond) (e : env) (p : packet) : env :=
  match m with
  | MLimit spec     => set_limit e p spec
  | MQuota spec     => set_quota e p spec
  | MConnlimit spec => set_connlimit e p spec
  | _ => e
  end.

(** A match with no limiter consumes nothing. *)
Definition match_consumefree (m : matchcond) : bool :=
  match m with MLimit _ | MQuota _ | MConnlimit _ => false | _ => true end.

Lemma match_consume_free_id : forall m e p,
  match_consumefree m = true -> match_consume m e p = e.
Proof. intros m e p H; destruct m; try reflexivity; discriminate H. Qed.

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
  destruct (set_untracked_proj p) as (Hmeta & Hl2 & Hl4 & Hfr & Heh & Hlh & Hnh
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

(** Whether a body contains a `notrack` statement (the latch source).  When
    [false] the walk's [set_untracked] threading never fires, so
    [rule_applies_walk] is exactly the original
    [forallb eval_matchcond (body_matches …)] over [p]. *)
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
    ROLE: this is the WRITE-FREE projection of the per-rule fold — the pure
    strand ([eval_rules]/[run_program], the optimizer theorems) consumes it,
    and on rules without mutating statements it agrees with the authoritative
    single fold [rule_step] below ([rule_step_mutfree]); a rule WITH intra-rule
    writes is evaluated by the fold, which threads them.
    Statements are walked in ORDER: a SYN-proxy statement that STOPS traversal
    (see [synproxy_stops]) short-circuits — any match positioned AFTER it is
    unreachable (the kernel has already STOLEN/DROPped the packet), so the
    remaining matches vacuously pass; a match positioned BEFORE a stopping synproxy
    still gates whether the synproxy runs at all (a failing earlier match BREAKs
    the rule first).  Every other statement is verdict-neutral.  When the body has
    no stopping synproxy this is exactly [forallb eval_matchcond (body_matches …)]
    (proved as [rule_applies_no_synproxy]). *)
Fixpoint rule_applies_walk (body : list body_item) (e : env) (p : packet) : bool :=
  match body with
  | [] => true
  | BMatch m :: rest => eval_matchcond m e p && rule_applies_walk rest e p
  | BStmt (SSynproxy _ _) :: rest =>
      if synproxy_stops p then true else rule_applies_walk rest e p
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
     (the compiled [INotrack] threads the same [set_untracked]).  This threading
     is NOT a parallel semantics: it is the SAME transform [body_step]'s
     [SNotrack] case applies, and [rule_purewalk_ok] (end of file) proves the
     walk IS the break/no-break projection of the fold on every effect-free-
     but-notrack body its callers feed it. *)
  | BStmt SNotrack :: rest => rule_applies_walk rest e (set_untracked p)
  | BStmt _ :: rest => rule_applies_walk rest e p
  end.
Definition rule_applies (r : rule) (e : env) (p : packet) : bool :=
  rule_applies_walk (r_body r) e p.

(** When the body contains no stopping synproxy AND no `notrack` (so the
    walk's [set_untracked] threading never fires),
    [rule_applies_walk] is exactly
    [forallb eval_matchcond] over the body's matches against the ORIGINAL [p]. *)
Lemma rule_applies_walk_no_synproxy : forall body e p,
  body_synproxy_stops body p = false ->
  body_has_notrack body = false ->
  rule_applies_walk body e p = forallb (fun m => eval_matchcond m e p) (body_matches body).
Proof.
  induction body as [| it body IH]; intros e p Hsp Hnt; [reflexivity|].
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

(** The concatenated lookup key of a map-sourced NAT operand (`dnat to … map`):
    the first field is transformed in place, the rest are taken raw, then all are
    concatenated — exactly the operand the compiler leaves in the key registers
    (cf. [nat_addr] / [compile_terminal]). *)
Definition nat_map_key (fields : list field) (ts : list transform)
                       (e : env) (p : packet) : data :=
  match fields with
  | [] => []   (* no key fields: the empty concatenation (matches the VM register key) *)
  | f0 :: frest =>
      List.concat (apply_transforms ts (field_value f0 e p)
                   :: map (fun f => field_value f e p) frest)
  end.

Definition terminal_loadable (r : rule) (e : env) (p : packet) : bool :=
  match r_nat r with
  | Some n => match nat_src n with
              | Some vs => vsrc_loadable vs p
              | None => match nat_map n with
                        (* a data-map operand BREAKs (NFT_BREAK) on a key the map
                           does not contain: the lookup must HIT for the terminal
                           NAT to apply (matches the VM's [ILookupValBr] break). *)
                        | Some (fields, ts, name) =>
                            fields_loadable fields p
                            && map_has_key (nat_map_key fields ts e p) (e_map e name)
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
    set/mangle/NAT statement.  [run_vsrc_value] (in Correct) proves the compiled
    operand leaves exactly this in reg 1; this is the foundation for modelling
    mutation: a `meta mark set vs` writes [eval_vsrc vs p].
    (Defined to mirror the bytecode, incl. its simplifications — faithfulness of
    e.g. jhash-over-concatenation to the kernel is checked separately, by the
    corpus/validate gates.) *)
Definition eval_vsrc (vs : vsrc) (e : env) (p : packet) : data :=
  match vs with
  | VImm v      => v
  | VField f ts => apply_transforms ts (field_value f e p)
  | VMap fields ts name =>
      let key := match fields with
                 | [] => apply_transforms ts []
                 | f0 :: frest =>
                     List.concat (apply_transforms ts (field_value f0 e p)
                                  :: map (fun f => field_value f e p) frest)
                 end in
      map_lookup_data key (e_map e name)
  | VHash fields len seed modulus offset =>
      data_jhash len seed modulus offset
        (match fields with [] => [] | f0 :: _ => field_value f0 e p end)
  | VOr srcs final =>
      match srcs with
      | [] => []
      | base :: rest =>
          apply_transforms final
            (fold_left
               (fun acc fe => data_or acc (apply_transforms (snd fe) (field_value (fst fe) e p)))
               rest (apply_transforms (snd base) (field_value (fst base) e p)))
      end
  | VMapT elems name =>
      map_lookup_data
        (List.concat (map (fun fe => apply_transforms (snd fe) (field_value (fst fe) e p)) elems))
        (e_map e name)
  | VHashMap fields len seed modulus offset name =>
      map_lookup_data
        (data_jhash len seed modulus offset
           (match fields with [] => [] | f0 :: _ => field_value f0 e p end))
        (e_map e name)
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
Definition outcome_core (r : rule) (e : env) (p : packet) : option verdict :=
  match r_vmap r with
  | Some vm =>
      let key := match vm_keyf vm with
                 | Some (f, ts) => apply_transforms ts (field_value f e p)
                 | None => List.concat (map (fun f => field_value f e p) (vm_fields vm))
                 end in
      match assoc_verdict key (e_vmap e (vm_name vm)) with
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

Definition outcome (r : rule) (e : env) (p : packet) : option verdict :=
  if body_synproxy_stops (r_body r) p then Some Drop
  else outcome_core r e (body_thread (r_body r) p).

(** ** Ratchet: the outcome sum evaluates exactly as the old product encoding.

    [terminal_outcome_prod]/[outcome_core_prod]/[outcome_prod] are verbatim the
    pre-sum evaluation over the historical [rule_prod] record (one filler
    verdict + five optional slots).  [run_rule_outcome_eq] proves that
    translating a well-formed product ([Syntax.prod_wf]: at most one populated
    slot, filler [Continue] under a vmap) through [rule_of_prod] preserves the
    rule outcome on every env/packet — the representation change is
    evaluation-invisible. *)
Definition terminal_outcome_prod (rp : rule_prod) (p : packet) : option verdict :=
  match rp_nat rp with
  | Some _ => Some Accept
  | None =>
  match rp_tproxy rp with
  | Some _ => Some Accept
  | None =>
  match rp_fwd rp with
  | Some _ => Some Accept
  | None =>
  match rp_queue rp with
  | Some _ => Some Accept
  | None => match rp_verdict rp with
            | Continue => stmts_after_outcome (rp_after rp) p
            | v => Some v
            end
  end
  end
  end
  end.

Definition outcome_core_prod (rp : rule_prod) (e : env) (p : packet) : option verdict :=
  match rp_vmap rp with
  | Some vm =>
      let key := match vm_keyf vm with
                 | Some (f, ts) => apply_transforms ts (field_value f e p)
                 | None => List.concat (map (fun f => field_value f e p) (vm_fields vm))
                 end in
      match assoc_verdict key (e_vmap e (vm_name vm)) with
      | Some v => Some v
      | None   => terminal_outcome_prod rp p
      end
  | None => terminal_outcome_prod rp p
  end.

Definition outcome_prod (rp : rule_prod) (e : env) (p : packet) : option verdict :=
  if body_synproxy_stops (rp_body rp) p then Some Drop
  else outcome_core_prod rp e (body_thread (rp_body rp) p).

Theorem run_rule_outcome_eq : forall rp e p,
  prod_wf rp = true ->
  outcome (rule_of_prod rp) e p = outcome_prod rp e p.
Proof.
  intros rp e p Hwf.
  unfold outcome, outcome_prod, rule_of_prod, prod_wf in *; cbn [r_body].
  destruct (body_synproxy_stops (rp_body rp) p); [reflexivity|].
  unfold outcome_core, outcome_core_prod, terminal_outcome, terminal_outcome_prod,
         r_vmap, r_nat, r_tproxy, r_fwd, r_queue, r_verdict, r_after, r_outcome,
         outcome_of_prod in *; cbn.
  destruct (rp_vmap rp) as [vm|]; destruct (rp_nat rp) as [ns|];
    destruct (rp_tproxy rp) as [tp|]; destruct (rp_fwd rp) as [fw|];
    destruct (rp_queue rp) as [q|]; try discriminate Hwf; cbn.
  - (* vmap + NAT: the miss fires the terminal NAT (OVmapNat) *)
    reflexivity.
  - (* vmap only: filler verdict is Continue *)
    destruct (rp_verdict rp); try discriminate Hwf; reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - destruct (rp_verdict rp); reflexivity.
Qed.

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
Definition tail_loadable (r : rule) (e : env) (p : packet) : bool :=
  terminal_loadable r e p &&
  (match terminal_outcome r p with
   | None => forallb (fun s => stmt_loadable s p) (r_after r)  (* fall-through: r_after runs *)
   | Some _ => true                                            (* terminal: r_after skipped *)
   end).

(** Loadability of a rule's outcome computation (verdict map then terminal),
    mirroring [outcome]'s evaluation order. *)
Definition end_loadable (r : rule) (e : env) (p : packet) : bool :=
  match r_vmap r with
  | Some vm =>
      vmap_loadable (r_vmap r) p &&
      (let key := match vm_keyf vm with
                  | Some (f, ts) => apply_transforms ts (field_value f e p)
                  | None => List.concat (map (fun f => field_value f e p) (vm_fields vm))
                  end in
       match assoc_verdict key (e_vmap e (vm_name vm)) with
       | Some _ => true                (* vmap HIT: terminal/r_after unreachable *)
       | None   => tail_loadable r e p (* vmap MISS: terminal runs *)
       end)
  | None => tail_loadable r e p
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
Definition rule_loadable (r : rule) (e : env) (p : packet) : bool :=
  body_loadable_walk (r_body r) p &&
  (if body_synproxy_stops (r_body r) p then true
   else end_loadable r e (body_thread (r_body r) p)).

(** Evaluate a rule list.  [None] means "fell through every rule"; [Some v]
    means a terminal verdict [v] was reached.  A [Continue] verdict on an
    applicable rule simply proceeds, exactly like a non-applicable rule.

    NON-RECURSIVE (M6): the pure strand owns no recursion of its own — this is
    a [fold_right] of the per-rule read [rule_loadable]/[rule_applies]/[outcome]
    (the write-free per-rule projection, [rule_step_mutfree]); the ONE recursive
    rule-list traversal on the DSL side is the unified [eval_rules_u].  Proofs
    step this definition with [eval_rules_nil]/[eval_rules_cons], which restate
    the historical unfolding verbatim. *)
Definition eval_rules (rs : list rule) (e : env) (p : packet) : option verdict :=
  fold_right (fun r k =>
      if rule_loadable r e p && rule_applies r e p then
        match outcome r e p with
        | Some v => if terminal v then Some v else k
        | None   => k
        end
      else k) None rs.

Arguments eval_rules : simpl never.

Lemma eval_rules_nil : forall e p, eval_rules [] e p = None.
Proof. reflexivity. Qed.

Lemma eval_rules_cons : forall r rest e p,
  eval_rules (r :: rest) e p
  = if rule_loadable r e p && rule_applies r e p then
      match outcome r e p with
      | Some v => if terminal v then Some v else eval_rules rest e p
      | None   => eval_rules rest e p
      end
    else eval_rules rest e p.
Proof. reflexivity. Qed.

Definition eval_chain (c : chain) (e : env) (p : packet) : verdict :=
  match eval_rules (c_rules c) e p with
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
    RETURN pops to the caller).  The faithful interpreter is the unified
    [eval_rules_u]/[eval_table_u] (§ "The unified semantics", end of file); on
    write-free rules the environment-aware pure [eval_rules_j]/[eval_table]
    below coincides with it ([eval_rules_u_writefree]).

    [outcome_jumpfree r p] holds exactly when the rule's realised outcome on [p]
    is NOT a control-transfer verdict; [rules_jumpfree]/[chain_jumpfree] lift it to
    a rule list / chain.  On this domain — and only on it — the cheap
    environment-free [eval_chain] coincides with the faithful [eval_table] (see
    [eval_rules_jumpfree_eq_j] / [eval_chain_eq_table_jumpfree] in Correct.v). *)
Definition outcome_jumpfree (r : rule) (e : env) (p : packet) : bool :=
  match outcome r e p with
  | Some (Jump _) | Some (Goto _) | Some Return => false
  | _ => true
  end.

Definition rules_jumpfree (rs : list rule) (e : env) (p : packet) : bool :=
  forallb (fun r => outcome_jumpfree r e p) rs.

Definition chain_jumpfree (c : chain) (e : env) (p : packet) : bool :=
  rules_jumpfree (c_rules c) e p.

(** ** Bytecode VM semantics. *)

(** Run one rule's program over a register file.  [None] means a [cmp] failed
    (the rule does not apply, like netfilter "breaking" out of the rule);
    [Some v] means an [immediate] set verdict [v]. *)
Fixpoint run_rule (rf : regfile) (is : rule_prog) (e : env) (p : packet) : option verdict :=
  match is with
  | [] => None
  | IMetaLoad k dst :: rest =>
      run_rule (set_reg rf dst (read_meta p k)) rest e p
  | ICtLoad k dst :: rest =>
      (* identical to [do_load (LCt k)]: every key reads the SHARED flow-keyed
         conntrack table [e_ct] at this packet's flow, EXCEPT that
         a `ct state` read after a `notrack` returns NF_CT_STATE_UNTRACKED_BIT.  A
         conntrack load on a packet with NO entry ([pkt_ct_present = false]) BREAKs the
         rule for EVERY key except [CKstate] (kernel nft_ct.c:81-82 `if (ct == NULL)
         goto err`); gate on the same [load_ok] predicate the DSL uses so DSL/VM stay
         in lock-step. *)
      if load_ok (LCt k) p
      then run_rule (set_reg rf dst (do_load (LCt k) e p)) rest e p
      else None
  | IRtLoad k dst :: rest =>
      run_rule (set_reg rf dst (read_rt e k)) rest e p
  | ISocketLoad k dst :: rest =>
      run_rule (set_reg rf dst (read_socket p k)) rest e p
  | INumgen spec dst :: rest =>
      (* `numgen inc` reads the SHARED counter value (= [do_load (LNumgen spec) e p],
         deterministic from [e_numgen]) into the dreg.  [run_rule] is the write-free
         projection of the fold, so it only READS the counter; the COUNTER ADVANCE
         (the cross-packet round-robin) is applied in-fold by [run_rule_step]'s
         [INumgen] case — VM-only, with no DSL twin: the lowering rejects
         incremental numgen fail-loud ([Lower.LEnumgen]), so every frontend-emitted
         rule is [rule_numgen_free] and the advance never fires there
         ([Lower_Proofs.lower_ruleset_numgen_free]).  Reading [do_load] keeps this
         lock-step with the DSL [outcome]. *)
      run_rule (set_reg rf dst (do_load (LNumgen spec) e p)) rest e p
  | IOsf dst :: rest =>
      run_rule (set_reg rf dst (read_osf p)) rest e p
  | IExthdrLoad ep h o l pr dst :: rest =>
      (* A VALUE load (pr=false) of an ABSENT extension-header / TCP-option /
         SCTP-chunk makes the kernel set NFT_BREAK (nft_exthdr_*_eval err path).
         An EXISTENCE load (pr=true) never breaks (stores 0 under F_PRESENT).
         Gate on the same predicate the DSL's [load_ok] uses. *)
      if load_ok (LExthdr ep h o l pr) p
      then run_rule (set_reg rf dst (pkt_eh p ep h o l pr)) rest e p
      else None
  | IFibLoad sel res dst :: rest =>
      run_rule (set_reg rf dst (lpm_fib (e_routes e) (pkt_fibkey p sel) res)) rest e p
  | ICtDirLoad key dir dst :: rest =>
      run_rule (set_reg rf dst (pkt_ctdir p key dir)) rest e p
  | IXfrmLoad dir sp key dst :: rest =>
      run_rule (set_reg rf dst (pkt_xfrm p dir sp key)) rest e p
  | ITunnelLoad key dst :: rest =>
      run_rule (set_reg rf dst (pkt_tunnel p key)) rest e p
  | ISymhash m o dst :: rest =>
      run_rule (set_reg rf dst (read_symhash p m o)) rest e p
  | IInnerLoad t h fl desc _ dst :: rest =>
      run_rule (set_reg rf dst (pkt_inner p t h fl desc)) rest e p
  | IPayloadLoad b o l dst :: rest =>
      (* A payload read that runs off the end of the header (or a transport read on
         a fragment / no-L4 packet) makes the kernel set the verdict to NFT_BREAK,
         i.e. the rule does NOT match.  Model that as breaking the rule here
         ([None]), rather than loading a truncated value. *)
      if read_payload_ok b o l p
      then run_rule (set_reg rf dst (read_payload b o l p)) rest e p
      else None
  | ICmp op src v :: rest =>
      if eval_cmp op (rf src) v then run_rule rf rest e p else None
  | IRange op src lo hi :: rest =>
      if eval_range op (rf src) lo hi then run_rule rf rest e p else None
  | IBitwise dst src mask xor :: rest =>
      run_rule (set_reg rf dst (data_bitops (rf src) mask xor)) rest e p
  | IBitwiseOr dst src1 src2 :: rest =>
      run_rule (set_reg rf dst (data_or (rf src1) (rf src2))) rest e p
  | IBitShift dst src shl amt :: rest =>
      run_rule (set_reg rf dst (data_shift shl amt (rf src))) rest e p
  | IByteorder dst src h sz len :: rest =>
      run_rule (set_reg rf dst (data_byteorder h sz len (rf src))) rest e p
  | IJhash dst src l s m o :: rest =>
      run_rule (set_reg rf dst (data_jhash l s m o (rf src))) rest e p
  | ILookup srcs name neg :: rest =>
      (* set membership: contents read from the named set in [e].  Each
         source register holds one concatenated field's value, so [map rf srcs]
         is the per-field value list; [concat_set_mem] tests each field against
         its own per-field interval (NFT_SET_CONCAT cross-product semantics). *)
      if xorb neg (concat_set_mem (map rf srcs) (e_set e name))
      then run_rule rf rest e p else None
  | IVmap srcs name :: rest =>
      (* a verdict map: a hit terminates with that verdict; a miss falls through
         to the rest (e.g. a trailing redirect/masquerade), exactly as nft does.
         Entries are read by [name] from [e]. *)
      match assoc_verdict (List.concat (map rf srcs)) (e_vmap e name) with
      | Some v => Some v
      | None   => run_rule rf rest e p
      end
  | IImmediateData dst v :: rest =>
      run_rule (set_reg rf dst v) rest e p
  (* Set/mangle: no-ops in this WRITE-FREE projection.  [run_rule] is the
     mutation-free evaluator the pure strand ([eval_rules]/[run_program], the
     optimizer theorems) consumes; the authoritative per-rule semantics is the
     single fold [run_rule_step] below, which applies these writes to the
     running state so a later expression of the SAME rule reads them (kernel
     nft_rule_dp_for_each_expr).  On rules without mutating statements the two
     agree ([Correct.run_rule_step_no_writes] / [rule_step_mutfree]). *)
  | IPayloadWrite _ _ _ _ _ _ _ :: rest => run_rule rf rest e p
  | IMetaSet _ _ :: rest => run_rule rf rest e p
  | ICtSet _ _ :: rest => run_rule rf rest e p
  | ILookupVal keys name dreg :: rest =>
      run_rule (set_reg rf dreg (map_lookup_data (List.concat (map rf keys))
                                                 (e_map e name))) rest e p
  | ILookupValBr keys name dreg :: rest =>
      (* a map lookup feeding a terminal operand: BREAK on a miss (the terminal
         does not fire), else load the value and continue. *)
      if map_has_key (List.concat (map rf keys)) (e_map e name)
      then run_rule (set_reg rf dreg (map_lookup_data (List.concat (map rf keys))
                                                      (e_map e name))) rest e p
      else None
  | INat _ _ _ _ _ _ _ :: _ => Some Accept   (* terminal *)
  | ITproxy _ _ _ :: _ => Some Accept        (* terminal redirect *)
  | IFwd _ _ _ :: _ => Some Accept           (* terminal forward *)
  | IQueueSreg _ _ _ :: _ => Some Accept     (* terminal queue *)
  | ILimit spec :: rest =>
      (* the limit instruction carries NFT_LIMIT_F_INV (bit 0 of ls_flags); the
         kernel BREAKs iff [under_test ^ invert].  Continue iff [match] = the
         negation, i.e. iff the matchcond body is true. *)
      if xorb (Nat.eqb (Nat.land (ls_flags spec) 1) 1) (lim_under e p spec)
      then run_rule rf rest e p else None
  | IQuota spec :: rest =>
      if xorb (Nat.eqb (Nat.land (q_flags spec) 1) 1) (quota_under e p spec)
      then run_rule rf rest e p else None
  | IConnlimit spec :: rest =>
      if xorb (Nat.eqb (Nat.land (cl_flags spec) 1) 1) (connlimit_under e p spec)
      then run_rule rf rest e p else None
  | ICounter _ _ :: rest => run_rule rf rest e p   (* verdict-neutral *)
  (* `notrack` is verdict-neutral but forces IP_CT_UNTRACKED for the rest of this
     rule's traversal: thread [set_untracked] so a later [ICtLoad CKstate] reads
     the untracked bit (lock-step with [rule_applies_walk]'s [SNotrack]). *)
  | INotrack :: rest      => run_rule rf rest e (set_untracked p)
  | ILog _ :: rest        => run_rule rf rest e p
  | IObjref _ _ :: rest   => run_rule rf rest e p   (* verdict-neutral *)
  | ISynproxy _ _ :: rest =>
      (* SYN-proxy: a non-TCP packet BREAKs the rule (NFT_BREAK); a TCP packet with
         SYN or ACK set STOPS traversal (NF_STOLEN/NF_DROP, modelled as terminal
         Drop); any other TCP packet falls through (NFT_CONTINUE).  See
         [synproxy_loadable]/[synproxy_stops]. *)
      if synproxy_loadable p
      then (if synproxy_stops p then Some Drop else run_rule rf rest e p)
      else None
  | ILast _ :: rest       => run_rule rf rest e p
  | IDynset _ _ _ _ _ :: rest => run_rule rf rest e p   (* verdict-neutral *)
  | IExthdrReset _ _ :: rest => run_rule rf rest e p (* verdict-neutral *)
  | IDup _ _ :: rest      => run_rule rf rest e p   (* verdict-neutral *)
  | IObjrefMap _ _ :: rest => run_rule rf rest e p  (* verdict-neutral *)
  | ICtSetDir _ _ _ :: rest => run_rule rf rest e p (* verdict-neutral *)
  | IExthdrWrite _ _ _ _ _ :: rest => run_rule rf rest e p (* verdict-neutral *)
  | IReject t c :: _ => Some (Reject t c)
  | IQueue lo hi b f :: _ => Some (Queue lo hi b f)
  | IImmediate v :: _ => Some v
  end.

(** Run a base chain's program: ordered per-rule programs, each from a fresh
    (empty) register file, stopping at the first terminal verdict.

    NON-RECURSIVE (M6): a [fold_right] of the write-free per-rule interpreter
    [run_rule]; the ONE recursive program traversal on the VM side is the
    unified [run_rules_u].  Step with [run_program_nil]/[run_program_cons]. *)
Definition run_program (prog : program) (e : env) (p : packet) : option verdict :=
  fold_right (fun rp k =>
      match run_rule empty_rf rp e p with
      | Some v => if terminal v then Some v else k
      | None   => k
      end) None prog.

Arguments run_program : simpl never.

Lemma run_program_nil : forall e p, run_program [] e p = None.
Proof. reflexivity. Qed.

Lemma run_program_cons : forall rp rest e p,
  run_program (rp :: rest) e p
  = match run_rule empty_rf rp e p with
    | Some v => if terminal v then Some v else run_program rest e p
    | None   => run_program rest e p
    end.
Proof. reflexivity. Qed.

Definition run_chain (prog : program) (policy : verdict) (e : env) (p : packet) : verdict :=
  match run_program prog e p with
  | Some v => v
  | None   => policy
  end.

(** ** In-traversal mutation: the single-fold rule semantics.

    A `meta mark set X` mutates state that BOTH a later expression of the SAME
    rule and every later rule read (kernel nft_rule_dp_for_each_expr: one
    left-to-right walk against the running state).  The primitives below
    ([set_meta]/[set_ct]/[env_set_upd]/[env_map_upd]) are the write effects;
    [run_rule_step] (bytecode) and [rule_step] (DSL) fold them into one
    per-rule traversal, and [eval_chain_mut]/[run_chain_mut] thread the state
    a rule leaves across rules (and, via the _env forms, across packets). *)

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
    emitted by the parser — but routing it through the same flow table keeps the
    write faithful and the DSL/VM in lock-step.

    KERNEL GUARD (nft_ct.c:288-290, nft_ct_set_eval):
    [ct = nf_ct_get(skb, &ctinfo); if (ct == NULL || nf_ct_is_template(ct)) return;]
    — the SET is a NO-OP when the packet has no conntrack entry.  So we gate the
    write on [pkt_ct_present p]: an entryless packet's `ct mark/label set` leaves
    [e_ct] (and the whole packet) unchanged, exactly mirroring how [set_untracked]
    gates the [notrack] latch on the dual guard.  This rules out the
    cross-packet bug where a later same-flow entry-bearing packet would read back a
    mark the kernel never wrote. *)
Definition set_ct (e : env) (p : packet) (k : ct_key) (v : data) : env :=
  if pkt_ct_present p then env_ct_upd e (pkt_flow p) k v
  else e.

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
  match l4_csum_slot (read_meta p MKl4proto) with
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
  destruct (l4_csum_slot (read_meta p MKl4proto)) as [[[coff clen] mand]|]; [|reflexivity].
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
  destruct (l4_csum_slot (read_meta p MKl4proto)) as [[[coff clen] mand]|] eqn:Hslot;
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
Definition saddr_slot (family : nat_af) : nat * nat :=
  if nataf_eqb family nat_fam_ip6 then (8, 16) else (12, 4).
Definition daddr_slot (family : nat_af) : nat * nat :=
  if nataf_eqb family nat_fam_ip6 then (24, 16) else (16, 4).

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
    performs; [set_saddr nat_fam_ip4 p (e_ifaddr e oifname)] realises
    `masquerade` = "use the IP of the interface the packet exits".  For IPv4 the
    IP header checksum is incrementally updated ([set_nh_addr_ip4], mirroring
    [csum_replace4]); IPv6 has no L3 checksum so it is a bare slot splice. *)
Definition set_saddr (family : nat_af) (p : packet) (v : data) : packet :=
  let '(off, len) := saddr_slot family in
  let old := slice (pkt_nh p) off len in
  let p1 :=
    if nataf_eqb family nat_fam_ip6 then set_nh_field p off len v
    else set_nh_addr_ip4 p off len v in
  set_l4_csum_addr p1 old v.

(** Destination-NAT a packet: rewrite its destination address (the [daddr_slot]
    for the NAT [family]) to [v].  This is the data-plane effect a
    `dnat`/`redirect` performs — the kernel `nft_nat` applies [NF_NAT_MANIP_DST]
    from [NFTNL_EXPR_NAT_REG_ADDR_MIN] (netlink_linearize.c:1304), and
    [nf_nat_ipv4_manip_pkt] also runs [csum_replace4] on the IPv4 header checksum. *)
Definition set_daddr (family : nat_af) (p : packet) (v : data) : packet :=
  let '(off, len) := daddr_slot family in
  let old := slice (pkt_nh p) off len in
  let p1 :=
    if nataf_eqb family nat_fam_ip6 then set_nh_field p off len v
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
  destruct (l4_csum_slot (read_meta p MKl4proto)) as [[[coff clen] mand]|] eqn:Hslot;
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
  destruct (nataf_eqb fam nat_fam_ip6); reflexivity.
Qed.
Lemma set_daddr_th_port : forall fam p v poff plen,
  poff + plen <= 6 ->
  slice (pkt_th (set_daddr fam p v)) poff plen = slice (pkt_th p) poff plen.
Proof.
  intros fam p v poff plen Hle. unfold set_daddr.
  destruct (daddr_slot fam) as [off len].
  rewrite slice_set_l4_csum_addr_port by lia.
  destruct (nataf_eqb fam nat_fam_ip6); reflexivity.
Qed.

(** [set_saddr]/[set_daddr] preserve the LENGTH of the transport header (the
    address splice never touches [pkt_th]; the L4-checksum splice is in-bounds). *)
Lemma set_saddr_th_len : forall fam p v,
  List.length (pkt_th (set_saddr fam p v)) = List.length (pkt_th p).
Proof.
  intros fam p v. unfold set_saddr. destruct (saddr_slot fam) as [off len].
  rewrite set_l4_csum_addr_th_len.
  destruct (nataf_eqb fam nat_fam_ip6); reflexivity.
Qed.
Lemma set_daddr_th_len : forall fam p v,
  List.length (pkt_th (set_daddr fam p v)) = List.length (pkt_th p).
Proof.
  intros fam p v. unfold set_daddr. destruct (daddr_slot fam) as [off len].
  rewrite set_l4_csum_addr_th_len.
  destruct (nataf_eqb fam nat_fam_ip6); reflexivity.
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
       if nataf_eqb fam nat_fam_ip6 then pkt_nh (set_nh_field p off len v)
       else pkt_nh (set_nh_addr_ip4 p off len v)).
Proof.
  intros fam p v. unfold set_saddr. destruct (saddr_slot fam) as [off len].
  rewrite set_l4_csum_addr_nh.
  destruct (nataf_eqb fam nat_fam_ip6); reflexivity.
Qed.
Lemma set_daddr_nh : forall fam p v,
  pkt_nh (set_daddr fam p v)
    = (let '(off, len) := daddr_slot fam in
       if nataf_eqb fam nat_fam_ip6 then pkt_nh (set_nh_field p off len v)
       else pkt_nh (set_nh_addr_ip4 p off len v)).
Proof.
  intros fam p v. unfold set_daddr. destruct (daddr_slot fam) as [off len].
  rewrite set_l4_csum_addr_nh.
  destruct (nataf_eqb fam nat_fam_ip6); reflexivity.
Qed.

(** IPv4 source/destination address read-back through the FULL NAT rewrite
    (address splice + L3 checksum update + L4 checksum update): the address slot
    survives byte-for-byte. *)
Lemma slice_set_saddr_ip4_same : forall p v,
  16 <= List.length (pkt_nh p) -> List.length v = 4 ->
  slice (pkt_nh (set_saddr nat_fam_ip4 p v)) 12 4 = v.
Proof.
  intros p v Hlen Hv. rewrite set_saddr_nh. change (saddr_slot nat_fam_ip4) with (12, 4).
  change (nataf_eqb nat_fam_ip4 nat_fam_ip6) with false; cbv iota.
  apply slice_set_nh_addr_ip4_same; lia.
Qed.
Lemma slice_set_daddr_ip4_same : forall p v,
  20 <= List.length (pkt_nh p) -> List.length v = 4 ->
  slice (pkt_nh (set_daddr nat_fam_ip4 p v)) 16 4 = v.
Proof.
  intros p v Hlen Hv. rewrite set_daddr_nh. change (daddr_slot nat_fam_ip4) with (16, 4).
  change (nataf_eqb nat_fam_ip4 nat_fam_ip6) with false; cbv iota.
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
Definition env_set_upd (e : env) (op : dynset_op) (name : String.string) (key : data) : env :=
  with_e_set e
    (fun n =>
       if String.eqb n name
       then if dynsetop_eqb op op_delete
            then filter (fun lh => negb (andb (data_eqb (fst lh) key) (data_eqb (snd lh) key)))
                        (e_set e n)
            else (key, key) :: e_set e n
       else e_set e n).


(** The map analogue: a `dynset` whose target is a MAP (`add @m {key : data}`)
    learns the entry [key -> data] in the named value-map [e_map], so a later
    `@m`-keyed lookup (map value / verdict map) sees it.  add/update prepend the
    entry (so [map_lookup_data] finds the freshest first), delete drops entries
    with that key. *)
Definition env_map_upd (e : env) (op : dynset_op) (name : String.string) (key dat : data) : env :=
  with_e_map e
    (fun n =>
       if String.eqb n name
       then if dynsetop_eqb op op_delete
            then filter (fun kv => negb (data_eqb (fst kv) key)) (e_map e n)
            else (key, dat) :: e_map e n
       else e_map e n).


(** The target ADDRESS operand of a NAT statement — the value the kernel loads
    into [NFTNL_EXPR_NAT_REG_ADDR_MIN] (register 1) and applies as the new
    source/destination address.  This mirrors exactly the register-1 operand the
    compiler emits ([compile_terminal]) and the loadability discipline
    ([terminal_loadable]): an explicit value source ([nat_src]), else a named-map
    lookup ([nat_map]), else a (transformed) packet field ([nat_field]), else the
    immediate destined for register 1 ([nat_addr_imm]). *)
Definition nat_addr (ns : nat_spec) (e : env) (p : packet) : data :=
  match nat_src ns with
  | Some vs => eval_vsrc vs e p
  | None =>
  match nat_map ns with
  | Some (fields, ts, name) =>
      map_lookup_data (nat_map_key fields ts e p) (e_map e name)
  | None =>
  match nat_field ns with
  | Some (f, ts) => apply_transforms ts (field_value f e p)
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
    ([nat_extra]) is a separate obligation.  An unrecognised kind
    leaves the packet unchanged. *)
Definition nat_af_norm (f : nat_af) : nat_af :=
  if nataf_eqb f nat_fam_ip6 then nat_fam_ip6
  else if nataf_eqb f nat_fam_inet then nat_fam_inet
  else nat_fam_ip4.
Definition nat_addrfamily (ns : nat_spec) : nat_af := nat_af_norm (nat_family ns).

(** The PACKET's L3 protocol family — exactly the bit [nft_pf(pkt)] encodes — read
    from the [meta nfproto] byte: NFPROTO_IPV6 = 10 -> "ip6", everything else (incl.
    NFPROTO_IPV4 = 2) -> "ip".  This is what the kernel's [nft_masq_inet_eval]
    `switch (nft_pf(pkt))` dispatches on. *)
Definition pkt_l3_family (p : packet) : nat_af :=
  if N.eqb (data_to_N (read_meta p MKnfproto)) 10 then nat_fam_ip6 else nat_fam_ip4.

(** The L3 NAT address family to USE for [p]: for a STATIC family ("ip"/"ip6", e.g.
    an `ip`/`ip6` table or an explicit-literal snat/dnat) the rule's own family; for
    the RUNTIME-DISPATCHED [nat_fam_inet] (an inet-table masquerade/redirect/snat-by-
    iface, which sees both protocols) the PACKET's L3 family ([pkt_l3_family]).  This
    is the precise model of the kernel's runtime `switch (nft_pf(pkt))`: an IPv6
    packet through an inet-table masquerade gets the 16-byte IPv6 geometry + IPv6
    interface address, an IPv4 packet the 4-byte IPv4 geometry — instead of a single
    statically-pinned family that corrupts the other protocol. *)
Definition nat_af_pkt (f : nat_af) (p : packet) : nat_af :=
  if nataf_eqb (nat_af_norm f) nat_fam_inet then pkt_l3_family p
  else nat_af_norm f.
Definition nat_addrfamily_pkt (ns : nat_spec) (p : packet) : nat_af :=
  nat_af_pkt (nat_family ns) p.

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
Definition loopback_addr (family : nat_af) : data :=
  if nataf_eqb family nat_fam_ip6 then loopback_ip6 else loopback_ip4.

(** The destination a `redirect` rewrites to, which is HOOK-DEPENDENT exactly as
    the kernel core [nf_nat_redirect_ipv4]/[nf_nat_redirect_ipv6] (branch on
    [hooknum]): at [Houtput] (NF_INET_LOCAL_OUT) local packets are forced to the
    loopback address (127.0.0.1 / ::1); otherwise (PRE_ROUTING) the new
    destination is the inbound interface's primary address.  [nft_redir_validate]
    permits only these two hooks. *)
Definition redir_daddr (h : hook_id) (fam : nat_af) (e : env) (p : packet) : data :=
  match h with
  | Houtput => loopback_addr fam
  | _ => e_ifaddr e (field_value FMetaIifname e p)
  end.

(** The SOURCE address a `masquerade` rewrites to: the exit interface's primary
    address, chosen by family exactly as the kernel dispatches masquerade BY FAMILY
    (nft_masq.c:113-121 branches NFPROTO_IPV4 -> nf_nat_masquerade_ipv4 vs
    NFPROTO_IPV6 -> nf_nat_masquerade_ipv6).  An IPv4 masquerade writes the 4-byte
    [e_ifaddr]; an IPv6 masquerade writes the 16-byte [e_ifaddr6] (the kernel
    computes it via ipv6_dev_get_saddr — a DIFFERENT, 128-bit value, not the IPv4
    address).  Keyed by the exit-interface name ([FMetaOifname]). *)
Definition masq_saddr (fam : nat_af) (e : env) (p : packet) : data :=
  if nataf_eqb fam nat_fam_ip6
  then e_ifaddr6 e (field_value FMetaOifname e p)
  else e_ifaddr  e (field_value FMetaOifname e p).

(** The L4 port the kernel writes is [min_proto.all] of the NAT range, loaded as a
    big-endian 16-bit value from the proto-min register ([nft_nat_setup_proto],
    nft_nat.c:57-60).  In the model the operand is [nat_port_num]; encode it as the
    2-byte big-endian port the transport header carries. *)
Definition nat_port_bytes (pmin : nat) : data := N_to_data 2 (N.of_nat pmin).

(** Apply the L4 PORT half of a NAT effect, mirroring the kernel
    [nft_nat_setup_proto]: the port rewrite happens ONLY when the proto-min
    register is set (`if (priv->sreg_proto_min)`, nft_nat.c:120) — in the model,
    when [nat_port_num ns = Some pmin].  A SOURCE NAT (snat/masquerade) rewrites the
    L4 SOURCE port ([set_sport]); a DESTINATION NAT (dnat/redirect) the L4
    DESTINATION port ([set_dport]) — exactly the [NF_NAT_MANIP_{SRC,DST}] split of
    [tcp_manip_pkt] (nf_nat_proto.c).  Address-only NAT ([nat_port_num] = None) leaves
    the port byte-for-byte unchanged. *)
(** REGISTER-FREE: the port is the VALUE [lo] (a 2-byte port operand), never
    [nat_port_bytes] of a register index — the two must not be conflated (a
    register index is compile-time bookkeeping, [Compile.nat_pmin_reg]).
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
    a packet field ([nat_field]), or a register-1 immediate ([nat_addr_imm]). *)
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
    ([nat_port_num] = Some), the L4 port rewrite ([apply_nat_port], the independent
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
Definition nat_kind_src (k : nat_op) : bool :=
  natop_eqb k nat_masq_kind || natop_eqb k nat_snat_kind.
Definition nat_is_src (ns : nat_spec) : bool := nat_kind_src (nat_kind ns).

(** The L3 ADDRESS the operand evaluates to, i.e. the value the kernel loads into
    [NAT_REG_ADDR_MIN] on the unconfirmed packet to build the new tuple — or [None]
    when the spec carries no address operand (a port-only snat/dnat, the kernel's
    `if (priv->sreg_addr_min)` guard being false, nft_nat.c:114).  masquerade derives
    its source from the exit interface, redirect from the inbound interface/loopback,
    so both always carry an (implicit) address.  This is the ONLY part of the NAT
    effect that re-reads the current packet, so it is exactly what must be FROZEN at
    the flow's first packet. *)
(** The core form, shared VERBATIM by the DSL and the VM: the kind [k] and raw
    family [fam0] come from the rule spec / the [INat] instruction; the
    snat/dnat address OPERAND [opnd] is the only side-specific input — the DSL
    evaluates the spec's operand ([nat_addr], when [nat_has_addr]), the VM
    reads the [INat] addr-min register.  masquerade/redirect derive their
    address from the interface state, identically on both sides. *)
Definition nat_new_addr (h : hook_id) (k : nat_op) (fampkt : nat_af)
                        (opnd : option data) (e : env) (p : packet) : option data :=
  if natop_eqb k nat_masq_kind
  then Some (masq_saddr fampkt e p)
  else if natop_eqb k nat_redir_kind
  then Some (redir_daddr h fampkt e p)
  else if natop_eqb k nat_snat_kind || natop_eqb k nat_dnat_kind
  then opnd
  else None.

(** The DSL's L3 ADDRESS operand: the evaluated spec operand when one is
    present ([nat_has_addr], the kernel's `if (priv->sreg_addr_min)` guard) —
    except for masq/redir ([nat_portonly]), whose operand is their PORT
    ([nat_port_val]) and whose address always comes from the interface state.
    This is exactly the addr-min REGISTER discipline ([Compile.nat_amin_reg]),
    so the VM's [option_map rf amin] matches it shape for shape. *)
Definition nat_opnd (ns : nat_spec) (e : env) (p : packet) : option data :=
  if nat_portonly ns then None
  else if nat_has_addr ns then Some (nat_addr ns e p) else None.

Definition nat_operand_addr (h : hook_id) (ns : nat_spec) (e : env) (p : packet)
  : option data :=
  nat_new_addr h (nat_kind ns) (nat_addrfamily_pkt ns p) (nat_opnd ns e p) e p.

(** Apply a (possibly absent) L4 PORT translation [port_opt] to packet [p],
    rewriting the SOURCE port for a source NAT or the DESTINATION port for a
    destination NAT — the value-level analogue of [apply_nat_port] that takes the
    stored port directly instead of re-reading [nat_port_num]. *)
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
Definition apply_nat_tuple_c (is_src : bool) (fam : nat_af) (p : packet)
                             (m : option data * option data * option nat * option data) : packet :=
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

Definition apply_nat_tuple (ns : nat_spec) (p : packet)
                           (m : option data * option data * option nat * option data) : packet :=
  apply_nat_tuple_c (nat_is_src ns) (nat_addrfamily_pkt ns p) p m.

(** STORE the flow-keyed NAT mapping [m] at [p]'s flow into the shared env
    ([env_nat_upd]) — exactly where the kernel writes it into the conntrack
    entry.  A pure env update: the packet is untouched (the address rewrite is
    the separate [apply_nat_tuple]). *)
Definition store_nat_mapping (e : env) (p : packet)
    (m : option data * option data * option nat * option data) : env :=
  env_nat_upd e (pkt_flow p) m.

(** The data-plane NAT effect of a terminal rule at hook [h], now FLOW-STATEFUL,
    mirroring [nf_nat_setup_info]/[nft_nat_eval]:

    - On the FIRST (unconfirmed) packet of a flow ([e_nat (pkt_flow p) = None]) the
      kernel computes the new tuple from the rule operand (get_unique_tuple,
      nf_nat_core.c:796), STORES it in the conntrack entry (nf_conntrack_alter_reply,
      :803), and applies the rewrite.  The model mirrors this: it evaluates
      [nat_operand_addr]/[nat_port_num] from the CURRENT packet, applies the tuple
      ([apply_nat_tuple]) AND stores it into the shared, flow-keyed [e_nat]
      ([store_nat_mapping]).

    - On every LATER (confirmed) packet of the SAME flow ([e_nat (pkt_flow p) =
      Some m]) the kernel returns NF_ACCEPT from nf_nat_setup_info WITHOUT
      recomputing (nf_nat_core.c:778-780), and the rewrite comes from the STORED
      tuple [m] (nf_nat_manip_pkt).  The model mirrors this: it applies [m] verbatim
      ([apply_nat_tuple]) and does NOT re-read the operand — so two same-flow packets
      with different saddrs both get the translation chosen on packet 1.

    This is the exact analogue of the flow-keyed conntrack-mark state [e_ct], for
    the NAT tuple.  The verdict side is untouched (NAT is terminal-Accept), so
    [compile_chain_correct] is unaffected. *)

(** The ORIGINAL (pre-NAT) address of the slot a NAT of kind [ns] rewrites — read
    from the CURRENT packet before any rewrite: the SOURCE slot for a source NAT
    ([nat_is_src]: snat/masquerade), the DESTINATION slot for a destination NAT
    (dnat/redirect).  This is the address the kernel records as the OTHER tuple of
    the conntrack entry (nf_conntrack_alter_reply), so a reply-direction packet can
    be un-NAT'd back to it (the reply's opposite slot is restored to this value). *)
Definition nat_orig_addr_c (is_src : bool) (fam : nat_af) (p : packet) : data :=
  let '(off, len) := if is_src then saddr_slot fam else daddr_slot fam in
  slice (pkt_nh p) off len.
Definition nat_orig_addr (ns : nat_spec) (p : packet) : data :=
  nat_orig_addr_c (nat_is_src ns) (nat_addrfamily_pkt ns p) p.

(** The ORIGINAL (pre-NAT) L4 PORT of the slot a NAT of kind [ns] rewrites — read
    from the CURRENT packet's transport header before any rewrite: the SOURCE port
    (transport bytes 0..1) for a source NAT ([nat_is_src]: snat/masquerade), the
    DESTINATION port (bytes 2..3) for a destination NAT (dnat/redirect).  Stored
    ONLY when a port operand is present ([nat_port_num ns = Some _], the kernel's
    `if (priv->sreg_proto_min)` guard, nft_nat.c:120) — otherwise [None], so the
    reply leaves the port byte-for-byte unchanged.  This is the port half of the
    reply tuple the kernel records (nf_conntrack_alter_reply), un-rewritten onto
    the OPPOSITE slot of a reply-direction packet (mirroring nf_nat_manip_pkt's
    inverted maniptype). *)
(** The port operand as a NUMBER, for the flow tuple (register-free; the source
    carries the port as a 2-byte VALUE in [nat_extra], decoded here). *)
(** masq/redir never translate an ADDRESS: any primary operand they carry
    (value source / map / field / immediate) is their PORT — nft loads it into
    the proto-min register ([Compile.nat_portonly] mirrors this at register
    allocation).  A dnat/snat port is the [NXimm] port-min immediate.  A port
    living in a concat-MAP value slot ([NXmap_port]/[NXmap_full]) is NOT
    statically modelled (the model VM delivers map values whole in the lookup
    dreg and leaves the value-slot registers 9+ unwritten): both semantics
    skip it identically — an unmodeled-feature gap (DEVELOPMENT.md), not a
    divergence. *)
Definition nat_port_val (ns : nat_spec) (e : env) (p : packet) : option data :=
  match nat_extra ns with
  | NXimm _ (Some lo) _ => Some lo
  | NXmap_port | NXmap_full => None
  | _ => if nat_portonly ns && nat_has_addr ns
         then Some (nat_addr ns e p)   (* masq/redir `to :port`: the operand IS the port *)
         else None
  end.
Definition nat_port_num (ns : nat_spec) (e : env) (p : packet) : option nat :=
  match nat_port_val ns e p with
  | Some lo => Some (N.to_nat (data_to_N lo))
  | None => None
  end.
Definition nat_orig_port_c (is_src : bool) (port : option nat) (p : packet) : option data :=
  match port with
  | Some _ =>
      if is_src
      then Some (slice (pkt_th p) 0 2)   (* source NAT: original SOURCE port *)
      else Some (slice (pkt_th p) 2 2)   (* dest   NAT: original DEST   port *)
  | None => None
  end.
Definition nat_orig_port (ns : nat_spec) (e : env) (p : packet) : option data :=
  nat_orig_port_c (nat_is_src ns) (nat_port_num ns e p) p.
(** The core effect, shared VERBATIM by both sides (the DSL supplies the
    evaluated spec operands, the VM the [INat] register contents). *)
Definition apply_nat_c (h : hook_id) (k : nat_op) (fam0 : nat_af)
                       (opnd : option data) (port : option nat)
                       (e : env) (p : packet) : env * packet :=
  let fam := nat_af_pkt fam0 p in
  let is_src := nat_kind_src k in
  match e_nat e (pkt_flow p) with
  | Some m =>
      (* confirmed flow: reuse the stored tuple (direction-aware), do NOT re-read
         the operand *)
      (e, apply_nat_tuple_c is_src fam p m)
  | None =>
      (* No mapping established yet.  The kernel establishes the NAT tuple only on
         the connection's ORIGINAL-direction packet (nf_nat_setup_info runs on the
         unconfirmed, original-direction skb).  A reply-direction packet with no
         established mapping is NOT translated. *)
      if pkt_ctdir_orig p then
        (* first packet of the flow (original direction): capture the original
           address, compute the tuple, apply it FORWARD, and STORE it *)
        let m := (Some (nat_orig_addr_c is_src fam p), nat_new_addr h k fam opnd e p,
                  port, nat_orig_port_c is_src port p) in
        (store_nat_mapping e p m, apply_nat_tuple_c is_src fam p m)
      else
        (e, p)
  end.

Definition apply_nat (h : hook_id) (r : rule) (e : env) (p : packet) : env * packet :=
  match r_nat r with
  | Some ns =>
      match e_nat e (pkt_flow p) with
      | Some m =>
          (* confirmed flow: reuse the stored tuple (direction-aware), do NOT re-read
             the operand *)
          (e, apply_nat_tuple ns p m)
      | None =>
          if pkt_ctdir_orig p then
            (* first packet of the flow (original direction): capture the original
               address, compute the tuple, apply it FORWARD, and STORE it *)
            let m := (Some (nat_orig_addr ns p), nat_operand_addr h ns e p,
                      nat_port_num ns e p, nat_orig_port ns e p) in
            (store_nat_mapping e p m, apply_nat_tuple ns p m)
          else
            (e, p)
      end
  | None => (e, p)
  end.

(** [apply_nat] IS the shared core at the spec's operands — the equation the
    compiler bridge uses to meet the VM's register-fed [apply_nat_c]
    ([Correct.step_inat_terminal]). *)
Lemma apply_nat_eq_c : forall h r e p,
  apply_nat h r e p
  = match r_nat r with
    | Some ns => apply_nat_c h (nat_kind ns) (nat_family ns) (nat_opnd ns e p)
                             (nat_port_num ns e p) e p
    | None => (e, p)
    end.
Proof.
  intros h r e p. unfold apply_nat, apply_nat_c. cbv zeta.
  destruct (r_nat r) as [ns|]; [|reflexivity].
  destruct (e_nat e (pkt_flow p)) as [m|]; [reflexivity|].
  destruct (pkt_ctdir_orig p); reflexivity.
Qed.

(** The kernel's NAT CORE DROPS a packet when the interface it must take an
    address FROM has no usable address — a data-plane drop computed by
    [nat_drops_c] and consumed by BOTH sides of the single fold:
    [terminal_step] (DSL) and the [INat] instruction case (VM), so it is
    compiler-certified ([Correct.compile_nat_effect_correct]).  Two cases
    mirror the kernel exactly:

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
Definition nat_iface_addr_absent (h : hook_id) (k : nat_op) (fam0 : nat_af)
                                 (e : env) (p : packet) : bool :=
  if natop_eqb k nat_masq_kind
  then match masq_saddr (nat_af_pkt fam0 p) e p with [] => true | _ => false end
  else if natop_eqb k nat_redir_kind
  then match h with
       | Houtput => false   (* loopback: never empty, never drops *)
       | _ => match redir_daddr h (nat_af_pkt fam0 p) e p with [] => true | _ => false end
       end
  else false.

(** The core drop test, shared verbatim by both sides — it reads only the
    kind/family (both carried by the [INat] instruction), the shared flow
    state and the packet. *)
Definition nat_drops_c (h : hook_id) (k : nat_op) (fam0 : nat_af)
                       (e : env) (p : packet) : bool :=
  match e_nat e (pkt_flow p) with
  | Some _ => false            (* confirmed flow: reuse stored tuple, no recompute *)
  | None => pkt_ctdir_orig p && nat_iface_addr_absent h k fam0 e p
  end.

Definition nat_drops (h : hook_id) (r : rule) (e : env) (p : packet) : bool :=
  match r_nat r with
  | Some ns => nat_drops_c h (nat_kind ns) (nat_family ns) e p
  | None => false
  end.

(** The VM's port operand at an [INat]: the proto-min REGISTER content, as a
    port number — present exactly when the register is one of the per-rule
    scratch registers 1..8 this rule's own loads populate.  A proto register
    pointing at a concat-map value SLOT (register 9+, [Compile.reg_of_slot])
    carries no statically-modelled value — the model VM delivers map values
    whole in the lookup dreg — so, like the DSL ([nat_port_val]), the port
    half of a map value is skipped (unmodeled feature, not a divergence). *)
Definition vm_nat_port (rf : regfile) (pmin : option nat) : option nat :=
  match pmin with
  | Some r => if Nat.ltb r 9 then Some (N.to_nat (data_to_N (rf r))) else None
  | None => None
  end.

(* ------------------------------------------------------------------ *)
(** ** Evaluation at a netfilter hook.

    Everything from here on evaluates AT a given netfilter hook [h] — the
    kernel passes the hook number in the packet state ([nft_pktinfo]),
    and the data-plane NAT effect of a terminal rule is hook-dependent
    ([redir_daddr], [nat_drops_core]).  [h] threads through BOTH per-rule
    folds ([rule_step]/[run_rule_step]) and every evaluator built on them;
    definitions in this section that do not mention [h] stay hook-free. *)
Section AtHook.
Context (h : hook_id).

(** ** ONE left-to-right fold per rule — the kernel's expression walk.

    nf_tables_core.c [nft_do_chain] runs a rule's expressions ONCE, left to
    right, against the RUNNING state ([nft_rule_dp_for_each_expr]; the loop
    breaks as soon as [regs.verdict.code != NFT_CONTINUE]).  Every expression
    — a match, a statement operand, the verdict-map key, a limiter check —
    therefore sees the writes of the expressions BEFORE it in the SAME rule,
    whether packet-local ([set_meta]/[set_ct]) or environment writes (dynset
    [env_set_upd]/[env_map_upd]).  [run_rule_step] (bytecode) and [rule_step]
    (DSL, below) are that single fold: they return the rule's verdict AND the
    state it leaves, from one traversal.  A failing match / breaking load
    stops the walk KEEPING the writes made before it (they happened); a
    statement whose operand load BREAKs stops before its write; statements
    positioned after a terminal verdict never run.

    [run_rule] above remains as the WRITE-FREE projection of this fold: the
    per-entry-packet verdict evaluator that the pure strand
    ([eval_rules]/[run_program], the optimizer theorems) consumes.  On rules
    without mutating statements the two agree ([rule_step_mutfree] /
    [Correct.run_rule_step_no_writes]); on rules WITH intra-rule writes the
    fold is the authoritative (kernel-faithful) semantics. *)

Fixpoint run_rule_step (rf : regfile) (is : list instr) (e : env) (p : packet)
  : option verdict * (env * packet) :=
  match is with
  | [] => (None, (e, p))
  | IMetaLoad k dst :: rest => run_rule_step (set_reg rf dst (read_meta p k)) rest e p
  | ICtLoad k dst :: rest =>
      (* a conntrack load on a no-entry packet ([pkt_ct_present = false]) breaks the
         rule for every key except [CKstate] (NFT_BREAK): no later statement runs and
         the state so far is kept — kernel nft_ct.c:81-82 `if (ct == NULL) goto err`. *)
      if load_ok (LCt k) p
      then run_rule_step (set_reg rf dst (do_load (LCt k) e p)) rest e p
      else (None, (e, p))
  | IRtLoad k dst :: rest => run_rule_step (set_reg rf dst (read_rt e k)) rest e p
  | ISocketLoad k dst :: rest => run_rule_step (set_reg rf dst (read_socket p k)) rest e p
  | INumgen spec dst :: rest =>
      (* `numgen inc` reads the SHARED counter value THEN advances the counter
         — the kernel's read-and-atomically-increment per evaluation
         (nft_ng_inc_gen), at the instruction's own position: an [INumgen]
         after a breaking load never advances, and a second read in the SAME
         rule sees the first one's advance.  [set_numgen] is the identity for
         `numgen random` (no counter). *)
      run_rule_step (set_reg rf dst (do_load (LNumgen spec) e p)) rest (set_numgen e spec) p
  | IOsf dst :: rest => run_rule_step (set_reg rf dst (read_osf p)) rest e p
  | IExthdrLoad ep h o l pr dst :: rest =>
      (* a VALUE load of an absent exthdr/option breaks the rule (NFT_BREAK,
         nft_exthdr_*_eval err path); an EXISTENCE load never breaks. *)
      if load_ok (LExthdr ep h o l pr) p
      then run_rule_step (set_reg rf dst (pkt_eh p ep h o l pr)) rest e p
      else (None, (e, p))
  | IFibLoad sel res dst :: rest => run_rule_step (set_reg rf dst (lpm_fib (e_routes e) (pkt_fibkey p sel) res)) rest e p
  | ICtDirLoad key dir dst :: rest => run_rule_step (set_reg rf dst (pkt_ctdir p key dir)) rest e p
  | IXfrmLoad dir sp key dst :: rest => run_rule_step (set_reg rf dst (pkt_xfrm p dir sp key)) rest e p
  | ITunnelLoad key dst :: rest => run_rule_step (set_reg rf dst (pkt_tunnel p key)) rest e p
  | ISymhash m o dst :: rest => run_rule_step (set_reg rf dst (read_symhash p m o)) rest e p
  | IInnerLoad t h fl desc _ dst :: rest =>
      run_rule_step (set_reg rf dst (pkt_inner p t h fl desc)) rest e p
  | IPayloadLoad b o l dst :: rest =>
      (* a payload read off the end of the header (or a transport read on a
         fragment / no-L4 packet) is NFT_BREAK: the rule yields no verdict and
         the walk stops, keeping earlier writes. *)
      if read_payload_ok b o l p
      then run_rule_step (set_reg rf dst (read_payload b o l p)) rest e p
      else (None, (e, p))
  | ICmp op src v :: rest =>
      if eval_cmp op (rf src) v then run_rule_step rf rest e p else (None, (e, p))
  | IRange op src lo hi :: rest =>
      if eval_range op (rf src) lo hi then run_rule_step rf rest e p else (None, (e, p))
  | IBitwise dst src mask xor :: rest => run_rule_step (set_reg rf dst (data_bitops (rf src) mask xor)) rest e p
  | IBitwiseOr dst src1 src2 :: rest => run_rule_step (set_reg rf dst (data_or (rf src1) (rf src2))) rest e p
  | IBitShift dst src shl amt :: rest => run_rule_step (set_reg rf dst (data_shift shl amt (rf src))) rest e p
  | IByteorder dst src h sz len :: rest => run_rule_step (set_reg rf dst (data_byteorder h sz len (rf src))) rest e p
  | IJhash dst src l s m o :: rest => run_rule_step (set_reg rf dst (data_jhash l s m o (rf src))) rest e p
  | ILookup srcs name neg :: rest =>
      (* set membership against the RUNNING env: an [IDynset] earlier in the
         SAME rule is visible here (the intra-rule dynset feedback loop). *)
      if xorb neg (concat_set_mem (map rf srcs) (e_set e name))
      then run_rule_step rf rest e p else (None, (e, p))
  | IVmap srcs name :: rest =>
      (* a verdict map keyed against the RUNNING state: a hit terminates with
         that verdict; a miss falls through to the rest. *)
      match assoc_verdict (List.concat (map rf srcs)) (e_vmap e name) with
      | Some v => (Some v, (e, p))
      | None   => run_rule_step rf rest e p
      end
  | IImmediateData dst v :: rest => run_rule_step (set_reg rf dst v) rest e p
  | IPayloadWrite _ _ _ _ _ _ _ :: rest => run_rule_step rf rest e p
  (* meta/ct set: the write is applied HERE, to the running state, so every
     later instruction of the SAME rule (a cmp load, a vmap key, a dynset key)
     reads it — nft_meta_set_eval / nft_ct_set_eval followed by any later
     expression of the rule. *)
  | IMetaSet k src :: rest => run_rule_step rf rest e (set_meta p k (rf src))
  | ICtSet k src :: rest => run_rule_step rf rest (set_ct e p k (rf src)) p
  | ILookupVal keys name dreg :: rest =>
      run_rule_step (set_reg rf dreg (map_lookup_data (List.concat (map rf keys))
                                                      (e_map e name))) rest e p
  | ILookupValBr keys name dreg :: rest =>
      (* a map lookup feeding a terminal operand: BREAK on a miss (the terminal
         does not fire), else load the value and continue. *)
      if map_has_key (List.concat (map rf keys)) (e_map e name)
      then run_rule_step (set_reg rf dreg (map_lookup_data (List.concat (map rf keys))
                                                           (e_map e name))) rest e p
      else (None, (e, p))
  | INat k fam amin _ pmin _ _ :: _ =>
      (* terminal NAT: the data-plane effect happens HERE, at the instruction —
         which by construction is only reached when no earlier expression broke
         the rule and no [IVmap] hit delivered a verdict (outcome PROVENANCE is
         the fold's structure).  The kernel core first refuses a masquerade /
         redirect whose interface has no usable address (NF_DROP,
         [nat_drops_c]); otherwise it establishes/reuses the flow's NAT tuple
         and rewrites the packet ([apply_nat_c]), then the rule accepts. *)
      if nat_drops_c h k fam e p then (Some Drop, (e, p))
      else (Some Accept,
            apply_nat_c h k fam (option_map rf amin) (vm_nat_port rf pmin) e p)
  | ITproxy _ _ _ :: _ => (Some Accept, (e, p))        (* terminal redirect *)
  | IFwd _ _ _ :: _ => (Some Accept, (e, p))           (* terminal forward *)
  | IQueueSreg _ _ _ :: _ => (Some Accept, (e, p))     (* terminal queue *)
  | ILimit spec :: rest =>
      (* ONE evaluation of the limiter, at its own position: the CHECK reads
         the pre-write bucket and the bucket CONSUMPTION ([set_limit], the
         kernel nft_limit_eval's tokens store on BOTH branches) is applied
         here, in-fold — so a limiter after a failing match/breaking load is
         never evaluated and never consumes (kernel NFT_BREAK order), while a
         failing LIMITER still stores its capped level. *)
      if xorb (Nat.eqb (Nat.land (ls_flags spec) 1) 1) (lim_under e p spec)
      then run_rule_step rf rest (set_limit e p spec) p
      else (None, (set_limit e p spec, p))
  | IQuota spec :: rest =>
      (* quota accumulates skb->len on EVERY evaluation (pass or fail). *)
      if xorb (Nat.eqb (Nat.land (q_flags spec) 1) 1) (quota_under e p spec)
      then run_rule_step rf rest (set_quota e p spec) p
      else (None, (set_quota e p spec, p))
  | IConnlimit spec :: rest =>
      (* connlimit counts the tuple on EVERY evaluation (idempotent add). *)
      if xorb (Nat.eqb (Nat.land (cl_flags spec) 1) 1) (connlimit_under e p spec)
      then run_rule_step rf rest (set_connlimit e p spec) p
      else (None, (set_connlimit e p spec, p))
  | ICounter _ _ :: rest => run_rule_step rf rest e p   (* verdict-neutral *)
  | INotrack :: rest      => run_rule_step rf rest e (set_untracked p)
  | ILog _ :: rest        => run_rule_step rf rest e p
  | IObjref _ _ :: rest   => run_rule_step rf rest e p
  | ISynproxy _ _ :: rest =>
      (* SYN-proxy: a non-TCP packet BREAKs the rule (NFT_BREAK); a TCP packet
         with SYN or ACK set STOPS traversal (NF_STOLEN/NF_DROP, modelled as
         terminal Drop); any other TCP packet falls through. *)
      if synproxy_loadable p
      then (if synproxy_stops p then (Some Drop, (e, p)) else run_rule_step rf rest e p)
      else (None, (e, p))
  | ILast _ :: rest       => run_rule_step rf rest e p
  | IDynset op name keyregs None _ :: rest =>
      (* pure-set dynset: insert/remove the concatenated key in the named set —
         visible to a LATER [ILookup] of the SAME rule and to later rules. *)
      run_rule_step rf rest (env_set_upd e op name (List.concat (map rf keyregs))) p
  | IDynset op name keyregs (Some dreg) true :: rest =>
      (* map dynset whose data is a packet field: learn key -> data in the map. *)
      run_rule_step rf rest (env_map_upd e op name (List.concat (map rf keyregs)) (rf dreg)) p
  | IDynset _ _ _ (Some _) false :: rest => run_rule_step rf rest e p  (* immediate-data dynset: env-neutral *)
  | IExthdrReset _ _ :: rest => run_rule_step rf rest e p
  | IDup _ _ :: rest => run_rule_step rf rest e p
  | IObjrefMap _ _ :: rest => run_rule_step rf rest e p
  | ICtSetDir _ _ _ :: rest => run_rule_step rf rest e p
  | IExthdrWrite _ _ _ _ _ :: rest => run_rule_step rf rest e p
  | IReject t c :: _ => (Some (Reject t c), (e, p))
  | IQueue lo hi b f :: _ => (Some (Queue lo hi b f), (e, p))
  | IImmediate v :: _ => (Some v, (e, p))
  end.

(** A "mutating" statement: a meta/ct set (mutates a packet field) OR a dynset
    (mutates the named-set state) OR notrack (sets the flow's ct state).  These
    are the statements whose writes the fold threads; every other statement is
    meta/ct- and env-neutral. *)
Definition is_mut_stmt (s : stmt) : bool :=
  match s with SMetaSet _ _ | SCtSet _ _ | SDynset _ _ _ _ | SNotrack => true | _ => false end.

(** ** The DSL single fold.

    [body_step] walks a rule body left-to-right against the running state,
    mirroring [run_rule_step] on the compiled body.  Its result distinguishes
    the three ways a body walk can end:

    - [BRbreak e p]: an expression BREAKs (a failing match, or a statement
      whose operand load breaks — NFT_BREAK): the rule yields no verdict, the
      walk stops BEFORE that statement's write, and the writes made before the
      break are kept (they happened);
    - [BRstop e p]: a SYN-proxy STOLE the packet (terminal Drop; nothing after
      it runs);
    - [BRdone e p]: the body completed; the rule's end — verdict map, then
      terminal, then post-outcome statements — is evaluated against the FINAL
      state [e]/[p], so a vmap key or a terminal operand sees the body's
      writes. *)
Inductive body_res : Type :=
| BRbreak : env -> packet -> body_res
| BRstop  : env -> packet -> body_res
| BRdone  : env -> packet -> body_res.

Definition body_res_state (b : body_res) : env * packet :=
  match b with BRbreak e p | BRstop e p | BRdone e p => (e, p) end.

Fixpoint body_step (body : list body_item) (e : env) (p : packet) : body_res :=
  match body with
  | [] => BRdone e p
  (* [eval_matchcond] is loadability-guarded: a match whose load breaks is
     [false], and either way a failing match ends the walk keeping the state.
     EVALUATING the match applies its env consumption ([match_consume]: a
     `limit`/`quota`/`connlimit` writes its shared bucket on pass AND on fail,
     every other match consumes nothing) — at the match's own position, so a
     limiter the walk never reaches is never consumed (kernel NFT_BREAK
     order), and the check itself reads the pre-write bucket. *)
  | BMatch m :: rest =>
      if eval_matchcond m e p then body_step rest (match_consume m e p) p
      else BRbreak (match_consume m e p) p
  | BStmt (SMetaSet k vs) :: rest =>
      if vsrc_loadable vs p
      then body_step rest e (set_meta p k (eval_vsrc vs e p)) else BRbreak e p
  | BStmt (SCtSet k vs) :: rest =>
      if vsrc_loadable vs p
      then body_step rest (set_ct e p k (eval_vsrc vs e p)) p else BRbreak e p
  | BStmt (SDynset op name keyfs nil) :: rest =>
      (* pure-set dynset: insert/remove the concatenated key in the named set;
         a LATER lookup in the SAME rule (and any later rule) observes it. *)
      if fields_loadable keyfs p
      then body_step rest (env_set_upd e op name
                             (List.concat (map (fun f => field_value f e p) keyfs))) p
      else BRbreak e p
  | BStmt (SDynset op name keyfs (d :: ds)) :: rest =>
      (* map dynset with a field-valued data: learn key -> (first data field) in
         the named map.  (Only the first data field is recorded; the corpus never
         emits a multi-field map data, and BOTH sides record exactly this.) *)
      if fields_loadable (keyfs ++ d :: ds) p
      then body_step rest (env_map_upd e op name
                             (List.concat (map (fun f => field_value f e p) keyfs))
                             (field_value d e p)) p
      else BRbreak e p
  (* SYN-proxy: BREAK on a non-TCP packet, STOP (terminal Drop) on SYN/ACK,
     fall through otherwise (cf. [run_rule_step]'s ISynproxy). *)
  | BStmt (SSynproxy _ _) :: rest =>
      if synproxy_loadable p
      then (if synproxy_stops p then BRstop e p else body_step rest e p)
      else BRbreak e p
  (* `notrack` forces IP_CT_UNTRACKED for the rest of THIS traversal (kernel
     nft_notrack_eval guard modelled by [set_untracked]). *)
  | BStmt SNotrack :: rest => body_step rest e (set_untracked p)
  (* every OTHER statement is meta/ct- and env-neutral, but it still LOADS its
     operand fields; an unloadable load BREAKs the rule. *)
  | BStmt s :: rest => if stmt_loadable s p then body_step rest e p else BRbreak e p
  end.

(** The post-outcome ([r_after]) statements, run left-to-right on a [Continue]
    fall-through — with the SAME threading discipline as body statements: a
    mutating statement's write is applied to the running state (and kept by the
    rule's step), an operand whose load BREAKs abandons the rule, a SYN-proxy
    stop is terminal Drop.  This is what retires the old "no mutating statement
    in [r_after]" domain hypothesis: the fold simply runs them. *)
Fixpoint after_step (ss : list stmt) (e : env) (p : packet)
  : option verdict * (env * packet) :=
  match ss with
  | [] => (None, (e, p))
  | SMetaSet k vs :: rest =>
      if vsrc_loadable vs p
      then after_step rest e (set_meta p k (eval_vsrc vs e p)) else (None, (e, p))
  | SCtSet k vs :: rest =>
      if vsrc_loadable vs p
      then after_step rest (set_ct e p k (eval_vsrc vs e p)) p else (None, (e, p))
  | SDynset op name keyfs nil :: rest =>
      if fields_loadable keyfs p
      then after_step rest (env_set_upd e op name
                              (List.concat (map (fun f => field_value f e p) keyfs))) p
      else (None, (e, p))
  | SDynset op name keyfs (d :: ds) :: rest =>
      if fields_loadable (keyfs ++ d :: ds) p
      then after_step rest (env_map_upd e op name
                              (List.concat (map (fun f => field_value f e p) keyfs))
                              (field_value d e p)) p
      else (None, (e, p))
  | SSynproxy _ _ :: rest =>
      if synproxy_loadable p
      then (if synproxy_stops p then (Some Drop, (e, p)) else after_step rest e p)
      else (None, (e, p))
  | SNotrack :: rest => after_step rest e (set_untracked p)
  | s :: rest => if stmt_loadable s p then after_step rest e p else (None, (e, p))
  end.

(** Whether the rule carries a side-effect terminal (nat/tproxy/fwd/queue). *)
Definition has_effect_terminal (r : rule) : bool :=
  match r_nat r, r_tproxy r, r_fwd r, r_queue r with
  | None, None, None, None => false
  | _, _, _, _ => true
  end.

(** The terminal of the rule, evaluated against the state the walk reached: a
    side-effect terminal loads its operand — a breaking load (or a nat
    map-operand miss, [terminal_loadable]) abandons the rule — and ACCEPTs (the
    translation/redirect/hand-off is a side effect); a static non-[Continue]
    verdict is returned; a [Continue] falls through to the post-outcome
    statements. *)
Definition terminal_step (r : rule) (e : env) (p : packet)
  : option verdict * (env * packet) :=
  if has_effect_terminal r
  then if terminal_loadable r e p
       then (* The NAT data-plane effect happens HERE — at the terminal the walk
               actually reached, so a vmap HIT (handled in [end_step] before
               this) never runs it: outcome PROVENANCE is the fold's structure,
               exactly the kernel's per-expression verdict break.  The kernel
               core first refuses a masquerade/redirect whose interface has no
               usable address (NF_DROP, [nat_drops]); otherwise it establishes/
               reuses the flow's NAT tuple, rewrites the packet ([apply_nat])
               and the rule accepts.  tproxy/fwd/queue have [r_nat] = None:
               their hand-off is a modelled-as-Accept side effect, state
               untouched. *)
            if nat_drops h r e p then (Some Drop, (e, p))
            else (Some Accept, apply_nat h r e p)
       else (None, (e, p))
  else match r_verdict r with
       | Continue => after_step (r_after r) e p
       | v => (Some v, (e, p))
       end.

(** The rule's end — verdict map then terminal — evaluated against the state
    the body walk reached: the vmap KEY is loaded from the running state (a
    breaking key load abandons the rule), a hit gives its verdict (nothing
    after the [IVmap] runs), a miss falls through to the terminal. *)
Definition end_step (r : rule) (e : env) (p : packet)
  : option verdict * (env * packet) :=
  match r_vmap r with
  | Some vm =>
      if vmap_loadable (Some vm) p
      then let key := match vm_keyf vm with
                      | Some (f, ts) => apply_transforms ts (field_value f e p)
                      | None => List.concat (map (fun f => field_value f e p) (vm_fields vm))
                      end in
           match assoc_verdict key (e_vmap e (vm_name vm)) with
           | Some v => (Some v, (e, p))
           | None   => terminal_step r e p
           end
      else (None, (e, p))
  | None => terminal_step r e p
  end.

(** THE per-rule semantics: one fold.  [Correct.run_rule_step_compile_rule]
    proves the compiled bytecode's fold equal to this, UNCONDITIONALLY:
    [run_rule_step empty_rf (compile_rule r) e p = rule_step r e p]. *)
Definition rule_step (r : rule) (e : env) (p : packet)
  : option verdict * (env * packet) :=
  match body_step (r_body r) e p with
  | BRbreak e' p' => (None, (e', p'))
  | BRstop e' p'  => (Some Drop, (e', p'))
  | BRdone e' p'  => end_step r e' p'
  end.

(** The meta/ct/env effect of a rule BODY — the state projection of the body
    fold (kept as the named notion the optimizer's per-merge-shape certificates
    reason about). *)
Definition body_writes (body : list body_item) (e : env) (p : packet) : env * packet :=
  body_res_state (body_step body e p).
Arguments body_writes !body e p /.
Definition dsl_writes (r : rule) (e : env) (p : packet) : env * packet :=
  body_writes (r_body r) e p.

(** ** ONE step function per rule, per side: [rule_step] (DSL) and
    [run_rule_step empty_rf] (VM).

    In mutation mode a rule's whole contribution to a traversal is a single
    STEP: the verdict it produces paired with the state it leaves — its
    meta/ct/env writes AND the consumption of every `limit`/`quota`/
    `connlimit` (and, VM-only, `numgen inc` counter advance) it EVALUATED,
    each applied at its own position inside the break-aware fold.  Every
    mutation evaluator below consumes ONLY the step functions, so the
    verdict/effect composition is written here and nowhere else.  The
    compiler-correctness bridge is one equation, on numgen-free rules (every
    frontend-emitted rule; [Lower_Proofs.lower_ruleset_numgen_free]):
    [run_rule_step empty_rf (compile_rule r) = rule_step r]
    ([Correct.run_rule_step_compile_rule]).

    (The historical [dsl_rule_step]/[vm_rule_step] boundary wrappers — the
    fold plus an unconditional whole-body limiter/numgen sweep, the historical
    over-consumption divergence — are RETIRED: with the consumption
    in-fold they equal the folds; see THEOREMS.md § strata retirements.) *)

(** The state half of a rule's step (writes + limiter consumption + the NAT
    data plane) — the named notion the optimizer's effect certificates
    consume. *)
Definition dsl_step (r : rule) (e : env) (p : packet) : env * packet :=
  snd (rule_step r e p).

(** ** Projections and mut-free coincidence with the pure strand. *)

(** [after_step] over a mut-free statement list is exactly the historical
    [stmts_after_outcome] verdict, with the state unchanged. *)
Lemma after_step_mutfree : forall ss e p,
  forallb (fun s => negb (is_mut_stmt s)) ss = true ->
  after_step ss e p = (stmts_after_outcome ss p, (e, p)).
Proof.
  induction ss as [| s ss IH]; intros e p Hmf; [reflexivity|].
  cbn [forallb] in Hmf. apply Bool.andb_true_iff in Hmf. destruct Hmf as [Hs Hss].
  destruct s; cbn [is_mut_stmt negb] in Hs; try discriminate Hs;
    cbn [after_step stmts_after_outcome];
    try (destruct (stmt_loadable _ p); [apply IH; exact Hss | reflexivity]).
  (* SSynproxy *)
  destruct (synproxy_loadable p); [| reflexivity].
  destruct (synproxy_stops p); [reflexivity | apply IH; exact Hss].
Qed.

(** A rule body / whole rule that WRITES NO STATE: no mutating statement
    ([is_mut_stmt]: meta/ct set, dynset, notrack) anywhere AND no
    `limit`/`quota`/`connlimit` match ([match_consumefree]: evaluating one
    writes its shared bucket) in the body.  This is exactly the domain on
    which the fold is state-preserving and coincides with the historical pure
    verdict predicates ([rule_step_mutfree] below). *)
Definition body_item_mutfree (it : body_item) : bool :=
  match it with BStmt s => negb (is_mut_stmt s) | BMatch m => match_consumefree m end.
(** A NAT terminal WRITES state (the packet rewrite + the flow-keyed [e_nat]
    store), so a rule that carries one is NOT mut-free — the pure strand's
    loadability-guarded Accept is only the projection of the fold on rules
    without it.  tproxy/fwd/queue terminals remain state-free. *)
Definition rule_natfree (r : rule) : bool :=
  match r_nat r with None => true | Some _ => false end.
Definition rule_mutfree (r : rule) : bool :=
  forallb body_item_mutfree (r_body r)
  && forallb (fun s => negb (is_mut_stmt s)) (r_after r)
  && rule_natfree r.

(** On a mut-free rule the fold's terminal/end agree with the historical
    loadability-guarded [terminal_outcome]/[outcome_core] at the SAME state. *)
Lemma terminal_step_mutfree : forall r e p,
  rule_natfree r = true ->
  forallb (fun s => negb (is_mut_stmt s)) (r_after r) = true ->
  terminal_step r e p
  = ((if tail_loadable r e p then terminal_outcome r p else None), (e, p)).
Proof.
  intros r e p Hnat Hmf.
  unfold rule_natfree in Hnat.
  unfold terminal_step, has_effect_terminal, tail_loadable, terminal_loadable,
         terminal_outcome, nat_drops, apply_nat.
  destruct (r_nat r) as [n|]; [discriminate Hnat|].
  destruct (r_tproxy r) as [t|]; [reflexivity|].
  destruct (r_fwd r) as [w|];
    [destruct (vsrc_loadable (fwd_dev w) p); reflexivity|].
  destruct (r_queue r) as [q|];
    [destruct (vsrc_loadable (q_num q) p); reflexivity|].
  (* static verdict; only [Continue] runs r_after *)
  destruct (r_verdict r); try reflexivity.
  rewrite (after_step_mutfree (r_after r) e p Hmf).
  destruct (stmts_after_outcome (r_after r) p) eqn:Hsa; [reflexivity|].
  destruct (forallb (fun s => stmt_loadable s p) (r_after r)); reflexivity.
Qed.

Lemma end_step_mutfree : forall r e p,
  rule_natfree r = true ->
  forallb (fun s => negb (is_mut_stmt s)) (r_after r) = true ->
  end_step r e p
  = ((if end_loadable r e p then outcome_core r e p else None), (e, p)).
Proof.
  intros r e p Hnat Hmf. unfold end_step, end_loadable, outcome_core.
  destruct (r_vmap r) as [vm|]; [| apply terminal_step_mutfree; assumption].
  destruct (vmap_loadable (Some vm) p) eqn:Hvl; [| reflexivity].
  cbv zeta.
  destruct (vm_keyf vm) as [[f ts]|]; cbv iota.
  - destruct (assoc_verdict (apply_transforms ts (field_value f e p))
                            (e_vmap e (vm_name vm))); [reflexivity|].
    rewrite (terminal_step_mutfree r e p Hnat Hmf). reflexivity.
  - destruct (assoc_verdict
                (List.concat (map (fun f => field_value f e p) (vm_fields vm)))
                (e_vmap e (vm_name vm))); [reflexivity|].
    rewrite (terminal_step_mutfree r e p Hnat Hmf). reflexivity.
Qed.

(** On a mut-free body the fold's walk agrees with the historical three
    predicates ([body_loadable_walk]/[rule_applies_walk]/[body_synproxy_stops])
    and never changes the state. *)
Lemma body_step_mutfree : forall body e p,
  forallb body_item_mutfree body = true ->
  body_step body e p
  = if body_loadable_walk body p && rule_applies_walk body e p
    then (if body_synproxy_stops body p then BRstop e p else BRdone e p)
    else BRbreak e p.
Proof.
  induction body as [| it body IH]; intros e p Hmf; [reflexivity|].
  cbn [forallb] in Hmf. apply Bool.andb_true_iff in Hmf. destruct Hmf as [Hit Hmf].
  assert (Hstops : forall it0 b, body_synproxy_stops (it0 :: b) p =
            (match it0 with BStmt (SSynproxy _ _) => synproxy_stops p | _ => false end)
            || body_synproxy_stops b p) by reflexivity.
  destruct it as [m | s].
  - cbn [body_item_mutfree] in Hit.
    cbn [body_step body_loadable_walk rule_applies_walk body_item_loadable].
    rewrite Hstops. cbn [orb].
    rewrite (match_consume_free_id m e p Hit).
    unfold eval_matchcond.
    destruct (match_loadable m p).
    + destruct (eval_matchcond_body m e p).
      * exact (IH e p Hmf).
      * destruct (body_loadable_walk body p); reflexivity.
    + reflexivity.
  - destruct s; cbn [body_item_mutfree is_mut_stmt negb] in Hit; try discriminate Hit;
      cbn [body_step body_loadable_walk rule_applies_walk body_item_loadable];
      rewrite Hstops; cbn [orb];
      try (destruct (stmt_loadable _ p); [exact (IH e p Hmf) | reflexivity]).
    (* SSynproxy *)
    destruct (synproxy_loadable p); [| reflexivity].
    destruct (synproxy_stops p).
    + destruct (rule_applies_walk body e p); reflexivity.
    + exact (IH e p Hmf).
Qed.

(** COINCIDENCE with the pure strand: on a mut-free rule the fold IS the
    historical loadability-guarded verdict — [rule_applies]/[outcome]/
    [rule_loadable] are the write-free projection of the single fold, which is
    why the pure evaluators ([eval_rules]/[run_program], the optimizer
    theorems) remain stated over them. *)
Theorem rule_step_mutfree : forall r e p,
  rule_mutfree r = true ->
  rule_step r e p
  = ((if rule_loadable r e p && rule_applies r e p then outcome r e p else None),
     (e, p)).
Proof.
  intros r e p Hmf. unfold rule_mutfree in Hmf.
  apply Bool.andb_true_iff in Hmf. destruct Hmf as [Hmf Hnat].
  apply Bool.andb_true_iff in Hmf. destruct Hmf as [Hbody Hafter].
  assert (Hnt : body_has_notrack (r_body r) = false).
  { unfold body_has_notrack. apply Bool.not_true_is_false. intro Hex.
    apply existsb_exists in Hex. destruct Hex as [it [Hin Hit]].
    destruct it as [m | s]; [discriminate Hit|]. destruct s; try discriminate Hit.
    rewrite forallb_forall in Hbody. specialize (Hbody _ Hin). discriminate Hbody. }
  assert (Hbt : body_thread (r_body r) p = p)
    by (unfold body_thread; rewrite Hnt; reflexivity).
  unfold rule_step, rule_applies, rule_loadable, outcome.
  rewrite Hbt.
  rewrite (body_step_mutfree (r_body r) e p Hbody).
  destruct (body_loadable_walk (r_body r) p) eqn:Hlw;
    [| destruct (rule_applies_walk (r_body r) e p); reflexivity].
  destruct (rule_applies_walk (r_body r) e p) eqn:Haw.
  2:{ destruct (body_synproxy_stops (r_body r) p);
      [reflexivity | destruct (end_loadable r e p); reflexivity]. }
  destruct (body_synproxy_stops (r_body r) p) eqn:Hst.
  - reflexivity.
  - cbn [andb]. rewrite (end_step_mutfree r e p Hnat Hafter).
    rewrite Bool.andb_true_r.
    destruct (end_loadable r e p); reflexivity.
Qed.

(** State-side corollaries: with a mut-free [r_after] the whole-rule state is
    the BODY's writes (the end never mutates), and a limit-free body makes the
    step the bare writes. *)
Lemma after_step_state_mutfree : forall ss e p,
  forallb (fun s => negb (is_mut_stmt s)) ss = true ->
  snd (after_step ss e p) = (e, p).
Proof.
  intros ss e p H. rewrite (after_step_mutfree ss e p H). reflexivity.
Qed.

Lemma rule_step_state_after_free : forall r e p,
  rule_natfree r = true ->
  forallb (fun s => negb (is_mut_stmt s)) (r_after r) = true ->
  snd (rule_step r e p) = dsl_writes r e p.
Proof.
  intros r e p Hnat Hmf. unfold rule_step, dsl_writes, body_writes.
  destruct (body_step (r_body r) e p) as [e' p' | e' p' | e' p'] eqn:Hb;
    cbn [body_res_state]; try reflexivity.
  rewrite (end_step_mutfree r e' p' Hnat Hmf).
  destruct (end_loadable r e' p'); reflexivity.
Qed.

(** With a mut-free [r_after] the step's state half is exactly the BODY's
    writes — which, post the in-fold limiter fix, already include any
    limiter consumption at its own position (successor of the retired
    [dsl_step_limit_free], whose extra limit-freedom hypothesis existed only
    to cancel the boundary sweep). *)
Lemma dsl_step_after_free : forall r e p,
  rule_natfree r = true ->
  forallb (fun s => negb (is_mut_stmt s)) (r_after r) = true ->
  dsl_step r e p = dsl_writes r e p.
Proof. intros r e p Hnat Hmf. exact (rule_step_state_after_free r e p Hnat Hmf). Qed.

(** Mutation-aware rule-list evaluation: every non-terminal rule threads its
    writes to the rest, so a later rule observes an earlier `set` (the write
    happens whether or not the rule's verdict matched — a non-applicable rule
    still ran the statements up to its failing match).

    ONE flat export, three views (M6): [eval_rules_mut_st] is the FULL-STATE
    flat (transfer-free) fold of [rule_step] — verdict AND the exact
    (env, packet) left, nothing dropped.  It is NON-RECURSIVE: a [fold_left]
    of the per-rule step with an absorbing "stopped" accumulator (the ONE
    recursive rule-list traversal on the DSL side is the unified
    [eval_rules_u]; on transfer-free rules this fold is its whole-triple
    projection, [eval_rules_u_mut_st_proj]).  [eval_rules_mut] /
    [eval_rules_mut_env] are BY DEFINITION its verdict / (verdict, env)
    projections — no re-proved bridge, the projection IS the definition.
    Proofs step all three with the [_nil]/[_cons] equations below, which
    restate the historical unfoldings verbatim.  The optimizer's effect-level
    pipeline theorem ([Optimize_MutEnv.optimize_table_uncond_mut_st_correct])
    is stated against [eval_chain_mut_st], so a pass cannot alter a
    packet-half write while preserving verdict and env. *)

Definition mut_st_step (r : rule) (acc : option verdict * (env * packet))
  : option verdict * (env * packet) :=
  match acc with
  | (Some v, s) => (Some v, s)
  | (None, (e, p)) =>
      match rule_step r e p with
      | (Some v, (e', p')) =>
          if terminal v then (Some v, (e', p')) else (None, (e', p'))
      | (None, (e', p')) => (None, (e', p'))
      end
  end.

Definition eval_rules_mut_st (rs : list rule) (e : env) (p : packet)
  : option verdict * (env * packet) :=
  fold_left (fun acc r => mut_st_step r acc) rs (None, (e, p)).

Arguments eval_rules_mut_st : simpl never.

(** A stopped accumulator absorbs the rest of the fold — the early exit of the
    historical recursion, as a lemma. *)
Lemma mut_st_fold_stopped : forall rs v s,
  fold_left (fun acc r => mut_st_step r acc) rs (Some v, s) = (Some v, s).
Proof. induction rs as [| r rs IH]; intros; [reflexivity | apply IH]. Qed.

Lemma eval_rules_mut_st_nil : forall e p,
  eval_rules_mut_st [] e p = (None, (e, p)).
Proof. reflexivity. Qed.

Lemma eval_rules_mut_st_cons : forall r rest e p,
  eval_rules_mut_st (r :: rest) e p
  = match rule_step r e p with
    | (Some v, (e', p')) => if terminal v then (Some v, (e', p'))
                            else eval_rules_mut_st rest e' p'
    | (None,   (e', p')) => eval_rules_mut_st rest e' p'
    end.
Proof.
  intros r rest e p. unfold eval_rules_mut_st. cbn [fold_left].
  unfold mut_st_step at 2.
  destruct (rule_step r e p) as [[v|] [e' p']].
  - destruct (terminal v); [apply mut_st_fold_stopped | reflexivity].
  - reflexivity.
Qed.

(** The verdict projection of the full-state fold. *)
Definition eval_rules_mut (rs : list rule) (e : env) (p : packet) : option verdict :=
  fst (eval_rules_mut_st rs e p).

Arguments eval_rules_mut : simpl never.

Lemma eval_rules_mut_nil : forall e p, eval_rules_mut [] e p = None.
Proof. reflexivity. Qed.

Lemma eval_rules_mut_cons : forall r rest e p,
  eval_rules_mut (r :: rest) e p
  = match rule_step r e p with
    | (Some v, (e', p')) => if terminal v then Some v else eval_rules_mut rest e' p'
    | (None,   (e', p')) => eval_rules_mut rest e' p'
    end.
Proof.
  intros r rest e p. unfold eval_rules_mut. rewrite eval_rules_mut_st_cons.
  destruct (rule_step r e p) as [[v|] [e' p']]; [destruct (terminal v)|]; reflexivity.
Qed.

(** VM full-state flat fold, mirroring [eval_rules_mut_st].  The state a rule
    LEAVES carries its [run_rule_step] meta/ct/env writes, its `numgen inc`
    counter advance, AND the consumption of every `limit`/`quota`/`connlimit`
    it evaluated (all applied in-fold at their positions); the next rule (and,
    through the env, the next packet) sees all three.  NON-RECURSIVE (M6):
    the ONE recursive program traversal on the VM side is [run_rules_u]. *)
Definition vm_mut_st_step (rp : rule_prog) (acc : option verdict * (env * packet))
  : option verdict * (env * packet) :=
  match acc with
  | (Some v, s) => (Some v, s)
  | (None, (e, p)) =>
      match run_rule_step empty_rf rp e p with
      | (Some v, (e', p')) =>
          if terminal v then (Some v, (e', p')) else (None, (e', p'))
      | (None, (e', p')) => (None, (e', p'))
      end
  end.

Definition run_program_mut_st (prog : program) (e : env) (p : packet)
  : option verdict * (env * packet) :=
  fold_left (fun acc rp => vm_mut_st_step rp acc) prog (None, (e, p)).

Arguments run_program_mut_st : simpl never.

Lemma vm_mut_st_fold_stopped : forall prog v s,
  fold_left (fun acc rp => vm_mut_st_step rp acc) prog (Some v, s) = (Some v, s).
Proof. induction prog as [| rp prog IH]; intros; [reflexivity | apply IH]. Qed.

Lemma run_program_mut_st_nil : forall e p,
  run_program_mut_st [] e p = (None, (e, p)).
Proof. reflexivity. Qed.

Lemma run_program_mut_st_cons : forall rp rest e p,
  run_program_mut_st (rp :: rest) e p
  = match run_rule_step empty_rf rp e p with
    | (Some v, (e', p')) => if terminal v then (Some v, (e', p'))
                            else run_program_mut_st rest e' p'
    | (None,   (e', p')) => run_program_mut_st rest e' p'
    end.
Proof.
  intros rp rest e p. unfold run_program_mut_st. cbn [fold_left].
  unfold vm_mut_st_step at 2.
  destruct (run_rule_step empty_rf rp e p) as [[v|] [e' p']].
  - destruct (terminal v); [apply vm_mut_st_fold_stopped | reflexivity].
  - reflexivity.
Qed.

Definition run_program_mut (prog : program) (e : env) (p : packet) : option verdict :=
  fst (run_program_mut_st prog e p).

Arguments run_program_mut : simpl never.

Lemma run_program_mut_nil : forall e p, run_program_mut [] e p = None.
Proof. reflexivity. Qed.

Lemma run_program_mut_cons : forall rp rest e p,
  run_program_mut (rp :: rest) e p
  = match run_rule_step empty_rf rp e p with
    | (Some v, (e', p')) => if terminal v then Some v else run_program_mut rest e' p'
    | (None,   (e', p')) => run_program_mut rest e' p'
    end.
Proof.
  intros rp rest e p. unfold run_program_mut. rewrite run_program_mut_st_cons.
  destruct (run_rule_step empty_rf rp e p) as [[v|] [e' p']];
    [destruct (terminal v)|]; reflexivity.
Qed.

Definition eval_chain_mut (c : chain) (e : env) (p : packet) : verdict :=
  match eval_rules_mut (c_rules c) e p with Some v => v | None => c_policy c end.
Definition run_chain_mut (prog : program) (policy : verdict) (e : env) (p : packet) : verdict :=
  match run_program_mut prog e p with Some v => v | None => policy end.

(** ** Cross-packet persistence of learned state.

    A `dynset` learns an element into a named set; that learning must persist to
    the NEXT packet (per-source rate limiting, learning sets, …).  Within one
    packet [eval_rules_mut]/[run_program_mut] thread the mutated packet (hence its
    env) across rules; to thread it across PACKETS we expose the final
    environment.  [eval_rules_mut_env]/[run_program_mut_env] mirror the verdict
    evaluators but also return the env left after the chain ran (the shared
    set/map/limiter state, NOT the per-packet meta/ct fields, which are local to
    each packet).  On a terminal verdict the env still reflects the writes the
    final rule's body made before the verdict. *)
Definition eval_rules_mut_env (rs : list rule) (e : env) (p : packet)
  : option verdict * env :=
  let '(v, (e', _)) := eval_rules_mut_st rs e p in (v, e').

Arguments eval_rules_mut_env : simpl never.

Lemma eval_rules_mut_env_nil : forall e p,
  eval_rules_mut_env [] e p = (None, e).
Proof. reflexivity. Qed.

Lemma eval_rules_mut_env_cons : forall r rest e p,
  eval_rules_mut_env (r :: rest) e p
  = match rule_step r e p with
    | (Some v, (e', p')) => if terminal v then (Some v, e')
                            else eval_rules_mut_env rest e' p'
    | (None,   (e', p')) => eval_rules_mut_env rest e' p'
    end.
Proof.
  intros r rest e p. unfold eval_rules_mut_env. rewrite eval_rules_mut_st_cons.
  destruct (rule_step r e p) as [[v|] [e' p']]; [destruct (terminal v)|]; reflexivity.
Qed.

Definition run_program_mut_env (prog : program) (e : env) (p : packet)
  : option verdict * env :=
  let '(v, (e', _)) := run_program_mut_st prog e p in (v, e').

Arguments run_program_mut_env : simpl never.

Lemma run_program_mut_env_nil : forall e p,
  run_program_mut_env [] e p = (None, e).
Proof. reflexivity. Qed.

Lemma run_program_mut_env_cons : forall rp rest e p,
  run_program_mut_env (rp :: rest) e p
  = match run_rule_step empty_rf rp e p with
    | (Some v, (e', p')) => if terminal v then (Some v, e')
                            else run_program_mut_env rest e' p'
    | (None,   (e', p')) => run_program_mut_env rest e' p'
    end.
Proof.
  intros rp rest e p. unfold run_program_mut_env. rewrite run_program_mut_st_cons.
  destruct (run_rule_step empty_rf rp e p) as [[v|] [e' p']];
    [destruct (terminal v)|]; reflexivity.
Qed.

(** Run a base chain in mutation mode, returning the verdict AND the env the chain
    leaves (with any dynset-learned elements), so a packet sequence can thread it. *)
Definition eval_chain_mut_env (c : chain) (e : env) (p : packet) : verdict * env :=
  match eval_rules_mut_env (c_rules c) e p with
  | (Some v, e') => (v, e') | (None, e') => (c_policy c, e') end.
Definition run_chain_mut_env (prog : program) (policy : verdict) (e : env) (p : packet)
  : verdict * env :=
  match run_program_mut_env prog e p with
  | (Some v, e') => (v, e') | (None, e') => (policy, e') end.

(** The env-returning evaluators RESTRICT to the verdict-only ones: the verdict
    component of [eval_rules_mut_env]/[run_program_mut_env] is exactly
    [eval_rules_mut]/[run_program_mut].  Since M6 both are DEFINED as
    projections of the same full-state fold, so the bridge is one [destruct]
    (a compiler-correctness proof for the _env pair still yields the _mut pair
    for free, [Correct.run_program_mut_compile_chain]). *)
Lemma eval_rules_mut_env_fst : forall rs e p,
  fst (eval_rules_mut_env rs e p) = eval_rules_mut rs e p.
Proof.
  intros rs e p. unfold eval_rules_mut_env, eval_rules_mut.
  destruct (eval_rules_mut_st rs e p) as [v [e' p']]; reflexivity.
Qed.

Lemma run_program_mut_env_fst : forall prog e p,
  fst (run_program_mut_env prog e p) = run_program_mut prog e p.
Proof.
  intros prog e p. unfold run_program_mut_env, run_program_mut.
  destruct (run_program_mut_st prog e p) as [v [e' p']]; reflexivity.
Qed.

(** Chain-level restriction: the verdict component of the env-returning chain
    evaluators is the _mut chain verdict. *)
Lemma eval_chain_mut_env_fst : forall c e p,
  fst (eval_chain_mut_env c e p) = eval_chain_mut c e p.
Proof.
  intros c e p. unfold eval_chain_mut_env, eval_chain_mut.
  rewrite <- eval_rules_mut_env_fst.
  destruct (eval_rules_mut_env (c_rules c) e p) as [[v|] e']; reflexivity.
Qed.

Lemma run_chain_mut_env_fst : forall prog policy e p,
  fst (run_chain_mut_env prog policy e p) = run_chain_mut prog policy e p.
Proof.
  intros prog policy e p. unfold run_chain_mut_env, run_chain_mut.
  rewrite <- run_program_mut_env_fst.
  destruct (run_program_mut_env prog e p) as [[v|] e']; reflexivity.
Qed.

(** ** The FULL-STATE base-chain form of the flat fold: verdict AND resulting
    (env, packet).  The PACKET half of the state is equally an observable — a
    `meta mark set` is a packet write that the unified semantics' own priority
    dispatch reads in a later base chain at the same hook ([eval_ruleset_u]).
    The optimizer's effect-level pipeline theorem
    ([Optimize_MutEnv.optimize_table_uncond_mut_st_correct]) is stated against
    it, so a pass cannot alter a packet-half write while preserving verdict
    and env. *)
Definition eval_chain_mut_st (c : chain) (e : env) (p : packet)
  : verdict * (env * packet) :=
  match eval_rules_mut_st (c_rules c) e p with
  | (Some v, s) => (v, s) | (None, s) => (c_policy c, s) end.

(** The (verdict, env) evaluators are the (fst, fst . snd) projections of the
    full-state fold — since M6, by definition. *)
Lemma eval_rules_mut_env_st : forall rs e p,
  eval_rules_mut_env rs e p
  = (fst (eval_rules_mut_st rs e p), fst (snd (eval_rules_mut_st rs e p))).
Proof.
  intros rs e p. unfold eval_rules_mut_env.
  destruct (eval_rules_mut_st rs e p) as [v [e' p']]; reflexivity.
Qed.

Lemma eval_chain_mut_env_st : forall c e p,
  eval_chain_mut_env c e p
  = (fst (eval_chain_mut_st c e p), fst (snd (eval_chain_mut_st c e p))).
Proof.
  intros c e p. unfold eval_chain_mut_env, eval_chain_mut_st.
  rewrite (eval_rules_mut_env_st (c_rules c) e p).
  destruct (eval_rules_mut_st (c_rules c) e p) as [[v|] [e' p']]; reflexivity.
Qed.

Lemma eval_rules_mut_st_fst : forall rs e p,
  fst (eval_rules_mut_st rs e p) = eval_rules_mut rs e p.
Proof. reflexivity. Qed.


(** A packet sequence threaded through a shared, learning environment: each packet
    is evaluated against the current [e], and the env it LEAVES (learned sets/maps,
    depleted limiter buckets, NAT mappings) seeds the next packet — the state
    update is the ruleset's OWN env-out, never an external caller-supplied step.
    So a later packet's `lookup @s` observes what an earlier packet's `add @s`
    learned.  THE sequence semantics is this fold over the unified per-packet
    run: [seq_eval_env (eval_hook_env_u h fuel rs)]
    (compiler theorem [Correct.compile_seq_hook_correct]). *)
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
    environment is not structurally terminating (nft rejects jump loops at load
    time; the kernel additionally bounds jump nesting at 16 —
    NFT_JUMP_STACK_SIZE, include/net/netfilter/nf_tables.h), so the
    interpreters are *fuel-bounded*; the compile-correctness theorem holds for
    every fuel.  Fuel EXHAUSTION, however, is observationally conflated with
    fall-through ([None]) — see § "Fuel discipline for the jump strand" below
    for the monotonicity/adequacy lemmas that make a chosen fuel budget a
    checkable hypothesis instead of an unstated side condition. *)

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

(** PROJECTION evaluator under a chain environment [cs] (the user-defined
    chains): the jump/goto/return traversal with NO state threading.

    License: on WRITE-FREE rules everywhere ([rule_writefree] on the entry
    list, [chains_writefree] on [cs]) this is exactly the verdict projection
    of the unified fold, with the state provably untouched —
    [eval_rules_u_writefree]:
      eval_rules_u fuel cs rs e p = (eval_rules_j fuel cs rs e p, (e, p)).
    A rule OUTSIDE that domain (a meta/ct set, dynset, notrack, or limiter)
    must be evaluated by the unified [eval_rules_u], which threads its writes
    through the transfer (Regression/Setread_UnderJump.v pins a config where
    the two genuinely differ).  NON-RECURSIVE (M6): the traversal is a
    [nat_rect] on the fuel (the pure per-rule read applied under the stdlib
    recursor — it owns no recursion of its own; the ONE recursive rule-list
    traversal is [eval_rules_u]); proofs step it with [eval_rules_j_0] /
    [eval_rules_j_S], which restate the historical unfolding verbatim.  The
    license theorem is what makes this a projection, not a second semantics. *)
Definition eval_rules_j (fuel : nat) (cs : list (String.string * chain))
                        (rs : list rule) (e : env) (p : packet) : option verdict :=
  nat_rect (fun _ => list rule -> env -> packet -> option verdict)
    (fun _ _ _ => None)
    (fun _ rec rs e p =>
      match rs with
      | [] => None
      | r :: rest =>
        if rule_loadable r e p && rule_applies r e p then
          match outcome r e p with
          | None => rec rest e p
          | Some Return => None
          | Some (Jump n) =>
              match chain_lookup cs n with
              | Some ch => match rec (c_rules ch) e p with
                           | Some v => Some v
                           | None   => rec rest e p
                           end
              | None => rec rest e p
              end
          | Some (Goto n) =>
              match chain_lookup cs n with
              | Some ch => rec (c_rules ch) e p
              | None    => None
              end
          | Some Continue => rec rest e p
          | Some v => Some v
          end
        else rec rest e p
      end)
    fuel rs e p.

Arguments eval_rules_j : simpl never.

Lemma eval_rules_j_0 : forall cs rs e p, eval_rules_j 0 cs rs e p = None.
Proof. reflexivity. Qed.

Lemma eval_rules_j_S : forall fuel' cs rs e p,
  eval_rules_j (S fuel') cs rs e p =
  match rs with
  | [] => None
  | r :: rest =>
    if rule_loadable r e p && rule_applies r e p then
      match outcome r e p with
      | None => eval_rules_j fuel' cs rest e p
      | Some Return => None
      | Some (Jump n) =>
          match chain_lookup cs n with
          | Some ch => match eval_rules_j fuel' cs (c_rules ch) e p with
                       | Some v => Some v
                       | None   => eval_rules_j fuel' cs rest e p
                       end
          | None => eval_rules_j fuel' cs rest e p
          end
      | Some (Goto n) =>
          match chain_lookup cs n with
          | Some ch => eval_rules_j fuel' cs (c_rules ch) e p
          | None    => None
          end
      | Some Continue => eval_rules_j fuel' cs rest e p
      | Some v => Some v
      end
    else eval_rules_j fuel' cs rest e p
  end.
Proof. reflexivity. Qed.

Definition eval_table (fuel : nat) (cs : list (String.string * chain))
                      (base : chain) (e : env) (p : packet) : verdict :=
  match eval_rules_j fuel cs (c_rules base) e p with
  | Some v => v
  | None   => c_policy base
  end.

(** Bytecode VM under a compiled chain environment [cs]; mirrors [eval_rules_j]
    (NON-RECURSIVE for the same reason; step with [run_rules_j_0]/[run_rules_j_S]). *)
Definition run_rules_j (fuel : nat) (cs : list (String.string * program))
                       (prog : program) (e : env) (p : packet) : option verdict :=
  nat_rect (fun _ => program -> env -> packet -> option verdict)
    (fun _ _ _ => None)
    (fun _ rec prog e p =>
      match prog with
      | [] => None
      | rp :: rest =>
        match run_rule empty_rf rp e p with
        | None => rec rest e p
        | Some Return => None
        | Some (Jump n) =>
            match prog_lookup cs n with
            | Some prg => match rec prg e p with
                          | Some v => Some v
                          | None   => rec rest e p
                          end
            | None => rec rest e p
            end
        | Some (Goto n) =>
            match prog_lookup cs n with
            | Some prg => rec prg e p
            | None     => None
            end
        | Some Continue => rec rest e p
        | Some v => Some v
        end
      end)
    fuel prog e p.

Arguments run_rules_j : simpl never.

Lemma run_rules_j_0 : forall cs prog e p, run_rules_j 0 cs prog e p = None.
Proof. reflexivity. Qed.

Lemma run_rules_j_S : forall fuel' cs prog e p,
  run_rules_j (S fuel') cs prog e p =
  match prog with
  | [] => None
  | rp :: rest =>
    match run_rule empty_rf rp e p with
    | None => run_rules_j fuel' cs rest e p
    | Some Return => None
    | Some (Jump n) =>
        match prog_lookup cs n with
        | Some prg => match run_rules_j fuel' cs prg e p with
                      | Some v => Some v
                      | None   => run_rules_j fuel' cs rest e p
                      end
        | None => run_rules_j fuel' cs rest e p
        end
    | Some (Goto n) =>
        match prog_lookup cs n with
        | Some prg => run_rules_j fuel' cs prg e p
        | None     => None
        end
    | Some Continue => run_rules_j fuel' cs rest e p
    | Some v => Some v
    end
  end.
Proof. reflexivity. Qed.

Definition run_table (fuel : nat) (cs : list (String.string * program))
                     (base : program) (policy : verdict) (e : env) (p : packet) : verdict :=
  match run_rules_j fuel cs base e p with
  | Some v => v
  | None   => policy
  end.

(* ================================================================== *)
(** ** Fuel discipline for the jump strand: adequacy + fuel-independence.

    (Scope: this section lives inside the PURE PROJECTION strand --
    [eval_rules_j]/[eval_table], licensed on write-free rules by
    [eval_rules_u_writefree] below.  The unified evaluator carries its OWN
    fuel discipline -- [eval_rules_u_fuel_indep] / [eval_table_u_fuel_indep],
    § "Fuel discipline for the unified evaluator" -- proved by the same
    rank-descent induction, so effectful configs are not carved out of the
    adequacy story.)

    THE PROBLEM.  [eval_rules_j fuel] returns [None] BOTH on genuine
    fall-through (empty rule list, [return], goto to a missing chain) AND on
    fuel exhaustion, and [eval_table] maps [None] to the base chain's policy.
    The exhaustion fallback is a verdict the kernel can never produce: nft
    rejects jump/goto loops at load time (libnftables walks the chain-binding
    graph and errors out on a cycle), and the kernel additionally bounds jump
    nesting at 16 (include/net/netfilter/nf_tables.h, NFT_JUMP_STACK_SIZE = 16;
    nft_do_chain breaks on overflow).  So a per-configuration theorem stated at
    ONE fuel value is kernel-meaningful only if that fuel is ADEQUATE -- large
    enough that the exhaustion case is unreachable.  The lemmas below turn that
    adequacy into a checkable hypothesis and make the verdict provably
    fuel-independent above a computable bound.

    WHY NOT PLAIN MONOTONICITY.  The naive statement

        eval_rules_j fuel cs rs e p = Some v ->
        eval_rules_j (S fuel) cs rs e p = Some v

    is FALSE for this evaluator, because a jump treats the callee's [None] as
    the callee's fall-through and resumes the caller: with too little fuel the
    callee exhausts, the caller resumes as if the callee fell through, and MORE
    fuel can flip the verdict.  [eval_rules_j_not_naively_monotone] below pins
    a two-chain counterexample (Some Accept at fuel 2, Some Drop at fuel 3),
    machine-checked so the false statement cannot be "restored" by accident.

    THE HONEST STATEMENT.  Under [chain_ranked] -- a rank function witnessing
    the load-time acyclicity nft itself enforces (every realised jump/goto
    target of a chain's rule has smaller rank; targets read from a verdict map
    depend on the ENV, so the hypothesis is stated per-env, dischargeable once
    the relevant [e_vmap] contents are pinned) -- every fuel at
    [sufficient_fuel cs rs] or above yields the SAME result
    ([eval_rules_j_fuel_indep]).  The proof is ONE rank-descent induction on
    the fuel ([eval_rules_j_fuel_indep_aux]): with fuel at the structural
    bound for the current rank budget, a jump's callee (strictly smaller
    rank) and the resumed caller (one rule shorter) are each themselves
    adequately fueled, so the exhaustion arm is unreachable in EVERY branch
    and extra fuel changes nothing.  [sufficient_fuel cs rs] is a computable
    structural bound (S (|rs| + |cs| * S (max chain length)) -- fuel is a
    DESCENT budget, not a work budget: a jump gives callee and continuation
    the SAME decremented fuel, so the requirement is the longest chain of
    nested decrements, which an acyclic jump graph bounds by one traversal of
    each chain plus the base).  Consequently [eval_table]'s verdict is
    fuel-independent there ([eval_table_fuel_indep]) and its policy fallback
    can only be GENUINE fall-through: a [None] at adequate fuel persists at
    every adequate fuel, which exhaustion -- curable by more fuel -- cannot
    ([eval_table_policy_is_fallthrough]).  For the common transfer-free case
    (no rule outcome is ever Jump/Goto under the given env) the boolean
    [chains_no_transfer] discharges [chain_ranked] in one [reflexivity]
    ([chains_no_transfer_ranked]).

    RETIRED STRATUM (M6): the historical exhaustion-observable TWIN evaluator
    (the "jx" strand) -- a third recursive jump traversal whose [Some o]
    witnessed a clean run, with its Kleene-monotonicity layer (monotone /
    stable / the jx-witnessed [eval_rules_j_fuel_stable])
    -- is DELETED: the direct rank-descent induction proves the same
    user-facing fuel-independence with no parallel traversal for rules to
    flow through, and the unified evaluator now carries the same discipline
    itself.  See THEOREMS.md § strata retirements.

    VM side: the compiled mirror needs no second development --
    [Correct.compile_table_correct] equates [run_table] with [eval_table] at
    EVERY fuel, so fuel-independence transports to every compiled chain
    environment ([Correct.run_table_fuel_indep_compiled]); a hand-written
    program that no source chain compiles to has no jump-graph rank to speak
    of, and is out of scope by design.

    User-facing forms: [Nft_Tactics.nft_yields_fuel_indep] (and the
    accepts/denies corollaries) + proof/CONFIG_PROOFS.md § "Choosing the fuel
    budget"; worked instance [Tutorial_Proofs.tutorial_blocks_exactly_any_fuel]. *)

(* ------------------------------------------------------------------ *)
(** *** Counterexample: [eval_rules_j] alone is NOT fuel-monotone.

    Base chain [jump b; accept], user chain b = [fall-through; drop].  At fuel
    2 the callee exhausts after its first rule, the caller treats that as b's
    fall-through and accepts; at fuel 3 the callee reaches its drop.  Any
    fuel-monotonicity claim must therefore carry an adequacy witness — the
    [chain_ranked] + [sufficient_fuel] hypotheses of the rank-descent lemmas
    below.  ([reflexivity] proves both equations for
    EVERY env and packet: the probe rules have empty bodies.) *)

Definition fuel_probe_noop : rule :=
  {| r_body := []; r_outcome := ONone; r_after := [] |}.
Definition fuel_probe_drop : rule :=
  {| r_body := []; r_outcome := OVerdict Drop; r_after := [] |}.
Definition fuel_probe_accept : rule :=
  {| r_body := []; r_outcome := OVerdict Accept; r_after := [] |}.
Definition fuel_probe_jump : rule :=
  {| r_body := []; r_outcome := OVerdict (Jump "b"%string); r_after := [] |}.
Definition fuel_probe_cs : list (String.string * chain) :=
  [("b"%string,
    {| c_policy := Accept; c_rules := [fuel_probe_noop; fuel_probe_drop] |})].
Definition fuel_probe_rs : list rule := [fuel_probe_jump; fuel_probe_accept].

Example eval_rules_j_not_naively_monotone : forall e p,
  eval_rules_j 2 fuel_probe_cs fuel_probe_rs e p = Some Accept
  /\ eval_rules_j 3 fuel_probe_cs fuel_probe_rs e p = Some Drop.
Proof. intros e p. split; reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(** *** Adequacy: a computable sufficient fuel under an acyclic jump graph. *)

Definition chain_len_max (cs : list (String.string * chain)) : nat :=
  fold_right Nat.max 0 (map (fun nc => List.length (c_rules (snd nc))) cs).

Lemma chain_lookup_len_max : forall cs n ch,
  chain_lookup cs n = Some ch ->
  List.length (c_rules ch) <= chain_len_max cs.
Proof.
  induction cs as [| [m ch'] cs IH]; intros n ch H; cbn in H; [ discriminate | ].
  unfold chain_len_max; cbn [map fold_right snd].
  destruct (String.eqb n m).
  - injection H as <-. apply Nat.le_max_l.
  - specialize (IH _ _ H). unfold chain_len_max in IH.
    etransitivity; [ exact IH | apply Nat.le_max_r ].
Qed.

(** The computable bound: one traversal of the entry rule list plus one
    traversal of every chain of the environment (each entered at most once on
    any descent path of an acyclic graph).  Deliberately COARSE — it
    over-approximates the exact need so it stays a one-liner a user can
    [vm_compute]; the kernel's own bound is depth (16 jump frames), ours is the
    acyclicity that load-time checking guarantees. *)
Definition sufficient_fuel (cs : list (String.string * chain)) (rs : list rule) : nat :=
  S (List.length rs + List.length cs * S (chain_len_max cs)).

(** Every jump/goto target that rule [r] can realise (under env [e], on any
    packet) and that resolves in [cs] has rank below [k]. *)
Definition rule_targets_below (rank : String.string -> nat)
    (cs : list (String.string * chain)) (e : env) (k : nat) (r : rule) : Prop :=
  forall p m ch',
    (outcome r e p = Some (Jump m) \/ outcome r e p = Some (Goto m)) ->
    chain_lookup cs m = Some ch' ->
    rank m < k.

(** The acyclicity witness: a rank function under which every chain's realised
    transfers strictly descend.  This is the semantic shadow of nft's
    LOAD-TIME loop rejection (nft refuses a ruleset whose chain-binding graph
    has a cycle), stated per-env because vmap verdicts — hence jump targets —
    live in [e_vmap e]. *)
Definition chain_ranked (rank : String.string -> nat)
    (cs : list (String.string * chain)) (e : env) : Prop :=
  forall n ch, chain_lookup cs n = Some ch ->
    rank n < List.length cs /\
    (forall r, In r (c_rules ch) -> rule_targets_below rank cs e (rank n) r).

(** The rank-descent induction, in pairwise-equality form: with fuel at the
    structural bound for the current rank budget [k], MORE fuel cannot change
    the result -- callee and resumed caller are each adequately fueled, so no
    branch can reach the exhaustion arm.  The entry rule list needs no
    hypothesis of its own in the corollaries: any target it resolves in [cs]
    has rank below [length cs] by [chain_ranked]. *)
Lemma eval_rules_j_fuel_indep_aux : forall rank cs e,
  chain_ranked rank cs e ->
  forall fuel k rs p fuel',
    (forall r, In r rs -> rule_targets_below rank cs e k r) ->
    S (List.length rs + k * S (chain_len_max cs)) <= fuel ->
    fuel <= fuel' ->
    eval_rules_j fuel' cs rs e p = eval_rules_j fuel cs rs e p.
Proof.
  intros rank cs e Hcr.
  induction fuel as [| f IH]; intros k rs p fuel' Htgt Hfuel Hle; [ lia | ].
  destruct fuel' as [| f']; [ lia | ].
  apply le_S_n in Hle.
  rewrite !eval_rules_j_S.
  destruct rs as [| r rest]; [ reflexivity | ].
  cbn [List.length] in Hfuel.
  assert (Hrest : forall r0, In r0 rest -> rule_targets_below rank cs e k r0)
    by (intros; apply Htgt; now right).
  destruct (rule_loadable r e p && rule_applies r e p) eqn:Hga.
  2:{ apply (IH k rest p f' Hrest); lia. }
  destruct (outcome r e p) as [v|] eqn:Hout.
  2:{ apply (IH k rest p f' Hrest); lia. }
  destruct v as [ | | | tc cc | lo hi bp fo | n | n | ];
    try reflexivity;
    try (apply (IH k rest p f' Hrest); lia).
  - (* Jump *)
    destruct (chain_lookup cs n) as [ch|] eqn:Hlk;
      [ | apply (IH k rest p f' Hrest); lia ].
    assert (Hrn : rank n < k)
      by (eapply (Htgt r (or_introl eq_refl) p n ch); eauto).
    pose proof (chain_lookup_len_max cs n ch Hlk) as Hlen.
    pose proof (proj2 (Hcr n ch Hlk)) as Hch.
    rewrite (IH (rank n) (c_rules ch) p f' Hch); [ | nia | lia ].
    destruct (eval_rules_j f cs (c_rules ch) e p).
    + reflexivity.
    + apply (IH k rest p f' Hrest); lia.
  - (* Goto *)
    destruct (chain_lookup cs n) as [ch|] eqn:Hlk; [ | reflexivity ].
    assert (Hrn : rank n < k)
      by (eapply (Htgt r (or_introl eq_refl) p n ch); eauto).
    pose proof (chain_lookup_len_max cs n ch Hlk) as Hlen.
    pose proof (proj2 (Hcr n ch Hlk)) as Hch.
    apply (IH (rank n) (c_rules ch) p f' Hch); [ nia | lia ].
Qed.

(** Above the bound the verdict no longer depends on the fuel at all -- the
    fuel-free form config theorems quantify with. *)
Theorem eval_rules_j_fuel_indep : forall rank cs e,
  chain_ranked rank cs e ->
  forall rs p fuel fuel',
    sufficient_fuel cs rs <= fuel ->
    sufficient_fuel cs rs <= fuel' ->
    eval_rules_j fuel cs rs e p = eval_rules_j fuel' cs rs e p.
Proof.
  intros rank cs e Hcr rs p fuel fuel' Hf Hf'.
  assert (Htgt : forall r, In r rs ->
            rule_targets_below rank cs e (List.length cs) r).
  { intros r _ q m ch' _ Hlk. exact (proj1 (Hcr m ch' Hlk)). }
  assert (Hbound : S (List.length rs
                      + List.length cs * S (chain_len_max cs))
                   <= sufficient_fuel cs rs) by (unfold sufficient_fuel; lia).
  transitivity (eval_rules_j (sufficient_fuel cs rs) cs rs e p).
  - exact (eval_rules_j_fuel_indep_aux rank cs e Hcr
             (sufficient_fuel cs rs) (List.length cs) rs p fuel
             Htgt Hbound Hf).
  - symmetry.
    exact (eval_rules_j_fuel_indep_aux rank cs e Hcr
             (sufficient_fuel cs rs) (List.length cs) rs p fuel'
             Htgt Hbound Hf').
Qed.

Theorem eval_table_fuel_indep : forall rank cs e,
  chain_ranked rank cs e ->
  forall base p fuel fuel',
    sufficient_fuel cs (c_rules base) <= fuel ->
    sufficient_fuel cs (c_rules base) <= fuel' ->
    eval_table fuel cs base e p = eval_table fuel' cs base e p.
Proof.
  intros rank cs e Hcr base p fuel fuel' Hf Hf'. unfold eval_table.
  now rewrite (eval_rules_j_fuel_indep rank cs e Hcr (c_rules base) p fuel fuel').
Qed.

(** At adequate fuel, [eval_table]'s policy fallback can only be GENUINE
    fall-through: the [None] it maps to the policy persists at EVERY adequate
    fuel -- which exhaustion, curable by more fuel, cannot.  (Successor of the
    retired jx-witnessed form: same name, same role in config proofs; the
    cleanness witness is now fuel-independence itself.) *)
Theorem eval_table_policy_is_fallthrough : forall rank cs e,
  chain_ranked rank cs e ->
  forall base p fuel,
    sufficient_fuel cs (c_rules base) <= fuel ->
    eval_rules_j fuel cs (c_rules base) e p = None ->
    forall fuel', sufficient_fuel cs (c_rules base) <= fuel' ->
      eval_rules_j fuel' cs (c_rules base) e p = None.
Proof.
  intros rank cs e Hcr base p fuel Hf Hnone fuel' Hf'.
  rewrite (eval_rules_j_fuel_indep rank cs e Hcr (c_rules base) p fuel' fuel Hf' Hf).
  exact Hnone.
Qed.

(* ------------------------------------------------------------------ *)
(** *** Discharging [chain_ranked] for transfer-free chain environments.

    Most config proofs are about chains none of whose rules can transfer
    (every static verdict and every vmap verdict under the pinned env is
    non-Jump/Goto).  [chains_no_transfer] decides that by computation and
    [chains_no_transfer_ranked] turns it into the rank witness (rank 0 for
    everything: no realisable transfer means nothing to descend on). *)

Definition verdict_no_transfer (v : verdict) : bool :=
  match v with Jump _ | Goto _ => false | _ => true end.

Definition rule_no_transfer (e : env) (r : rule) : bool :=
  match r_outcome r with
  | OVerdict v => verdict_no_transfer v
  | OVmap s | OVmapNat s _ =>
      forallb (fun ent => verdict_no_transfer (snd ent)) (e_vmap e (vm_name s))
  | _ => true
  end.

Lemma assoc_verdict_in : forall key l v,
  assoc_verdict key l = Some v -> exists lo hi, In (lo, hi, v) l.
Proof.
  induction l as [| [[lo hi] v'] l IH]; cbn; intros v H; [ discriminate | ].
  destruct (data_in_iv key (lo, hi)).
  - injection H as <-. eauto.
  - destruct (IH _ H) as (lo' & hi' & Hin). eauto.
Qed.

(** The only verdict [r_after] statements can produce is the synproxy [Drop]. *)
Lemma stmts_after_outcome_drop : forall ss p v,
  stmts_after_outcome ss p = Some v -> v = Drop.
Proof.
  induction ss as [| s ss IH]; cbn; intros p v H; [ discriminate | ].
  destruct s; try (destruct (stmt_loadable _ p); [ eauto | discriminate ]).
  destruct (synproxy_loadable p); [ | discriminate ].
  destruct (synproxy_stops p); [ now injection H as <- | eauto ].
Qed.

Lemma rule_no_transfer_sound : forall e r,
  rule_no_transfer e r = true ->
  forall p m,
    outcome r e p <> Some (Jump m) /\ outcome r e p <> Some (Goto m).
Proof.
  intros e r H p m.
  unfold outcome, outcome_core, terminal_outcome.
  destruct (body_synproxy_stops (r_body r) p); [ split; discriminate | ].
  unfold rule_no_transfer in H.
  unfold r_vmap, r_nat, r_tproxy, r_fwd, r_queue, r_verdict.
  destruct (r_outcome r) as [ v | | s | s ns | ns | ts | fs | qs ]; cbn.
  - (* OVerdict v *)
    destruct v; try (split; discriminate); try discriminate H.
    (* Continue: the static verdict falls through to the after-statements *)
    split; intro Hc; apply stmts_after_outcome_drop in Hc; discriminate.
  - (* ONone *)
    split; intro Hc; apply stmts_after_outcome_drop in Hc; discriminate.
  - (* OVmap *)
    destruct (assoc_verdict _ (e_vmap e (vm_name s))) as [v|] eqn:Ha.
    + apply assoc_verdict_in in Ha as (lo & hi & Hin).
      eapply forallb_forall in H; [ | exact Hin ].
      cbn in H. destruct v; try (split; discriminate); discriminate H.
    + (* miss: falls through to the after-statements *)
      split; intro Hc; apply stmts_after_outcome_drop in Hc; discriminate.
  - (* OVmapNat *)
    destruct (assoc_verdict _ (e_vmap e (vm_name s))) as [v|] eqn:Ha.
    + apply assoc_verdict_in in Ha as (lo & hi & Hin).
      eapply forallb_forall in H; [ | exact Hin ].
      cbn in H. destruct v; try (split; discriminate); discriminate H.
    + split; discriminate.
  - split; discriminate.
  - split; discriminate.
  - split; discriminate.
  - split; discriminate.
Qed.

Definition chains_no_transfer (e : env) (cs : list (String.string * chain)) : bool :=
  forallb (fun nc => forallb (rule_no_transfer e) (c_rules (snd nc))) cs.

Lemma chain_lookup_in : forall cs n ch,
  chain_lookup cs n = Some ch -> In (n, ch) cs.
Proof.
  induction cs as [| [m ch'] cs IH]; cbn; intros n ch H; [ discriminate | ].
  destruct (String.eqb n m) eqn:He.
  - apply String.eqb_eq in He. subst m. injection H as <-. now left.
  - right. now apply IH.
Qed.

Lemma chains_no_transfer_ranked : forall e cs,
  chains_no_transfer e cs = true ->
  chain_ranked (fun _ => O) cs e.
Proof.
  intros e cs H n ch Hlk.
  pose proof (chain_lookup_in _ _ _ Hlk) as Hin. split.
  - destruct cs; [ cbn in Hlk; discriminate | cbn; lia ].
  - intros r Hr p m ch' Ho Hlk'.
    exfalso.
    unfold chains_no_transfer in H.
    eapply forallb_forall in H; [ | exact Hin ].
    eapply forallb_forall in H; [ | exact Hr ].
    destruct (rule_no_transfer_sound _ _ H p m) as [H1 H2].
    destruct Ho; auto.
Qed.

(* ------------------------------------------------------------------ *)
(** *** SYNTACTIC jump-freedom: the entry-state-free license (M6).

    [rules_jumpfree]/[chain_jumpfree] are ENTRY-STATE predicates: they ask
    whether the realised outcomes at ONE (env, packet) are transfer-free,
    which is exactly the pair the traversal was entered with -- under
    mutation, later rules run at a DIFFERENT state, so an entry-state
    hypothesis about them is wrong by construction.  The syntactic form below
    quantifies away the state: a rule whose STATIC outcome is neither a
    transfer verdict nor a verdict-map dispatch can realise no Jump/Goto/
    Return at ANY (env, packet) -- its only other verdict sources are the
    post-outcome statements (Drop only, [stmts_after_outcome_drop]) and the
    NAT/tproxy/fwd/queue terminals (never transfers).  The implication lemma
    [rules_jumpfree_syn_sound] discharges the semantic predicate at every
    state at once, so no license needs an entry-state hypothesis. *)

Definition rule_jumpfree_syn (r : rule) : bool :=
  match r_outcome r with
  | OVerdict (Jump _) | OVerdict (Goto _) | OVerdict Return => false
  | OVmap _ | OVmapNat _ _ => false
  | _ => true
  end.

Definition rules_jumpfree_syn (rs : list rule) : bool :=
  forallb rule_jumpfree_syn rs.

Definition chain_jumpfree_syn (c : chain) : bool :=
  rules_jumpfree_syn (c_rules c).

Lemma rule_jumpfree_syn_sound : forall r,
  rule_jumpfree_syn r = true ->
  forall e p, outcome_jumpfree r e p = true.
Proof.
  intros r H e p.
  unfold outcome_jumpfree.
  destruct (outcome r e p) as [v|] eqn:Ho; [| reflexivity].
  unfold outcome, outcome_core, terminal_outcome in Ho.
  destruct (body_synproxy_stops (r_body r) p);
    [ injection Ho as <-; reflexivity |].
  unfold rule_jumpfree_syn in H.
  unfold r_vmap, r_nat, r_tproxy, r_fwd, r_queue, r_verdict in Ho.
  destruct (r_outcome r) as [ w | | s | s ns | ns | ts | fs | qs ];
    cbn in Ho, H; try discriminate H.
  - (* OVerdict w *)
    destruct w; try discriminate H; try (injection Ho as <-; reflexivity).
    (* Continue: falls through to the after-statements (Drop only) *)
    apply stmts_after_outcome_drop in Ho. now subst v.
  - (* ONone: after-statements only *)
    apply stmts_after_outcome_drop in Ho. now subst v.
  - (* ONat *) destruct v; try reflexivity; discriminate Ho.
  - (* OTproxy *) destruct v; try reflexivity; discriminate Ho.
  - (* OFwd *) destruct v; try reflexivity; discriminate Ho.
  - (* OQueue *) destruct v; try reflexivity; discriminate Ho.
Qed.

Lemma rules_jumpfree_syn_sound : forall rs,
  rules_jumpfree_syn rs = true ->
  forall e p, rules_jumpfree rs e p = true.
Proof.
  intros rs H e p. unfold rules_jumpfree. apply forallb_forall.
  intros r Hr. apply rule_jumpfree_syn_sound.
  unfold rules_jumpfree_syn in H. eapply forallb_forall in H; eauto.
Qed.

Lemma chain_jumpfree_syn_sound : forall c,
  chain_jumpfree_syn c = true ->
  forall e p, chain_jumpfree c e p = true.
Proof.
  intros c H e p. unfold chain_jumpfree. now apply rules_jumpfree_syn_sound.
Qed.


(* ------------------------------------------------------------------ *)
(** *** The under-fueled fallback, exhibited and then excluded.

    With fuel 1 the probe ruleset's [eval_table] returns the chain POLICY
    ([Continue] here — a verdict no kernel hook can yield): the jump exhausts
    and the fallback fires.  At [sufficient_fuel] (= 6, computable) and above,
    the adequacy lemma pins the verdict to the real [Drop] for EVERY fuel —
    the exhaustion fallback is gone. *)

Example eval_table_under_fueled : forall e p,
  eval_table 1 fuel_probe_cs
    {| c_policy := Continue; c_rules := fuel_probe_rs |} e p = Continue.
Proof. intros e p. reflexivity. Qed.

Example fuel_probe_ranked : forall e, chain_ranked (fun _ => O) fuel_probe_cs e.
Proof. intro e. apply chains_no_transfer_ranked. reflexivity. Qed.

Example fuel_probe_sufficient :
  sufficient_fuel fuel_probe_cs fuel_probe_rs = 6.
Proof. reflexivity. Qed.

Example eval_table_adequately_fueled : forall e p fuel,
  6 <= fuel ->
  eval_table fuel fuel_probe_cs
    {| c_policy := Continue; c_rules := fuel_probe_rs |} e p = Drop.
Proof.
  intros e p fuel Hf.
  set (base := {| c_policy := Continue; c_rules := fuel_probe_rs |}).
  assert (Hs : sufficient_fuel fuel_probe_cs (c_rules base) <= fuel) by exact Hf.
  assert (H6 : sufficient_fuel fuel_probe_cs (c_rules base) <= 6) by exact (le_n 6).
  rewrite (eval_table_fuel_indep (fun _ => O) fuel_probe_cs e (fuel_probe_ranked e)
             base p fuel 6 Hs H6).
  reflexivity.
Qed.

(** ** Multi-table / multi-hook dispatch (netfilter verdict combination).

    At one hook the registered base chains across all tables run in priority
    order.  Selecting and ordering the base chains for a hook is the control
    plane's job; here we model the *data-plane* traversal over an already
    (hook,priority)-ordered list of (chain-env, base-chain) pairs: a base chain
    that ACCEPTs (or falls through to an accept policy) lets the packet proceed to
    the NEXT base chain, while DROP/REJECT/QUEUE is terminal — exactly how
    netfilter propagates a verdict across the chains at a hook.  If every base
    chain accepts, the packet is accepted.

    PROJECTION evaluator: built on [eval_table], so — like it — no writes are
    threaded between rules, between chains, or between base chains; licensed
    on write-free bases by [eval_ruleset_u_writefree] (the unified
    [eval_ruleset_u] below threads the state a base chain leaves into the
    next one). *)
Definition base_continues (v : verdict) : bool :=
  match v with Accept | Continue => true | _ => false end.

(** NON-RECURSIVE (M6): the pure hook dispatch is a [fold_left] over the base
    chains with a "settled" accumulator ([Some v] = a non-continuing verdict
    settled the hook, absorbing the rest; [None] = still traversing); step
    with [eval_ruleset_nil]/[eval_ruleset_cons].  The unified
    [eval_ruleset_u] below has the same shape with the state threaded. *)
Definition eval_ruleset_step (fuel : nat) (e : env) (p : packet)
    (acc : option verdict) (cb : list (String.string * chain) * chain)
  : option verdict :=
  match acc with
  | Some v => Some v
  | None =>
      let v := eval_table fuel (fst cb) (snd cb) e p in
      if base_continues v then None else Some v
  end.

Definition eval_ruleset (fuel : nat)
    (bases : list (list (String.string * chain) * chain)) (e : env) (p : packet) : verdict :=
  match fold_left (eval_ruleset_step fuel e p) bases None with
  | Some v => v
  | None => Accept
  end.

Arguments eval_ruleset : simpl never.

Lemma eval_ruleset_settled : forall fuel bases e p v,
  fold_left (eval_ruleset_step fuel e p) bases (Some v) = Some v.
Proof.
  intros fuel bases e p; induction bases as [| cb bases IH]; intros v;
    [reflexivity | apply IH].
Qed.

Lemma eval_ruleset_nil : forall fuel e p, eval_ruleset fuel [] e p = Accept.
Proof. reflexivity. Qed.

Lemma eval_ruleset_cons : forall fuel cs base rest e p,
  eval_ruleset fuel ((cs, base) :: rest) e p
  = let v := eval_table fuel cs base e p in
    if base_continues v then eval_ruleset fuel rest e p else v.
Proof.
  intros fuel cs base rest e p. cbv zeta. unfold eval_ruleset.
  cbn [fold_left]. unfold eval_ruleset_step at 2. cbn [fst snd].
  destruct (base_continues (eval_table fuel cs base e p)) eqn:Hv;
    [ reflexivity | now rewrite eval_ruleset_settled ].
Qed.

(** VM mirror; same shape. *)
Definition run_ruleset_step (fuel : nat) (e : env) (p : packet)
    (acc : option verdict)
    (cb : list (String.string * program) * (program * verdict))
  : option verdict :=
  match acc with
  | Some v => Some v
  | None =>
      let v := run_table fuel (fst cb) (fst (snd cb)) (snd (snd cb)) e p in
      if base_continues v then None else Some v
  end.

Definition run_ruleset (fuel : nat)
    (bases : list (list (String.string * program) * (program * verdict))) (e : env) (p : packet) : verdict :=
  match fold_left (run_ruleset_step fuel e p) bases None with
  | Some v => v
  | None => Accept
  end.

Arguments run_ruleset : simpl never.

Lemma run_ruleset_settled : forall fuel bases e p v,
  fold_left (run_ruleset_step fuel e p) bases (Some v) = Some v.
Proof.
  intros fuel bases e p; induction bases as [| cb bases IH]; intros v;
    [reflexivity | apply IH].
Qed.

Lemma run_ruleset_nil : forall fuel e p, run_ruleset fuel [] e p = Accept.
Proof. reflexivity. Qed.

Lemma run_ruleset_cons : forall fuel cs base policy rest e p,
  run_ruleset fuel ((cs, (base, policy)) :: rest) e p
  = let v := run_table fuel cs base policy e p in
    if base_continues v then run_ruleset fuel rest e p else v.
Proof.
  intros fuel cs base policy rest e p. cbv zeta. unfold run_ruleset.
  cbn [fold_left]. unfold run_ruleset_step at 2. cbn [fst snd].
  destruct (base_continues (run_table fuel cs base policy e p)) eqn:Hv;
    [ reflexivity | now rewrite run_ruleset_settled ].
Qed.

(** ** Hook registration: which base chains are active at which hook, and in what
    priority order.  This is *separate* metadata from a chain's rules (a base
    chain is `type filter hook input priority 0`), so we model it as a tagged list
    rather than fields on [chain] — the engine then filters by hook and sorts by
    priority to obtain the ordered base-chain list [eval_ruleset] traverses.
    [hook_id]/[hook_eqb] are defined above (near [apply_nat], which is itself
    hook-dependent). *)
Record hooked_chain : Type := {
  hc_hook : hook_id;
  hc_prio : Z;   (* kernel hook priority: a SIGNED int (e.g. dnat prerouting -100) *)
  hc_env  : list (String.string * chain);  (* the jump-target chains in its table *)
  hc_base : chain;
}.

Fixpoint insert_hc (x : hooked_chain) (l : list hooked_chain) : list hooked_chain :=
  match l with
  | [] => [x]
  | y :: ys => if Z.leb (hc_prio x) (hc_prio y) then x :: y :: ys else y :: insert_hc x ys
  end.
Fixpoint sort_hc (l : list hooked_chain) : list hooked_chain :=
  match l with [] => [] | x :: xs => insert_hc x (sort_hc xs) end.

(** The ordered (env, base-chain) list active at hook [h]: the registered base
    chains for [h], ascending by priority (lower priority runs first). *)
Definition select_hook (rs : list hooked_chain) (h : hook_id)
  : list (list (String.string * chain) * chain) :=
  map (fun hc => (hc_env hc, hc_base hc))
      (sort_hc (filter (fun hc => hook_eqb (hc_hook hc) h) rs)).

(** Full ruleset evaluation at a hook: select+order the base chains, then dispatch.
    PROJECTION evaluator: inherits [eval_ruleset]'s license — no writes are
    threaded; on write-free bases it is the verdict projection of the unified
    [eval_hook_u] ([eval_hook_u_writefree]). *)
Definition eval_hook (fuel : nat) (rs : list hooked_chain) (h : hook_id)
                     (e : env) (p : packet) : verdict :=
  eval_ruleset fuel (select_hook rs h) e p.

(** ** Stateful accumulation across a packet sequence.

    RETIRED STRATUM: the historical [seq_eval] threaded the between-packet
    environment through an EXTERNAL, caller-supplied
    [step : verdict -> env -> env] — the environment evolution was NOT
    generated by the ruleset itself, so an effectful ruleset's own learning
    (dynset adds, limiter depletion, NAT mappings) was modeled by whatever the
    caller wrote, i.e. not modeled at all.  Its successor is [seq_eval_env]
    (above) instantiated with the unified per-packet run [eval_hook_env_u]:
    the between-packet env is definitionally the ruleset's OWN env-out
    (compiler theorem [Correct.compile_seq_hook_correct]; cross-packet pins
    Regression/Seq_Hook_Carry.v). *)

(* ================================================================== *)
(** ** THE UNIFIED SEMANTICS: one effect-threading, jump-following evaluator
    per side.

    [eval_rules_u] (DSL) and [run_rules_u] (VM, below) are THE semantics of a
    rule list under a chain environment: a single fuel-bounded fold that BOTH
    threads every state effect — packet meta/ct writes, dynset env writes, the
    notrack latch, position-exact limiter/quota/connlimit consumption, all via
    the per-rule single fold [rule_step]/[run_rule_step] — AND follows control flow
    (jump / goto / return, user-defined chains).  The control-flow shape is
    exactly [eval_rules_j]'s (fuel as a descent budget, a jump resumes the
    caller on the callee's fall-through, [None] on exhaustion), but the state
    is threaded THROUGH the transfer: the jumped-to chain starts from the
    caller's accumulated (env, packet), each of its rules sees its own
    intra-rule writes, and on fall-through/return the callee's accumulated
    state carries BACK into the resuming caller.  This is the kernel shape:
    nft_do_chain runs every expression against the one live (skb, state)
    regardless of which chain frame the rule sits in
    (net/netfilter/nf_tables_core.c, the jumpstack loop).

    Effectful × control-flow behaviour is jointly verified at this evaluator:
    compiler correctness is [Correct.compile_table_u_correct] /
    [compile_ruleset_u_correct] / [compile_hook_u_correct] /
    [compile_seq_hook_correct]; the witnessed behaviour (intra-rule
    set-then-read ACCEPTS inside a jumped-to chain, caller writes visible in
    the callee, callee writes visible after the return, dynset learning under
    a jump) is pinned in Regression/Setread_UnderJump.v.

    Every earlier rule-list evaluator in this file is a PROJECTION of this
    fold, licensed by a coincidence theorem on the sub-domain where it
    provably agrees (see the evaluator matrix in the file header):
    [eval_rules_u_writefree] (the pure jump strand, on write-free rules) and
    [eval_rules_u_mut_proj] (the flat mutation strand, on transfer-free
    rules). *)

Fixpoint eval_rules_u (fuel : nat) (cs : list (String.string * chain))
                      (rs : list rule) (e : env) (p : packet)
  : option verdict * (env * packet) :=
  match fuel with
  | O => (None, (e, p))
  | S fuel' =>
    match rs with
    | [] => (None, (e, p))
    | r :: rest =>
      match rule_step r e p with
      | (Some v, (e', p')) =>
          match v with
          | Jump n =>
              match chain_lookup cs n with
              | Some ch =>
                  match eval_rules_u fuel' cs (c_rules ch) e' p' with
                  | (Some w, s) => (Some w, s)
                  | (None, (e'', p'')) => eval_rules_u fuel' cs rest e'' p''
                  end
              | None => eval_rules_u fuel' cs rest e' p'
              end
          | Goto n =>
              match chain_lookup cs n with
              | Some ch => eval_rules_u fuel' cs (c_rules ch) e' p'
              | None    => (None, (e', p'))
              end
          | Return => (None, (e', p'))
          | Continue => eval_rules_u fuel' cs rest e' p'
          | _ => (Some v, (e', p'))
          end
      | (None, (e', p')) => eval_rules_u fuel' cs rest e' p'
      end
    end
  end.

(** Base-chain form: verdict (policy on fall-through) plus the state the
    traversal leaves — the packet for the next hook, the env (learned dynsets,
    depleted limiters) for the next packet. *)
Definition eval_table_u (fuel : nat) (cs : list (String.string * chain))
                        (base : chain) (e : env) (p : packet)
  : verdict * (env * packet) :=
  match eval_rules_u fuel cs (c_rules base) e p with
  | (Some v, s) => (v, s)
  | (None,   s) => (c_policy base, s)
  end.

(** VM twin: same traversal over compiled rule programs, per-rule state from
    [run_rule_step]. *)
Fixpoint run_rules_u (fuel : nat) (cs : list (String.string * program))
                     (prog : program) (e : env) (p : packet)
  : option verdict * (env * packet) :=
  match fuel with
  | O => (None, (e, p))
  | S fuel' =>
    match prog with
    | [] => (None, (e, p))
    | rp :: rest =>
      match run_rule_step empty_rf rp e p with
      | (Some v, (e', p')) =>
          match v with
          | Jump n =>
              match prog_lookup cs n with
              | Some prg =>
                  match run_rules_u fuel' cs prg e' p' with
                  | (Some w, s) => (Some w, s)
                  | (None, (e'', p'')) => run_rules_u fuel' cs rest e'' p''
                  end
              | None => run_rules_u fuel' cs rest e' p'
              end
          | Goto n =>
              match prog_lookup cs n with
              | Some prg => run_rules_u fuel' cs prg e' p'
              | None     => (None, (e', p'))
              end
          | Return => (None, (e', p'))
          | Continue => run_rules_u fuel' cs rest e' p'
          | _ => (Some v, (e', p'))
          end
      | (None, (e', p')) => run_rules_u fuel' cs rest e' p'
      end
    end
  end.

Definition run_table_u (fuel : nat) (cs : list (String.string * program))
                       (base : program) (policy : verdict) (e : env) (p : packet)
  : verdict * (env * packet) :=
  match run_rules_u fuel cs base e p with
  | (Some v, s) => (v, s)
  | (None,   s) => (policy, s)
  end.

(** The state a single (jump-free) chain LEAVES — the packet handed to the next
    chain/hook and the env (learned dynsets, established NAT tuples, depleted
    limiters) for the next packet.  Successor of the RETIRED trace strand
    ([eval_rules_trace]/[eval_chain_trace]/[chain_out], THEOREMS.md § strata
    retirements): the packet/env/NAT threading is the unified fold's own state
    half, not a side evaluator's. *)
Definition eval_chain_u (c : chain) (e : env) (p : packet)
  : verdict * (env * packet) :=
  eval_table_u (S (List.length (c_rules c))) [] c e p.
Definition chain_out (c : chain) (e : env) (p : packet) : packet :=
  snd (snd (eval_chain_u c e p)).
Definition chain_out_env (c : chain) (e : env) (p : packet) : env :=
  fst (snd (eval_chain_u c e p)).

(** Multi-table / multi-hook dispatch with the state THREADED between base
    chains: a base chain that lets the packet proceed hands the NEXT base chain
    the packet (and env) it left — a mark set in an earlier-priority chain is
    visible to a later one, as the kernel carries it on the skb. *)
(** NON-RECURSIVE (M6): like the pure dispatch, a [fold_left] with a
    "settled" accumulator -- but carrying the (env, packet) state so each base
    chain starts from the state the previous one left, and a settling verdict
    freezes the state it settled at.  The ONE recursive traversal stays
    [eval_rules_u]/[run_rules_u]; the dispatch layers above them are folds of
    [eval_table_u]/[run_table_u].  Step with the [_nil]/[_cons] equations. *)
Definition eval_ruleset_u_step (fuel : nat)
    (acc : option verdict * (env * packet))
    (cb : list (String.string * chain) * chain)
  : option verdict * (env * packet) :=
  match acc with
  | (Some v, s) => (Some v, s)
  | (None, (e, p)) =>
      match eval_table_u fuel (fst cb) (snd cb) e p with
      | (v, s) => if base_continues v then (None, s) else (Some v, s)
      end
  end.

Definition eval_ruleset_u (fuel : nat)
    (bases : list (list (String.string * chain) * chain)) (e : env) (p : packet)
  : verdict * (env * packet) :=
  match fold_left (eval_ruleset_u_step fuel) bases (None, (e, p)) with
  | (Some v, s) => (v, s)
  | (None, s) => (Accept, s)
  end.

Arguments eval_ruleset_u : simpl never.

Lemma eval_ruleset_u_settled : forall fuel bases v s,
  fold_left (eval_ruleset_u_step fuel) bases (Some v, s) = (Some v, s).
Proof.
  intros fuel bases; induction bases as [| cb bases IH]; intros v s;
    [reflexivity | apply IH].
Qed.

Lemma eval_ruleset_u_nil : forall fuel e p,
  eval_ruleset_u fuel [] e p = (Accept, (e, p)).
Proof. reflexivity. Qed.

Lemma eval_ruleset_u_cons : forall fuel cs base rest e p,
  eval_ruleset_u fuel ((cs, base) :: rest) e p
  = match eval_table_u fuel cs base e p with
    | (v, (e', p')) =>
        if base_continues v then eval_ruleset_u fuel rest e' p' else (v, (e', p'))
    end.
Proof.
  intros fuel cs base rest e p. unfold eval_ruleset_u.
  cbn [fold_left]. unfold eval_ruleset_u_step at 2. cbn [fst snd].
  destruct (eval_table_u fuel cs base e p) as [v [e' p']].
  destruct (base_continues v) eqn:Hv.
  - reflexivity.
  - now rewrite eval_ruleset_u_settled.
Qed.

Definition run_ruleset_u_step (fuel : nat)
    (acc : option verdict * (env * packet))
    (cb : list (String.string * program) * (program * verdict))
  : option verdict * (env * packet) :=
  match acc with
  | (Some v, s) => (Some v, s)
  | (None, (e, p)) =>
      match run_table_u fuel (fst cb) (fst (snd cb)) (snd (snd cb)) e p with
      | (v, s) => if base_continues v then (None, s) else (Some v, s)
      end
  end.

Definition run_ruleset_u (fuel : nat)
    (bases : list (list (String.string * program) * (program * verdict)))
    (e : env) (p : packet) : verdict * (env * packet) :=
  match fold_left (run_ruleset_u_step fuel) bases (None, (e, p)) with
  | (Some v, s) => (v, s)
  | (None, s) => (Accept, s)
  end.

Arguments run_ruleset_u : simpl never.

Lemma run_ruleset_u_settled : forall fuel bases v s,
  fold_left (run_ruleset_u_step fuel) bases (Some v, s) = (Some v, s).
Proof.
  intros fuel bases; induction bases as [| cb bases IH]; intros v s;
    [reflexivity | apply IH].
Qed.

Lemma run_ruleset_u_nil : forall fuel e p,
  run_ruleset_u fuel [] e p = (Accept, (e, p)).
Proof. reflexivity. Qed.

Lemma run_ruleset_u_cons : forall fuel cs base policy rest e p,
  run_ruleset_u fuel ((cs, (base, policy)) :: rest) e p
  = match run_table_u fuel cs base policy e p with
    | (v, (e', p')) =>
        if base_continues v then run_ruleset_u fuel rest e' p' else (v, (e', p'))
    end.
Proof.
  intros fuel cs base policy rest e p. unfold run_ruleset_u.
  cbn [fold_left]. unfold run_ruleset_u_step at 2. cbn [fst snd].
  destruct (run_table_u fuel cs base policy e p) as [v [e' p']].
  destruct (base_continues v) eqn:Hv.
  - reflexivity.
  - now rewrite run_ruleset_u_settled.
Qed.

(** Hook dispatch (same selection/ordering as [eval_hook]). *)
Definition eval_hook_u (fuel : nat) (rs : list hooked_chain)
                       (e : env) (p : packet) : verdict * (env * packet) :=
  eval_ruleset_u fuel (select_hook rs h) e p.

(** Cross-packet env carry at a hook: the per-packet evaluator whose env output
    [seq_eval_env] threads into the next packet — the shared set/map/limiter
    state persists, the per-packet meta/ct fields are local to each packet
    (exactly [eval_chain_mut_env]'s discipline, now with jumps and multi-chain
    dispatch inside the per-packet run). *)
Definition eval_hook_env_u (fuel : nat) (rs : list hooked_chain)
                           (e : env) (p : packet) : verdict * env :=
  let '(v, s) := eval_hook_u fuel rs e p in (v, fst s).

Definition run_ruleset_env_u (fuel : nat)
    (bases : list (list (String.string * program) * (program * verdict)))
    (e : env) (p : packet) : verdict * env :=
  let '(v, s) := run_ruleset_u fuel bases e p in (v, fst s).

(* ------------------------------------------------------------------ *)
(** *** Projection 1: the pure jump strand, licensed on WRITE-FREE rules.

    A rule is [rule_writefree] when it writes NO state at all — which since
    the in-fold limiter fix is exactly [rule_mutfree]: no mutating statement
    (meta/ct set, dynset, notrack) and no limiter/quota/connlimit match
    (whose bucket consumption is an env write) anywhere.  On such a rule the
    per-rule fold IS the historical loadability-guarded pure verdict and
    leaves the state untouched
    ([rule_step_mutfree]); lifted through the traversal, the pure jump
    strand [eval_rules_j]/[eval_table] is exactly the verdict projection of
    the unified fold ([eval_rules_u_writefree]/[eval_table_u_writefree]) —
    the coincidence equation that licenses it as a projection, not an
    independent semantics.  A rule OUTSIDE this domain must be evaluated by
    the unified fold (Regression/Setread_UnderJump.v pins a witness where the
    two genuinely differ, and its [rule_writefree] check is [false]). *)

Definition rule_writefree (r : rule) : bool := rule_mutfree r.

Definition chains_writefree (cs : list (String.string * chain)) : bool :=
  forallb (fun nc => forallb rule_writefree (c_rules (snd nc))) cs.

Lemma rule_step_writefree : forall r e p,
  rule_writefree r = true ->
  rule_step r e p
  = ((if rule_loadable r e p && rule_applies r e p then outcome r e p else None),
     (e, p)).
Proof. intros r e p H. exact (rule_step_mutfree r e p H). Qed.

Lemma chains_writefree_lookup : forall cs n ch,
  chains_writefree cs = true ->
  chain_lookup cs n = Some ch ->
  forallb rule_writefree (c_rules ch) = true.
Proof.
  intros cs n ch Hcs Hlk.
  apply chain_lookup_in in Hlk.
  unfold chains_writefree in Hcs.
  eapply forallb_forall in Hcs; [| exact Hlk]. exact Hcs.
Qed.

Theorem eval_rules_u_writefree : forall fuel cs rs e p,
  forallb rule_writefree rs = true ->
  chains_writefree cs = true ->
  eval_rules_u fuel cs rs e p = (eval_rules_j fuel cs rs e p, (e, p)).
Proof.
  induction fuel as [| f IH]; intros cs rs e p Hrs Hcs; [reflexivity|].
  destruct rs as [| r rest]; [reflexivity|].
  cbn [forallb] in Hrs. apply Bool.andb_true_iff in Hrs. destruct Hrs as [Hr Hrest].
  rewrite eval_rules_j_S. cbn [eval_rules_u].
  rewrite (rule_step_writefree r e p Hr).
  destruct (rule_loadable r e p && rule_applies r e p); [| now apply IH].
  destruct (outcome r e p) as [v|]; [| now apply IH].
  destruct v as [ | | | tc cc | lo hi bp fo | n | n | ];
    try reflexivity; try (now apply IH).
  - (* Jump *)
    destruct (chain_lookup cs n) as [ch|] eqn:Hlk; [| now apply IH].
    rewrite (IH cs (c_rules ch) e p (chains_writefree_lookup cs n ch Hcs Hlk) Hcs).
    destruct (eval_rules_j f cs (c_rules ch) e p); [reflexivity | now apply IH].
  - (* Goto *)
    destruct (chain_lookup cs n) as [ch|] eqn:Hlk; [| reflexivity].
    apply IH; [eapply chains_writefree_lookup; eauto | exact Hcs].
Qed.

Corollary eval_table_u_writefree : forall fuel cs base e p,
  forallb rule_writefree (c_rules base) = true ->
  chains_writefree cs = true ->
  eval_table_u fuel cs base e p = (eval_table fuel cs base e p, (e, p)).
Proof.
  intros fuel cs base e p Hb Hcs. unfold eval_table_u, eval_table.
  rewrite (eval_rules_u_writefree fuel cs (c_rules base) e p Hb Hcs).
  destruct (eval_rules_j fuel cs (c_rules base) e p); reflexivity.
Qed.

Definition bases_writefree
    (bases : list (list (String.string * chain) * chain)) : bool :=
  forallb (fun cb => chains_writefree (fst cb)
                     && forallb rule_writefree (c_rules (snd cb))) bases.

Corollary eval_ruleset_u_writefree : forall fuel bases e p,
  bases_writefree bases = true ->
  eval_ruleset_u fuel bases e p = (eval_ruleset fuel bases e p, (e, p)).
Proof.
  intros fuel bases. induction bases as [| [cs base] rest IHb]; intros e p Hwf;
    [reflexivity|].
  cbn [bases_writefree forallb] in Hwf. apply Bool.andb_true_iff in Hwf.
  destruct Hwf as [Hhd Hrest]. apply Bool.andb_true_iff in Hhd.
  destruct Hhd as [Hcs Hb]. cbn [fst snd] in Hcs, Hb.
  rewrite eval_ruleset_u_cons, eval_ruleset_cons. cbv zeta.
  rewrite (eval_table_u_writefree fuel cs base e p Hb Hcs).
  cbv beta iota.
  destruct (base_continues (eval_table fuel cs base e p)); [now apply IHb | reflexivity].
Qed.

Corollary eval_hook_u_writefree : forall fuel rs e p,
  bases_writefree (select_hook rs h) = true ->
  eval_hook_u fuel rs e p = (eval_hook fuel rs h e p, (e, p)).
Proof.
  intros fuel rs e p Hwf. unfold eval_hook_u, eval_hook.
  now apply eval_ruleset_u_writefree.
Qed.

(* ------------------------------------------------------------------ *)
(** *** Projection 1b: the LIMITER-TOLERANT license for the pure jump strand.

    [eval_rules_u_writefree] licenses the pure strand only on fully
    write-free configs — a single `limit rate 5/second` anywhere voids it,
    even though that limiter's bucket write provably cannot change any
    verdict when no later read observes the depleted bucket.  This section
    proves that stronger license: on configs whose ONLY state writes are the
    bucket consumptions of tolerable limiter matches sitting in
    match-only, terminal-outcome rules ([rule_one_limiter]), the pure jump
    strand [eval_rules_j]/[eval_table] computes exactly the unified
    evaluator's VERDICT — at every fuel, env and packet; jumps, gotos and
    chain re-entries included.  (Only the verdict projection: the unified
    run's final state genuinely differs — the bucket IS depleted.)

    Why the side conditions are the honest boundary, not a convenience:
    - NON-INVERTED limit/quota ([match_limiter_tol]): an inverted limiter
      (`limit rate over ...`) that BREAKs its rule has just PASSED its token
      check, so the consumption genuinely depletes the bucket; a revisit of
      the same rule (two jumps to its chain, or a vmap looping under an
      adversarial env) could then flip the check where the pure strand —
      which reads the entry env — would not.  A NON-inverted limiter that
      breaks stores back its capped level: the bucket stays exhausted and
      every revisit agrees.  `connlimit` consumption is the idempotent
      insert of THIS packet's flow, so its count never changes within a
      traversal and any invert bit is tolerable.
    - TERMINAL static outcome ([terminal (r_verdict r)]): when the limiter
      check passes, the rule's verdict ends the whole traversal, so the
      consumption it just performed is unobservable by later reads.
    - MATCH-ONLY body: every other item of the rule is a consume-free match
      (no statement), so the rule writes nothing but its one bucket.
    The router config's `icmp ... limit rate 5/second accept` rule is
    exactly this shape; the Examples/Router_*.v files instantiate the
    license by [vm_compute] ([Router_Input.inbound_licensed] etc.). *)

(** The env with its three consumable (limit-family) components replaced —
    the normal form every state a limiter-tolerant traversal can reach has
    over its entry env.  Every OTHER component is untouched, which is what
    the congruence lemmas below exploit. *)
Definition env_upd_limits (e : env) (lf : limit_spec -> nat)
    (qf : quota_spec -> nat) (cf : connlimit_spec -> list data) : env :=
  with_e_limit (with_e_quota (with_e_connlimit e cf) qf) lf.

Lemma env_upd_limits_self : forall e,
  env_upd_limits e (e_limit e) (e_quota e) (e_connlimit e) = e.
Proof. intro e. destruct e. reflexivity. Qed.

(** Every load reads the env ONLY through its non-consumable components. *)
Lemma do_load_upd_limits : forall ld e lf qf cf p,
  do_load ld (env_upd_limits e lf qf cf) p = do_load ld e p.
Proof. intros ld e lf qf cf p. destruct ld; reflexivity. Qed.

Lemma field_value_upd_limits : forall f e lf qf cf p,
  field_value f (env_upd_limits e lf qf cf) p = field_value f e p.
Proof. intros. apply do_load_upd_limits. Qed.

Lemma map_field_value_upd_limits : forall fs e lf qf cf p,
  map (fun f => field_value f (env_upd_limits e lf qf cf) p) fs
  = map (fun f => field_value f e p) fs.
Proof. intros. apply map_ext. intro f. apply field_value_upd_limits. Qed.

(** A consume-free match reads NO consumable component: its evaluation is
    invariant under any limit/quota/connlimit replacement. *)
Lemma eval_matchcond_body_upd_limits : forall m e lf qf cf p,
  match_consumefree m = true ->
  eval_matchcond_body m (env_upd_limits e lf qf cf) p = eval_matchcond_body m e p.
Proof.
  intros m e lf qf cf p Hcf.
  destruct m; try discriminate Hcf; cbn [eval_matchcond_body];
    rewrite ?field_value_upd_limits, ?map_field_value_upd_limits;
    try reflexivity;
    (* transformed per-element loads (MConcatSetT) *)
    (f_equal; f_equal; apply map_ext; intro fe; now rewrite field_value_upd_limits).
Qed.

Lemma eval_matchcond_upd_limits : forall m e lf qf cf p,
  match_consumefree m = true ->
  eval_matchcond m (env_upd_limits e lf qf cf) p = eval_matchcond m e p.
Proof.
  intros. unfold eval_matchcond.
  now rewrite (eval_matchcond_body_upd_limits m e lf qf cf p).
Qed.

Lemma rule_applies_walk_upd_limits : forall body e lf qf cf p,
  forallb body_item_mutfree body = true ->
  rule_applies_walk body (env_upd_limits e lf qf cf) p = rule_applies_walk body e p.
Proof.
  induction body as [| it body IH]; intros e lf qf cf p H; [reflexivity|].
  cbn [forallb] in H. apply Bool.andb_true_iff in H. destruct H as [Hit Hb].
  destruct it as [m | s].
  - cbn [rule_applies_walk].
    now rewrite (eval_matchcond_upd_limits m e lf qf cf p Hit), (IH e lf qf cf p Hb).
  - destruct s; cbn [body_item_mutfree is_mut_stmt negb] in Hit; try discriminate Hit;
      cbn [rule_applies_walk]; try (apply IH; exact Hb).
    (* SSynproxy *)
    destruct (synproxy_stops p); [reflexivity | apply IH; exact Hb].
Qed.

Lemma nat_map_key_upd_limits : forall fields ts e lf qf cf p,
  nat_map_key fields ts (env_upd_limits e lf qf cf) p = nat_map_key fields ts e p.
Proof.
  intros. unfold nat_map_key. destruct fields as [| f0 frest]; [reflexivity|].
  now rewrite field_value_upd_limits, map_field_value_upd_limits.
Qed.

Lemma terminal_loadable_upd_limits : forall r e lf qf cf p,
  terminal_loadable r (env_upd_limits e lf qf cf) p = terminal_loadable r e p.
Proof.
  intros. unfold terminal_loadable.
  destruct (r_nat r) as [n|]; [| reflexivity].
  destruct (nat_src n) as [vs|]; [reflexivity|].
  destruct (nat_map n) as [[[fields ts] name]|]; [| reflexivity].
  now rewrite nat_map_key_upd_limits.
Qed.

Lemma tail_loadable_upd_limits : forall r e lf qf cf p,
  tail_loadable r (env_upd_limits e lf qf cf) p = tail_loadable r e p.
Proof.
  intros. unfold tail_loadable. now rewrite terminal_loadable_upd_limits.
Qed.

Lemma end_loadable_upd_limits : forall r e lf qf cf p,
  end_loadable r (env_upd_limits e lf qf cf) p = end_loadable r e p.
Proof.
  intros. unfold end_loadable.
  destruct (r_vmap r) as [vm|]; [| apply tail_loadable_upd_limits].
  cbv zeta. destruct (vm_keyf vm) as [[f ts]|];
    rewrite ?field_value_upd_limits, ?map_field_value_upd_limits;
    change (e_vmap (env_upd_limits e lf qf cf)) with (e_vmap e);
    destruct (assoc_verdict _ (e_vmap e (vm_name vm)));
    rewrite ?tail_loadable_upd_limits; reflexivity.
Qed.

Lemma outcome_core_upd_limits : forall r e lf qf cf p,
  outcome_core r (env_upd_limits e lf qf cf) p = outcome_core r e p.
Proof.
  intros. unfold outcome_core.
  destruct (r_vmap r) as [vm|]; [| reflexivity].
  cbv zeta. destruct (vm_keyf vm) as [[f ts]|];
    rewrite ?field_value_upd_limits, ?map_field_value_upd_limits;
    change (e_vmap (env_upd_limits e lf qf cf)) with (e_vmap e);
    destruct (assoc_verdict _ (e_vmap e (vm_name vm))); reflexivity.
Qed.

Lemma outcome_upd_limits : forall r e lf qf cf p,
  outcome r (env_upd_limits e lf qf cf) p = outcome r e p.
Proof.
  intros. unfold outcome.
  destruct (body_synproxy_stops (r_body r) p); [reflexivity|].
  apply outcome_core_upd_limits.
Qed.

Lemma rule_loadable_upd_limits : forall r e lf qf cf p,
  rule_loadable r (env_upd_limits e lf qf cf) p = rule_loadable r e p.
Proof.
  intros. unfold rule_loadable.
  destruct (body_synproxy_stops (r_body r) p); [reflexivity|].
  now rewrite end_loadable_upd_limits.
Qed.

Lemma rule_applies_upd_limits : forall r e lf qf cf p,
  rule_mutfree r = true ->
  rule_applies r (env_upd_limits e lf qf cf) p = rule_applies r e p.
Proof.
  intros r e lf qf cf p H. unfold rule_mutfree in H.
  apply Bool.andb_true_iff in H. destruct H as [H _].
  apply Bool.andb_true_iff in H. destruct H as [Hb _].
  apply rule_applies_walk_upd_limits. exact Hb.
Qed.

(** Structural spec equality decides real equality (the specs are records of
    nats/bools), so an eqb-keyed bucket update hits exactly one spec. *)
Lemma limit_eqb_eq : forall a b, limit_eqb a b = true -> a = b.
Proof.
  intros a b H. unfold limit_eqb in H.
  apply Bool.andb_true_iff in H; destruct H as [H1 H].
  apply Bool.andb_true_iff in H; destruct H as [H2 H].
  apply Bool.andb_true_iff in H; destruct H as [H3 H].
  apply Bool.andb_true_iff in H; destruct H as [H4 H5].
  apply Nat.eqb_eq in H1, H2, H3, H5. apply Bool.eqb_prop in H4.
  destruct a, b; cbn in *; congruence.
Qed.

Lemma limit_eqb_refl : forall a, limit_eqb a a = true.
Proof.
  intro a. unfold limit_eqb.
  now rewrite !Nat.eqb_refl, Bool.eqb_reflx.
Qed.

Lemma quota_eqb_eq : forall a b, quota_eqb a b = true -> a = b.
Proof.
  intros a b H. unfold quota_eqb in H.
  apply Bool.andb_true_iff in H; destruct H as [H1 H].
  apply Bool.andb_true_iff in H; destruct H as [H2 H3].
  apply Nat.eqb_eq in H1, H2, H3.
  destruct a, b; cbn in *; congruence.
Qed.

Lemma quota_eqb_refl : forall a, quota_eqb a a = true.
Proof. intro a. unfold quota_eqb. now rewrite !Nat.eqb_refl. Qed.

Lemma connlimit_eqb_eq : forall a b, connlimit_eqb a b = true -> a = b.
Proof.
  intros a b H. unfold connlimit_eqb in H.
  apply Bool.andb_true_iff in H; destruct H as [H1 H2].
  apply Nat.eqb_eq in H1, H2.
  destruct a, b; cbn in *; congruence.
Qed.

Lemma connlimit_eqb_refl : forall a, connlimit_eqb a a = true.
Proof. intro a. unfold connlimit_eqb. now rewrite !Nat.eqb_refl. Qed.

(** The under-tests read exactly one bucket. *)
Lemma lim_under_ext : forall e e' p s,
  e_limit e' s = e_limit e s -> lim_under e' p s = lim_under e p s.
Proof. intros e e' p s H. unfold lim_under, lim_avail. now rewrite H. Qed.

Lemma quota_under_ext : forall e e' p s,
  e_quota e' s = e_quota e s -> quota_under e' p s = quota_under e p s.
Proof. intros e e' p s H. unfold quota_under. now rewrite H. Qed.

Lemma connlimit_under_ext : forall e e' p s,
  e_connlimit e' s = e_connlimit e s -> connlimit_under e' p s = connlimit_under e p s.
Proof.
  intros e e' p s H. unfold connlimit_under, connlimit_count, connlimit_after.
  now rewrite H.
Qed.

(** THE traversal invariant relating the unified run's threaded env [e'] to
    the entry env [e0] the pure strand reads: [e'] differs from [e0] only in
    consumable components, and each touched bucket is EXHAUSTED at both (a
    non-inverted limiter that broke) — so every future read agrees — while
    each connlimit count is unchanged (the insert of THIS packet's flow is
    idempotent). *)
Definition limiter_inv (e0 e' : env) (p : packet) : Prop :=
  (exists lf qf cf, e' = env_upd_limits e0 lf qf cf)
  /\ (forall s, e_limit e' s = e_limit e0 s
        \/ (lim_under e' p s = false /\ lim_under e0 p s = false))
  /\ (forall s, e_quota e' s = e_quota e0 s
        \/ (quota_under e' p s = false /\ quota_under e0 p s = false))
  /\ (forall s, connlimit_under e' p s = connlimit_under e0 p s).

Lemma limiter_inv_refl : forall e p, limiter_inv e e p.
Proof.
  intros e p. split; [| split; [| split]].
  - exists (e_limit e), (e_quota e), (e_connlimit e).
    symmetry. apply env_upd_limits_self.
  - intro s. left. reflexivity.
  - intro s. left. reflexivity.
  - intro s. reflexivity.
Qed.

Lemma limiter_inv_lim_under : forall e0 e' p, limiter_inv e0 e' p ->
  forall s, lim_under e' p s = lim_under e0 p s.
Proof.
  intros e0 e' p Hinv s. destruct Hinv as (_ & HL & _ & _).
  destruct (HL s) as [Heq | [Hf Hf0]].
  - apply lim_under_ext. exact Heq.
  - now rewrite Hf, Hf0.
Qed.

Lemma limiter_inv_quota_under : forall e0 e' p, limiter_inv e0 e' p ->
  forall s, quota_under e' p s = quota_under e0 p s.
Proof.
  intros e0 e' p Hinv s. destruct Hinv as (_ & _ & HQ & _).
  destruct (HQ s) as [Heq | [Hf Hf0]].
  - apply quota_under_ext. exact Heq.
  - now rewrite Hf, Hf0.
Qed.

Lemma limiter_inv_connlimit_under : forall e0 e' p, limiter_inv e0 e' p ->
  forall s, connlimit_under e' p s = connlimit_under e0 p s.
Proof. intros e0 e' p Hinv s. destruct Hinv as (_ & _ & _ & HC). exact (HC s). Qed.

(** EVERY match — consume-free or limiter-family — evaluates identically at
    an invariant-related state and at the entry env. *)
Lemma eval_matchcond_inv : forall m e0 e' p,
  limiter_inv e0 e' p -> eval_matchcond m e' p = eval_matchcond m e0 p.
Proof.
  intros m e0 e' p Hinv.
  destruct (match_consumefree m) eqn:Hcf.
  - destruct Hinv as ((lf & qf & cf & ->) & _).
    apply eval_matchcond_upd_limits. exact Hcf.
  - destruct m; try discriminate Hcf;
      unfold eval_matchcond; cbn [match_loadable eval_matchcond_body andb].
    + now rewrite (limiter_inv_lim_under e0 e' p Hinv).
    + now rewrite (limiter_inv_quota_under e0 e' p Hinv).
    + now rewrite (limiter_inv_connlimit_under e0 e' p Hinv).
Qed.

(** Consuming an EXHAUSTED non-inverted `limit` preserves the invariant: the
    kernel's fail-branch update stores back the capped level, so the bucket
    stays exhausted (and stays exhausted under any number of revisits). *)
Lemma limiter_inv_set_limit : forall e0 e' p s,
  limiter_inv e0 e' p -> lim_under e' p s = false ->
  limiter_inv e0 (set_limit e' p s) p.
Proof.
  intros e0 e' p s Hinv Hf.
  pose proof (limiter_inv_lim_under e0 e' p Hinv s) as Hagree.
  destruct Hinv as ((lf & qf & cf & Heq) & HL & HQ & HC).
  assert (Hself : e_limit (set_limit e' p s) s = lim_avail e' p s).
  { unfold set_limit, env_limit_upd, with_e_limit. cbn [e_limit].
    rewrite limit_eqb_refl. unfold lim_newtokens.
    unfold lim_under in Hf. cbv zeta. now rewrite Hf. }
  assert (Hother : forall s2, limit_eqb s s2 = false ->
            e_limit (set_limit e' p s) s2 = e_limit e' s2).
  { intros s2 E. unfold set_limit, env_limit_upd, with_e_limit. cbn [e_limit].
    now rewrite E. }
  split; [| split; [| split]].
  - subst e'. eexists _, qf, cf. reflexivity.
  - intro s2. destruct (limit_eqb s s2) eqn:E.
    + apply limit_eqb_eq in E. subst s2. right. split.
      * (* the re-capped bucket is still exhausted *)
        unfold lim_under, lim_avail at 1. rewrite Hself.
        rewrite Nat.min_l by (unfold lim_avail; apply Nat.le_min_r).
        unfold lim_under in Hf. exact Hf.
      * congruence.
    + destruct (HL s2) as [Heq2 | [Hf2 Hf02]].
      * left. rewrite (Hother s2 E). exact Heq2.
      * right. split; [| exact Hf02].
        rewrite (lim_under_ext e' (set_limit e' p s) p s2 (Hother s2 E)). exact Hf2.
  - intro s2. exact (HQ s2).
  - intro s2. exact (HC s2).
Qed.

(** Consuming an EXHAUSTED non-inverted `quota` preserves the invariant: the
    unconditional skb->len accumulation only shrinks the remaining bytes. *)
Lemma limiter_inv_set_quota : forall e0 e' p s,
  limiter_inv e0 e' p -> quota_under e' p s = false ->
  limiter_inv e0 (set_quota e' p s) p.
Proof.
  intros e0 e' p s Hinv Hf.
  pose proof (limiter_inv_quota_under e0 e' p Hinv s) as Hagree.
  destruct Hinv as ((lf & qf & cf & Heq) & HL & HQ & HC).
  assert (Hself : e_quota (set_quota e' p s) s = e_quota e' s - quota_cost p).
  { unfold set_quota, env_quota_upd, with_e_quota. cbn [e_quota].
    now rewrite quota_eqb_refl. }
  assert (Hother : forall s2, quota_eqb s s2 = false ->
            e_quota (set_quota e' p s) s2 = e_quota e' s2).
  { intros s2 E. unfold set_quota, env_quota_upd, with_e_quota. cbn [e_quota].
    now rewrite E. }
  split; [| split; [| split]].
  - subst e'. eexists lf, _, cf. reflexivity.
  - intro s2. exact (HL s2).
  - intro s2. destruct (quota_eqb s s2) eqn:E.
    + apply quota_eqb_eq in E. subst s2. right. split.
      * unfold quota_under in *. rewrite Hself.
        apply Nat.leb_gt. apply Nat.leb_gt in Hf. lia.
      * congruence.
    + destruct (HQ s2) as [Heq2 | [Hf2 Hf02]].
      * left. rewrite (Hother s2 E). exact Heq2.
      * right. split; [| exact Hf02].
        rewrite (quota_under_ext e' (set_quota e' p s) p s2 (Hother s2 E)). exact Hf2.
  - intro s2. exact (HC s2).
Qed.

Lemma data_mem_head : forall x l, data_mem x (x :: l) = true.
Proof. intros. unfold data_mem. cbn. now rewrite data_eqb_refl. Qed.

Lemma data_mem_connlimit_after : forall e s fl,
  data_mem fl (connlimit_after e s fl) = true.
Proof.
  intros. unfold connlimit_after.
  destruct (data_mem fl (e_connlimit e s)) eqn:E; [exact E | apply data_mem_head].
Qed.

(** `connlimit` consumption is the idempotent insert of THIS packet's flow:
    it never changes the count any evaluation of THIS traversal reads. *)
Lemma connlimit_under_upd : forall e p s s2,
  connlimit_under (set_connlimit e p s) p s2 = connlimit_under e p s2.
Proof.
  intros e p s s2.
  destruct (connlimit_eqb s s2) eqn:E.
  - apply connlimit_eqb_eq in E. subst s2.
    assert (Hlist : e_connlimit (set_connlimit e p s) s
                    = connlimit_after e s (pkt_flow p)).
    { unfold set_connlimit, env_connlimit_upd, with_e_connlimit. cbn [e_connlimit].
      now rewrite connlimit_eqb_refl. }
    unfold connlimit_under. f_equal. f_equal.
    unfold connlimit_count at 1. unfold connlimit_after at 1. rewrite Hlist.
    now rewrite data_mem_connlimit_after.
  - apply connlimit_under_ext.
    unfold set_connlimit, env_connlimit_upd, with_e_connlimit. cbn [e_connlimit].
    now rewrite E.
Qed.

Lemma limiter_inv_set_connlimit : forall e0 e' p s,
  limiter_inv e0 e' p -> limiter_inv e0 (set_connlimit e' p s) p.
Proof.
  intros e0 e' p s Hinv.
  destruct Hinv as ((lf & qf & cf & Heq) & HL & HQ & HC).
  split; [| split; [| split]].
  - subst e'. eexists lf, qf, _. reflexivity.
  - intro s2. exact (HL s2).
  - intro s2. exact (HQ s2).
  - intro s2. rewrite (connlimit_under_upd e' p s s2). exact (HC s2).
Qed.

(** A TOLERABLE limiter match: non-inverted `limit`/`quota` (an inverted one
    that breaks has just consumed a live bucket — see the section header), or
    any `connlimit` (idempotent within a traversal). *)
Definition match_limiter_tol (m : matchcond) : bool :=
  match m with
  | MLimit s => negb (Nat.eqb (Nat.land (ls_flags s) 1) 1)
  | MQuota s => negb (Nat.eqb (Nat.land (q_flags s) 1) 1)
  | MConnlimit _ => true
  | _ => false
  end.

(** Evaluating (and thus consuming) a tolerable limiter that BREAKS its rule
    preserves the invariant. *)
Lemma limiter_inv_match_consume : forall m e0 e' p,
  limiter_inv e0 e' p -> match_limiter_tol m = true ->
  eval_matchcond m e' p = false ->
  limiter_inv e0 (match_consume m e' p) p.
Proof.
  intros m e0 e' p Hinv Htol Hc.
  destruct m; try discriminate Htol; cbn [match_consume].
  - (* MLimit *)
    apply limiter_inv_set_limit; [exact Hinv|].
    unfold eval_matchcond in Hc. cbn [match_loadable eval_matchcond_body andb] in Hc.
    cbn [match_limiter_tol] in Htol. apply Bool.negb_true_iff in Htol.
    rewrite Htol, Bool.xorb_false_l in Hc. exact Hc.
  - (* MQuota *)
    apply limiter_inv_set_quota; [exact Hinv|].
    unfold eval_matchcond in Hc. cbn [match_loadable eval_matchcond_body andb] in Hc.
    cbn [match_limiter_tol] in Htol. apply Bool.negb_true_iff in Htol.
    rewrite Htol, Bool.xorb_false_l in Hc. exact Hc.
  - (* MConnlimit *)
    apply limiter_inv_set_connlimit. exact Hinv.
Qed.

(** A ONE-LIMITER body: consume-free matches followed by ONE tolerable
    limiter match in the last position — no statements at all (the rule
    writes nothing but that bucket). *)
Fixpoint body_one_limiter (body : list body_item) : bool :=
  match body with
  | BMatch m :: nil => match_limiter_tol m
  | BMatch m :: rest => match_consumefree m && body_one_limiter rest
  | _ => false
  end.

Lemma body_one_limiter_no_synproxy : forall body p,
  body_one_limiter body = true -> body_synproxy_stops body p = false.
Proof.
  induction body as [| it rest IH]; intros p H; [reflexivity|].
  destruct it as [m | s]; [| destruct rest; discriminate H].
  destruct rest as [| it2 rest2]; [reflexivity|].
  cbn [body_one_limiter] in H. apply Bool.andb_true_iff in H. destruct H as [_ H2].
  specialize (IH p H2). unfold body_synproxy_stops in *. cbn [existsb]. exact IH.
Qed.

Lemma body_one_limiter_no_notrack : forall body,
  body_one_limiter body = true -> body_has_notrack body = false.
Proof.
  induction body as [| it rest IH]; intros H; [reflexivity|].
  destruct it as [m | s]; [| destruct rest; discriminate H].
  destruct rest as [| it2 rest2]; [reflexivity|].
  cbn [body_one_limiter] in H. apply Bool.andb_true_iff in H. destruct H as [_ H2].
  specialize (IH H2). unfold body_has_notrack in *. cbn [existsb]. exact IH.
Qed.

Lemma body_one_limiter_applies_loadable : forall body e p,
  body_one_limiter body = true ->
  rule_applies_walk body e p = true -> body_loadable_walk body p = true.
Proof.
  induction body as [| it rest IH]; intros e p H Ha; [reflexivity|].
  destruct it as [m | s]; [| destruct rest; discriminate H].
  cbn [rule_applies_walk] in Ha. apply Bool.andb_true_iff in Ha.
  destruct Ha as [Hm Ha].
  unfold eval_matchcond in Hm. apply Bool.andb_true_iff in Hm. destruct Hm as [Hl _].
  cbn [body_loadable_walk body_item_loadable]. rewrite Hl. cbn [andb].
  destruct rest as [| it2 rest2]; [reflexivity|].
  cbn [body_one_limiter] in H. apply Bool.andb_true_iff in H. destruct H as [_ H2].
  exact (IH e p H2 Ha).
Qed.

(** The body walk of a one-limiter body at an invariant-related state: it
    completes exactly when the pure walk at the ENTRY env applies, and a
    break (which may have consumed the limiter) preserves the invariant. *)
Lemma body_step_one_limiter : forall body e0 e' p,
  limiter_inv e0 e' p -> body_one_limiter body = true ->
  exists e'',
    body_step body e' p
      = (if rule_applies_walk body e0 p then BRdone e'' p else BRbreak e'' p)
    /\ (rule_applies_walk body e0 p = false -> limiter_inv e0 e'' p).
Proof.
  induction body as [| it rest IH]; intros e0 e' p Hinv H; [discriminate H|].
  destruct it as [m | s]; [| destruct rest; discriminate H].
  destruct rest as [| it2 rest2].
  - (* the limiter itself, in last position *)
    cbn [body_one_limiter] in H.
    cbn [body_step rule_applies_walk].
    rewrite (eval_matchcond_inv m e0 e' p Hinv), Bool.andb_true_r.
    exists (match_consume m e' p).
    destruct (eval_matchcond m e0 p) eqn:Hc.
    + split; [reflexivity | intro Hcontr; discriminate Hcontr].
    + split; [reflexivity|]. intros _.
      apply limiter_inv_match_consume; [exact Hinv | exact H |].
      rewrite (eval_matchcond_inv m e0 e' p Hinv). exact Hc.
  - (* a consume-free prefix match *)
    cbn [body_one_limiter] in H. apply Bool.andb_true_iff in H.
    destruct H as [Hm Hrest].
    cbn [body_step rule_applies_walk].
    rewrite (eval_matchcond_inv m e0 e' p Hinv).
    rewrite (match_consume_free_id m e' p Hm).
    destruct (eval_matchcond m e0 p) eqn:Hc.
    + cbn [andb]. apply IH; assumption.
    + cbn [andb]. exists e'. split; [reflexivity | intros _; exact Hinv].
Qed.

(** A ONE-LIMITER rule: a one-limiter body under a STATIC TERMINAL verdict
    (accept/drop/reject/queue — the traversal ends when it fires, so the
    consumption the firing evaluation performed is unobservable). *)
Definition rule_one_limiter (r : rule) : bool :=
  body_one_limiter (r_body r)
  && match r_outcome r with OVerdict v => terminal v | _ => false end.

(** The whole one-limiter rule at an invariant-related state: its step IS
    the pure triple at the ENTRY env, its outcome is a static terminal, and
    a non-firing step preserves the invariant. *)
Lemma rule_step_one_limiter : forall r e0 e' p,
  limiter_inv e0 e' p -> rule_one_limiter r = true ->
  exists e'',
    rule_step r e' p
      = ((if rule_loadable r e0 p && rule_applies r e0 p
          then outcome r e0 p else None),
         (e'', p))
    /\ (rule_loadable r e0 p && rule_applies r e0 p = false ->
        limiter_inv e0 e'' p)
    /\ (exists v, outcome r e0 p = Some v /\ terminal v = true).
Proof.
  intros r e0 e' p Hinv H.
  unfold rule_one_limiter in H. apply Bool.andb_true_iff in H. destruct H as [Hb Ho].
  destruct (r_outcome r) as [v | | | | | | |] eqn:Hout; try discriminate Ho.
  assert (Hsp := body_one_limiter_no_synproxy (r_body r) p Hb).
  assert (Hnt := body_one_limiter_no_notrack (r_body r) Hb).
  assert (Hvm : r_vmap r = None) by (unfold r_vmap; now rewrite Hout).
  assert (Hnat : r_nat r = None) by (unfold r_nat; now rewrite Hout).
  assert (Htp : r_tproxy r = None) by (unfold r_tproxy; now rewrite Hout).
  assert (Hfw : r_fwd r = None) by (unfold r_fwd; now rewrite Hout).
  assert (Hq : r_queue r = None) by (unfold r_queue; now rewrite Hout).
  assert (Hrv : r_verdict r = v) by (unfold r_verdict; now rewrite Hout).
  assert (Hbt : body_thread (r_body r) p = p)
    by (unfold body_thread; now rewrite Hnt).
  assert (Hoc : outcome r e0 p = Some v).
  { unfold outcome. rewrite Hsp, Hbt. unfold outcome_core. rewrite Hvm.
    unfold terminal_outcome. rewrite Hnat, Htp, Hfw, Hq, Hrv.
    destruct v; try reflexivity; discriminate Ho. }
  assert (Hend : forall e2 p2, end_step r e2 p2 = (Some v, (e2, p2))).
  { intros e2 p2. unfold end_step. rewrite Hvm.
    unfold terminal_step, has_effect_terminal.
    rewrite Hnat, Htp, Hfw, Hq, Hrv.
    destruct v; try reflexivity; discriminate Ho. }
  destruct (body_step_one_limiter (r_body r) e0 e' p Hinv Hb) as (e'' & Hbs & Hbinv).
  exists e''.
  unfold rule_step. rewrite Hbs.
  unfold rule_applies.
  destruct (rule_applies_walk (r_body r) e0 p) eqn:Ha.
  - (* the body passes: the terminal fires *)
    rewrite Hend.
    assert (Hld : rule_loadable r e0 p = true).
    { unfold rule_loadable. rewrite Hsp.
      rewrite (body_one_limiter_applies_loadable (r_body r) e0 p Hb Ha).
      cbn [andb]. rewrite Hbt.
      unfold end_loadable. rewrite Hvm. unfold tail_loadable.
      unfold terminal_loadable. rewrite Hnat, Htp, Hfw, Hq.
      unfold terminal_outcome. rewrite Hnat, Htp, Hfw, Hq, Hrv.
      destruct v; try reflexivity; discriminate Ho. }
    rewrite Hld. cbn [andb]. rewrite Hoc.
    split; [reflexivity|]. split.
    + intro Hcontr. discriminate Hcontr.
    + exists v. split; [reflexivity | exact Ho].
  - (* the body breaks (possibly consuming the limiter) *)
    rewrite Bool.andb_false_r.
    split; [reflexivity|]. split.
    + intros _. apply Hbinv. reflexivity.
    + exists v. split; [exact Hoc | exact Ho].
Qed.

(** The write-free pure triple is invariant across the invariant relation. *)
Lemma pure_step_inv : forall r e0 e' p,
  limiter_inv e0 e' p -> rule_mutfree r = true ->
  (if rule_loadable r e' p && rule_applies r e' p then outcome r e' p else None)
  = (if rule_loadable r e0 p && rule_applies r e0 p then outcome r e0 p else None).
Proof.
  intros r e0 e' p Hinv Hmf.
  destruct Hinv as ((lf & qf & cf & ->) & _).
  now rewrite rule_loadable_upd_limits,
              (rule_applies_upd_limits r e0 lf qf cf p Hmf),
              outcome_upd_limits.
Qed.

(** The LIMITER-TOLERANT domain: every rule is write-free OR a one-limiter
    rule.  Checkable by [vm_compute] on a concrete config. *)
Definition rule_limiter_tol (r : rule) : bool :=
  rule_writefree r || rule_one_limiter r.

Definition chains_limiter_tol (cs : list (String.string * chain)) : bool :=
  forallb (fun nc => forallb rule_limiter_tol (c_rules (snd nc))) cs.

Lemma chains_limiter_tol_lookup : forall cs n ch,
  chains_limiter_tol cs = true ->
  chain_lookup cs n = Some ch ->
  forallb rule_limiter_tol (c_rules ch) = true.
Proof.
  intros cs n ch Hcs Hlk. apply chain_lookup_in in Hlk.
  unfold chains_limiter_tol in Hcs.
  eapply forallb_forall in Hcs; [| exact Hlk]. exact Hcs.
Qed.

Lemma eval_rules_u_limiter_tol_aux : forall fuel cs rs e0 e' p,
  limiter_inv e0 e' p ->
  forallb rule_limiter_tol rs = true ->
  chains_limiter_tol cs = true ->
  fst (eval_rules_u fuel cs rs e' p) = eval_rules_j fuel cs rs e0 p
  /\ snd (snd (eval_rules_u fuel cs rs e' p)) = p
  /\ (fst (eval_rules_u fuel cs rs e' p) = None ->
      limiter_inv e0 (fst (snd (eval_rules_u fuel cs rs e' p))) p).
Proof.
  induction fuel as [| f IH]; intros cs rs e0 e' p Hinv Hrs Hcs.
  { cbn. split; [reflexivity | split; [reflexivity | intros _; exact Hinv]]. }
  destruct rs as [| r rest].
  { cbn. split; [reflexivity | split; [reflexivity | intros _; exact Hinv]]. }
  cbn [forallb] in Hrs. apply Bool.andb_true_iff in Hrs. destruct Hrs as [Hr Hrest].
  rewrite eval_rules_j_S. cbn [eval_rules_u].
  destruct (rule_writefree r) eqn:Hwf.
  - (* write-free rule: the fold is the pure triple, congruent to the entry env *)
    rewrite (rule_step_writefree r e' p Hwf).
    rewrite (pure_step_inv r e0 e' p Hinv Hwf).
    destruct (rule_loadable r e0 p && rule_applies r e0 p);
      [| exact (IH cs rest e0 e' p Hinv Hrest Hcs)].
    destruct (outcome r e0 p) as [v|];
      [| exact (IH cs rest e0 e' p Hinv Hrest Hcs)].
    destruct v as [ | | | tc cc | lo hi bp fo | n | n | ];
      try (split; [reflexivity | split; [reflexivity | intro Hc; discriminate Hc]]);
      try (exact (IH cs rest e0 e' p Hinv Hrest Hcs)).
    + (* Jump *)
      destruct (chain_lookup cs n) as [ch|] eqn:Hlk;
        [| exact (IH cs rest e0 e' p Hinv Hrest Hcs)].
      destruct (eval_rules_u f cs (c_rules ch) e' p) as [ov [e1 p1]] eqn:E1.
      pose proof (IH cs (c_rules ch) e0 e' p Hinv
                    (chains_limiter_tol_lookup cs n ch Hcs Hlk) Hcs) as IH1.
      rewrite E1 in IH1. cbn [fst snd] in IH1.
      destruct IH1 as (IHv & IHp & IHinv).
      rewrite <- IHv. subst p1.
      destruct ov as [w|].
      * split; [reflexivity | split; [reflexivity | intro Hc; discriminate Hc]].
      * exact (IH cs rest e0 e1 p (IHinv eq_refl) Hrest Hcs).
    + (* Goto *)
      destruct (chain_lookup cs n) as [ch|] eqn:Hlk.
      * exact (IH cs (c_rules ch) e0 e' p Hinv
                 (chains_limiter_tol_lookup cs n ch Hcs Hlk) Hcs).
      * split; [reflexivity | split; [reflexivity | intros _; exact Hinv]].
    + (* Return *)
      split; [reflexivity | split; [reflexivity | intros _; exact Hinv]].
  - (* one-limiter rule *)
    assert (Hol : rule_one_limiter r = true).
    { unfold rule_limiter_tol in Hr. rewrite Hwf in Hr. exact Hr. }
    destruct (rule_step_one_limiter r e0 e' p Hinv Hol)
      as (e'' & Hstep & Hinv'' & (v & Hoc & Hterm)).
    rewrite Hstep.
    destruct (rule_loadable r e0 p && rule_applies r e0 p) eqn:Hg;
      [| exact (IH cs rest e0 e'' p (Hinv'' eq_refl) Hrest Hcs)].
    rewrite Hoc.
    destruct v; try discriminate Hterm;
      split; [reflexivity | split; [reflexivity | intro Hc; discriminate Hc]
             |reflexivity | split; [reflexivity | intro Hc; discriminate Hc]
             |reflexivity | split; [reflexivity | intro Hc; discriminate Hc]
             |reflexivity | split; [reflexivity | intro Hc; discriminate Hc]].
Qed.

(** THE limiter-tolerant license: on a limiter-tolerant config the pure jump
    strand is the VERDICT projection of the unified fold — every fuel, env,
    packet; jumps and re-entries included. *)
Theorem eval_rules_u_limiter_tolerant : forall fuel cs rs e p,
  forallb rule_limiter_tol rs = true ->
  chains_limiter_tol cs = true ->
  fst (eval_rules_u fuel cs rs e p) = eval_rules_j fuel cs rs e p.
Proof.
  intros fuel cs rs e p Hrs Hcs.
  exact (proj1 (eval_rules_u_limiter_tol_aux fuel cs rs e e p
                  (limiter_inv_refl e p) Hrs Hcs)).
Qed.

Corollary eval_table_u_limiter_tolerant : forall fuel cs base e p,
  forallb rule_limiter_tol (c_rules base) = true ->
  chains_limiter_tol cs = true ->
  fst (eval_table_u fuel cs base e p) = eval_table fuel cs base e p.
Proof.
  intros fuel cs base e p Hb Hcs.
  unfold eval_table_u, eval_table.
  pose proof (eval_rules_u_limiter_tolerant fuel cs (c_rules base) e p Hb Hcs) as Hv.
  destruct (eval_rules_u fuel cs (c_rules base) e p) as [[v|] s];
    cbn [fst] in Hv; rewrite <- Hv; reflexivity.
Qed.

(** Hook form for a hook with ONE registered base chain (the common case; a
    multi-base hook would additionally thread a fired limiter's depletion
    from one base into the next, where the pure strand cannot follow). *)
Corollary eval_hook_u_limiter_tolerant_1 : forall fuel rs cs base e p,
  select_hook rs h = [(cs, base)] ->
  forallb rule_limiter_tol (c_rules base) = true ->
  chains_limiter_tol cs = true ->
  fst (eval_hook_u fuel rs e p) = eval_hook fuel rs h e p.
Proof.
  intros fuel rs cs base e p Hsel Hb Hcs.
  unfold eval_hook_u, eval_hook. rewrite Hsel.
  rewrite eval_ruleset_u_cons, eval_ruleset_cons.
  pose proof (eval_table_u_limiter_tolerant fuel cs base e p Hb Hcs) as Hv.
  destruct (eval_table_u fuel cs base e p) as [v [e1 p1]].
  cbn [fst] in Hv. subst v. cbv zeta.
  destruct (base_continues (eval_table fuel cs base e p)); reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** *** Projection 2: the flat mutation strand, licensed on TRANSFER-FREE
    rules.

    [eval_rules_mut]/[eval_rules_mut_env] thread the same per-rule fold but
    follow no control transfers (a realised Jump/Goto is a fall-through,
    a Return does not pop).  They are the projection of the unified fold on
    rules that can realise NO transfer verdict: [rule_plain] — every static
    verdict and every verdict-map entry (under the run's verdict maps) is
    non-Jump/Goto/Return.  Because nothing a rule writes can change a verdict
    map ([rule_step_vmap]: [e_vmap] is invariant under the fold — dynset
    writes named SETS and value MAPS, not verdict maps), the hypothesis is
    checkable once at the ENTRY env and transports itself along the run; this
    is the step-threaded faithful-domain predicate the mutation strand
    previously could not state. *)

Definition verdict_plain (v : verdict) : bool :=
  match v with Jump _ | Goto _ | Return => false | _ => true end.

Definition rule_plain (e : env) (r : rule) : bool :=
  match r_outcome r with
  | OVerdict v => verdict_plain v
  | OVmap s | OVmapNat s _ =>
      forallb (fun ent => verdict_plain (snd ent)) (e_vmap e (vm_name s))
  | _ => true
  end.

(** [rule_plain] reads the env ONLY through its verdict maps. *)
Lemma rule_plain_vmap_ext : forall e e' r,
  e_vmap e' = e_vmap e -> rule_plain e' r = rule_plain e r.
Proof.
  intros e e' r Hv. unfold rule_plain.
  destruct (r_outcome r); try reflexivity; now rewrite Hv.
Qed.

(** No env write of the per-rule fold touches a verdict map: every writer
    ([env_set_upd]/[env_map_upd]/[set_ct]/the limiter sweeps) copies [e_vmap]
    verbatim. *)
Lemma e_vmap_env_set_upd : forall e op n k, e_vmap (env_set_upd e op n k) = e_vmap e.
Proof. reflexivity. Qed.
Lemma e_vmap_env_map_upd : forall e op n k d, e_vmap (env_map_upd e op n k d) = e_vmap e.
Proof. reflexivity. Qed.
Lemma e_vmap_set_ct : forall e p k v, e_vmap (set_ct e p k v) = e_vmap e.
Proof. intros. unfold set_ct. destruct (pkt_ct_present p); reflexivity. Qed.
Lemma e_vmap_set_limit : forall e p s, e_vmap (set_limit e p s) = e_vmap e.
Proof. reflexivity. Qed.
Lemma e_vmap_set_quota : forall e p s, e_vmap (set_quota e p s) = e_vmap e.
Proof. reflexivity. Qed.
Lemma e_vmap_set_connlimit : forall e p s, e_vmap (set_connlimit e p s) = e_vmap e.
Proof. reflexivity. Qed.

Lemma body_step_vmap : forall body e p,
  e_vmap (fst (body_res_state (body_step body e p))) = e_vmap e.
Proof.
  induction body as [| it body IH]; intros e p; [reflexivity|].
  destruct it as [m | s].
  - cbn [body_step].
    assert (Hmc : e_vmap (match_consume m e p) = e_vmap e)
      by (destruct m; reflexivity).
    destruct (eval_matchcond m e p);
      [rewrite IH; exact Hmc | cbn [body_res_state fst]; exact Hmc].
  - destruct s; cbn [body_step];
      repeat first
        [ match goal with
          | |- context [match ?l with nil => _ | cons _ _ => _ end] =>
              is_var l; destruct l; cbn [body_step]
          end
        | match goal with
          | |- context [if ?b then _ else _] => destruct b
          end ];
      cbn [body_res_state fst];
      rewrite ?IH; rewrite ?e_vmap_set_ct, ?e_vmap_env_set_upd, ?e_vmap_env_map_upd;
      reflexivity.
Qed.

Lemma after_step_vmap : forall ss e p,
  e_vmap (fst (snd (after_step ss e p))) = e_vmap e.
Proof.
  induction ss as [| s ss IH]; intros e p; [reflexivity|].
  destruct s; cbn [after_step];
    repeat first
      [ match goal with
        | |- context [match ?l with nil => _ | cons _ _ => _ end] =>
            is_var l; destruct l; cbn [after_step]
        end
      | match goal with
        | |- context [if ?b then _ else _] => destruct b
        end ];
    cbn [fst snd];
    rewrite ?IH; rewrite ?e_vmap_set_ct, ?e_vmap_env_set_upd, ?e_vmap_env_map_upd;
    reflexivity.
Qed.

(** The NAT effect never touches the verdict-map environment: its env write is
    the flow-keyed [e_nat] store only. *)
Lemma e_vmap_apply_nat_c : forall h' k fam opnd port e p,
  e_vmap (fst (apply_nat_c h' k fam opnd port e p)) = e_vmap e.
Proof.
  intros h' k fam opnd port e p. unfold apply_nat_c. cbv zeta.
  destruct (e_nat e (pkt_flow p)); [reflexivity|].
  destruct (pkt_ctdir_orig p); reflexivity.
Qed.

Lemma terminal_step_vmap : forall r e p,
  e_vmap (fst (snd (terminal_step r e p))) = e_vmap e.
Proof.
  intros r e p. unfold terminal_step.
  destruct (has_effect_terminal r).
  - destruct (terminal_loadable r e p); [|reflexivity].
    destruct (nat_drops h r e p); [reflexivity|].
    cbn [fst snd]. unfold apply_nat.
    destruct (r_nat r) as [ns|]; [apply e_vmap_apply_nat_c | reflexivity].
  - destruct (r_verdict r); try reflexivity. apply after_step_vmap.
Qed.

Lemma end_step_vmap : forall r e p,
  e_vmap (fst (snd (end_step r e p))) = e_vmap e.
Proof.
  intros r e p. unfold end_step.
  destruct (r_vmap r) as [vm|]; [| apply terminal_step_vmap].
  destruct (vmap_loadable (Some vm) p); [| reflexivity]. cbv zeta.
  destruct (vm_keyf vm) as [[f ts]|];
    destruct (assoc_verdict _ (e_vmap e (vm_name vm)));
    solve [reflexivity | apply terminal_step_vmap].
Qed.

Lemma rule_step_vmap : forall r e p,
  e_vmap (fst (snd (rule_step r e p))) = e_vmap e.
Proof.
  intros r e p. unfold rule_step.
  pose proof (body_step_vmap (r_body r) e p) as Hb.
  destruct (body_step (r_body r) e p) as [e' p' | e' p' | e' p'];
    cbn [body_res_state fst] in Hb; cbn [fst snd]; try exact Hb.
  rewrite (end_step_vmap r e' p'). exact Hb.
Qed.

(** Every verdict [after_step] itself produces is the synproxy [Drop]. *)
Lemma after_step_verdict_drop : forall ss e p v,
  fst (after_step ss e p) = Some v -> v = Drop.
Proof.
  induction ss as [| s ss IH]; intros e p v H; [discriminate H|].
  destruct s; cbn [after_step] in H;
    repeat first
      [ match type of H with
        | context [match ?l with nil => _ | cons _ _ => _ end] =>
            is_var l; destruct l; cbn [after_step] in H
        end
      | match type of H with
        | context [if ?b then _ else _] => destruct b
        end ];
    cbn [fst] in H;
    solve [ eapply IH; exact H
          | discriminate H
          | injection H as H; congruence ].
Qed.

(** Fold-level transfer-freedom: a [rule_plain] rule's step verdict is never a
    control transfer — at ANY state whose verdict maps agree with the env the
    predicate was checked at. *)
Lemma rule_step_plain : forall e r,
  rule_plain e r = true ->
  forall e' p v, e_vmap e' = e_vmap e ->
  fst (rule_step r e' p) = Some v ->
  verdict_plain v = true.
Proof.
  intros e r Hpl e' p v Hvm.
  unfold rule_step.
  pose proof (body_step_vmap (r_body r) e' p) as Hbvm.
  destruct (body_step (r_body r) e' p) as [e2 p2 | e2 p2 | e2 p2] eqn:Hb;
    rewrite ?Hb in Hbvm; cbn [body_res_state fst] in Hbvm; cbn [fst].
  - intro Hstep. discriminate Hstep.
  - intro Hstep. injection Hstep as <-. reflexivity.
  - (* BRdone: the end runs at (e2, p2), whose verdict maps are the entry's *)
    assert (Hvm2 : e_vmap e2 = e_vmap e) by congruence.
    unfold rule_plain in Hpl.
    unfold end_step, terminal_step, has_effect_terminal,
           r_vmap, r_nat, r_tproxy, r_fwd, r_queue, r_verdict.
    destruct (r_outcome r) as [ w | | s | s ns | ns | ts | fs | qs ] eqn:Ho;
      cbn [fst].
    + (* OVerdict w *)
      destruct w; cbn;
        try (intro Hstep; injection Hstep as <-; reflexivity);
        try discriminate Hpl.
      (* Continue: falls through to the after-statements *)
      intro Hstep. apply after_step_verdict_drop in Hstep. now subst v.
    + (* ONone *)
      intro Hstep. apply after_step_verdict_drop in Hstep. now subst v.
    + (* OVmap *)
      destruct (vmap_loadable (Some s) p2); [| intro Hstep; discriminate Hstep].
      cbv zeta. rewrite Hvm2.
      destruct (vm_keyf s) as [[f ts]|]; cbv iota;
        (destruct (assoc_verdict _ (e_vmap e (vm_name s))) as [w|] eqn:Ha;
         [ intro Hstep; injection Hstep as <-;
           apply assoc_verdict_in in Ha; destruct Ha as (lo & hi & Hin);
           eapply forallb_forall in Hpl; [| exact Hin]; exact Hpl
         | intro Hstep; apply after_step_verdict_drop in Hstep; now subst v ]).
    + (* OVmapNat *)
      destruct (vmap_loadable (Some s) p2); [| intro Hstep; discriminate Hstep].
      cbv zeta. rewrite Hvm2.
      destruct (vm_keyf s) as [[f ts]|]; cbv iota;
        (destruct (assoc_verdict _ (e_vmap e (vm_name s))) as [w|] eqn:Ha;
         [ intro Hstep; injection Hstep as <-;
           apply assoc_verdict_in in Ha; destruct Ha as (lo & hi & Hin);
           eapply forallb_forall in Hpl; [| exact Hin]; exact Hpl
         | destruct (terminal_loadable r e2 p2);
           [destruct (nat_drops h r e2 p2)|]; intro Hstep;
           [now injection Hstep as <- | now injection Hstep as <-
            | discriminate Hstep] ]).
    + (* ONat / tproxy / fwd / queue: the terminal is Accept-or-NAT-Drop-or-break *)
      destruct (terminal_loadable r e2 p2);
        [destruct (nat_drops h r e2 p2)|]; intro Hstep;
        [now injection Hstep as <- | now injection Hstep as <- | discriminate Hstep].
    + destruct (terminal_loadable r e2 p2);
        [destruct (nat_drops h r e2 p2)|]; intro Hstep;
        [now injection Hstep as <- | now injection Hstep as <- | discriminate Hstep].
    + destruct (terminal_loadable r e2 p2);
        [destruct (nat_drops h r e2 p2)|]; intro Hstep;
        [now injection Hstep as <- | now injection Hstep as <- | discriminate Hstep].
    + destruct (terminal_loadable r e2 p2);
        [destruct (nat_drops h r e2 p2)|]; intro Hstep;
        [now injection Hstep as <- | now injection Hstep as <- | discriminate Hstep].
Qed.

Lemma eval_rules_u_mut_proj_aux : forall rs fuel cs e0 e p,
  List.length rs < fuel ->
  e_vmap e = e_vmap e0 ->
  forallb (rule_plain e0) rs = true ->
  fst (eval_rules_u fuel cs rs e p) = eval_rules_mut rs e p
  /\ fst (snd (eval_rules_u fuel cs rs e p)) = snd (eval_rules_mut_env rs e p).
Proof.
  induction rs as [| r rest IH]; intros fuel cs e0 e p Hfuel Hvm Hpl;
    (destruct fuel as [| f]; [exfalso; cbn in Hfuel; lia |]).
  - cbn. auto.
  - cbn [List.length] in Hfuel.
    cbn [forallb] in Hpl. apply Bool.andb_true_iff in Hpl.
    destruct Hpl as [Hr Hrest].
    rewrite eval_rules_mut_cons, eval_rules_mut_env_cons. cbn [eval_rules_u].
    pose proof (rule_step_vmap r e p) as Hstepvm.
    destruct (rule_step r e p) as [[v|] [e' p']] eqn:Hstep;
      cbn [fst snd] in Hstepvm.
    + assert (Hplain : verdict_plain v = true).
      { eapply (rule_step_plain e0 r Hr e p v).
        - congruence.
        - now rewrite Hstep. }
      destruct v; try discriminate Hplain; cbn [terminal];
        try (split; reflexivity).
      (* Continue *)
      apply (IH f cs e0 e' p'); [lia | congruence | exact Hrest].
    + apply (IH f cs e0 e' p'); [lia | congruence | exact Hrest].
Qed.

(** THE mutation-strand projection: on transfer-free rules the unified fold's
    verdict is [eval_rules_mut] and its env is [eval_rules_mut_env]'s — the
    flat mutation strand is a projection of the unified semantics, licensed by
    this equation (any fuel that can traverse the flat list; no chain
    environment is consulted because no transfer is realisable). *)
Theorem eval_rules_u_mut_proj : forall fuel cs rs e p,
  List.length rs < fuel ->
  forallb (rule_plain e) rs = true ->
  fst (eval_rules_u fuel cs rs e p) = eval_rules_mut rs e p
  /\ fst (snd (eval_rules_u fuel cs rs e p)) = snd (eval_rules_mut_env rs e p).
Proof.
  intros fuel cs rs e p Hfuel Hpl.
  eapply eval_rules_u_mut_proj_aux; eauto.
Qed.

Corollary eval_table_u_mut_proj : forall fuel cs c e p,
  List.length (c_rules c) < fuel ->
  forallb (rule_plain e) (c_rules c) = true ->
  fst (eval_table_u fuel cs c e p) = eval_chain_mut c e p
  /\ fst (snd (eval_table_u fuel cs c e p)) = snd (eval_chain_mut_env c e p).
Proof.
  intros fuel cs c e p Hfuel Hpl.
  destruct (eval_rules_u_mut_proj fuel cs (c_rules c) e p Hfuel Hpl) as [Hv He].
  unfold eval_table_u, eval_chain_mut, eval_chain_mut_env.
  rewrite <- (eval_rules_mut_env_fst (c_rules c) e p) in *.
  destruct (eval_rules_u fuel cs (c_rules c) e p) as [[v|] s];
    destruct (eval_rules_mut_env (c_rules c) e p) as [[w|] e'];
    cbn [fst snd] in *; subst; try discriminate Hv;
    try (injection Hv as <-); auto.
Qed.

Lemma eval_rules_u_mut_st_proj_aux : forall rs fuel cs e0 e p,
  List.length rs < fuel ->
  e_vmap e = e_vmap e0 ->
  forallb (rule_plain e0) rs = true ->
  eval_rules_u fuel cs rs e p = eval_rules_mut_st rs e p.
Proof.
  induction rs as [| r rest IH]; intros fuel cs e0 e p Hfuel Hvm Hpl;
    (destruct fuel as [| f]; [exfalso; cbn in Hfuel; lia |]).
  - reflexivity.
  - cbn [List.length] in Hfuel.
    cbn [forallb] in Hpl. apply Bool.andb_true_iff in Hpl.
    destruct Hpl as [Hr Hrest].
    rewrite eval_rules_mut_st_cons. cbn [eval_rules_u].
    pose proof (rule_step_vmap r e p) as Hstepvm.
    destruct (rule_step r e p) as [[v|] [e' p']] eqn:Hstep;
      cbn [fst snd] in Hstepvm.
    + assert (Hplain : verdict_plain v = true).
      { eapply (rule_step_plain e0 r Hr e p v).
        - congruence.
        - now rewrite Hstep. }
      destruct v; try discriminate Hplain; cbn [terminal]; try reflexivity.
      (* Continue *)
      apply (IH f cs e0 e' p'); [lia | congruence | exact Hrest].
    + apply (IH f cs e0 e' p'); [lia | congruence | exact Hrest].
Qed.

(** The FULL-STATE mutation-strand projection: on transfer-free rules the
    unified fold IS the flat full-state fold — the whole triple
    (verdict, env, packet), not just its verdict/env components.  This is the
    license under which [eval_rules_mut_st] (and its [eval_rules_mut]/
    [eval_rules_mut_env] projections) may stand in for the unified semantics. *)
Theorem eval_rules_u_mut_st_proj : forall fuel cs rs e p,
  List.length rs < fuel ->
  forallb (rule_plain e) rs = true ->
  eval_rules_u fuel cs rs e p = eval_rules_mut_st rs e p.
Proof.
  intros fuel cs rs e p Hfuel Hpl.
  eapply eval_rules_u_mut_st_proj_aux; eauto.
Qed.

Corollary eval_table_u_mut_st_proj : forall fuel cs c e p,
  List.length (c_rules c) < fuel ->
  forallb (rule_plain e) (c_rules c) = true ->
  eval_table_u fuel cs c e p = eval_chain_mut_st c e p.
Proof.
  intros fuel cs c e p Hfuel Hpl.
  unfold eval_table_u, eval_chain_mut_st.
  rewrite (eval_rules_u_mut_st_proj fuel cs (c_rules c) e p Hfuel Hpl).
  destruct (eval_rules_mut_st (c_rules c) e p) as [[v|] s]; reflexivity.
Qed.


(* ================================================================== *)
(** ** Fuel discipline for the UNIFIED evaluator: the exhaustion observation
    lives at the one semantics (M6).

    The pure strand's rank-descent fuel-independence (§ "Fuel discipline for
    the jump strand") covers only the write-free projection; stating adequacy
    ONLY there would carve effectful configs out of the fuel story.  The same
    induction goes through at [eval_rules_u] itself: the state a traversal
    accumulates never touches the verdict maps ([rule_step_vmap] /
    [eval_rules_u_vmap]), so a rank witness stated against the entry env's
    [e_vmap] bounds every transfer the run can realise -- at the mutated
    states included.  [chain_ranked_u] is that witness ([rule_step]-level,
    quantified over every vmap-agreeing state); [chains_plain] (every rule
    [rule_plain]) discharges it by computation for the transfer-free case,
    at rank 0 ([chains_plain_ranked_u]). *)

(** A whole unified traversal preserves the verdict maps: no effect writes
    [e_vmap]. *)
Lemma eval_rules_u_vmap : forall fuel cs rs e p,
  e_vmap (fst (snd (eval_rules_u fuel cs rs e p))) = e_vmap e.
Proof.
  induction fuel as [| f IH]; intros cs rs e p; [reflexivity |].
  destruct rs as [| r rest]; [reflexivity |].
  cbn [eval_rules_u].
  pose proof (rule_step_vmap r e p) as Hvm.
  destruct (rule_step r e p) as [[v|] [e' p']] eqn:Hstep; cbn [fst snd] in Hvm.
  2:{ rewrite (IH cs rest e' p'). exact Hvm. }
  destruct v as [ | | | tc cc | lo hi bp fo | n | n | ]; cbn [fst snd];
    try exact Hvm;
    try (rewrite (IH cs rest e' p'); exact Hvm).
  - (* Jump *)
    destruct (chain_lookup cs n) as [ch|].
    2:{ rewrite (IH cs rest e' p'). exact Hvm. }
    pose proof (IH cs (c_rules ch) e' p') as Hcallee.
    destruct (eval_rules_u f cs (c_rules ch) e' p') as [[w|] [e2 p2]];
      cbn [fst snd] in Hcallee |- *.
    + congruence.
    + rewrite (IH cs rest e2 p2). congruence.
  - (* Goto *)
    destruct (chain_lookup cs n) as [ch|]; cbn [fst snd].
    + rewrite (IH cs (c_rules ch) e' p'). exact Hvm.
    + exact Hvm.
Qed.

(** Every transfer rule [r] can realise -- from ANY state agreeing with [e]
    on the verdict maps -- that resolves in [cs] has rank below [k]. *)
Definition rule_step_targets_below (rank : String.string -> nat)
    (cs : list (String.string * chain)) (e : env) (k : nat) (r : rule) : Prop :=
  forall e' p m ch',
    e_vmap e' = e_vmap e ->
    (fst (rule_step r e' p) = Some (Jump m)
     \/ fst (rule_step r e' p) = Some (Goto m)) ->
    chain_lookup cs m = Some ch' ->
    rank m < k.

(** The unified-level acyclicity witness: like [chain_ranked], but against the
    per-rule FOLD's verdict and stable under every vmap-preserving mutation --
    exactly the states a unified traversal can reach. *)
Definition chain_ranked_u (rank : String.string -> nat)
    (cs : list (String.string * chain)) (e : env) : Prop :=
  forall n ch, chain_lookup cs n = Some ch ->
    rank n < List.length cs /\
    (forall r, In r (c_rules ch) -> rule_step_targets_below rank cs e (rank n) r).

Lemma eval_rules_u_fuel_indep_aux : forall rank cs e0,
  chain_ranked_u rank cs e0 ->
  forall fuel k rs e p fuel',
    e_vmap e = e_vmap e0 ->
    (forall r, In r rs -> rule_step_targets_below rank cs e0 k r) ->
    S (List.length rs + k * S (chain_len_max cs)) <= fuel ->
    fuel <= fuel' ->
    eval_rules_u fuel' cs rs e p = eval_rules_u fuel cs rs e p.
Proof.
  intros rank cs e0 Hcr.
  induction fuel as [| f IH]; intros k rs e p fuel' Hvm Htgt Hfuel Hle; [lia |].
  destruct fuel' as [| f']; [lia |].
  apply le_S_n in Hle.
  cbn [eval_rules_u].
  destruct rs as [| r rest]; [reflexivity |].
  cbn [List.length] in Hfuel.
  assert (Hrest : forall r0, In r0 rest -> rule_step_targets_below rank cs e0 k r0)
    by (intros; apply Htgt; now right).
  pose proof (rule_step_vmap r e p) as Hsvm.
  destruct (rule_step r e p) as [[v|] [e' p']] eqn:Hstep; cbn [fst snd] in Hsvm.
  2:{ apply (IH k rest e' p' f'); [congruence | exact Hrest | lia | lia]. }
  destruct v as [ | | | tc cc | lo hi bp fo | n | n | ];
    try reflexivity;
    try (apply (IH k rest e' p' f'); [congruence | exact Hrest | lia | lia]).
  - (* Jump *)
    destruct (chain_lookup cs n) as [ch|] eqn:Hlk;
      [ | apply (IH k rest e' p' f'); [congruence | exact Hrest | lia | lia] ].
    assert (Hrn : rank n < k).
    { eapply (Htgt r (or_introl eq_refl) e p n ch Hvm); [| exact Hlk].
      left. now rewrite Hstep. }
    pose proof (chain_lookup_len_max cs n ch Hlk) as Hlen.
    pose proof (proj2 (Hcr n ch Hlk)) as Hch.
    assert (Hvm' : e_vmap e' = e_vmap e0) by congruence.
    rewrite (IH (rank n) (c_rules ch) e' p' f' Hvm' Hch); [ | nia | lia ].
    pose proof (eval_rules_u_vmap f cs (c_rules ch) e' p') as Hcvm.
    destruct (eval_rules_u f cs (c_rules ch) e' p') as [[w|] [e2 p2]];
      cbn [fst snd] in Hcvm.
    + reflexivity.
    + apply (IH k rest e2 p2 f'); [congruence | exact Hrest | lia | lia].
  - (* Goto *)
    destruct (chain_lookup cs n) as [ch|] eqn:Hlk; [ | reflexivity ].
    assert (Hrn : rank n < k).
    { eapply (Htgt r (or_introl eq_refl) e p n ch Hvm); [| exact Hlk].
      right. now rewrite Hstep. }
    pose proof (chain_lookup_len_max cs n ch Hlk) as Hlen.
    pose proof (proj2 (Hcr n ch Hlk)) as Hch.
    assert (Hvm' : e_vmap e' = e_vmap e0) by congruence.
    apply (IH (rank n) (c_rules ch) e' p' f' Hvm' Hch); [ nia | lia ].
Qed.

(** HEADLINE (fuel axis, unified): above the same computable bound as the
    pure strand's, the UNIFIED evaluator's whole result -- verdict AND state
    -- is fuel-independent.  Effectful configs are inside the adequacy story,
    not carved out of it. *)
Theorem eval_rules_u_fuel_indep : forall rank cs e,
  chain_ranked_u rank cs e ->
  forall rs p fuel fuel',
    sufficient_fuel cs rs <= fuel ->
    sufficient_fuel cs rs <= fuel' ->
    eval_rules_u fuel cs rs e p = eval_rules_u fuel' cs rs e p.
Proof.
  intros rank cs e Hcr rs p fuel fuel' Hf Hf'.
  assert (Htgt : forall r, In r rs ->
            rule_step_targets_below rank cs e (List.length cs) r).
  { intros r _ e' q m ch' _ _ Hlk. exact (proj1 (Hcr m ch' Hlk)). }
  assert (Hbound : S (List.length rs
                      + List.length cs * S (chain_len_max cs))
                   <= sufficient_fuel cs rs) by (unfold sufficient_fuel; lia).
  transitivity (eval_rules_u (sufficient_fuel cs rs) cs rs e p).
  - exact (eval_rules_u_fuel_indep_aux rank cs e Hcr
             (sufficient_fuel cs rs) (List.length cs) rs e p fuel
             eq_refl Htgt Hbound Hf).
  - symmetry.
    exact (eval_rules_u_fuel_indep_aux rank cs e Hcr
             (sufficient_fuel cs rs) (List.length cs) rs e p fuel'
             eq_refl Htgt Hbound Hf').
Qed.

Corollary eval_table_u_fuel_indep : forall rank cs e,
  chain_ranked_u rank cs e ->
  forall base p fuel fuel',
    sufficient_fuel cs (c_rules base) <= fuel ->
    sufficient_fuel cs (c_rules base) <= fuel' ->
    eval_table_u fuel cs base e p = eval_table_u fuel' cs base e p.
Proof.
  intros rank cs e Hcr base p fuel fuel' Hf Hf'. unfold eval_table_u.
  now rewrite (eval_rules_u_fuel_indep rank cs e Hcr (c_rules base) p fuel fuel').
Qed.

(** Discharging [chain_ranked_u] for transfer-free chain environments: every
    rule [rule_plain] (no realisable transfer at any vmap-agreeing state,
    [rule_step_plain]) gives the rank-0 witness by computation. *)
Definition chains_plain (e : env) (cs : list (String.string * chain)) : bool :=
  forallb (fun nc => forallb (rule_plain e) (c_rules (snd nc))) cs.

Lemma chains_plain_ranked_u : forall e cs,
  chains_plain e cs = true ->
  chain_ranked_u (fun _ => O) cs e.
Proof.
  intros e cs H n ch Hlk. split.
  - destruct cs; [cbn in Hlk; discriminate | cbn; lia].
  - intros r Hr e' p m ch' Hvm Hdisj Hlk'. exfalso.
    pose proof (chain_lookup_in _ _ _ Hlk) as Hin.
    unfold chains_plain in H.
    eapply forallb_forall in H; [| exact Hin].
    eapply forallb_forall in H; [| exact Hr].
    destruct Hdisj as [Hj | Hj];
      pose proof (rule_step_plain e r H e' p _ Hvm Hj) as Hpl;
      discriminate Hpl.
Qed.

(* ================================================================== *)
(** ** The pure body walk is the fold's projection -- notrack included (M6).

    [rule_applies_walk] hand-threads exactly ONE effect: the `notrack`
    untracked latch ([set_untracked]).  That threading is not a parallel
    semantics -- it is the SAME transform [body_step]'s [SNotrack] case
    applies, and on every body whose other items are effect-free (consume-free
    matches, non-mutating statements; `notrack` itself ALLOWED) the walk is
    provably the break/no-break projection of the fold.  This is the
    notrack-admitting coincidence [rule_step_mutfree] could not state
    ([rule_mutfree] excludes [SNotrack]); together they cover every rule the
    pure strand's licenses admit, and the pure strand's remaining divergence
    (consumable matches read the entry bucket in the walk, the running bucket
    in the fold) is licensed at traversal level by Projection 1b -- never by
    an unbridged walk. *)

Definition body_item_purewalk (it : body_item) : bool :=
  match it with
  | BMatch m => match_consumefree m
  | BStmt SNotrack => true
  | BStmt s => negb (is_mut_stmt s)
  end.

Definition body_purewalk (body : list body_item) : bool :=
  forallb body_item_purewalk body.

Theorem rule_purewalk_ok : forall body e p,
  body_purewalk body = true ->
  body_loadable_walk body p = true ->
  rule_applies_walk body e p
  = match body_step body e p with
    | BRbreak _ _ => false
    | _ => true
    end.
Proof.
  induction body as [| it body IH]; intros e p Hpw Hld; [reflexivity |].
  unfold body_purewalk in Hpw. cbn [forallb] in Hpw.
  apply Bool.andb_true_iff in Hpw. destruct Hpw as [Hit Hrest].
  destruct it as [m | s].
  - (* match: both sides evaluate [eval_matchcond] at the same state; a
       consume-free match leaves the env untouched *)
    cbn [body_item_purewalk] in Hit.
    cbn [rule_applies_walk body_step].
    cbn [body_loadable_walk body_item_loadable] in Hld.
    apply Bool.andb_true_iff in Hld. destruct Hld as [_ Hld].
    destruct (eval_matchcond m e p) eqn:Hm; [| reflexivity].
    rewrite (match_consume_free_id m e p Hit). cbn [andb].
    apply IH; [exact Hrest | exact Hld].
  - destruct s; cbn [body_item_purewalk is_mut_stmt negb] in Hit;
      try discriminate Hit;
      (* non-mutating, non-synproxy, non-notrack statements: the walk skips,
         the fold checks the operand load the loadability walk guarantees *)
      try (cbn [rule_applies_walk body_step];
           cbn [body_loadable_walk body_item_loadable] in Hld;
           apply Bool.andb_true_iff in Hld; destruct Hld as [Hs Hld];
           rewrite Hs; apply IH; [exact Hrest | exact Hld]).
    + (* SNotrack: BOTH sides thread the same [set_untracked] *)
      cbn [rule_applies_walk body_step].
      cbn [body_loadable_walk body_item_loadable stmt_loadable andb] in Hld.
      rewrite <- (body_loadable_walk_untracked body p) in Hld.
      apply IH; [exact Hrest | exact Hld].
    + (* SSynproxy *)
      cbn [rule_applies_walk body_step].
      cbn [body_loadable_walk] in Hld.
      apply Bool.andb_true_iff in Hld. destruct Hld as [Hsl Hld].
      rewrite Hsl.
      destruct (synproxy_stops p); [reflexivity |].
      apply IH; [exact Hrest | exact Hld].
Qed.


End AtHook.

Arguments body_writes !body e p /.