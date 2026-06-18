(** * Semantics: the meaning of both languages as packet -> verdict.

    Both the declarative DSL and the bytecode are given the *same* observable
    semantics — a function from a packet to the verdict the base chain produces —
    so "semantics preserving" is a literal equality of these functions. *)

From Stdlib Require Import List NArith Bool.
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
      xorb (Nat.eqb (Nat.land (ls_flags spec) 1) 1) (Nat.ltb 0 (e_limit (pkt_env p) spec))
  | MQuota spec =>
      xorb (Nat.eqb (Nat.land (q_flags spec) 1) 1) (Nat.ltb 0 (e_quota (pkt_env p) spec))
  | MConnlimit spec =>
      xorb (Nat.eqb (Nat.land (cl_flags spec) 1) 1) (Nat.ltb 0 (e_connlimit (pkt_env p) spec))
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
  | BStmt _ :: rest => rule_applies_walk rest p
  end.
Definition rule_applies (r : rule) (p : packet) : bool :=
  rule_applies_walk (r_body r) p.

(** When the body contains no stopping synproxy, [rule_applies_walk] is exactly
    [forallb eval_matchcond] over the body's matches. *)
Lemma rule_applies_walk_no_synproxy : forall body p,
  body_synproxy_stops body p = false ->
  rule_applies_walk body p = forallb (fun m => eval_matchcond m p) (body_matches body).
Proof.
  induction body as [| it body IH]; intro p; [reflexivity|].
  assert (Hcons : forall it0 b, body_synproxy_stops (it0 :: b) p =
            (match it0 with BStmt (SSynproxy _ _) => synproxy_stops p | _ => false end)
            || body_synproxy_stops b p) by reflexivity.
  rewrite Hcons. destruct it as [m | s].
  - cbn [orb]. cbn [rule_applies_walk body_matches flat_map app forallb]. intro H.
    rewrite IH by exact H. reflexivity.
  - destruct s; cbn [rule_applies_walk body_matches flat_map app];
      try (cbn [orb]; intro H; apply IH; exact H).
    (* SSynproxy: the [orb] head is [synproxy_stops p]; the hypothesis forces it false *)
    destruct (synproxy_stops p) eqn:Hs; cbn [orb];
      [discriminate | intro H; apply IH; exact H].
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
  | SDynsetImm _ _ keyfs _ _ => fields_loadable keyfs p
  | SExthdrWrite vs _ _ _ _ => vsrc_loadable vs p
  | SDupSrc src _ _ _ => vsrc_loadable src p
  | SSynproxy _ _ => synproxy_loadable p   (* non-TCP / non-L4 => NFT_BREAK (rule skipped) *)
  | SCounter _ _ | SNotrack | SLog _ | SObjref _ _
  | SLast _ | SExthdrReset _ _ | SDup _ _ _ => true
  end.

Definition body_item_loadable (it : body_item) (p : packet) : bool :=
  match it with
  | BMatch m => match_loadable m p
  | BStmt s => stmt_loadable s p
  end.

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
  | Some w => match fwd_src w with Some vs => vsrc_loadable vs p | None => true end
  | None =>
  match r_queue r with
  | Some q => match q_src q with Some vs => vsrc_loadable vs p | None => true end
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
  sd_vmaps : list (String.string * list (data * verdict));  (* verdict-map name -> entries *)
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
     e_ifaddr := e_ifaddr base;
     e_limit := e_limit base; e_quota := e_quota base; e_connlimit := e_connlimit base |}.

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

(** Look up a key in a verdict map's entries. *)
Fixpoint assoc_verdict (key : data) (entries : list (data * verdict)) : option verdict :=
  match entries with
  | [] => None
  | (k, v) :: rest => if data_eqb key k then Some v else assoc_verdict key rest
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

Definition outcome (r : rule) (p : packet) : option verdict :=
  if body_synproxy_stops (r_body r) p then Some Drop else outcome_core r p.

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

Definition rule_loadable (r : rule) (p : packet) : bool :=
  body_loadable_walk (r_body r) p &&
  (if body_synproxy_stops (r_body r) p then true else end_loadable r p).

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
      run_rule (set_reg rf dst (pkt_ct p k)) rest p
  | IRtLoad k dst :: rest =>
      run_rule (set_reg rf dst (e_rt (pkt_env p) k)) rest p
  | ISocketLoad k dst :: rest =>
      run_rule (set_reg rf dst (pkt_sock p k)) rest p
  | INumgen spec dst :: rest =>
      run_rule (set_reg rf dst (pkt_numgen p spec)) rest p
  | IOsf dst :: rest =>
      run_rule (set_reg rf dst (pkt_osf p)) rest p
  | IExthdrLoad ep h o l pr dst :: rest =>
      run_rule (set_reg rf dst (pkt_eh p ep h o l pr)) rest p
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
      if xorb (Nat.eqb (Nat.land (ls_flags spec) 1) 1) (Nat.ltb 0 (e_limit (pkt_env p) spec))
      then run_rule rf rest p else None
  | IQuota spec :: rest =>
      if xorb (Nat.eqb (Nat.land (q_flags spec) 1) 1) (Nat.ltb 0 (e_quota (pkt_env p) spec))
      then run_rule rf rest p else None
  | IConnlimit spec :: rest =>
      if xorb (Nat.eqb (Nat.land (cl_flags spec) 1) 1) (Nat.ltb 0 (e_connlimit (pkt_env p) spec))
      then run_rule rf rest p else None
  | ICounter _ _ :: rest => run_rule rf rest p   (* verdict-neutral *)
  | INotrack :: rest      => run_rule rf rest p
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
  {| pkt_env := pkt_env p;
     pkt_meta := (fun k' => if meta_eqb k k' then v else pkt_meta p k');
     pkt_ct := pkt_ct p; pkt_sock := pkt_sock p;
     pkt_eh := pkt_eh p; pkt_lh := pkt_lh p; pkt_nh := pkt_nh p; pkt_th := pkt_th p;
     pkt_ih := pkt_ih p; pkt_tnl := pkt_tnl p; pkt_fibkey := pkt_fibkey p;     pkt_numgen := pkt_numgen p; pkt_osf := pkt_osf p;
     pkt_tunnel := pkt_tunnel p; pkt_symhash := pkt_symhash p; pkt_xfrm := pkt_xfrm p;
     pkt_ctdir := pkt_ctdir p; pkt_inner := pkt_inner p;
     pkt_have_l4 := pkt_have_l4 p; pkt_fragoff := pkt_fragoff p |}.
Definition set_ct (p : packet) (k : ct_key) (v : data) : packet :=
  {| pkt_env := pkt_env p; pkt_meta := pkt_meta p;
     pkt_ct := (fun k' => if ct_eqb k k' then v else pkt_ct p k');
     pkt_sock := pkt_sock p;
     pkt_eh := pkt_eh p; pkt_lh := pkt_lh p; pkt_nh := pkt_nh p; pkt_th := pkt_th p;
     pkt_ih := pkt_ih p; pkt_tnl := pkt_tnl p; pkt_fibkey := pkt_fibkey p;     pkt_numgen := pkt_numgen p; pkt_osf := pkt_osf p;
     pkt_tunnel := pkt_tunnel p; pkt_symhash := pkt_symhash p; pkt_xfrm := pkt_xfrm p;
     pkt_ctdir := pkt_ctdir p; pkt_inner := pkt_inner p;
     pkt_have_l4 := pkt_have_l4 p; pkt_fragoff := pkt_fragoff p |}.

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
  {| pkt_env := pkt_env p; pkt_meta := pkt_meta p; pkt_ct := pkt_ct p;
     pkt_sock := pkt_sock p; pkt_eh := pkt_eh p; pkt_lh := pkt_lh p;
     pkt_nh := splice (pkt_nh p) off len v; pkt_th := pkt_th p;
     pkt_ih := pkt_ih p; pkt_tnl := pkt_tnl p; pkt_fibkey := pkt_fibkey p;
     pkt_numgen := pkt_numgen p; pkt_osf := pkt_osf p;
     pkt_tunnel := pkt_tunnel p; pkt_symhash := pkt_symhash p; pkt_xfrm := pkt_xfrm p;
     pkt_ctdir := pkt_ctdir p; pkt_inner := pkt_inner p;
     pkt_have_l4 := pkt_have_l4 p; pkt_fragoff := pkt_fragoff p |}.

(** The (offset, length) of the L3 source / destination address slot for a NAT
    [family] ("ip" = IPv4: src @12 len 4 / dst @16 len 4, where [FIp4Saddr] /
    [FIp4Daddr] read; "ip6" = IPv6: src @8 len 16 / dst @24 len 16, where
    [FIp6Saddr] / [FIp6Daddr] read).  The kernel chooses 32 vs 128 bits by family
    ([nat_addrlen], netlink_linearize.c:1237). *)
Definition saddr_slot (family : String.string) : nat * nat :=
  if String.eqb family nat_fam_ip6 then (8, 16) else (12, 4).
Definition daddr_slot (family : String.string) : nat * nat :=
  if String.eqb family nat_fam_ip6 then (24, 16) else (16, 4).

(** Source-NAT a packet: rewrite its source address (the [saddr_slot] for the
    NAT [family]) to [v].  This is the data-plane effect a `snat`/`masquerade`
    performs; [set_saddr "ip" p (e_ifaddr (pkt_env p) oifname)] realises
    `masquerade` = "use the IP of the interface the packet exits". *)
Definition set_saddr (family : String.string) (p : packet) (v : data) : packet :=
  let '(off, len) := saddr_slot family in set_nh_field p off len v.

(** Destination-NAT a packet: rewrite its destination address (the [daddr_slot]
    for the NAT [family]) to [v].  This is the data-plane effect a
    `dnat`/`redirect` performs — the kernel `nft_nat` applies [NF_NAT_MANIP_DST]
    from [NFTNL_EXPR_NAT_REG_ADDR_MIN] (netlink_linearize.c:1304). *)
Definition set_daddr (family : String.string) (p : packet) (v : data) : packet :=
  let '(off, len) := daddr_slot family in set_nh_field p off len v.

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
  {| e_set := (fun n =>
       if String.eqb n name
       then if String.eqb op op_delete
            then filter (fun lh => negb (andb (data_eqb (fst lh) key) (data_eqb (snd lh) key)))
                        (e_set e n)
            else (key, key) :: e_set e n
       else e_set e n);
     e_vmap := e_vmap e; e_map := e_map e;
     e_routes := e_routes e; e_rt := e_rt e;
     e_ifaddr := e_ifaddr e;
     e_limit := e_limit e; e_quota := e_quota e; e_connlimit := e_connlimit e |}.

Definition set_env_dynset (p : packet) (op name : String.string) (key : data) : packet :=
  {| pkt_env := env_set_upd (pkt_env p) op name key;
     pkt_meta := pkt_meta p; pkt_ct := pkt_ct p; pkt_sock := pkt_sock p;
     pkt_eh := pkt_eh p; pkt_lh := pkt_lh p; pkt_nh := pkt_nh p; pkt_th := pkt_th p;
     pkt_ih := pkt_ih p; pkt_tnl := pkt_tnl p; pkt_fibkey := pkt_fibkey p;
     pkt_numgen := pkt_numgen p; pkt_osf := pkt_osf p;
     pkt_tunnel := pkt_tunnel p; pkt_symhash := pkt_symhash p; pkt_xfrm := pkt_xfrm p;
     pkt_ctdir := pkt_ctdir p; pkt_inner := pkt_inner p;
     pkt_have_l4 := pkt_have_l4 p; pkt_fragoff := pkt_fragoff p |}.

(** The map analogue: a `dynset` whose target is a MAP (`add @m {key : data}`)
    learns the entry [key -> data] in the named value-map [e_map], so a later
    `@m`-keyed lookup (map value / verdict map) sees it.  add/update prepend the
    entry (so [map_lookup_data] finds the freshest first), delete drops entries
    with that key. *)
Definition env_map_upd (e : env) (op name : String.string) (key dat : data) : env :=
  {| e_set := e_set e; e_vmap := e_vmap e;
     e_map := (fun n =>
       if String.eqb n name
       then if String.eqb op op_delete
            then filter (fun kv => negb (data_eqb (fst kv) key)) (e_map e n)
            else (key, dat) :: e_map e n
       else e_map e n);
     e_routes := e_routes e; e_rt := e_rt e;
     e_ifaddr := e_ifaddr e;
     e_limit := e_limit e; e_quota := e_quota e; e_connlimit := e_connlimit e |}.

Definition set_env_dynset_map (p : packet) (op name : String.string) (key dat : data) : packet :=
  {| pkt_env := env_map_upd (pkt_env p) op name key dat;
     pkt_meta := pkt_meta p; pkt_ct := pkt_ct p; pkt_sock := pkt_sock p;
     pkt_eh := pkt_eh p; pkt_lh := pkt_lh p; pkt_nh := pkt_nh p; pkt_th := pkt_th p;
     pkt_ih := pkt_ih p; pkt_tnl := pkt_tnl p; pkt_fibkey := pkt_fibkey p;
     pkt_numgen := pkt_numgen p; pkt_osf := pkt_osf p;
     pkt_tunnel := pkt_tunnel p; pkt_symhash := pkt_symhash p; pkt_xfrm := pkt_xfrm p;
     pkt_ctdir := pkt_ctdir p; pkt_inner := pkt_inner p;
     pkt_have_l4 := pkt_have_l4 p; pkt_fragoff := pkt_fragoff p |}.

(** The VM's meta/ct effect of running one rule's bytecode: mirrors [run_rule]'s
    register threading, but instead of a verdict it returns the packet with the
    [IMetaSet]/[ICtSet] writes applied (in execution order; a write only happens
    once the matches before it have passed — a failed cmp/lookup/limit returns the
    packet unchanged, exactly as the verdict run breaks). *)
Fixpoint run_rule_writes (rf : regfile) (is : list instr) (p : packet) : packet :=
  match is with
  | [] => p
  | IMetaLoad k dst :: rest => run_rule_writes (set_reg rf dst (pkt_meta p k)) rest p
  | ICtLoad k dst :: rest => run_rule_writes (set_reg rf dst (pkt_ct p k)) rest p
  | IRtLoad k dst :: rest => run_rule_writes (set_reg rf dst (e_rt (pkt_env p) k)) rest p
  | ISocketLoad k dst :: rest => run_rule_writes (set_reg rf dst (pkt_sock p k)) rest p
  | INumgen spec dst :: rest => run_rule_writes (set_reg rf dst (pkt_numgen p spec)) rest p
  | IOsf dst :: rest => run_rule_writes (set_reg rf dst (pkt_osf p)) rest p
  | IExthdrLoad ep h o l pr dst :: rest =>
      run_rule_writes (set_reg rf dst (pkt_eh p ep h o l pr)) rest p
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
  | ILimit spec :: rest => if xorb (Nat.eqb (Nat.land (ls_flags spec) 1) 1) (Nat.ltb 0 (e_limit (pkt_env p) spec)) then run_rule_writes rf rest p else p
  | IQuota spec :: rest => if xorb (Nat.eqb (Nat.land (q_flags spec) 1) 1) (Nat.ltb 0 (e_quota (pkt_env p) spec)) then run_rule_writes rf rest p else p
  | IConnlimit spec :: rest => if xorb (Nat.eqb (Nat.land (cl_flags spec) 1) 1) (Nat.ltb 0 (e_connlimit (pkt_env p) spec)) then run_rule_writes rf rest p else p
  | ICounter _ _ :: rest => run_rule_writes rf rest p
  | INotrack :: rest => run_rule_writes rf rest p
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
  (* every OTHER statement is meta/ct- and env-neutral, but it still LOADS its
     operand fields; an unloadable load BREAKs the rule (so no later statement
     runs), exactly as [run_rule_writes] breaks at that operand's payload load. *)
  | BStmt s :: rest => if stmt_loadable s p then body_writes rest p else p
  end.
Definition dsl_writes (r : rule) (p : packet) : packet := body_writes (r_body r) p.

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
        | Some v => if terminal v then Some v else eval_rules_mut rest (dsl_writes r p)
        | None   => eval_rules_mut rest (dsl_writes r p)
        end
      else eval_rules_mut rest (dsl_writes r p)
  end.

Fixpoint run_program_mut (prog : program) (p : packet) : option verdict :=
  match prog with
  | [] => None
  | rp :: rest =>
      match run_rule empty_rf rp p with
      | Some v => if terminal v then Some v else run_program_mut rest (run_rule_writes empty_rf rp p)
      | None   => run_program_mut rest (run_rule_writes empty_rf rp p)
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
        | Some v => if terminal v then (Some v, pkt_env (dsl_writes r p))
                    else eval_rules_mut_env rest (dsl_writes r p)
        | None   => eval_rules_mut_env rest (dsl_writes r p)
        end
      else eval_rules_mut_env rest (dsl_writes r p)
  end.

Fixpoint run_program_mut_env (prog : program) (p : packet) : option verdict * env :=
  match prog with
  | [] => (None, pkt_env p)
  | rp :: rest =>
      match run_rule empty_rf rp p with
      | Some v => if terminal v then (Some v, pkt_env (run_rule_writes empty_rf rp p))
                  else run_program_mut_env rest (run_rule_writes empty_rf rp p)
      | None   => run_program_mut_env rest (run_rule_writes empty_rf rp p)
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
  | None =>
      (* the immediate loaded into register 1 = NFTNL_EXPR_NAT_REG_ADDR_MIN *)
      match find (fun rv => Nat.eqb (fst rv) 1) (nat_imms ns) with
      | Some rv => snd rv
      | None => []
      end
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
  if String.eqb (nat_family ns) nat_fam_ip6 then nat_fam_ip6 else nat_fam_ip4.

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

(** The data-plane NAT effect of a terminal rule at hook [h].  Only [redir] is
    hook-dependent (see [redir_daddr]); masq/snat/dnat are hook-invariant. *)
Definition apply_nat (h : hook_id) (r : rule) (p : packet) : packet :=
  match r_nat r with
  | Some ns =>
      let fam := nat_addrfamily ns in
      if String.eqb (nat_kind ns) nat_masq_kind
      then set_saddr fam p (e_ifaddr (pkt_env p) (field_value FMetaOifname p))
      else if String.eqb (nat_kind ns) nat_snat_kind
      then set_saddr fam p (nat_addr ns p)
      else if String.eqb (nat_kind ns) nat_dnat_kind
      then set_daddr fam p (nat_addr ns p)
      else if String.eqb (nat_kind ns) nat_redir_kind
      then set_daddr fam p (redir_daddr h fam p)
      else p
  | None => p
  end.

(** [eval_rules_trace]/[eval_chain_trace] take the netfilter hook [h] the base
    chain is attached to, because the data-plane NAT effect at a terminal verdict
    ([apply_nat]) is hook-dependent (an OUTPUT-hooked `redirect` rewrites the
    destination to loopback, not the inbound-interface address). *)
Fixpoint eval_rules_trace (h : hook_id) (rs : list rule) (p : packet) : option verdict * packet :=
  match rs with
  | [] => (None, p)
  | r :: rest =>
      if rule_loadable r p && rule_applies r p then
        match outcome r p with
        | Some v => if terminal v then (Some v, apply_nat h r (dsl_writes r p))
                    else eval_rules_trace h rest (dsl_writes r p)
        | None   => eval_rules_trace h rest (dsl_writes r p)
        end
      else eval_rules_trace h rest (dsl_writes r p)
  end.

Definition eval_chain_trace (h : hook_id) (c : chain) (p : packet) : verdict * packet :=
  match eval_rules_trace h (c_rules c) p with
  | (Some v, q) => (v, q) | (None, q) => (c_policy c, q) end.

Lemma eval_rules_trace_verdict : forall h rs p,
  fst (eval_rules_trace h rs p) = eval_rules_mut rs p.
Proof.
  induction rs as [|r rest IH]; intros p; simpl; [reflexivity|].
  destruct (rule_loadable r p && rule_applies r p).
  - destruct (outcome r p) as [v|]; [destruct (terminal v); simpl; auto|]; auto.
  - auto.
Qed.

Lemma eval_chain_trace_verdict : forall h c p,
  fst (eval_chain_trace h c p) = eval_chain_mut c p.
Proof.
  intros h c p. unfold eval_chain_trace, eval_chain_mut.
  rewrite <- (eval_rules_trace_verdict h (c_rules c) p).
  destruct (eval_rules_trace h (c_rules c) p) as [[v|] q]; reflexivity.
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
  {| pkt_env := e; pkt_meta := pkt_meta p; pkt_ct := pkt_ct p; pkt_sock := pkt_sock p;
     pkt_eh := pkt_eh p; pkt_lh := pkt_lh p; pkt_nh := pkt_nh p; pkt_th := pkt_th p;
     pkt_ih := pkt_ih p; pkt_tnl := pkt_tnl p; pkt_fibkey := pkt_fibkey p; pkt_numgen := pkt_numgen p;
     pkt_osf := pkt_osf p; pkt_tunnel := pkt_tunnel p; pkt_symhash := pkt_symhash p;
     pkt_xfrm := pkt_xfrm p; pkt_ctdir := pkt_ctdir p; pkt_inner := pkt_inner p;
     pkt_have_l4 := pkt_have_l4 p; pkt_fragoff := pkt_fragoff p |}.

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
