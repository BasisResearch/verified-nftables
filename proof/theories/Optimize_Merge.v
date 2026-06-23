(** * Optimize_Merge: the [nft -o] / [nft --optimize] consolidation passes,
    proved verdict-preserving against the same [eval_chain] semantics.

    [nft --optimize] (src/optimize.c, [chain_optimize]) merges a run of ADJACENT
    rules that are identical except in the right-hand VALUE of one selector into a
    single rule using an anonymous set / verdict map (the [MERGE_BY_VERDICT] case
    of [merge_rules]).  Two canonical forms:

      1. value merge (same selector, SAME verdict, differing values):
           `tcp dport 22 accept`            ┐
           `tcp dport 80 accept`            ┘  =>  `tcp dport { 22, 80 } accept`
         (src/optimize.c [merge_expr_stmts] / [merge_stmts]).

      2. verdict-map merge (same selector, DIFFERENT verdicts):
           `tcp dport 22 accept`            ┐
           `tcp dport 80 drop`              ┘  =>  `tcp dport vmap { 22:accept, 80:drop }`
         (src/optimize.c [merge_stmts_vmap]).

    Both are sound for the SAME reason: in first-match order, a run of adjacent
    rules `sel=v_i -> outcome_i` (all sharing every other statement, the selector
    field, and the loadability path) is verdict-equivalent to ONE rule whose head
    selector matches the DISJUNCTION `sel in {v_1,…,v_n}` and whose outcome is, per
    matched value, `outcome_i` — which is exactly an anonymous set (when all
    `outcome_i` coincide) or a verdict map (when they differ).

    This file proves the GENERAL two-rule adjacent merge ([eval_rules_merge2])
    from a single matchcond-level *disjunction certificate*
      [eval_matchcond m12 p = eval_matchcond m1 p || eval_matchcond m2 p]
      [match_loadable  m12 p = match_loadable  m1 p  (= match_loadable m2 p)]
    and the rules being otherwise identical (same tail body, same verdict/vmap/
    nat/…/after).  It then instantiates the certificate for the value-merge case
    that is expressible WITHOUT a new syntax constructor or a runtime set
    declaration: two point matches `MEq f v1` / `MEq f v2` whose union is the
    contiguous interval `[lo,hi]` collapse to one range match `MRange f false lo hi`
    (the range form `nft` itself coalesces a contiguous anonymous set into).

    The pass [merge_chain] folds adjacent value-merges over a chain; the theorem
    [merge_chain_correct] shows the packet->verdict function is unchanged.  It is
    proven axiom-free (Print Assumptions: Closed under the global context). *)

From Stdlib Require Import List PeanoNat Bool Lia Wellfounded Arith.Wf_nat.
From Nft Require Import Bytes Packet Verdict Syntax Bytecode Semantics Optimize.
Import ListNotations.

(** ** The abstract adjacent-rule merge.

    [eval_rules_merge2]: if [r12] is loadable / applies / outcomes EXACTLY as the
    disjunction of two adjacent rules [r1], [r2] demands, then putting [r12] in
    place of the pair [r1; r2] does not change [eval_rules] on any packet.  The
    three hypotheses are precisely the obligations the kernel's first-match
    traversal imposes:

      - [Hl]  both originals and the merged rule have the SAME loadability (the
              break/NFT_BREAK path is shared — they read the same fields);
      - [Ho]  the merged rule's outcome equals each original's (so a hit gives the
              right verdict; for a value-merge all three coincide, for a vmap-merge
              the per-value outcome is what the merged rule reproduces);
      - [Ha]  the merged rule applies iff EITHER original applies (the head
              selector is the disjunction of the two originals' selectors). *)
Lemma eval_rules_merge2 : forall r1 r2 r12 rest p,
  rule_loadable r12 p = rule_loadable r1 p ->
  rule_loadable r12 p = rule_loadable r2 p ->
  outcome r12 p = outcome r1 p ->
  outcome r12 p = outcome r2 p ->
  rule_applies r12 p = orb (rule_applies r1 p) (rule_applies r2 p) ->
  eval_rules (r12 :: rest) p = eval_rules (r1 :: r2 :: rest) p.
Proof.
  intros r1 r2 r12 rest p Hl1 Hl2 Ho1 Ho2 Ha.
  (* normalise everything onto r1's loadability/outcome *)
  assert (Hl2' : rule_loadable r1 p = rule_loadable r2 p) by (rewrite <- Hl1; exact Hl2).
  assert (Ho2' : outcome r1 p = outcome r2 p) by (rewrite <- Ho1; exact Ho2).
  cbn [eval_rules].
  rewrite Hl1, Ho1, Ha.
  destruct (rule_loadable r1 p) eqn:EL.
  - (* loadable on r1 (hence on r2 and r12) *)
    rewrite <- Hl2'. cbn [andb].
    destruct (rule_applies r1 p) eqn:Ea1; cbn [orb].
    + (* r1 applies: merged fires with outcome r1 = same as r1 *)
      destruct (outcome r1 p) as [v |] eqn:Eo.
      * destruct (terminal v) eqn:Et; [reflexivity|].
        cbn [eval_rules].
        destruct (rule_applies r2 p) eqn:Ea2; cbn [andb].
        -- rewrite <- Ho2', Et. reflexivity.
        -- reflexivity.
      * cbn [eval_rules].
        destruct (rule_applies r2 p) eqn:Ea2; cbn [andb].
        -- rewrite <- Ho2'. reflexivity.
        -- reflexivity.
    + (* r1 does not apply: merged applies iff r2 applies *)
      cbn [andb eval_rules].
      destruct (rule_applies r2 p) eqn:Ea2; cbn [andb].
      * rewrite <- Ho2'. reflexivity.
      * reflexivity.
  - (* not loadable: merged skipped, r1 skipped, r2 also skipped *)
    rewrite <- Hl2'. cbn [andb].
    reflexivity.
Qed.

(** ** From a matchcond disjunction certificate to the three merge obligations.

    Two adjacent rules eligible for a value-merge share EVERYTHING but their head
    match: rule [mk_head m rest verd …] is [BMatch m :: rest] with a fixed
    verdict/vmap/nat/…/after.  [merge_head] replaces the head match [m] by [m12].
    When [m12] is the DISJUNCTION certificate of [m1] and [m2] — same field loaded
    ([match_loadable] equal) and value test the [orb] of the two — the merged rule
    meets [eval_rules_merge2]'s three obligations, because every other ingredient
    of [rule_loadable]/[outcome]/[rule_applies] is shared (the head [BMatch]
    contributes nothing to [body_synproxy_stops]/[body_has_notrack], and the
    body-tail / end-fields are identical). *)

Definition mk_head (m : matchcond) (rest : list body_item) (r : rule) : rule :=
  {| r_body := BMatch m :: rest;
     r_verdict := r_verdict r; r_vmap := r_vmap r; r_nat := r_nat r;
     r_tproxy := r_tproxy r; r_fwd := r_fwd r; r_queue := r_queue r;
     r_after := r_after r |}.

(* The head [BMatch] is transparent to the synproxy-stop and notrack predicates,
   so [body_thread] and [body_synproxy_stops] of [mk_head] depend only on [rest]. *)
Lemma synproxy_stops_mk_head : forall m rest r p,
  body_synproxy_stops (r_body (mk_head m rest r)) p = body_synproxy_stops rest p.
Proof. reflexivity. Qed.

Lemma has_notrack_mk_head : forall m rest r,
  body_has_notrack (r_body (mk_head m rest r)) = body_has_notrack rest.
Proof. reflexivity. Qed.

Lemma body_thread_mk_head : forall m rest r p,
  body_thread (r_body (mk_head m rest r)) p = body_thread rest p.
Proof. intros. unfold body_thread. rewrite has_notrack_mk_head. reflexivity. Qed.

(* end-loadability and outcome-core of [mk_head] only read the (shared) end-fields
   of the record, NOT the body — so two [mk_head]s over the same [r] agree there. *)
Lemma end_loadable_mk_head : forall m rest r q,
  end_loadable (mk_head m rest r) q = end_loadable r q.
Proof.
  intros. unfold end_loadable, tail_loadable, terminal_loadable, vmap_loadable,
    terminal_outcome. reflexivity.
Qed.

Lemma outcome_core_mk_head : forall m rest r q,
  outcome_core (mk_head m rest r) q = outcome_core r q.
Proof.
  intros. unfold outcome_core, terminal_outcome. reflexivity.
Qed.

(* loadability of the merged head reduces to: head match loads + tail body loads +
   shared end loads.  Pulling the head out makes the dependence on [m] explicit. *)
Lemma rule_loadable_mk_head : forall m rest r p,
  rule_loadable (mk_head m rest r) p =
    match_loadable m p &&
    (body_loadable_walk rest p &&
     (if body_synproxy_stops rest p then true
      else end_loadable r (body_thread rest p))).
Proof.
  intros m rest r p. unfold rule_loadable.
  rewrite synproxy_stops_mk_head, body_thread_mk_head, end_loadable_mk_head.
  (* body_loadable_walk (BMatch m :: rest) = match_loadable m p && walk rest *)
  cbn [r_body body_loadable_walk body_item_loadable].
  rewrite Bool.andb_assoc. reflexivity.
Qed.

Lemma outcome_mk_head : forall m rest r p,
  outcome (mk_head m rest r) p =
    if body_synproxy_stops rest p then Some Drop
    else outcome_core r (body_thread rest p).
Proof.
  intros m rest r p. unfold outcome.
  rewrite synproxy_stops_mk_head, body_thread_mk_head, outcome_core_mk_head.
  reflexivity.
Qed.

Lemma rule_applies_mk_head : forall m rest r p,
  rule_applies (mk_head m rest r) p = eval_matchcond m p && rule_applies_walk rest p.
Proof.
  intros m rest r p. unfold rule_applies.
  cbn [r_body rule_applies_walk]. reflexivity.
Qed.

(** The value-merge correctness on a two-rule prefix.  Given the disjunction
    certificate ([Hml] same field loads, [Hev] value test is the [orb]) the merged
    rule [mk_head m12 rest r1] replaces the adjacent pair and preserves the
    verdict.  [r2] must be [mk_head m2 rest r1] — i.e. agree with [r1] on every
    field BUT the head value — which is exactly nft's [rules_eq] eligibility. *)
Theorem eval_rules_value_merge : forall m1 m2 m12 rest r1 rest2 p,
  (forall q, match_loadable m12 q = match_loadable m1 q) ->
  (forall q, match_loadable m12 q = match_loadable m2 q) ->
  (forall q, eval_matchcond m12 q = orb (eval_matchcond m1 q) (eval_matchcond m2 q)) ->
  eval_rules (mk_head m12 rest r1 :: rest2) p
    = eval_rules (mk_head m1 rest r1 :: mk_head m2 rest r1 :: rest2) p.
Proof.
  intros m1 m2 m12 rest r1 rest2 p Hml1 Hml2 Hev.
  apply eval_rules_merge2.
  - (* rule_loadable r12 = rule_loadable r1 *)
    rewrite !rule_loadable_mk_head. rewrite Hml1. reflexivity.
  - rewrite !rule_loadable_mk_head. rewrite Hml2. reflexivity.
  - rewrite !outcome_mk_head. reflexivity.
  - rewrite !outcome_mk_head. reflexivity.
  - rewrite !rule_applies_mk_head. rewrite Hev.
    rewrite Bool.andb_orb_distrib_l. reflexivity.
Qed.

(** ** A concrete, env-free disjunction certificate: contiguous single-byte ranges.

    The general certificate above needs a concrete [m12] whose value test is the
    [orb] of two adjacent matches.  The cleanest case that needs NO new syntax
    constructor and NO runtime set declaration is a CONTIGUOUS RANGE: two adjacent
    rules `f >= lo, f <= mid` and `f >= mid+1, f <= hi` over the SAME single-byte
    field collapse to one `f >= lo, f <= hi` — exactly the range form `nft -o`
    coalesces a contiguous anonymous set into (`{ lo-mid, (mid+1)-hi }` => `lo-hi`).

    For SINGLE-BYTE operands ([lo],[mid],[hi] each one byte), [data_le [a] [b]] is
    [Nat.leb a b] (after the equal-head test collapses), so contiguity is pure
    [Nat] arithmetic: every byte [x] is in [lo,hi] iff it is in [lo,mid] or in
    [mid+1,hi], provided [lo <= mid < hi] (and [hi] within byte range is
    automatic).  We prove this for the full-byte value the field exposes; the
    one-byte width keeps it env-free and decidable. *)

Lemma data_le_byte : forall a b, data_le [a] [b] = Nat.leb a b.
Proof.
  intros a b. cbn [data_le]. destruct (Nat.eqb a b) eqn:E.
  - apply Nat.eqb_eq in E; subst. cbn. symmetry. apply Nat.leb_le. lia.
  - reflexivity.
Qed.

(** The single-byte contiguity disjunction on the raw range test. *)
Lemma range_byte_split : forall lo mid hi x,
  lo <= mid -> mid < hi ->
  (andb (data_le [lo] [x]) (data_le [x] [hi]))
  = orb (andb (data_le [lo] [x]) (data_le [x] [mid]))
        (andb (data_le [S mid] [x]) (data_le [x] [hi])).
Proof.
  intros lo mid hi x Hlm Hmh.
  rewrite !data_le_byte.
  destruct (Nat.leb lo x) eqn:Elo; cbn [andb];
    [ apply Nat.leb_le in Elo
    | (* lo > x: the first disjunct's [lo<=x] conjunct is false; the [S mid]
         disjunct needs [S mid <= x], but [lo <= mid < S mid] and [x < lo] make
         it false too *)
      apply Nat.leb_nle in Elo; cbn [orb];
      destruct (Nat.leb (S mid) x) eqn:ESm; cbn [andb]; [|reflexivity];
      apply Nat.leb_le in ESm; exfalso; lia ].
  destruct (Nat.leb x hi) eqn:Exh; destruct (Nat.leb x mid) eqn:Exm;
    destruct (Nat.leb (S mid) x) eqn:ESmx; cbn [orb andb];
    try reflexivity;
    repeat (match goal with
            | H : Nat.leb _ _ = true |- _ => apply Nat.leb_le in H
            | H : Nat.leb _ _ = false |- _ => apply Nat.leb_nle in H
            end); lia.
Qed.

(** ** Decidable equality for whole rules (for the adjacent-duplicate pass).

    [nft]'s pipeline removes redundant rules; the simplest faithful instance is
    CONSECUTIVE-DUPLICATE-RULE elimination — two byte-for-byte identical adjacent
    rules `r; r` are equivalent to a single `r` (the second can never fire after
    the first on any packet for which the first is terminal, and is a no-op
    otherwise; this is the [r1=r2=r12] instance of [eval_rules_merge2]).  It needs
    decidable rule equality, built bottom-up from the component [eq_dec]s (a single
    monolithic [decide equality] on [rule] is intractable, so we layer it). *)

Definition verdict_eq_dec (a b : verdict) : {a = b} + {a <> b}.
Proof. decide equality; (apply Nat.eq_dec || apply Bool.bool_dec || apply String.string_dec). Defined.

Definition vsrc_eq_dec (a b : vsrc) : {a = b} + {a <> b}.
Proof.
  decide equality;
    repeat first
      [ apply Nat.eq_dec | apply Bool.bool_dec | apply String.string_dec
      | apply field_eq_dec | apply transform_eq_dec
      | apply (list_eq_dec Nat.eq_dec)
      | apply (list_eq_dec transform_eq_dec)
      | apply (list_eq_dec field_eq_dec)
      | decide equality ].
Defined.

Definition stmt_eq_dec (a b : stmt) : {a = b} + {a <> b}.
Proof.
  decide equality;
    repeat first
      [ apply Nat.eq_dec | apply Bool.bool_dec | apply String.string_dec
      | apply field_eq_dec | apply transform_eq_dec | apply vsrc_eq_dec
      | apply (list_eq_dec Nat.eq_dec)
      | apply (list_eq_dec field_eq_dec)
      | apply (list_eq_dec (fun x y => prod_eqdec' x y))
      | decide equality ].
Defined.

Definition vmap_spec_eq_dec (a b : vmap_spec) : {a = b} + {a <> b}.
Proof.
  decide equality;
    repeat first
      [ apply String.string_dec | apply (list_eq_dec field_eq_dec)
      | apply field_eq_dec | apply (list_eq_dec transform_eq_dec) | decide equality ].
Defined.

Definition nat_spec_eq_dec (a b : nat_spec) : {a = b} + {a <> b}.
Proof.
  decide equality;
    repeat first
      [ apply Nat.eq_dec | apply String.string_dec | apply vsrc_eq_dec
      | apply field_eq_dec | apply (list_eq_dec transform_eq_dec)
      | apply (list_eq_dec field_eq_dec)
      | apply (list_eq_dec Nat.eq_dec) | decide equality ].
Defined.

Definition tproxy_spec_eq_dec (a b : tproxy_spec) : {a = b} + {a <> b}.
Proof.
  decide equality;
    repeat first
      [ apply Nat.eq_dec | apply String.string_dec
      | apply (list_eq_dec Nat.eq_dec) | decide equality ].
Defined.

Definition fwd_spec_eq_dec (a b : fwd_spec) : {a = b} + {a <> b}.
Proof.
  decide equality;
    repeat first
      [ apply Nat.eq_dec | apply vsrc_eq_dec
      | apply (list_eq_dec Nat.eq_dec) | decide equality ].
Defined.

Definition queue_spec_eq_dec (a b : queue_spec) : {a = b} + {a <> b}.
Proof.
  decide equality;
    repeat first
      [ apply Nat.eq_dec | apply Bool.bool_dec | apply vsrc_eq_dec
      | apply (list_eq_dec Nat.eq_dec) | decide equality ].
Defined.

Definition body_item_eq_dec (a b : body_item) : {a = b} + {a <> b}.
Proof. decide equality; (apply matchcond_eq_dec || apply stmt_eq_dec). Defined.

Definition rule_eq_dec (a b : rule) : {a = b} + {a <> b}.
Proof.
  decide equality;
    repeat first
      [ apply (list_eq_dec body_item_eq_dec) | apply verdict_eq_dec
      | apply (list_eq_dec stmt_eq_dec)
      | (apply option_eq_dec; [ .. ]) | decide equality ];
    try (apply vmap_spec_eq_dec || apply nat_spec_eq_dec || apply tproxy_spec_eq_dec
         || apply fwd_spec_eq_dec || apply queue_spec_eq_dec).
Defined.

(** ** Pass: consecutive-duplicate-rule elimination.

    Drop the SECOND of two byte-for-byte identical adjacent rules.  This is the
    [r1 = r2] instance of [eval_rules_merge2] (with [r12 = r1]): the three
    obligations hold by [Coq] reflexivity once [r1 = r2], so removing the duplicate
    is verdict-preserving on every packet.  [nft -o] performs the same collapse (a
    run of identical rules folds to one). *)
Fixpoint dedup_adj (rs : list rule) : list rule :=
  match rs with
  | r1 :: (r2 :: _) as rest =>
      if rule_eq_dec r1 r2 then dedup_adj rest else r1 :: dedup_adj rest
  | _ => rs
  end.

Lemma eval_rules_drop_dup : forall r rest p,
  eval_rules (r :: rest) p = eval_rules (r :: r :: rest) p.
Proof.
  intros r rest p. apply eval_rules_merge2; try reflexivity.
  rewrite Bool.orb_diag. reflexivity.
Qed.

Lemma eval_rules_dedup_adj : forall rs p, eval_rules (dedup_adj rs) p = eval_rules rs p.
Proof.
  (* induction on length: both recursive calls are on the strictly shorter tail
     [r2 :: rest] of [r1 :: r2 :: rest]. *)
  intro rs. remember (length rs) as n eqn:Hn. revert rs Hn.
  induction n as [n IH] using (well_founded_induction Nat.lt_wf_0); intros rs Hn p.
  destruct rs as [| r1 [| r2 rest]]; try reflexivity.
  cbn [dedup_adj]. destruct (rule_eq_dec r1 r2) as [Heq | Hne].
  - (* drop the duplicate [r2 = r1]: dedup_adj (r2::rest), then re-insert via drop_dup *)
    rewrite (IH (length (r2 :: rest))) with (rs := r2 :: rest); try reflexivity.
    + subst r2. apply eval_rules_drop_dup.
    + subst n. cbn [length]. lia.
  - cbn [eval_rules].
    rewrite (IH (length (r2 :: rest))) with (rs := r2 :: rest); try reflexivity.
    subst n. cbn [length]. lia.
Qed.

(** ** Guarded value-merge into a contiguous range (concrete certificate).

    The value-merge `f lo-mid, f (mid+1)-hi  =>  f lo-hi` is the disjunction
    certificate instantiated with [m1 = MRange f false [lo] [mid]],
    [m2 = MRange f false [S mid] [hi]], [m12 = MRange f false [lo] [hi]].  Its
    soundness needs the single-byte contiguity [range_byte_split], which holds when
    the field's loaded value is ONE byte — the GUARD [length (field_value f p) = 1].
    (A multi-byte field would compare its bound as a prefix, for which a contiguous
    two-element set is NOT a single range; hence the guard, exactly the kind of
    side-condition nft's own range-coalescing assumes on a fixed-width selector.)

    We package the certificate per-packet under the guard; the abstract
    [eval_rules_value_merge] then yields the rule-list rewrite. *)
Lemma mrange_byte_loadable : forall f neg lo hi p,
  match_loadable (MRange f neg lo hi) p = field_loadable f p.
Proof. reflexivity. Qed.

Lemma mrange_byte_disjunction : forall f lo mid hi p,
  lo <= mid -> mid < hi ->
  length (field_value f p) = 1 ->
  eval_matchcond (MRange f false [lo] [hi]) p
  = orb (eval_matchcond (MRange f false [lo] [mid]) p)
        (eval_matchcond (MRange f false [S mid] [hi]) p).
Proof.
  intros f lo mid hi p Hlm Hmh Hlen.
  unfold eval_matchcond, eval_matchcond_body. cbn [match_loadable].
  destruct (field_loadable f p) eqn:Hld; cbn [andb];
    [| reflexivity ].
  unfold eval_range. cbn [andb].
  (* field_value f p is a single byte [x] *)
  destruct (field_value f p) as [| x [| ? ?]] eqn:Ev; cbn [length] in Hlen;
    try discriminate Hlen.
  exact (range_byte_split lo mid hi x Hlm Hmh).
Qed.

(** The two adjacent single-byte-range rules collapse to one, on every packet for
    which the merged field is single-byte (the guard, as a per-packet hypothesis).
    [rest2] is the remainder of the chain; [r1] supplies the shared verdict/end. *)
Theorem eval_rules_range_value_merge : forall f lo mid hi rest r1 rest2 p,
  lo <= mid -> mid < hi ->
  length (field_value f p) = 1 ->
  eval_rules (mk_head (MRange f false [lo] [hi]) rest r1 :: rest2) p
  = eval_rules (mk_head (MRange f false [lo] [mid]) rest r1
                :: mk_head (MRange f false [S mid] [hi]) rest r1 :: rest2) p.
Proof.
  intros f lo mid hi rest r1 rest2 p Hlm Hmh Hlen.
  (* the three certificate hypotheses are needed only at THIS packet p, but
     [eval_rules_value_merge] quantifies them over all q.  We instead apply the
     abstract [eval_rules_merge2] directly, discharging its obligations at p. *)
  apply eval_rules_merge2.
  - rewrite !rule_loadable_mk_head. reflexivity.
  - rewrite !rule_loadable_mk_head. reflexivity.
  - rewrite !outcome_mk_head. reflexivity.
  - rewrite !outcome_mk_head. reflexivity.
  - rewrite !rule_applies_mk_head.
    rewrite (mrange_byte_disjunction f lo mid hi p Hlm Hmh Hlen).
    rewrite Bool.andb_orb_distrib_l. reflexivity.
Qed.

(** ** The combined optimizer with consolidation, and its correctness.

    [optimize_chain2] runs the existing verdict-preserving pipeline
    ([optimize_chain]: dedup/simplify/prune/dce) and then the [nft -o]
    consecutive-duplicate-rule consolidation ([dedup_adj]).  Both stages preserve
    [eval_chain], so the composite does too — axiom-free, by reusing
    [optimize_chain_correct] and [eval_rules_dedup_adj]. *)
Definition optimize_chain2 (c : chain) : chain :=
  {| c_policy := c_policy (optimize_chain c);
     c_rules  := dedup_adj (c_rules (optimize_chain c)) |}.

Theorem optimize_chain2_correct : forall c p,
  eval_chain (optimize_chain2 c) p = eval_chain c p.
Proof.
  intros c p. unfold eval_chain, optimize_chain2. cbn [c_rules c_policy].
  rewrite eval_rules_dedup_adj.
  change (match eval_rules (c_rules (optimize_chain c)) p with
          | Some v => v | None => c_policy (optimize_chain c) end)
    with (eval_chain (optimize_chain c) p).
  apply optimize_chain_correct.
Qed.
