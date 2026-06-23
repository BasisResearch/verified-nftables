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
    nat/…/after).

    It then delivers the HEADLINE value->anonymous-SET pass as an EXECUTABLE
    table-level rewrite ([optimize_rules_sets] / [optimize_chain_sets]): on an
    adjacent pair `tcp dport 22 accept` / `tcp dport 80 accept` it mints a fresh
    `__setN`, emits its element declaration [(22,22);(80,80)] into [sd_sets], and
    rewrites the pair into ONE `MConcatSet [dport] false __setN accept` — exactly
    what `nft -o` consolidates into `tcp dport { 22, 80 } accept` (the anonymous set
    interned by name).  [optimize_chain_sets_correct] proves it verdict-preserving
    end-to-end over the table semantics WITH the synthesised set in scope, via the
    disjunction certificate [concat_set_two_points] + [eval_rules_merge2], guarded
    by a fixed-width-field side-condition ([field_fixed_len]) and a fresh-name
    discipline ([setname_inj]).  Every theorem is axiom-free (Print Assumptions:
    Closed under the global context).

    [optimize_chain2] (= the existing pipeline then [dedup_adj]) remains as the
    consecutive-duplicate pass.  NOTE on fidelity: the earlier contiguous-range
    certificate [eval_rules_range_value_merge] models `6,7 => 6-7` as a RANGE, but
    `nft -o` actually emits a discrete SET `{ 6, 7 }`; the value->set pass above is
    the faithful consolidation and emits the discrete elements. *)

From Stdlib Require Import Ascii String.
From Stdlib Require Import List PeanoNat Bool Lia Wellfounded Arith.Wf_nat.
From Nft Require Import Bytes Packet Verdict Syntax Bytecode Semantics Optimize.
Import ListNotations.
Local Open Scope nat_scope.

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

(** ** The HEADLINE [nft -o] pass: value -> anonymous SET, as an executable
    table-level rewrite synthesising a real [__setN] declaration.

    [nft -o] consolidates a run of adjacent rules that are identical except in the
    right-hand VALUE of one selector, with the SAME verdict, into ONE rule whose
    head matches an anonymous SET of those values:

        tcp dport 22 accept              => tcp dport { 22, 80 } accept
        tcp dport 80 accept

    An anonymous set is, here and in real nftables, an INTERNED NAMED set: the
    parser ([nft_lower.ml intern_anon_set]) mints a fresh `__setN`, pushes its
    elements onto the table's set declarations, and lowers the inline `{ … }` to
    [MConcatSet ([f], neg, "__setN")] — a reference BY NAME, membership read at run
    time from [e_set (pkt_env p) "__setN"].  So this pass needs NO new constructor:
    it lifts the merge to the TABLE / [set_decls] level, minting `__setN` with a
    fresh counter, reusing the EXISTING named-set machinery.

    Fidelity note: [nft -o] NEVER coalesces contiguous values into a range — it
    keeps a discrete SET `{ 22, 23, 24 }`; this pass emits exactly [(v1,v1);(v2,v2)]. *)

Lemma data_in_iv_point : forall x v, data_in_iv x (v, v) = data_eqb x v.
Proof.
  intros x v. unfold data_in_iv. cbn [fst snd].
  rewrite data_le_antisym. apply data_eqb_sym.
Qed.

Lemma concat_set_two_points : forall f v1 v2 name q,
  e_set (pkt_env q) name = [(v1, v1); (v2, v2)] ->
  (field_loadable f q = true -> length (field_value f q) = length v1) ->
  (field_loadable f q = true -> length (field_value f q) = length v2) ->
  eval_matchcond (MConcatSet [f] false name) q
  = orb (eval_matchcond (MCmp f CEq v1) q) (eval_matchcond (MCmp f CEq v2) q).
Proof.
  intros f v1 v2 name q Hset H1 H2.
  unfold eval_matchcond, eval_matchcond_body.
  cbn [match_loadable fields_loadable forallb].
  rewrite Bool.andb_true_r.
  destruct (field_loadable f q) eqn:Hld; cbn [andb]; [| reflexivity ].
  specialize (H1 eq_refl). specialize (H2 eq_refl).
  cbn [map]. rewrite concat_set_mem_single. unfold set_mem. rewrite Hset.
  cbn [existsb]. rewrite Bool.orb_false_r.
  rewrite !data_in_iv_point.
  unfold eval_cmp.
  rewrite <- H1, <- H2, !List.firstn_all.
  reflexivity.
Qed.

(** A loaded PAYLOAD field reads exactly its [len] bytes (the kernel's
    [skb_copy_bits] of [priv->len], gated by [read_payload_ok]). *)
Lemma payload_loaded_len : forall b off len p,
  read_payload_ok b off len p = true ->
  length (read_payload b off len p) = len.
Proof.
  intros b off len p H. unfold read_payload_ok in H.
  apply Bool.andb_true_iff in H as [_ Hfit].
  apply Bool.negb_true_iff, Nat.ltb_ge in Hfit.
  unfold read_payload, slice.
  destruct b; cbn [base_bytes] in Hfit;
    rewrite List.length_firstn, List.length_skipn, Nat.min_l by lia; reflexivity.
Qed.

(** *** Fixed-width fields the set-merge may target.

    The merge is sound only on a field whose loaded width is CONSTANT and equal to
    the matched value's width (else [MCmp]'s prefix equality differs from the set's
    full-width membership — e.g. a wildcard `iifname "eth*"`).  [field_fixed_len]
    returns [Some len] for the PAYLOAD-backed fixed-width fields (ports, addresses,
    protocol, ttl, … — the overwhelming majority of nft -o's set-merge targets). *)
Definition field_fixed_len (f : field) : option nat :=
  match field_load f with
  | LPayload _ _ len => Some len
  | _ => None
  end.

Lemma field_fixed_len_loaded : forall f len q,
  field_fixed_len f = Some len ->
  field_loadable f q = true ->
  length (field_value f q) = len.
Proof.
  intros f len q Hfx Hld. unfold field_fixed_len in Hfx.
  unfold field_loadable, field_value in *.
  destruct (field_load f) eqn:Efl; try discriminate.
  inversion Hfx; subst.
  cbn [do_load]. apply payload_loaded_len. exact Hld.
Qed.

(** Unary fresh-name rendering; the EXACT spelling is irrelevant to fidelity (an
    anonymous set is rendered by its CONTENTS `{ … }`, never by its internal name),
    so the proof only needs INJECTIVITY, which a length-[n] string gives. *)
Fixpoint string_of_nat (n : nat) : String.string :=
  match n with
  | O => String.EmptyString
  | S k => String.String "I"%char (string_of_nat k)
  end.

Definition setname (n : nat) : String.string :=
  String.append "__set"%string (string_of_nat n).

Lemma string_of_nat_inj : forall a b, string_of_nat a = string_of_nat b -> a = b.
Proof.
  induction a as [| a IH]; intros [| b] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H. f_equal. apply IH. exact H.
Qed.

Lemma setname_inj : forall a b, setname a = setname b -> a = b.
Proof.
  intros a b H. unfold setname in H.
  apply string_of_nat_inj. cbn in H. repeat (injection H as H). exact H.
Qed.

(* Keep [setname] folded under [cbn]/[simpl] so freshness lookups reason about it
   abstractly (only its injectivity matters, [setname_inj]). *)
Global Opaque setname.

(** Recognise a value-merge-eligible head [BMatch (MCmp f CEq v) :: rest]. *)
Definition head_value (r : rule) : option (field * data * list body_item) :=
  match r_body r with
  | BMatch (MCmp f CEq v) :: rest => Some (f, v, rest)
  | _ => None
  end.

(** Two rules form an eligible adjacent value-merge pair iff their heads are
    [MCmp f CEq v1] / [MCmp f CEq v2] over the SAME fixed-width field [f], with the
    SAME tail [rest], the SAME end-fields, and [v1 <> v2].  The fixed-width guard
    ([field_fixed_len f1 = Some len = len v1 = len v2]) is precisely what makes the
    set membership equal the disjunction of the two point matches. *)
Definition value_merge_pair (r1 r2 : rule) : option (field * data * data * list body_item) :=
  match head_value r1, head_value r2 with
  | Some (f1, v1, rest1), Some (f2, v2, rest2) =>
      if field_eq_dec f1 f2 then
      if list_eq_dec body_item_eq_dec rest1 rest2 then
      if list_eq_dec Nat.eq_dec v1 v2 then None
      else
      match field_fixed_len f1 with
      | Some len =>
        if Nat.eq_dec len (length v1) then
        if Nat.eq_dec len (length v2) then
        (* compare the two rules with a COMMON head ([v1] for both), so the test
           checks ONLY that r1 and r2 agree on every END field (verdict/vmap/nat/…)
           — the heads legitimately differ in their value. *)
        if rule_eq_dec (mk_head (MCmp f1 CEq v1) rest1 r1)
                       (mk_head (MCmp f1 CEq v1) rest1 r2)
        then Some (f1, v1, v2, rest1)
        else None
        else None else None
      | None => None
      end
      else None else None
  | _, _ => None
  end.

Fixpoint optimize_rules_sets (n : nat) (d : set_decls) (rs : list rule)
  : nat * set_decls * list rule :=
  match rs with
  | r1 :: ((r2 :: rest) as tl) =>
      match value_merge_pair r1 r2 with
      | Some (f, v1, v2, body) =>
          let name := setname n in
          let d' := {| sd_sets := (name, [(v1, v1); (v2, v2)]) :: sd_sets d;
                       sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} in
          let merged := mk_head (MConcatSet [f] false name) body r1 in
          let '(n'', d'', rest') := optimize_rules_sets (S n) d' rest in
          (n'', d'', merged :: rest')
      | None =>
          let '(n'', d'', tl') := optimize_rules_sets n d tl in
          (n'', d'', r1 :: tl')
      end
  | _ => (n, d, rs)
  end.

(** One-step unfolding equation on a cons-cons input (so the recursive calls stay
    folded; [cbn] would over-reduce them on the abstract tail). *)
Lemma optimize_rules_sets_cons2 : forall n d r1 r2 rest,
  optimize_rules_sets n d (r1 :: r2 :: rest) =
  match value_merge_pair r1 r2 with
  | Some (f, v1, v2, body) =>
      let name := setname n in
      let d' := {| sd_sets := (name, [(v1, v1); (v2, v2)]) :: sd_sets d;
                   sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} in
      let merged := mk_head (MConcatSet [f] false name) body r1 in
      let '(n'', d'', rest') := optimize_rules_sets (S n) d' rest in
      (n'', d'', merged :: rest')
  | None =>
      let '(n'', d'', tl') := optimize_rules_sets n d (r2 :: rest) in
      (n'', d'', r1 :: tl')
  end.
Proof. reflexivity. Qed.

Definition optimize_chain_sets (n : nat) (d : set_decls) (c : chain)
  : nat * set_decls * chain :=
  let '(n', d', rs') := optimize_rules_sets n d (c_rules c) in
  (n', d', {| c_policy := c_policy c; c_rules := rs' |}).

(** A declared set's lookup peels [assoc_str]. *)
Lemma e_set_cons : forall base name elems d m,
  m <> name ->
  e_set (env_with_sets base
            {| sd_sets := (name, elems) :: sd_sets d;
               sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |}) m
  = e_set (env_with_sets base d) m.
Proof.
  intros base name elems d m Hne.
  rewrite !e_set_declared. cbn [sd_sets assoc_str].
  destruct (String.eqb m name) eqn:E.
  - apply String.eqb_eq in E. contradiction.
  - reflexivity.
Qed.

(** ** Env-irrelevance for CLEAN rules: adding fresh set declarations cannot change
    the verdict of a rule that reads no named set/vmap/map. *)
Definition mc_clean (m : matchcond) : bool :=
  match m with
  | MConcatSet _ _ _ | MSetT _ _ _ _ | MConcatSetT _ _ _ => false
  | _ => true
  end.

Definition bi_clean (b : body_item) : bool :=
  match b with BMatch m => mc_clean m | BStmt _ => false end.

Definition rule_clean (r : rule) : bool :=
  forallb bi_clean (r_body r) &&
  match r_vmap r with Some _ => false | None => true end &&
  match r_nat r with Some _ => false | None => true end &&
  match r_tproxy r with Some _ => false | None => true end &&
  match r_fwd r with Some _ => false | None => true end &&
  match r_queue r with Some _ => false | None => true end &&
  match r_after r with [] => true | _ => false end.

Definition rules_clean (rs : list rule) : bool := forallb rule_clean rs.

Lemma do_load_env_with_sets : forall ld p base d1 d2,
  do_load ld (set_env p (env_with_sets base d1))
  = do_load ld (set_env p (env_with_sets base d2)).
Proof.
  intros ld p base d1 d2.
  unfold do_load, set_env, env_with_sets; cbn.
  destruct ld; try reflexivity; try (destruct k; reflexivity).
Qed.

Lemma field_value_env_with_sets : forall f p base d1 d2,
  field_value f (set_env p (env_with_sets base d1))
  = field_value f (set_env p (env_with_sets base d2)).
Proof. intros. unfold field_value. apply do_load_env_with_sets. Qed.

Lemma eval_matchcond_clean_env : forall m p base d1 d2,
  mc_clean m = true ->
  eval_matchcond m (set_env p (env_with_sets base d1))
  = eval_matchcond m (set_env p (env_with_sets base d2)).
Proof.
  intros m p base d1 d2 Hc.
  unfold eval_matchcond, eval_matchcond_body, match_loadable.
  destruct m; cbn in Hc; try discriminate;
    rewrite ?field_value_env_with_sets;
    repeat (match goal with
            | |- context[field_value ?f (set_env p (env_with_sets base d1))] =>
                rewrite (field_value_env_with_sets f p base d1 d2)
            end);
    reflexivity.
Qed.

Lemma rule_applies_clean_env : forall body p base d1 d2,
  forallb bi_clean body = true ->
  rule_applies_walk body (set_env p (env_with_sets base d1))
  = rule_applies_walk body (set_env p (env_with_sets base d2)).
Proof.
  induction body as [| b body IH]; intros p base d1 d2 Hc; [reflexivity|].
  cbn [forallb] in Hc. apply Bool.andb_true_iff in Hc as [Hb Hrest].
  destruct b as [m | s]; cbn [bi_clean] in Hb; [| discriminate].
  cbn [rule_applies_walk].
  rewrite (eval_matchcond_clean_env m p base d1 d2 Hb).
  rewrite (IH p base d1 d2 Hrest). reflexivity.
Qed.

Lemma body_item_loadable_clean_env : forall b p base d1 d2,
  bi_clean b = true ->
  body_item_loadable b (set_env p (env_with_sets base d1))
  = body_item_loadable b (set_env p (env_with_sets base d2)).
Proof.
  intros b p base d1 d2 Hc. destruct b as [m | s]; cbn [bi_clean] in Hc; [| discriminate].
  cbn [body_item_loadable match_loadable].
  destruct m; cbn in Hc; try discriminate;
    cbn [match_loadable];
    rewrite ?field_value_env_with_sets; try reflexivity;
    unfold fields_loadable, field_loadable; reflexivity.
Qed.

Lemma body_synproxy_stops_clean : forall body p,
  forallb bi_clean body = true ->
  body_synproxy_stops body p = false.
Proof.
  induction body as [| b body IH]; intros p Hc; [reflexivity|].
  cbn [forallb] in Hc. apply Bool.andb_true_iff in Hc as [Hb Hrest].
  destruct b as [m | s]; cbn [bi_clean] in Hb; [| discriminate].
  unfold body_synproxy_stops in *. cbn [existsb]. apply (IH p Hrest).
Qed.

Lemma body_has_notrack_clean : forall body,
  forallb bi_clean body = true -> body_has_notrack body = false.
Proof.
  induction body as [| b body IH]; intros Hc; [reflexivity|].
  cbn [forallb] in Hc. apply Bool.andb_true_iff in Hc as [Hb Hrest].
  destruct b as [m | s]; cbn [bi_clean] in Hb; [| discriminate].
  cbn [body_has_notrack]. apply (IH Hrest).
Qed.

Lemma body_loadable_clean_env : forall body p base d1 d2,
  forallb bi_clean body = true ->
  body_loadable_walk body (set_env p (env_with_sets base d1))
  = body_loadable_walk body (set_env p (env_with_sets base d2)).
Proof.
  intros body p base d1 d2 Hc.
  rewrite !body_loadable_walk_no_synproxy by (apply body_synproxy_stops_clean; exact Hc).
  revert Hc. induction body as [| b body IH]; intro Hc; [reflexivity|].
  cbn [forallb] in Hc. apply Bool.andb_true_iff in Hc as [Hb Hrest].
  cbn [forallb].
  rewrite (body_item_loadable_clean_env b p base d1 d2 Hb).
  rewrite (IH Hrest). reflexivity.
Qed.

Lemma rule_clean_env : forall r p base d1 d2,
  rule_clean r = true ->
  rule_loadable r (set_env p (env_with_sets base d1))
    = rule_loadable r (set_env p (env_with_sets base d2))
  /\ rule_applies r (set_env p (env_with_sets base d1))
    = rule_applies r (set_env p (env_with_sets base d2))
  /\ outcome r (set_env p (env_with_sets base d1))
    = outcome r (set_env p (env_with_sets base d2)).
Proof.
  intros r p base d1 d2 Hc.
  unfold rule_clean in Hc.
  apply Bool.andb_true_iff in Hc as [Hc Hafter].
  apply Bool.andb_true_iff in Hc as [Hc Hqueue].
  apply Bool.andb_true_iff in Hc as [Hc Hfwd].
  apply Bool.andb_true_iff in Hc as [Hc Htproxy].
  apply Bool.andb_true_iff in Hc as [Hc Hnat].
  apply Bool.andb_true_iff in Hc as [Hbody Hvmap].
  destruct (r_vmap r) eqn:Hv; [discriminate|].
  destruct (r_nat r) eqn:Hn; [discriminate|].
  destruct (r_tproxy r) eqn:Ht; [discriminate|].
  destruct (r_fwd r) eqn:Hf; [discriminate|].
  destruct (r_queue r) eqn:Hq; [discriminate|].
  destruct (r_after r) eqn:Ha; [| discriminate].
  assert (Hns : forall pp, body_synproxy_stops (r_body r) pp = false)
    by (intro; apply body_synproxy_stops_clean; exact Hbody).
  assert (Hnt : body_has_notrack (r_body r) = false)
    by (apply body_has_notrack_clean; exact Hbody).
  repeat split.
  - unfold rule_loadable.
    rewrite (body_loadable_clean_env _ p base d1 d2 Hbody).
    rewrite !Hns. unfold body_thread. rewrite Hnt.
    unfold end_loadable. rewrite Hv.
    unfold tail_loadable, terminal_loadable, terminal_outcome.
    rewrite Hn, Ht, Hf, Hq, Ha. reflexivity.
  - unfold rule_applies. apply (rule_applies_clean_env _ p base d1 d2 Hbody).
  - unfold outcome. rewrite !Hns.
    unfold body_thread. rewrite Hnt.
    unfold outcome_core, terminal_outcome. rewrite Hv, Hn, Ht, Hf, Hq, Ha.
    reflexivity.
Qed.

Lemma eval_rules_clean_env : forall rs p base d1 d2,
  rules_clean rs = true ->
  eval_rules rs (set_env p (env_with_sets base d1))
  = eval_rules rs (set_env p (env_with_sets base d2)).
Proof.
  induction rs as [| r rs IH]; intros p base d1 d2 Hc; [reflexivity|].
  cbn [rules_clean forallb] in Hc. apply Bool.andb_true_iff in Hc as [Hr Hrest].
  destruct (rule_clean_env r p base d1 d2 Hr) as [Hl [Ha Ho]].
  cbn [eval_rules]. rewrite Hl, Ha, Ho.
  rewrite (IH p base d1 d2 Hrest). reflexivity.
Qed.

Lemma eval_rules_cons_cong : forall r rest1 rest2 p,
  eval_rules rest1 p = eval_rules rest2 p ->
  eval_rules (r :: rest1) p = eval_rules (r :: rest2) p.
Proof.
  intros r rest1 rest2 p H. cbn [eval_rules].
  destruct (rule_loadable r p && rule_applies r p); [| exact H].
  destruct (outcome r p) as [v |]; [| exact H].
  destruct (terminal v); [reflexivity | exact H].
Qed.

(** ** Freshness bookkeeping: [optimize_rules_sets] only PREPENDS entries keyed by
    [setname k] with [n <= k < n'], so on an UN-minted name the augmented [sd_sets]
    agrees with the input. *)
Lemma optimize_rules_sets_assoc_stable : forall rs n d n' d' rs' nm X,
  optimize_rules_sets n d rs = (n', d', rs') ->
  (forall k, n <= k -> nm <> setname k) ->
  assoc_str nm (sd_sets d') X = assoc_str nm (sd_sets d) X.
Proof.
  induction rs as [rs H0] using (induction_ltof1 _ (@length rule)).
  intros n d n' d' rs' nm X H Hnm.
  destruct rs as [| r1 [| r2 rest] ].
  - cbn in H. inversion H; subst; reflexivity.
  - cbn in H. inversion H; subst; reflexivity.
  - rewrite optimize_rules_sets_cons2 in H. cbv zeta in H.
    destruct (value_merge_pair r1 r2) as [[[[f v1] v2] body] |] eqn:Evm.
    + destruct (optimize_rules_sets (S n)
                  {| sd_sets := (setname n, [(v1,v1);(v2,v2)]) :: sd_sets d;
                     sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest)
        as [[m'' dd''] rr''] eqn:Erec.
      inversion H; subst n' d' rs'. clear H.
      erewrite (H0 rest); [ | unfold ltof; cbn; lia | exact Erec | ].
      * cbn [sd_sets assoc_str].
        destruct (String.eqb nm (setname n)) eqn:Eqn.
        -- apply String.eqb_eq in Eqn. exfalso. apply (Hnm n); [lia | exact Eqn].
        -- reflexivity.
      * intros k Hk. apply Hnm. lia.
    + destruct (optimize_rules_sets n d (r2 :: rest)) as [[m'' dd''] rr''] eqn:Erec.
      inversion H. subst n' d' rs'. clear H.
      eapply (H0 (r2 :: rest)); [ unfold ltof; cbn; lia | exact Erec | exact Hnm ].
Qed.

(** When a merge fires, the two input rules are EXACTLY the canonical shells, and
    the field is fixed-width — so the rewrite matches the value-merge certificate. *)
Lemma value_merge_pair_shape : forall r1 r2 f v1 v2 body,
  value_merge_pair r1 r2 = Some (f, v1, v2, body) ->
  r1 = mk_head (MCmp f CEq v1) body r1 /\
  r2 = mk_head (MCmp f CEq v2) body r1 /\
  field_fixed_len f = Some (length v1) /\
  field_fixed_len f = Some (length v2).
Proof.
  intros r1 r2 f v1 v2 body H. unfold value_merge_pair in H.
  destruct (head_value r1) as [[[f1 w1] rest1] |] eqn:H1; [| discriminate].
  destruct (head_value r2) as [[[f2 w2] rest2] |] eqn:H2; [| discriminate].
  unfold head_value in H1, H2.
  destruct (r_body r1) as [| [m1 | s1] b1] eqn:Eb1; try discriminate.
  destruct m1 as [ | | | | f1' op1 v1' | | | | | | | | ]; try discriminate.
  destruct op1; try discriminate. inversion H1; subst f1 w1 rest1.
  destruct (r_body r2) as [| [m2 | s2] b2] eqn:Eb2; try discriminate.
  destruct m2 as [ | | | | f2' op2 v2' | | | | | | | | ]; try discriminate.
  destruct op2; try discriminate. inversion H2; subst f2 w2 rest2.
  destruct (field_eq_dec f1' f2') as [Ef | ]; [| discriminate]. subst f2'.
  destruct (list_eq_dec body_item_eq_dec b1 b2) as [Erest | ]; [| discriminate]. subst b2.
  destruct (list_eq_dec Nat.eq_dec v1' v2') as [Ev | Hv]; [discriminate |].
  destruct (field_fixed_len f1') as [len |] eqn:Hfx; [| discriminate].
  destruct (Nat.eq_dec len (length v1')) as [Elen1 |]; [| discriminate].
  destruct (Nat.eq_dec len (length v2')) as [Elen2 |]; [| discriminate].
  destruct (rule_eq_dec (mk_head (MCmp f1' CEq v1') b1 r1)
                        (mk_head (MCmp f1' CEq v1') b1 r2)) as [Eshell |]; [| discriminate].
  inversion H; subst f v1 v2 body.
  assert (Hr1 : r1 = mk_head (MCmp f1' CEq v1') b1 r1).
  { unfold mk_head. rewrite <- Eb1. destruct r1; reflexivity. }
  split; [exact Hr1 |].
  split.
  - assert (Hr2 : r2 = mk_head (MCmp f1' CEq v2') b1 r2).
    { unfold mk_head. rewrite <- Eb2. destruct r2; reflexivity. }
    rewrite Hr2.
    (* r1, r2 agree on every END field (from Eshell), so swapping r2->r1 in the
       shell with head v2' is identity. *)
    unfold mk_head in Eshell |- *. injection Eshell as Eva Evm Ena Etp Efw Equ Eaf.
    rewrite Eva, Evm, Ena, Etp, Efw, Equ, Eaf. reflexivity.
  - split; rewrite Hfx; f_equal; congruence.
Qed.

(** *** The executable value->set merge, proved verdict-preserving END-TO-END over
    the table semantics with the synthesised set in scope, axiom-free.

    On clean rules with the minted names fresh for [d], the rewritten [rs'] under
    the augmented declarations [d'] yields the SAME verdict on every packet as [rs]
    under [d].  The merged head's `__setN` lookup resolves to its two point elements
    (freshness + injectivity); [concat_set_two_points] turns it into the [orb] of
    the two original point matches; [eval_rules_merge2] collapses the pair; the
    clean tail is env-irrelevant. *)
Theorem optimize_rules_sets_correct : forall rs n d n' d' rs' base p,
  optimize_rules_sets n d rs = (n', d', rs') ->
  rules_clean rs = true ->
  (forall k, n <= k -> ~ In (setname k) (map fst (sd_sets d))) ->
  eval_rules rs' (set_env p (env_with_sets base d'))
  = eval_rules rs  (set_env p (env_with_sets base d)).
Proof.
  induction rs as [rs H0] using (induction_ltof1 _ (@length rule)).
  intros n d n' d' rs' base p H Hclean Hfresh.
  destruct rs as [| r1 [| r2 rest] ].
  - cbn in H. inversion H; subst. reflexivity.
  - cbn in H. inversion H; subst. reflexivity.
  - rewrite optimize_rules_sets_cons2 in H. cbv zeta in H.
    destruct (value_merge_pair r1 r2) as [[[[f v1] v2] body] |] eqn:Evm.
    + (* MERGE fires *)
      set (dn := {| sd_sets := (setname n, [(v1,v1);(v2,v2)]) :: sd_sets d;
                    sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |}) in *.
      destruct (optimize_rules_sets (S n) dn rest) as [[m'' dd''] rr''] eqn:Erec.
      inversion H; subst n' d' rs'. clear H.
      cbn [rules_clean forallb] in Hclean.
      apply Bool.andb_true_iff in Hclean as [Hc1 Hclean].
      apply Bool.andb_true_iff in Hclean as [Hc2 Hcrest].
      (* the merged head reads setname n; resolve it in dd'' to its two points *)
      assert (Hlook : e_set (pkt_env (set_env p (env_with_sets base dd''))) (setname n)
                      = [(v1,v1);(v2,v2)]).
      { cbn [set_env pkt_env]. rewrite e_set_declared.
        erewrite (optimize_rules_sets_assoc_stable rest (S n) dn _ _ _ (setname n) _ Erec).
        - subst dn; cbn [sd_sets assoc_str]. rewrite String.eqb_refl. reflexivity.
        - intros k Hk Heq. apply setname_inj in Heq. lia. }
      (* the optimized tail equals the original tail under dn (by IH) *)
      assert (Htail : eval_rules rr'' (set_env p (env_with_sets base dd''))
                      = eval_rules rest (set_env p (env_with_sets base dn))).
      { eapply (H0 rest); [ unfold ltof; cbn; lia | exact Erec | exact Hcrest |].
        intros k Hk Hin. subst dn; cbn [sd_sets map] in Hin.
        destruct Hin as [Heq | Hin].
        - apply setname_inj in Heq. lia.
        - apply (Hfresh k); [lia | exact Hin]. }
      (* rest is clean: env-irrelevant, so rest@dn = rest@d *)
      assert (Hrestdn : eval_rules rest (set_env p (env_with_sets base dn))
                        = eval_rules rest (set_env p (env_with_sets base d)))
        by (apply eval_rules_clean_env; exact Hcrest).
      destruct (value_merge_pair_shape r1 r2 f v1 v2 body Evm)
        as [Hr1 [Hr2 [Hfx1 Hfx2]]].
      set (qd  := set_env p (env_with_sets base dd'')) in *.
      (* certificate at qd for the merged head vs the two point heads *)
      assert (Hcert : eval_matchcond (MConcatSet [f] false (setname n)) qd
              = orb (eval_matchcond (MCmp f CEq v1) qd) (eval_matchcond (MCmp f CEq v2) qd)).
      { apply concat_set_two_points.
        - exact Hlook.
        - intro Hld. apply (field_fixed_len_loaded f (length v1) qd Hfx1 Hld).
        - intro Hld. apply (field_fixed_len_loaded f (length v2) qd Hfx2 Hld). }
      (* the tail rr'' under dd'' equals the original rest under dd'' (clean tail) *)
      assert (Htail' : eval_rules rr'' qd = eval_rules rest qd).
      { rewrite Htail. unfold qd.
        rewrite (eval_rules_clean_env rest p base dn dd'' Hcrest). reflexivity. }
      (* Goal: eval_rules (merged::rr'') qd = eval_rules (r1::r2::rest) @d.
         Step 1: collapse merged head -> two point heads (merge2). *)
      transitivity (eval_rules (mk_head (MCmp f CEq v1) body r1
                      :: mk_head (MCmp f CEq v2) body r1 :: rr'') qd).
      { apply eval_rules_merge2.
        - rewrite !rule_loadable_mk_head. cbn [match_loadable fields_loadable forallb].
          rewrite Bool.andb_true_r. reflexivity.
        - rewrite !rule_loadable_mk_head. cbn [match_loadable fields_loadable forallb].
          rewrite Bool.andb_true_r. reflexivity.
        - rewrite !outcome_mk_head. reflexivity.
        - rewrite !outcome_mk_head. reflexivity.
        - rewrite !rule_applies_mk_head. rewrite Hcert.
          rewrite Bool.andb_orb_distrib_l. reflexivity. }
      (* Step 2: tail rr'' -> rest (Htail'), then point heads -> r1, r2 (Hr1,Hr2). *)
      transitivity (eval_rules (r1 :: r2 :: rest) qd).
      { rewrite <- Hr1, <- Hr2.
        apply eval_rules_cons_cong. apply eval_rules_cons_cong. exact Htail'. }
      (* Step 3: whole clean list at dd'' equals at d. *)
      unfold qd. apply eval_rules_clean_env.
      cbn [rules_clean forallb]. rewrite Hc1, Hc2, Hcrest. reflexivity.
    + (* NO merge at the head: recurse on the tail (r2::rest), keep r1 *)
      destruct (optimize_rules_sets n d (r2 :: rest)) as [[m'' dd''] rr''] eqn:Erec.
      inversion H; subst n' d' rs'. clear H.
      cbn [rules_clean forallb] in Hclean.
      apply Bool.andb_true_iff in Hclean as [Hc1 Hclean].
      assert (Htail : eval_rules rr'' (set_env p (env_with_sets base dd''))
                      = eval_rules (r2 :: rest) (set_env p (env_with_sets base d))).
      { eapply (H0 (r2 :: rest)); [ unfold ltof; cbn; lia | exact Erec | | exact Hfresh ].
        cbn [rules_clean forallb]. exact Hclean. }
      cbn [eval_rules].
      (* r1 is clean: its loadable/applies/outcome at dd'' equal those at d *)
      destruct (rule_clean_env r1 p base dd'' d Hc1) as [Hl [Ha Ho]].
      rewrite Hl, Ha, Ho. rewrite Htail. reflexivity.
Qed.

(** *** The CHAIN-level entry: pick a counter past every existing set name (here
    [0] suffices when the input table declares no [setname]-shaped name — the case
    for a freshly-parsed ruleset, whose anonymous sets are named `__setN` by the
    parser but whose EXPLICIT named sets are user identifiers, never a bare unary
    `__setIII…`).  We expose the general theorem with the freshness side-condition;
    [optimize_chain_sets_correct] is its [eval_chain] specialisation. *)
Theorem optimize_chain_sets_correct : forall n d c n' d' c' base p,
  optimize_chain_sets n d c = (n', d', c') ->
  rules_clean (c_rules c) = true ->
  (forall k, n <= k -> ~ In (setname k) (map fst (sd_sets d))) ->
  eval_chain c' (set_env p (env_with_sets base d'))
  = eval_chain c  (set_env p (env_with_sets base d)).
Proof.
  intros n d c n' d' c' base p H Hclean Hfresh.
  unfold optimize_chain_sets in H.
  destruct (optimize_rules_sets n d (c_rules c)) as [[m'' dd''] rr''] eqn:Erec.
  inversion H; subst n' d' c'. cbn [c_rules c_policy].
  unfold eval_chain. cbn [c_rules c_policy].
  rewrite (optimize_rules_sets_correct (c_rules c) n d m'' dd'' rr'' base p Erec Hclean Hfresh).
  reflexivity.
Qed.
