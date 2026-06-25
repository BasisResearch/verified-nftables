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
    interned by name).  Its correctness — verdict-preserving
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

(** ** Compact boolean equality on a rule's END fields (everything except the body).

    [value_merge_pair] compares two rules that share a freshly-built head/body
    ([mk_head m rest r1] vs [mk_head m rest r2]); such a comparison reduces to the
    END fields (verdict / vmap / nat / tproxy / fwd / queue / after) agreeing.
    Using the monolithic [rule_eq_dec] here forces extraction to inline the
    [list body_item]/[matchcond] decidable equality, which blows the extracted
    OCaml up to ~42 MB.  We instead test ONLY the END fields with a small boolean
    [rule_end_eqb], built from the (small) per-field [eq_dec]s, and prove it
    characterises the [mk_head] equality.  This is what the extracted optimizer
    actually runs. *)
Definition sumbool_eqb {A} (dec : forall x y : A, {x = y} + {x <> y}) (x y : A) : bool :=
  if dec x y then true else false.

Lemma sumbool_eqb_true_iff : forall A dec (x y : A),
  sumbool_eqb dec x y = true <-> x = y.
Proof.
  intros A dec x y. unfold sumbool_eqb. destruct (dec x y) as [E | Ne]; split;
    intro H; (exact E || discriminate H || (subst; exfalso; apply Ne; reflexivity) || reflexivity).
Qed.

Definition opt_eqb {A} (dec : forall x y : A, {x = y} + {x <> y})
  (x y : option A) : bool :=
  match x, y with
  | None, None => true
  | Some a, Some b => sumbool_eqb dec a b
  | _, _ => false
  end.

Lemma opt_eqb_true_iff : forall A dec (x y : option A),
  opt_eqb dec x y = true <-> x = y.
Proof.
  intros A dec [a|] [b|]; cbn; try (split; intro H; discriminate H || reflexivity).
  rewrite sumbool_eqb_true_iff. split; intro H; [subst; reflexivity | injection H; auto].
Qed.

Definition rule_end_eqb (a b : rule) : bool :=
  sumbool_eqb verdict_eq_dec (r_verdict a) (r_verdict b) &&
  opt_eqb vmap_spec_eq_dec (r_vmap a) (r_vmap b) &&
  opt_eqb nat_spec_eq_dec (r_nat a) (r_nat b) &&
  opt_eqb tproxy_spec_eq_dec (r_tproxy a) (r_tproxy b) &&
  opt_eqb fwd_spec_eq_dec (r_fwd a) (r_fwd b) &&
  opt_eqb queue_spec_eq_dec (r_queue a) (r_queue b) &&
  sumbool_eqb (list_eq_dec stmt_eq_dec) (r_after a) (r_after b).

(** [rule_end_eqb] characterises exactly equality of two [mk_head]-built shells with
    the same head/body: the bodies coincide by construction, so the records are equal
    iff the END fields are. *)
Lemma rule_end_eqb_mk_head : forall m rest r1 r2,
  rule_end_eqb r1 r2 = true <->
  mk_head m rest r1 = mk_head m rest r2.
Proof.
  intros m rest r1 r2. unfold rule_end_eqb.
  rewrite !Bool.andb_true_iff.
  rewrite !sumbool_eqb_true_iff, !opt_eqb_true_iff.
  unfold mk_head. split.
  - intros [[[[[[Hv Hvm] Hn] Ht] Hf] Hq] Ha].
    rewrite Hv, Hvm, Hn, Ht, Hf, Hq, Ha. reflexivity.
  - intro H. injection H as Hvm Hn Ht Hf Hq Ha Hv.
    repeat split; assumption.
Qed.

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

(** Point-interval membership in the orientation this file's MCmp goals want
    (RHS [data_eqb x v], key-first).  The fact itself is proved once as the
    canonical [Bytes.data_in_iv_point] ([data_eqb v x]); here we only flip the
    [data_eqb] arguments with [data_eqb_sym] — no reproof from scratch. *)
Lemma data_in_iv_point_eqb : forall x v, data_in_iv x (v, v) = data_eqb x v.
Proof.
  intros x v. rewrite data_in_iv_point. apply data_eqb_sym.
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
  rewrite !data_in_iv_point_eqb.
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
           — the heads legitimately differ in their value.  [rule_end_eqb] is the
           compact boolean equivalent of [rule_eq_dec] on these shells (see
           [rule_end_eqb_mk_head]); it keeps the extracted optimizer small. *)
        if rule_end_eqb r1 r2
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
  destruct (rule_end_eqb r1 r2) as [|] eqn:Eeqb; [| discriminate].
  pose proof (proj1 (rule_end_eqb_mk_head (MCmp f1' CEq v1') b1 r1 r2) Eeqb) as Eshell.
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
(** *** The CHAIN-level entry: pick a counter past every existing set name (here
    [0] suffices when the input table declares no [setname]-shaped name — the case
    for a freshly-parsed ruleset, whose anonymous sets are named `__setN` by the
    parser but whose EXPLICIT named sets are user identifiers, never a bare unary
    `__setIII…`).  We expose the general theorem with the freshness side-condition. *)

(** * N-WAY consolidation: a whole RUN of adjacent value-merge-eligible rules folds
      into ONE rule with an N-element anonymous set.

    The pairwise pass above merges exactly two rules and recurses past the second,
    so a run [dport 22 accept; dport 80 accept; dport 443 accept] became a 2-element
    set [{22,80}] plus a leftover [dport 443 accept] — strictly LESS consolidated
    than [nft -o], which emits ONE rule [dport { 22, 80, 443 } accept].  This
    section delivers the faithful N-way pass: it scans the MAXIMAL run of rules that
    all share the same fixed-width field [f], the same tail [body], and the same
    end-fields (verdict/…), differing only in their head value, and folds the WHOLE
    run into one [MConcatSet [f] false __setN] whose set carries one point element
    per rule.  [nft -o] keeps the values discrete (never range-coalesced), so the
    synthesised set is [map (fun v => (v,v)) vals]. *)

Lemma existsb_map_eq : forall (A B : Type) (f : B -> bool) (g : A -> B) (l : list A),
  existsb f (map g l) = existsb (fun x => f (g x)) l.
Proof.
  induction l as [| a l IH]; intros; [reflexivity|].
  cbn [map existsb]. rewrite IH. reflexivity.
Qed.

Lemma existsb_ext : forall (A : Type) (f g : A -> bool) (l : list A),
  (forall x, In x l -> f x = g x) -> existsb f l = existsb g l.
Proof.
  induction l as [| a l IH]; intros H; [reflexivity|].
  cbn [existsb]. rewrite (H a (or_introl eq_refl)).
  rewrite IH; [reflexivity|]. intros x Hx. apply H. right; exact Hx.
Qed.

Lemma existsb_false_forall : forall (A : Type) (f : A -> bool) (l : list A),
  (forall x, In x l -> f x = false) -> existsb f l = false.
Proof.
  induction l as [| a l IH]; intros H; [reflexivity|].
  cbn [existsb]. rewrite (H a (or_introl eq_refl)). cbn [orb].
  apply IH. intros x Hx. apply H. right; exact Hx.
Qed.

(** ** The N-element membership certificate.

    A single-field set [map (fun v => (v,v)) vals] (each value at the field's full
    width when loadable) is matched by [MConcatSet [f] false name] iff SOME value
    matches the point test [MCmp f CEq v] — i.e. the [existsb] disjunction over the
    run.  Generalises [concat_set_two_points] from 2 to N elements. *)
(** A point [MCmp f CEq v] over a field loaded at the value's full width is exactly
    [data_eqb (field_value f q) v] (no [firstn] truncation). *)
Lemma eval_mcmp_point : forall f v q,
  field_loadable f q = true ->
  length (field_value f q) = length v ->
  eval_matchcond (MCmp f CEq v) q = data_eqb (field_value f q) v.
Proof.
  intros f v q Hld Hlen.
  unfold eval_matchcond, eval_matchcond_body, match_loadable.
  rewrite Hld. cbn [andb]. unfold eval_cmp.
  rewrite <- Hlen, List.firstn_all. reflexivity.
Qed.

Lemma eval_mcmp_point_unload : forall f v q,
  field_loadable f q = false ->
  eval_matchcond (MCmp f CEq v) q = false.
Proof.
  intros f v q Hld.
  unfold eval_matchcond, match_loadable. rewrite Hld. reflexivity.
Qed.

Lemma concat_set_existsb : forall f vals name q,
  e_set (pkt_env q) name = map (fun v => (v, v)) vals ->
  (forall v, In v vals -> field_loadable f q = true -> length (field_value f q) = length v) ->
  eval_matchcond (MConcatSet [f] false name) q
  = existsb (fun v => eval_matchcond (MCmp f CEq v) q) vals.
Proof.
  intros f vals name q Hset Hlen.
  unfold eval_matchcond at 1, eval_matchcond_body at 1.
  cbn [match_loadable fields_loadable forallb].
  rewrite Bool.andb_true_r.
  destruct (field_loadable f q) eqn:Hld; cbn [andb].
  - cbn [map]. rewrite concat_set_mem_single. unfold set_mem. rewrite Hset.
    rewrite existsb_map_eq.
    apply existsb_ext. intros v Hv.
    rewrite data_in_iv_point_eqb.
    rewrite (eval_mcmp_point f v q Hld (Hlen v Hv eq_refl)). reflexivity.
  - symmetry. apply existsb_false_forall. intros v Hv.
    apply (eval_mcmp_point_unload f v q Hld).
Qed.


(** ** The N-way run merge over [eval_rules], proved DIRECTLY.

    Every rule in the run [map (fun m => mk_head m body r1) ms] shares the SAME
    loadability path, the SAME outcome, and the SAME applies-walk tail (all read off
    the shared record [r1] / shared [body]); they differ ONLY in the head match's
    [eval_matchcond] (and every head shares [match_loadable = ML]).  We unfold
    [eval_rules] directly: in first-match order the run fires iff SOME rule loads &
    applies, with the common outcome — exactly the disjunction
    [existsb (eval_matchcond .) ms] that the merged head realises. *)
(** *** Fully general N-way run collapse (rule-list level, family-agnostic).

    A nonempty run [rs] of rules that all share the SAME loadability [LL] and the SAME
    outcome [O] on [p] collapses to ONE merged rule [rm] whose loadability is [LL] and
    whose [rule_applies] is the [existsb] of the run's applicabilities.  Used by the
    value->set and concat-set N-way passes (both have a single shared verdict); the
    vmap pass needs the value-DEPENDENT analogue and is handled separately. *)
Lemma eval_rules_run_collapse :
  forall (rs : list rule) (LL : bool) (O : option verdict) rm rest p,
  rs <> [] ->
  (forall r, In r rs -> rule_loadable r p = LL) ->
  (forall r, In r rs -> outcome r p = O) ->
  rule_loadable rm p = LL ->
  outcome rm p = O ->
  rule_applies rm p = existsb (fun r => rule_applies r p) rs ->
  eval_rules (rm :: rest) p = eval_rules (rs ++ rest) p.
Proof.
  intros rs LL O rm rest p Hne HL HO Hrl Hro Hra.
  cbn [eval_rules]. rewrite Hrl, Hro, Hra.
  (* characterise eval_rules (rs ++ rest) p *)
  assert (Hrun :
    eval_rules (rs ++ rest) p
    = if (LL && existsb (fun r => rule_applies r p) rs) then
        match O with
        | Some v => if terminal v then Some v else eval_rules rest p
        | None => eval_rules rest p
        end
      else eval_rules rest p).
  { assert (Hterm :
        (match O with Some w => if terminal w then Some w else eval_rules rest p
                    | None => eval_rules rest p end = eval_rules rest p)
        \/ (exists v, O = Some v /\ terminal v = true)).
    { destruct O as [v |]; [destruct (terminal v) eqn:Et;
        [ right; eauto | left; reflexivity ] | left; reflexivity ]. }
    destruct Hterm as [Htarget | [v [EO Ev]]].
    - transitivity (eval_rules rest p).
      2:{ rewrite Htarget. destruct (LL && _); reflexivity. }
      clear Hne Hra Hrl Hro. revert HL HO.
      induction rs as [| r rs IH]; intros HL HO; [reflexivity|].
      cbn [app eval_rules].
      rewrite (HL r (or_introl eq_refl)), (HO r (or_introl eq_refl)).
      rewrite (IH (fun r' Hr' => HL r' (or_intror Hr'))
                  (fun r' Hr' => HO r' (or_intror Hr'))).
      destruct (LL && rule_applies r p); [ rewrite Htarget; reflexivity | reflexivity ].
    - rewrite EO. clear Hne Hra Hrl Hro. revert HL HO.
      induction rs as [| r rs IH]; intros HL HO.
      + cbn [app eval_rules existsb]. rewrite Bool.andb_false_r. reflexivity.
      + cbn [app eval_rules].
        rewrite (HL r (or_introl eq_refl)), (HO r (or_introl eq_refl)).
        rewrite (IH (fun r' Hr' => HL r' (or_intror Hr'))
                    (fun r' Hr' => HO r' (or_intror Hr'))).
        cbn [existsb]. rewrite EO, Ev.
        destruct LL; cbn [andb]; [| reflexivity].
        destruct (rule_applies r p); cbn [orb]; reflexivity. }
  rewrite Hrun. reflexivity.
Qed.

Lemma eval_rules_run_merge_abs :
  forall (ms : list matchcond) (ML : packet -> bool) body r1 m12 rest p,
  ms <> [] ->
  (forall m, In m ms -> match_loadable m p = ML p) ->
  match_loadable m12 p = ML p ->
  eval_matchcond m12 p = existsb (fun m => eval_matchcond m p) ms ->
  eval_rules (mk_head m12 body r1 :: rest) p
  = eval_rules (map (fun m => mk_head m body r1) ms ++ rest) p.
Proof.
  intros ms ML body r1 m12 rest p Hne HmlAll Hml Hev.
  (* Abbreviations for the shared loadability path, applies-walk, outcome. *)
  set (L := body_loadable_walk body p &&
            (if body_synproxy_stops body p then true
             else end_loadable r1 (body_thread body p))).
  set (A := rule_applies_walk body p).
  set (O := if body_synproxy_stops body p then Some Drop
            else outcome_core r1 (body_thread body p)).
  (* Each [mk_head m body r1] has loadable = match_loadable m p && L,
     applies = eval_matchcond m p && A, outcome = O. *)
  assert (Hload : forall m, rule_loadable (mk_head m body r1) p
                            = match_loadable m p && L).
  { intro m. rewrite rule_loadable_mk_head. reflexivity. }
  assert (Happ : forall m, rule_applies (mk_head m body r1) p
                           = eval_matchcond m p && A).
  { intro m. rewrite rule_applies_mk_head. reflexivity. }
  assert (Hout : forall m, outcome (mk_head m body r1) p = O).
  { intro m. rewrite outcome_mk_head. reflexivity. }
  (* The merged single rule: *)
  cbn [eval_rules]. rewrite (Hload m12), (Happ m12), (Hout m12).
  rewrite Hml, Hev.
  (* Now the RHS: the run. We characterise eval_rules (run ++ rest) p by induction
     on ms, exposing that ML and L and A and O are shared across the run. *)
  (* Generalise: prove eval_rules (run ++ rest) p depends only on existsb. *)
  assert (Hrun :
    eval_rules (map (fun m => mk_head m body r1) ms ++ rest) p
    = if ((ML p && L) && (existsb (fun m => eval_matchcond m p) ms && A)) then
        match O with
        | Some v => if terminal v then Some v else eval_rules rest p
        | None => eval_rules rest p
        end
      else eval_rules rest p).
  { clear Hev Hml m12.
    (* CASE on the common outcome O: if it is non-terminal (or None), the run NEVER
       terminates, so the WHOLE [run ++ rest] reduces to [eval_rules rest p] (and so
       does the target's [match O] branch, on either side of the [if]).  Only a
       TERMINAL [Some v] makes first-match position matter. *)
    assert (Hterm : (match O with
                     | Some v => terminal v
                     | None => false
                     end) = false \/
                    (exists v, O = Some v /\ terminal v = true)).
    { destruct O as [v |]; [destruct (terminal v) eqn:Et; [right; eauto | left; reflexivity]
                          | left; reflexivity]. }
    destruct Hterm as [Hnt | [v [EO Ev]]].
    - (* non-terminal / None: both sides are eval_rules rest p *)
      assert (Htarget :
        match O with
        | Some w => if terminal w then Some w else eval_rules rest p
        | None => eval_rules rest p
        end = eval_rules rest p).
      { clearbody O. destruct O as [w |]; [ destruct (terminal w) eqn:Etw;
          [ exfalso; clear -Hnt Etw; cbn in Hnt; congruence | reflexivity ]
          | reflexivity ]. }
      transitivity (eval_rules rest p).
      2:{ rewrite Htarget. destruct ((ML p && L) && _); reflexivity. }
      (* LHS: induct, every rule falls through to eval_rules rest p *)
      clear Hne Hnt. revert HmlAll. induction ms as [| m ms IH]; intro HmlAll.
      + reflexivity.
      + cbn [map app eval_rules].
        rewrite (Hload m), (Happ m), (Hout m).
        rewrite (IH (fun mm Hmm => HmlAll mm (or_intror Hmm))).
        destruct (match_loadable m p && L && (eval_matchcond m p && A));
          [ rewrite Htarget; reflexivity | reflexivity ].
    - (* terminal Some v: first-match position matters *)
      rewrite EO. clear Hne. revert HmlAll. induction ms as [| m ms IH]; intro HmlAll.
      + (* empty: existsb [] = false, both sides eval_rules rest p *)
        cbn [map app eval_rules existsb]. rewrite Bool.andb_false_r. reflexivity.
      + cbn [map app eval_rules].
        rewrite (Hload m), (Happ m), (Hout m).
        rewrite (HmlAll m (or_introl eq_refl)). cbn [existsb].
        rewrite (IH (fun mm Hmm => HmlAll mm (or_intror Hmm))).
        rewrite EO, Ev.
        (* boolean case split: ML p && L, A, eval_matchcond m p, existsb ms *)
        destruct (ML p && L); cbn [andb]; [| reflexivity].
        destruct A; [| rewrite !Bool.andb_false_r; reflexivity ].
        rewrite !Bool.andb_true_r.
        destruct (eval_matchcond m p); cbn [orb andb]; reflexivity. }
  rewrite Hrun. reflexivity.
Qed.

(** ** The executable N-WAY value->set pass.

    [take_value_run r1 rest] scans the MAXIMAL prefix of [rest] of rules that each
    form a value-merge pair with the canonical first rule [r1] (same fixed-width
    field, same tail body, same end-fields, differing value), returning their values
    [vs] (in source order) and the LEFTOVER suffix [rest'].  [optimize_rules_setsN]
    then folds the whole run [r1 :: matched] into ONE rule whose head is
    [MConcatSet [f] false __setN] over the N-element set
    [map (fun v => (v,v)) (v1 :: vs)] — exactly the consolidation [nft -o] emits
    for a run of >= 2 single-dimension-differing rules. *)
Fixpoint take_value_run (r1 : rule) (rest : list rule)
  : list data * list rule :=
  match rest with
  | [] => ([], [])
  | r2 :: tl =>
      match value_merge_pair r1 r2 with
      | Some (_, _, v2, _) =>
          let '(vs, rest') := take_value_run r1 tl in
          (v2 :: vs, rest')
      | None => ([], rest)
      end
  end.

Lemma take_value_run_len : forall r1 rest vs rest',
  take_value_run r1 rest = (vs, rest') ->
  length vs + length rest' = length rest.
Proof.
  intros r1 rest. induction rest as [| r2 tl IH]; intros vs rest' H.
  - cbn in H. inversion H; subst. reflexivity.
  - cbn in H. destruct (value_merge_pair r1 r2) as [[[[f v] v2] body] |] eqn:Evm.
    + destruct (take_value_run r1 tl) as [vs0 rest0] eqn:Erec.
      inversion H; subst vs rest'. cbn [length].
      rewrite <- (IH vs0 rest0 eq_refl). cbn [length]. lia.
    + inversion H; subst vs rest'. cbn [length]. reflexivity.
Qed.

(** Fuel-bounded driver ([fuel] >= [length rs] suffices; the chain wrapper passes
    [length (c_rules c)]).  Each productive recursive call consumes at least one rule
    from the front, so the fuel is never the limiting factor. *)
Fixpoint optimize_rules_setsN (fuel : nat) (n : nat) (d : set_decls) (rs : list rule)
  : nat * set_decls * list rule :=
  match fuel with
  | O => (n, d, rs)
  | S fuel' =>
    match rs with
    | r1 :: ((_ :: _) as rest) =>
        match head_value r1 with
        | Some (f, v1, body) =>
            match take_value_run r1 rest with
            | ([], _) =>
                let '(n'', d'', rest') := optimize_rules_setsN fuel' n d rest in
                (n'', d'', r1 :: rest')
            | ((_ :: _) as vs, rest') =>
                let name := setname n in
                let elems := map (fun v => (v, v)) (v1 :: vs) in
                let d' := {| sd_sets := (name, elems) :: sd_sets d;
                             sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} in
                let merged := mk_head (MConcatSet [f] false name) body r1 in
                let '(n'', d'', rest'') := optimize_rules_setsN fuel' (S n) d' rest' in
                (n'', d'', merged :: rest'')
            end
        | None =>
            let '(n'', d'', rest') := optimize_rules_setsN fuel' n d rest in
            (n'', d'', r1 :: rest')
        end
    | _ => (n, d, rs)
    end
  end.

Definition optimize_chain_setsN (n : nat) (d : set_decls) (c : chain)
  : nat * set_decls * chain :=
  let '(n', d', rs') := optimize_rules_setsN (length (c_rules c)) n d (c_rules c) in
  (n', d', {| c_policy := c_policy c; c_rules := rs' |}).


(** [value_merge_pair] returns [r1]'s field/value/body in slots 1/2/4 (the differing
    slot 3 is [r2]'s value), so when [head_value r1 = Some (f,v1,body)] the result is
    [Some (f, v1, v2, body)] and [r2] is the canonical shell over [v2]. *)
Lemma value_merge_pair_with_head : forall r1 r2 f v1 body f' v1' v2 body',
  head_value r1 = Some (f, v1, body) ->
  value_merge_pair r1 r2 = Some (f', v1', v2, body') ->
  f' = f /\ v1' = v1 /\ body' = body /\
  r2 = mk_head (MCmp f CEq v2) body r1 /\
  field_fixed_len f = Some (length v2).
Proof.
  intros r1 r2 f v1 body f' v1' v2 body' Hhd Hvm.
  destruct (value_merge_pair_shape r1 r2 f' v1' v2 body' Hvm) as [Hr1 [Hr2 [Hfx1 Hfx2]]].
  (* head_value r1 = Some (f', v1', body') by Hr1 unfolding, and = Some (f,v1,body) *)
  assert (Hhd' : head_value r1 = Some (f', v1', body')).
  { rewrite Hr1 at 1. unfold head_value, mk_head. cbn [r_body]. reflexivity. }
  rewrite Hhd in Hhd'. inversion Hhd'; subst f' v1' body'.
  repeat split; [ exact Hr2 | exact Hfx2 ].
Qed.

(** When the run is NONEMPTY, [r1]'s own value is also field-width (the first pair
    fired [value_merge_pair], whose shape forces [field_fixed_len f = Some (len v1)]). *)
Lemma take_value_run_head_width : forall r1 f v1 body r2 rest vs rest',
  head_value r1 = Some (f, v1, body) ->
  take_value_run r1 (r2 :: rest) = (vs, rest') ->
  vs <> [] ->
  field_fixed_len f = Some (length v1).
Proof.
  intros r1 f v1 body r2 rest vs rest' Hhd Hrun Hne.
  cbn in Hrun. destruct (value_merge_pair r1 r2) as [[[[fa va] v2] bd] |] eqn:Evm.
  - destruct (value_merge_pair_shape r1 r2 fa va v2 bd Evm) as [Hr1 [_ [Hfx1 _]]].
    assert (Hhd' : head_value r1 = Some (fa, va, bd)).
    { rewrite Hr1 at 1. unfold head_value, mk_head. cbn [r_body]. reflexivity. }
    rewrite Hhd in Hhd'. inversion Hhd'; subst fa va bd. exact Hfx1.
  - destruct (take_value_run r1 rest) as [vs0 rest0] eqn:Erec0.
    inversion Hrun; subst. contradiction.
Qed.

(** Shape of the collected run: the matched prefix of [rest] is exactly the canonical
    shells [map (fun v => mk_head (MCmp f CEq v) body r1) vs], [rest] splits as that
    prefix ++ [rest'], and every collected value is field-width. *)
Lemma take_value_run_shape : forall r1 f v1 body rest vs rest',
  head_value r1 = Some (f, v1, body) ->
  take_value_run r1 rest = (vs, rest') ->
  rest = map (fun v => mk_head (MCmp f CEq v) body r1) vs ++ rest'
  /\ (forall v, In v vs -> field_fixed_len f = Some (length v)).
Proof.
  intros r1 f v1 body rest. induction rest as [| r2 tl IH]; intros vs rest' Hhd H.
  - cbn in H. inversion H; subst. split; [reflexivity| intros v []].
  - cbn in H. destruct (value_merge_pair r1 r2) as [[[[fa va] v2] bd] |] eqn:Evm.
    + destruct (take_value_run r1 tl) as [vs0 rest0] eqn:Erec.
      inversion H; subst vs rest'. clear H.
      destruct (value_merge_pair_with_head r1 r2 f v1 body fa va v2 bd Hhd Evm)
        as [_ [_ [_ [Hr2 Hfx]]]].
      destruct (IH vs0 rest0 Hhd eq_refl) as [Hsplit Hall].
      split.
      * cbn [map app]. rewrite <- Hr2, <- Hsplit. reflexivity.
      * intros v [Hv | Hv]; [ subst v; exact Hfx | apply Hall; exact Hv ].
    + inversion H; subst vs rest'. split; [reflexivity| intros v []].
Qed.

(** One-step unfolding on a cons-cons input under [S fuel] (recursive calls stay
    folded). *)
Lemma optimize_rules_setsN_consSS : forall fuel n d r1 r2 rest,
  optimize_rules_setsN (S fuel) n d (r1 :: r2 :: rest) =
  match head_value r1 with
  | Some (f, v1, body) =>
      match take_value_run r1 (r2 :: rest) with
      | ([], _) =>
          let '(n'', d'', rest') := optimize_rules_setsN fuel n d (r2 :: rest) in
          (n'', d'', r1 :: rest')
      | ((_ :: _) as vs, rest') =>
          let name := setname n in
          let elems := map (fun v => (v, v)) (v1 :: vs) in
          let d' := {| sd_sets := (name, elems) :: sd_sets d;
                       sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} in
          let merged := mk_head (MConcatSet [f] false name) body r1 in
          let '(n'', d'', rest'') := optimize_rules_setsN fuel (S n) d' rest' in
          (n'', d'', merged :: rest'')
      end
  | None =>
      let '(n'', d'', rest') := optimize_rules_setsN fuel n d (r2 :: rest) in
      (n'', d'', r1 :: rest')
  end.
Proof. reflexivity. Qed.

(** Freshness bookkeeping for the N-way pass: it only PREPENDS [sd_sets] entries keyed
    [setname k] with [n <= k < n'], so an un-minted name's lookup is preserved. *)
Lemma optimize_rules_setsN_assoc_stable : forall fuel n d rs n' d' rs' nm X,
  optimize_rules_setsN fuel n d rs = (n', d', rs') ->
  (forall k, n <= k -> nm <> setname k) ->
  assoc_str nm (sd_sets d') X = assoc_str nm (sd_sets d) X.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' nm X H Hnm.
  - cbn in H. inversion H; subst; reflexivity.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; reflexivity.
    + cbn in H. inversion H; subst; reflexivity.
    + rewrite optimize_rules_setsN_consSS in H.
      destruct (head_value r1) as [[[f v1] body] |] eqn:Ehd.
      * destruct (take_value_run r1 (r2 :: rest)) as [vs rest'] eqn:Erun.
        destruct vs as [| v vs'].
        -- remember (optimize_rules_setsN fuel n d (r2 :: rest)) as t eqn:Erec.
           destruct t as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst d'. clear Hn' Hr'.
           eapply (IH n d (r2 :: rest)); [symmetry; exact Erec | exact Hnm].
        -- cbv zeta in H.
           remember (optimize_rules_setsN fuel (S n)
                       {| sd_sets := (setname n, map (fun v => (v,v)) (v1 :: v :: vs'))
                                     :: sd_sets d;
                          sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
             as t eqn:Erec.
           destruct t as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst d'. clear Hn' Hr'.
           erewrite (IH (S n) _ rest'); [ | symmetry; exact Erec | intros k Hk; apply Hnm; lia ].
           cbn [sd_sets assoc_str].
           destruct (String.eqb nm (setname n)) eqn:Eqn.
           ++ apply String.eqb_eq in Eqn. exfalso. apply (Hnm n); [lia | exact Eqn].
           ++ reflexivity.
      * remember (optimize_rules_setsN fuel n d (r2 :: rest)) as t eqn:Erec.
        destruct t as [[m'' dd''] rr'']. cbv zeta in H.
        injection H as Hn' Hd' Hr'. subst d'. clear Hn' Hr'.
        eapply (IH n d (r2 :: rest)); [symmetry; exact Erec | exact Hnm].
Qed.

(** [head_value r1 = Some (f,v1,body)] means [r1] IS the canonical value-head shell. *)
Lemma head_value_canon : forall r1 f v1 body,
  head_value r1 = Some (f, v1, body) ->
  r1 = mk_head (MCmp f CEq v1) body r1.
Proof.
  intros r1 f v1 body H. unfold head_value in H.
  destruct (r_body r1) as [| [m | s] b] eqn:Eb; try discriminate.
  destruct m as [ | | | | f' op v' | | | | | | | | ]; try discriminate.
  destruct op; try discriminate. inversion H; subst f' v' b.
  unfold mk_head. rewrite <- Eb. destruct r1; reflexivity.
Qed.

(** Congruence of [eval_rules] under a shared prefix. *)
Lemma eval_rules_app_cong : forall pre t1 t2 p,
  eval_rules t1 p = eval_rules t2 p ->
  eval_rules (pre ++ t1) p = eval_rules (pre ++ t2) p.
Proof.
  induction pre as [| r pre IH]; intros t1 t2 p H; [exact H|].
  cbn [app eval_rules].
  destruct (rule_loadable r p && rule_applies r p); [| apply IH; exact H].
  destruct (outcome r p) as [v |]; [| apply IH; exact H].
  destruct (terminal v); [reflexivity | apply IH; exact H].
Qed.

(** The merged head [MConcatSet [f] false name] and the canonical point heads
    [MCmp f CEq w] all share [match_loadable = fields_loadable [f]]. *)
Lemma match_loadable_mconcat1 : forall f name q,
  match_loadable (MConcatSet [f] false name) q = fields_loadable [f] q.
Proof. reflexivity. Qed.

Lemma match_loadable_mcmp_fields : forall f w q,
  match_loadable (MCmp f CEq w) q = fields_loadable [f] q.
Proof.
  intros. cbn [match_loadable fields_loadable forallb]. rewrite Bool.andb_true_r.
  reflexivity.
Qed.

(** Every head in [map (MCmp f CEq) vals] shares [match_loadable = fields_loadable [f]]. *)
Lemma match_loadable_run : forall f vals q m,
  In m (map (fun w => MCmp f CEq w) vals) ->
  match_loadable m q = fields_loadable [f] q.
Proof.
  intros f vals q m Hin. apply in_map_iff in Hin as [w [Hw _]]. subst m.
  apply match_loadable_mcmp_fields.
Qed.

(** *** The executable N-WAY value->set merge, proved verdict-preserving END-TO-END
    over the table semantics with the synthesised N-element set in scope, axiom-free.

    A whole adjacent RUN of >= 2 value-merge-eligible rules folds into ONE rule whose
    `__setN` resolves to its N point elements (freshness + [optimize_..._assoc_stable]);
    [concat_set_existsb] turns the merged head into the [existsb] disjunction of the N
    point matches; [eval_rules_run_merge_abs] collapses the whole run; the clean
    leftover tail is env-irrelevant.  This matches [nft -o]'s consolidation of an
    N-rule run into a single N-element anonymous set. *)
Theorem optimize_rules_setsN_correct : forall fuel rs n d n' d' rs' base p,
  optimize_rules_setsN fuel n d rs = (n', d', rs') ->
  rules_clean rs = true ->
  (forall k, n <= k -> ~ In (setname k) (map fst (sd_sets d))) ->
  eval_rules rs' (set_env p (env_with_sets base d'))
  = eval_rules rs  (set_env p (env_with_sets base d)).
Proof.
  induction fuel as [| fuel IH]; intros rs n d n' d' rs' base p H Hclean Hfresh.
  - cbn in H. inversion H; subst; reflexivity.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; reflexivity.
    + cbn in H. inversion H; subst; reflexivity.
    + rewrite optimize_rules_setsN_consSS in H.
      cbn [rules_clean forallb] in Hclean.
      apply Bool.andb_true_iff in Hclean as [Hc1 Hclrest].
      destruct (head_value r1) as [[[f v1] body] |] eqn:Ehd.
      * destruct (take_value_run r1 (r2 :: rest)) as [vs rest'] eqn:Erun.
        destruct (take_value_run_shape r1 f v1 body (r2 :: rest) vs rest' Ehd Erun)
          as [Hsplit Hwidth].
        destruct vs as [| v vs'].
        -- (* no eligible neighbour: keep r1, recurse on r2::rest *)
           remember (optimize_rules_setsN fuel n d (r2 :: rest)) as t eqn:Erec.
           destruct t as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           cbn [eval_rules].
           rewrite (IH (r2 :: rest) n d m'' dd'' rr'' base p
                       (eq_sym Erec) Hclrest Hfresh).
           destruct (rule_clean_env r1 p base dd'' d Hc1) as [Hl [Ha Ho]].
           rewrite Hl, Ha, Ho. reflexivity.
        -- (* RUN of >= 2 rules: fold them all into one __setN *)
           cbv zeta in H.
           remember (optimize_rules_setsN fuel (S n)
                       {| sd_sets := (setname n, map (fun w => (w,w)) (v1 :: v :: vs'))
                                     :: sd_sets d;
                          sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
             as t eqn:Erec.
           destruct t as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           set (vals := v1 :: v :: vs') in *.
           set (elems := map (fun w => (w, w)) vals) in *.
           set (dn := {| sd_sets := (setname n, elems) :: sd_sets d;
                         sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |}) in *.
           (* rest = (the run minus r1) ++ rest'; r1 :: that = the whole run *)
           assert (Hrun_eq : r1 :: r2 :: rest
                   = map (fun w => mk_head (MCmp f CEq w) body r1) vals ++ rest').
           { subst vals. cbn [map app]. f_equal.
             - apply (head_value_canon r1 f v1 body Ehd).
             - exact Hsplit. }
           (* the optimized tail equals the original rest' under dn (by IH on fuel) *)
           assert (Htail : eval_rules rr'' (set_env p (env_with_sets base dd''))
                           = eval_rules rest' (set_env p (env_with_sets base dn))).
           { (* rest' is clean: it is a suffix of the clean (r2::rest) *)
             assert (Hcrest' : rules_clean rest' = true).
             { assert (Hsub : rules_clean (r2 :: rest) = true)
                 by (cbn [rules_clean forallb]; exact Hclrest).
               rewrite Hsplit in Hsub. unfold rules_clean in Hsub.
               rewrite forallb_app in Hsub.
               apply Bool.andb_true_iff in Hsub. exact (proj2 Hsub). }
             eapply (IH rest' (S n) dn m'' dd'' rr'' base p (eq_sym Erec) Hcrest').
             intros k Hk Hin. subst dn; cbn [sd_sets map] in Hin.
             destruct Hin as [Heq | Hin].
             - apply setname_inj in Heq. lia.
             - apply (Hfresh k); [lia | exact Hin]. }
           (* resolve the minted set name to its N elements in dd'' *)
           assert (Hlook : e_set (pkt_env (set_env p (env_with_sets base dd''))) (setname n)
                           = elems).
           { cbn [set_env with_pkt_env pkt_env]. rewrite e_set_declared.
             erewrite (optimize_rules_setsN_assoc_stable fuel (S n) dn _ _ _ _
                         (setname n) _ (eq_sym Erec)).
             - subst dn; cbn [sd_sets assoc_str]. rewrite String.eqb_refl. reflexivity.
             - intros k Hk Heq. apply setname_inj in Heq. lia. }
           set (qd := set_env p (env_with_sets base dd'')) in *.
           (* membership certificate: merged head = existsb of the N point matches *)
           assert (Hcert : eval_matchcond (MConcatSet [f] false (setname n)) qd
                   = existsb (fun w => eval_matchcond (MCmp f CEq w) qd) vals).
           { apply (concat_set_existsb f vals (setname n) qd).
             - subst elems. exact Hlook.
             - intros w Hw Hld.
               assert (Hfxw : field_fixed_len f = Some (length w)).
               { subst vals. destruct Hw as [Hw | Hw].
                 - subst w. apply (take_value_run_head_width r1 f v1 body r2 rest
                                     (v :: vs') rest' Ehd Erun). discriminate.
                 - apply (Hwidth w Hw). }
               apply (field_fixed_len_loaded f (length w) qd Hfxw Hld). }
           (* collapse the merged rule into the whole run via run_merge_abs *)
           transitivity (eval_rules
             (map (fun m => mk_head m body r1) (map (fun w => MCmp f CEq w) vals)
              ++ rr'') qd).
           { apply (eval_rules_run_merge_abs
                      (map (fun w => MCmp f CEq w) vals)
                      (fun q => fields_loadable [f] q) body r1
                      (MConcatSet [f] false (setname n)) rr'' qd).
             - subst vals. discriminate.
             - intros m Hm. apply (match_loadable_run f vals qd m Hm).
             - apply match_loadable_mconcat1.
             - rewrite Hcert. rewrite existsb_map_eq. reflexivity. }
           rewrite List.map_map.
           (* tail rr'' -> rest' (clean, env-stable), then point heads = the originals *)
           assert (Htail' : eval_rules rr'' qd = eval_rules rest' qd).
           { rewrite Htail. unfold qd.
             apply (eval_rules_clean_env rest' p base dn dd'').
             (* rest' clean (proved above) *)
             clear -Hclrest Hsplit.
             assert (Hsub : rules_clean (r2 :: rest) = true)
               by (cbn [rules_clean forallb]; exact Hclrest).
             rewrite Hsplit in Hsub. unfold rules_clean in Hsub.
             rewrite forallb_app in Hsub.
             apply Bool.andb_true_iff in Hsub. exact (proj2 Hsub). }
           (* now both sides over qd: replace rr'' by rest', then map heads by run *)
           rewrite (eval_rules_app_cong
                      (map (fun w => mk_head (MCmp f CEq w) body r1) vals)
                      rr'' rest' qd Htail').
           rewrite <- Hrun_eq.
           (* whole clean list at dd'' equals at d *)
           unfold qd. apply (eval_rules_clean_env (r1 :: r2 :: rest) p base dd'' d).
           cbn [rules_clean forallb]. rewrite Hc1, Hclrest. reflexivity.
      * (* head not value-eligible: keep r1, recurse *)
        remember (optimize_rules_setsN fuel n d (r2 :: rest)) as t eqn:Erec.
        destruct t as [[m'' dd''] rr'']. cbv zeta in H.
        injection H as Hn' Hd' Hr'. subst n' d' rs'.
        cbn [eval_rules].
        rewrite (IH (r2 :: rest) n d m'' dd'' rr'' base p (eq_sym Erec) Hclrest Hfresh).
        destruct (rule_clean_env r1 p base dd'' d Hc1) as [Hl [Ha Ho]].
        rewrite Hl, Ha, Ho. reflexivity.
Qed.

(** *** Chain-level N-WAY value->set: verdict-preserving end-to-end, axiom-free. *)
Theorem optimize_chain_setsN_correct : forall n d c n' d' c' base p,
  optimize_chain_setsN n d c = (n', d', c') ->
  rules_clean (c_rules c) = true ->
  (forall k, n <= k -> ~ In (setname k) (map fst (sd_sets d))) ->
  eval_chain c' (set_env p (env_with_sets base d'))
  = eval_chain c  (set_env p (env_with_sets base d)).
Proof.
  intros n d c n' d' c' base p H Hclean Hfresh.
  unfold optimize_chain_setsN in H.
  destruct (optimize_rules_setsN (length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:Erec.
  inversion H; subst n' d' c'. cbn [c_rules c_policy].
  unfold eval_chain. cbn [c_rules c_policy].
  rewrite (optimize_rules_setsN_correct (length (c_rules c)) (c_rules c) n d
             m'' dd'' rr'' base p Erec Hclean Hfresh).
  reflexivity.
Qed.
