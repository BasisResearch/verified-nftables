(** * Optimize: verified rewrites on the declarative DSL.

    Two semantics-preserving optimizations (the kind a firewall-minimizer such as
    diekmann's Iptables_Semantics performs), proved correct against the *same*
    [eval_chain] semantics used for the compiler:

      1. [dce] — dead-rule elimination: once a rule matches every packet and is
         terminal (no match conditions, verdict Accept/Drop), all later rules are
         unreachable and are dropped.

      2. [dedup_rule] — remove duplicate match conditions within a rule (a
         conjunction is idempotent), shrinking the emitted bytecode.

    [optimize_chain] runs dedup on every rule, then DCE; the top-level theorem
    [optimize_chain_correct] shows the packet->verdict function is unchanged. *)

From Stdlib Require Import List PeanoNat Bool String.
From Nft Require Import Bytes Packet Verdict Syntax Bytecode Semantics.
Import ListNotations.

(** ** Decidable equality for match conditions (needed by [nodup]). *)

Definition field_eq_dec (a b : field) : {a = b} + {a <> b}.
Proof.
  decide equality;
    repeat (apply Nat.eq_dec || apply Bool.bool_dec || decide equality).
Defined.
Definition transform_eq_dec (a b : transform) : {a = b} + {a <> b}.
Proof.
  decide equality;
    (apply Nat.eq_dec || apply Bool.bool_dec || apply (list_eq_dec Nat.eq_dec)).
Defined.

Definition limit_spec_eq_dec (a b : limit_spec) : {a = b} + {a <> b}.
Proof. decide equality; (apply Nat.eq_dec || apply Bool.bool_dec). Defined.

Definition matchcond_eq_dec (a b : matchcond) : {a = b} + {a <> b}.
Proof.
  decide equality;
    try (apply list_eq_dec; apply Nat.eq_dec);
    try (apply list_eq_dec; apply list_eq_dec; apply Nat.eq_dec);
    try (apply list_eq_dec; apply transform_eq_dec);
    try apply field_eq_dec;
    try apply Bool.bool_dec;
    try apply string_dec;
    try apply limit_spec_eq_dec.
Defined.

(** ** Optimization 1: dead-rule elimination. *)

Definition is_empty {A} (l : list A) : bool :=
  match l with [] => true | _ => false end.

(** A rule that matches everything and stops chain traversal. *)
Definition shadows (r : rule) : bool :=
  is_empty (r_matches r) && terminal (r_verdict r).

Fixpoint dce (rs : list rule) : list rule :=
  match rs with
  | [] => []
  | r :: rest => if shadows r then [r] else r :: dce rest
  end.

Lemma eval_rules_dce : forall rs p, eval_rules (dce rs) p = eval_rules rs p.
Proof.
  induction rs as [| r rs IH]; intros p.
  - reflexivity.
  - cbn [dce]. destruct (shadows r) eqn:Hs.
    + (* r shadows the rest: r matches all and is terminal *)
      unfold shadows in Hs. apply andb_true_iff in Hs. destruct Hs as [Hm Hv].
      cbn [eval_rules]. unfold rule_applies.
      destruct (r_matches r) as [| m ms] eqn:Em; [| discriminate Hm].
      cbn [forallb]. destruct (r_verdict r) eqn:Ev; cbn in Hv; try discriminate Hv;
        reflexivity.
    + (* keep r, recurse *)
      cbn [eval_rules]. destruct (rule_applies r p) eqn:Ha.
      * destruct (r_verdict r); try reflexivity; apply IH.
      * apply IH.
Qed.

(** ** Optimization 2: intra-rule match deduplication. *)

Definition dedup_rule (r : rule) : rule :=
  {| r_matches := nodup matchcond_eq_dec (r_matches r);
     r_stmts   := r_stmts r;
     r_verdict := r_verdict r |}.

Lemma forallb_nodup :
  forall (A : Type) (dec : forall x y : A, {x = y} + {x <> y}) f (l : list A),
    forallb f (nodup dec l) = forallb f l.
Proof.
  intros A dec f l. destruct (forallb f l) eqn:E.
  - rewrite forallb_forall in E. apply forallb_forall.
    intros x Hx. apply E. apply nodup_In in Hx. exact Hx.
  - destruct (forallb f (nodup dec l)) eqn:E2; [| reflexivity].
    rewrite forallb_forall in E2.
    assert (forallb f l = true) as Hbad.
    { apply forallb_forall. intros x Hx. apply E2. apply nodup_In. exact Hx. }
    congruence.
Qed.

Lemma rule_applies_dedup : forall r p,
  rule_applies (dedup_rule r) p = rule_applies r p.
Proof.
  intros r p. unfold rule_applies, dedup_rule. cbn [r_matches].
  apply forallb_nodup.
Qed.

Lemma eval_rules_map_dedup : forall rs p,
  eval_rules (map dedup_rule rs) p = eval_rules rs p.
Proof.
  induction rs as [| r rs IH]; intros p.
  - reflexivity.
  - cbn [map eval_rules]. rewrite rule_applies_dedup.
    destruct (rule_applies r p) eqn:Ha.
    + (* r_verdict (dedup_rule r) = r_verdict r definitionally *)
      cbn [r_verdict dedup_rule]. destruct (r_verdict r); try reflexivity; apply IH.
    + apply IH.
Qed.

(** ** The combined pass and its correctness. *)

Definition optimize_chain (c : chain) : chain :=
  {| c_policy := c_policy c;
     c_rules  := dce (map dedup_rule (c_rules c)) |}.

Theorem optimize_chain_correct : forall c p,
  eval_chain (optimize_chain c) p = eval_chain c p.
Proof.
  intros c p. unfold eval_chain, optimize_chain. cbn [c_rules c_policy].
  rewrite eval_rules_dce, eval_rules_map_dedup. reflexivity.
Qed.
