(** * Correct: the compiler is semantics preserving.

    Main result [compile_chain_correct]: for every base chain and every packet,
    running the compiled control-plane bytecode yields exactly the verdict the
    declarative semantics assigns.  Equivalently, the netlink ruleset [nft] would
    install filters packets exactly as the DSL specifies. *)

From Stdlib Require Import List NArith Bool.
From Nft Require Import Bytes Packet Verdict Syntax Bytecode Semantics Compile.
Import ListNotations.

(** Executing a compiled load writes the field's value into the destination
    register and falls through to the rest of the program. *)
Lemma compile_load_correct : forall f rf rest p,
  run_rule rf (compile_load (field_load f) 1 :: rest) p =
  run_rule (set_reg rf 1 (field_value f p)) rest p.
Proof.
  intros f rf rest p. unfold field_value, do_load, compile_load.
  destruct (field_load f) eqn:E; simpl; reflexivity.
Qed.

(** The heart of the proof: a compiled match-list followed by an immediate runs
    to [Some v] iff every match condition holds, else [None] (a [cmp] broke).
    Quantifying over [rf] gives a strong-enough induction hypothesis. *)
Lemma run_compile_matches : forall ms rf v p,
  run_rule rf (flat_map compile_match ms ++ [IImmediate v]) p =
  if forallb (fun m => eval_matchcond m p) ms then Some v else None.
Proof.
  induction ms as [| m ms IH]; intros rf v p.
  - reflexivity.
  - destruct m as [f v0 | f v0 | f neg lo hi | f neg mask xor v0 | f neg nm elems];
      cbn [flat_map compile_match app]; rewrite compile_load_correct.
    + (* MEq *) cbn [run_rule]. rewrite set_reg_same.
      cbn [forallb eval_matchcond]. unfold eval_cmp.
      destruct (data_eqb (field_value f p) v0); cbn [andb negb];
        [apply IH | reflexivity].
    + (* MNeq *) cbn [run_rule]. rewrite set_reg_same.
      cbn [forallb eval_matchcond]. unfold eval_cmp.
      destruct (data_eqb (field_value f p) v0); cbn [andb negb];
        [reflexivity | apply IH].
    + (* MRange *) cbn [run_rule]. rewrite set_reg_same.
      cbn [forallb eval_matchcond].
      destruct (eval_range (if neg then CNe else CEq) (field_value f p) lo hi);
        cbn [andb]; [apply IH | reflexivity].
    + (* MMasked *) cbn [run_rule]. rewrite !set_reg_same.
      cbn [forallb eval_matchcond].
      destruct (eval_cmp (if neg then CNe else CEq)
                 (data_bitops (field_value f p) mask xor) v0);
        cbn [andb]; [apply IH | reflexivity].
    + (* MSet *) cbn [run_rule]. rewrite set_reg_same.
      cbn [forallb eval_matchcond].
      destruct (xorb neg (data_mem (field_value f p) elems));
        cbn [andb]; [apply IH | reflexivity].
Qed.

(** A compiled match list with no trailing verdict always falls through
    ([None]): a [Continue] rule never sets the verdict register. *)
Lemma run_matches_no_tail : forall ms rf p,
  run_rule rf (flat_map compile_match ms) p = None.
Proof.
  induction ms as [| m ms IH]; intros rf p.
  - reflexivity.
  - destruct m as [f v0 | f v0 | f neg lo hi | f neg mask xor v0 | f neg nm elems];
      cbn [flat_map compile_match app]; rewrite compile_load_correct.
    + cbn [run_rule]. rewrite set_reg_same. unfold eval_cmp.
      destruct (data_eqb (field_value f p) v0); [apply IH | reflexivity].
    + cbn [run_rule]. rewrite set_reg_same. unfold eval_cmp.
      destruct (data_eqb (field_value f p) v0); [reflexivity | apply IH].
    + cbn [run_rule]. rewrite set_reg_same.
      destruct (eval_range (if neg then CNe else CEq) (field_value f p) lo hi);
        [apply IH | reflexivity].
    + cbn [run_rule]. rewrite !set_reg_same.
      destruct (eval_cmp (if neg then CNe else CEq)
                 (data_bitops (field_value f p) mask xor) v0);
        [apply IH | reflexivity].
    + cbn [run_rule]. rewrite set_reg_same.
      destruct (xorb neg (data_mem (field_value f p) elems));
        [apply IH | reflexivity].
Qed.

(** A compiled rule: a terminal rule runs to its verdict exactly when it
    applies; a [Continue] rule always falls through. *)
Lemma run_rule_compile_rule : forall r p,
  run_rule empty_rf (compile_rule r) p =
  match r_verdict r with
  | Continue => None
  | v        => if rule_applies r p then Some v else None
  end.
Proof.
  intros r p. unfold compile_rule, rule_applies. destruct (r_verdict r) eqn:Ev.
  - apply run_compile_matches.
  - apply run_compile_matches.
  - rewrite app_nil_r. apply run_matches_no_tail.
Qed.

(** Chain level: the compiled program reproduces the rule-list evaluation. *)
Lemma run_program_compile_chain : forall rs p,
  run_program (map compile_rule rs) p = eval_rules rs p.
Proof.
  induction rs as [| r rs IH]; intros p.
  - reflexivity.
  - cbn [map run_program eval_rules]. rewrite run_rule_compile_rule.
    destruct (r_verdict r) eqn:Ev.
    + destruct (rule_applies r p); cbn [terminal]; [reflexivity | apply IH].
    + destruct (rule_applies r p); cbn [terminal]; [reflexivity | apply IH].
    + destruct (rule_applies r p); apply IH.
Qed.

(** ** Main theorem: semantic preservation. *)
Theorem compile_chain_correct : forall c p,
  run_chain (compile_chain c) (c_policy c) p = eval_chain c p.
Proof.
  intros c p. unfold run_chain, eval_chain, compile_chain.
  rewrite run_program_compile_chain. reflexivity.
Qed.
