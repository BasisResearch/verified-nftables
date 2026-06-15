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
  - destruct m as [f v0 | f v0];
      cbn [flat_map compile_match app];
      rewrite compile_load_correct;
      cbn [run_rule];
      rewrite set_reg_same;
      unfold eval_cmp;
      cbn [forallb eval_matchcond];
      destruct (data_eqb (field_value f p) v0) eqn:Hd;
      cbn [andb negb];
      try reflexivity;
      apply IH.
Qed.

(** A compiled rule runs to its verdict exactly when the rule applies. *)
Lemma run_rule_compile_rule : forall r p,
  run_rule empty_rf (compile_rule r) p =
  if rule_applies r p then Some (r_verdict r) else None.
Proof.
  intros r p. unfold compile_rule, rule_applies. apply run_compile_matches.
Qed.

(** Chain level: the compiled program reproduces the rule-list evaluation. *)
Lemma run_program_compile_chain : forall rs p,
  run_program (map compile_rule rs) p = eval_rules rs p.
Proof.
  induction rs as [| r rs IH]; intros p.
  - reflexivity.
  - cbn [map run_program eval_rules]. rewrite run_rule_compile_rule.
    destruct (rule_applies r p) eqn:Ha; cbn [terminal].
    + destruct (r_verdict r); cbn; try apply IH; reflexivity.
    + apply IH.
Qed.

(** ** Main theorem: semantic preservation. *)
Theorem compile_chain_correct : forall c p,
  run_chain (compile_chain c) (c_policy c) p = eval_chain c p.
Proof.
  intros c p. unfold run_chain, eval_chain, compile_chain.
  rewrite run_program_compile_chain. reflexivity.
Qed.
