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

(** Running a compiled transform chain then a [cmp]: the chain leaves register 1
    holding [apply_transforms ts (rf 1)] (other registers unchanged, so the
    resulting file is left existential — the trailing program reads only reg 1). *)
Lemma run_transforms_cmp : forall ts rf op v cont p,
  exists rf',
    run_rule rf (compile_transforms ts ++ ICmp op 1 v :: cont) p =
    (if eval_cmp op (apply_transforms ts (rf 1)) v
     then run_rule rf' cont p else None).
Proof.
  induction ts as [| t ts IH]; intros rf op v cont p.
  - exists rf. cbn [compile_transforms app run_rule]. reflexivity.
  - destruct t; cbn [compile_transforms compile_transform app run_rule];
      [ edestruct (IH (set_reg rf 1 (data_bitops (rf 1) mask xor))) as [rf' Hr]
      | edestruct (IH (set_reg rf 1 (data_shift shl amt (rf 1)))) as [rf' Hr]
      | edestruct (IH (set_reg rf 1 (data_byteorder hton size len (rf 1)))) as [rf' Hr] ];
      exists rf'; rewrite Hr; rewrite set_reg_same; reflexivity.
Qed.

(** The heart of the proof, generalized over the trailing program [tail]: as
    long as [tail] runs to a constant [res] from any register file (true for the
    verdict tail — an immediate / reject / empty — composed after the
    verdict-neutral statements), a compiled match-list followed by [tail] runs to
    [res] iff every match holds, else [None]. *)
Lemma run_compile_matches_const : forall ms tail res p,
  (forall rf, run_rule rf tail p = res) ->
  forall rf, run_rule rf (flat_map compile_match ms ++ tail) p =
    if forallb (fun m => eval_matchcond m p) ms then res else None.
Proof.
  induction ms as [| m ms IH]; intros tail res p Hc rf.
  - cbn [flat_map app forallb]. apply Hc.
  - destruct m as [f v0 | f v0 | f neg lo hi | f neg mask xor v0 | f neg nm elems
                  | f ts neg v0];
      cbn [flat_map compile_match app]; rewrite compile_load_correct.
    + cbn [run_rule]. rewrite set_reg_same. cbn [forallb eval_matchcond]. unfold eval_cmp.
      destruct (data_eqb (field_value f p) v0); cbn [andb negb];
        [apply IH; exact Hc | reflexivity].
    + cbn [run_rule]. rewrite set_reg_same. cbn [forallb eval_matchcond]. unfold eval_cmp.
      destruct (data_eqb (field_value f p) v0); cbn [andb negb];
        [reflexivity | apply IH; exact Hc].
    + cbn [run_rule]. rewrite set_reg_same. cbn [forallb eval_matchcond].
      destruct (eval_range (if neg then CNe else CEq) (field_value f p) lo hi);
        cbn [andb]; [apply IH; exact Hc | reflexivity].
    + cbn [run_rule]. rewrite !set_reg_same. cbn [forallb eval_matchcond].
      destruct (eval_cmp (if neg then CNe else CEq)
                 (data_bitops (field_value f p) mask xor) v0);
        cbn [andb]; [apply IH; exact Hc | reflexivity].
    + cbn [run_rule]. rewrite set_reg_same. cbn [forallb eval_matchcond].
      destruct (xorb neg (data_mem (field_value f p) elems));
        cbn [andb]; [apply IH; exact Hc | reflexivity].
    + (* MTransform *)
      rewrite <- !app_assoc. cbn [app].
      edestruct run_transforms_cmp as [rf' Hr]. rewrite Hr. rewrite set_reg_same.
      cbn [forallb eval_matchcond].
      destruct (eval_cmp (if neg then CNe else CEq)
                 (apply_transforms ts (field_value f p)) v0);
        cbn [andb]; [apply IH; exact Hc | reflexivity].
Qed.

(** Verdict-neutral statements pass through unchanged. *)
Lemma run_stmts_passthrough : forall ss rf tail p,
  run_rule rf (flat_map compile_stmt ss ++ tail) p = run_rule rf tail p.
Proof.
  induction ss as [| s ss IH]; intros rf tail p.
  - reflexivity.
  - destruct s; cbn [flat_map compile_stmt app run_rule]; apply IH.
Qed.

Definition verdict_result (v : verdict) : option verdict :=
  match v with Continue => None | _ => Some v end.

Lemma run_verdict_tail : forall v rf p,
  run_rule rf (verdict_tail v) p = verdict_result v.
Proof. intros v rf p. destruct v; reflexivity. Qed.

(** A compiled rule runs to its verdict exactly when it applies (the trailing
    verdict-neutral statements never change that). *)
Lemma run_rule_compile_rule : forall r p,
  run_rule empty_rf (compile_rule r) p =
  if rule_applies r p then verdict_result (r_verdict r) else None.
Proof.
  intros r p. unfold compile_rule, rule_applies.
  apply run_compile_matches_const.
  intro rf. rewrite run_stmts_passthrough. apply run_verdict_tail.
Qed.

(** Chain level: the compiled program reproduces the rule-list evaluation. *)
Lemma run_program_compile_chain : forall rs p,
  run_program (map compile_rule rs) p = eval_rules rs p.
Proof.
  induction rs as [| r rs IH]; intros p.
  - reflexivity.
  - cbn [map run_program eval_rules]. rewrite run_rule_compile_rule.
    destruct (rule_applies r p); destruct (r_verdict r);
      cbn [terminal verdict_result]; try reflexivity; apply IH.
Qed.

(** ** Main theorem: semantic preservation. *)
Theorem compile_chain_correct : forall c p,
  run_chain (compile_chain c) (c_policy c) p = eval_chain c p.
Proof.
  intros c p. unfold run_chain, eval_chain, compile_chain.
  rewrite run_program_compile_chain. reflexivity.
Qed.
