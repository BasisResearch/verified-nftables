(** * RegsValid_Proofs: EVERY frontend-emitted program passes the kernel
    register validator — the W2 discharge.

    [Lower.lower_rule] admits a rule only if its compiled image satisfies
    [RegsValid.regs_valid] (fail-loud [LEregalloc]), so the claim holds for
    the plain compile of every rule a successful [lower_ruleset] emits BY
    CONSTRUCTION.  The DEFAULT pipeline additionally runs nft's always-on
    linearization ([Optimize_Linearize.compile_chain_default] = compile after
    payload-merge + xor-fold); both stages PRESERVE validator success from
    their own guards alone:

      - a payload merge is admitted only when the combined width is within
        NFT_REG_SIZE = 16 bytes ([seg_can_merge], nft's payload_can_merge),
        so the fused load/cmp re-validates;
      - the xor constant transfer keeps every operand length
        ([xorfold_mc]'s guard pins |mask| = |xor| = |v|).

    HEADLINE: [lower_ruleset_default_regs_valid] — for every ruleset the
    frontend lowers, every chain's DEFAULT-pipeline bytecode passes
    [RegsValid.regs_valid_prog].  Quantified over ALL lowerings (the
    [lower_ruleset_numgen_free] pattern), no per-ruleset spot check, no
    hypothesis.  The `-O` consolidation passes construct new rules outside
    this statement; their outputs are checked empirically by the corpus
    round-trip's runtime [regs_valid] assertion (extracted/corpus_test.ml). *)

From Stdlib Require Import String List Bool PeanoNat Lia.
From Nft Require Import Bytes Packet Verdict Syntax Bytecode Compile RegsValid
  Optimize_PayMerge Optimize_XorFold Optimize_Linearize.
From Nft Require Import Ast Lower.
Import ListNotations.

(* ================================================================== *)
(** ** Small helpers. *)

Lemma forallb_map' : forall (A B : Type) (f : B -> bool) (g : A -> B) l,
  forallb f (map g l) = forallb (fun x => f (g x)) l.
Proof. induction l; cbn; congruence. Qed.

Lemma forallb_impl : forall (A : Type) (f g : A -> bool) l,
  (forall x, f x = true -> g x = true) ->
  forallb f l = true -> forallb g l = true.
Proof.
  intros A f g l Himp. induction l as [|x l IH]; cbn; intros H; [reflexivity|].
  apply andb_true_iff in H as [Hx Hl].
  rewrite (Himp _ Hx), (IH Hl). reflexivity.
Qed.

Lemma forallb_rev' : forall (A : Type) (f : A -> bool) (l : list A),
  forallb f (rev l) = forallb f l.
Proof.
  intros A f l. induction l as [|x l IH]; [reflexivity|].
  cbn [rev forallb]. rewrite forallb_app, IH.
  cbn [forallb]. rewrite Bool.andb_true_r, Bool.andb_comm. reflexivity.
Qed.

(** Register 1 (word index 4, the first data register) admits any transfer of
    1..64 bytes — the [nft_validate_register_load] bounds at index 4. *)
Lemma reg1_ok : forall n, 1 <= n -> n <= 64 -> reg_load_ok 1 n = true.
Proof.
  intros n H1 H2. destruct n as [|m]; [lia|].
  unfold reg_load_ok, nft_reg_index, nft_regfile_bytes, nft_reg32_num.
  cbn. apply Nat.leb_le. lia.
Qed.

Lemma imm_ok_intro : forall v, 1 <= length v -> length v <= 16 ->
  imm_value_ok v = true.
Proof.
  intros v H1 H2. unfold imm_value_ok, nft_data_value_max.
  remember (List.length v) as n eqn:En.
  destruct n as [|m]; [lia|].
  cbn. apply Nat.leb_le. lia.
Qed.

Lemma imm_ok_bounds : forall v, imm_value_ok v = true ->
  1 <= length v /\ length v <= 16.
Proof.
  intros v H. unfold imm_value_ok, nft_data_value_max in H.
  apply andb_true_iff in H as [H1 H2].
  split; apply Nat.leb_le; assumption.
Qed.

(* ================================================================== *)
(** ** The xor-fold stage preserves validator success. *)

Lemma xorfold_mc_regs : forall m,
  regs_valid (compile_match m) = true ->
  regs_valid (compile_match (xorfold_mc m)) = true.
Proof.
  intros m H.
  destruct m as [f v|f v|f n lo hi|f op mask xor v|f op v|fs n nm|f ts op v
                |f ts n nm|f ts n lo hi|sp|sp|sp|el n nm]; try exact H.
  cbn [xorfold_mc].
  destruct (data_eqb mask (repeat 255 (length v))
            && Nat.eqb (length xor) (length v)
            && match op with CEq | CNe => true | _ => false end)%bool eqn:G;
    [| exact H].
  apply andb_true_iff in G as [G _].
  apply andb_true_iff in G as [Gmask Gxor].
  apply data_eqb_true_iff in Gmask.
  apply Nat.eqb_eq in Gxor.
  assert (Hml : length mask = length v) by (rewrite Gmask; apply repeat_length).
  cbn [compile_match regs_valid forallb] in H |- *.
  apply andb_true_iff in H as [Hload H].
  apply andb_true_iff in H as [Hbw H].
  apply andb_true_iff in H as [Hcmp _].
  rewrite Hload. cbn [andb].
  cbn [instr_regs_ok] in Hbw, Hcmp |- *.
  apply andb_true_iff in Hcmp as [Hcmpl Hcmpi].
  apply andb_true_iff in Hbw as [Hbw Hbxi].
  apply andb_true_iff in Hbw as [Hbw _].
  apply andb_true_iff in Hbw as [Hbw Hxlen].
  apply andb_true_iff in Hbw as [Hbl Hbs].
  destruct (imm_ok_bounds _ Hcmpi) as [Hv1 Hv16].
  (* the rewritten bitwise: same mask, zero xor of length |v| *)
  rewrite Hbl, Hbs. cbn [andb].
  rewrite repeat_length, Hml, Nat.eqb_refl. cbn [andb].
  assert (Him : imm_value_ok mask = true)
    by (apply imm_ok_intro; rewrite Hml; assumption).
  rewrite Him. cbn [andb].
  assert (Hi0 : imm_value_ok (repeat 0 (length v)) = true)
    by (apply imm_ok_intro; rewrite repeat_length; assumption).
  rewrite Hi0. cbn [andb].
  (* the rewritten cmp: value length preserved (|v ^ xor| = |v|) *)
  assert (Hxl : length (data_xor v xor) = length v)
    by (rewrite data_xor_length, Gxor; apply Nat.min_id).
  rewrite Hxl, Hcmpl. cbn [andb].
  assert (Hix : imm_value_ok (data_xor v xor) = true)
    by (apply imm_ok_intro; rewrite Hxl; assumption).
  rewrite Hix. reflexivity.
Qed.

Lemma xorfold_bi_regs : forall it,
  regs_valid (compile_body_item it) = true ->
  regs_valid (compile_body_item (xorfold_bi it)) = true.
Proof.
  intros [m|s] H; [apply xorfold_mc_regs; exact H | exact H].
Qed.

Lemma xorfold_body_regs : forall body,
  regs_valid (flat_map compile_body_item body) = true ->
  regs_valid (flat_map compile_body_item (map xorfold_bi body)) = true.
Proof.
  induction body as [|it body IH]; intros H; [exact H|].
  cbn [map flat_map] in H |- *.
  rewrite regs_valid_app in H |- *.
  apply andb_true_iff in H as [H1 H2].
  rewrite (xorfold_bi_regs _ H1), (IH H2). reflexivity.
Qed.

(* ================================================================== *)
(** ** The payload-merge stage preserves validator success. *)

(** A recognised payload segment's compare value is a validated nft_data
    value (the segment IS a compiled load + cmp in the admitted rule). *)
Lemma payload_seg_imm : forall m b o l v,
  payload_seg m = Some (b, o, l, v) ->
  regs_valid (compile_match m) = true ->
  imm_value_ok v = true.
Proof.
  intros m b o l v S H. unfold payload_seg in S.
  destruct m as [f v0|f v0|f n lo hi|f op msk xr w|f op v0| | | | | | | | ];
    try discriminate.
  - destruct (field_load f) as [| | | | | | | | | | | | |b' o' l'] eqn:Efl;
      try discriminate.
    destruct (Nat.eqb (length v0) l') eqn:El; [|discriminate].
    injection S as <- <- <- <-.
    cbn [compile_match regs_valid forallb] in H.
    apply andb_true_iff in H as [_ H].
    apply andb_true_iff in H as [H _].
    cbn [instr_regs_ok] in H.
    apply andb_true_iff in H as [_ Hi]. exact Hi.
  - destruct op; try discriminate.
    destruct (field_load f) as [| | | | | | | | | | | | |b' o' l'] eqn:Efl;
      try discriminate.
    destruct (Nat.eqb (length v0) l') eqn:El; [|discriminate].
    injection S as <- <- <- <-.
    cbn [compile_match regs_valid forallb] in H.
    apply andb_true_iff in H as [_ H].
    apply andb_true_iff in H as [H _].
    cbn [instr_regs_ok] in H.
    apply andb_true_iff in H as [_ Hi]. exact Hi.
Qed.

Lemma try_merge_regs : forall m1 m2 m,
  try_merge m1 m2 = Some m ->
  regs_valid (compile_match m1) = true ->
  regs_valid (compile_match m2) = true ->
  regs_valid (compile_match m) = true.
Proof.
  intros m1 m2 m T H1 H2. unfold try_merge in T.
  destruct (payload_seg m1) as [[[[b1 o1] l1] v1]|] eqn:S1; [|discriminate].
  destruct (payload_seg m2) as [[[[b2 o2] l2] v2]|] eqn:S2; [|discriminate].
  destruct (seg_can_merge b1 o1 l1 b2 o2 l2) eqn:C; [|discriminate].
  injection T as <-.
  pose proof (payload_seg_imm _ _ _ _ _ S1 H1) as I1.
  pose proof (payload_seg_imm _ _ _ _ _ S2 H2) as I2.
  apply payload_seg_spec in S1 as (_ & _ & L1).
  apply payload_seg_spec in S2 as (_ & _ & L2).
  apply imm_ok_bounds in I1 as [I1a _]. apply imm_ok_bounds in I2 as [I2a _].
  unfold seg_can_merge in C.
  apply andb_true_iff in C as [C _].
  apply andb_true_iff in C as [_ Hle].
  apply Nat.leb_le in Hle.
  assert (Hl : length (v1 ++ v2) = l1 + l2)
    by (rewrite length_app, L1, L2; reflexivity).
  cbn [compile_match compile_load field_load regs_valid forallb instr_regs_ok].
  unfold reg_store_ok.
  rewrite Hl.
  rewrite !(reg1_ok (l1 + l2)) by lia.
  assert (Hi : imm_value_ok (v1 ++ v2) = true)
    by (apply imm_ok_intro; rewrite Hl; lia).
  rewrite Hi. reflexivity.
Qed.

Lemma merge_body_fuel_nil : forall fuel, merge_body_fuel fuel [] = [].
Proof. destruct fuel; reflexivity. Qed.

Lemma merge_body_fuel_regs : forall fuel body,
  regs_valid (flat_map compile_body_item body) = true ->
  regs_valid (flat_map compile_body_item (merge_body_fuel fuel body)) = true.
Proof.
  induction fuel as [|fk IH]; intros body H; [exact H|].
  destruct body as [|it rest]; [exact H|].
  destruct it as [m1|s1].
  - destruct rest as [|[m2|s2] rest'].
    + cbn [merge_body_fuel]. rewrite merge_body_fuel_nil. exact H.
    + cbn [merge_body_fuel].
      destruct (try_merge m1 m2) as [m|] eqn:T.
      * cbn [flat_map compile_body_item] in H.
        rewrite !regs_valid_app in H.
        apply andb_true_iff in H as [Hm1 H].
        apply andb_true_iff in H as [Hm2 Hrest].
        apply IH. cbn [flat_map compile_body_item].
        rewrite regs_valid_app,
          (try_merge_regs _ _ _ T Hm1 Hm2), Hrest.
        reflexivity.
      * cbn [flat_map compile_body_item] in H |- *.
        rewrite regs_valid_app in H |- *.
        apply andb_true_iff in H as [Hm1 Hrest].
        rewrite Hm1. cbn [andb].
        apply IH. cbn [flat_map compile_body_item]. exact Hrest.
    + cbn [merge_body_fuel].
      cbn [flat_map compile_body_item] in H |- *.
      rewrite regs_valid_app in H |- *.
      apply andb_true_iff in H as [Hm1 Hrest].
      rewrite Hm1. cbn [andb].
      apply IH. cbn [flat_map compile_body_item]. exact Hrest.
  - cbn [merge_body_fuel].
    cbn [flat_map compile_body_item] in H |- *.
    rewrite regs_valid_app in H |- *.
    apply andb_true_iff in H as [Hs Hrest].
    rewrite Hs, (IH _ Hrest). reflexivity.
Qed.

(* ================================================================== *)
(** ** Rule-level preservation and the per-rule discharge. *)

(** The frontend-checked per-rule predicate: the rule's own compiled image
    passes the kernel register validator ([Lower.lower_rule]'s admission). *)
Definition rule_regs_ok (r : rule) : bool := regs_valid (compile_rule r).

Lemma compile_rule_split : forall r,
  regs_valid (compile_rule r)
  = regs_valid (flat_map compile_body_item (r_body r))
    && (regs_valid (compile_end r)
        && regs_valid (flat_map compile_stmt (r_after r))).
Proof.
  intros r. unfold compile_rule. rewrite !regs_valid_app. reflexivity.
Qed.

Lemma paymerge_rule_regs : forall r,
  rule_regs_ok r = true -> rule_regs_ok (paymerge_rule r) = true.
Proof.
  intros r H. unfold rule_regs_ok in *.
  rewrite compile_rule_split in H |- *.
  (* end/after project [r_outcome]/[r_after], both copied verbatim *)
  change (compile_end (paymerge_rule r)) with (compile_end r).
  change (r_after (paymerge_rule r)) with (r_after r).
  rewrite paymerge_rule_body.
  apply andb_true_iff in H as [Hb Hrest].
  unfold merge_body.
  rewrite (merge_body_fuel_regs _ _ Hb), Hrest. reflexivity.
Qed.

Lemma xorfold_rule_regs : forall r,
  rule_regs_ok r = true -> rule_regs_ok (xorfold_rule r) = true.
Proof.
  intros r H. unfold rule_regs_ok in *.
  rewrite compile_rule_split in H |- *.
  change (compile_end (xorfold_rule r)) with (compile_end r).
  change (r_after (xorfold_rule r)) with (r_after r).
  rewrite xorfold_r_body.
  apply andb_true_iff in H as [Hb Hrest].
  rewrite (xorfold_body_regs _ Hb), Hrest. reflexivity.
Qed.

(** The always-on linearization (the DEFAULT pipeline's rewrite stage)
    preserves the validator. *)
Lemma linearize_rule_regs : forall r,
  rule_regs_ok r = true ->
  rule_regs_ok (xorfold_rule (paymerge_rule r)) = true.
Proof.
  intros r H. apply xorfold_rule_regs, paymerge_rule_regs, H.
Qed.

(** [lower_rule]'s fail-loud admission, read back: every emitted rule's
    compiled image validates. *)
Lemma lower_rule_regs : forall oracle fuel family defs cls fs r fs',
  lower_rule oracle fuel family defs cls fs = LOk (r, fs') ->
  rule_regs_ok r = true.
Proof.
  intros oracle fuel family defs cls fs r fs' H.
  unfold lower_rule in H.
  destruct (lower_clauses oracle fuel family defs cls rl0 fs) as [[rl fs1]|];
    [| discriminate H].
  cbn in H.
  destruct (assemble_outcome rl) as [outc|]; [| discriminate H].
  cbn in H.
  destruct (rule_numgen_free
              {| r_body := rev (rl_body rl); r_outcome := outc; r_after := nil |});
    [| discriminate H].
  match type of H with (if ?b then _ else _) = _ =>
    destruct b eqn:E; [| discriminate H] end.
  injection H as <- _. exact E.
Qed.

(* ================================================================== *)
(** ** Plumbing over chains/tables (the [lower_ruleset_numgen_free] walk). *)

Lemma lower_chain_items_regs :
  forall oracle fuel family defs items pol rules fs pol' rules' fs',
    lower_chain_items oracle fuel family defs items pol rules fs
      = LOk (pol', rules', fs') ->
    forallb rule_regs_ok rules = true ->
    forallb rule_regs_ok rules' = true.
Proof.
  intros oracle fuel family defs items.
  induction items as [| it items IH]; intros pol rules fs pol' rules' fs' H Hacc.
  - cbn in H. injection H as <- <- <-. exact Hacc.
  - destruct it; cbn in H.
    + eapply IH; eassumption.
    + eapply IH; eassumption.
    + destruct (lower_rule oracle fuel family defs r fs) as [[r0 fs1]|] eqn:Hr;
        [| discriminate H].
      cbn in H.
      eapply IH; [exact H |].
      cbn [forallb]. rewrite (lower_rule_regs _ _ _ _ _ _ _ _ Hr), Hacc.
      reflexivity.
Qed.

Lemma lower_chain_regs : forall oracle fuel family defs sc fs nm c hk fs',
  lower_chain oracle fuel family defs sc fs = LOk ((nm, c), hk, fs') ->
  forallb rule_regs_ok (c_rules c) = true.
Proof.
  intros oracle fuel family defs sc fs nm c hk fs' H.
  unfold lower_chain in H.
  destruct (match chain_hookinfo (sc_items sc) with
            | Some (_, h, _, _) => if is_known_hook h then LOk tt else LErr (LEhook h)
            | None => LOk tt end); [| discriminate H].
  cbn in H.
  destruct (lower_chain_items oracle fuel family defs (sc_items sc) None nil fs)
    as [[[pol rules] fs1]|] eqn:Hi; [| discriminate H].
  cbn in H. injection H as _ <- _ _.
  cbn [c_rules]. rewrite forallb_rev'.
  eapply lower_chain_items_regs; [exact Hi | reflexivity].
Qed.

Definition chains_regs_ok (chains : list (string * chain)) : bool :=
  forallb (fun nc => forallb rule_regs_ok (c_rules (snd nc))) chains.

Lemma lower_table_chains_regs :
  forall oracle fuel defs family items chains hooks fs chains' hooks' fs',
    lower_table_chains oracle fuel defs family items chains hooks fs
      = LOk (chains', hooks', fs') ->
    chains_regs_ok chains = true ->
    chains_regs_ok chains' = true.
Proof.
  intros oracle fuel defs family items.
  induction items as [| it items IH]; intros chains hooks fs chains' hooks' fs' H Hacc.
  - cbn in H. injection H as <- _ _. unfold chains_regs_ok. rewrite forallb_rev'.
    exact Hacc.
  - destruct it; cbn in H; try (eapply IH; eassumption).
    destruct (lower_chain oracle fuel family defs c fs)
      as [[[[nm c0] hk] fs1]|] eqn:Hc; [| discriminate H].
    cbn in H.
    eapply IH; [exact H |].
    unfold chains_regs_ok in Hacc |- *. cbn [forallb snd].
    rewrite (lower_chain_regs _ _ _ _ _ _ _ _ _ _ Hc), Hacc. reflexivity.
Qed.

Definition tables_regs_ok
    (tables : list (string * string * list (string * chain))) : bool :=
  forallb (fun t => let '(_, _, chains) := t in chains_regs_ok chains) tables.

Lemma lower_tables_regs :
  forall oracle fuel defs rs tables allhooks fs tables' hooks' fs',
    lower_tables oracle fuel defs rs tables allhooks fs
      = LOk (tables', hooks', fs') ->
    tables_regs_ok tables = true ->
    tables_regs_ok tables' = true.
Proof.
  intros oracle fuel defs rs.
  induction rs as [| tl rs IH]; intros tables allhooks fs tables' hooks' fs' H Hacc.
  - cbn in H. injection H as <- _ _.
    unfold tables_regs_ok in Hacc |- *. rewrite forallb_rev'. exact Hacc.
  - destruct tl; cbn in H; try (eapply IH; eassumption).
    destruct (lower_table_chains oracle fuel defs (st_family t) (st_items t) nil nil fs)
      as [[[chains hooks] fs1]|] eqn:Hc; [| discriminate H].
    cbn in H.
    eapply IH; [exact H |].
    unfold tables_regs_ok in Hacc |- *. cbn [forallb].
    rewrite Hacc, Bool.andb_true_r.
    exact (lower_table_chains_regs _ _ _ _ _ _ _ _ _ _ _ Hc eq_refl).
Qed.

(** Every rule of every chain a successful lowering emits has a
    validator-passing compiled image. *)
Theorem lower_ruleset_regs_ok : forall oracle rs lr,
  lower_ruleset oracle rs = LOk lr ->
  tables_regs_ok (lr_tables lr) = true.
Proof.
  intros oracle rs lr H. unfold lower_ruleset in H.
  destruct (lower_setdecls_top _ _ _ _) as [fs1|]; [| discriminate H].
  cbn in H.
  destruct (lower_tables oracle _ (collect_defines rs) rs nil nil fs1)
    as [[[tables hooks] fs2]|] eqn:Ht; [| discriminate H].
  cbn in H. injection H as <-. cbn [lr_tables].
  exact (lower_tables_regs _ _ _ _ _ _ _ _ _ _ Ht eq_refl).
Qed.

(* ================================================================== *)
(** ** The program-level headlines. *)

Lemma compile_chain_default_rules : forall c,
  compile_chain_default c
  = map (fun r => compile_rule (xorfold_rule (paymerge_rule r))) (c_rules c).
Proof.
  intros c.
  unfold compile_chain_default, linearize_chain, compile_chain.
  cbn [xorfold_chain paymerge_chain c_rules].
  rewrite !map_map. reflexivity.
Qed.

(** A chain of validator-passing rules compiles to a validator-passing
    program — through the DEFAULT (always-on linearization) pipeline. *)
Lemma chain_default_regs_valid : forall c,
  forallb rule_regs_ok (c_rules c) = true ->
  regs_valid_prog (compile_chain_default c) = true.
Proof.
  intros c H. rewrite compile_chain_default_rules.
  unfold regs_valid_prog. rewrite forallb_map'.
  eapply forallb_impl; [| exact H].
  intros r Hr. apply (linearize_rule_regs _ Hr).
Qed.

(** HEADLINE (W2): for EVERY ruleset the frontend lowers, EVERY chain's
    DEFAULT-pipeline bytecode passes the kernel register validator
    ([nft_validate_register_load]/[nft_validate_register_store] mirrored by
    [RegsValid.regs_valid]).  Quantified over all lowerings; no hypothesis.
    Axiom-free (gated in `make axioms`). *)
Theorem lower_ruleset_default_regs_valid : forall oracle rs lr,
  lower_ruleset oracle rs = LOk lr ->
  forallb (fun t => let '(_, _, chains) := t in
      forallb (fun nc => regs_valid_prog (compile_chain_default (snd nc))) chains)
    (lr_tables lr) = true.
Proof.
  intros oracle rs lr H.
  pose proof (lower_ruleset_regs_ok _ _ _ H) as Hok.
  unfold tables_regs_ok in Hok.
  eapply forallb_impl; [| exact Hok].
  intros [[tn tf] chains] Hc.
  unfold chains_regs_ok in Hc.
  eapply forallb_impl; [| exact Hc].
  intros nc Hnc. apply chain_default_regs_valid, Hnc.
Qed.

(** The PLAIN-compile mirror (no linearization): the same claim for
    [compile_chain] directly — the exact image [lower_rule] admits. *)
Theorem lower_ruleset_compile_regs_valid : forall oracle rs lr,
  lower_ruleset oracle rs = LOk lr ->
  forallb (fun t => let '(_, _, chains) := t in
      forallb (fun nc => regs_valid_prog (compile_chain (snd nc))) chains)
    (lr_tables lr) = true.
Proof.
  intros oracle rs lr H.
  pose proof (lower_ruleset_regs_ok _ _ _ H) as Hok.
  unfold tables_regs_ok in Hok.
  eapply forallb_impl; [| exact Hok].
  intros [[tn tf] chains] Hc.
  unfold chains_regs_ok in Hc.
  eapply forallb_impl; [| exact Hc].
  intros nc Hnc. unfold compile_chain.
  unfold regs_valid_prog. rewrite forallb_map'. exact Hnc.
Qed.

(* ================================================================== *)
(** ** Non-vacuity: the validator genuinely rejects — an out-of-file store
    and a >16-byte immediate both fail, and a real compiled rule passes. *)

Example regs_valid_rejects_out_of_file :
  instr_regs_ok (IMetaLoad MKiifname 23) = false.
Proof. vm_compute. reflexivity. Qed.  (* 16-byte name at NFT_REG32_15: word 19*4+16 > 80 *)

Example regs_valid_rejects_wide_immediate :
  instr_regs_ok (IImmediateData 1 (repeat 0 17)) = false.
Proof. vm_compute. reflexivity. Qed.  (* an nft_data value is at most 16 bytes *)

Example regs_valid_accepts_compiled_match :
  regs_valid (compile_match (MEq FThDport [0; 22])) = true.
Proof. vm_compute. reflexivity. Qed.

(** Axiom-freedom audit (build-time guard; enforcement is `make axioms`). *)
Print Assumptions lower_ruleset_default_regs_valid.
Print Assumptions lower_ruleset_compile_regs_valid.
