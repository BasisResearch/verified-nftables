(** * Correct: the compiler is semantics preserving.

    Main result [compile_chain_correct]: for every base chain and every packet,
    running the compiled control-plane bytecode yields exactly the verdict the
    declarative semantics assigns.  Equivalently, the netlink ruleset [nft] would
    install filters packets exactly as the DSL specifies. *)

From Stdlib Require Import List NArith Bool Lia PeanoNat.
From Nft Require Import Bytes Packet Verdict Syntax Bytecode Semantics Compile.
Import ListNotations.

(** Executing a compiled load writes the field's value into the destination
    register and falls through to the rest of the program (any [dst]). *)
Lemma compile_load_correct : forall f dst rf rest p,
  run_rule rf (compile_load (field_load f) dst :: rest) p =
  run_rule (set_reg rf dst (field_value f p)) rest p.
Proof.
  intros f dst rf rest p. unfold field_value, do_load, compile_load.
  destruct (field_load f) eqn:E; simpl; reflexivity.
Qed.

(** ** Multi-register concatenation: the allocator emits distinct registers, so
    the per-field loads do not clobber one another and the lookup reads exactly
    the concatenation of the field values. *)

Lemma field_slots_pos : forall f, 1 <= field_slots f.
Proof. intro f. unfold field_slots. apply Nat.le_max_l. Qed.

Lemma reg_of_slot_mono : forall a b, a < b -> reg_of_slot a < reg_of_slot b.
Proof.
  intros a b H. unfold reg_of_slot. destruct a; destruct b; simpl; lia.
Qed.

Lemma alloc_regs_lb : forall fields slot r,
  In r (map snd (alloc_regs slot fields)) -> reg_of_slot slot <= r.
Proof.
  induction fields as [| f fs IH]; intros slot r Hin; simpl in Hin.
  - contradiction.
  - destruct Hin as [Heq | Hin].
    + subst r. reflexivity.
    + apply IH in Hin. pose proof (field_slots_pos f).
      assert (slot < slot + field_slots f) as Hlt by lia.
      apply reg_of_slot_mono in Hlt. lia.
Qed.

Lemma alloc_regs_nodup : forall fields slot, NoDup (map snd (alloc_regs slot fields)).
Proof.
  induction fields as [| f fs IH]; intros slot; simpl.
  - constructor.
  - constructor.
    + intro Hin. apply alloc_regs_lb in Hin. pose proof (field_slots_pos f).
      assert (slot < slot + field_slots f) as Hlt by lia.
      apply reg_of_slot_mono in Hlt. lia.
    + apply IH.
Qed.

Lemma alloc_regs_fst : forall fields slot,
  map (@fst field reg) (alloc_regs slot fields) = fields.
Proof. induction fields; intros; simpl; [reflexivity | f_equal; auto]. Qed.

Lemma map_fst_field : forall (pairs : list (field * reg)) p,
  map (fun fr => field_value (fst fr) p) pairs
  = map (fun f => field_value f p) (map (@fst field reg) pairs).
Proof. induction pairs; intros; simpl; [reflexivity | f_equal; auto]. Qed.

(** The net effect of the field loads on the register file. *)
Fixpoint write_fields (rf : regfile) (pairs : list (field * reg)) (p : packet) : regfile :=
  match pairs with
  | []           => rf
  | (f, r) :: rest => write_fields (set_reg rf r (field_value f p)) rest p
  end.

Lemma write_fields_other : forall pairs rf p r,
  ~ In r (map snd pairs) -> write_fields rf pairs p r = rf r.
Proof.
  induction pairs as [| [f r'] rest IH]; intros rf p r Hni; simpl in *.
  - reflexivity.
  - rewrite IH by (intro Hin; apply Hni; right; exact Hin).
    apply set_reg_other. intro Heq; apply Hni; left; exact Heq.
Qed.

Lemma map_write_fields : forall pairs rf p,
  NoDup (map snd pairs) ->
  map (write_fields rf pairs p) (map snd pairs)
  = map (fun fr => field_value (fst fr) p) pairs.
Proof.
  induction pairs as [| [f r] rest IH]; intros rf p Hnd; simpl in *.
  - reflexivity.
  - inversion Hnd as [| ? ? Hni Hnd' ]; subst. f_equal.
    + rewrite write_fields_other by assumption. apply set_reg_same.
    + apply IH. assumption.
Qed.

Lemma run_load_fields : forall pairs rf tail p,
  run_rule rf (load_fields pairs ++ tail) p = run_rule (write_fields rf pairs p) tail p.
Proof.
  induction pairs as [| [f r] rest IH]; intros rf tail p.
  - reflexivity.
  - cbn [load_fields map fst snd app write_fields].
    rewrite compile_load_correct. apply IH.
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
      | edestruct (IH (set_reg rf 1 (data_byteorder hton size len (rf 1)))) as [rf' Hr]
      | edestruct (IH (set_reg rf 1 (data_jhash len seed modulus offset (rf 1)))) as [rf' Hr] ];
      exists rf'; rewrite Hr; rewrite set_reg_same; reflexivity.
Qed.

(** General version: a transform chain leaves register 1 holding the transformed
    value and is otherwise transparent to the trailing program (which reads reg
    1).  Reusable for any tester after the transforms (cmp / range / lookup). *)
Lemma run_compile_transform : forall t rf rest p,
  run_rule rf (compile_transform t :: rest) p
  = run_rule (set_reg rf 1 (apply_transform t (rf 1))) rest p.
Proof. intros t rf rest p. destruct t; reflexivity. Qed.

Lemma run_transforms_prefix : forall ts rf rest p,
  exists rf', rf' 1 = apply_transforms ts (rf 1) /\
    run_rule rf (compile_transforms ts ++ rest) p = run_rule rf' rest p.
Proof.
  induction ts as [| t ts IH]; intros rf rest p.
  - exists rf. split; reflexivity.
  - cbn [compile_transforms app]. rewrite run_compile_transform.
    edestruct (IH (set_reg rf 1 (apply_transform t (rf 1)))) as [rf' [H1 H2]].
    exists rf'. rewrite set_reg_same in H1. split; [exact H1 | exact H2].
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
  - destruct m as [f v0 | f v0 | f neg lo hi | f neg mask xor v0 | f op v0
                  | fields neg nm elems | f ts op v0 | f ts neg nm elems
                  | f ts neg lo hi | spec | qspec | clspec];
      cbn [flat_map compile_match app].
    + (* MEq *) rewrite compile_load_correct.
      cbn [run_rule]. rewrite set_reg_same. cbn [forallb eval_matchcond]. unfold eval_cmp.
      destruct (data_eqb (field_value f p) v0); cbn [andb negb];
        [apply IH; exact Hc | reflexivity].
    + (* MNeq *) rewrite compile_load_correct.
      cbn [run_rule]. rewrite set_reg_same. cbn [forallb eval_matchcond]. unfold eval_cmp.
      destruct (data_eqb (field_value f p) v0); cbn [andb negb];
        [reflexivity | apply IH; exact Hc].
    + (* MRange *) rewrite compile_load_correct.
      cbn [run_rule]. rewrite set_reg_same. cbn [forallb eval_matchcond].
      destruct (eval_range (if neg then CNe else CEq) (field_value f p) lo hi);
        cbn [andb]; [apply IH; exact Hc | reflexivity].
    + (* MMasked *) rewrite compile_load_correct.
      cbn [run_rule]. rewrite !set_reg_same. cbn [forallb eval_matchcond].
      destruct (eval_cmp (if neg then CNe else CEq)
                 (data_bitops (field_value f p) mask xor) v0);
        cbn [andb]; [apply IH; exact Hc | reflexivity].
    + (* MCmp: ordered comparison *) rewrite compile_load_correct.
      cbn [run_rule]. rewrite set_reg_same. cbn [forallb eval_matchcond].
      destruct (eval_cmp op (field_value f p) v0);
        cbn [andb]; [apply IH; exact Hc | reflexivity].
    + (* MConcatSet: multi-register key, distinct registers per field *)
      rewrite <- !app_assoc. cbn [app].
      rewrite run_load_fields. cbn [run_rule].
      rewrite map_write_fields by apply alloc_regs_nodup.
      rewrite map_fst_field, alloc_regs_fst.
      cbn [forallb eval_matchcond].
      destruct (xorb neg
                 (data_mem (concat (map (fun f => field_value f p) fields)) elems));
        cbn [andb]; [apply IH; exact Hc | reflexivity].
    + (* MTransform *) rewrite compile_load_correct.
      rewrite <- !app_assoc. cbn [app].
      edestruct run_transforms_cmp as [rf' Hr]. rewrite Hr. rewrite set_reg_same.
      cbn [forallb eval_matchcond].
      destruct (eval_cmp op
                 (apply_transforms ts (field_value f p)) v0);
        cbn [andb]; [apply IH; exact Hc | reflexivity].
    + (* MSetT: set membership of a transformed value *)
      rewrite compile_load_correct. rewrite <- !app_assoc. cbn [app].
      edestruct (run_transforms_prefix ts (set_reg rf 1 (field_value f p))
                  (ILookup [1] nm neg elems :: (flat_map compile_match ms ++ tail)) p)
        as [rf' [H1 H2]].
      rewrite H2. cbn [run_rule concat map]. rewrite app_nil_r, H1, set_reg_same.
      cbn [forallb eval_matchcond].
      destruct (xorb neg (data_mem (apply_transforms ts (field_value f p)) elems));
        cbn [andb]; [apply IH; exact Hc | reflexivity].
    + (* MRangeT: range of a transformed value *)
      rewrite compile_load_correct. rewrite <- !app_assoc. cbn [app].
      edestruct (run_transforms_prefix ts (set_reg rf 1 (field_value f p))
                  (IRange (if neg then CNe else CEq) 1 lo hi
                   :: (flat_map compile_match ms ++ tail)) p) as [rf' [H1 H2]].
      rewrite H2. cbn [run_rule]. rewrite H1, set_reg_same.
      cbn [forallb eval_matchcond].
      destruct (eval_range (if neg then CNe else CEq)
                 (apply_transforms ts (field_value f p)) lo hi);
        cbn [andb]; [apply IH; exact Hc | reflexivity].
    + (* MLimit: no load, a stateful break *)
      cbn [run_rule forallb eval_matchcond].
      destruct (pkt_limit p spec); cbn [andb];
        [apply IH; exact Hc | reflexivity].
    + (* MQuota: no load, a stateful break *)
      cbn [run_rule forallb eval_matchcond].
      destruct (pkt_quota p qspec); cbn [andb];
        [apply IH; exact Hc | reflexivity].
    + (* MConnlimit: no load, a stateful break *)
      cbn [run_rule forallb eval_matchcond].
      destruct (pkt_connlimit p clspec); cbn [andb];
        [apply IH; exact Hc | reflexivity].
Qed.

(** Statements never produce a verdict; they leave the register file in *some*
    state (a value-source may load register 1 via a load + transform chain, which
    yields an existential register file) and fall through to the verdict tail.
    Because every verdict tail is register-independent, this existential is all
    the rule-correctness proof needs. *)
Lemma run_vsrc_exists : forall vs rf rest p,
  exists rf', run_rule rf (compile_vsrc vs ++ rest) p = run_rule rf' rest p.
Proof.
  destruct vs as [v | f ts | fields vts name entries | hf hl hs hm ho]; intros rf rest p.
  - exists (set_reg rf 1 v). reflexivity.
  - edestruct (run_transforms_prefix ts (set_reg rf 1 (field_value f p)) rest p)
      as [rf' [_ Hr]].
    exists rf'. cbn [compile_vsrc app]. rewrite compile_load_correct. exact Hr.
  - (* VMap: concat key loaded, optionally transformed, then ILookupVal writes
       dreg; all verdict-neutral, so the verdict tail is reached from some rf. *)
    cbn [compile_vsrc]. rewrite <- !app_assoc. rewrite run_load_fields.
    edestruct (run_transforms_prefix vts (write_fields rf (alloc_regs 0 fields) p)
                ([ILookupVal (map snd (alloc_regs 0 fields)) name 1 entries] ++ rest) p)
      as [rf' [_ Hr]].
    rewrite Hr. cbn [app run_rule]. eexists; reflexivity.
  - (* VHash: load the concat source fields, then the verdict-neutral IJhash *)
    cbn [compile_vsrc]. rewrite <- app_assoc. rewrite run_load_fields.
    cbn [app run_rule]. eexists; reflexivity.
Qed.

(** Operand immediates are verdict-neutral: running them leaves the tail reached
    from some register file. *)
Lemma run_imms_through : forall imms rf tail p,
  exists rf', run_rule rf (map (fun rv => IImmediateData (fst rv) (snd rv)) imms ++ tail) p
            = run_rule rf' tail p.
Proof.
  induction imms as [| [r v] rest IH]; intros rf tail p.
  - exists rf. reflexivity.
  - cbn [map fst snd app run_rule]. apply IH.
Qed.

Lemma run_stmt_exists : forall s rf rest p,
  exists rf', run_rule rf (compile_stmt s ++ rest) p = run_rule rf' rest p.
Proof.
  destruct s; intros rf rest p; try (exists rf; reflexivity).
  - (* SMangle *) edestruct (run_vsrc_exists vs rf
      (IPayloadWrite 1 b off len ctype coff cflags :: rest) p) as [rf' Hr].
    exists rf'. cbn [compile_stmt]. rewrite <- app_assoc. cbn [app].
    rewrite Hr. reflexivity.
  - (* SMetaSet *) edestruct (run_vsrc_exists vs rf (IMetaSet k 1 :: rest) p) as [rf' Hr].
    exists rf'. cbn [compile_stmt]. rewrite <- app_assoc. cbn [app].
    rewrite Hr. reflexivity.
  - (* SCtSet *) edestruct (run_vsrc_exists vs rf (ICtSet k 1 :: rest) p) as [rf' Hr].
    exists rf'. cbn [compile_stmt]. rewrite <- app_assoc. cbn [app].
    rewrite Hr. reflexivity.
  - (* SCtSetDir *) edestruct (run_vsrc_exists vs rf (ICtSetDir key dir 1 :: rest) p) as [rf' Hr].
    exists rf'. cbn [compile_stmt]. rewrite <- app_assoc. cbn [app].
    rewrite Hr. reflexivity.
  - (* SDynset: load the concat key fields, then the verdict-neutral IDynset *)
    cbn [compile_stmt]. rewrite <- app_assoc. rewrite run_load_fields.
    cbn [app run_rule]. eexists; reflexivity.
  - (* SDup: operand immediates, then the verdict-neutral IDup *)
    edestruct (run_imms_through imms rf (IDup devreg addrreg :: rest) p) as [rf' Hr].
    exists rf'. cbn [compile_stmt]. rewrite <- app_assoc. cbn [app].
    rewrite Hr. cbn [run_rule]. reflexivity.
  - (* SObjrefMap: load the key fields, then the verdict-neutral IObjrefMap *)
    cbn [compile_stmt]. rewrite <- app_assoc. rewrite run_load_fields.
    cbn [app run_rule]. eexists; reflexivity.
  - (* SExthdrWrite: value source, then the verdict-neutral IExthdrWrite *)
    edestruct (run_vsrc_exists vs rf (IExthdrWrite proto htype off len 1 :: rest) p) as [rf' Hr].
    exists rf'. cbn [compile_stmt]. rewrite <- app_assoc. cbn [app].
    rewrite Hr. reflexivity.
Qed.

Lemma run_stmts_exists : forall ss rf tail p,
  exists rf', run_rule rf (flat_map compile_stmt ss ++ tail) p = run_rule rf' tail p.
Proof.
  induction ss as [| s ss IH]; intros rf tail p.
  - exists rf. reflexivity.
  - cbn [flat_map]. rewrite <- app_assoc.
    edestruct (run_stmt_exists s rf (flat_map compile_stmt ss ++ tail) p) as [rf1 H1].
    rewrite H1. edestruct (IH rf1 tail p) as [rf2 H2]. exists rf2. rewrite H2. reflexivity.
Qed.

Definition verdict_result (v : verdict) : option verdict :=
  match v with Continue => None | v0 => Some v0 end.

Lemma run_verdict_tail : forall v rf p,
  run_rule rf (verdict_tail v) p = verdict_result v.
Proof. intros v rf p. destruct v; reflexivity. Qed.

(** A compiled rule runs to its verdict exactly when it applies (the trailing
    verdict-neutral statements never change that). *)
(** A NAT outcome: the operand immediates pass through and the terminal [INat]
    accepts. *)
Lemma run_imms_nat : forall imms tail rf k fam amin amax pmin pmax fl p,
  run_rule rf (map (fun rv => IImmediateData (fst rv) (snd rv)) imms
               ++ INat k fam amin amax pmin pmax fl :: tail) p = Some Accept.
Proof.
  induction imms as [| [r v] rest IH]; intros; cbn [map fst snd app run_rule].
  - reflexivity.
  - apply IH.
Qed.

(** A tproxy outcome: the operand immediates pass through and the terminal
    [ITproxy] accepts (ignoring anything after it). *)
Lemma run_imms_tproxy : forall imms tail rf fam areg preg p,
  run_rule rf (map (fun rv => IImmediateData (fst rv) (snd rv)) imms
               ++ ITproxy fam areg preg :: tail) p = Some Accept.
Proof.
  induction imms as [| [r v] rest IH]; intros; cbn [map fst snd app run_rule].
  - reflexivity.
  - apply IH.
Qed.

(** A fwd outcome: the operand immediates pass through and the terminal [IFwd]
    accepts (ignoring anything after it). *)
Lemma run_imms_fwd : forall imms tail rf dev addr nfp p,
  run_rule rf (map (fun rv => IImmediateData (fst rv) (snd rv)) imms
               ++ IFwd dev addr nfp :: tail) p = Some Accept.
Proof.
  induction imms as [| [r v] rest IH]; intros; cbn [map fst snd app run_rule].
  - reflexivity.
  - apply IH.
Qed.

(** A queue outcome: the operand immediates pass through and the terminal
    [IQueueSreg] accepts (ignoring anything after it). *)
Lemma run_imms_queue : forall imms tail rf sreg b f p,
  run_rule rf (map (fun rv => IImmediateData (fst rv) (snd rv)) imms
               ++ IQueueSreg sreg b f :: tail) p = Some Accept.
Proof.
  induction imms as [| [r v] rest IH]; intros; cbn [map fst snd app run_rule].
  - reflexivity.
  - apply IH.
Qed.

(** A value-sourced queue number: the value source is verdict-neutral, then the
    terminal [IQueueSreg] accepts. *)
Lemma run_vsrc_queue : forall vs tail rf sreg b f p,
  run_rule rf (compile_vsrc vs ++ IQueueSreg sreg b f :: tail) p = Some Accept.
Proof.
  intros. edestruct (run_vsrc_exists vs rf (IQueueSreg sreg b f :: tail) p) as [rf' Hr].
  rewrite Hr. cbn [run_rule]. reflexivity.
Qed.

(** A map-sourced NAT operand: load the key (+ transforms), look it up in the map
    (into reg 1), then the terminal [INat] accepts — all verdict-neutral until
    [INat]. *)
Lemma run_map_nat : forall fields ts name tail rf k fam amin amax pmin pmax fl p,
  run_rule rf
    ((load_fields (alloc_regs 0 fields) ++ compile_transforms ts
        ++ [ILookupVal (map snd (alloc_regs 0 fields)) name 1 []])
     ++ INat k fam amin amax pmin pmax fl :: tail) p = Some Accept.
Proof.
  intros. rewrite <- !app_assoc. rewrite run_load_fields.
  edestruct (run_transforms_prefix ts (write_fields rf (alloc_regs 0 fields) p)
              ([ILookupVal (map snd (alloc_regs 0 fields)) name 1 []]
                 ++ INat k fam amin amax pmin pmax fl :: tail) p) as [rf' [_ Hr]].
  rewrite Hr. cbn [app run_rule]. reflexivity.
Qed.

(** A field-sourced NAT operand: load the field (+ transforms), then the terminal
    [INat] accepts. *)
Lemma run_field_nat : forall f ts tail rf k fam amin amax pmin pmax fl p,
  run_rule rf ((compile_load (field_load f) 1 :: compile_transforms ts)
               ++ INat k fam amin amax pmin pmax fl :: tail) p = Some Accept.
Proof.
  intros. cbn [app]. rewrite compile_load_correct.
  edestruct (run_transforms_prefix ts (set_reg rf 1 (field_value f p))
              (INat k fam amin amax pmin pmax fl :: tail) p) as [rf' [_ Hr]].
  rewrite Hr. cbn [run_rule]. reflexivity.
Qed.

(** Running verdict-neutral statements alone falls through to [None]. *)
Lemma run_stmts_none : forall ss rf p,
  run_rule rf (flat_map compile_stmt ss) p = None.
Proof.
  intros ss rf p. edestruct (run_stmts_exists ss rf [] p) as [rf' H].
  rewrite app_nil_r in H. rewrite H. reflexivity.
Qed.

(** A static verdict tail followed by trailing statements: a terminal verdict
    ignores them; a [Continue] tail runs them (verdict-neutrally) to [None]. *)
Lemma run_verdict_tail_after : forall v tail rf p,
  run_rule rf (verdict_tail v ++ tail) p =
    match v with Continue => run_rule rf tail p | _ => verdict_result v end.
Proof. destruct v; cbn [verdict_tail app run_rule]; reflexivity. Qed.

(** The body version: an ordered list of matches and verdict-neutral statements.
    A [BMatch] is the single-match step (reusing [run_compile_matches_const] at a
    one-element list); a [BStmt] threads the register file through and drops out
    of [body_matches]. *)
Lemma run_compile_body : forall body tail res p,
  (forall rf, run_rule rf tail p = res) ->
  forall rf, run_rule rf (flat_map compile_body_item body ++ tail) p =
    if forallb (fun m => eval_matchcond m p) (body_matches body) then res else None.
Proof.
  induction body as [| it body IH]; intros tail res p Hc rf.
  - cbn [flat_map app body_matches forallb]. apply Hc.
  - destruct it as [m | s]; cbn [flat_map compile_body_item]; rewrite <- app_assoc.
    + (* BMatch m: a single-match step, then the rest of the body *)
      replace (compile_match m ++ (flat_map compile_body_item body ++ tail))
        with (flat_map compile_match [m] ++ (flat_map compile_body_item body ++ tail))
        by (cbn [flat_map app]; rewrite app_nil_r; reflexivity).
      rewrite (run_compile_matches_const [m] (flat_map compile_body_item body ++ tail)
                 (if forallb (fun m => eval_matchcond m p) (body_matches body) then res else None)
                 p (fun rf0 => IH tail res p Hc rf0)).
      cbn [body_matches flat_map app forallb]. rewrite Bool.andb_true_r.
      destruct (eval_matchcond m p); reflexivity.
    + (* BStmt s: verdict-neutral, drops out of body_matches *)
      cbn [body_matches flat_map app].
      edestruct (run_stmt_exists s rf (flat_map compile_body_item body ++ tail) p) as [rf' Hr].
      rewrite Hr. apply IH; exact Hc.
Qed.

Lemma run_rule_compile_rule : forall r p,
  run_rule empty_rf (compile_rule r) p =
  if rule_applies r p then outcome r p else None.
Proof.
  intros r p. unfold compile_rule, rule_applies.
  apply run_compile_body.
  (* the trailing tail is the outcome instrs then the post-outcome statements;
     a terminal outcome ignores them, a Continue tail runs them to None *)
  intro rf. unfold compile_end, outcome. destruct (r_nat r) as [n |].
  - rewrite <- app_assoc. destruct (nat_map n) as [[[fields ts] name] |].
    + apply run_map_nat.
    + destruct (nat_field n) as [[f ts] |]; [apply run_field_nat | apply run_imms_nat].
  - destruct (r_tproxy r) as [t |].
    + rewrite <- app_assoc. apply run_imms_tproxy.
    + destruct (r_fwd r) as [w |].
      * rewrite <- app_assoc. apply run_imms_fwd.
      * destruct (r_queue r) as [q |].
        -- rewrite <- app_assoc. destruct (q_src q) as [vs |];
             [apply run_vsrc_queue | apply run_imms_queue].
        -- destruct (r_vmap r) as [vm |].
           ++ destruct (vm_keyf vm) as [[f ts] |].
              ** (* transformed single-field key *)
                 cbn [app]. rewrite compile_load_correct. rewrite <- app_assoc.
                 edestruct (run_transforms_prefix ts (set_reg rf 1 (field_value f p))
                             ([IVmap [1] (vm_name vm) (vm_entries vm)]
                                ++ flat_map compile_stmt (r_after r)) p) as [rf' [Hr1 Hr2]].
                 rewrite Hr2. cbn [app run_rule concat map].
                 rewrite app_nil_r, Hr1, set_reg_same. reflexivity.
              ** (* concat key: IVmap reads the loaded concatenation, ignores the tail *)
                 rewrite <- app_assoc. rewrite run_load_fields. cbn [app run_rule].
                 rewrite map_write_fields by apply alloc_regs_nodup.
                 rewrite map_fst_field, alloc_regs_fst. reflexivity.
           ++ (* static verdict, then the post-outcome statements *)
              rewrite run_verdict_tail_after.
              destruct (r_verdict r); solve [ reflexivity | apply run_stmts_none ].
Qed.

(** Chain level: the compiled program reproduces the rule-list evaluation. *)
Lemma run_program_compile_chain : forall rs p,
  run_program (map compile_rule rs) p = eval_rules rs p.
Proof.
  induction rs as [| r rs IH]; intros p.
  - reflexivity.
  - cbn [map run_program eval_rules]. rewrite run_rule_compile_rule.
    destruct (rule_applies r p); cbn [terminal].
    + destruct (outcome r p) as [v |].
      * destruct (terminal v); [reflexivity | apply IH].
      * apply IH.
    + apply IH.
Qed.

(** ** Main theorem: semantic preservation. *)
Theorem compile_chain_correct : forall c p,
  run_chain (compile_chain c) (c_policy c) p = eval_chain c p.
Proof.
  intros c p. unfold run_chain, eval_chain, compile_chain.
  rewrite run_program_compile_chain. reflexivity.
Qed.
