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

(** The slot register of one concatenation element is strictly below every
    register allocated to the later elements, so it never collides with them. *)
Lemma reg_head_not_in : forall f fields slot,
  ~ In (reg_of_slot slot) (map snd (alloc_regs (slot + field_slots f) fields)).
Proof.
  intros f fields slot Hin. apply alloc_regs_lb in Hin.
  pose proof (field_slots_pos f).
  assert (slot < slot + field_slots f) as Hlt by lia.
  apply reg_of_slot_mono in Hlt. lia.
Qed.

(** A transform chain applied *in place at register [r]*: it leaves [r] holding
    the transformed value, every other register untouched, and runs transparently
    to the trailing program. *)
Lemma run_transforms_at_prefix : forall ts r rf rest p,
  exists rf',
    rf' r = apply_transforms ts (rf r)
    /\ (forall r0, r0 <> r -> rf' r0 = rf r0)
    /\ run_rule rf (compile_transforms_at r ts ++ rest) p = run_rule rf' rest p.
Proof.
  induction ts as [| t ts IH]; intros r rf rest p.
  - exists rf. cbn [compile_transforms_at map app]. repeat split; reflexivity.
  - edestruct (IH r (set_reg rf r (apply_transform t (rf r))) rest p) as [rf' [H1 [H2 H3]]].
    exists rf'. split; [| split].
    + rewrite H1, set_reg_same. reflexivity.
    + intros r0 Hne. rewrite (H2 r0 Hne). apply set_reg_other.
      intro Heq; apply Hne; symmetry; exact Heq.
    + cbn [compile_transforms_at map app]. destruct t;
        cbn [compile_transform_at run_rule]; exact H3.
Qed.

(** Loading a transformed concatenation key: the resulting register file reads
    each slot register as the corresponding transformed field value (distinct
    slots never clobber one another), is unchanged outside those slots, and runs
    transparently to the trailing program. *)
Lemma run_load_fields_t : forall elems slot rf tail p,
  exists rf',
    map rf' (map snd (alloc_regs slot (map fst elems)))
      = map (fun fe => apply_transforms (snd fe) (field_value (fst fe) p)) elems
    /\ (forall r0, ~ In r0 (map snd (alloc_regs slot (map fst elems))) -> rf' r0 = rf r0)
    /\ run_rule rf (load_fields_t slot elems ++ tail) p = run_rule rf' tail p.
Proof.
  induction elems as [| [f ts] rest IH]; intros slot rf tail p.
  - exists rf. cbn [load_fields_t map alloc_regs app]. repeat split; reflexivity.
  - cbn [load_fields_t map fst snd alloc_regs].
    edestruct (run_transforms_at_prefix ts (reg_of_slot slot)
                (set_reg rf (reg_of_slot slot) (field_value f p))
                (load_fields_t (slot + field_slots f) rest ++ tail) p) as [rf1 [Ht1 [Ht2 Ht3]]].
    edestruct (IH (slot + field_slots f) rf1 tail p) as [rf' [Hr1 [Hr2 Hr3]]].
    exists rf'. split; [| split].
    + (* readback of the slot register, then of the later elements *)
      cbn [map]. f_equal.
      * rewrite (Hr2 (reg_of_slot slot) (reg_head_not_in f (map fst rest) slot)).
        rewrite Ht1, set_reg_same. reflexivity.
      * exact Hr1.
    + (* frame: anything outside this key's registers is untouched *)
      intros r0 Hni. cbn [map] in Hni.
      assert (r0 <> reg_of_slot slot) as Hne by (intro; apply Hni; left; symmetry; assumption).
      rewrite (Hr2 r0 (fun H => Hni (or_intror H))).
      rewrite (Ht2 r0 Hne). apply set_reg_other.
      intro Heq; apply Hne; symmetry; exact Heq.
    + (* verdict-transparency *)
      rewrite <- app_assoc. cbn [app].
      rewrite compile_load_correct, Ht3, Hr3. reflexivity.
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
                  | fields neg nm | f ts op v0 | f ts neg nm
                  | f ts neg lo hi | spec | qspec | clspec
                  | celems neg nm];
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
                 (set_mem (concat (map (fun f => field_value f p) fields))
                           (e_set (pkt_env p) nm)));
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
                  (ILookup [1] nm neg :: (flat_map compile_match ms ++ tail)) p)
        as [rf' [H1 H2]].
      rewrite H2. cbn [run_rule concat map]. rewrite app_nil_r, H1, set_reg_same.
      cbn [forallb eval_matchcond].
      destruct (xorb neg (set_mem (apply_transforms ts (field_value f p))
                                   (e_set (pkt_env p) nm)));
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
    + (* MConcatSetT: transformed multi-register key, distinct registers per element *)
      rewrite <- !app_assoc. cbn [app].
      edestruct (run_load_fields_t celems 0 rf
                  (ILookup (map snd (alloc_regs 0 (map fst celems))) nm neg
                   :: (flat_map compile_match ms ++ tail)) p) as [rf' [Hrb [_ Hrun]]].
      rewrite Hrun. cbn [run_rule]. rewrite Hrb.
      cbn [forallb eval_matchcond].
      destruct (xorb neg (set_mem
                 (concat (map (fun fe => apply_transforms (snd fe) (field_value (fst fe) p)) celems))
                 (e_set (pkt_env p) nm)));
        cbn [andb]; [apply IH; exact Hc | reflexivity].
Qed.

(** Statements never produce a verdict; they leave the register file in *some*
    state (a value-source may load register 1 via a load + transform chain, which
    yields an existential register file) and fall through to the verdict tail.
    Because every verdict tail is register-independent, this existential is all
    the rule-correctness proof needs. *)
(** An OR-chain of value sources: each later source is loaded into reg 2,
    transformed in place, then [bitwise reg1 = reg1 | reg2] folds it into the
    accumulator.  Every instruction is verdict-neutral, so the trailing program
    is reached from some register file. *)
Lemma run_or_chain : forall srcs rf tail p,
  exists rf',
    run_rule rf
      (flat_map (fun e =>
         compile_load (field_load (fst e)) 2 :: compile_transforms_at 2 (snd e)
         ++ [IBitwiseOr 1 1 2]) srcs ++ tail) p
    = run_rule rf' tail p.
Proof.
  induction srcs as [| [f ts] srcs IH]; intros rf tail p.
  - exists rf. reflexivity.
  - cbn [flat_map fst snd]. rewrite <- !app_assoc. cbn [app].
    rewrite compile_load_correct. rewrite <- app_assoc.
    edestruct (run_transforms_at_prefix ts 2 (set_reg rf 2 (field_value f p)))
      as [rf1 [_ [_ Ht]]].
    rewrite Ht. cbn [app run_rule].
    edestruct (IH (set_reg rf1 1 (data_or (rf1 1) (rf1 2))) tail p) as [rf' Hr].
    rewrite Hr. exists rf'. reflexivity.
Qed.

Lemma run_vsrc_exists : forall vs rf rest p,
  exists rf', run_rule rf (compile_vsrc vs ++ rest) p = run_rule rf' rest p.
Proof.
  destruct vs as [v | f ts | fields vts name | hf hl hs hm ho
                 | osrcs ofinal | telems tname
                 | hmf hml hms hmm hmo hmname]; intros rf rest p.
  - exists (set_reg rf 1 v). reflexivity.
  - edestruct (run_transforms_prefix ts (set_reg rf 1 (field_value f p)) rest p)
      as [rf' [_ Hr]].
    exists rf'. cbn [compile_vsrc app]. rewrite compile_load_correct. exact Hr.
  - (* VMap: concat key loaded, optionally transformed, then ILookupVal writes
       dreg; all verdict-neutral, so the verdict tail is reached from some rf. *)
    cbn [compile_vsrc]. rewrite <- !app_assoc. rewrite run_load_fields.
    edestruct (run_transforms_prefix vts (write_fields rf (alloc_regs 0 fields) p)
                ([ILookupVal (map snd (alloc_regs 0 fields)) name 1] ++ rest) p)
      as [rf' [_ Hr]].
    rewrite Hr. cbn [app run_rule]. eexists; reflexivity.
  - (* VHash: load the concat source fields, then the verdict-neutral IJhash *)
    cbn [compile_vsrc]. rewrite <- app_assoc. rewrite run_load_fields.
    cbn [app run_rule]. eexists; reflexivity.
  - (* VOr: base into reg1, OR-chain folding more sources, then final transforms *)
    destruct osrcs as [| [f0 ts0] orest].
    + exists rf. cbn [compile_vsrc app]. reflexivity.
    + cbn [compile_vsrc fst snd]. rewrite <- !app_assoc. cbn [app].
      rewrite compile_load_correct.
      edestruct (run_transforms_at_prefix ts0 1 (set_reg rf 1 (field_value f0 p)))
        as [rf1 [_ [_ Ht0]]].
      rewrite Ht0.
      edestruct (run_or_chain orest rf1) as [rf2 Hc].
      rewrite Hc.
      edestruct (run_transforms_at_prefix ofinal 1 rf2 rest p) as [rf' [_ [_ Hf]]].
      rewrite Hf. exists rf'. reflexivity.
  - (* VMapT: transformed-concat key loaded, then verdict-neutral ILookupVal *)
    cbn [compile_vsrc]. rewrite <- app_assoc.
    edestruct (run_load_fields_t telems 0 rf
                ([ILookupVal (map snd (alloc_regs 0 (map fst telems))) tname 1]
                 ++ rest) p) as [rf' [_ [_ Hrun]]].
    rewrite Hrun. cbn [app run_rule]. eexists; reflexivity.
  - (* VHashMap: load source, jhash into reg 1, then verdict-neutral ILookupVal *)
    cbn [compile_vsrc]. rewrite <- !app_assoc. rewrite run_load_fields.
    cbn [app run_rule]. eexists; reflexivity.
Qed.

(** Operand *value*-correctness (Phase-B foundation): the compiled operand leaves
    exactly [eval_vsrc vs p] in register 1.  Proven here for the common immediate
    and field(+transform) sources — this is the value the verdict proof delegated
    to the corpus, and what a `meta/ct set vs` must write for mutation to be
    modelled faithfully. *)
Lemma run_vsrc_value_VImm : forall v rf rest p,
  exists rf', run_rule rf (compile_vsrc (VImm v) ++ rest) p = run_rule rf' rest p
              /\ rf' 1 = eval_vsrc (VImm v) p.
Proof.
  intros. cbn [compile_vsrc app run_rule]. exists (set_reg rf 1 v).
  split; [reflexivity | apply set_reg_same].
Qed.

Lemma run_vsrc_value_VField : forall f ts rf rest p,
  exists rf', run_rule rf (compile_vsrc (VField f ts) ++ rest) p = run_rule rf' rest p
              /\ rf' 1 = eval_vsrc (VField f ts) p.
Proof.
  intros. cbn [compile_vsrc app]. rewrite compile_load_correct.
  edestruct (run_transforms_prefix ts (set_reg rf 1 (field_value f p)) rest p) as [rf' [H1 H2]].
  exists rf'. split; [exact H2 |].
  cbn [eval_vsrc]. rewrite H1, set_reg_same. reflexivity.
Qed.

(** ** Phase B: mutation-correctness scaffolding.

    [run_rule_writes] is packet-neutral on any instruction list containing no
    [IMetaSet]/[ICtSet]: a rule that does not set meta/ct mutates nothing, so the
    mutation-aware run threads the packet unchanged.  Hence on the whole verified
    fragment without meta/ct set, [run_program_mut] coincides with [run_program]
    and the mutation semantics conservatively extends [compile_chain_correct]. *)
Definition writes_instr (i : instr) : bool :=
  match i with IMetaSet _ _ | ICtSet _ _ => true | _ => false end.
Definition no_writes (is : list instr) : bool :=
  forallb (fun i => negb (writes_instr i)) is.

Lemma run_rule_writes_neutral : forall is rf p,
  no_writes is = true -> run_rule_writes rf is p = p.
Proof.
  induction is as [| i is IH]; intros rf p Hno; [reflexivity|].
  cbn [no_writes forallb] in Hno. apply Bool.andb_true_iff in Hno. destruct Hno as [Hi Hno].
  destruct i; cbn [run_rule_writes] in *;
    try (apply IH; exact Hno);
    try reflexivity;
    try (cbn [writes_instr negb] in Hi; discriminate Hi).
  all: try (destruct (eval_cmp _ _ _); [apply IH; exact Hno | reflexivity]).
  all: try (destruct (eval_range _ _ _ _); [apply IH; exact Hno | reflexivity]).
  all: try (destruct (xorb _ _); [apply IH; exact Hno | reflexivity]).
  all: try (destruct (pkt_limit _ _); [apply IH; exact Hno | reflexivity]).
  all: try (destruct (pkt_quota _ _); [apply IH; exact Hno | reflexivity]).
  all: try (destruct (pkt_connlimit _ _); [apply IH; exact Hno | reflexivity]).
  all: try (destruct (assoc_verdict _ _); [reflexivity | apply IH; exact Hno]).
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

(** ---- run_rule_writes twins of the load/transform/operand helpers ---- *)
(** These mirror [compile_load_correct] / [run_load_fields] / [run_compile_transform]
    / [run_transforms_prefix] exactly: register threading is identical in
    [run_rule_writes], only the return type differs. *)
Lemma compile_load_writes : forall f dst rf rest p,
  run_rule_writes rf (compile_load (field_load f) dst :: rest) p =
  run_rule_writes (set_reg rf dst (field_value f p)) rest p.
Proof.
  intros f dst rf rest p. unfold field_value, do_load, compile_load.
  destruct (field_load f) eqn:E; simpl; reflexivity.
Qed.

Lemma run_load_fields_writes : forall pairs rf tail p,
  run_rule_writes rf (load_fields pairs ++ tail) p = run_rule_writes (write_fields rf pairs p) tail p.
Proof.
  induction pairs as [| [f r] rest IH]; intros rf tail p.
  - reflexivity.
  - cbn [load_fields map fst snd app write_fields]. rewrite compile_load_writes. apply IH.
Qed.

Lemma run_compile_transform_writes : forall t rf rest p,
  run_rule_writes rf (compile_transform t :: rest) p
  = run_rule_writes (set_reg rf 1 (apply_transform t (rf 1))) rest p.
Proof. intros t rf rest p. destruct t; reflexivity. Qed.

Lemma run_transforms_prefix_writes : forall ts rf rest p,
  exists rf', rf' 1 = apply_transforms ts (rf 1)
    /\ (forall r, r <> 1 -> rf' r = rf r)
    /\ run_rule_writes rf (compile_transforms ts ++ rest) p = run_rule_writes rf' rest p.
Proof.
  induction ts as [| t ts IH]; intros rf rest p.
  - exists rf. repeat split; reflexivity.
  - cbn [compile_transforms app]. rewrite run_compile_transform_writes.
    edestruct (IH (set_reg rf 1 (apply_transform t (rf 1)))) as [rf' [H1 [Hfr H2]]].
    exists rf'. rewrite set_reg_same in H1. split; [exact H1 | split; [| exact H2]].
    intros r Hr. rewrite (Hfr r Hr). apply set_reg_other.
    intro Heq; apply Hr; symmetry; exact Heq.
Qed.

Lemma run_transforms_at_prefix_writes : forall ts r rf rest p,
  exists rf', rf' r = apply_transforms ts (rf r)
    /\ (forall r0, r0 <> r -> rf' r0 = rf r0)
    /\ run_rule_writes rf (compile_transforms_at r ts ++ rest) p = run_rule_writes rf' rest p.
Proof.
  induction ts as [| t ts IH]; intros r rf rest p.
  - exists rf. cbn [compile_transforms_at map app]. repeat split; reflexivity.
  - edestruct (IH r (set_reg rf r (apply_transform t (rf r))) rest p) as [rf' [H1 [H2 H3]]].
    exists rf'. split; [| split].
    + rewrite H1, set_reg_same. reflexivity.
    + intros r0 Hne. rewrite (H2 r0 Hne). apply set_reg_other.
      intro Heq; apply Hne; symmetry; exact Heq.
    + cbn [compile_transforms_at map app]. destruct t;
        cbn [compile_transform_at run_rule_writes]; exact H3.
Qed.

Lemma run_load_fields_t_writes : forall elems slot rf tail p,
  exists rf',
    map rf' (map snd (alloc_regs slot (map fst elems)))
      = map (fun fe => apply_transforms (snd fe) (field_value (fst fe) p)) elems
    /\ (forall r0, ~ In r0 (map snd (alloc_regs slot (map fst elems))) -> rf' r0 = rf r0)
    /\ run_rule_writes rf (load_fields_t slot elems ++ tail) p = run_rule_writes rf' tail p.
Proof.
  induction elems as [| [f ts] rest IH]; intros slot rf tail p.
  - exists rf. cbn [load_fields_t map alloc_regs app]. repeat split; reflexivity.
  - cbn [load_fields_t map fst snd alloc_regs].
    edestruct (run_transforms_at_prefix_writes ts (reg_of_slot slot)
                (set_reg rf (reg_of_slot slot) (field_value f p))
                (load_fields_t (slot + field_slots f) rest ++ tail) p) as [rf1 [Ht1 [Ht2 Ht3]]].
    edestruct (IH (slot + field_slots f) rf1 tail p) as [rf' [Hr1 [Hr2 Hr3]]].
    exists rf'. split; [| split].
    + cbn [map]. f_equal.
      * rewrite (Hr2 (reg_of_slot slot) (reg_head_not_in f (map fst rest) slot)).
        rewrite Ht1, set_reg_same. reflexivity.
      * exact Hr1.
    + intros r0 Hni. cbn [map] in Hni.
      assert (r0 <> reg_of_slot slot) as Hne by (intro; apply Hni; left; symmetry; assumption).
      rewrite (Hr2 r0 (fun H => Hni (or_intror H))).
      rewrite (Ht2 r0 Hne). apply set_reg_other.
      intro Heq; apply Hne; symmetry; exact Heq.
    + rewrite <- app_assoc. cbn [app].
      rewrite compile_load_writes, Ht3, Hr3. reflexivity.
Qed.

(** Writes-version of the OR-chain, additionally tracking register 1's folded
    value: each source is loaded into reg 2 (transformed there), then OR'd into
    the accumulator reg 1. *)
Lemma run_or_chain_writes : forall srcs rf tail p,
  exists rf',
    run_rule_writes rf
      (flat_map (fun e =>
         compile_load (field_load (fst e)) 2 :: compile_transforms_at 2 (snd e)
         ++ [IBitwiseOr 1 1 2]) srcs ++ tail) p
    = run_rule_writes rf' tail p
    /\ rf' 1 = fold_left
                 (fun acc e => data_or acc (apply_transforms (snd e) (field_value (fst e) p)))
                 srcs (rf 1).
Proof.
  induction srcs as [| [f ts] srcs IH]; intros rf tail p.
  - exists rf. split; reflexivity.
  - cbn [flat_map fst snd]. rewrite <- !app_assoc. cbn [app].
    rewrite compile_load_writes. rewrite <- !app_assoc.
    edestruct (run_transforms_at_prefix_writes ts 2 (set_reg rf 2 (field_value f p))
                ([IBitwiseOr 1 1 2] ++ flat_map (fun e =>
                   compile_load (field_load (fst e)) 2 :: compile_transforms_at 2 (snd e)
                   ++ [IBitwiseOr 1 1 2]) srcs ++ tail) p) as [rf1 [Ht1 [Ht2 Ht3]]].
    rewrite Ht3. cbn [app run_rule_writes].
    edestruct (IH (set_reg rf1 1 (data_or (rf1 1) (rf1 2))) tail p) as [rf' [Hr Hv]].
    rewrite Hr. exists rf'. split; [reflexivity |].
    rewrite Hv, set_reg_same. cbn [fold_left]. f_equal.
    rewrite Ht1, set_reg_same. rewrite (Ht2 1) by (intro; discriminate).
    rewrite set_reg_other by (intro; discriminate). reflexivity.
Qed.

(** The head register of a field allocation holds the first field's value (the
    later fields occupy strictly higher registers, so they never clobber it). *)
Lemma write_fields_head : forall f frest slot rf p,
  write_fields rf (alloc_regs slot (f :: frest)) p (reg_of_slot slot) = field_value f p.
Proof.
  intros f frest slot rf p. cbn [alloc_regs write_fields].
  rewrite write_fields_other.
  - apply set_reg_same.
  - intro Hin. apply alloc_regs_lb in Hin. pose proof (field_slots_pos f).
    assert (slot < slot + field_slots f) as Hlt by lia. apply reg_of_slot_mono in Hlt. lia.
Qed.

(** A simple operand leaves exactly [eval_vsrc vs p] in register 1 under
    [run_rule_writes] (the operand is packet-neutral; it only loads/transforms/
    looks-up/hashes registers).  Covers immediate, field, nonempty-key value map,
    transformed-concat value map, and jhash(-then-map) operands. *)
Lemma writes_vsrc_simple : forall vs rf rest p,
  simple_vsrc vs = true ->
  exists rf', run_rule_writes rf (compile_vsrc vs ++ rest) p = run_rule_writes rf' rest p
              /\ rf' 1 = eval_vsrc vs p.
Proof.
  intros vs rf rest p Hs.
  destruct vs as [v | f ts | fields ts nm | hfields hlen hseed hmod hoff
                 | osrcs ofinal | elems nm | mfields mlen mseed mmod moff mnm];
    cbn [simple_vsrc] in Hs; try discriminate.
  - (* VImm *) exists (set_reg rf 1 v). cbn [compile_vsrc app run_rule_writes].
    split; [reflexivity | apply set_reg_same].
  - (* VField *) cbn [compile_vsrc app]. rewrite compile_load_writes.
    edestruct (run_transforms_prefix_writes ts (set_reg rf 1 (field_value f p)) rest p)
      as [rf' [H1 [_ H2]]].
    exists rf'. split; [exact H2 |]. cbn [eval_vsrc]. rewrite H1, set_reg_same. reflexivity.
  - (* VMap (f0 :: fr) [] nm : load key fields (no key transform), lookup *)
    destruct fields as [| f0 fr]; [discriminate Hs |].
    destruct ts as [| t ts]; [| discriminate Hs].
    cbn [compile_vsrc compile_transforms]. rewrite <- !app_assoc. cbn [app].
    rewrite run_load_fields_writes. cbn [run_rule_writes].
    eexists. split; [reflexivity |]. rewrite set_reg_same.
    cbn [eval_vsrc apply_transforms].
    rewrite map_write_fields by apply alloc_regs_nodup.
    rewrite map_fst_field, alloc_regs_fst. reflexivity.
  - (* VHash (hf0 :: hfr) ... : jhash of the first loaded field *)
    destruct hfields as [| hf0 hfr]; [discriminate Hs |].
    cbn [compile_vsrc]. rewrite <- app_assoc. rewrite run_load_fields_writes.
    replace (match map snd (alloc_regs 4 (hf0 :: hfr)) with r :: _ => r | [] => 1 end)
      with (reg_of_slot 4) by reflexivity.
    cbn [app run_rule_writes].
    eexists. split; [reflexivity |]. rewrite set_reg_same, write_fields_head.
    cbn [eval_vsrc]. reflexivity.
  - (* VOr ((f0,ts0) :: orest) ofinal : base into reg 1, OR-fold, final transforms *)
    destruct osrcs as [| [f0 ts0] orest]; [discriminate Hs |].
    cbn [compile_vsrc fst snd]. rewrite <- !app_assoc. cbn [app].
    rewrite compile_load_writes.
    edestruct (run_transforms_at_prefix_writes ts0 1 (set_reg rf 1 (field_value f0 p))
                (flat_map (fun e => compile_load (field_load (fst e)) 2
                                    :: compile_transforms_at 2 (snd e) ++ [IBitwiseOr 1 1 2]) orest
                 ++ compile_transforms_at 1 ofinal ++ rest) p) as [rf1 [Hv1 [_ Hr1]]].
    rewrite Hr1.
    edestruct (run_or_chain_writes orest rf1 (compile_transforms_at 1 ofinal ++ rest) p)
      as [rf2 [Hr2 Hv2]].
    rewrite Hr2.
    edestruct (run_transforms_at_prefix_writes ofinal 1 rf2 rest p) as [rf3 [Hv3 [_ Hr3]]].
    rewrite Hr3. exists rf3. split; [reflexivity |].
    cbn [eval_vsrc fst snd]. rewrite Hv3, Hv2, Hv1, set_reg_same. reflexivity.
  - (* VMapT elems nm : transformed-concat key, then lookup *)
    cbn [compile_vsrc]. rewrite <- app_assoc.
    edestruct (run_load_fields_t_writes elems 0 rf
                ([ILookupVal (map snd (alloc_regs 0 (map fst elems))) nm 1] ++ rest) p)
      as [rf' [Hrb [_ Hr]]].
    rewrite Hr. cbn [app run_rule_writes].
    eexists. split; [reflexivity |]. rewrite set_reg_same, Hrb. reflexivity.
  - (* VHashMap (mf0 :: mfr) ... : jhash then value-map lookup *)
    destruct mfields as [| mf0 mfr]; [discriminate Hs |].
    cbn [compile_vsrc]. rewrite <- !app_assoc. rewrite run_load_fields_writes.
    replace (match map snd (alloc_regs 4 (mf0 :: mfr)) with r :: _ => r | [] => 1 end)
      with (reg_of_slot 4) by reflexivity.
    cbn [app run_rule_writes map concat].
    eexists. split; [reflexivity |]. rewrite !set_reg_same, app_nil_r, write_fields_head.
    cbn [eval_vsrc]. reflexivity.
Qed.

(** Single-match gating under [run_rule_writes]: a match passes (continue to the
    [run_rule_writes]-constant tail result [R]) or breaks (return the packet
    unchanged), exactly tracking [eval_matchcond].  Mirrors the per-match cases of
    [run_compile_matches_const], with the break returning [p] instead of [None]. *)
Lemma writes_match_one : forall m X p R,
  (forall rf, run_rule_writes rf X p = R) ->
  forall rf, run_rule_writes rf (compile_match m ++ X) p = if eval_matchcond m p then R else p.
Proof.
  intros m X p R Hc rf.
  destruct m as [f v0 | f v0 | f neg lo hi | f neg mask xor v0 | f op v0
                | fields neg nm | f ts op v0 | f ts neg nm
                | f ts neg lo hi | spec | qspec | clspec
                | celems neg nm]; cbn [compile_match app].
  - (* MEq *) rewrite compile_load_writes. cbn [run_rule_writes]. rewrite set_reg_same.
    cbn [eval_matchcond]. unfold eval_cmp.
    destruct (data_eqb (field_value f p) v0); [apply Hc | reflexivity].
  - (* MNeq *) rewrite compile_load_writes. cbn [run_rule_writes]. rewrite set_reg_same.
    cbn [eval_matchcond]. unfold eval_cmp.
    destruct (data_eqb (field_value f p) v0); cbn [negb]; [reflexivity | apply Hc].
  - (* MRange *) rewrite compile_load_writes. cbn [run_rule_writes]. rewrite set_reg_same.
    cbn [eval_matchcond].
    destruct (eval_range (if neg then CNe else CEq) (field_value f p) lo hi);
      [apply Hc | reflexivity].
  - (* MMasked *) rewrite compile_load_writes. cbn [run_rule_writes]. rewrite !set_reg_same.
    cbn [eval_matchcond].
    destruct (eval_cmp (if neg then CNe else CEq) (data_bitops (field_value f p) mask xor) v0);
      [apply Hc | reflexivity].
  - (* MCmp *) rewrite compile_load_writes. cbn [run_rule_writes]. rewrite set_reg_same.
    cbn [eval_matchcond].
    destruct (eval_cmp op (field_value f p) v0); [apply Hc | reflexivity].
  - (* MConcatSet *) rewrite <- !app_assoc. cbn [app].
    rewrite run_load_fields_writes. cbn [run_rule_writes].
    rewrite map_write_fields by apply alloc_regs_nodup.
    rewrite map_fst_field, alloc_regs_fst. cbn [eval_matchcond].
    destruct (xorb neg (set_mem (concat (map (fun f => field_value f p) fields))
                                 (e_set (pkt_env p) nm)));
      [apply Hc | reflexivity].
  - (* MTransform *) rewrite compile_load_writes. rewrite <- !app_assoc. cbn [app].
    edestruct (run_transforms_prefix_writes ts (set_reg rf 1 (field_value f p))
                (ICmp op 1 v0 :: X) p) as [rf' [H1 [_ H2]]].
    rewrite H2. cbn [run_rule_writes]. rewrite H1, set_reg_same. cbn [eval_matchcond].
    destruct (eval_cmp op (apply_transforms ts (field_value f p)) v0); [apply Hc | reflexivity].
  - (* MSetT *) rewrite compile_load_writes. rewrite <- !app_assoc. cbn [app].
    edestruct (run_transforms_prefix_writes ts (set_reg rf 1 (field_value f p))
                (ILookup [1] nm neg :: X) p) as [rf' [H1 [_ H2]]].
    rewrite H2. cbn [run_rule_writes concat map]. rewrite app_nil_r, H1, set_reg_same.
    cbn [eval_matchcond].
    destruct (xorb neg (set_mem (apply_transforms ts (field_value f p)) (e_set (pkt_env p) nm)));
      [apply Hc | reflexivity].
  - (* MRangeT *) rewrite compile_load_writes. rewrite <- !app_assoc. cbn [app].
    edestruct (run_transforms_prefix_writes ts (set_reg rf 1 (field_value f p))
                (IRange (if neg then CNe else CEq) 1 lo hi :: X) p) as [rf' [H1 [_ H2]]].
    rewrite H2. cbn [run_rule_writes]. rewrite H1, set_reg_same. cbn [eval_matchcond].
    destruct (eval_range (if neg then CNe else CEq) (apply_transforms ts (field_value f p)) lo hi);
      [apply Hc | reflexivity].
  - (* MLimit *) cbn [run_rule_writes eval_matchcond].
    destruct (pkt_limit p spec); [apply Hc | reflexivity].
  - (* MQuota *) cbn [run_rule_writes eval_matchcond].
    destruct (pkt_quota p qspec); [apply Hc | reflexivity].
  - (* MConnlimit *) cbn [run_rule_writes eval_matchcond].
    destruct (pkt_connlimit p clspec); [apply Hc | reflexivity].
  - (* MConcatSetT *) rewrite <- !app_assoc. cbn [app].
    edestruct (run_load_fields_t_writes celems 0 rf
                (ILookup (map snd (alloc_regs 0 (map fst celems))) nm neg :: X) p)
      as [rf' [Hrb [_ Hrun]]].
    rewrite Hrun. cbn [run_rule_writes]. rewrite Hrb. cbn [eval_matchcond].
    destruct (xorb neg (set_mem
               (concat (map (fun fe => apply_transforms (snd fe) (field_value (fst fe) p)) celems))
               (e_set (pkt_env p) nm)));
      [apply Hc | reflexivity].
Qed.

(** ---- the compiler emits IMetaSet/ICtSet only for SMetaSet/SCtSet body
    statements; every other compiled fragment is [no_writes] ---- *)
Lemma nw_cons : forall i l, no_writes (i :: l) = negb (writes_instr i) && no_writes l.
Proof. reflexivity. Qed.
Lemma nw_app : forall a b, no_writes (a ++ b) = no_writes a && no_writes b.
Proof. intros a b. apply forallb_app. Qed.
Lemma nw_map : forall {A} (g : A -> instr) (l : list A),
  (forall x, writes_instr (g x) = false) -> no_writes (map g l) = true.
Proof.
  intros A g l Hg. induction l as [| x xs IH]; [reflexivity|].
  cbn [map]. rewrite nw_cons, Hg, IH. reflexivity.
Qed.
Lemma nw_load_fields : forall pairs, no_writes (load_fields pairs) = true.
Proof.
  intros. unfold load_fields. apply nw_map. intros [f r]. cbn [fst snd].
  unfold compile_load. destruct (field_load f); reflexivity.
Qed.
Lemma nw_imms : forall (imms : list (reg * data)),
  no_writes (map (fun rv => IImmediateData (fst rv) (snd rv)) imms) = true.
Proof. intros. apply nw_map. reflexivity. Qed.
Lemma nw_flat_map : forall {A} (g : A -> list instr) (l : list A),
  (forall x, no_writes (g x) = true) -> no_writes (flat_map g l) = true.
Proof.
  intros A g l Hg. induction l as [| x xs IH]; [reflexivity|].
  cbn [flat_map]. rewrite nw_app, Hg, IH. reflexivity.
Qed.
Lemma nw_transforms : forall ts, no_writes (compile_transforms ts) = true.
Proof.
  induction ts as [| t ts IH]; [reflexivity|].
  cbn [compile_transforms]. rewrite nw_cons, IH, Bool.andb_true_r. destruct t; reflexivity.
Qed.
Lemma nw_transforms_at : forall r ts, no_writes (compile_transforms_at r ts) = true.
Proof.
  intros r ts. unfold compile_transforms_at. apply nw_map. intros t. destruct t; reflexivity.
Qed.
Lemma nw_load_fields_t : forall elems slot, no_writes (load_fields_t slot elems) = true.
Proof.
  induction elems as [| [f ts] rest IH]; intros slot; [reflexivity|].
  cbn [load_fields_t]. rewrite nw_app, nw_cons, nw_transforms_at, IH.
  unfold compile_load; destruct (field_load f); reflexivity.
Qed.
Lemma nw_vsrc : forall vs, no_writes (compile_vsrc vs) = true.
Proof.
  destruct vs as [v | f ts | fields ts nm | fields len seed modulus offset
                 | osrcs ofinal | elems nm | fields len seed modulus offset nm];
    cbn [compile_vsrc].
  - reflexivity.
  - rewrite nw_cons, nw_transforms. unfold compile_load; destruct (field_load f); reflexivity.
  - rewrite nw_app, nw_load_fields, nw_app, nw_transforms. reflexivity.
  - rewrite nw_app, nw_load_fields. reflexivity.
  - destruct osrcs as [| [f0 ts0] rest]; [reflexivity|].
    rewrite !nw_app, nw_cons.
    rewrite (nw_flat_map _ rest).
    2: { intros [f ts0']. cbn [fst snd]. rewrite nw_cons, nw_app, nw_transforms_at.
         unfold compile_load; destruct (field_load f); reflexivity. }
    rewrite !nw_transforms_at.
    unfold compile_load; destruct (field_load f0); reflexivity.
  - rewrite nw_app, nw_load_fields_t. reflexivity.
  - rewrite nw_app, nw_load_fields, nw_app. reflexivity.
Qed.
Lemma nw_verdict_tail : forall v, no_writes (verdict_tail v) = true.
Proof. destruct v; reflexivity. Qed.
Lemma nw_compile_vmap : forall r, no_writes (compile_vmap r) = true.
Proof.
  intros r. unfold compile_vmap. destruct (r_vmap r) as [vm |]; [|reflexivity].
  destruct (vm_keyf vm) as [[f ts] |].
  - rewrite nw_cons, nw_app, nw_transforms. unfold compile_load; destruct (field_load f); reflexivity.
  - rewrite nw_app, nw_load_fields. reflexivity.
Qed.
Lemma nw_compile_terminal : forall r, no_writes (compile_terminal r) = true.
Proof.
  intros r. unfold compile_terminal.
  destruct (r_nat r) as [n |].
  { rewrite nw_app. destruct (nat_src n) as [vs |]; [rewrite nw_vsrc; reflexivity|].
    destruct (nat_map n) as [[[fields ts] name] |].
    - rewrite nw_app, nw_load_fields, nw_app, nw_transforms. reflexivity.
    - destruct (nat_field n) as [[f ts] |].
      + rewrite nw_cons, nw_transforms. unfold compile_load; destruct (field_load f); reflexivity.
      + rewrite nw_imms. reflexivity. }
  destruct (r_tproxy r) as [t |].
  { rewrite nw_app. destruct (tp_portmap t) as [[[m o] name] |].
    - rewrite nw_app, nw_imms. reflexivity.
    - rewrite nw_imms. reflexivity. }
  destruct (r_fwd r) as [w |].
  { rewrite nw_app. destruct (fwd_src w) as [vs |]; [rewrite nw_vsrc | rewrite nw_imms]; reflexivity. }
  destruct (r_queue r) as [q |].
  { rewrite nw_app. destruct (q_src q) as [vs |]; [rewrite nw_vsrc | rewrite nw_imms]; reflexivity. }
  apply nw_verdict_tail.
Qed.
Lemma nw_compile_end : forall r, no_writes (compile_end r) = true.
Proof.
  intros r. unfold compile_end. rewrite nw_app, nw_compile_vmap, nw_compile_terminal. reflexivity.
Qed.

(** The body, compiled and run under [run_rule_writes] before a packet-neutral
    tail, realises exactly [body_writes] — the declarative meta/ct effect. *)
Lemma run_compile_body_writes : forall body tail,
  (forall rf p, run_rule_writes rf tail p = p) ->
  simple_body body = true ->
  forall rf p, run_rule_writes rf (flat_map compile_body_item body ++ tail) p = body_writes body p.
Proof.
  induction body as [| it body IH]; intros tail Htail Hsb rf p.
  - cbn [flat_map app body_writes]. apply Htail.
  - cbn [simple_body forallb] in Hsb. apply Bool.andb_true_iff in Hsb. destruct Hsb as [Hit Hsb'].
    destruct it as [m | s]; cbn [flat_map compile_body_item].
    + (* BMatch *) rewrite <- app_assoc.
      rewrite (writes_match_one m (flat_map compile_body_item body ++ tail) p
                 (body_writes body p) (fun rf0 => IH tail Htail Hsb' rf0 p)).
      reflexivity.
    + (* BStmt: only SMetaSet/SCtSet survive [simple_body] *)
      destruct s; cbn in Hit; try discriminate Hit;
      cbn [compile_stmt]; rewrite <- !app_assoc.
      * (* SMetaSet k vs *)
        edestruct (writes_vsrc_simple vs rf
                    ([IMetaSet k 1] ++ (flat_map compile_body_item body ++ tail)) p Hit)
          as [rf' [Hr Hv]].
        rewrite Hr. cbn [app run_rule_writes]. rewrite Hv.
        cbn [body_writes]. apply IH; [exact Htail | exact Hsb'].
      * (* SCtSet k vs *)
        edestruct (writes_vsrc_simple vs rf
                    ([ICtSet k 1] ++ (flat_map compile_body_item body ++ tail)) p Hit)
          as [rf' [Hr Hv]].
        rewrite Hr. cbn [app run_rule_writes]. rewrite Hv.
        cbn [body_writes]. apply IH; [exact Htail | exact Hsb'].
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
  - (* SDynsetImm: load the key, then immediate data, then verdict-neutral IDynset *)
    cbn [compile_stmt]. rewrite <- app_assoc. rewrite run_load_fields.
    rewrite <- app_assoc.
    edestruct run_imms_through as [rf' Hr]. rewrite Hr.
    cbn [run_rule]. eexists; reflexivity.
  - (* SExthdrWrite: value source, then the verdict-neutral IExthdrWrite *)
    edestruct (run_vsrc_exists vs rf (IExthdrWrite proto htype off len 1 :: rest) p) as [rf' Hr].
    exists rf'. cbn [compile_stmt]. rewrite <- app_assoc. cbn [app].
    rewrite Hr. reflexivity.
  - (* SDupSrc: value source, then operand immediates, then verdict-neutral IDup *)
    cbn [compile_stmt]. rewrite <- app_assoc.
    edestruct run_vsrc_exists as [rf1 Hr1]. rewrite Hr1.
    rewrite <- app_assoc.
    edestruct run_imms_through as [rf2 Hr2]. rewrite Hr2.
    cbn [run_rule]. eexists; reflexivity.
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

(** A value-sourced NAT operand: the value source is verdict-neutral, then the
    terminal [INat] accepts. *)
Lemma run_vsrc_nat : forall vs tail rf k fam amin amax pmin pmax fl p,
  run_rule rf (compile_vsrc vs ++ INat k fam amin amax pmin pmax fl :: tail) p = Some Accept.
Proof.
  intros. edestruct (run_vsrc_exists vs rf
                      (INat k fam amin amax pmin pmax fl :: tail) p) as [rf' Hr].
  rewrite Hr. cbn [run_rule]. reflexivity.
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

(** A symhash-keyed-map tproxy port: the operand immediates, then the
    verdict-neutral symhash + map lookup, then the terminal [ITproxy] accepts. *)
Lemma run_portmap_tproxy : forall imms m o name fam areg preg tail rf p,
  run_rule rf ((map (fun rv => IImmediateData (fst rv) (snd rv)) imms
                ++ [ISymhash m o 2; ILookupVal [2] name 2])
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

(** A value-sourced fwd device: the value source is verdict-neutral, then the
    terminal [IFwd] accepts. *)
Lemma run_vsrc_fwd : forall vs tail rf dev addr nfp p,
  run_rule rf (compile_vsrc vs ++ IFwd dev addr nfp :: tail) p = Some Accept.
Proof.
  intros. edestruct (run_vsrc_exists vs rf (IFwd dev addr nfp :: tail) p) as [rf' Hr].
  rewrite Hr. cbn [run_rule]. reflexivity.
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
        ++ [ILookupVal (map snd (alloc_regs 0 fields)) name 1])
     ++ INat k fam amin amax pmin pmax fl :: tail) p = Some Accept.
Proof.
  intros. rewrite <- !app_assoc. rewrite run_load_fields.
  edestruct (run_transforms_prefix ts (write_fields rf (alloc_regs 0 fields) p)
              ([ILookupVal (map snd (alloc_regs 0 fields)) name 1]
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

(** The terminal of a rule (nat/tproxy/fwd/queue/verdict) runs, from any register
    file, to its [terminal_outcome] — ignoring the post-outcome statements after a
    side-effect terminal, running them to [None] after a [Continue]. *)
Lemma run_terminal : forall r rf p,
  run_rule rf (compile_terminal r ++ flat_map compile_stmt (r_after r)) p
  = terminal_outcome r p.
Proof.
  intros r rf p. unfold compile_terminal, terminal_outcome. destruct (r_nat r) as [n |].
  - rewrite <- app_assoc. destruct (nat_src n) as [vs |].
    + apply run_vsrc_nat.
    + destruct (nat_map n) as [[[fields ts] name] |].
      * apply run_map_nat.
      * destruct (nat_field n) as [[f ts] |]; [apply run_field_nat | apply run_imms_nat].
  - destruct (r_tproxy r) as [t |].
    + rewrite <- app_assoc. destruct (tp_portmap t) as [[[m o] name] |];
        [apply run_portmap_tproxy | apply run_imms_tproxy].
    + destruct (r_fwd r) as [w |].
      * rewrite <- app_assoc. destruct (fwd_src w) as [vs |];
          [apply run_vsrc_fwd | apply run_imms_fwd].
      * destruct (r_queue r) as [q |].
        -- rewrite <- app_assoc. destruct (q_src q) as [vs |];
             [apply run_vsrc_queue | apply run_imms_queue].
        -- rewrite run_verdict_tail_after.
           destruct (r_verdict r); solve [ reflexivity | apply run_stmts_none ].
Qed.

Lemma run_rule_compile_rule : forall r p,
  run_rule empty_rf (compile_rule r) p =
  if rule_applies r p then outcome r p else None.
Proof.
  intros r p. unfold compile_rule, rule_applies.
  apply run_compile_body.
  (* the trailing tail is the vmap prefix, then the terminal, then the
     post-outcome statements; a vmap hit wins, a miss falls to the terminal *)
  intro rf. unfold compile_end, compile_vmap, outcome. destruct (r_vmap r) as [vm |].
  - (* verdict map first: load the key, IVmap hits -> verdict, misses -> terminal *)
    rewrite <- app_assoc. destruct (vm_keyf vm) as [[f ts] |].
    + (* transformed single-field key *)
      cbn [app]. rewrite compile_load_correct. rewrite <- app_assoc.
      edestruct (run_transforms_prefix ts (set_reg rf 1 (field_value f p))
                  ([IVmap [1] (vm_name vm)]
                     ++ compile_terminal r ++ flat_map compile_stmt (r_after r)) p)
        as [rf' [Hr1 Hr2]].
      rewrite Hr2. cbn [app run_rule concat map].
      rewrite app_nil_r, Hr1, set_reg_same.
      destruct (assoc_verdict (apply_transforms ts (field_value f p))
                              (e_vmap (pkt_env p) (vm_name vm)));
        [reflexivity | apply run_terminal].
    + (* concat key: IVmap reads the loaded concatenation *)
      rewrite <- app_assoc. rewrite run_load_fields. cbn [app run_rule].
      rewrite map_write_fields by apply alloc_regs_nodup.
      rewrite map_fst_field, alloc_regs_fst.
      destruct (assoc_verdict (concat (map (fun f => field_value f p) (vm_fields vm)))
                              (e_vmap (pkt_env p) (vm_name vm)));
        [reflexivity | apply run_terminal].
  - (* no verdict map: just the terminal *)
    cbn [app]. apply run_terminal.
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

(** ** Phase B main theorem: the compiler preserves in-traversal mutation.

    For a plain rule whose set statements use simple (immediate/field) operands,
    the compiled bytecode's meta/ct effect equals the declarative one — so a
    `meta/ct set` is faithfully visible to later rules on BOTH sides, and the
    mutation-aware semantics agree end to end. *)
Lemma run_rule_writes_compile_rule : forall r p,
  simple_writes r = true -> r_after r = [] ->
  run_rule_writes empty_rf (compile_rule r) p = dsl_writes r p.
Proof.
  intros r p Hs Ha. unfold compile_rule. rewrite Ha. cbn [flat_map].
  rewrite app_nil_r. unfold dsl_writes.
  apply run_compile_body_writes; [| exact Hs].
  intros rf p'. apply run_rule_writes_neutral, nw_compile_end.
Qed.

(** A ruleset is "plain & simple" when every rule has simple set-operands and no
    post-outcome statements — the fragment on which mutation is modelled. *)
Definition plain_simple (r : rule) : bool :=
  simple_writes r && match r_after r with [] => true | _ :: _ => false end.

Lemma run_program_mut_compile_chain : forall rs p,
  forallb plain_simple rs = true ->
  run_program_mut (map compile_rule rs) p = eval_rules_mut rs p.
Proof.
  induction rs as [| r rs IH]; intros p Hall; [reflexivity|].
  cbn [forallb] in Hall. apply Bool.andb_true_iff in Hall. destruct Hall as [Hr Hrs].
  unfold plain_simple in Hr. apply Bool.andb_true_iff in Hr. destruct Hr as [Hs Ha].
  assert (Hae : r_after r = []) by (destruct (r_after r); [reflexivity | discriminate Ha]).
  cbn [map run_program_mut eval_rules_mut].
  rewrite run_rule_compile_rule. rewrite (run_rule_writes_compile_rule r p Hs Hae).
  destruct (rule_applies r p).
  - destruct (outcome r p) as [v |].
    + destruct (terminal v); [reflexivity | apply IH; exact Hrs].
    + apply IH; exact Hrs.
  - apply IH; exact Hrs.
Qed.

Theorem compile_chain_mut_correct : forall c p,
  forallb plain_simple (c_rules c) = true ->
  run_chain_mut (compile_chain c) (c_policy c) p = eval_chain_mut c p.
Proof.
  intros c p Hall. unfold run_chain_mut, eval_chain_mut, compile_chain.
  rewrite run_program_mut_compile_chain by exact Hall. reflexivity.
Qed.

(** ** Multi-chain semantic preservation (jump / goto / return + user chains).

    The compiled jump-aware VM agrees with the DSL interpreter for *every* fuel
    and *every* chain environment — so the compiler preserves the packet verdict
    of a whole ruleset, not just one base chain. *)

Lemma prog_lookup_compile_env : forall cs n,
  prog_lookup (compile_env cs) n = option_map compile_chain (chain_lookup cs n).
Proof.
  induction cs as [| [m ch] cs IH]; intros n;
    cbn [compile_env map prog_lookup chain_lookup fst snd]; [reflexivity |].
  destruct (String.eqb n m); [reflexivity | apply IH].
Qed.

Lemma run_eval_rules_j : forall fuel cs rs p,
  run_rules_j fuel (compile_env cs) (map compile_rule rs) p = eval_rules_j fuel cs rs p.
Proof.
  induction fuel as [| fuel IH]; intros cs rs p; [reflexivity |].
  destruct rs as [| r rest]; [reflexivity |].
  cbn [run_rules_j eval_rules_j map]. rewrite run_rule_compile_rule.
  destruct (rule_applies r p); [| apply IH].
  destruct (outcome r p) as [v |]; [| apply IH].
  destruct v as [ | | | tt cc | lo hi bb ff | n | n | ]; try reflexivity.
  - apply IH.                                  (* Continue (dead: outcome maps it to None) *)
  - (* Jump n: run the callee, then resume the caller on fall-through *)
    rewrite prog_lookup_compile_env. unfold compile_chain.
    destruct (chain_lookup cs n) as [ch |]; cbn [option_map].
    + rewrite IH. destruct (eval_rules_j fuel cs (c_rules ch) p); [reflexivity | apply IH].
    + apply IH.
  - (* Goto n: tail-call the callee, do not resume *)
    rewrite prog_lookup_compile_env. unfold compile_chain.
    destruct (chain_lookup cs n) as [ch |]; cbn [option_map]; [apply IH | reflexivity].
Qed.

Theorem compile_table_correct : forall fuel cs base p,
  run_table fuel (compile_env cs) (compile_chain base) (c_policy base) p
  = eval_table fuel cs base p.
Proof.
  intros fuel cs base p. unfold run_table, eval_table, compile_chain.
  rewrite run_eval_rules_j. reflexivity.
Qed.
