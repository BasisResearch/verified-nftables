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
  field_loadable f p = true ->
  run_rule rf (compile_load (field_load f) dst :: rest) p =
  run_rule (set_reg rf dst (field_value f p)) rest p.
Proof.
  intros f dst rf rest p Hl. unfold field_value, do_load, compile_load.
  unfold field_loadable, load_ok in Hl.
  destruct (field_load f) eqn:E; simpl; try reflexivity.
  (* LPayload: the VM guards on read_payload_ok, which [Hl] establishes *)
  rewrite Hl. reflexivity.
Qed.

Lemma forallb_map : forall {A B} (g : B -> bool) (h : A -> B) (l : list A),
  forallb g (map h l) = forallb (fun x => g (h x)) l.
Proof. induction l as [| x xs IH]; cbn [map forallb]; [reflexivity | rewrite IH; reflexivity]. Qed.

(** A compiled load whose field is NOT loadable BREAKs the rule: the VM's
    [IPayloadLoad] returns [None] (NFT_BREAK), regardless of the trailing program.
    (Non-payload loads are always loadable, so this only fires for payload fields.) *)
Lemma compile_load_break : forall f dst rf rest p,
  field_loadable f p = false ->
  run_rule rf (compile_load (field_load f) dst :: rest) p = None.
Proof.
  intros f dst rf rest p Hl. unfold field_loadable, load_ok in Hl.
  unfold compile_load. destruct (field_load f) eqn:E; cbn [run_rule] in *; try discriminate Hl.
  rewrite Hl. reflexivity.
Qed.

Lemma compile_load_break_writes : forall f dst rf rest p,
  field_loadable f p = false ->
  run_rule_writes rf (compile_load (field_load f) dst :: rest) p = p.
Proof.
  intros f dst rf rest p Hl. unfold field_loadable, load_ok in Hl.
  unfold compile_load. destruct (field_load f) eqn:E; cbn [run_rule_writes] in *; try discriminate Hl.
  rewrite Hl. reflexivity.
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

(** Loadability of the allocated key registers reduces to loadability of the
    underlying fields (the allocation only renames registers). *)
Lemma forallb_alloc_regs : forall fields slot p,
  forallb (fun fr => field_loadable (fst fr) p) (alloc_regs slot fields)
  = forallb (fun f => field_loadable f p) fields.
Proof.
  induction fields as [| f fs IH]; intros slot p; cbn [alloc_regs forallb fst]; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

Lemma run_load_fields : forall pairs rf tail p,
  forallb (fun fr => field_loadable (fst fr) p) pairs = true ->
  run_rule rf (load_fields pairs ++ tail) p = run_rule (write_fields rf pairs p) tail p.
Proof.
  induction pairs as [| [f r] rest IH]; intros rf tail p Hl.
  - reflexivity.
  - cbn [forallb fst] in Hl. apply Bool.andb_true_iff in Hl. destruct Hl as [Hf Hrest].
    cbn [load_fields map fst snd app write_fields].
    rewrite compile_load_correct by exact Hf. apply IH; exact Hrest.
Qed.

(** If any field in the list is NOT loadable, the loads BREAK (the VM hits the
    failing payload load and returns [None]). *)
Lemma run_load_fields_break : forall pairs rf tail p,
  forallb (fun fr => field_loadable (fst fr) p) pairs = false ->
  run_rule rf (load_fields pairs ++ tail) p = None.
Proof.
  induction pairs as [| [f r] rest IH]; intros rf tail p Hl; [discriminate Hl|].
  cbn [forallb fst] in Hl. apply Bool.andb_false_iff in Hl.
  cbn [load_fields map fst snd app].
  destruct Hl as [Hf | Hrest].
  - apply compile_load_break; exact Hf.
  - destruct (field_loadable f p) eqn:Hf.
    + rewrite compile_load_correct by exact Hf. apply IH; exact Hrest.
    + apply compile_load_break; exact Hf.
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
  forallb (fun fe => field_loadable (fst fe) p) elems = true ->
  exists rf',
    map rf' (map snd (alloc_regs slot (map fst elems)))
      = map (fun fe => apply_transforms (snd fe) (field_value (fst fe) p)) elems
    /\ (forall r0, ~ In r0 (map snd (alloc_regs slot (map fst elems))) -> rf' r0 = rf r0)
    /\ run_rule rf (load_fields_t slot elems ++ tail) p = run_rule rf' tail p.
Proof.
  induction elems as [| [f ts] rest IH]; intros slot rf tail p Hl.
  - exists rf. cbn [load_fields_t map alloc_regs app]. repeat split; reflexivity.
  - cbn [forallb fst] in Hl. apply Bool.andb_true_iff in Hl. destruct Hl as [Hf Hrest].
    cbn [load_fields_t map fst snd alloc_regs].
    edestruct (run_transforms_at_prefix ts (reg_of_slot slot)
                (set_reg rf (reg_of_slot slot) (field_value f p))
                (load_fields_t (slot + field_slots f) rest ++ tail) p) as [rf1 [Ht1 [Ht2 Ht3]]].
    edestruct (IH (slot + field_slots f) rf1 tail p Hrest) as [rf' [Hr1 [Hr2 Hr3]]].
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
      rewrite compile_load_correct by exact Hf. rewrite Ht3, Hr3. reflexivity.
Qed.

(** If any element field is NOT loadable, the transformed-concat loads BREAK. *)
Lemma run_load_fields_t_break : forall elems slot rf tail p,
  forallb (fun fe => field_loadable (fst fe) p) elems = false ->
  run_rule rf (load_fields_t slot elems ++ tail) p = None.
Proof.
  induction elems as [| [f ts] rest IH]; intros slot rf tail p Hl; [discriminate Hl|].
  cbn [forallb fst] in Hl. apply Bool.andb_false_iff in Hl.
  cbn [load_fields_t fst snd]. rewrite <- app_assoc. cbn [app].
  destruct Hl as [Hf | Hrest].
  - apply compile_load_break; exact Hf.
  - destruct (field_loadable f p) eqn:Hf.
    + rewrite compile_load_correct by exact Hf.
      edestruct (run_transforms_at_prefix ts (reg_of_slot slot)
                  (set_reg rf (reg_of_slot slot) (field_value f p))
                  (load_fields_t (slot + field_slots f) rest ++ tail) p) as [rf1 [_ [_ Ht3]]].
      rewrite Ht3. apply IH; exact Hrest.
    + apply compile_load_break; exact Hf.
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
  - cbn [forallb]. unfold eval_matchcond.
    destruct m as [f v0 | f v0 | f neg lo hi | f neg mask xor v0 | f op v0
                  | fields neg nm | f ts op v0 | f ts neg nm
                  | f ts neg lo hi | spec | qspec | clspec
                  | celems neg nm];
      cbn [flat_map compile_match app match_loadable eval_matchcond_body].
    + (* MEq *) destruct (field_loadable f p) eqn:Hf; cbn [andb];
        [| rewrite compile_load_break by exact Hf; reflexivity].
      rewrite compile_load_correct by exact Hf.
      cbn [run_rule]. rewrite set_reg_same. unfold eval_cmp.
      destruct (data_eqb (List.firstn (List.length v0) (field_value f p)) v0); cbn [andb negb];
        [apply IH; exact Hc | reflexivity].
    + (* MNeq *) destruct (field_loadable f p) eqn:Hf; cbn [andb];
        [| rewrite compile_load_break by exact Hf; reflexivity].
      rewrite compile_load_correct by exact Hf.
      cbn [run_rule]. rewrite set_reg_same. unfold eval_cmp.
      destruct (data_eqb (List.firstn (List.length v0) (field_value f p)) v0); cbn [andb negb];
        [reflexivity | apply IH; exact Hc].
    + (* MRange *) destruct (field_loadable f p) eqn:Hf; cbn [andb];
        [| rewrite compile_load_break by exact Hf; reflexivity].
      rewrite compile_load_correct by exact Hf.
      cbn [run_rule]. rewrite set_reg_same.
      destruct (eval_range (if neg then CNe else CEq) (field_value f p) lo hi);
        cbn [andb]; [apply IH; exact Hc | reflexivity].
    + (* MMasked *) destruct (field_loadable f p) eqn:Hf; cbn [andb];
        [| rewrite compile_load_break by exact Hf; reflexivity].
      rewrite compile_load_correct by exact Hf.
      cbn [run_rule]. rewrite !set_reg_same.
      destruct (eval_cmp (if neg then CNe else CEq)
                 (data_bitops (field_value f p) mask xor) v0);
        cbn [andb]; [apply IH; exact Hc | reflexivity].
    + (* MCmp: ordered comparison *) destruct (field_loadable f p) eqn:Hf; cbn [andb];
        [| rewrite compile_load_break by exact Hf; reflexivity].
      rewrite compile_load_correct by exact Hf.
      cbn [run_rule]. rewrite set_reg_same.
      destruct (eval_cmp op (field_value f p) v0);
        cbn [andb]; [apply IH; exact Hc | reflexivity].
    + (* MConcatSet: multi-register key, distinct registers per field *)
      change (match_loadable (MConcatSet fields neg nm) p) with (fields_loadable fields p).
      unfold fields_loadable.
      destruct (forallb (fun f => field_loadable f p) fields) eqn:Hf; cbn [andb].
      2:{ rewrite <- !app_assoc. cbn [app]. rewrite run_load_fields_break; [reflexivity|].
          rewrite forallb_alloc_regs. exact Hf. }
      rewrite <- !app_assoc. cbn [app].
      rewrite run_load_fields by (rewrite forallb_alloc_regs; exact Hf).
      cbn [run_rule].
      rewrite map_write_fields by apply alloc_regs_nodup.
      rewrite map_fst_field, alloc_regs_fst.
      destruct (xorb neg
                 (concat_set_mem (map (fun f => field_value f p) fields)
                           (e_set (pkt_env p) nm)));
        cbn [andb]; [apply IH; exact Hc | reflexivity].
    + (* MTransform *) destruct (field_loadable f p) eqn:Hf; cbn [andb];
        [| rewrite compile_load_break by exact Hf; reflexivity].
      rewrite compile_load_correct by exact Hf.
      rewrite <- !app_assoc. cbn [app].
      edestruct run_transforms_cmp as [rf' Hr]. rewrite Hr. rewrite set_reg_same.
      destruct (eval_cmp op
                 (apply_transforms ts (field_value f p)) v0);
        cbn [andb]; [apply IH; exact Hc | reflexivity].
    + (* MSetT: set membership of a transformed value *)
      destruct (field_loadable f p) eqn:Hf; cbn [andb];
        [| rewrite compile_load_break by exact Hf; reflexivity].
      rewrite compile_load_correct by exact Hf. rewrite <- !app_assoc. cbn [app].
      edestruct (run_transforms_prefix ts (set_reg rf 1 (field_value f p))
                  (ILookup [1] nm neg :: (flat_map compile_match ms ++ tail)) p)
        as [rf' [H1 H2]].
      rewrite H2. cbn [run_rule map]. rewrite H1, set_reg_same.
      rewrite concat_set_mem_single.
      destruct (xorb neg (set_mem (apply_transforms ts (field_value f p))
                                   (e_set (pkt_env p) nm)));
        cbn [andb]; [apply IH; exact Hc | reflexivity].
    + (* MRangeT: range of a transformed value *)
      destruct (field_loadable f p) eqn:Hf; cbn [andb];
        [| rewrite compile_load_break by exact Hf; reflexivity].
      rewrite compile_load_correct by exact Hf. rewrite <- !app_assoc. cbn [app].
      edestruct (run_transforms_prefix ts (set_reg rf 1 (field_value f p))
                  (IRange (if neg then CNe else CEq) 1 lo hi
                   :: (flat_map compile_match ms ++ tail)) p) as [rf' [H1 H2]].
      rewrite H2. cbn [run_rule]. rewrite H1, set_reg_same.
      destruct (eval_range (if neg then CNe else CEq)
                 (apply_transforms ts (field_value f p)) lo hi);
        cbn [andb]; [apply IH; exact Hc | reflexivity].
    + (* MLimit: no load, a stateful break (over-bit XORed into the test) *)
      cbn [run_rule andb].
      destruct (xorb (Nat.eqb (Nat.land (ls_flags spec) 1) 1)
                     (Nat.ltb 0 (e_limit (pkt_env p) spec))); cbn [andb];
        [apply IH; exact Hc | reflexivity].
    + (* MQuota: no load, a stateful break (over-bit XORed into the test) *)
      cbn [run_rule andb].
      destruct (xorb (Nat.eqb (Nat.land (q_flags qspec) 1) 1)
                     (Nat.ltb 0 (e_quota (pkt_env p) qspec))); cbn [andb];
        [apply IH; exact Hc | reflexivity].
    + (* MConnlimit: no load, a stateful break (over-bit XORed into the test) *)
      cbn [run_rule andb].
      destruct (xorb (Nat.eqb (Nat.land (cl_flags clspec) 1) 1)
                     (Nat.ltb 0 (e_connlimit (pkt_env p) clspec))); cbn [andb];
        [apply IH; exact Hc | reflexivity].
    + (* MConcatSetT: transformed multi-register key, distinct registers per element *)
      change (match_loadable (MConcatSetT celems neg nm) p)
        with (fields_loadable (map fst celems) p).
      unfold fields_loadable. rewrite forallb_map.
      destruct (forallb (fun fe => field_loadable (fst fe) p) celems) eqn:Hf; cbn [andb].
      2:{ rewrite <- !app_assoc. cbn [app]. rewrite run_load_fields_t_break by exact Hf.
          reflexivity. }
      rewrite <- !app_assoc. cbn [app].
      edestruct (run_load_fields_t celems 0 rf
                  (ILookup (map snd (alloc_regs 0 (map fst celems))) nm neg
                   :: (flat_map compile_match ms ++ tail)) p Hf) as [rf' [Hrb [_ Hrun]]].
      rewrite Hrun. cbn [run_rule]. rewrite Hrb.
      destruct (xorb neg (concat_set_mem
                 (map (fun fe => apply_transforms (snd fe) (field_value (fst fe) p)) celems)
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
  forallb (fun e => field_loadable (fst e) p) srcs = true ->
  exists rf',
    run_rule rf
      (flat_map (fun e =>
         compile_load (field_load (fst e)) 2 :: compile_transforms_at 2 (snd e)
         ++ [IBitwiseOr 1 1 2]) srcs ++ tail) p
    = run_rule rf' tail p.
Proof.
  induction srcs as [| [f ts] srcs IH]; intros rf tail p Hl.
  - exists rf. reflexivity.
  - cbn [forallb fst] in Hl. apply Bool.andb_true_iff in Hl. destruct Hl as [Hf Hrest].
    cbn [flat_map fst snd]. rewrite <- !app_assoc. cbn [app].
    rewrite compile_load_correct by exact Hf. rewrite <- app_assoc.
    edestruct (run_transforms_at_prefix ts 2 (set_reg rf 2 (field_value f p)))
      as [rf1 [_ [_ Ht]]].
    rewrite Ht. cbn [app run_rule].
    edestruct (IH (set_reg rf1 1 (data_or (rf1 1) (rf1 2))) tail p Hrest) as [rf' Hr].
    rewrite Hr. exists rf'. reflexivity.
Qed.

Lemma run_or_chain_break : forall srcs rf tail p,
  forallb (fun e => field_loadable (fst e) p) srcs = false ->
  run_rule rf
    (flat_map (fun e =>
       compile_load (field_load (fst e)) 2 :: compile_transforms_at 2 (snd e)
       ++ [IBitwiseOr 1 1 2]) srcs ++ tail) p = None.
Proof.
  induction srcs as [| [f ts] srcs IH]; intros rf tail p Hl; [discriminate Hl|].
  cbn [forallb fst] in Hl. apply Bool.andb_false_iff in Hl.
  cbn [flat_map fst snd]. rewrite <- !app_assoc. cbn [app].
  destruct (field_loadable f p) eqn:Hf.
  - rewrite compile_load_correct by exact Hf. rewrite <- app_assoc.
    edestruct (run_transforms_at_prefix ts 2 (set_reg rf 2 (field_value f p)))
      as [rf1 [_ [_ Ht]]].
    rewrite Ht. cbn [app run_rule]. apply IH.
    destruct Hl as [Hd | Hr]; [congruence | exact Hr].
  - apply compile_load_break; exact Hf.
Qed.

Lemma run_vsrc_exists : forall vs rf rest p,
  vsrc_loadable vs p = true ->
  exists rf', run_rule rf (compile_vsrc vs ++ rest) p = run_rule rf' rest p.
Proof.
  destruct vs as [v | f ts | fields vts name | hf hl hs hm ho
                 | osrcs ofinal | telems tname
                 | hmf hml hms hmm hmo hmname]; intros rf rest p Hl;
    cbn [vsrc_loadable] in Hl.
  - exists (set_reg rf 1 v). reflexivity.
  - edestruct (run_transforms_prefix ts (set_reg rf 1 (field_value f p)) rest p)
      as [rf' [_ Hr]].
    exists rf'. cbn [compile_vsrc app]. rewrite compile_load_correct by exact Hl. exact Hr.
  - (* VMap: concat key loaded, optionally transformed, then ILookupVal writes
       dreg; all verdict-neutral, so the verdict tail is reached from some rf. *)
    cbn [compile_vsrc]. rewrite <- !app_assoc.
    rewrite run_load_fields by (rewrite forallb_alloc_regs; exact Hl).
    edestruct (run_transforms_prefix vts (write_fields rf (alloc_regs 0 fields) p)
                ([ILookupVal (map snd (alloc_regs 0 fields)) name 1] ++ rest) p)
      as [rf' [_ Hr]].
    rewrite Hr. cbn [app run_rule]. eexists; reflexivity.
  - (* VHash: load the concat source fields, then the verdict-neutral IJhash *)
    cbn [compile_vsrc]. rewrite <- app_assoc.
    rewrite run_load_fields by (rewrite forallb_alloc_regs; exact Hl).
    cbn [app run_rule]. eexists; reflexivity.
  - (* VOr: base into reg1, OR-chain folding more sources, then final transforms *)
    destruct osrcs as [| [f0 ts0] orest].
    + exists rf. cbn [compile_vsrc app]. reflexivity.
    + unfold fields_loadable in Hl. rewrite forallb_map in Hl.
      cbn [forallb fst] in Hl. apply Bool.andb_true_iff in Hl. destruct Hl as [Hf0 Hrest].
      cbn [compile_vsrc fst snd]. rewrite <- !app_assoc. cbn [app].
      rewrite compile_load_correct by exact Hf0.
      edestruct (run_transforms_at_prefix ts0 1 (set_reg rf 1 (field_value f0 p)))
        as [rf1 [_ [_ Ht0]]].
      rewrite Ht0.
      edestruct (run_or_chain orest rf1) as [rf2 Hc]; [exact Hrest|].
      rewrite Hc.
      edestruct (run_transforms_at_prefix ofinal 1 rf2 rest p) as [rf' [_ [_ Hf]]].
      rewrite Hf. exists rf'. reflexivity.
  - (* VMapT: transformed-concat key loaded, then verdict-neutral ILookupVal *)
    cbn [compile_vsrc]. rewrite <- app_assoc.
    edestruct (run_load_fields_t telems 0 rf
                ([ILookupVal (map snd (alloc_regs 0 (map fst telems))) tname 1]
                 ++ rest) p) as [rf' [_ [_ Hrun]]].
    { unfold fields_loadable in Hl. rewrite forallb_map in Hl. exact Hl. }
    rewrite Hrun. cbn [app run_rule]. eexists; reflexivity.
  - (* VHashMap: load source, jhash into reg 1, then verdict-neutral ILookupVal *)
    cbn [compile_vsrc]. rewrite <- !app_assoc.
    rewrite run_load_fields by (rewrite forallb_alloc_regs; exact Hl).
    cbn [app run_rule]. eexists; reflexivity.
Qed.

(** If a value source's fields are not all loadable, its compiled load BREAKs. *)
Lemma run_vsrc_break : forall vs rf rest p,
  vsrc_loadable vs p = false ->
  run_rule rf (compile_vsrc vs ++ rest) p = None.
Proof.
  destruct vs as [v | f ts | fields ts nm | hf hl hs hm ho
                 | osrcs ofinal | telems tname
                 | hmf hml hms hmm hmo hmname]; intros rf rest p Hl;
    cbn [vsrc_loadable] in Hl; try discriminate Hl.
  - (* VField *) cbn [compile_vsrc app]. apply compile_load_break; exact Hl.
  - (* VMap *) cbn [compile_vsrc]. rewrite <- !app_assoc.
    rewrite run_load_fields_break; [reflexivity|]. rewrite forallb_alloc_regs; exact Hl.
  - (* VHash *) cbn [compile_vsrc]. rewrite <- app_assoc.
    rewrite run_load_fields_break; [reflexivity|]. rewrite forallb_alloc_regs; exact Hl.
  - (* VOr *) destruct osrcs as [| [f0 ts0] orest]; [discriminate Hl |].
    unfold fields_loadable in Hl. rewrite forallb_map in Hl.
    cbn [forallb fst] in Hl. apply Bool.andb_false_iff in Hl.
    cbn [compile_vsrc fst snd]. rewrite <- !app_assoc. cbn [app].
    destruct (field_loadable f0 p) eqn:Hf0.
    + (* base loads; a later OR source breaks *)
      rewrite compile_load_correct by exact Hf0.
      edestruct (run_transforms_at_prefix ts0 1 (set_reg rf 1 (field_value f0 p)))
        as [rf1 [_ [_ Ht0]]].
      rewrite Ht0. rewrite run_or_chain_break; [reflexivity|].
      destruct Hl as [Hd | Hr]; [congruence | exact Hr].
    + apply compile_load_break; exact Hf0.
  - (* VMapT *) cbn [compile_vsrc]. rewrite <- app_assoc.
    rewrite run_load_fields_t_break; [reflexivity|].
    unfold fields_loadable in Hl. rewrite forallb_map in Hl. exact Hl.
  - (* VHashMap *) cbn [compile_vsrc]. rewrite <- !app_assoc.
    rewrite run_load_fields_break; [reflexivity|]. rewrite forallb_alloc_regs; exact Hl.
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
  field_loadable f p = true ->
  exists rf', run_rule rf (compile_vsrc (VField f ts) ++ rest) p = run_rule rf' rest p
              /\ rf' 1 = eval_vsrc (VField f ts) p.
Proof.
  intros f ts rf rest p Hl. cbn [compile_vsrc app]. rewrite compile_load_correct by exact Hl.
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
  match i with
  | IMetaSet _ _ | ICtSet _ _ | INotrack
  | IDynset _ _ _ None _ | IDynset _ _ _ (Some _) true => true
  | _ => false end.
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
  all: try (destruct (Nat.ltb 0 (e_limit _ _)); [apply IH; exact Hno | reflexivity]).
  all: try (destruct (Nat.ltb 0 (e_quota _ _)); [apply IH; exact Hno | reflexivity]).
  all: try (destruct (Nat.ltb 0 (e_connlimit _ _)); [apply IH; exact Hno | reflexivity]).
  all: try (destruct (assoc_verdict _ _); [reflexivity | apply IH; exact Hno]).
  all: try (destruct (read_payload_ok _ _ _ _); [apply IH; exact Hno | reflexivity]).
  (* ISynproxy: break/stop return [p]; the continue arm threads by IH. *)
  all: try (destruct (synproxy_loadable p);
            [destruct (synproxy_stops p); [reflexivity | apply IH; exact Hno] | reflexivity]).
  (* IDynset: writes_instr and run_rule_writes branch on the data-reg option and
     the field/immediate flag.  set (None) and field-map (Some _, true) are writes
     so [no_writes] excludes them (discriminate); an immediate-map (Some _, false)
     is env-neutral, threaded by IH. *)
  all: match goal with
       | [ d : option reg, b : bool |- _ ] =>
           destruct d as [dreg |]; [destruct b |];
           cbn [run_rule_writes writes_instr negb] in *;
           solve [ apply IH; exact Hno | discriminate Hi ]
       end.
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
  field_loadable f p = true ->
  run_rule_writes rf (compile_load (field_load f) dst :: rest) p =
  run_rule_writes (set_reg rf dst (field_value f p)) rest p.
Proof.
  intros f dst rf rest p Hl. unfold field_value, do_load, compile_load.
  unfold field_loadable, load_ok in Hl.
  destruct (field_load f) eqn:E; simpl; try reflexivity.
  rewrite Hl. reflexivity.
Qed.

Lemma run_load_fields_writes : forall pairs rf tail p,
  forallb (fun fr => field_loadable (fst fr) p) pairs = true ->
  run_rule_writes rf (load_fields pairs ++ tail) p = run_rule_writes (write_fields rf pairs p) tail p.
Proof.
  induction pairs as [| [f r] rest IH]; intros rf tail p Hl.
  - reflexivity.
  - cbn [forallb fst] in Hl. apply Bool.andb_true_iff in Hl. destruct Hl as [Hf Hrest].
    cbn [load_fields map fst snd app write_fields].
    rewrite compile_load_writes by exact Hf. apply IH; exact Hrest.
Qed.

Lemma run_load_fields_writes_break : forall pairs rf tail p,
  forallb (fun fr => field_loadable (fst fr) p) pairs = false ->
  run_rule_writes rf (load_fields pairs ++ tail) p = p.
Proof.
  induction pairs as [| [f r] rest IH]; intros rf tail p Hl; [discriminate Hl|].
  cbn [forallb fst] in Hl. apply Bool.andb_false_iff in Hl.
  cbn [load_fields map fst snd app].
  destruct Hl as [Hf | Hrest].
  - apply compile_load_break_writes; exact Hf.
  - destruct (field_loadable f p) eqn:Hf.
    + rewrite compile_load_writes by exact Hf. apply IH; exact Hrest.
    + apply compile_load_break_writes; exact Hf.
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
  forallb (fun fe => field_loadable (fst fe) p) elems = true ->
  exists rf',
    map rf' (map snd (alloc_regs slot (map fst elems)))
      = map (fun fe => apply_transforms (snd fe) (field_value (fst fe) p)) elems
    /\ (forall r0, ~ In r0 (map snd (alloc_regs slot (map fst elems))) -> rf' r0 = rf r0)
    /\ run_rule_writes rf (load_fields_t slot elems ++ tail) p = run_rule_writes rf' tail p.
Proof.
  induction elems as [| [f ts] rest IH]; intros slot rf tail p Hl.
  - exists rf. cbn [load_fields_t map alloc_regs app]. repeat split; reflexivity.
  - cbn [forallb fst] in Hl. apply Bool.andb_true_iff in Hl. destruct Hl as [Hf Hrest].
    cbn [load_fields_t map fst snd alloc_regs].
    edestruct (run_transforms_at_prefix_writes ts (reg_of_slot slot)
                (set_reg rf (reg_of_slot slot) (field_value f p))
                (load_fields_t (slot + field_slots f) rest ++ tail) p) as [rf1 [Ht1 [Ht2 Ht3]]].
    edestruct (IH (slot + field_slots f) rf1 tail p Hrest) as [rf' [Hr1 [Hr2 Hr3]]].
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
      rewrite compile_load_writes by exact Hf. rewrite Ht3, Hr3. reflexivity.
Qed.

Lemma run_load_fields_t_writes_break : forall elems slot rf tail p,
  forallb (fun fe => field_loadable (fst fe) p) elems = false ->
  run_rule_writes rf (load_fields_t slot elems ++ tail) p = p.
Proof.
  induction elems as [| [f ts] rest IH]; intros slot rf tail p Hl; [discriminate Hl|].
  cbn [forallb fst] in Hl. apply Bool.andb_false_iff in Hl.
  cbn [load_fields_t fst snd]. rewrite <- app_assoc. cbn [app].
  destruct Hl as [Hf | Hrest].
  - apply compile_load_break_writes; exact Hf.
  - destruct (field_loadable f p) eqn:Hf.
    + rewrite compile_load_writes by exact Hf.
      edestruct (run_transforms_at_prefix_writes ts (reg_of_slot slot)
                  (set_reg rf (reg_of_slot slot) (field_value f p))
                  (load_fields_t (slot + field_slots f) rest ++ tail) p) as [rf1 [_ [_ Ht3]]].
      rewrite Ht3. apply IH; exact Hrest.
    + apply compile_load_break_writes; exact Hf.
Qed.

(** Writes-version of the OR-chain, additionally tracking register 1's folded
    value: each source is loaded into reg 2 (transformed there), then OR'd into
    the accumulator reg 1. *)
Lemma run_or_chain_writes : forall srcs rf tail p,
  forallb (fun e => field_loadable (fst e) p) srcs = true ->
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
  induction srcs as [| [f ts] srcs IH]; intros rf tail p Hl.
  - exists rf. split; reflexivity.
  - cbn [forallb fst] in Hl. apply Bool.andb_true_iff in Hl. destruct Hl as [Hf Hrest].
    cbn [flat_map fst snd]. rewrite <- !app_assoc. cbn [app].
    rewrite compile_load_writes by exact Hf. rewrite <- !app_assoc.
    edestruct (run_transforms_at_prefix_writes ts 2 (set_reg rf 2 (field_value f p))
                ([IBitwiseOr 1 1 2] ++ flat_map (fun e =>
                   compile_load (field_load (fst e)) 2 :: compile_transforms_at 2 (snd e)
                   ++ [IBitwiseOr 1 1 2]) srcs ++ tail) p) as [rf1 [Ht1 [Ht2 Ht3]]].
    rewrite Ht3. cbn [app run_rule_writes].
    edestruct (IH (set_reg rf1 1 (data_or (rf1 1) (rf1 2))) tail p Hrest) as [rf' [Hr Hv]].
    rewrite Hr. exists rf'. split; [reflexivity |].
    rewrite Hv, set_reg_same. cbn [fold_left]. f_equal.
    rewrite Ht1, set_reg_same. rewrite (Ht2 1) by (intro; discriminate).
    rewrite set_reg_other by (intro; discriminate). reflexivity.
Qed.

Lemma run_or_chain_writes_break : forall srcs rf tail p,
  forallb (fun e => field_loadable (fst e) p) srcs = false ->
  run_rule_writes rf
    (flat_map (fun e =>
       compile_load (field_load (fst e)) 2 :: compile_transforms_at 2 (snd e)
       ++ [IBitwiseOr 1 1 2]) srcs ++ tail) p = p.
Proof.
  induction srcs as [| [f ts] srcs IH]; intros rf tail p Hl; [discriminate Hl|].
  cbn [forallb fst] in Hl. apply Bool.andb_false_iff in Hl.
  cbn [flat_map fst snd]. rewrite <- !app_assoc. cbn [app].
  destruct (field_loadable f p) eqn:Hf.
  - rewrite compile_load_writes by exact Hf. rewrite <- app_assoc.
    edestruct (run_transforms_at_prefix_writes ts 2 (set_reg rf 2 (field_value f p)))
      as [rf1 [_ [_ Ht]]].
    rewrite Ht. cbn [app run_rule_writes]. apply IH.
    destruct Hl as [Hd | Hr]; [congruence | exact Hr].
  - apply compile_load_break_writes; exact Hf.
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
  vsrc_loadable vs p = true ->
  exists rf', run_rule_writes rf (compile_vsrc vs ++ rest) p = run_rule_writes rf' rest p
              /\ rf' 1 = eval_vsrc vs p.
Proof.
  intros vs rf rest p Hs Hld.
  destruct vs as [v | f ts | fields ts nm | hfields hlen hseed hmod hoff
                 | osrcs ofinal | elems nm | mfields mlen mseed mmod moff mnm];
    cbn [simple_vsrc] in Hs; cbn [vsrc_loadable] in Hld; try discriminate.
  - (* VImm *) exists (set_reg rf 1 v). cbn [compile_vsrc app run_rule_writes].
    split; [reflexivity | apply set_reg_same].
  - (* VField *) cbn [compile_vsrc app]. rewrite compile_load_writes by exact Hld.
    edestruct (run_transforms_prefix_writes ts (set_reg rf 1 (field_value f p)) rest p)
      as [rf' [H1 [_ H2]]].
    exists rf'. split; [exact H2 |]. cbn [eval_vsrc]. rewrite H1, set_reg_same. reflexivity.
  - (* VMap (f0 :: fr) ts nm : load key fields, transform reg 1, lookup *)
    destruct fields as [| f0 fr]; [discriminate Hs |].
    cbn [compile_vsrc]. rewrite <- !app_assoc.
    rewrite run_load_fields_writes by (rewrite forallb_alloc_regs; exact Hld).
    edestruct (run_transforms_prefix_writes ts (write_fields rf (alloc_regs 0 (f0 :: fr)) p)
                ([ILookupVal (map snd (alloc_regs 0 (f0 :: fr))) nm 1] ++ rest) p)
      as [rf1 [Hv1 [Hfr Hr1]]].
    rewrite Hr1. cbn [app run_rule_writes].
    eexists. split; [reflexivity |]. rewrite set_reg_same. cbn [eval_vsrc].
    do 2 f_equal.
    replace (map snd (alloc_regs 0 (f0 :: fr)))
      with (1 :: map snd (alloc_regs (field_slots f0) fr))
      by (cbn [alloc_regs map snd reg_of_slot Nat.eqb Nat.add]; reflexivity).
    cbn [map]. f_equal.
    + (* head: reg 1 holds the transformed first field *)
      rewrite Hv1. f_equal. apply write_fields_head.
    + (* tail: later key regs untouched by the reg-1 transforms *)
      transitivity (map (write_fields rf (alloc_regs 0 (f0 :: fr)) p)
                        (map snd (alloc_regs (field_slots f0) fr))).
      * apply map_ext_in. intros r Hin. apply Hfr. intro Heq; subst r.
        apply alloc_regs_lb in Hin. pose proof (field_slots_pos f0).
        assert (0 < field_slots f0) as Hlt by lia. apply reg_of_slot_mono in Hlt.
        cbn [reg_of_slot Nat.eqb] in Hlt. lia.
      * pose proof (map_write_fields (alloc_regs 0 (f0 :: fr)) rf p (alloc_regs_nodup _ _)) as Hwf.
        rewrite map_fst_field, alloc_regs_fst in Hwf.
        cbn [alloc_regs map snd Nat.add] in Hwf. injection Hwf as _ Htl. exact Htl.
  - (* VHash (hf0 :: hfr) ... : jhash of the first loaded field *)
    destruct hfields as [| hf0 hfr]; [discriminate Hs |].
    cbn [compile_vsrc]. rewrite <- app_assoc.
    rewrite run_load_fields_writes by (rewrite forallb_alloc_regs; exact Hld).
    replace (match map snd (alloc_regs 4 (hf0 :: hfr)) with r :: _ => r | [] => 1 end)
      with (reg_of_slot 4) by reflexivity.
    cbn [app run_rule_writes].
    eexists. split; [reflexivity |]. rewrite set_reg_same, write_fields_head.
    cbn [eval_vsrc]. reflexivity.
  - (* VOr ((f0,ts0) :: orest) ofinal : base into reg 1, OR-fold, final transforms *)
    destruct osrcs as [| [f0 ts0] orest]; [discriminate Hs |].
    unfold fields_loadable in Hld. rewrite forallb_map in Hld.
    cbn [forallb fst] in Hld. apply Bool.andb_true_iff in Hld. destruct Hld as [Hf0 Hldr].
    cbn [compile_vsrc fst snd]. rewrite <- !app_assoc. cbn [app].
    rewrite compile_load_writes by exact Hf0.
    edestruct (run_transforms_at_prefix_writes ts0 1 (set_reg rf 1 (field_value f0 p))
                (flat_map (fun e => compile_load (field_load (fst e)) 2
                                    :: compile_transforms_at 2 (snd e) ++ [IBitwiseOr 1 1 2]) orest
                 ++ compile_transforms_at 1 ofinal ++ rest) p) as [rf1 [Hv1 [_ Hr1]]].
    rewrite Hr1.
    edestruct (run_or_chain_writes orest rf1 (compile_transforms_at 1 ofinal ++ rest) p Hldr)
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
    { unfold fields_loadable in Hld. rewrite forallb_map in Hld. exact Hld. }
    rewrite Hr. cbn [app run_rule_writes].
    eexists. split; [reflexivity |]. rewrite set_reg_same, Hrb. reflexivity.
  - (* VHashMap (mf0 :: mfr) ... : jhash then value-map lookup *)
    destruct mfields as [| mf0 mfr]; [discriminate Hs |].
    cbn [compile_vsrc]. rewrite <- !app_assoc.
    rewrite run_load_fields_writes by (rewrite forallb_alloc_regs; exact Hld).
    replace (match map snd (alloc_regs 4 (mf0 :: mfr)) with r :: _ => r | [] => 1 end)
      with (reg_of_slot 4) by reflexivity.
    cbn [app run_rule_writes map concat].
    eexists. split; [reflexivity |]. rewrite !set_reg_same, app_nil_r, write_fields_head.
    cbn [eval_vsrc]. reflexivity.
Qed.

(** Writes-version of the value-source break: an unloadable operand stops the run
    with the packet unchanged. *)
Lemma run_vsrc_writes_break : forall vs rf rest p,
  vsrc_loadable vs p = false ->
  run_rule_writes rf (compile_vsrc vs ++ rest) p = p.
Proof.
  destruct vs as [v | f ts | fields ts nm | hf hl hs hm ho
                 | osrcs ofinal | telems tname
                 | hmf hml hms hmm hmo hmname]; intros rf rest p Hl;
    cbn [vsrc_loadable] in Hl; try discriminate Hl.
  - (* VField *) cbn [compile_vsrc app]. apply compile_load_break_writes; exact Hl.
  - (* VMap *) cbn [compile_vsrc]. rewrite <- !app_assoc.
    rewrite run_load_fields_writes_break; [reflexivity|]. rewrite forallb_alloc_regs; exact Hl.
  - (* VHash *) cbn [compile_vsrc]. rewrite <- app_assoc.
    rewrite run_load_fields_writes_break; [reflexivity|]. rewrite forallb_alloc_regs; exact Hl.
  - (* VOr *) destruct osrcs as [| [f0 ts0] orest]; [discriminate Hl |].
    unfold fields_loadable in Hl. rewrite forallb_map in Hl.
    cbn [forallb fst] in Hl. apply Bool.andb_false_iff in Hl.
    cbn [compile_vsrc fst snd]. rewrite <- !app_assoc. cbn [app].
    destruct (field_loadable f0 p) eqn:Hf0.
    + rewrite compile_load_writes by exact Hf0.
      edestruct (run_transforms_at_prefix_writes ts0 1 (set_reg rf 1 (field_value f0 p)))
        as [rf1 [_ [_ Ht0]]].
      rewrite Ht0. rewrite run_or_chain_writes_break; [reflexivity|].
      destruct Hl as [Hd | Hr]; [congruence | exact Hr].
    + apply compile_load_break_writes; exact Hf0.
  - (* VMapT *) cbn [compile_vsrc]. rewrite <- app_assoc.
    rewrite run_load_fields_t_writes_break; [reflexivity|].
    unfold fields_loadable in Hl. rewrite forallb_map in Hl. exact Hl.
  - (* VHashMap *) cbn [compile_vsrc]. rewrite <- !app_assoc.
    rewrite run_load_fields_writes_break; [reflexivity|]. rewrite forallb_alloc_regs; exact Hl.
Qed.

(** Single-match gating under [run_rule_writes]: a match passes (continue to the
    [run_rule_writes]-constant tail result [R]) or breaks (return the packet
    unchanged), exactly tracking [eval_matchcond].  Mirrors the per-match cases of
    [run_compile_matches_const], with the break returning [p] instead of [None]. *)
Lemma writes_match_one : forall m X p R,
  (forall rf, run_rule_writes rf X p = R) ->
  forall rf, run_rule_writes rf (compile_match m ++ X) p = if eval_matchcond m p then R else p.
Proof.
  intros m X p R Hc rf. unfold eval_matchcond.
  destruct m as [f v0 | f v0 | f neg lo hi | f neg mask xor v0 | f op v0
                | fields neg nm | f ts op v0 | f ts neg nm
                | f ts neg lo hi | spec | qspec | clspec
                | celems neg nm]; cbn [compile_match app match_loadable eval_matchcond_body].
  - (* MEq *) destruct (field_loadable f p) eqn:Hf; cbn [andb];
      [| rewrite compile_load_break_writes by exact Hf; reflexivity].
    rewrite compile_load_writes by exact Hf. cbn [run_rule_writes]. rewrite set_reg_same.
    unfold eval_cmp.
    destruct (data_eqb (List.firstn (List.length v0) (field_value f p)) v0); [apply Hc | reflexivity].
  - (* MNeq *) destruct (field_loadable f p) eqn:Hf; cbn [andb];
      [| rewrite compile_load_break_writes by exact Hf; reflexivity].
    rewrite compile_load_writes by exact Hf. cbn [run_rule_writes]. rewrite set_reg_same.
    unfold eval_cmp.
    destruct (data_eqb (List.firstn (List.length v0) (field_value f p)) v0); cbn [negb]; [reflexivity | apply Hc].
  - (* MRange *) destruct (field_loadable f p) eqn:Hf; cbn [andb];
      [| rewrite compile_load_break_writes by exact Hf; reflexivity].
    rewrite compile_load_writes by exact Hf. cbn [run_rule_writes]. rewrite set_reg_same.
    destruct (eval_range (if neg then CNe else CEq) (field_value f p) lo hi);
      [apply Hc | reflexivity].
  - (* MMasked *) destruct (field_loadable f p) eqn:Hf; cbn [andb];
      [| rewrite compile_load_break_writes by exact Hf; reflexivity].
    rewrite compile_load_writes by exact Hf. cbn [run_rule_writes]. rewrite !set_reg_same.
    destruct (eval_cmp (if neg then CNe else CEq) (data_bitops (field_value f p) mask xor) v0);
      [apply Hc | reflexivity].
  - (* MCmp *) destruct (field_loadable f p) eqn:Hf; cbn [andb];
      [| rewrite compile_load_break_writes by exact Hf; reflexivity].
    rewrite compile_load_writes by exact Hf. cbn [run_rule_writes]. rewrite set_reg_same.
    destruct (eval_cmp op (field_value f p) v0); [apply Hc | reflexivity].
  - (* MConcatSet *)
    change (match_loadable (MConcatSet fields neg nm) p) with (fields_loadable fields p).
    unfold fields_loadable.
    destruct (forallb (fun f => field_loadable f p) fields) eqn:Hf; cbn [andb].
    2:{ rewrite <- !app_assoc. cbn [app].
        rewrite run_load_fields_writes_break by (rewrite forallb_alloc_regs; exact Hf). reflexivity. }
    rewrite <- !app_assoc. cbn [app].
    rewrite run_load_fields_writes by (rewrite forallb_alloc_regs; exact Hf). cbn [run_rule_writes].
    rewrite map_write_fields by apply alloc_regs_nodup.
    rewrite map_fst_field, alloc_regs_fst.
    destruct (xorb neg (concat_set_mem (map (fun f => field_value f p) fields)
                                 (e_set (pkt_env p) nm)));
      [apply Hc | reflexivity].
  - (* MTransform *) destruct (field_loadable f p) eqn:Hf; cbn [andb];
      [| rewrite compile_load_break_writes by exact Hf; reflexivity].
    rewrite compile_load_writes by exact Hf. rewrite <- !app_assoc. cbn [app].
    edestruct (run_transforms_prefix_writes ts (set_reg rf 1 (field_value f p))
                (ICmp op 1 v0 :: X) p) as [rf' [H1 [_ H2]]].
    rewrite H2. cbn [run_rule_writes]. rewrite H1, set_reg_same.
    destruct (eval_cmp op (apply_transforms ts (field_value f p)) v0); [apply Hc | reflexivity].
  - (* MSetT *) destruct (field_loadable f p) eqn:Hf; cbn [andb];
      [| rewrite compile_load_break_writes by exact Hf; reflexivity].
    rewrite compile_load_writes by exact Hf. rewrite <- !app_assoc. cbn [app].
    edestruct (run_transforms_prefix_writes ts (set_reg rf 1 (field_value f p))
                (ILookup [1] nm neg :: X) p) as [rf' [H1 [_ H2]]].
    rewrite H2. cbn [run_rule_writes map]. rewrite H1, set_reg_same.
    rewrite concat_set_mem_single.
    destruct (xorb neg (set_mem (apply_transforms ts (field_value f p)) (e_set (pkt_env p) nm)));
      [apply Hc | reflexivity].
  - (* MRangeT *) destruct (field_loadable f p) eqn:Hf; cbn [andb];
      [| rewrite compile_load_break_writes by exact Hf; reflexivity].
    rewrite compile_load_writes by exact Hf. rewrite <- !app_assoc. cbn [app].
    edestruct (run_transforms_prefix_writes ts (set_reg rf 1 (field_value f p))
                (IRange (if neg then CNe else CEq) 1 lo hi :: X) p) as [rf' [H1 [_ H2]]].
    rewrite H2. cbn [run_rule_writes]. rewrite H1, set_reg_same.
    destruct (eval_range (if neg then CNe else CEq) (apply_transforms ts (field_value f p)) lo hi);
      [apply Hc | reflexivity].
  - (* MLimit *) cbn [run_rule_writes andb].
    destruct (xorb (Nat.eqb (Nat.land (ls_flags spec) 1) 1)
                   (Nat.ltb 0 (e_limit (pkt_env p) spec))); [apply Hc | reflexivity].
  - (* MQuota *) cbn [run_rule_writes andb].
    destruct (xorb (Nat.eqb (Nat.land (q_flags qspec) 1) 1)
                   (Nat.ltb 0 (e_quota (pkt_env p) qspec))); [apply Hc | reflexivity].
  - (* MConnlimit *) cbn [run_rule_writes andb].
    destruct (xorb (Nat.eqb (Nat.land (cl_flags clspec) 1) 1)
                   (Nat.ltb 0 (e_connlimit (pkt_env p) clspec))); [apply Hc | reflexivity].
  - (* MConcatSetT *)
    change (match_loadable (MConcatSetT celems neg nm) p)
      with (fields_loadable (map fst celems) p).
    unfold fields_loadable. rewrite forallb_map.
    destruct (forallb (fun fe => field_loadable (fst fe) p) celems) eqn:Hf; cbn [andb].
    2:{ rewrite <- !app_assoc. cbn [app]. rewrite run_load_fields_t_writes_break by exact Hf.
        reflexivity. }
    rewrite <- !app_assoc. cbn [app].
    edestruct (run_load_fields_t_writes celems 0 rf
                (ILookup (map snd (alloc_regs 0 (map fst celems))) nm neg :: X) p Hf)
      as [rf' [Hrb [_ Hrun]]].
    rewrite Hrun. cbn [run_rule_writes]. rewrite Hrb.
    destruct (xorb neg (concat_set_mem
               (map (fun fe => apply_transforms (snd fe) (field_value (fst fe) p)) celems)
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

(** ---- "straight-line" instruction lists: no meta/ct write, no break, no
    terminal.  [run_rule_writes] threads through such a prefix to the tail — this
    discharges EVERY non-meta/ct statement (mangle/dup/counter/log/dynset/exthdr/
    objref/ctsetdir), so the mutation theorem no longer has to exclude them. ---- *)
Definition straight_instr (i : instr) : bool :=
  match i with
  | ICmp _ _ _ | IRange _ _ _ _ | ILookup _ _ _ | IVmap _ _
  | ILimit _ | IQuota _ | IConnlimit _
  | INat _ _ _ _ _ _ _ | ITproxy _ _ _ | IFwd _ _ _ | IQueueSreg _ _ _
  | IReject _ _ | IQueue _ _ _ _ | IImmediate _
  | IMetaSet _ _ | ICtSet _ _ | INotrack
  | ISynproxy _ _   (* can BREAK (non-TCP) or STOP (SYN/ACK) the rule *)
  | IDynset _ _ _ None _ | IDynset _ _ _ (Some _) true => false
  | _ => true
  end.
Definition straight (is : list instr) : bool := forallb straight_instr is.

Lemma straight_imp_nw : forall is, straight is = true -> no_writes is = true.
Proof.
  unfold straight, no_writes. intros is. rewrite !forallb_forall. intros H i Hin.
  specialize (H i Hin). destruct i; cbn in *; try congruence.
  (* IDynset: both predicates branch on the data-reg option and field/imm flag *)
  match goal with [ d : option reg, b : bool |- _ ] =>
    destruct d; [destruct b |]; cbn in *; congruence end.
Qed.
Lemma str_cons : forall i l, straight (i :: l) = straight_instr i && straight l.
Proof. reflexivity. Qed.
Lemma str_app : forall a b, straight (a ++ b) = straight a && straight b.
Proof. intros. apply forallb_app. Qed.
Lemma str_map : forall {A} (g : A -> instr) (l : list A),
  (forall x, straight_instr (g x) = true) -> straight (map g l) = true.
Proof.
  intros A g l Hg. induction l as [| x xs IH]; [reflexivity|]. cbn [map]. rewrite str_cons, Hg, IH. reflexivity.
Qed.
Lemma str_flat_map : forall {A} (g : A -> list instr) (l : list A),
  (forall x, straight (g x) = true) -> straight (flat_map g l) = true.
Proof.
  intros A g l Hg. induction l as [| x xs IH]; [reflexivity|]. cbn [flat_map]. rewrite str_app, Hg, IH. reflexivity.
Qed.
Lemma str_load_fields : forall pairs, straight (load_fields pairs) = true.
Proof.
  intros. unfold load_fields. apply str_map. intros [f r]. cbn [fst snd].
  unfold compile_load; destruct (field_load f); reflexivity.
Qed.
Lemma str_imms : forall (imms : list (reg * data)),
  straight (map (fun rv => IImmediateData (fst rv) (snd rv)) imms) = true.
Proof. intros. apply str_map. reflexivity. Qed.
Lemma str_transforms : forall ts, straight (compile_transforms ts) = true.
Proof.
  induction ts as [| t ts IH]; [reflexivity|].
  cbn [compile_transforms]. rewrite str_cons, IH, Bool.andb_true_r. destruct t; reflexivity.
Qed.
Lemma str_transforms_at : forall r ts, straight (compile_transforms_at r ts) = true.
Proof.
  intros r ts. unfold compile_transforms_at. apply str_map. intros t. destruct t; reflexivity.
Qed.
Lemma str_load_fields_t : forall elems slot, straight (load_fields_t slot elems) = true.
Proof.
  induction elems as [| [f ts] rest IH]; intros slot; [reflexivity|].
  cbn [load_fields_t]. rewrite str_app, str_cons, str_transforms_at, IH.
  unfold compile_load; destruct (field_load f); reflexivity.
Qed.
Lemma str_vsrc : forall vs, straight (compile_vsrc vs) = true.
Proof.
  destruct vs as [v | f ts | fields ts nm | fields len seed modulus offset
                 | osrcs ofinal | elems nm | fields len seed modulus offset nm];
    cbn [compile_vsrc].
  - reflexivity.
  - rewrite str_cons, str_transforms. unfold compile_load; destruct (field_load f); reflexivity.
  - rewrite str_app, str_load_fields, str_app, str_transforms. reflexivity.
  - rewrite str_app, str_load_fields. reflexivity.
  - destruct osrcs as [| [f0 ts0] rest]; [reflexivity|].
    rewrite !str_app, str_cons.
    rewrite (str_flat_map _ rest).
    2: { intros [f ts0']. cbn [fst snd]. rewrite str_cons, str_app, str_transforms_at.
         unfold compile_load; destruct (field_load f); reflexivity. }
    rewrite !str_transforms_at. unfold compile_load; destruct (field_load f0); reflexivity.
  - rewrite str_app, str_load_fields_t. reflexivity.
  - rewrite str_app, str_load_fields, str_app. reflexivity.
Qed.

(** Whether every payload load in an instruction list SUCCEEDS on [p] (the only
    instruction that can break a straight prefix is a failing [IPayloadLoad]). *)
Definition loads_ok_instr (i : instr) (p : packet) : bool :=
  match i with IPayloadLoad b o l _ => read_payload_ok b o l p | _ => true end.
Definition loads_ok (is : list instr) (p : packet) : bool :=
  forallb (fun i => loads_ok_instr i p) is.

Lemma lo_cons : forall i l p, loads_ok (i :: l) p = loads_ok_instr i p && loads_ok l p.
Proof. reflexivity. Qed.
Lemma lo_app : forall a b p, loads_ok (a ++ b) p = loads_ok a p && loads_ok b p.
Proof. intros a b p. apply forallb_app. Qed.
Lemma lo_compile_load : forall f r p, loads_ok_instr (compile_load (field_load f) r) p = field_loadable f p.
Proof.
  intros f r p. unfold field_loadable, load_ok, compile_load.
  destruct (field_load f); reflexivity.
Qed.
Lemma lo_map_imms : forall (imms : list (reg * data)) p,
  loads_ok (map (fun rv => IImmediateData (fst rv) (snd rv)) imms) p = true.
Proof. intros. induction imms as [|[r v] xs IH]; [reflexivity|]. cbn [map fst snd]. rewrite lo_cons; cbn [loads_ok_instr]. exact IH. Qed.
Lemma lo_transforms : forall ts p, loads_ok (compile_transforms ts) p = true.
Proof.
  induction ts as [|t ts IH]; intro p; [reflexivity|].
  cbn [compile_transforms]. rewrite lo_cons, IH, Bool.andb_true_r. destruct t; reflexivity.
Qed.
Lemma lo_transforms_at : forall r ts p, loads_ok (compile_transforms_at r ts) p = true.
Proof.
  intros r ts p. unfold compile_transforms_at.
  induction ts as [|t ts IH]; [reflexivity|]. cbn [map]. rewrite lo_cons, IH, Bool.andb_true_r. destruct t; reflexivity.
Qed.
Lemma lo_load_fields : forall pairs p,
  loads_ok (load_fields pairs) p = forallb (fun fr => field_loadable (fst fr) p) pairs.
Proof.
  intros pairs p. unfold load_fields.
  induction pairs as [|[f r] xs IH]; [reflexivity|]. cbn [map forallb fst].
  rewrite lo_cons, lo_compile_load, IH. reflexivity.
Qed.
Lemma lo_load_fields_t : forall elems slot p,
  loads_ok (load_fields_t slot elems) p = forallb (fun fe => field_loadable (fst fe) p) elems.
Proof.
  intros elems slot p. revert slot.
  induction elems as [|[f ts] rest IH]; intros slot; [reflexivity|].
  cbn [load_fields_t forallb fst]. rewrite lo_app, lo_cons, lo_compile_load, lo_transforms_at, IH.
  rewrite Bool.andb_true_r. reflexivity.
Qed.
Lemma lo_or_flat : forall orest p,
  loads_ok (flat_map (fun e =>
    compile_load (field_load (fst e)) 2 :: compile_transforms_at 2 (snd e)
    ++ [IBitwiseOr 1 1 2]) orest) p
  = forallb (fun e => field_loadable (fst e) p) orest.
Proof.
  induction orest as [|[f1 ts1] os IH]; intro p; [reflexivity|].
  cbn [flat_map]. rewrite lo_app, lo_cons, lo_compile_load, lo_app, lo_transforms_at.
  replace (loads_ok [IBitwiseOr 1 1 2] p) with true by reflexivity.
  rewrite !Bool.andb_true_l, !Bool.andb_true_r, IH. cbn [forallb fst]. reflexivity.
Qed.

Lemma lo_vsrc : forall vs p, loads_ok (compile_vsrc vs) p = vsrc_loadable vs p.
Proof.
  destruct vs as [v | f ts | fields ts nm | fields len seed modulus offset
                 | osrcs ofinal | elems nm | fields len seed modulus offset nm];
    intro p; cbn [compile_vsrc vsrc_loadable].
  - reflexivity.
  - rewrite lo_cons, lo_compile_load, lo_transforms, Bool.andb_true_r. reflexivity.
  - rewrite lo_app, lo_load_fields, lo_app, lo_transforms, Bool.andb_true_r, forallb_alloc_regs.
    cbn [loads_ok loads_ok_instr forallb]; rewrite ?Bool.andb_true_r; reflexivity.
  - rewrite lo_app, lo_load_fields, forallb_alloc_regs.
    cbn [loads_ok loads_ok_instr forallb]; rewrite ?Bool.andb_true_r; reflexivity.
  - destruct osrcs as [| [f0 ts0] orest].
    + reflexivity.
    + unfold fields_loadable. rewrite forallb_map. cbn [map forallb fst].
      rewrite !lo_app, lo_cons, lo_compile_load, lo_transforms_at.
      rewrite (lo_transforms_at 1 ofinal).
      rewrite Bool.andb_true_r, lo_or_flat, Bool.andb_true_r. reflexivity.
  - rewrite lo_app, lo_load_fields_t.
    cbn [loads_ok loads_ok_instr forallb]; rewrite ?Bool.andb_true_r.
    unfold fields_loadable. rewrite forallb_map. reflexivity.
  - rewrite lo_app, lo_load_fields, forallb_alloc_regs, lo_app.
    cbn [loads_ok loads_ok_instr forallb]; rewrite ?Bool.andb_true_r; reflexivity.
Qed.
Lemma lo_compile_stmt : forall s p, stmt_loadable s p = true -> loads_ok (compile_stmt s) p = true.
Proof.
  destruct s; intro p; cbn [compile_stmt stmt_loadable]; intro Hl.
  - reflexivity.                                          (* SCounter *)
  - reflexivity.                                          (* SNotrack *)
  - reflexivity.                                          (* SLog *)
  - rewrite lo_app, lo_vsrc, Hl. reflexivity.             (* SMangle *)
  - rewrite lo_app, lo_vsrc, Hl. reflexivity.             (* SMetaSet *)
  - rewrite lo_app, lo_vsrc, Hl. reflexivity.             (* SCtSet *)
  - rewrite lo_app, lo_vsrc, Hl. reflexivity.             (* SCtSetDir *)
  - reflexivity.                                          (* SObjref *)
  - reflexivity.                                          (* SSynproxy *)
  - reflexivity.                                          (* SLast *)
  - (* SDynset *) rewrite lo_app, lo_load_fields, forallb_alloc_regs.
    cbn [loads_ok loads_ok_instr forallb]; rewrite ?Bool.andb_true_r.
    unfold fields_loadable in Hl. rewrite Hl. reflexivity.
  - reflexivity.                                          (* SExthdrReset *)
  - rewrite lo_app, lo_map_imms. reflexivity.             (* SDup *)
  - (* SObjrefMap *) rewrite lo_app, lo_load_fields, forallb_alloc_regs.
    cbn [loads_ok loads_ok_instr forallb]; rewrite ?Bool.andb_true_r.
    unfold fields_loadable in Hl. rewrite Hl. reflexivity.
  - (* SDynsetImm *) rewrite lo_app, lo_load_fields, forallb_alloc_regs, lo_app, lo_map_imms.
    rewrite ?Bool.andb_true_r. cbn [loads_ok loads_ok_instr forallb]; rewrite ?Bool.andb_true_r.
    unfold fields_loadable in Hl. rewrite Hl. reflexivity.
  - rewrite lo_app, lo_vsrc, Hl. reflexivity.             (* SExthdrWrite *)
  - rewrite lo_app, lo_vsrc, Hl, lo_app, lo_map_imms. reflexivity.  (* SDupSrc *)
Qed.

Lemma run_rule_writes_straight : forall pre rf rest p,
  straight pre = true ->
  loads_ok pre p = true ->
  exists rf', run_rule_writes rf (pre ++ rest) p = run_rule_writes rf' rest p.
Proof.
  induction pre as [| i pre IH]; intros rf rest p Hs Hlo; [exists rf; reflexivity|].
  cbn [straight forallb] in Hs. apply Bool.andb_true_iff in Hs. destruct Hs as [Hi Hpre].
  cbn [loads_ok forallb] in Hlo. apply Bool.andb_true_iff in Hlo. destruct Hlo as [Hl Hlop].
  destruct i; cbn [straight_instr] in Hi; try discriminate Hi;
    try (cbn [app run_rule_writes]; apply IH; [exact Hpre | exact Hlop]).
  (* Two remaining goals: IDynset (branches on datareg/fdata) and IPayloadLoad
     (succeeds by [Hl], threading to the rest). *)
  all: cbn [loads_ok_instr] in Hl.
  - (* IDynset *) match goal with [ d : option reg, b : bool |- _ ] =>
      destruct d as [dreg |]; [destruct b |]; cbn [straight_instr] in Hi;
      cbn [app run_rule_writes];
      solve [ apply IH; [exact Hpre | exact Hlop] | discriminate Hi ]
    end.
  - (* IPayloadLoad *) cbn [app run_rule_writes].
    match goal with |- context [if ?c then _ else _] => destruct c; [| discriminate Hl] end.
    apply IH; [exact Hpre | exact Hlop].
Qed.

(** A "mutating" statement: a meta/ct set (mutates a packet field) OR a dynset
    (mutates the named-set state).  These are the statements the mutation
    threading handles specially; every other statement is meta/ct- and env-neutral. *)
Definition is_mut_stmt (s : stmt) : bool :=
  match s with SMetaSet _ _ | SCtSet _ _ | SDynset _ _ _ _ | SNotrack => true | _ => false end.
(** A SYN-proxy statement: write-neutral but NOT straight — it can BREAK (non-TCP)
    or STOP (SYN/ACK) the rule, so it is excluded from the straight-line scaffolding
    and handled explicitly (cf. [run_compile_body_writes]). *)
Definition is_synproxy_stmt (s : stmt) : bool :=
  match s with SSynproxy _ _ => true | _ => false end.
(** A `notrack` statement: write-neutral but NOT straight in the [run_compile_body]
    sense — it threads [set_untracked] into the running packet, so it is handled
    explicitly (like synproxy) rather than by the straight-line scaffolding. *)
Definition is_notrack_stmt (s : stmt) : bool :=
  match s with SNotrack => true | _ => false end.
Lemma straight_compile_stmt : forall s,
  is_mut_stmt s = false -> is_synproxy_stmt s = false -> straight (compile_stmt s) = true.
Proof.
  destruct s; intros H Hsp; try discriminate H; try discriminate Hsp; cbn [compile_stmt].
  - reflexivity.                                          (* SCounter *)
  - reflexivity.                                          (* SLog *)
  - rewrite str_app, str_vsrc; reflexivity.               (* SMangle *)
  - rewrite str_app, str_vsrc; reflexivity.               (* SCtSetDir *)
  - reflexivity.                                          (* SObjref *)
  - reflexivity.                                          (* SLast *)
  - reflexivity.                                          (* SExthdrReset *)
  - rewrite str_app, str_imms; reflexivity.               (* SDup *)
  - rewrite str_app, str_load_fields; reflexivity.        (* SObjrefMap *)
  - rewrite str_app, str_load_fields, str_app, str_imms; reflexivity.  (* SDynsetImm *)
  - rewrite str_app, str_vsrc; reflexivity.               (* SExthdrWrite *)
  - rewrite str_app, str_vsrc, str_app, str_imms; reflexivity.         (* SDupSrc *)
Qed.
Lemma run_stmt_writes_neutral : forall s rf rest p,
  is_mut_stmt s = false -> is_synproxy_stmt s = false ->
  stmt_loadable s p = true ->
  exists rf', run_rule_writes rf (compile_stmt s ++ rest) p = run_rule_writes rf' rest p.
Proof.
  intros s rf rest p Hm Hsp Hl. apply run_rule_writes_straight.
  - apply straight_compile_stmt; [exact Hm | exact Hsp].
  - apply lo_compile_stmt; exact Hl.
Qed.
Lemma body_writes_nonset : forall s body p,
  is_mut_stmt s = false -> is_synproxy_stmt s = false -> stmt_loadable s p = true ->
  body_writes (BStmt s :: body) p = body_writes body p.
Proof.
  intros s body p H Hsp Hl. destruct s; cbn [is_mut_stmt is_synproxy_stmt] in H, Hsp;
    try discriminate H; try discriminate Hsp;
    cbn [body_writes]; rewrite Hl; reflexivity.
Qed.
(** [no_writes] of a single compiled statement that is not a meta/ct set. *)
Lemma nw_compile_stmt_nonmut : forall s,
  is_mut_stmt s = false -> no_writes (compile_stmt s) = true.
Proof.
  intros s Hm. destruct (is_synproxy_stmt s) eqn:Hsp.
  - (* SSynproxy => [ISynproxy m w], which is not a write *)
    destruct s; cbn [is_synproxy_stmt] in Hsp; try discriminate Hsp.
    cbn [compile_stmt no_writes forallb writes_instr negb]. reflexivity.
  - apply straight_imp_nw, straight_compile_stmt; [exact Hm | exact Hsp].
Qed.
(** A statement list with no meta/ct set compiles to a no-write tail. *)
Lemma nw_flat_compile_stmt : forall ss,
  forallb (fun s => negb (is_mut_stmt s)) ss = true ->
  no_writes (flat_map compile_stmt ss) = true.
Proof.
  induction ss as [| s ss IH]; intro H; [reflexivity|].
  cbn [flat_map]. cbn [forallb] in H. apply Bool.andb_true_iff in H. destruct H as [Hs Hss].
  rewrite nw_app. apply Bool.andb_true_iff. split.
  - apply nw_compile_stmt_nonmut. destruct (is_mut_stmt s); [discriminate Hs | reflexivity].
  - apply IH; exact Hss.
Qed.

(** ---- dynset (dynamic-set) write scaffolding ---- *)
(** A field allocation has exactly one register per field. *)
Lemma alloc_regs_length : forall fields slot, length (alloc_regs slot fields) = length fields.
Proof. induction fields as [| f fs IH]; intros slot; cbn [alloc_regs length]; [reflexivity | f_equal; apply IH]. Qed.

(** A pure-set dynset (empty data fields) compiles its data register to [None]:
    the key registers exhaust the allocation, so [skipn (length keyfs)] is empty. *)
Lemma skipn_map_snd_alloc_nil : forall keyfs,
  skipn (length keyfs) (map snd (alloc_regs 0 keyfs)) = [].
Proof.
  intros. apply skipn_all2. rewrite map_length, alloc_regs_length. apply Nat.le_refl.
Qed.

Lemma compile_dynset_set : forall op name keyfs,
  compile_stmt (SDynset op name keyfs []) =
  load_fields (alloc_regs 0 keyfs) ++ [IDynset op name (map snd (alloc_regs 0 keyfs)) None false].
Proof.
  intros. cbn [compile_stmt]. rewrite app_nil_r, skipn_map_snd_alloc_nil. reflexivity.
Qed.

(** Reading back the concatenated key the loads leave in the key registers: it is
    exactly the concatenation of the field values (distinct registers, cf. the
    [MConcatSet] proof). *)
Lemma write_fields_concat_key : forall keyfs rf p,
  List.concat (map (write_fields rf (alloc_regs 0 keyfs) p) (map snd (alloc_regs 0 keyfs)))
  = List.concat (map (fun f => field_value f p) keyfs).
Proof.
  intros. rewrite map_write_fields by apply alloc_regs_nodup.
  rewrite map_fst_field, alloc_regs_fst. reflexivity.
Qed.

(** The mutation effect of a compiled pure-set dynset: after loading the key, the
    [IDynset _ None] inserts/removes the concatenated key in the named set — i.e.
    threads the packet whose env has [name] updated.  This is the dynamic-set
    feedback loop on the VM side. *)
Lemma run_dynset_set_writes : forall op name keyfs rf rest p,
  fields_loadable keyfs p = true ->
  run_rule_writes rf (compile_stmt (SDynset op name keyfs []) ++ rest) p
  = run_rule_writes (write_fields rf (alloc_regs 0 keyfs) p) rest
      (set_env_dynset p op name (List.concat (map (fun f => field_value f p) keyfs))).
Proof.
  intros op name keyfs rf rest p Hl. rewrite compile_dynset_set, <- app_assoc.
  rewrite run_load_fields_writes by (rewrite forallb_alloc_regs; exact Hl).
  cbn [app run_rule_writes]. rewrite write_fields_concat_key. reflexivity.
Qed.

(** ---- map-dynset (key -> field data) write scaffolding ---- *)
(** Total register slots a field list occupies (one allocation per field). *)
Fixpoint slots_of (fields : list field) : nat :=
  match fields with [] => 0 | f :: r => field_slots f + slots_of r end.

(** A field allocation splits over [++]: the second list starts after the first's
    slots.  This isolates the KEY registers ([alloc_regs 0 keyfs]) as a prefix of
    the full key+data allocation, so they read back as the key field values. *)
Lemma alloc_regs_app : forall a b slot,
  alloc_regs slot (a ++ b) = alloc_regs slot a ++ alloc_regs (slot + slots_of a) b.
Proof.
  induction a as [| f a IH]; intros b slot; cbn [alloc_regs app slots_of].
  - rewrite Nat.add_0_r. reflexivity.
  - rewrite IH. replace (slot + field_slots f + slots_of a)
      with (slot + (field_slots f + slots_of a)) by lia. reflexivity.
Qed.

Lemma write_fields_app : forall A B rf p,
  write_fields rf (A ++ B) p = write_fields (write_fields rf A p) B p.
Proof. induction A as [| [f r] A IH]; intros; cbn [write_fields app]; [reflexivity | apply IH]. Qed.

Lemma nodup_app_disjoint : forall {A} (l l' : list A) x,
  NoDup (l ++ l') -> In x l -> ~ In x l'.
Proof.
  induction l as [| a l IH]; intros l' x Hnd Hin; [inversion Hin|].
  cbn [app] in Hnd. inversion Hnd as [| ? ? Hni Hnd' ]; subst.
  destruct Hin as [-> | Hin].
  - intro Hin'. apply Hni, in_or_app. right. exact Hin'.
  - apply (IH l' x Hnd' Hin).
Qed.

(** Reading the LEFT (key) registers of a key++data allocation: the data writes
    never clobber a key register (distinct slots), so they read back as the key
    fields' values. *)
Lemma map_write_fields_app_l : forall A B rf p,
  NoDup (map snd (A ++ B)) ->
  map (write_fields rf (A ++ B) p) (map snd A) = map (fun fr => field_value (fst fr) p) A.
Proof.
  intros A B rf p Hnd. rewrite map_app in Hnd.
  rewrite <- (map_write_fields A rf p (NoDup_app_remove_r _ _ Hnd)).
  apply map_ext_in. intros r Hr. rewrite write_fields_app.
  apply write_fields_other, (nodup_app_disjoint _ _ r Hnd Hr).
Qed.

Lemma write_fields_concat_key_app : forall keyfs extra rf p,
  List.concat (map (write_fields rf (alloc_regs 0 (keyfs ++ extra)) p) (map snd (alloc_regs 0 keyfs)))
  = List.concat (map (fun f => field_value f p) keyfs).
Proof.
  intros. rewrite alloc_regs_app.
  rewrite map_write_fields_app_l by (rewrite <- alloc_regs_app; apply alloc_regs_nodup).
  rewrite map_fst_field, alloc_regs_fst. reflexivity.
Qed.

(** The first data register of a key++(d::ds) allocation reads back as [d]'s value. *)
Lemma write_fields_data_head : forall keyfs d ds rf p,
  write_fields rf (alloc_regs 0 (keyfs ++ d :: ds)) p (reg_of_slot (slots_of keyfs)) = field_value d p.
Proof.
  intros. rewrite alloc_regs_app, write_fields_app, Nat.add_0_l. apply write_fields_head.
Qed.

(** The data register a map dynset compiles to is the first slot past the key. *)
Lemma skipn_map_snd_alloc_app : forall keyfs extra,
  skipn (length keyfs) (map snd (alloc_regs 0 (keyfs ++ extra)))
  = map snd (alloc_regs (slots_of keyfs) extra).
Proof.
  intros. rewrite alloc_regs_app, map_app, Nat.add_0_l, skipn_app.
  rewrite skipn_all2 by (rewrite map_length, alloc_regs_length; apply Nat.le_refl).
  rewrite map_length, alloc_regs_length, Nat.sub_diag. reflexivity.
Qed.

Lemma compile_dynset_map : forall op name keyfs d ds,
  compile_stmt (SDynset op name keyfs (d :: ds)) =
  load_fields (alloc_regs 0 (keyfs ++ d :: ds)) ++
  [IDynset op name (map snd (alloc_regs 0 keyfs)) (Some (reg_of_slot (slots_of keyfs))) true].
Proof.
  intros. cbn [compile_stmt]. rewrite skipn_map_snd_alloc_app. cbn [alloc_regs map]. reflexivity.
Qed.

(** The mutation effect of a compiled field-data map dynset: after loading the key
    and the data field, [IDynset _ (Some dreg) true] learns key -> (data field) in
    the named map — the map analogue of the dynamic-set feedback loop. *)
Lemma run_dynset_map_writes : forall op name keyfs d ds rf rest p,
  fields_loadable (keyfs ++ d :: ds) p = true ->
  run_rule_writes rf (compile_stmt (SDynset op name keyfs (d :: ds)) ++ rest) p
  = run_rule_writes (write_fields rf (alloc_regs 0 (keyfs ++ d :: ds)) p) rest
      (set_env_dynset_map p op name
         (List.concat (map (fun f => field_value f p) keyfs)) (field_value d p)).
Proof.
  intros op name keyfs d ds rf rest p Hl. rewrite compile_dynset_map, <- app_assoc.
  rewrite run_load_fields_writes by (rewrite forallb_alloc_regs; exact Hl).
  cbn [app run_rule_writes].
  rewrite write_fields_concat_key_app, write_fields_data_head. reflexivity.
Qed.

(** A compiled statement whose operand load BREAKs returns the packet unchanged
    under [run_rule_writes] (the VM stops at the failing payload load). *)
Lemma run_stmt_writes_break : forall s rf rest p,
  stmt_loadable s p = false ->
  run_rule_writes rf (compile_stmt s ++ rest) p = p.
Proof.
  destruct s; intros rf rest p Hl; cbn [stmt_loadable] in Hl; try discriminate Hl;
    cbn [compile_stmt]; rewrite <- ?app_assoc.
  - rewrite run_vsrc_writes_break by exact Hl; reflexivity.   (* SMangle *)
  - rewrite run_vsrc_writes_break by exact Hl; reflexivity.   (* SMetaSet *)
  - rewrite run_vsrc_writes_break by exact Hl; reflexivity.   (* SCtSet *)
  - rewrite run_vsrc_writes_break by exact Hl; reflexivity.   (* SCtSetDir *)
  - (* SSynproxy: stmt_loadable = synproxy_loadable = false (non-TCP) => break *)
    cbn [app run_rule_writes]. unfold synproxy_loadable in *. rewrite Hl. reflexivity.
  - rewrite run_load_fields_writes_break; [reflexivity|]. rewrite forallb_alloc_regs; exact Hl.  (* SDynset *)
  - rewrite run_load_fields_writes_break; [reflexivity|]. rewrite forallb_alloc_regs; exact Hl.  (* SObjrefMap *)
  - rewrite run_load_fields_writes_break; [reflexivity|]. rewrite forallb_alloc_regs; exact Hl.  (* SDynsetImm *)
  - rewrite run_vsrc_writes_break by exact Hl; reflexivity.   (* SExthdrWrite *)
  - rewrite run_vsrc_writes_break by exact Hl; reflexivity.   (* SDupSrc *)
Qed.

(** The body, compiled and run under [run_rule_writes] before a packet-neutral
    tail, realises exactly [body_writes] — the declarative meta/ct effect.  Holds
    UNCONDITIONALLY: a broken load makes BOTH sides stop with the packet mutated so
    far (the break-aware [body_writes] mirrors [run_rule_writes] on the body). *)
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
    + (* BStmt s.  SMetaSet/SCtSet write meta/ct; every OTHER statement is a
         "straight-line", meta/ct-neutral prefix threaded through unchanged. *)
      destruct (stmt_loadable s p) eqn:Hsl.
      2:{ (* operand load breaks: both sides stop with the packet unchanged *)
          rewrite <- app_assoc, run_stmt_writes_break by exact Hsl.
          destruct s; cbn [is_mut_stmt body_writes];
            try (rewrite Hsl; reflexivity);
            (* mutating-stmt + synproxy cases: body_writes guards on the same loadability *)
            cbn [stmt_loadable] in Hsl;
            (* SNotrack is always loadable, so this break case is vacuous *)
            try discriminate Hsl.
          - rewrite Hsl; reflexivity.                           (* SMetaSet *)
          - rewrite Hsl; reflexivity.                           (* SCtSet *)
          - rewrite Hsl; reflexivity.                           (* SSynproxy *)
          - destruct dataf as [| d ds].                         (* SDynset *)
            + unfold fields_loadable in Hsl; rewrite app_nil_r in Hsl;
                fold (fields_loadable keyfs p) in Hsl; rewrite Hsl; reflexivity.
            + rewrite Hsl; reflexivity. }
      destruct (is_mut_stmt s) eqn:Es.
      * (* the genuine mutating statements: meta/ct set (packet) or dynset (env) *)
        destruct s; cbn [is_mut_stmt] in Es; try discriminate Es;
          cbn [stmt_loadable] in Hsl.
        -- (* SNotrack: compiles to [INotrack], both sides apply [set_untracked] *)
           cbn [compile_stmt] in Hit |- *. cbn [app run_rule_writes].
           cbn [body_writes]. apply IH; [exact Htail | exact Hsb'].
        -- (* SMetaSet k vs *)
           cbn [compile_stmt] in Hit |- *; rewrite <- !app_assoc.
           edestruct (writes_vsrc_simple vs rf
                       ([IMetaSet k 1] ++ (flat_map compile_body_item body ++ tail)) p Hit Hsl)
             as [rf' [Hr Hv]].
           rewrite Hr. cbn [app run_rule_writes]. rewrite Hv.
           cbn [body_writes]. rewrite Hsl. apply IH; [exact Htail | exact Hsb'].
        -- (* SCtSet k vs *)
           cbn [compile_stmt] in Hit |- *; rewrite <- !app_assoc.
           edestruct (writes_vsrc_simple vs rf
                       ([ICtSet k 1] ++ (flat_map compile_body_item body ++ tail)) p Hit Hsl)
             as [rf' [Hr Hv]].
           rewrite Hr. cbn [app run_rule_writes]. rewrite Hv.
           cbn [body_writes]. rewrite Hsl. apply IH; [exact Htail | exact Hsb'].
        -- (* SDynset op name keyfs dataf *)
           rewrite <- !app_assoc. destruct dataf as [| d ds].
           ++ unfold fields_loadable in Hsl. rewrite app_nil_r in Hsl.
              fold (fields_loadable keyfs p) in Hsl.
              rewrite run_dynset_set_writes by exact Hsl. cbn [body_writes].
              rewrite Hsl. apply IH; [exact Htail | exact Hsb'].
           ++ rewrite run_dynset_map_writes by exact Hsl. cbn [body_writes].
              rewrite Hsl. apply IH; [exact Htail | exact Hsb'].
      * destruct (is_synproxy_stmt s) eqn:Esp.
        -- (* SSynproxy: loadable (TCP) here.  If it STOPS, both sides are [p];
              otherwise it threads (verdict-neutral for writes). *)
           destruct s; cbn [is_synproxy_stmt] in Esp; try discriminate Esp.
           cbn [compile_stmt] in Hit |- *; rewrite <- app_assoc.
           cbn [stmt_loadable] in Hsl. cbn [app run_rule_writes body_writes].
           rewrite Hsl. destruct (synproxy_stops p) eqn:Hstop.
           ++ reflexivity.
           ++ apply IH; [exact Htail | exact Hsb'].
        -- (* any other non-mutating statement: threaded straight, body_writes is the identity *)
           edestruct (run_stmt_writes_neutral s rf
                        (flat_map compile_body_item body ++ tail) p Es Esp Hsl) as [rf' Hr].
           rewrite <- app_assoc, Hr, (body_writes_nonset s body p Es Esp Hsl).
           apply (IH tail Htail Hsb' rf' p).
Qed.

Lemma run_stmt_exists : forall s rf rest p,
  is_notrack_stmt s = false ->
  is_synproxy_stmt s = false ->
  stmt_loadable s p = true ->
  exists rf', run_rule rf (compile_stmt s ++ rest) p = run_rule rf' rest p.
Proof.
  destruct s; intros rf rest p Hnt Hsp Hl;
    cbn [stmt_loadable is_synproxy_stmt is_notrack_stmt] in Hnt, Hsp, Hl;
    try discriminate Hsp; try discriminate Hnt; try (exists rf; reflexivity).
  - (* SMangle *) edestruct (run_vsrc_exists vs rf
      (IPayloadWrite 1 b off len ctype coff cflags :: rest) p Hl) as [rf' Hr].
    exists rf'. cbn [compile_stmt]. rewrite <- app_assoc. cbn [app].
    rewrite Hr. reflexivity.
  - (* SMetaSet *) edestruct (run_vsrc_exists vs rf (IMetaSet k 1 :: rest) p Hl) as [rf' Hr].
    exists rf'. cbn [compile_stmt]. rewrite <- app_assoc. cbn [app].
    rewrite Hr. reflexivity.
  - (* SCtSet *) edestruct (run_vsrc_exists vs rf (ICtSet k 1 :: rest) p Hl) as [rf' Hr].
    exists rf'. cbn [compile_stmt]. rewrite <- app_assoc. cbn [app].
    rewrite Hr. reflexivity.
  - (* SCtSetDir *) edestruct (run_vsrc_exists vs rf (ICtSetDir key dir 1 :: rest) p Hl) as [rf' Hr].
    exists rf'. cbn [compile_stmt]. rewrite <- app_assoc. cbn [app].
    rewrite Hr. reflexivity.
  - (* SDynset: load the concat key fields, then the verdict-neutral IDynset *)
    cbn [compile_stmt]. rewrite <- app_assoc.
    rewrite run_load_fields by (rewrite forallb_alloc_regs; exact Hl).
    cbn [app run_rule]. eexists; reflexivity.
  - (* SDup: operand immediates, then the verdict-neutral IDup *)
    edestruct (run_imms_through imms rf (IDup devreg addrreg :: rest) p) as [rf' Hr].
    exists rf'. cbn [compile_stmt]. rewrite <- app_assoc. cbn [app].
    rewrite Hr. cbn [run_rule]. reflexivity.
  - (* SObjrefMap: load the key fields, then the verdict-neutral IObjrefMap *)
    cbn [compile_stmt]. rewrite <- app_assoc.
    rewrite run_load_fields by (rewrite forallb_alloc_regs; exact Hl).
    cbn [app run_rule]. eexists; reflexivity.
  - (* SDynsetImm: load the key, then immediate data, then verdict-neutral IDynset *)
    cbn [compile_stmt]. rewrite <- app_assoc.
    rewrite run_load_fields by (rewrite forallb_alloc_regs; exact Hl).
    rewrite <- app_assoc.
    edestruct run_imms_through as [rf' Hr]. rewrite Hr.
    cbn [run_rule]. eexists; reflexivity.
  - (* SExthdrWrite: value source, then the verdict-neutral IExthdrWrite *)
    edestruct (run_vsrc_exists vs rf (IExthdrWrite proto htype off len 1 :: rest) p Hl) as [rf' Hr].
    exists rf'. cbn [compile_stmt]. rewrite <- app_assoc. cbn [app].
    rewrite Hr. reflexivity.
  - (* SDupSrc: value source, then operand immediates, then verdict-neutral IDup *)
    cbn [compile_stmt]. rewrite <- app_assoc.
    edestruct (run_vsrc_exists src rf) as [rf1 Hr1]; [exact Hl|]. rewrite Hr1.
    rewrite <- app_assoc.
    edestruct run_imms_through as [rf2 Hr2]. rewrite Hr2.
    cbn [run_rule]. eexists; reflexivity.
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
  vsrc_loadable vs p = true ->
  run_rule rf (compile_vsrc vs ++ INat k fam amin amax pmin pmax fl :: tail) p = Some Accept.
Proof.
  intros vs tail rf k fam amin amax pmin pmax fl p Hl.
  edestruct (run_vsrc_exists vs rf
                      (INat k fam amin amax pmin pmax fl :: tail) p Hl) as [rf' Hr].
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
  vsrc_loadable vs p = true ->
  run_rule rf (compile_vsrc vs ++ IFwd dev addr nfp :: tail) p = Some Accept.
Proof.
  intros vs tail rf dev addr nfp p Hl.
  edestruct (run_vsrc_exists vs rf (IFwd dev addr nfp :: tail) p Hl) as [rf' Hr].
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
  vsrc_loadable vs p = true ->
  run_rule rf (compile_vsrc vs ++ IQueueSreg sreg b f :: tail) p = Some Accept.
Proof.
  intros vs tail rf sreg b f p Hl.
  edestruct (run_vsrc_exists vs rf (IQueueSreg sreg b f :: tail) p Hl) as [rf' Hr].
  rewrite Hr. cbn [run_rule]. reflexivity.
Qed.

(** A map-sourced NAT operand: load the key (+ transforms), look it up in the map
    (into reg 1), then the terminal [INat] accepts — all verdict-neutral until
    [INat]. *)
Lemma run_map_nat : forall fields ts name tail rf k fam amin amax pmin pmax fl p,
  fields_loadable fields p = true ->
  run_rule rf
    ((load_fields (alloc_regs 0 fields) ++ compile_transforms ts
        ++ [ILookupVal (map snd (alloc_regs 0 fields)) name 1])
     ++ INat k fam amin amax pmin pmax fl :: tail) p = Some Accept.
Proof.
  intros fields ts name tail rf k fam amin amax pmin pmax fl p Hl.
  rewrite <- !app_assoc. rewrite run_load_fields by (rewrite forallb_alloc_regs; exact Hl).
  edestruct (run_transforms_prefix ts (write_fields rf (alloc_regs 0 fields) p)
              ([ILookupVal (map snd (alloc_regs 0 fields)) name 1]
                 ++ INat k fam amin amax pmin pmax fl :: tail) p) as [rf' [_ Hr]].
  rewrite Hr. cbn [app run_rule]. reflexivity.
Qed.

(** A field-sourced NAT operand: load the field (+ transforms), then the terminal
    [INat] accepts. *)
Lemma run_field_nat : forall f ts tail rf k fam amin amax pmin pmax fl p,
  field_loadable f p = true ->
  run_rule rf ((compile_load (field_load f) 1 :: compile_transforms ts)
               ++ INat k fam amin amax pmin pmax fl :: tail) p = Some Accept.
Proof.
  intros f ts tail rf k fam amin amax pmin pmax fl p Hl.
  cbn [app]. rewrite compile_load_correct by exact Hl.
  edestruct (run_transforms_prefix ts (set_reg rf 1 (field_value f p))
              (INat k fam amin amax pmin pmax fl :: tail) p) as [rf' [_ Hr]].
  rewrite Hr. cbn [run_rule]. reflexivity.
Qed.

(** A statement whose operand load BREAKs returns [None] (the VM stops at the
    failing payload load), regardless of the trailing program. *)
Lemma run_stmt_break : forall s rf rest p,
  stmt_loadable s p = false ->
  run_rule rf (compile_stmt s ++ rest) p = None.
Proof.
  destruct s; intros rf rest p Hl; cbn [stmt_loadable] in Hl; try discriminate Hl;
    cbn [compile_stmt]; rewrite <- ?app_assoc.
  - (* SMangle *) rewrite run_vsrc_break by exact Hl. reflexivity.
  - (* SMetaSet *) rewrite run_vsrc_break by exact Hl. reflexivity.
  - (* SCtSet *) rewrite run_vsrc_break by exact Hl. reflexivity.
  - (* SCtSetDir *) rewrite run_vsrc_break by exact Hl. reflexivity.
  - (* SSynproxy: synproxy_loadable = false (non-TCP) => the rule BREAKs to None *)
    cbn [app run_rule]. unfold synproxy_loadable in *. rewrite Hl. reflexivity.
  - (* SDynset *) rewrite run_load_fields_break; [reflexivity|]. rewrite forallb_alloc_regs; exact Hl.
  - (* SObjrefMap *) rewrite run_load_fields_break; [reflexivity|]. rewrite forallb_alloc_regs; exact Hl.
  - (* SDynsetImm *) rewrite run_load_fields_break; [reflexivity|]. rewrite forallb_alloc_regs; exact Hl.
  - (* SExthdrWrite *) rewrite run_vsrc_break by exact Hl. reflexivity.
  - (* SDupSrc *) rewrite run_vsrc_break by exact Hl. reflexivity.
Qed.

(** Unfold [stmts_after_outcome] on a non-synproxy head (the catch-all arm). *)
Lemma stmts_after_outcome_nonsyn : forall s ss p,
  is_synproxy_stmt s = false ->
  stmts_after_outcome (s :: ss) p =
    if stmt_loadable s p then stmts_after_outcome ss p else None.
Proof.
  intros s ss p Hsp. destruct s; cbn [is_synproxy_stmt] in Hsp; try discriminate Hsp;
    reflexivity.
Qed.

(** Running the post-outcome statements alone realises [stmts_after_outcome]: a
    verdict-neutral statement falls through, a SYN-proxy decides (BREAK/STOP); a
    loadable list with no synproxy falls through to [None]. *)
Lemma run_stmts_after : forall ss rf p,
  run_rule rf (flat_map compile_stmt ss) p = stmts_after_outcome ss p.
Proof.
  induction ss as [| s ss IH]; intros rf p; [reflexivity|].
  cbn [flat_map].
  destruct (is_notrack_stmt s) eqn:Hnt.
  - (* SNotrack: VM threads [set_untracked]; verdict-neutral, and
       [stmts_after_outcome] is invariant under it *)
    destruct s; cbn [is_notrack_stmt] in Hnt; try discriminate Hnt.
    cbn [compile_stmt app run_rule stmts_after_outcome].
    rewrite IH, stmts_after_outcome_untracked. reflexivity.
  - destruct (is_synproxy_stmt s) eqn:Hsp.
    + (* SSynproxy: break / stop / continue, mirroring run_rule's ISynproxy *)
      destruct s; cbn [is_synproxy_stmt] in Hsp; try discriminate Hsp.
      cbn [compile_stmt app run_rule stmts_after_outcome].
      destruct (synproxy_loadable p) eqn:Hld.
      * destruct (synproxy_stops p) eqn:Hstop; [reflexivity | apply IH].
      * reflexivity.
    + (* any other statement: verdict-neutral when loadable, else BREAK to None *)
      rewrite stmts_after_outcome_nonsyn by exact Hsp.
      destruct (stmt_loadable s p) eqn:Hl.
      * edestruct (run_stmt_exists s rf (flat_map compile_stmt ss) p Hnt Hsp Hl) as [rf' Hr].
        rewrite Hr. apply IH.
      * rewrite run_stmt_break by exact Hl. reflexivity.
Qed.

(** A static verdict tail followed by trailing statements: a terminal verdict
    ignores them; a [Continue] tail runs them (verdict-neutrally) to [None]. *)
Lemma run_verdict_tail_after : forall v tail rf p,
  run_rule rf (verdict_tail v ++ tail) p =
    match v with Continue => run_rule rf tail p | _ => verdict_result v end.
Proof. destruct v; cbn [verdict_tail app run_rule]; reflexivity. Qed.

(** The body version: an ordered list of matches and statements, walked
    left-to-right.  A [BMatch] is the single-match step; a verdict-neutral [BStmt]
    threads the register file through; a SYN-proxy [BStmt] that STOPS short-circuits
    to [Some Drop] (matches after it never run), so the result is exactly
    [if rule_applies_walk body then (if body_synproxy_stops body then Some Drop else res) else None].
    (On a loadable body — the hypothesis — synproxy never BREAKs here.) *)
(** [body_thread] of a cons: a [notrack] head latches [set_untracked] (collapsing
    with the rest by idempotence), any other head leaves the latch to the rest. *)
Lemma body_thread_cons_notrack : forall body p,
  body_thread (BStmt SNotrack :: body) p = body_thread body (set_untracked p).
Proof.
  intros body p. unfold body_thread.
  cbn [body_has_notrack existsb]. cbn [orb].
  destruct (body_has_notrack body); [rewrite set_untracked_idem|]; reflexivity.
Qed.

Lemma body_thread_cons_other : forall it body p,
  (match it with BStmt SNotrack => false | _ => true end) = true ->
  body_thread (it :: body) p = body_thread body p.
Proof.
  intros it body p Hit. unfold body_thread.
  destruct it as [m | s]; cbn [body_has_notrack existsb].
  - reflexivity.
  - destruct s; cbn [orb]; try reflexivity; discriminate Hit.
Qed.

(** [synproxy_stops] is invariant under [set_untracked]: needed to discharge the
    synproxy-continue case's hypothesis at the threaded packet [set_untracked p]. *)
Lemma synproxy_stops_untracked_or : forall p q,
  (q = p \/ q = set_untracked p) -> synproxy_stops q = synproxy_stops p.
Proof.
  intros p q [-> | ->]; [reflexivity | apply synproxy_stops_untracked].
Qed.

(** [res] is now a FUNCTION of the running packet, and the tail is run at the
    body-threaded packet [body_thread body p] (the latch a reached [notrack]
    leaves).  [Hc] quantifies over the running packet [q] — which the induction only
    ever instantiates at [p] or (past a [notrack]) at [set_untracked p], so [Hc]
    carries that [q ∈ {p, set_untracked p}] restriction. *)
Lemma run_compile_body : forall body tail (res : packet -> option verdict) p,
  (forall q, (q = p \/ q = set_untracked p) ->
             body_synproxy_stops body q = false -> forall rf, run_rule rf tail q = res q) ->
  body_loadable_walk body p = true ->
  forall rf, run_rule rf (flat_map compile_body_item body ++ tail) p =
    if rule_applies_walk body p
    then (if body_synproxy_stops body p then Some Drop else res (body_thread body p))
    else None.
Proof.
  induction body as [| it body IH]; intros tail res p Hc Hld rf.
  - cbn [flat_map app rule_applies_walk body_synproxy_stops existsb].
    unfold body_thread; cbn [body_has_notrack existsb]. apply Hc; [left; reflexivity | reflexivity].
  - destruct it as [m | s]; cbn [flat_map compile_body_item]; rewrite <- app_assoc.
    + (* BMatch m: a single-match step, then the rest of the body *)
      cbn [body_loadable_walk] in Hld. apply Bool.andb_true_iff in Hld. destruct Hld as [Hitl Hldr].
      assert (Hrelay : forall q, (q = p \/ q = set_untracked p) ->
                  body_synproxy_stops body q = false -> forall rf0, run_rule rf0 tail q = res q).
      { intros q Hq Hb rf0. apply Hc; [exact Hq|].
        unfold body_synproxy_stops. cbn [existsb]. cbn [orb]. exact Hb. }
      replace (compile_match m ++ (flat_map compile_body_item body ++ tail))
        with (flat_map compile_match [m] ++ (flat_map compile_body_item body ++ tail))
        by (cbn [flat_map app]; rewrite app_nil_r; reflexivity).
      rewrite (run_compile_matches_const [m] (flat_map compile_body_item body ++ tail)
                 (if rule_applies_walk body p
                  then (if body_synproxy_stops body p then Some Drop else res (body_thread body p)) else None)
                 p (fun rf0 => IH tail res p Hrelay Hldr rf0)).
      cbn [flat_map app forallb]. rewrite Bool.andb_true_r.
      cbn [rule_applies_walk body_synproxy_stops existsb]. cbn [orb].
      rewrite (body_thread_cons_other (BMatch m) body p eq_refl).
      destruct (eval_matchcond m p); reflexivity.
    + (* BStmt s: notrack threads [set_untracked]; synproxy decides; others thread *)
      destruct (is_notrack_stmt s) eqn:Hnt.
      * (* SNotrack: VM threads [set_untracked p]; DSL walk threads it too *)
        destruct s; cbn [is_notrack_stmt] in Hnt; try discriminate Hnt.
        cbn [body_loadable_walk body_item_loadable stmt_loadable] in Hld.
        cbn [andb] in Hld.
        cbn [compile_stmt app run_rule].
        change (rule_applies_walk (BStmt SNotrack :: body) p)
          with (rule_applies_walk body (set_untracked p)).
        assert (Hss : body_synproxy_stops (BStmt SNotrack :: body) p
                      = body_synproxy_stops body p)
          by (unfold body_synproxy_stops; cbn [existsb]; reflexivity).
        rewrite Hss, body_thread_cons_notrack.
        rewrite <- (body_synproxy_stops_untracked body p).
        assert (Hc' : forall q, (q = set_untracked p \/ q = set_untracked (set_untracked p)) ->
                       body_synproxy_stops body q = false ->
                       forall rf0, run_rule rf0 tail q = res q).
        { intros q Hq Hb rf0. apply Hc.
          - rewrite set_untracked_idem in Hq. destruct Hq; right; assumption.
          - unfold body_synproxy_stops; cbn [existsb]; exact Hb. }
        rewrite (IH tail res (set_untracked p) Hc'
                   ltac:(rewrite body_loadable_walk_untracked; exact Hld)).
        reflexivity.
      * destruct (is_synproxy_stmt s) eqn:Hsp.
        -- (* SSynproxy: stop => Some Drop, else continue *)
           destruct s; cbn [is_synproxy_stmt] in Hsp; try discriminate Hsp.
           cbn [body_loadable_walk] in Hld. apply Bool.andb_true_iff in Hld. destruct Hld as [Hitl Hldr'].
           cbn [compile_stmt app run_rule]. rewrite Hitl.
           change (body_synproxy_stops (BStmt (SSynproxy mss wscale) :: body) p)
             with (synproxy_stops p || body_synproxy_stops body p).
           change (rule_applies_walk (BStmt (SSynproxy mss wscale) :: body) p)
             with (if synproxy_stops p then true else rule_applies_walk body p).
           rewrite (body_thread_cons_other (BStmt (SSynproxy mss wscale)) body p eq_refl).
           destruct (synproxy_stops p) eqn:Hstop; cbn [orb].
           ++ reflexivity.
           ++ (* continue: Hldr' is [body_loadable_walk body] *)
              apply IH; [| exact Hldr']. intros q Hq Hb rf0. apply Hc; [exact Hq|].
              change (body_synproxy_stops (BStmt (SSynproxy mss wscale) :: body) q)
                with (synproxy_stops q || body_synproxy_stops body q).
              rewrite (synproxy_stops_untracked_or p q Hq), Hstop. cbn [orb]. exact Hb.
        -- (* verdict-neutral statement (not notrack, not synproxy): threads straight *)
           assert (Hbw : body_loadable_walk (BStmt s :: body) p =
                     body_item_loadable (BStmt s) p && body_loadable_walk body p)
             by (destruct s; cbn [is_synproxy_stmt] in Hsp; try discriminate Hsp; reflexivity).
           rewrite Hbw in Hld. apply Bool.andb_true_iff in Hld. destruct Hld as [Hitl Hldr].
           cbn [body_item_loadable] in Hitl.
           edestruct (run_stmt_exists s rf (flat_map compile_body_item body ++ tail) p Hnt Hsp Hitl)
             as [rf' Hr].
           rewrite Hr.
           assert (Hh : (match BStmt s with BStmt (SSynproxy _ _) => synproxy_stops p | _ => false end) = false)
             by (destruct s; cbn [is_synproxy_stmt] in Hsp; try discriminate Hsp; reflexivity).
           assert (Hhead : body_synproxy_stops (BStmt s :: body) p = body_synproxy_stops body p)
             by (unfold body_synproxy_stops; cbn [existsb]; rewrite Hh; reflexivity).
           assert (Hwalk : rule_applies_walk (BStmt s :: body) p = rule_applies_walk body p)
             by (destruct s; cbn [is_synproxy_stmt] in Hsp, Hnt; cbn [is_notrack_stmt] in Hnt;
                 try discriminate Hsp; try discriminate Hnt; reflexivity).
           rewrite Hhead, Hwalk.
           rewrite (body_thread_cons_other (BStmt s) body p
                      ltac:(destruct s; cbn [is_notrack_stmt] in Hnt;
                            try discriminate Hnt; reflexivity)).
           apply IH; [| exact Hldr].
           intros q Hq Hb rf0. apply Hc; [exact Hq|].
           assert (Hheadq : body_synproxy_stops (BStmt s :: body) q = body_synproxy_stops body q)
             by (destruct s; cbn [is_synproxy_stmt] in Hsp; try discriminate Hsp; reflexivity).
           rewrite Hheadq. exact Hb.
Qed.

(** A single compiled match whose field is unloadable BREAKs the rule. *)
Lemma compile_match_break : forall m rest p,
  match_loadable m p = false ->
  forall rf, run_rule rf (compile_match m ++ rest) p = None.
Proof.
  intros m rest p Hl rf.
  destruct m as [f v0 | f v0 | f neg lo hi | f neg mask xor v0 | f op v0
                | fields neg nm | f ts op v0 | f ts neg nm
                | f ts neg lo hi | spec | qspec | clspec
                | celems neg nm]; cbn [compile_match match_loadable] in *; try discriminate Hl;
    rewrite <- ?app_assoc; try (cbn [app]; apply compile_load_break; exact Hl).
  - (* MConcatSet *) cbn [app]. rewrite run_load_fields_break; [reflexivity|].
    rewrite forallb_alloc_regs. unfold fields_loadable in Hl. exact Hl.
  - (* MConcatSetT *) cbn [app]. rewrite run_load_fields_t_break; [reflexivity|].
    unfold fields_loadable in Hl. rewrite forallb_map in Hl. exact Hl.
Qed.

(** If the body's load walk BREAKs (an item on the reachable path is unloadable),
    the compiled body runs to [None] — the VM hits the failing load before any
    verdict-bearing synproxy. *)
Lemma run_compile_body_break : forall body tail p,
  body_loadable_walk body p = false ->
  forall rf, run_rule rf (flat_map compile_body_item body ++ tail) p = None.
Proof.
  induction body as [| it body IH]; intros tail p Hl rf; [discriminate Hl|].
  destruct it as [m | s]; cbn [flat_map compile_body_item] in *; rewrite <- app_assoc.
  - (* BMatch *) cbn [body_loadable_walk body_item_loadable] in Hl.
    apply Bool.andb_false_iff in Hl. destruct (match_loadable m p) eqn:Hm.
    + (* match loads; break later in body *)
      assert (Hbr : body_loadable_walk body p = false)
        by (destruct Hl as [Hd | Hr]; [congruence | exact Hr]).
      replace (compile_match m ++ flat_map compile_body_item body ++ tail)
        with (flat_map compile_match [m] ++ (flat_map compile_body_item body ++ tail))
        by (cbn [flat_map app]; rewrite app_nil_r; reflexivity).
      rewrite (run_compile_matches_const [m] (flat_map compile_body_item body ++ tail)
                 None p (fun rf0 => IH tail p Hbr rf0)).
      destruct (forallb (fun m0 => eval_matchcond m0 p) [m]); reflexivity.
    + apply compile_match_break; exact Hm.
  - (* BStmt *) destruct (is_notrack_stmt s) eqn:Hnt.
    + (* SNotrack: VM threads [set_untracked]; the break is in the rest, and
         [body_loadable_walk] is invariant under [set_untracked] *)
      destruct s; cbn [is_notrack_stmt] in Hnt; try discriminate Hnt.
      cbn [body_loadable_walk body_item_loadable stmt_loadable] in Hl. cbn [andb] in Hl.
      cbn [compile_stmt app run_rule].
      apply IH. rewrite body_loadable_walk_untracked. exact Hl.
    + destruct (is_synproxy_stmt s) eqn:Hsp.
    * (* SSynproxy: walk = synproxy_loadable && (if stops then true else walk rest) *)
      destruct s; cbn [is_synproxy_stmt] in Hsp; try discriminate Hsp.
      cbn [body_loadable_walk] in Hl. cbn [compile_stmt app run_rule].
      apply Bool.andb_false_iff in Hl. destruct (synproxy_loadable p) eqn:Hld.
      -- (* loadable: the break must be in the unreachable rest only when NOT stopping *)
        destruct Hl as [Hd | Hr]; [discriminate Hd|].
        destruct (synproxy_stops p) eqn:Hstop; [discriminate Hr | apply IH; exact Hr].
      -- reflexivity.
    * (* other statement *)
      assert (Hbw : body_loadable_walk (BStmt s :: body) p =
                body_item_loadable (BStmt s) p && body_loadable_walk body p)
        by (destruct s; cbn [is_synproxy_stmt] in Hsp; try discriminate Hsp; reflexivity).
      rewrite Hbw in Hl. apply Bool.andb_false_iff in Hl.
      cbn [body_item_loadable] in Hl. destruct (stmt_loadable s p) eqn:Hs.
      -- edestruct (run_stmt_exists s rf (flat_map compile_body_item body ++ tail) p Hnt Hsp Hs) as [rf' Hr].
        rewrite Hr. apply IH. destruct Hl as [Hd | Hr']; [congruence | exact Hr'].
      -- apply run_stmt_break; exact Hs.
Qed.

(** The terminal of a rule (nat/tproxy/fwd/queue/verdict) runs, from any register
    file, to its [terminal_outcome] — ignoring the post-outcome statements after a
    side-effect terminal, running them to [None] after a [Continue]. *)
Lemma run_terminal : forall r rf p,
  tail_loadable r p = true ->
  run_rule rf (compile_terminal r ++ flat_map compile_stmt (r_after r)) p
  = terminal_outcome r p.
Proof.
  intros r rf p Hl. unfold tail_loadable in Hl.
  apply Bool.andb_true_iff in Hl. destruct Hl as [Htl Har].
  unfold compile_terminal, terminal_outcome, terminal_loadable in *.
  destruct (r_nat r) as [n |].
  - rewrite <- app_assoc. destruct (nat_src n) as [vs |].
    + apply run_vsrc_nat; exact Htl.
    + destruct (nat_map n) as [[[fields ts] name] |].
      * apply run_map_nat; exact Htl.
      * destruct (nat_field n) as [[f ts] |]; [apply run_field_nat; exact Htl | apply run_imms_nat].
  - destruct (r_tproxy r) as [t |].
    + rewrite <- app_assoc. destruct (tp_portmap t) as [[[m o] name] |];
        [apply run_portmap_tproxy | apply run_imms_tproxy].
    + destruct (r_fwd r) as [w |].
      * rewrite <- app_assoc. destruct (fwd_src w) as [vs |];
          [apply run_vsrc_fwd; exact Htl | apply run_imms_fwd].
      * destruct (r_queue r) as [q |].
        -- rewrite <- app_assoc. destruct (q_src q) as [vs |];
             [apply run_vsrc_queue; exact Htl | apply run_imms_queue].
        -- rewrite run_verdict_tail_after.
           (* Continue runs r_after, realising [stmts_after_outcome] = the
              [Continue] arm of [terminal_outcome]; every other verdict is terminal. *)
           destruct (r_verdict r); solve [ reflexivity | apply run_stmts_after ].
Qed.

(** When the terminal/post-outcome part is NOT loadable, the compiled terminal
    BREAKs (the VM hits the failing operand load, or a failing post-outcome
    statement load on a fall-through). *)
Lemma run_terminal_break : forall r rf p,
  tail_loadable r p = false ->
  run_rule rf (compile_terminal r ++ flat_map compile_stmt (r_after r)) p = None.
Proof.
  intros r rf p Hl. unfold tail_loadable in Hl. apply Bool.andb_false_iff in Hl.
  unfold compile_terminal, terminal_loadable, terminal_outcome in *.
  destruct (r_nat r) as [n |].
  - rewrite <- app_assoc. destruct (nat_src n) as [vs |].
    + rewrite run_vsrc_break; [reflexivity|].
      destruct Hl as [Hd | Ht]; [exact Hd | discriminate Ht].
    + destruct (nat_map n) as [[[fields ts] name] |].
      * rewrite <- !app_assoc. rewrite run_load_fields_break; [reflexivity|].
        rewrite forallb_alloc_regs.
        destruct Hl as [Hd | Ht]; [exact Hd | discriminate Ht].
      * destruct (nat_field n) as [[f ts] |].
        -- cbn [app]. rewrite compile_load_break; [reflexivity|].
           destruct Hl as [Hd | Ht]; [exact Hd | discriminate Ht].
        -- (* immediate operands never break; tail_loadable false must be the [Some] r_after,
              but terminal_outcome is [Some Accept] here, so the second disjunct is [true=false] *)
           destruct Hl as [Hd | Ht]; [discriminate Hd | discriminate Ht].
  - destruct (r_tproxy r) as [t |].
    + (* tproxy: immediate/symhash operands never break; terminal_outcome=Some Accept *)
      destruct Hl as [Hd | Ht]; [discriminate Hd | discriminate Ht].
    + destruct (r_fwd r) as [w |].
      * rewrite <- app_assoc. destruct (fwd_src w) as [vs |].
        -- rewrite run_vsrc_break; [reflexivity|].
           destruct Hl as [Hd | Ht]; [exact Hd | discriminate Ht].
        -- destruct Hl as [Hd | Ht]; [discriminate Hd | discriminate Ht].
      * destruct (r_queue r) as [q |].
        -- rewrite <- app_assoc. destruct (q_src q) as [vs |].
           ++ rewrite run_vsrc_break; [reflexivity|].
              destruct Hl as [Hd | Ht]; [exact Hd | discriminate Ht].
           ++ destruct Hl as [Hd | Ht]; [discriminate Hd | discriminate Ht].
        -- (* static verdict: only a [Continue] runs r_after; a break there is in r_after *)
           rewrite run_verdict_tail_after.
           destruct (r_verdict r);
             try (destruct Hl as [Hd | Ht]; [discriminate Hd | discriminate Ht]).
           (* Continue: terminal_outcome = stmts_after_outcome (r_after); tail_loadable
              false forces it [None], and [run_stmts_after] realises that [None]. *)
           rewrite run_stmts_after.
           destruct Hl as [Hd | Ht]; [discriminate Hd|].
           destruct (stmts_after_outcome (r_after r) p); [discriminate Ht | reflexivity].
Qed.

(** The compiled verdict-map prefix + terminal + post-outcome statements runs to
    the rule's [outcome] when the [end_loadable] part of the rule succeeds. *)
Lemma run_compile_end : forall r rf p,
  end_loadable r p = true ->
  run_rule rf (compile_end r ++ flat_map compile_stmt (r_after r)) p = outcome_core r p.
Proof.
  intros r rf p Hel. unfold compile_end, compile_vmap, outcome_core, end_loadable in *.
  destruct (r_vmap r) as [vm |].
  - apply Bool.andb_true_iff in Hel. destruct Hel as [Hvk Hrest].
    unfold vmap_loadable in Hvk.
    rewrite <- app_assoc. destruct (vm_keyf vm) as [[f ts] |].
    + (* transformed single-field key *)
      cbn [app]. rewrite compile_load_correct by exact Hvk. rewrite <- app_assoc.
      edestruct (run_transforms_prefix ts (set_reg rf 1 (field_value f p))
                  ([IVmap [1] (vm_name vm)]
                     ++ compile_terminal r ++ flat_map compile_stmt (r_after r)) p)
        as [rf' [Hr1 Hr2]].
      rewrite Hr2. cbn [app run_rule concat map].
      rewrite app_nil_r, Hr1, set_reg_same.
      destruct (assoc_verdict (apply_transforms ts (field_value f p))
                              (e_vmap (pkt_env p) (vm_name vm)));
        [reflexivity | apply run_terminal; exact Hrest].
    + (* concat key: IVmap reads the loaded concatenation *)
      rewrite <- app_assoc. rewrite run_load_fields by (rewrite forallb_alloc_regs; exact Hvk).
      cbn [app run_rule].
      rewrite map_write_fields by apply alloc_regs_nodup.
      rewrite map_fst_field, alloc_regs_fst.
      destruct (assoc_verdict (concat (map (fun f => field_value f p) (vm_fields vm)))
                              (e_vmap (pkt_env p) (vm_name vm)));
        [reflexivity | apply run_terminal; exact Hrest].
  - (* no verdict map: just the terminal *)
    cbn [app]. apply run_terminal; exact Hel.
Qed.

(** When a rule is NOT loadable, the compiled rule BREAKs: the VM hits the first
    failing payload load (always on the evaluated path, by construction of
    [rule_loadable]) and returns [None].  We prove this via the body and end
    helpers' break behaviour. *)
Lemma run_compile_end_break : forall r rf p,
  end_loadable r p = false ->
  run_rule rf (compile_end r ++ flat_map compile_stmt (r_after r)) p = None.
Proof.
  intros r rf p Hel. unfold compile_end, compile_vmap, end_loadable, vmap_loadable in *.
  destruct (r_vmap r) as [vm |].
  - rewrite <- app_assoc. destruct (vm_keyf vm) as [[f ts] |];
      cbv zeta in Hel; apply Bool.andb_false_iff in Hel.
    + (* transformed single-field key *)
      destruct (field_loadable f p) eqn:Hf.
      * (* key loads: vmap miss forces tail break *)
        cbn [app]. rewrite compile_load_correct by exact Hf. rewrite <- app_assoc.
        edestruct (run_transforms_prefix ts (set_reg rf 1 (field_value f p))
                    ([IVmap [1] (vm_name vm)]
                       ++ compile_terminal r ++ flat_map compile_stmt (r_after r)) p)
          as [rf' [Hr1 Hr2]].
        rewrite Hr2. cbn [app run_rule concat map].
        rewrite app_nil_r, Hr1, set_reg_same.
        destruct Hel as [Hd | Ht]; [congruence|].
        destruct (assoc_verdict (apply_transforms ts (field_value f p))
                                (e_vmap (pkt_env p) (vm_name vm))).
        -- discriminate Ht.
        -- apply run_terminal_break; exact Ht.
      * (* key load breaks *)
        cbn [app]. apply compile_load_break; exact Hf.
    + (* concat key *)
      destruct (forallb (fun f => field_loadable f p) (vm_fields vm)) eqn:Hfs.
      * rewrite <- app_assoc. rewrite run_load_fields by (rewrite forallb_alloc_regs; exact Hfs).
        cbn [app run_rule].
        rewrite map_write_fields by apply alloc_regs_nodup.
        rewrite map_fst_field, alloc_regs_fst.
        destruct Hel as [Hd | Ht]; [unfold fields_loadable in Hd; congruence|].
        destruct (assoc_verdict (concat (map (fun f => field_value f p) (vm_fields vm)))
                                (e_vmap (pkt_env p) (vm_name vm))).
        -- discriminate Ht.
        -- apply run_terminal_break; exact Ht.
      * rewrite <- app_assoc. rewrite run_load_fields_break; [reflexivity|].
        rewrite forallb_alloc_regs; exact Hfs.
  - cbn [app]. apply run_terminal_break; exact Hel.
Qed.

Lemma run_rule_compile_rule : forall r p,
  rule_loadable r p = true ->
  run_rule empty_rf (compile_rule r) p =
  if rule_applies r p then outcome r p else None.
Proof.
  intros r p Hl. unfold rule_loadable in Hl. apply Bool.andb_true_iff in Hl. destruct Hl as [Hbody Hend].
  unfold compile_rule, rule_applies, outcome.
  rewrite (run_compile_body (r_body r) _
             (fun q => if end_loadable r q then outcome_core r q else None) p).
  - destruct (rule_applies_walk (r_body r) p); [| reflexivity].
    destruct (body_synproxy_stops (r_body r) p) eqn:Hbs.
    + reflexivity.
    + (* the synproxy-free branch: [Hend] is end-loadability at the threaded packet *)
      cbn match in Hend. rewrite Hend. reflexivity.
  - (* [Hc]: at any reachable packet [q] the compiled tail runs to the loadability-
       guarded outcome ([run_compile_end] when loadable, else [run_compile_end_break]). *)
    intros q Hq Hns rf. destruct (end_loadable r q) eqn:He.
    + apply run_compile_end; exact He.
    + apply run_compile_end_break; exact He.
  - exact Hbody.
Qed.

Lemma run_rule_compile_rule_break : forall r p,
  rule_loadable r p = false ->
  run_rule empty_rf (compile_rule r) p = None.
Proof.
  intros r p Hl. unfold rule_loadable in Hl. apply Bool.andb_false_iff in Hl.
  unfold compile_rule.
  destruct (body_loadable_walk (r_body r) p) eqn:Hbody.
  - (* body loads; so the break is in the end (and there is no stopping synproxy,
       else the [if body_synproxy_stops then true ...] disjunct could not be false) *)
    assert (Hns : body_synproxy_stops (r_body r) p = false).
    { destruct (body_synproxy_stops (r_body r) p) eqn:Hbs; [|reflexivity].
      destruct Hl as [Hd | He]; [congruence | discriminate He]. }
    assert (Hend : end_loadable r (body_thread (r_body r) p) = false).
    { rewrite Hns in Hl. destruct Hl as [Hd | He]; [congruence | exact He]. }
    rewrite (run_compile_body (r_body r)
              (compile_end r ++ flat_map compile_stmt (r_after r))
              (fun q => if end_loadable r q then outcome_core r q else None) p).
    + rewrite Hns. rewrite Hend.
      destruct (rule_applies_walk (r_body r) p); reflexivity.
    + intros q Hq Hns' rf. destruct (end_loadable r q) eqn:He.
      * apply run_compile_end; exact He.
      * apply run_compile_end_break; exact He.
    + exact Hbody.
  - (* a body item on the reachable path breaks *)
    apply run_compile_body_break; exact Hbody.
Qed.

(** Chain level: the compiled program reproduces the rule-list evaluation. *)
Lemma run_program_compile_chain : forall rs p,
  run_program (map compile_rule rs) p = eval_rules rs p.
Proof.
  induction rs as [| r rs IH]; intros p.
  - reflexivity.
  - cbn [map run_program eval_rules]. destruct (rule_loadable r p) eqn:Hrl.
    + rewrite (run_rule_compile_rule r p Hrl). cbn [andb].
      destruct (rule_applies r p); cbn [terminal].
      * destruct (outcome r p) as [v |].
        -- destruct (terminal v); [reflexivity | apply IH].
        -- apply IH.
      * apply IH.
    + rewrite (run_rule_compile_rule_break r p Hrl). cbn [andb]. apply IH.
Qed.

(** ** Main theorem: semantic preservation. *)
Theorem compile_chain_correct : forall c p,
  run_chain (compile_chain c) (c_policy c) p = eval_chain c p.
Proof.
  intros c p. unfold run_chain, eval_chain, compile_chain.
  rewrite run_program_compile_chain. reflexivity.
Qed.

(** Sets/maps as declared objects: evaluating a chain against the environment
    BUILT FROM a table's set/map declarations ([env_with_sets base d]), the
    compiled VM agrees with the DSL — and every `lookup @s` reads exactly the
    elements declared for [s] ([e_set_declared]).  So the membership semantics is
    tied to the declared set object, not to an inlined copy or a disconnected
    oracle.  (Corollary of [compile_chain_correct], which holds for every env.) *)
Theorem compile_chain_sets_correct : forall c base d p,
  run_chain (compile_chain c) (c_policy c) (set_env p (env_with_sets base d))
  = eval_chain c (set_env p (env_with_sets base d)).
Proof. intros. apply compile_chain_correct. Qed.

(** ** Phase B main theorem: the compiler preserves in-traversal mutation.

    The compiled bytecode's meta/ct effect equals the declarative one for ANY
    rule — matches, meta/ct sets (with non-degenerate operands), AND every other
    statement (mangle, NAT, dup, counter, log, dynset, exthdr, objref, …): those
    are threaded through as meta/ct-neutral, exactly as they are.  So a `meta/ct
    set` is faithfully visible to later rules on BOTH sides. *)
Lemma run_rule_writes_compile_rule : forall r p,
  simple_writes r = true ->
  forallb (fun s => negb (is_mut_stmt s)) (r_after r) = true ->
  run_rule_writes empty_rf (compile_rule r) p = dsl_writes r p.
Proof.
  intros r p Hs Ha. unfold compile_rule, dsl_writes.
  apply run_compile_body_writes; [| exact Hs].
  intros rf p'. apply run_rule_writes_neutral.
  rewrite nw_app, nw_compile_end, (nw_flat_compile_stmt _ Ha). reflexivity.
Qed.

(* (run_rule_writes_compile_rule holds for ALL packets, loadable or not — the
   break-aware [body_writes] mirrors the VM's break.) *)

(** The mutation theorem's only well-formedness requirement (NOT a feature scope):
    every meta/ct *set* operand is non-degenerate ([simple_writes] — i.e. not a
    malformed zero-field jhash/map/or, which no real ruleset emits), and the rule's
    post-outcome statements contain no meta/ct set (`r_after` is verdict-neutral —
    counter/log/objref — in every real ruleset; a meta-set after a verdict map is
    the one residual mutation case).  ALL ordinary statements (mangle/NAT/dup/
    counter/dynset/exthdr/…) are in scope. *)
Definition mut_wf (r : rule) : bool :=
  simple_writes r && forallb (fun s => negb (is_mut_stmt s)) (r_after r)
  (* the rule's bytecode contains no incremental `numgen` ([numgen_free_prog]), so the
     VM mutation evaluator's [numgen_sweep_prog] is the identity and agrees with the
     DSL [dsl_writes] (which has no numgen surface).  Every real ruleset satisfies this:
     numgen is reachable only through the bytecode, never the parser/DSL. *)
  && numgen_free_prog (compile_rule r).

Lemma run_program_mut_compile_chain : forall rs p,
  forallb mut_wf rs = true ->
  run_program_mut (map compile_rule rs) p = eval_rules_mut rs p.
Proof.
  induction rs as [| r rs IH]; intros p Hall; [reflexivity|].
  cbn [forallb] in Hall. apply Bool.andb_true_iff in Hall. destruct Hall as [Hr Hrs].
  unfold mut_wf in Hr. apply Bool.andb_true_iff in Hr. destruct Hr as [Hr Hnf].
  apply Bool.andb_true_iff in Hr. destruct Hr as [Hs Ha].
  cbn [map run_program_mut eval_rules_mut].
  (* the VM threads [numgen_sweep_prog (compile_rule r) (run_rule_writes …)]; the rule
     is numgen-free, so the sweep is the identity and this is just [run_rule_writes]. *)
  rewrite (numgen_sweep_prog_id (compile_rule r) _ Hnf).
  rewrite (run_rule_writes_compile_rule r p Hs Ha).
  destruct (rule_loadable r p) eqn:Hrl.
  - rewrite (run_rule_compile_rule r p Hrl). cbn [andb].
    destruct (rule_applies r p).
    + destruct (outcome r p) as [v |].
      * destruct (terminal v); [reflexivity | apply IH; exact Hrs].
      * apply IH; exact Hrs.
    + apply IH; exact Hrs.
  - rewrite (run_rule_compile_rule_break r p Hrl). cbn [andb]. apply IH; exact Hrs.
Qed.

Theorem compile_chain_mut_correct : forall c p,
  forallb mut_wf (c_rules c) = true ->
  run_chain_mut (compile_chain c) (c_policy c) p = eval_chain_mut c p.
Proof.
  intros c p Hall. unfold run_chain_mut, eval_chain_mut, compile_chain.
  rewrite run_program_mut_compile_chain by exact Hall. reflexivity.
Qed.

(** ** Cross-packet preservation: the env a chain LEAVES is preserved too.

    The same well-formedness gives that the compiled VM and the DSL agree not only
    on the verdict but on the *environment the chain leaves* — including any
    dynset-learned set/map elements.  This is what lets a learned element persist
    to the next packet. *)
Lemma run_program_mut_env_compile_chain : forall rs p,
  forallb mut_wf rs = true ->
  run_program_mut_env (map compile_rule rs) p = eval_rules_mut_env rs p.
Proof.
  induction rs as [| r rs IH]; intros p Hall; [reflexivity|].
  cbn [forallb] in Hall. apply Bool.andb_true_iff in Hall. destruct Hall as [Hr Hrs].
  unfold mut_wf in Hr. apply Bool.andb_true_iff in Hr. destruct Hr as [Hr Hnf].
  apply Bool.andb_true_iff in Hr. destruct Hr as [Hs Ha].
  cbn [map run_program_mut_env eval_rules_mut_env].
  rewrite (numgen_sweep_prog_id (compile_rule r) _ Hnf).
  rewrite (run_rule_writes_compile_rule r p Hs Ha).
  destruct (rule_loadable r p) eqn:Hrl.
  - rewrite (run_rule_compile_rule r p Hrl). cbn [andb].
    destruct (rule_applies r p).
    + destruct (outcome r p) as [v |].
      * destruct (terminal v); [reflexivity | apply IH; exact Hrs].
      * apply IH; exact Hrs.
    + apply IH; exact Hrs.
  - rewrite (run_rule_compile_rule_break r p Hrl). cbn [andb]. apply IH; exact Hrs.
Qed.

Theorem compile_chain_mut_env_correct : forall c p,
  forallb mut_wf (c_rules c) = true ->
  run_chain_mut_env (compile_chain c) (c_policy c) p = eval_chain_mut_env c p.
Proof.
  intros c p Hall. unfold run_chain_mut_env, eval_chain_mut_env, compile_chain.
  rewrite run_program_mut_env_compile_chain by exact Hall. reflexivity.
Qed.

(** [seq_eval_env] is congruent in its per-packet evaluator. *)
Lemma seq_eval_env_ext : forall ev1 ev2,
  (forall e p, ev1 e p = ev2 e p) ->
  forall e packets, seq_eval_env ev1 e packets = seq_eval_env ev2 e packets.
Proof.
  intros ev1 ev2 Hext e packets. revert e.
  induction packets as [| p ps IH]; intros e; cbn [seq_eval_env]; [reflexivity|].
  rewrite Hext. destruct (ev2 e p) as [v e']. f_equal. apply IH.
Qed.

(** Stateful cross-packet preservation for the LEARNING done by the ruleset itself:
    threading the env a chain leaves (dynset-learned sets/maps) into the next
    packet, the compiled VM reproduces the DSL sequence.  So a `add @s {…}` on an
    earlier packet is visible to a `lookup @s` on a later one, end-to-end and
    compiler-preserved — the cross-packet half of the dynamic-set feedback loop. *)
Theorem compile_seq_mut_correct : forall c e packets,
  forallb mut_wf (c_rules c) = true ->
  seq_eval_env (fun e' p => run_chain_mut_env (compile_chain c) (c_policy c) (set_env p e')) e packets
  = seq_eval_env (fun e' p => eval_chain_mut_env c (set_env p e')) e packets.
Proof.
  intros c e packets Hall. apply seq_eval_env_ext. intros e' p.
  apply compile_chain_mut_env_correct. exact Hall.
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
  cbn [run_rules_j eval_rules_j map]. destruct (rule_loadable r p) eqn:Hrl.
  2:{ rewrite (run_rule_compile_rule_break r p Hrl). cbn [andb]. apply IH. }
  rewrite (run_rule_compile_rule r p Hrl). cbn [andb].
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

(** ** Fidelity bridge: where the environment-FREE [eval_chain] is faithful.

    [compile_chain_correct] is a genuine *compiler*-correctness fact — the
    compiled bytecode [run_chain] reproduces the declarative [eval_chain] for
    every chain.  But [eval_chain] itself is only a faithful model of netfilter on
    chains whose realised outcomes carry no [Jump]/[Goto]/[Return] (it has no
    chain environment, so it can only treat a control-transfer verdict as a benign
    fall-through).  The theorem below pins down EXACTLY that: on a jump-free rule
    list the cheap [eval_rules] coincides with the faithful, environment-aware
    [eval_rules_j] for *every* fuel large enough to traverse it and *every* chain
    environment [cs].  Combined with [compile_chain_correct] and
    [compile_table_correct] this gives: for a jump-free base chain the compiled
    single-chain bytecode equals the faithful [eval_table] — and for a chain that
    DOES jump, the faithful semantics is [eval_table]/[run_table]
    ([compile_table_correct]), NOT [eval_chain]. *)
Lemma eval_rules_jumpfree_eq_j : forall fuel cs rs p,
  List.length rs < fuel ->
  rules_jumpfree rs p = true ->
  eval_rules_j fuel cs rs p = eval_rules rs p.
Proof.
  induction fuel as [| fuel IH]; intros cs rs p Hlen Hjf; [inversion Hlen|].
  destruct rs as [| r rest]; [reflexivity|].
  cbn [List.length] in Hlen. apply Nat.succ_lt_mono in Hlen.
  cbn [rules_jumpfree forallb] in Hjf. apply Bool.andb_true_iff in Hjf.
  destruct Hjf as [Hr Hrest].
  cbn [eval_rules_j eval_rules].
  destruct (rule_loadable r p && rule_applies r p); [| apply IH; assumption].
  unfold outcome_jumpfree in Hr.
  destruct (outcome r p) as [v |]; [| apply IH; assumption].
  destruct v; cbn [terminal]; try reflexivity; try discriminate;
    apply IH; assumption.
Qed.

(** On a jump-free chain the environment-free [eval_chain] equals the faithful
    [eval_table] (for any fuel that can traverse it and any environment). *)
Theorem eval_chain_eq_table_jumpfree : forall fuel cs c p,
  List.length (c_rules c) < fuel ->
  chain_jumpfree c p = true ->
  eval_chain c p = eval_table fuel cs c p.
Proof.
  intros fuel cs c p Hlen Hjf. unfold eval_chain, eval_table, chain_jumpfree in *.
  rewrite (eval_rules_jumpfree_eq_j fuel cs (c_rules c) p Hlen Hjf). reflexivity.
Qed.

(** Hence on a jump-free base chain the COMPILED single-chain bytecode reproduces
    the faithful environment-aware [eval_table] — the headline compiler result and
    the faithful semantics line up exactly on [eval_chain]'s valid domain. *)
Theorem compile_chain_faithful_jumpfree : forall fuel cs c p,
  List.length (c_rules c) < fuel ->
  chain_jumpfree c p = true ->
  run_chain (compile_chain c) (c_policy c) p = eval_table fuel cs c p.
Proof.
  intros fuel cs c p Hlen Hjf.
  rewrite compile_chain_correct.
  apply eval_chain_eq_table_jumpfree; assumption.
Qed.

(** ** Regression: the faithful semantics does NOT ignore a jump.

    A base chain whose only rule is [jump "deny"], with ["deny"] a chain that
    DROPs, must DROP — netfilter runs the target chain (nf_tables_core.c JUMP/GOTO
    dispatch).  The environment-free [eval_chain] would (consistently with the
    compiled bytecode) IGNORE the jump and return the base policy [Accept]; this
    is exactly why [eval_chain] is restricted to its jump-free domain above and the
    faithful semantics for jump-bearing chains is [eval_table].  Locked in here so
    the jump-ignoring behaviour can never silently become the certified meaning. *)
From Stdlib Require Import String.
Local Open Scope string_scope.
Definition rg_jump_rule : rule :=
  {| r_body := []; r_verdict := Jump "deny"; r_vmap := None; r_nat := None;
     r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |}.
Definition rg_drop_rule : rule :=
  {| r_body := []; r_verdict := Drop; r_vmap := None; r_nat := None;
     r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |}.
Definition rg_base : chain := {| c_policy := Accept; c_rules := [rg_jump_rule] |}.
Definition rg_deny : chain := {| c_policy := Accept; c_rules := [rg_drop_rule] |}.
Definition rg_cs : list (String.string * chain) := [("deny", rg_deny)].

(** (A) the faithful interpreter runs the target chain and DROPs (matches nft). *)
Theorem faithful_table_jump_drops : forall p, eval_table 10 rg_cs rg_base p = Drop.
Proof. reflexivity. Qed.

(** (B) and the compiled jump-aware VM agrees (via [compile_table_correct]). *)
Theorem compiled_table_jump_drops : forall p,
  run_table 10 (compile_env rg_cs) (compile_chain rg_base) (c_policy rg_base) p = Drop.
Proof. intro p. rewrite compile_table_correct. apply faithful_table_jump_drops. Qed.

(** (C) the base chain's only rule is NOT jump-free, so it is correctly OUTSIDE
    the domain of [eval_chain_eq_table_jumpfree] — i.e. the bridge does not (and
    cannot) certify the unfaithful [eval_chain] result on it. *)
Theorem rg_base_not_jumpfree : forall p, chain_jumpfree rg_base p = false.
Proof. reflexivity. Qed.
Local Close Scope string_scope.

(** ** Ruleset-level preservation: multi-table / multi-hook dispatch.

    Compiling each base chain (and its jump-target environment) and running the
    netfilter dispatch over the compiled bases reproduces the DSL dispatch — so
    the compiler preserves the verdict of a whole hook's worth of base chains
    across tables, not just one chain or one table. *)
Definition compile_base (cb : list (String.string * chain) * chain)
  : list (String.string * program) * (program * verdict) :=
  (compile_env (fst cb), (compile_chain (snd cb), c_policy (snd cb))).

Theorem compile_ruleset_correct : forall fuel bases p,
  run_ruleset fuel (map compile_base bases) p = eval_ruleset fuel bases p.
Proof.
  induction bases as [| [cs base] rest IH]; intros p; [reflexivity|].
  cbn [map compile_base eval_ruleset run_ruleset fst snd].
  rewrite compile_table_correct.
  destruct (base_continues (eval_table fuel cs base p)); [apply IH | reflexivity].
Qed.

(** Full hook dispatch: select+order the base chains for hook [h], compile each,
    and the netfilter dispatch over the compiled bases reproduces the DSL
    [eval_hook] — a corollary of [compile_ruleset_correct] (selection/ordering is
    a pure list operation applied identically on both sides). *)
Theorem compile_hook_correct : forall fuel rs h p,
  run_ruleset fuel (map compile_base (select_hook rs h)) p = eval_hook fuel rs h p.
Proof.
  intros fuel rs h p. unfold eval_hook. apply compile_ruleset_correct.
Qed.

(** [seq_eval] is congruent in the per-packet evaluator: pointwise-equal
    evaluators (and the same [step]) yield identical verdict sequences. *)
Lemma seq_eval_ext : forall ev1 ev2 step,
  (forall e' p, ev1 e' p = ev2 e' p) ->
  forall e packets, seq_eval ev1 step e packets = seq_eval ev2 step e packets.
Proof.
  intros ev1 ev2 step Hext e packets. revert e.
  induction packets as [| p ps IH]; intros e; cbn [seq_eval]; [reflexivity |].
  rewrite !(Hext e p). f_equal. apply IH.
Qed.

(** Stateful preservation: running a packet sequence with the compiled hook
    dispatch — threading a shared environment that [step] mutates between packets
    (rate limiters / quotas / conntrack counts) — reproduces the DSL run.  So the
    compiler preserves verdicts even when a packet's verdict depends on state
    *accumulated from earlier packets*. *)
Theorem compile_seq_correct : forall fuel rs h step e packets,
  seq_eval (fun e' p => run_ruleset fuel (map compile_base (select_hook rs h)) (set_env p e'))
           step e packets
  = seq_eval (fun e' p => eval_hook fuel rs h (set_env p e')) step e packets.
Proof.
  intros. apply seq_eval_ext. intros e' p. apply compile_hook_correct.
Qed.
