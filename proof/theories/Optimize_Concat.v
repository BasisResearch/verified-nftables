(** * Optimize_Concat: the [nft -o] CONCATENATION-SET merge, as an executable
    table-level rewrite, proved verdict-preserving and axiom-free.

    This is the THIRD and final headline [nft -o] merge family, the direct sibling
    of the value->anonymous-SET merge ([optimize_rules_sets], [Optimize_Merge]) and
    the VERDICT-MAP merge ([optimize_rules_vmap], [Optimize_Vmap]).  [nft -o]
    consolidates a run of ADJACENT rules that share every statement BUT the values of
    TWO selectors, with the SAME terminal verdict, into ONE rule whose head matches a
    CONCATENATION set [f1 . f2] of the paired tuples:

        ip saddr 1.1.1.1 tcp dport 22 accept    =>  ip saddr . tcp dport
        ip saddr 2.2.2.2 tcp dport 80 accept            { 1.1.1.1 . 22, 2.2.2.2 . 80 } accept

    A concatenation set is, here and in real nftables, an INTERNED NAMED set
    (NFT_SET_CONCAT): the parser mints a fresh `__setN`, pushes its per-field packed
    elements onto the table's set declarations, and lowers the inline `{ … }` to
    [MConcatSet ([f1;f2], neg, "__setN")] — a reference resolved at run time from
    [e_set (pkt_env p) "__setN"], matched by [concat_set_mem] (the kernel's per-field
    cross-product).  So this pass needs NO new constructor: it lifts the merge to the
    TABLE / [set_decls] level, minting `__setN` with a fresh counter, reusing the
    EXISTING [MConcatSet] / [sd_sets] / [concat_set_mem] machinery — exactly as the
    value->set pass reuses the single-field instance of the SAME [MConcatSet].

    The soundness backbone is the same first-match argument as [eval_rules_merge2]:
    a run of adjacent rules `(f1=a_i, f2=b_i) -> w` (sharing every other statement,
    the two fields, the loadability path, and the verdict) is verdict-equivalent to
    ONE rule whose head matches the DISJUNCTION over [i] of the per-row conjunctions
    `f1=a_i AND f2=b_i` — which is exactly a concatenation set of the tuples
    `{ a_i . b_i }`.  The new ingredient over the single-field case is the per-field
    CROSS-PRODUCT membership certificate [concat_in_iv_two_points]: a stored element
    packed as [pad_slot a ++ b] (each field in its register slot, last field taking
    the remainder) is matched iff BOTH fields' point tests hold — the literal
    two-field conjunction.

    Guarded by the same fixed-width side-condition ([field_fixed_len]) on BOTH
    fields and a fresh-name discipline ([setname_inj]).  Every top-level theorem is
    axiom-free (Print Assumptions: Closed under the global context). *)

From Stdlib Require Import Ascii String.
From Stdlib Require Import List PeanoNat Bool Lia Wellfounded Arith.Wf_nat.
From Nft Require Import Bytes Packet Verdict Syntax Bytecode Semantics Optimize
  Optimize_Merge.
Import ListNotations.
Local Open Scope nat_scope.

(** ** Packing a two-field point element into a concatenation-set bound.

    The kernel lays out a concatenated key by placing each field in its own 4-byte
    register SLOT.  [pad_slot v] is [v] padded with trailing zeros up to its register
    slot width ([reg_slot (length v)]); a two-field point element is [pad_slot a ++ b]
    (the LAST field takes the remainder, so it needs no padding for the membership
    test, which only [firstn (length b)]s it). *)
Definition pad_slot (v : data) : data := v ++ List.repeat 0 (reg_slot (List.length v) - List.length v).

Lemma pad_slot_len : forall v, List.length (pad_slot v) = reg_slot (List.length v).
Proof.
  intro v. unfold pad_slot. rewrite List.length_app, List.repeat_length.
  unfold reg_slot.
  pose proof (Nat.div_mod (List.length v + 3) 4 ltac:(lia)) as Hdm.
  pose proof (Nat.mod_upper_bound (List.length v + 3) 4 ltac:(lia)) as Hub.
  (* n+3 = 4*((n+3)/4) + (n+3) mod 4, with the remainder < 4, so 4*q >= n *)
  lia.
Qed.

Lemma pad_slot_firstn : forall v, List.firstn (List.length v) (pad_slot v) = v.
Proof.
  intro v. unfold pad_slot.
  rewrite List.firstn_app, Nat.sub_diag, List.firstn_O, List.app_nil_r.
  apply List.firstn_all.
Qed.

(** A two-field packed point element. *)
Definition pack2 (a b : data) : data := pad_slot a ++ b.

(** *** The two-field cross-product membership certificate.

    A stored CONCATENATION-set element [(pack2 a b, pack2 a b)] is matched by the
    two-field key [[va; vb]] iff [va] equals [a] AND [vb] equals [b] (each field's
    point test).  This is the literal two-field conjunction that mirrors
    [data_in_iv_point] in the single-field case. *)
Lemma concat_in_iv_two_points : forall va vb a b,
  List.length va = List.length a ->
  List.length vb = List.length b ->
  concat_in_iv [va; vb] (pack2 a b, pack2 a b)
  = andb (data_eqb va a) (data_eqb vb b).
Proof.
  intros va vb a b Hla Hlb.
  unfold concat_in_iv. cbn [map].
  (* slots = [reg_slot la; reg_slot lb]; split_by 2 widths = [firstn slot1; remainder] *)
  cbn [split_by].
  unfold pack2.
  (* fst/snd of the iv are both (pad_slot a ++ b) *)
  cbn [fst snd].
  (* firstn (reg_slot (length va)) (pad_slot a ++ b) : reg_slot(length va) = length(pad_slot a) *)
  assert (Hpa : reg_slot (List.length va) = List.length (pad_slot a)).
  { rewrite pad_slot_len. rewrite Hla. reflexivity. }
  rewrite Hpa.
  rewrite List.firstn_app, Nat.sub_diag, List.firstn_O, List.app_nil_r, List.firstn_all.
  rewrite List.skipn_app, Nat.sub_diag, List.skipn_O, List.skipn_all2 by lia.
  cbn [List.app].
  (* combine [va;vb] (combine [pad_slot a; b] [pad_slot a; b]) *)
  cbn [combine].
  cbn [forallb].
  rewrite Bool.andb_true_r.
  unfold field_in_iv. cbn [fst snd].
  (* field 1: firstn (length va) (pad_slot a) = a ; via length va = length a *)
  rewrite Hla, pad_slot_firstn.
  (* field 2: firstn (length vb) b = b *)
  rewrite Hlb, List.firstn_all.
  rewrite !data_le_antisym.
  rewrite (data_eqb_sym a va), (data_eqb_sym b vb).
  reflexivity.
Qed.

(** Membership in a TWO-element concat set of point tuples is the [orb] of the two
    two-field conjunctions. *)
Lemma concat_set_two_tuples_mem : forall va vb a1 b1 a2 b2,
  List.length va = List.length a1 -> List.length vb = List.length b1 ->
  List.length va = List.length a2 -> List.length vb = List.length b2 ->
  concat_set_mem [va; vb] [(pack2 a1 b1, pack2 a1 b1); (pack2 a2 b2, pack2 a2 b2)]
  = orb (andb (data_eqb va a1) (data_eqb vb b1))
        (andb (data_eqb va a2) (data_eqb vb b2)).
Proof.
  intros va vb a1 b1 a2 b2 H1 H2 H3 H4.
  unfold concat_set_mem. cbn [existsb].
  rewrite (concat_in_iv_two_points va vb a1 b1 H1 H2).
  rewrite (concat_in_iv_two_points va vb a2 b2 H3 H4).
  rewrite Bool.orb_false_r. reflexivity.
Qed.

(** *** The matchcond-level disjunction certificate for the merged concat head.

    The merged head [MConcatSet [f1;f2] false name], when [name] resolves to the two
    packed tuples and both fields are fixed-width matching the stored values, tests
    exactly the [orb] of the two per-row conjunctions
      [ (f1=a1 AND f2=b1) OR (f1=a2 AND f2=b2) ]
    where each [fi=x] is the original [MCmp fi CEq x] test. *)
Lemma concat_two_fields_certificate : forall f1 f2 a1 b1 a2 b2 name q,
  e_set (pkt_env q) name = [(pack2 a1 b1, pack2 a1 b1); (pack2 a2 b2, pack2 a2 b2)] ->
  (field_loadable f1 q = true -> List.length (field_value f1 q) = List.length a1) ->
  (field_loadable f2 q = true -> List.length (field_value f2 q) = List.length b1) ->
  (field_loadable f1 q = true -> List.length (field_value f1 q) = List.length a2) ->
  (field_loadable f2 q = true -> List.length (field_value f2 q) = List.length b2) ->
  eval_matchcond (MConcatSet [f1; f2] false name) q
  = orb (andb (eval_matchcond (MCmp f1 CEq a1) q) (eval_matchcond (MCmp f2 CEq b1) q))
        (andb (eval_matchcond (MCmp f1 CEq a2) q) (eval_matchcond (MCmp f2 CEq b2) q)).
Proof.
  intros f1 f2 a1 b1 a2 b2 name q Hset Ha1 Hb1 Ha2 Hb2.
  (* compute the two RHS MCmp tests *)
  assert (Em1a : forall x, eval_matchcond (MCmp f1 CEq x) q
                 = field_loadable f1 q && eval_cmp CEq (field_value f1 q) x).
  { intro x. reflexivity. }
  assert (Em2b : forall x, eval_matchcond (MCmp f2 CEq x) q
                 = field_loadable f2 q && eval_cmp CEq (field_value f2 q) x).
  { intro x. reflexivity. }
  rewrite !Em1a, !Em2b.
  unfold eval_matchcond, eval_matchcond_body.
  cbn [match_loadable fields_loadable forallb].
  rewrite Bool.andb_true_r.
  destruct (field_loadable f1 q) eqn:Hf1; cbn [andb];
    [| (* f1 not loadable: merged head false; RHS both rows have f1 conjunct false *)
       reflexivity ].
  destruct (field_loadable f2 q) eqn:Hf2; cbn [andb];
    [| (* f2 not loadable: merged head false; RHS both rows have f2 conjunct false *)
       rewrite !Bool.andb_false_r; reflexivity ].
  specialize (Ha1 eq_refl). specialize (Hb1 eq_refl).
  specialize (Ha2 eq_refl). specialize (Hb2 eq_refl).
  cbn [map xorb].
  rewrite Hset.
  (* membership step: [apply] (not [rewrite]) so full conversion bridges the
     [data] / [list byte] list-element annotation. *)
  etransitivity;
    [ apply (concat_set_two_tuples_mem (field_value f1 q) (field_value f2 q)
               a1 b1 a2 b2 Ha1 Hb1 Ha2 Hb2) | ].
  (* each MCmp f CEq x reduces to data_eqb (firstn (length x) (field_value f q)) x;
     length guard collapses firstn to the whole value *)
  unfold eval_cmp.
  rewrite <- Ha1, <- Hb1, <- Ha2, <- Hb2, !List.firstn_all.
  reflexivity.
Qed.

(** ** The merged concat-set rule and the two originals.

    The merged rule has a SINGLE head match — the concat set over [[f1;f2]] — atop
    the shared tail [body]: [mk_head (MConcatSet [f1;f2] false name) body r1].  Each
    original has TWO head matches (the two differing selectors) atop the SAME tail:
    [mk_head (MCmp f1 CEq a) (BMatch (MCmp f2 CEq b) :: body) r1].  A [BMatch] is
    transparent to [body_synproxy_stops] / [body_has_notrack] / [body_thread], so the
    merged rule's outcome and end-loadability coincide with each original's, and its
    head loadability/applicability is the per-field cross-product the certificate
    pins down. *)

Definition orig_rule2 (f1 f2 : field) (a b : data) (body : list body_item) (r1 : rule) : rule :=
  mk_head (MCmp f1 CEq a) (BMatch (MCmp f2 CEq b) :: body) r1.

Definition merged_rule2 (f1 f2 : field) (name : String.string) (body : list body_item) (r1 : rule) : rule :=
  mk_head (MConcatSet [f1; f2] false name) body r1.

(* A leading [BMatch] is transparent to the synproxy-stop / notrack predicates and
   to [body_thread], so the originals' tail [BMatch m2 :: body] threads exactly like
   [body]. *)
Lemma synproxy_stops_bmatch : forall m body p,
  body_synproxy_stops (BMatch m :: body) p = body_synproxy_stops body p.
Proof. reflexivity. Qed.

Lemma has_notrack_bmatch : forall m body,
  body_has_notrack (BMatch m :: body) = body_has_notrack body.
Proof. reflexivity. Qed.

Lemma body_thread_bmatch : forall m body p,
  body_thread (BMatch m :: body) p = body_thread body p.
Proof. intros. unfold body_thread. rewrite has_notrack_bmatch. reflexivity. Qed.

(** *** The two-field concat merge on a two-rule prefix.

    Given the disjunction certificate (the merged head is the [orb] of the two
    per-row conjunctions [f1=a_i AND f2=b_i]) and that BOTH fields load the same
    width as their matched values, the merged rule replaces the adjacent pair and
    preserves [eval_rules] on every packet.  This is the two-field analogue of
    [eval_rules_value_merge] / [eval_rules_range_value_merge], discharged through the
    abstract [eval_rules_merge2]. *)
Theorem eval_rules_concat_merge2 : forall f1 f2 a1 b1 a2 b2 name body r1 rest p,
  eval_matchcond (MConcatSet [f1; f2] false name) p
    = orb (andb (eval_matchcond (MCmp f1 CEq a1) p) (eval_matchcond (MCmp f2 CEq b1) p))
          (andb (eval_matchcond (MCmp f1 CEq a2) p) (eval_matchcond (MCmp f2 CEq b2) p)) ->
  match_loadable (MConcatSet [f1; f2] false name) p
    = match_loadable (MCmp f1 CEq a1) p && match_loadable (MCmp f2 CEq b1) p ->
  match_loadable (MConcatSet [f1; f2] false name) p
    = match_loadable (MCmp f1 CEq a2) p && match_loadable (MCmp f2 CEq b2) p ->
  eval_rules (merged_rule2 f1 f2 name body r1 :: rest) p
  = eval_rules (orig_rule2 f1 f2 a1 b1 body r1
                :: orig_rule2 f1 f2 a2 b2 body r1 :: rest) p.
Proof.
  intros f1 f2 a1 b1 a2 b2 name body r1 rest p Hcert Hl1 Hl2.
  unfold merged_rule2, orig_rule2.
  apply eval_rules_merge2.
  - (* loadable merged = loadable orig1 *)
    rewrite !rule_loadable_mk_head.
    rewrite synproxy_stops_bmatch, body_thread_bmatch.
    cbn [body_loadable_walk body_item_loadable].
    rewrite Hl1. cbn [match_loadable].
    rewrite <- !Bool.andb_assoc. reflexivity.
  - rewrite !rule_loadable_mk_head.
    rewrite synproxy_stops_bmatch, body_thread_bmatch.
    cbn [body_loadable_walk body_item_loadable].
    rewrite Hl2. cbn [match_loadable].
    rewrite <- !Bool.andb_assoc. reflexivity.
  - rewrite !outcome_mk_head.
    rewrite synproxy_stops_bmatch, body_thread_bmatch. reflexivity.
  - rewrite !outcome_mk_head.
    rewrite synproxy_stops_bmatch, body_thread_bmatch. reflexivity.
  - rewrite !rule_applies_mk_head. rewrite Hcert.
    cbn [rule_applies_walk].
    (* (c1 || c2) && W  vs  (m1a && (m2b && W)) || (m1a' && (m2b' && W)) *)
    rewrite Bool.andb_orb_distrib_l.
    rewrite !Bool.andb_assoc. reflexivity.
Qed.

(** ** Fresh-name minting for the concat set (same unary scheme as the value->set
    pass; reuses [setname] / [setname_inj] from [Optimize_Merge]). *)

(** Recognise a concat-merge-eligible head [BMatch (MCmp f1 CEq a) ::
    BMatch (MCmp f2 CEq b) :: rest]. *)
Definition head_value2 (r : rule)
  : option (field * data * field * data * list body_item) :=
  match r_body r with
  | BMatch (MCmp f1 CEq a) :: BMatch (MCmp f2 CEq b) :: rest =>
      Some (f1, a, f2, b, rest)
  | _ => None
  end.

(** Two rules form an eligible adjacent CONCAT-merge pair iff their heads are
    [MCmp f1 CEq a_i] / [MCmp f2 CEq b_i] over the SAME two fixed-width fields
    [f1],[f2] (in the SAME order), with the SAME tail [rest], the SAME end-fields,
    and the two TUPLES [(a1,b1)] / [(a2,b2)] DISTINCT (otherwise it is a duplicate,
    not a merge).  This is nft's two-differing-dimension eligibility. *)
Definition concat_merge_pair (r1 r2 : rule)
  : option (field * field * data * data * data * data * list body_item) :=
  match head_value2 r1, head_value2 r2 with
  | Some (f1, a1, g1, b1, rest1), Some (f2, a2, g2, b2, rest2) =>
      if field_eq_dec f1 f2 then
      if field_eq_dec g1 g2 then
      if list_eq_dec body_item_eq_dec rest1 rest2 then
      match field_fixed_len f1, field_fixed_len g1 with
      | Some lf, Some lg =>
        if Nat.eq_dec lf (length a1) then
        if Nat.eq_dec lf (length a2) then
        if Nat.eq_dec lg (length b1) then
        if Nat.eq_dec lg (length b2) then
        (* distinct tuples: not a duplicate *)
        if (if list_eq_dec Nat.eq_dec a1 a2 then
              if list_eq_dec Nat.eq_dec b1 b2 then true else false
            else false)
        then None
        else
        (* compare the two rules with a COMMON head (r1's values for both), so the
           test checks ONLY that r1 and r2 agree on every END field (verdict/vmap/
           nat/…) — the heads legitimately differ in their two values.
           [rule_end_eqb] is the compact boolean equivalent of [rule_eq_dec] on the
           two [orig_rule2] shells (both are [mk_head] of the SAME head/body over
           r1 / r2; see [rule_end_eqb_mk_head]); it keeps extraction small. *)
        if rule_end_eqb r1 r2
        then Some (f1, g1, a1, b1, a2, b2, rest1)
        else None
        else None else None else None else None
      | _, _ => None
      end
      else None else None else None
  | _, _ => None
  end.

(** When a concat-merge fires, the two input rules are EXACTLY the [orig_rule2]
    shells over the same two fixed-width fields. *)
Lemma concat_merge_pair_shape : forall r1 r2 f1 f2 a1 b1 a2 b2 body,
  concat_merge_pair r1 r2 = Some (f1, f2, a1, b1, a2, b2, body) ->
  r1 = orig_rule2 f1 f2 a1 b1 body r1 /\
  r2 = orig_rule2 f1 f2 a2 b2 body r1 /\
  field_fixed_len f1 = Some (length a1) /\ field_fixed_len f1 = Some (length a2) /\
  field_fixed_len f2 = Some (length b1) /\ field_fixed_len f2 = Some (length b2).
Proof.
  intros r1 r2 f1 f2 a1 b1 a2 b2 body H. unfold concat_merge_pair in H.
  destruct (head_value2 r1) as [[[[[fa1 ua1] ga1] ub1] s1] |] eqn:H1; [| discriminate].
  destruct (head_value2 r2) as [[[[[fa2 ua2] ga2] ub2] s2] |] eqn:H2; [| discriminate].
  unfold head_value2 in H1, H2.
  destruct (r_body r1) as [| [m1 | s1'] b1'] eqn:Eb1; try discriminate.
  destruct m1 as [ | | | | f1' op1 v1' | | | | | | | | ]; try discriminate.
  destruct op1; try discriminate.
  destruct b1' as [| [m1b | s1b] b1'']; try discriminate.
  destruct m1b as [ | | | | g1' op1b v1b' | | | | | | | | ]; try discriminate.
  destruct op1b; try discriminate. inversion H1; subst fa1 ua1 ga1 ub1 s1.
  destruct (r_body r2) as [| [m2 | s2'] b2'] eqn:Eb2; try discriminate.
  destruct m2 as [ | | | | f2' op2 v2' | | | | | | | | ]; try discriminate.
  destruct op2; try discriminate.
  destruct b2' as [| [m2b | s2b] b2'']; try discriminate.
  destruct m2b as [ | | | | g2' op2b v2b' | | | | | | | | ]; try discriminate.
  destruct op2b; try discriminate. inversion H2; subst fa2 ua2 ga2 ub2 s2.
  destruct (field_eq_dec f1' f2') as [Ef |]; [| discriminate]. subst f2'.
  destruct (field_eq_dec g1' g2') as [Eg |]; [| discriminate]. subst g2'.
  destruct (list_eq_dec body_item_eq_dec b1'' b2'') as [Es |]; [| discriminate]. subst b2''.
  destruct (field_fixed_len f1') as [lf |] eqn:Hfxf; [| discriminate].
  destruct (field_fixed_len g1') as [lg |] eqn:Hfxg; [| discriminate].
  destruct (Nat.eq_dec lf (length v1')) as [Elf1 |]; [| discriminate].
  destruct (Nat.eq_dec lf (length v2')) as [Elf2 |]; [| discriminate].
  destruct (Nat.eq_dec lg (length v1b')) as [Elg1 |]; [| discriminate].
  destruct (Nat.eq_dec lg (length v2b')) as [Elg2 |]; [| discriminate].
  destruct (if list_eq_dec Nat.eq_dec v1' v2' then
              if list_eq_dec Nat.eq_dec v1b' v2b' then true else false else false);
    [discriminate |].
  destruct (rule_end_eqb r1 r2) eqn:Eeqb; [| discriminate].
  pose proof (proj1 (rule_end_eqb_mk_head (MCmp f1' CEq v1')
                       (BMatch (MCmp g1' CEq v1b') :: b1'') r1 r2) Eeqb) as Eshell.
  unfold orig_rule2 in Eshell.
  inversion H; subst f1 f2 a1 b1 a2 b2 body. clear H.
  assert (Hr1 : r1 = orig_rule2 f1' g1' v1' v1b' b1'' r1).
  { unfold orig_rule2, mk_head. rewrite <- Eb1. destruct r1; reflexivity. }
  split; [exact Hr1 |].
  split.
  - assert (Hr2 : r2 = orig_rule2 f1' g1' v2' v2b' b1'' r2).
    { unfold orig_rule2, mk_head. rewrite <- Eb2. destruct r2; reflexivity. }
    rewrite Hr2. unfold orig_rule2, mk_head in Eshell |- *.
    injection Eshell as Eva Evm Ena Etp Efw Equ Eaf.
    rewrite Eva, Evm, Ena, Etp, Efw, Equ, Eaf. reflexivity.
  - rewrite Hfxf, Hfxg. repeat split; f_equal; congruence.
Qed.

(** ** The executable concat-set merge pass.

    On each adjacent eligible pair it mints a fresh [setname n], prepends the two
    packed point tuples [(pack2 a1 b1, …); (pack2 a2 b2, …)] to [sd_sets], and
    rewrites the pair into ONE [MConcatSet [f1;f2] false __setN] rule with the shared
    tail and verdict. *)
Fixpoint optimize_rules_concat (n : nat) (d : set_decls) (rs : list rule)
  : nat * set_decls * list rule :=
  match rs with
  | r1 :: ((r2 :: rest) as tl) =>
      match concat_merge_pair r1 r2 with
      | Some (f1, f2, a1, b1, a2, b2, body) =>
          let name := setname n in
          let d' := {| sd_sets := (name, [(pack2 a1 b1, pack2 a1 b1);
                                          (pack2 a2 b2, pack2 a2 b2)]) :: sd_sets d;
                       sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} in
          let merged := merged_rule2 f1 f2 name body r1 in
          let '(n'', d'', rest') := optimize_rules_concat (S n) d' rest in
          (n'', d'', merged :: rest')
      | None =>
          let '(n'', d'', tl') := optimize_rules_concat n d tl in
          (n'', d'', r1 :: tl')
      end
  | _ => (n, d, rs)
  end.

Lemma optimize_rules_concat_cons2 : forall n d r1 r2 rest,
  optimize_rules_concat n d (r1 :: r2 :: rest) =
  match concat_merge_pair r1 r2 with
  | Some (f1, f2, a1, b1, a2, b2, body) =>
      let name := setname n in
      let d' := {| sd_sets := (name, [(pack2 a1 b1, pack2 a1 b1);
                                      (pack2 a2 b2, pack2 a2 b2)]) :: sd_sets d;
                   sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} in
      let merged := merged_rule2 f1 f2 name body r1 in
      let '(n'', d'', rest') := optimize_rules_concat (S n) d' rest in
      (n'', d'', merged :: rest')
  | None =>
      let '(n'', d'', tl') := optimize_rules_concat n d (r2 :: rest) in
      (n'', d'', r1 :: tl')
  end.
Proof. reflexivity. Qed.

Definition optimize_chain_concat (n : nat) (d : set_decls) (c : chain)
  : nat * set_decls * chain :=
  let '(n', d', rs') := optimize_rules_concat n d (c_rules c) in
  (n', d', {| c_policy := c_policy c; c_rules := rs' |}).

(** *** Freshness bookkeeping: the pass only PREPENDS [sd_sets] entries keyed by
    [setname k] with [n <= k < n']. *)
Lemma optimize_rules_concat_assoc_stable : forall rs n d n' d' rs' nm X,
  optimize_rules_concat n d rs = (n', d', rs') ->
  (forall k, n <= k -> nm <> setname k) ->
  assoc_str nm (sd_sets d') X = assoc_str nm (sd_sets d) X.
Proof.
  induction rs as [rs H0] using (induction_ltof1 _ (@length rule)).
  intros n d n' d' rs' nm X H Hnm.
  destruct rs as [| r1 [| r2 rest] ].
  - cbn in H. inversion H; subst; reflexivity.
  - cbn in H. inversion H; subst; reflexivity.
  - rewrite optimize_rules_concat_cons2 in H. cbv zeta in H.
    destruct (concat_merge_pair r1 r2)
      as [[[[[[[f1 f2] a1] b1] a2] b2] body] |] eqn:Evm.
    + destruct (optimize_rules_concat (S n)
                  {| sd_sets := (setname n, [(pack2 a1 b1, pack2 a1 b1);
                                            (pack2 a2 b2, pack2 a2 b2)]) :: sd_sets d;
                     sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest)
        as [[m'' dd''] rr''] eqn:Erec.
      inversion H; subst n' d' rs'. clear H.
      erewrite (H0 rest); [ | unfold ltof; cbn; lia | exact Erec | ].
      * cbn [sd_sets assoc_str].
        destruct (String.eqb nm (setname n)) eqn:Eqn.
        -- apply String.eqb_eq in Eqn. exfalso. apply (Hnm n); [lia | exact Eqn].
        -- reflexivity.
      * intros k Hk. apply Hnm. lia.
    + destruct (optimize_rules_concat n d (r2 :: rest)) as [[m'' dd''] rr''] eqn:Erec.
      inversion H. subst n' d' rs'. clear H.
      eapply (H0 (r2 :: rest)); [ unfold ltof; cbn; lia | exact Erec | exact Hnm ].
Qed.

(** The merged head's two-field loadability splits as the per-field conjunction
    (used to discharge [eval_rules_concat_merge2]'s loadability obligations). *)
Lemma concat_match_loadable_split : forall f1 f2 name p,
  match_loadable (MConcatSet [f1; f2] false name) p
  = match_loadable (MCmp f1 CEq []) p && match_loadable (MCmp f2 CEq []) p.
Proof.
  intros f1 f2 name p. cbn [match_loadable fields_loadable forallb].
  rewrite Bool.andb_true_r. reflexivity.
Qed.

(** *** The executable CONCAT merge, proved verdict-preserving END-TO-END over the
    table semantics with the synthesised concat set in scope, axiom-free.

    On clean rules with the minted names fresh for [d], the rewritten [rs'] under the
    augmented declarations [d'] yields the SAME verdict on every packet as [rs] under
    [d].  The merged head's `__setN` lookup resolves to its two packed tuples
    (freshness + injectivity); [concat_two_fields_certificate] turns it into the [orb]
    of the two per-row conjunctions; [eval_rules_concat_merge2] collapses the pair;
    the clean tail is env-irrelevant. *)
(** *** The CHAIN-level entry (the [eval_chain] specialisation). *)
(** * N-WAY concatenation-set merge: fold a whole RUN of two-selector-differing rules
      into ONE concat set with N tuples (matching nft -o).

    The pairwise pass above merges exactly two rules; nft -o consolidates a whole run
    [ip saddr A1 dport B1 accept; A2 B2; A3 B3] into ONE
    [ip saddr . tcp dport { A1.B1, A2.B2, A3.B3 } accept].  This section delivers the
    N-way pass, reusing the family-agnostic [eval_rules_run_collapse] from
    [Optimize_Merge] (all rules in the run share the SAME verdict). *)

Definition pack_tuple (ab : data * data) : data * data :=
  (pack2 (fst ab) (snd ab), pack2 (fst ab) (snd ab)).

(** N-element two-field concat membership = [existsb] of the per-row conjunctions. *)
Lemma concat_set_mem_existsb : forall va vb tuples,
  (forall a b, In (a, b) tuples -> List.length va = List.length a) ->
  (forall a b, In (a, b) tuples -> List.length vb = List.length b) ->
  concat_set_mem [va; vb] (map pack_tuple tuples)
  = existsb (fun ab => andb (data_eqb va (fst ab)) (data_eqb vb (snd ab))) tuples.
Proof.
  intros va vb tuples. induction tuples as [| [a b] tuples IH]; intros Ha Hb;
    [reflexivity|].
  cbn [map existsb]. unfold concat_set_mem in *. cbn [existsb].
  unfold pack_tuple at 1. cbn [fst snd].
  rewrite (concat_in_iv_two_points va vb a b
             (Ha a b (or_introl eq_refl)) (Hb a b (or_introl eq_refl))).
  rewrite IH; [ reflexivity
              | intros a' b' Hin; apply (Ha a' b'); right; exact Hin
              | intros a' b' Hin; apply (Hb a' b'); right; exact Hin ].
Qed.

(** Matchcond-level N-way concat certificate: the merged head is the [existsb] over
    the run of the per-row two-field conjunctions. *)
Lemma concat_two_fields_certificate_N : forall f1 f2 tuples name q,
  e_set (pkt_env q) name = map pack_tuple tuples ->
  (forall a b, In (a, b) tuples -> field_loadable f1 q = true ->
               List.length (field_value f1 q) = List.length a) ->
  (forall a b, In (a, b) tuples -> field_loadable f2 q = true ->
               List.length (field_value f2 q) = List.length b) ->
  eval_matchcond (MConcatSet [f1; f2] false name) q
  = existsb (fun ab => andb (eval_matchcond (MCmp f1 CEq (fst ab)) q)
                            (eval_matchcond (MCmp f2 CEq (snd ab)) q)) tuples.
Proof.
  intros f1 f2 tuples name q Hset Ha Hb.
  unfold eval_matchcond at 1, eval_matchcond_body at 1.
  cbn [match_loadable fields_loadable forallb]. rewrite Bool.andb_true_r.
  destruct (field_loadable f1 q) eqn:Hf1; cbn [andb].
  - destruct (field_loadable f2 q) eqn:Hf2; cbn [andb].
    + (* both load: reduce both sides over the run *)
      cbn [xorb]. rewrite Hset.
      change (map (fun f => field_value f q) [f1; f2])
        with [field_value f1 q; field_value f2 q].
      etransitivity;
        [ apply (concat_set_mem_existsb (field_value f1 q) (field_value f2 q) tuples
                   (fun a b Hin => Ha a b Hin eq_refl) (fun a b Hin => Hb a b Hin eq_refl)) | ].
      apply existsb_ext. intros [a b] Hin. cbn [fst snd].
      rewrite (eval_mcmp_point f1 a q Hf1 (Ha a b Hin eq_refl)).
      rewrite (eval_mcmp_point f2 b q Hf2 (Hb a b Hin eq_refl)).
      reflexivity.
    + (* f2 fails: merged false; every row's f2 conjunct false *)
      symmetry. apply existsb_false_forall. intros [a b] _. cbn [fst snd].
      rewrite (eval_mcmp_point_unload f2 b q Hf2). apply Bool.andb_false_r.
  - (* f1 fails: merged false; every row's f1 conjunct false *)
    symmetry. apply existsb_false_forall. intros [a b] _. cbn [fst snd].
    rewrite (eval_mcmp_point_unload f1 a q Hf1). reflexivity.
Qed.

(** ** Executable N-WAY concat pass.

    [take_concat_run r1 rest] collects the maximal prefix of rules that each
    concat-merge with the canonical first rule [r1], returning their tuples [(ai,bi)]
    and the leftover; [optimize_rules_concatN] folds the whole run [r1 :: matched]
    into ONE [MConcatSet [f1;f2] false __setN] over the N packed tuples. *)
Fixpoint take_concat_run (r1 : rule) (rest : list rule)
  : list (data * data) * list rule :=
  match rest with
  | [] => ([], [])
  | r2 :: tl =>
      match concat_merge_pair r1 r2 with
      | Some (_, _, _, _, a2, b2, _) =>
          let '(ts, rest') := take_concat_run r1 tl in ((a2, b2) :: ts, rest')
      | None => ([], rest)
      end
  end.

Fixpoint optimize_rules_concatN (fuel n : nat) (d : set_decls) (rs : list rule)
  : nat * set_decls * list rule :=
  match fuel with
  | O => (n, d, rs)
  | S fuel' =>
    match rs with
    | r1 :: ((_ :: _) as rest) =>
        match head_value2 r1 with
        | Some (f1, a1, f2, b1, body) =>
            match take_concat_run r1 rest with
            | ([], _) =>
                let '(n'', d'', rest') := optimize_rules_concatN fuel' n d rest in
                (n'', d'', r1 :: rest')
            | ((_ :: _) as ts, rest') =>
                let name := setname n in
                let tuples := (a1, b1) :: ts in
                let d' := {| sd_sets := (name, map pack_tuple tuples) :: sd_sets d;
                             sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} in
                let merged := merged_rule2 f1 f2 name body r1 in
                let '(n'', d'', rest'') := optimize_rules_concatN fuel' (S n) d' rest' in
                (n'', d'', merged :: rest'')
            end
        | None =>
            let '(n'', d'', rest') := optimize_rules_concatN fuel' n d rest in
            (n'', d'', r1 :: rest')
        end
    | _ => (n, d, rs)
    end
  end.

Definition optimize_chain_concatN (n : nat) (d : set_decls) (c : chain)
  : nat * set_decls * chain :=
  let '(n', d', rs') := optimize_rules_concatN (length (c_rules c)) n d (c_rules c) in
  (n', d', {| c_policy := c_policy c; c_rules := rs' |}).

Lemma optimize_rules_concatN_consSS : forall fuel n d r1 r2 rest,
  optimize_rules_concatN (S fuel) n d (r1 :: r2 :: rest) =
  match head_value2 r1 with
  | Some (f1, a1, f2, b1, body) =>
      match take_concat_run r1 (r2 :: rest) with
      | ([], _) =>
          let '(n'', d'', rest') := optimize_rules_concatN fuel n d (r2 :: rest) in
          (n'', d'', r1 :: rest')
      | ((_ :: _) as ts, rest') =>
          let name := setname n in
          let tuples := (a1, b1) :: ts in
          let d' := {| sd_sets := (name, map pack_tuple tuples) :: sd_sets d;
                       sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} in
          let merged := merged_rule2 f1 f2 name body r1 in
          let '(n'', d'', rest'') := optimize_rules_concatN fuel (S n) d' rest' in
          (n'', d'', merged :: rest'')
      end
  | None =>
      let '(n'', d'', rest') := optimize_rules_concatN fuel n d (r2 :: rest) in
      (n'', d'', r1 :: rest')
  end.
Proof. reflexivity. Qed.

(** orig_rule2's loadability / outcome are INDEPENDENT of the two head values (the
    head [MCmp]s contribute only their field loadability, which is value-free), and
    its [rule_applies] is the per-row two-field conjunction times the body walk. *)
Lemma orig_rule2_loadable_indep : forall f1 f2 a b a' b' body r1 p,
  rule_loadable (orig_rule2 f1 f2 a b body r1) p
  = rule_loadable (orig_rule2 f1 f2 a' b' body r1) p.
Proof.
  intros. unfold orig_rule2. rewrite !rule_loadable_mk_head.
  rewrite !synproxy_stops_bmatch, !body_thread_bmatch.
  cbn [body_loadable_walk body_item_loadable match_loadable]. reflexivity.
Qed.

Lemma orig_rule2_outcome_indep : forall f1 f2 a b a' b' body r1 p,
  outcome (orig_rule2 f1 f2 a b body r1) p
  = outcome (orig_rule2 f1 f2 a' b' body r1) p.
Proof.
  intros. unfold orig_rule2. rewrite !outcome_mk_head.
  rewrite !synproxy_stops_bmatch, !body_thread_bmatch. reflexivity.
Qed.

Lemma orig_rule2_applies : forall f1 f2 a b body r1 p,
  rule_applies (orig_rule2 f1 f2 a b body r1) p
  = andb (andb (eval_matchcond (MCmp f1 CEq a) p) (eval_matchcond (MCmp f2 CEq b) p))
         (rule_applies_walk body p).
Proof.
  intros. unfold orig_rule2. rewrite rule_applies_mk_head.
  cbn [rule_applies_walk]. rewrite Bool.andb_assoc. reflexivity.
Qed.

Lemma merged_rule2_loadable_eq_orig : forall f1 f2 name a b body r1 p,
  rule_loadable (merged_rule2 f1 f2 name body r1) p
  = rule_loadable (orig_rule2 f1 f2 a b body r1) p.
Proof.
  intros. unfold merged_rule2, orig_rule2. rewrite !rule_loadable_mk_head.
  rewrite !synproxy_stops_bmatch, !body_thread_bmatch.
  cbn [body_loadable_walk body_item_loadable match_loadable fields_loadable forallb].
  rewrite Bool.andb_true_r, <- !Bool.andb_assoc. reflexivity.
Qed.

Lemma merged_rule2_outcome_eq_orig : forall f1 f2 name a b body r1 p,
  outcome (merged_rule2 f1 f2 name body r1) p
  = outcome (orig_rule2 f1 f2 a b body r1) p.
Proof.
  intros. unfold merged_rule2, orig_rule2. rewrite !outcome_mk_head.
  rewrite !synproxy_stops_bmatch, !body_thread_bmatch. reflexivity.
Qed.

Lemma merged_rule2_applies : forall f1 f2 name body r1 p,
  rule_applies (merged_rule2 f1 f2 name body r1) p
  = andb (eval_matchcond (MConcatSet [f1; f2] false name) p) (rule_applies_walk body p).
Proof.
  intros. unfold merged_rule2. rewrite rule_applies_mk_head. reflexivity.
Qed.

(** [concat_merge_pair] returns r1's fields/values in the canonical slots, forcing
    [r2] to be the orig_rule2 shell over r2's tuple. *)
Lemma concat_merge_pair_with_head : forall r1 r2 f1 a1 f2 b1 body fa aa fb bb a2 b2 body2,
  head_value2 r1 = Some (f1, a1, f2, b1, body) ->
  concat_merge_pair r1 r2 = Some (fa, fb, aa, bb, a2, b2, body2) ->
  fa = f1 /\ fb = f2 /\ aa = a1 /\ bb = b1 /\ body2 = body /\
  r2 = orig_rule2 f1 f2 a2 b2 body r1 /\
  field_fixed_len f1 = Some (length a2) /\ field_fixed_len f2 = Some (length b2).
Proof.
  intros r1 r2 f1 a1 f2 b1 body fa aa fb bb a2 b2 body2 Hhd Hvm.
  destruct (concat_merge_pair_shape r1 r2 fa fb aa bb a2 b2 body2 Hvm)
    as [Hr1 [Hr2 [Hx1 [Hx2 [Hx3 Hx4]]]]].
  assert (Hhd' : head_value2 r1 = Some (fa, aa, fb, bb, body2)).
  { rewrite Hr1 at 1. unfold head_value2, orig_rule2, mk_head. cbn [r_body]. reflexivity. }
  rewrite Hhd in Hhd'. inversion Hhd'; subst fa aa fb bb body2.
  repeat split; try assumption.
Qed.

Lemma take_concat_run_shape : forall r1 f1 a1 f2 b1 body rest ts rest',
  head_value2 r1 = Some (f1, a1, f2, b1, body) ->
  take_concat_run r1 rest = (ts, rest') ->
  rest = map (fun ab => orig_rule2 f1 f2 (fst ab) (snd ab) body r1) ts ++ rest'
  /\ (forall a b, In (a, b) ts -> field_fixed_len f1 = Some (length a))
  /\ (forall a b, In (a, b) ts -> field_fixed_len f2 = Some (length b)).
Proof.
  intros r1 f1 a1 f2 b1 body rest. induction rest as [| r2 tl IH]; intros ts rest' Hhd H.
  - cbn in H. inversion H; subst.
    split; [ reflexivity | split; intros a b []].
  - cbn in H. destruct (concat_merge_pair r1 r2)
      as [[[[[[[fa fb] aa] bb] a2] b2] bd] |] eqn:Evm.
    + destruct (take_concat_run r1 tl) as [ts0 rest0] eqn:Erec.
      inversion H; subst ts rest'. clear H.
      destruct (concat_merge_pair_with_head r1 r2 f1 a1 f2 b1 body fa aa fb bb a2 b2 bd
                  Hhd Evm) as [_ [_ [_ [_ [_ [Hr2 [Hfx1 Hfx2]]]]]]].
      destruct (IH ts0 rest0 Hhd eq_refl) as [Hsplit [Hall1 Hall2]].
      repeat split.
      * cbn [map app fst snd]. rewrite <- Hr2, <- Hsplit. reflexivity.
      * intros a b [Hab | Hin]; [ inversion Hab; subst; exact Hfx1 | apply (Hall1 a b Hin) ].
      * intros a b [Hab | Hin]; [ inversion Hab; subst; exact Hfx2 | apply (Hall2 a b Hin) ].
    + inversion H; subst ts rest'.
      split; [ reflexivity | split; intros a b []].
Qed.

Lemma take_concat_run_head_width : forall r1 f1 a1 f2 b1 body r2 rest ts rest',
  head_value2 r1 = Some (f1, a1, f2, b1, body) ->
  take_concat_run r1 (r2 :: rest) = (ts, rest') ->
  ts <> [] ->
  field_fixed_len f1 = Some (length a1) /\ field_fixed_len f2 = Some (length b1).
Proof.
  intros r1 f1 a1 f2 b1 body r2 rest ts rest' Hhd Hrun Hne.
  cbn in Hrun. destruct (concat_merge_pair r1 r2)
    as [[[[[[[fa fb] aa] bb] a2] b2] bd] |] eqn:Evm.
  - destruct (concat_merge_pair_shape r1 r2 fa fb aa bb a2 b2 bd Evm)
      as [Hr1 [_ [Hx1 [_ [Hx3 _]]]]].
    assert (Hhd' : head_value2 r1 = Some (fa, aa, fb, bb, bd)).
    { rewrite Hr1 at 1. unfold head_value2, orig_rule2, mk_head. cbn [r_body]. reflexivity. }
    rewrite Hhd in Hhd'. inversion Hhd'; subst fa aa fb bb bd. split; assumption.
  - destruct (take_concat_run r1 rest) as [ts0 rest0] eqn:Erec0.
    inversion Hrun; subst. contradiction.
Qed.

Lemma optimize_rules_concatN_assoc_stable : forall fuel n d rs n' d' rs' nm X,
  optimize_rules_concatN fuel n d rs = (n', d', rs') ->
  (forall k, n <= k -> nm <> setname k) ->
  assoc_str nm (sd_sets d') X = assoc_str nm (sd_sets d) X.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' nm X H Hnm.
  - cbn in H. inversion H; subst; reflexivity.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; reflexivity.
    + cbn in H. inversion H; subst; reflexivity.
    + rewrite optimize_rules_concatN_consSS in H.
      destruct (head_value2 r1) as [[[[[f1 a1] f2] b1] body] |] eqn:Ehd.
      * destruct (take_concat_run r1 (r2 :: rest)) as [ts rest'] eqn:Erun.
        destruct ts as [| t ts'].
        -- remember (optimize_rules_concatN fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst d'. clear Hn' Hr'.
           eapply (IH n d (r2 :: rest)); [symmetry; exact Erec | exact Hnm].
        -- cbv zeta in H.
           remember (optimize_rules_concatN fuel (S n)
                       {| sd_sets := (setname n, map pack_tuple ((a1,b1) :: t :: ts'))
                                     :: sd_sets d;
                          sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
             as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst d'. clear Hn' Hr'.
           erewrite (IH (S n) _ rest'); [ | symmetry; exact Erec | intros k Hk; apply Hnm; lia ].
           cbn [sd_sets assoc_str].
           destruct (String.eqb nm (setname n)) eqn:Eqn.
           ++ apply String.eqb_eq in Eqn. exfalso. apply (Hnm n); [lia | exact Eqn].
           ++ reflexivity.
      * remember (optimize_rules_concatN fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
        injection H as Hn' Hd' Hr'. subst d'. clear Hn' Hr'.
        eapply (IH n d (r2 :: rest)); [symmetry; exact Erec | exact Hnm].
Qed.

(** [existsb] of [conj && W] (W constant) factors as [(existsb conj) && W]. *)
Lemma existsb_andb_const : forall (A : Type) (g : A -> bool) (W : bool) (l : list A),
  existsb (fun x => andb (g x) W) l = andb (existsb g l) W.
Proof.
  induction l as [| a l IH]; intros; [ reflexivity |].
  cbn [existsb]. rewrite IH. rewrite Bool.andb_orb_distrib_l. reflexivity.
Qed.

(** Both head_value2-derived rule and the canonical orig_rule2 shell coincide. *)
Lemma head_value2_canon : forall r1 f1 a1 f2 b1 body,
  head_value2 r1 = Some (f1, a1, f2, b1, body) ->
  r1 = orig_rule2 f1 f2 a1 b1 body r1.
Proof.
  intros r1 f1 a1 f2 b1 body H. unfold head_value2 in H.
  destruct (r_body r1) as [| [m1 | s1] bb1] eqn:Eb; try discriminate.
  destruct m1 as [ | | | | g1 op1 u1 | | | | | | | | ]; try discriminate.
  destruct op1; try discriminate.
  destruct bb1 as [| [m2 | s2] bb2]; try discriminate.
  destruct m2 as [ | | | | g2 op2 u2 | | | | | | | | ]; try discriminate.
  destruct op2; try discriminate. inversion H; subst g1 u1 g2 u2 bb2.
  unfold orig_rule2, mk_head. rewrite <- Eb. destruct r1; reflexivity.
Qed.

(** *** Executable N-WAY concat merge: verdict-preserving end-to-end, axiom-free. *)
(** *** Chain-level N-WAY concat: verdict-preserving end-to-end, axiom-free. *)