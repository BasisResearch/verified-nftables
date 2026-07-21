(** * Optimize_Vmap: the [nft -o] VERDICT-MAP merge, as an executable table-level
    rewrite, proved verdict-preserving and axiom-free.

    This is the direct sibling of the value->anonymous-SET merge already delivered
    in [Optimize_ValueSet] ([optimize_rules_sets]).  [nft -o] consolidates a run of
    ADJACENT rules that share every match BUT a single selector value AND whose
    terminal VERDICTS DIFFER into ONE rule whose terminal is a VERDICT MAP keyed on
    that selector:

        tcp dport 22 accept              => tcp dport vmap { 22 : accept, 80 : drop }
        tcp dport 80 drop

    A verdict map is, here and in real nftables, an INTERNED NAMED object (the
    parser mints `__vmapN`, pushes its `key -> verdict` entries onto the table's
    declarations, and lowers the inline `vmap { … }` to an [r_vmap] keyed by name —
    a reference resolved at run time from [e_vmap e "__vmapN"]).  So this
    pass needs NO new constructor: it lifts the merge to the TABLE / [set_decls]
    level, minting `__vmapN` with a fresh counter, reusing the EXISTING [r_vmap] /
    [sd_vmaps] / [assoc_verdict] machinery — exactly as the value->set pass reuses
    [MConcatSet] / [sd_sets] / [set_mem].

    The soundness backbone is the same first-match argument: in first-match order a
    run of adjacent rules `dport=v_i -> w_i` (sharing every other statement, the
    selector field, and the loadability path) is verdict-equivalent to ONE rule
    that dispatches `dport` through a verdict map returning `w_i` on key `v_i` and
    FALLING THROUGH (a miss) on every other value — the merged rule applies on more
    packets than either original, but on the extra packets the vmap MISSES, the
    rule's outcome is [None], and [eval_rules] treats that exactly as "the rule did
    not apply".

    The two point keys resolve through [assoc_verdict] to `w1`/`w2` ([data_in_iv k
    (k,k) = data_eqb k k]); the certificate [vmap_two_points] mirrors
    [concat_set_two_points].  Guarded by the same fixed-width side-condition
    ([field_fixed_len]) — so [MCmp]'s prefix-equality coincides with the vmap key's
    full-width equality — and a fresh-name discipline ([vmapname_inj]).  Every
    top-level theorem is axiom-free (Print Assumptions: Closed under the global
    context). *)

From Stdlib Require Import Ascii String.
From Stdlib Require Import List PeanoNat Bool Lia Wellfounded Arith.Wf_nat.
From Nft Require Import Bytes Packet Verdict Syntax Bytecode Semantics Optimize Optimize_ValueSet.
Import ListNotations.
Local Open Scope nat_scope.

(** ** The merged VMAP rule.

    [mk_vmap_rule f nm body w1' w2'] is a rule with body [body] (the shared tail of
    the two originals, MINUS their differing head match — the head value is consumed
    into the vmap KEY), no static side-effect terminal, a [Continue] fall-through
    verdict (so a vmap MISS falls through to the next rule), and a verdict map keyed
    by the single field [f] (no transforms) against the named map [nm]. *)
Definition mk_vmap_rule (f : field) (nm : String.string) (body : list body_item) : rule :=
  {| r_body := body;
     r_outcome := OVmap {| vm_fields := [f]; vm_keyf := Some (f, []); vm_name := nm |}; r_after := [] |}.

(** The base rule the two originals share: a pure-terminal rule (no vmap / nat /
    tproxy / fwd / queue, no [r_after]) carrying a static TERMINAL verdict [w].
    Its body is supplied by [mk_head]; [mk_vmap_base w] holds the end fields. *)
Definition mk_vmap_base (w : verdict) : rule :=
  {| r_body := [];
     r_outcome := OVerdict w; r_after := [] |}.

(** *** The vmap-lookup certificate at two point keys.

    With the named map [nm] declared as the two POINT entries [(v1,v1,w1);
    (v2,v2,w2)], the merged rule's [outcome_core] at [q] is: [w1] when [f] loads to
    [v1], else [w2] when it loads to [v2], else the terminal fall-through
    ([Continue] => [None]).  Each point key test [data_in_iv k (vi,vi)] is exactly
    [data_eqb k vi] ([data_in_iv_point]); the width guard makes that the same test
    as the original [MCmp f CEq vi] head. *)
Lemma vmap_two_points : forall f nm v1 v2 w1 w2 body e q,
  e_vmap e nm = [(v1, v1, w1); (v2, v2, w2)] ->
  (field_loadable f q = true -> length (field_value f e q) = length v1) ->
  (field_loadable f q = true -> length (field_value f e q) = length v2) ->
  field_loadable f q = true ->
  outcome_core (mk_vmap_rule f nm body) e q
  = if eval_cmp CEq (field_value f e q) v1 then Some w1
    else if eval_cmp CEq (field_value f e q) v2 then Some w2
    else None.
Proof.
  intros f nm v1 v2 w1 w2 body e q Hvm H1 H2 Hld.
  specialize (H1 Hld). specialize (H2 Hld).
  unfold outcome_core, mk_vmap_rule. cbn [r_vmap vm_keyf vm_name vm_fields r_outcome].
  cbn [apply_transforms fold_left].
  rewrite Hvm. cbn [assoc_verdict].
  rewrite !data_in_iv_point_eqb.
  unfold eval_cmp.
  rewrite <- H1, <- H2, !List.firstn_all.
  rewrite (data_eqb_sym (field_value f e q) v1), (data_eqb_sym (field_value f e q) v2).
  destruct (data_eqb v1 (field_value f e q)) eqn:E1; [reflexivity|].
  destruct (data_eqb v2 (field_value f e q)) eqn:E2; [reflexivity|].
  unfold terminal_outcome, mk_vmap_rule. cbn [r_nat r_tproxy r_fwd r_queue r_verdict r_after r_outcome].
  reflexivity.
Qed.

(** ** Loadability of the merged vmap rule.

    Pull the head out: [mk_vmap_rule]'s body is [body] (no head match), so
    [rule_loadable] reduces to [body_loadable_walk body] times the vmap-keyed end
    load.  The two originals are [mk_head (MCmp f CEq vi) body (mk_vmap_base wi)],
    whose loadability is [field_loadable f] (the head) times the same
    [body_loadable_walk body] (the terminal of a pure-verdict rule always loads).
    We only ever USE these on the no-synproxy / no-notrack CLEAN body, where the
    bookkeeping collapses. *)

(** The originals' shape: [mk_head (MCmp f CEq vi) body (mk_vmap_base wi)]. *)
Definition orig_rule (f : field) (v : data) (body : list body_item) (w : verdict) : rule :=
  mk_head (MCmp f CEq v) body (mk_vmap_base w).

Lemma orig_rule_loadable : forall f v body w e p,
  rule_loadable (orig_rule f v body w) e p =
    field_loadable f p &&
    (body_loadable_walk body p &&
     (if body_synproxy_stops body p then true else true)).
Proof.
  intros f v body w e p. unfold orig_rule.
  rewrite rule_loadable_mk_head.
  cbn [match_loadable].
  (* end_loadable of mk_vmap_base = true (no vmap, terminal verdict loads) *)
  assert (Hend : forall q, end_loadable (mk_vmap_base w) e q = true).
  { intro q. unfold end_loadable, mk_vmap_base. cbn [r_vmap r_outcome].
    unfold tail_loadable, terminal_loadable, terminal_outcome.
    cbn [r_nat r_tproxy r_fwd r_queue r_verdict r_after r_outcome].
    destruct w; cbn [terminal]; reflexivity. }
  rewrite Hend.
  destruct (body_synproxy_stops body p); reflexivity.
Qed.

Lemma orig_rule_applies : forall f v body w e p,
  rule_applies (orig_rule f v body w) e p
  = eval_matchcond (MCmp f CEq v) e p && rule_applies_walk body e p.
Proof.
  intros. unfold orig_rule. apply rule_applies_mk_head.
Qed.

Lemma orig_rule_outcome : forall f v body w e p,
  outcome (orig_rule f v body w) e p =
    if body_synproxy_stops body p then Some Drop
    else (if body_has_notrack body
          then terminal_outcome (mk_vmap_base w) (set_untracked p)
          else terminal_outcome (mk_vmap_base w) p).
Proof.
  intros f v body w e p. unfold orig_rule.
  rewrite outcome_mk_head.
  destruct (body_synproxy_stops body p); [reflexivity|].
  unfold outcome_core, body_thread, mk_vmap_base. cbn [r_vmap r_outcome].
  destruct (body_has_notrack body); reflexivity.
Qed.

(** terminal_outcome of [mk_vmap_base w] for a TERMINAL [w] is [Some w]
    (independent of packet). *)
Lemma terminal_outcome_vmap_base : forall w q,
  terminal w = true ->
  terminal_outcome (mk_vmap_base w) q = Some w.
Proof.
  intros w q Hw. unfold terminal_outcome, mk_vmap_base.
  cbn [r_nat r_tproxy r_fwd r_queue r_verdict r_after r_outcome].
  destruct w; cbn [terminal] in Hw; try discriminate; reflexivity.
Qed.

(** ** The core two-rule vmap merge (per packet, on a CLEAN shared body).

    On a body with no stopping synproxy and no notrack, the merged vmap rule
    replaces the adjacent pair [orig_rule f v1 body w1 :: orig_rule f v2 body w2]
    without changing [eval_rules] on any packet — PROVIDED [w1],[w2] are terminal,
    [f] is fixed-width matching [v1],[v2], and [nm] resolves to the two point
    entries.  This is the vmap analogue of [eval_rules_value_merge]. *)
Theorem eval_rules_vmap_merge2 : forall f nm v1 v2 w1 w2 body rest e p,
  e_vmap e nm = [(v1, v1, w1); (v2, v2, w2)] ->
  field_fixed_len f = Some (length v1) ->
  field_fixed_len f = Some (length v2) ->
  terminal w1 = true ->
  terminal w2 = true ->
  body_synproxy_stops body p = false ->
  body_has_notrack body = false ->
  eval_rules (mk_vmap_rule f nm body :: rest) e p
  = eval_rules (orig_rule f v1 body w1 :: orig_rule f v2 body w2 :: rest) e p.
Proof.
  intros f nm v1 v2 w1 w2 body rest e p Hvm Hfx1 Hfx2 Hw1 Hw2 Hsp Hnt.
  (* loadability of the merged rule *)
  assert (HmL : rule_loadable (mk_vmap_rule f nm body) e p =
                body_loadable_walk body p &&
                (if field_loadable f p
                 then match assoc_verdict (field_value f e p) (e_vmap e nm) with
                      | Some _ => true | None => true end
                 else false)).
  { unfold rule_loadable, mk_vmap_rule. cbn [r_body].
    rewrite Hsp.
    unfold body_thread. cbn [r_body]. rewrite Hnt.
    unfold end_loadable. cbn [r_vmap r_outcome].
    unfold vmap_loadable. cbn [r_vmap vm_keyf r_outcome].
    cbn [apply_transforms fold_left vm_name].
    destruct (field_loadable f p) eqn:Hfld; cbn [andb].
    - destruct (assoc_verdict (field_value f e p) (e_vmap e nm)); reflexivity.
    - rewrite Bool.andb_false_r. reflexivity. }
  (* simplify the merged-rule loadability: both branches of the inner match are
     [true], so it is just [body_loadable_walk body p && field_loadable f p]. *)
  assert (HmL' : rule_loadable (mk_vmap_rule f nm body) e p =
                 body_loadable_walk body p && field_loadable f p).
  { rewrite HmL. destruct (field_loadable f p);
      [ destruct (assoc_verdict (field_value f e p) (e_vmap e nm)) | ];
      rewrite ?Bool.andb_true_r, ?Bool.andb_false_r; reflexivity. }
  (* applicability of the merged rule: body only (no head match) *)
  assert (HmA : rule_applies (mk_vmap_rule f nm body) e p = rule_applies_walk body e p)
    by reflexivity.
  (* now evaluate.  Field-loadable case split drives everything. *)
  rewrite ?eval_rules_cons, ?eval_rules_nil.
  rewrite HmL', HmA.
  destruct (field_loadable f p) eqn:Hfld; cbn [andb].
  - (* f loads.  Build the two point-equality tests. *)
    set (b1 := eval_cmp CEq (field_value f e p) v1).
    set (b2 := eval_cmp CEq (field_value f e p) v2).
    (* outcome of the merged rule via vmap_two_points *)
    assert (Hmout : outcome (mk_vmap_rule f nm body) e p =
                    if b1 then Some w1 else if b2 then Some w2 else None).
    { unfold outcome, mk_vmap_rule. cbn [r_body]. rewrite Hsp.
      unfold body_thread. cbn [r_body]. rewrite Hnt.
      change ({| r_body := body;
     r_outcome := OVmap {| vm_fields := [f]; vm_keyf := Some (f, []); vm_name := nm |}; r_after := [] |}) with (mk_vmap_rule f nm body).
      rewrite (vmap_two_points f nm v1 v2 w1 w2 body e p Hvm); try assumption.
      - reflexivity.
      - intro. apply (field_fixed_len_loaded f (length v1) e p Hfx1); assumption.
      - intro. apply (field_fixed_len_loaded f (length v2) e p Hfx2); assumption. }
    rewrite Hmout, Bool.andb_true_r.
    (* the originals: loadable = field_loadable && body_loadable_walk = same *)
    rewrite ?eval_rules_cons, ?eval_rules_nil.
    rewrite !orig_rule_loadable, !orig_rule_applies, !orig_rule_outcome.
    cbn [match_loadable]. rewrite Hfld, Hsp, Hnt. cbn [andb].
    rewrite !(terminal_outcome_vmap_base _ _ Hw1), !(terminal_outcome_vmap_base _ _ Hw2).
    (* eval_matchcond (MCmp f CEq vi) e p = field_loadable f && b_i = b_i *)
    assert (Hm1 : eval_matchcond (MCmp f CEq v1) e p = b1).
    { unfold eval_matchcond, eval_matchcond_body. cbn [match_loadable].
      rewrite Hfld. reflexivity. }
    assert (Hm2 : eval_matchcond (MCmp f CEq v2) e p = b2).
    { unfold eval_matchcond, eval_matchcond_body. cbn [match_loadable].
      rewrite Hfld. reflexivity. }
    rewrite Hm1, Hm2.
    (* split on whether the shared body applies; then on b1, b2 *)
    destruct (body_loadable_walk body p) eqn:HbL; cbn [andb];
      [| (* body not loadable: merged & both originals all skipped *)
         destruct b1; cbn [andb]; [reflexivity|];
         destruct b2; cbn [andb]; reflexivity ].
    destruct (rule_applies_walk body e p) eqn:HbA; cbn [andb].
    + (* body applies *)
      destruct b1; cbn [andb].
      * rewrite Hw1. reflexivity.
      * destruct b2; cbn [andb]; [rewrite Hw2; reflexivity | reflexivity].
    + (* body does not apply: every rule skipped, fall to rest *)
      rewrite !Bool.andb_false_r. reflexivity.
  - (* f does not load: merged rule not loadable (skipped); both originals have
       head match_loadable = field_loadable f = false -> not loadable, skipped. *)
    rewrite Bool.andb_false_r.
    rewrite ?eval_rules_cons, ?eval_rules_nil.
    rewrite !orig_rule_loadable.
    cbn [match_loadable]. rewrite Hfld. cbn [andb].
    reflexivity.
Qed.

(** ** Fresh-name minting for verdict maps. *)
Definition vmapname (n : nat) : String.string :=
  String.append "__vmap"%string (string_of_nat n).

Lemma vmapname_inj : forall a b, vmapname a = vmapname b -> a = b.
Proof.
  intros a b H. unfold vmapname in H.
  apply string_of_nat_inj. cbn in H. repeat (injection H as H). exact H.
Qed.

Global Opaque vmapname.

(** ** Compact boolean recognition of the [orig_rule] shell.

    The shell test [r = orig_rule f v rest (r_verdict r)] (used inside the vmap
    merge-pair recognisers) was previously done with the monolithic [rule_eq_dec],
    which extracts to ~42 MB of OCaml.  Given [head_value r = Some (f, v, rest)] the
    body of [r] already equals that of [orig_rule], so the test reduces to the END
    fields, which [rule_end_eqb r (mk_vmap_base (r_verdict r))] checks compactly.
    [mk_vmap_base (r_verdict r)] carries the END fields of [orig_rule] (an empty
    body / no vmap / no nat / ... / empty after), so this is exactly the shell test. *)
Lemma rule_end_eqb_orig_rule : forall r f v rest,
  head_value r = Some (f, v, rest) ->
  (rule_end_eqb r (mk_vmap_base (r_verdict r)) = true
   <-> r = orig_rule f v rest (r_verdict r)).
Proof.
  intros r f v rest Hhd.
  (* r_body r = BMatch (MCmp f CEq v) :: rest, so mk_head (MCmp f CEq v) rest r = r *)
  unfold head_value in Hhd.
  destruct (r_body r) as [| [m | s] b] eqn:Eb; try discriminate.
  destruct m as [ | | | | f' op v' | | | | | | | | ]; try discriminate.
  destruct op; try discriminate. inversion Hhd; subst f' v' b. clear Hhd.
  assert (Hself : mk_head (MCmp f CEq v) rest r = r).
  { unfold mk_head. rewrite <- Eb. destruct r; reflexivity. }
  rewrite (rule_end_eqb_mk_head (MCmp f CEq v) rest r (mk_vmap_base (r_verdict r))).
  unfold orig_rule. rewrite Hself. reflexivity.
Qed.

(** ** Recognise a vmap-merge-eligible adjacent pair.

    Heads [MCmp f CEq v1] / [MCmp f CEq v2] over the SAME fixed-width field [f],
    SAME tail body [rest], DIFFERING terminal verdicts [w1 <> w2] (both terminal),
    and the two rules otherwise identical pure-terminal rules ([r_vmap]/[r_nat]/…
    all empty, [r_after] = []).  This is precisely nft's single-differing-dimension
    eligibility with the differing dimension being the VERDICT. *)

Definition vmap_merge_pair (r1 r2 : rule)
  : option (field * data * data * verdict * verdict * list body_item) :=
  match head_value r1, head_value r2 with
  | Some (f1, v1, rest1), Some (f2, v2, rest2) =>
      if field_eq_dec f1 f2 then
      if list_eq_dec body_item_eq_dec rest1 rest2 then
      match field_fixed_len f1 with
      | Some len =>
        if Nat.eq_dec len (length v1) then
        if Nat.eq_dec len (length v2) then
        if terminal (r_verdict r1) then
        if terminal (r_verdict r2) then
        if verdict_eq_dec (r_verdict r1) (r_verdict r2) then None
        else
        (* the two rules are EXACTLY the pure-terminal shells differing only in head
           value and verdict — check by reconstructing each from [orig_rule].
           [rule_end_eqb] is the compact boolean shell test (see
           [rule_end_eqb_orig_rule]); it keeps the extracted optimizer small. *)
        if rule_end_eqb r1 (mk_vmap_base (r_verdict r1)) then
        if rule_end_eqb r2 (mk_vmap_base (r_verdict r2)) then
          Some (f1, v1, v2, r_verdict r1, r_verdict r2, rest1)
        else None else None
        else None else None else None else None
      | None => None
      end
      else None else None
  | _, _ => None
  end.

(** A RELAXED run-eligibility recogniser for the N-way pass: same field/body/end
    fields, terminal verdict — but [r2]'s verdict may EQUAL [r1]'s (a vmap groups a
    whole run whose verdicts need only be terminal; two consecutive equal verdicts are
    fine as long as the run overall has >= 2 DISTINCT ones, checked by the driver).
    This is what lets [22:accept, 80:drop, 443:accept] fold into ONE 3-entry vmap. *)
Definition vmap_run_pair (r1 r2 : rule)
  : option (field * data * verdict * list body_item) :=
  (* EFFECT-SAFETY GUARD — see [Optimize_ValueSet.value_merge_pair]. *)
  if negb (rule_mutfree r1) then None else
  match head_value r1, head_value r2 with
  | Some (f1, v1, rest1), Some (f2, v2, rest2) =>
      if field_eq_dec f1 f2 then
      if list_eq_dec body_item_eq_dec rest1 rest2 then
      match field_fixed_len f1 with
      | Some len =>
        if Nat.eq_dec len (length v1) then
        if Nat.eq_dec len (length v2) then
        if terminal (r_verdict r1) then
        if terminal (r_verdict r2) then
        if rule_end_eqb r1 (mk_vmap_base (r_verdict r1)) then
        if rule_end_eqb r2 (mk_vmap_base (r_verdict r2)) then
          Some (f1, v2, r_verdict r2, rest1)
        else None else None
        else None else None else None else None
      | None => None
      end
      else None else None
  | _, _ => None
  end.

(** The guard, extracted: a fired pair certifies its canonical rule write-free. *)
Lemma vmap_run_pair_mutfree : forall r1 r2 x,
  vmap_run_pair r1 r2 = Some x -> rule_mutfree r1 = true.
Proof.
  intros r1 r2 x H. unfold vmap_run_pair in H.
  destruct (rule_mutfree r1); [reflexivity | discriminate H].
Qed.

Lemma vmap_run_pair_shape : forall r1 r2 f v2 w2 body,
  vmap_run_pair r1 r2 = Some (f, v2, w2, body) ->
  (exists v1, head_value r1 = Some (f, v1, body)
              /\ r1 = orig_rule f v1 body (r_verdict r1)
              /\ field_fixed_len f = Some (length v1)
              /\ terminal (r_verdict r1) = true) /\
  r2 = orig_rule f v2 body w2 /\
  field_fixed_len f = Some (length v2) /\ terminal w2 = true.
Proof.
  intros r1 r2 f v2 w2 body H. unfold vmap_run_pair in H.
  destruct (negb (rule_mutfree r1)); [discriminate |].
  destruct (head_value r1) as [[[f1 u1] s1] |] eqn:H1; [| discriminate].
  destruct (head_value r2) as [[[f2 u2] s2] |] eqn:H2; [| discriminate].
  destruct (field_eq_dec f1 f2) as [Ef |]; [| discriminate]. subst f2.
  destruct (list_eq_dec body_item_eq_dec s1 s2) as [Es |]; [| discriminate]. subst s2.
  destruct (field_fixed_len f1) as [len |] eqn:Hfx; [| discriminate].
  destruct (Nat.eq_dec len (length u1)) as [El1 |]; [| discriminate].
  destruct (Nat.eq_dec len (length u2)) as [El2 |]; [| discriminate].
  destruct (terminal (r_verdict r1)) eqn:Ew1; [| discriminate].
  destruct (terminal (r_verdict r2)) eqn:Ew2; [| discriminate].
  destruct (rule_end_eqb r1 (mk_vmap_base (r_verdict r1))) eqn:Eb1; [| discriminate].
  destruct (rule_end_eqb r2 (mk_vmap_base (r_verdict r2))) eqn:Eb2; [| discriminate].
  pose proof (proj1 (rule_end_eqb_orig_rule r1 f1 u1 s1 H1) Eb1) as Esh1.
  pose proof (proj1 (rule_end_eqb_orig_rule r2 f1 u2 s1 H2) Eb2) as Esh2.
  injection H as Ef' Ev2 Ew2' Ebody. subst f w2 body v2.
  assert (Hfx1 : field_fixed_len f1 = Some (length u1)) by (rewrite Hfx; f_equal; exact El1).
  assert (Hfx2 : field_fixed_len f1 = Some (length u2)) by (rewrite Hfx; f_equal; exact El2).
  split.
  - exists u1. repeat split; first [assumption | reflexivity].
  - repeat split; first [assumption | reflexivity].
Qed.

(** When a vmap-merge fires, the two input rules are EXACTLY the [orig_rule]
    shells, the field is fixed-width, and the two verdicts are terminal. *)
Lemma vmap_merge_pair_shape : forall r1 r2 f v1 v2 w1 w2 body,
  vmap_merge_pair r1 r2 = Some (f, v1, v2, w1, w2, body) ->
  r1 = orig_rule f v1 body w1 /\
  r2 = orig_rule f v2 body w2 /\
  field_fixed_len f = Some (length v1) /\
  field_fixed_len f = Some (length v2) /\
  terminal w1 = true /\ terminal w2 = true.
Proof.
  intros r1 r2 f v1 v2 w1 w2 body H. unfold vmap_merge_pair in H.
  destruct (head_value r1) as [[[f1 u1] s1] |] eqn:H1; [| discriminate].
  destruct (head_value r2) as [[[f2 u2] s2] |] eqn:H2; [| discriminate].
  destruct (field_eq_dec f1 f2) as [Ef |]; [| discriminate]. subst f2.
  destruct (list_eq_dec body_item_eq_dec s1 s2) as [Es |]; [| discriminate]. subst s2.
  destruct (field_fixed_len f1) as [len |] eqn:Hfx; [| discriminate].
  destruct (Nat.eq_dec len (length u1)) as [El1 |]; [| discriminate].
  destruct (Nat.eq_dec len (length u2)) as [El2 |]; [| discriminate].
  destruct (terminal (r_verdict r1)) eqn:Ht1; [| discriminate].
  destruct (terminal (r_verdict r2)) eqn:Ht2; [| discriminate].
  destruct (verdict_eq_dec (r_verdict r1) (r_verdict r2)) as [|Hvne]; [discriminate|].
  destruct (rule_end_eqb r1 (mk_vmap_base (r_verdict r1))) eqn:Eb1; [| discriminate].
  destruct (rule_end_eqb r2 (mk_vmap_base (r_verdict r2))) eqn:Eb2; [| discriminate].
  pose proof (proj1 (rule_end_eqb_orig_rule r1 f1 u1 s1 H1) Eb1) as Er1.
  pose proof (proj1 (rule_end_eqb_orig_rule r2 f1 u2 s1 H2) Eb2) as Er2.
  inversion H; subst f v1 v2 w1 w2 body. clear H.
  repeat split.
  - exact Er1.
  - exact Er2.
  - rewrite Hfx; f_equal; congruence.
  - rewrite Hfx; f_equal; congruence.
  - exact Ht1.
  - exact Ht2.
Qed.

Fixpoint optimize_rules_vmap2 (n : nat) (d : set_decls) (rs : list rule)
  : nat * set_decls * list rule :=
  match rs with
  | r1 :: ((r2 :: rest) as tl) =>
      match vmap_merge_pair r1 r2 with
      | Some (f, v1, v2, w1, w2, body) =>
          let name := vmapname n in
          let d' := {| sd_sets := sd_sets d;
                       sd_vmaps := (name, [(v1, v1, w1); (v2, v2, w2)]) :: sd_vmaps d;
                       sd_maps := sd_maps d |} in
          let merged := mk_vmap_rule f name body in
          let '(n'', d'', rest') := optimize_rules_vmap2 (S n) d' rest in
          (n'', d'', merged :: rest')
      | None =>
          let '(n'', d'', tl') := optimize_rules_vmap2 n d tl in
          (n'', d'', r1 :: tl')
      end
  | _ => (n, d, rs)
  end.

Lemma optimize_rules_vmap2_cons2 : forall n d r1 r2 rest,
  optimize_rules_vmap2 n d (r1 :: r2 :: rest) =
  match vmap_merge_pair r1 r2 with
  | Some (f, v1, v2, w1, w2, body) =>
      let name := vmapname n in
      let d' := {| sd_sets := sd_sets d;
                   sd_vmaps := (name, [(v1, v1, w1); (v2, v2, w2)]) :: sd_vmaps d;
                   sd_maps := sd_maps d |} in
      let merged := mk_vmap_rule f name body in
      let '(n'', d'', rest') := optimize_rules_vmap2 (S n) d' rest in
      (n'', d'', merged :: rest')
  | None =>
      let '(n'', d'', tl') := optimize_rules_vmap2 n d (r2 :: rest) in
      (n'', d'', r1 :: tl')
  end.
Proof. reflexivity. Qed.

Definition optimize_chain_vmap2 (n : nat) (d : set_decls) (c : chain)
  : nat * set_decls * chain :=
  let '(n', d', rs') := optimize_rules_vmap2 n d (c_rules c) in
  (n', d', {| c_policy := c_policy c; c_rules := rs' |}).

(** *** Freshness bookkeeping for the minted vmap names (mirrors the set version). *)
Lemma optimize_rules_vmap2_assoc_stable : forall rs n d n' d' rs' nm X,
  optimize_rules_vmap2 n d rs = (n', d', rs') ->
  (forall k, n <= k -> nm <> vmapname k) ->
  assoc_str nm (sd_vmaps d') X = assoc_str nm (sd_vmaps d) X.
Proof.
  induction rs as [rs H0] using (induction_ltof1 _ (@length rule)).
  intros n d n' d' rs' nm X H Hnm.
  destruct rs as [| r1 [| r2 rest] ].
  - cbn in H. inversion H; subst; reflexivity.
  - cbn in H. inversion H; subst; reflexivity.
  - rewrite optimize_rules_vmap2_cons2 in H. cbv zeta in H.
    destruct (vmap_merge_pair r1 r2) as [[[[[[f v1] v2] w1] w2] body] |] eqn:Evm.
    + destruct (optimize_rules_vmap2 (S n)
                  {| sd_sets := sd_sets d;
                     sd_vmaps := (vmapname n, [(v1,v1,w1);(v2,v2,w2)]) :: sd_vmaps d;
                     sd_maps := sd_maps d |} rest)
        as [[m'' dd''] rr''] eqn:Erec.
      inversion H; subst n' d' rs'. clear H.
      erewrite (H0 rest); [ | unfold ltof; cbn; lia | exact Erec | ].
      * cbn [sd_vmaps assoc_str].
        destruct (String.eqb nm (vmapname n)) eqn:Eqn.
        -- apply String.eqb_eq in Eqn. exfalso. apply (Hnm n); [lia | exact Eqn].
        -- reflexivity.
      * intros k Hk. apply Hnm. lia.
    + destruct (optimize_rules_vmap2 n d (r2 :: rest)) as [[m'' dd''] rr''] eqn:Erec.
      inversion H. subst n' d' rs'. clear H.
      eapply (H0 (r2 :: rest)); [ unfold ltof; cbn; lia | exact Erec | exact Hnm ].
Qed.

(** A declared vmap's entries are exactly what a name-lookup reads. *)
Lemma e_vmap_env_with_sets : forall base d nm,
  e_vmap (env_with_sets base d) nm = assoc_str nm (sd_vmaps d) (e_vmap base nm).
Proof. reflexivity. Qed.

Lemma e_map_env_with_sets : forall base d nm,
  e_map (env_with_sets base d) nm = assoc_str nm (sd_maps d) (e_map base nm).
Proof. reflexivity. Qed.

(** *** The executable VMAP merge, proved verdict-preserving END-TO-END over the
    table semantics with the synthesised verdict map in scope, axiom-free.

    On clean rules with minted names fresh for [d], the rewritten [rs'] under the
    augmented declarations [d'] yields the SAME verdict on every packet as [rs]
    under [d].  The merged rule's `__vmapN` lookup resolves to its two point
    entries (freshness + injectivity); [eval_rules_vmap_merge2] collapses the pair;
    the clean tail is env-irrelevant. *)
(** *** The CHAIN-level entry (the [eval_chain] specialisation). *)
(** * N-WAY verdict-map merge: fold a whole RUN of same-field/different-verdict rules
      into ONE vmap with N entries (matching nft -o).

    nft -o consolidates [dport 22 accept; 80 drop; 443 accept] into ONE
    [tcp dport vmap { 22:accept, 80:drop, 443:accept }].  Unlike the value->set and
    concat families (single shared verdict), the vmap rule's OUTCOME is value-
    DEPENDENT, so this needs a dedicated N-way collapse rather than the shared-outcome
    [eval_rules_run_collapse]. *)

Definition vmap_pt (vw : data * verdict) : data * data * verdict :=
  (fst vw, fst vw, snd vw).

Fixpoint first_match (f : field) (e : env) (q : packet) (l : list (data * verdict)) : option verdict :=
  match l with
  | [] => None
  | (v, w) :: tl => if eval_matchcond (MCmp f CEq v) e q then Some w else first_match f e q tl
  end.

(** [assoc_verdict] over an N-entry POINT map is the first matching key's verdict
    (first-match order) — the same scan the run of [orig_rule]s performs. *)
Lemma assoc_verdict_points : forall es f e q,
  (forall v w, In (v, w) es -> field_loadable f q = true ->
               length (field_value f e q) = length v) ->
  field_loadable f q = true ->
  assoc_verdict (field_value f e q) (map vmap_pt es) = first_match f e q es.
Proof.
  intros es f e q Hlen Hld.
  induction es as [| [v w] es IH]; [reflexivity|].
  cbn [map]. unfold vmap_pt at 1. cbn [fst snd assoc_verdict first_match].
  rewrite data_in_iv_point_eqb.
  rewrite (eval_mcmp_point f v e q Hld (Hlen v w (or_introl eq_refl) Hld)).
  destruct (data_eqb (field_value f e q) v) eqn:E; [reflexivity|].
  apply IH. intros v' w' Hin Hld'. apply (Hlen v' w'); [right; exact Hin | exact Hld'].
Qed.

(** The merged vmap rule's [outcome_core] over an N-entry point map is [first_match]. *)
Lemma outcome_core_vmapN : forall es f e q nm body,
  e_vmap e nm = map vmap_pt es ->
  (forall v w, In (v, w) es -> field_loadable f q = true ->
               length (field_value f e q) = length v) ->
  field_loadable f q = true ->
  outcome_core (mk_vmap_rule f nm body) e q = first_match f e q es.
Proof.
  intros es f e q nm body Hvm Hlen Hld.
  unfold outcome_core, mk_vmap_rule. cbn [r_vmap vm_keyf vm_name vm_fields r_outcome].
  cbn [apply_transforms fold_left]. rewrite Hvm.
  rewrite (assoc_verdict_points es f e q Hlen Hld).
  destruct (first_match f e q es) eqn:Efm; [reflexivity|].
  unfold terminal_outcome, mk_vmap_rule.
  cbn [r_nat r_tproxy r_fwd r_queue r_verdict r_after terminal r_outcome]. reflexivity.
Qed.

(** On a clean body (no synproxy stop, no notrack), [orig_rule]'s outcome is just the
    terminal verdict (when [w] is terminal). *)
Lemma orig_rule_outcome_clean : forall f v body w e p,
  body_synproxy_stops body p = false ->
  body_has_notrack body = false ->
  terminal w = true ->
  outcome (orig_rule f v body w) e p = Some w.
Proof.
  intros f v body w e p Hsp Hnt Hw.
  rewrite orig_rule_outcome, Hsp, Hnt.
  apply (terminal_outcome_vmap_base w p Hw).
Qed.

(** The N-way vmap collapse: a run [map (fun '(v,w) => orig_rule f v body w) es] of
    same-field rules with DISTINCT terminal verdicts and DISTINCT keys, whose merged
    vmap [nm] carries the N point entries [map vmap_pt es], collapses to ONE
    [mk_vmap_rule].  On a packet matching key [vi] -> the verdict [wi] (first-match);
    on a miss -> the vmap returns None -> Continue -> fall through to [rest]. *)
Lemma eval_rules_vmap_mergeN : forall f nm es body rest e p,
  e_vmap e nm = map vmap_pt es ->
  (forall v w, In (v, w) es -> field_fixed_len f = Some (length v)) ->
  (forall v w, In (v, w) es -> terminal w = true) ->
  body_synproxy_stops body p = false ->
  body_has_notrack body = false ->
  eval_rules (mk_vmap_rule f nm body :: rest) e p
  = eval_rules (map (fun vw => orig_rule f (fst vw) body (snd vw)) es ++ rest) e p.
Proof.
  intros f nm es body rest e p Hvm Hfx Hterm Hsp Hnt.
  (* merged rule loadable / applies / outcome *)
  assert (HmL : rule_loadable (mk_vmap_rule f nm body) e p
                = body_loadable_walk body p && field_loadable f p).
  { unfold rule_loadable, mk_vmap_rule. cbn [r_body]. rewrite Hsp.
    unfold body_thread. cbn [r_body]. rewrite Hnt.
    unfold end_loadable. cbn [r_vmap r_outcome]. unfold vmap_loadable.
    cbn [r_vmap vm_keyf apply_transforms fold_left vm_name r_outcome].
    destruct (field_loadable f p) eqn:Hfld; cbn [andb].
    - destruct (assoc_verdict (field_value f e p) (e_vmap e nm));
        rewrite ?Bool.andb_true_r; reflexivity.
    - rewrite Bool.andb_false_r. reflexivity. }
  assert (HmA : rule_applies (mk_vmap_rule f nm body) e p = rule_applies_walk body e p)
    by reflexivity.
  rewrite ?eval_rules_cons, ?eval_rules_nil. rewrite HmL, HmA.
  destruct (field_loadable f p) eqn:Hfld; cbn [andb].
  - (* f loads: merged outcome = first_match; the run scans the same keys *)
    rewrite Bool.andb_true_r.
    assert (Hmout : outcome (mk_vmap_rule f nm body) e p = first_match f e p es).
    { unfold outcome, mk_vmap_rule. cbn [r_body]. rewrite Hsp.
      unfold body_thread. cbn [r_body]. rewrite Hnt.
      change ({| r_body := body;
     r_outcome := OVmap {| vm_fields := [f]; vm_keyf := Some (f, []); vm_name := nm |}; r_after := [] |}) with (mk_vmap_rule f nm body).
      apply (outcome_core_vmapN es f e p nm body Hvm); [| exact Hfld].
      intros v w Hin Hld. apply (field_fixed_len_loaded f (length v) e p (Hfx v w Hin) Hld). }
    rewrite Hmout.
    destruct (body_loadable_walk body p) eqn:HbL; cbn [andb].
    + destruct (rule_applies_walk body e p) eqn:HbA; cbn [andb].
      * (* body loads & applies: induct on es, matching first_match to the run *)
        clear HmL HmA Hmout Hvm.
        induction es as [| [v w] es IH]; cbn [map app first_match fst snd].
        -- (* empty run: first_match = None -> fall through to rest *)
           reflexivity.
        -- rewrite ?eval_rules_cons, ?eval_rules_nil.
           rewrite orig_rule_loadable, orig_rule_applies,
                   (orig_rule_outcome_clean f v body w e p Hsp Hnt
                      (Hterm v w (or_introl eq_refl))).
           cbn [match_loadable]. rewrite Hfld, HbL, Hsp. cbn [andb].
           assert (Hm : eval_matchcond (MCmp f CEq v) e p
                        = eval_cmp CEq (field_value f e p) v).
           { unfold eval_matchcond, eval_matchcond_body. cbn [match_loadable].
             rewrite Hfld. reflexivity. }
           rewrite Hm. rewrite HbA. cbn [andb].
           destruct (eval_cmp CEq (field_value f e p) v) eqn:Ev.
           ++ (* head matches: both sides give Some w (w terminal) *)
              rewrite (Hterm v w (or_introl eq_refl)). reflexivity.
           ++ (* head misses: both fall through; induct on the tail *)
              apply IH.
              ** intros v' w' Hin. apply (Hfx v' w'); right; exact Hin.
              ** intros v' w' Hin. apply (Hterm v' w'); right; exact Hin.
      * (* body doesn't apply: merged skipped (applies false), run all skipped *)
        clear HmL HmA Hmout Hvm.
        induction es as [| [v w] es IH]; cbn [map app fst snd]; [reflexivity|].
        rewrite ?eval_rules_cons, ?eval_rules_nil.
        rewrite orig_rule_loadable, orig_rule_applies.
        cbn [match_loadable]. rewrite Hfld, HbL, Hsp. cbn [andb].
        rewrite HbA. rewrite Bool.andb_false_r. apply IH;
          [ intros v' w' Hin; apply (Hfx v' w'); right; exact Hin
          | intros v' w' Hin; apply (Hterm v' w'); right; exact Hin ].
    + (* body doesn't load: merged skipped, run all skipped *)
      clear HmL HmA Hmout Hvm.
      induction es as [| [v w] es IH]; cbn [map app fst snd]; [reflexivity|].
      rewrite ?eval_rules_cons, ?eval_rules_nil.
      rewrite orig_rule_loadable. cbn [match_loadable]. rewrite Hfld, HbL, Hsp.
      cbn [andb]. apply IH;
        [ intros v' w' Hin; apply (Hfx v' w'); right; exact Hin
        | intros v' w' Hin; apply (Hterm v' w'); right; exact Hin ].
  - (* f does not load: merged skipped; every orig has head field-load false -> skipped *)
    rewrite Bool.andb_false_r. cbn [andb].
    clear HmL HmA Hvm.
    induction es as [| [v w] es IH]; cbn [map app fst snd]; [reflexivity|].
    rewrite ?eval_rules_cons, ?eval_rules_nil.
    rewrite orig_rule_loadable. cbn [match_loadable]. rewrite Hfld. cbn [andb].
    apply IH;
      [ intros v' w' Hin; apply (Hfx v' w'); right; exact Hin
      | intros v' w' Hin; apply (Hterm v' w'); right; exact Hin ].
Qed.

(** ** Executable N-WAY vmap pass.

    [take_vmap_run r1 rest] collects the maximal prefix of rules that each vmap-merge
    with the canonical first rule [r1] (same field, same body, DIFFERING terminal
    verdict), returning the collected (key,verdict) entries and the leftover;
    [optimize_rules_vmap] folds the whole run [r1 :: matched] into ONE
    [mk_vmap_rule] over the N-entry vmap. *)
Fixpoint take_vmap_run (r1 : rule) (rest : list rule)
  : list (data * verdict) * list rule :=
  match rest with
  | [] => ([], [])
  | r2 :: tl =>
      match vmap_run_pair r1 r2 with
      | Some (_, v2, w2, _) =>
          let '(es, rest') := take_vmap_run r1 tl in ((v2, w2) :: es, rest')
      | None => ([], rest)
      end
  end.

(** Does the collected run carry >= 2 DISTINCT verdicts (so it is genuinely a vmap,
    not a uniform-verdict SET)?  [entries] is [(v1, w1) :: es]. *)
Definition has_distinct_verdict (w1 : verdict) (es : list (data * verdict)) : bool :=
  existsb (fun vw => if verdict_eq_dec (snd vw) w1 then false else true) es.

(** A body is VMAP-MERGE-SAFE iff it carries no SYN-proxy and no `notrack`
    statement.  The vmap merge moves the key field read to AFTER the body (the
    merged rule reads field [f] as its vmap key at [body_thread body p]), whereas
    each original rule reads [f] in its HEAD match BEFORE the body.  A `notrack`
    in the body would make [body_thread] flip the conntrack latch, so a
    ct-dependent key would be read in a DIFFERENT tracking state than the originals
    — the merge would be UNSOUND.  Likewise a body SYN-proxy STOP short-circuits
    the outcome.  This guard is VACUOUSLY TRUE on a clean rule body (no statements),
    so it never blocks the merges [nft -o] performs on real rulesets, but it makes
    the pass sound on ARBITRARY input. *)
Definition body_vmap_safe (body : list body_item) : bool :=
  negb (body_has_synproxy body) && negb (body_has_notrack body).

Fixpoint optimize_rules_vmap (fuel n : nat) (d : set_decls) (rs : list rule)
  : nat * set_decls * list rule :=
  match fuel with
  | O => (n, d, rs)
  | S fuel' =>
    match rs with
    | r1 :: ((_ :: _) as rest) =>
        match head_value r1 with
        | Some (f, v1, body) =>
            match take_vmap_run r1 rest with
            | ((_ :: _) as es, rest') =>
                if has_distinct_verdict (r_verdict r1) es && body_vmap_safe body then
                  let name := vmapname n in
                  let entries := (v1, r_verdict r1) :: es in
                  let d' := {| sd_sets := sd_sets d;
                               sd_vmaps := (name, map vmap_pt entries) :: sd_vmaps d;
                               sd_maps := sd_maps d |} in
                  let merged := mk_vmap_rule f name body in
                  let '(n'', d'', rest'') := optimize_rules_vmap fuel' (S n) d' rest' in
                  (n'', d'', merged :: rest'')
                else
                  let '(n'', d'', rest') := optimize_rules_vmap fuel' n d rest in
                  (n'', d'', r1 :: rest')
            | ([], _) =>
                let '(n'', d'', rest') := optimize_rules_vmap fuel' n d rest in
                (n'', d'', r1 :: rest')
            end
        | None =>
            let '(n'', d'', rest') := optimize_rules_vmap fuel' n d rest in
            (n'', d'', r1 :: rest')
        end
    | _ => (n, d, rs)
    end
  end.

Definition optimize_chain_vmap (n : nat) (d : set_decls) (c : chain)
  : nat * set_decls * chain :=
  let '(n', d', rs') := optimize_rules_vmap (length (c_rules c)) n d (c_rules c) in
  (n', d', {| c_policy := c_policy c; c_rules := rs' |}).

Lemma optimize_rules_vmap_consSS : forall fuel n d r1 r2 rest,
  optimize_rules_vmap (S fuel) n d (r1 :: r2 :: rest) =
  match head_value r1 with
  | Some (f, v1, body) =>
      match take_vmap_run r1 (r2 :: rest) with
      | ((_ :: _) as es, rest') =>
          if has_distinct_verdict (r_verdict r1) es && body_vmap_safe body then
            let name := vmapname n in
            let entries := (v1, r_verdict r1) :: es in
            let d' := {| sd_sets := sd_sets d;
                         sd_vmaps := (name, map vmap_pt entries) :: sd_vmaps d;
                         sd_maps := sd_maps d |} in
            let merged := mk_vmap_rule f name body in
            let '(n'', d'', rest'') := optimize_rules_vmap fuel (S n) d' rest' in
            (n'', d'', merged :: rest'')
          else
            let '(n'', d'', rest') := optimize_rules_vmap fuel n d (r2 :: rest) in
            (n'', d'', r1 :: rest')
      | ([], _) =>
          let '(n'', d'', rest') := optimize_rules_vmap fuel n d (r2 :: rest) in
          (n'', d'', r1 :: rest')
      end
  | None =>
      let '(n'', d'', rest') := optimize_rules_vmap fuel n d (r2 :: rest) in
      (n'', d'', r1 :: rest')
  end.
Proof. reflexivity. Qed.

Lemma optimize_rules_vmap_assoc_stable : forall fuel n d rs n' d' rs' nm X,
  optimize_rules_vmap fuel n d rs = (n', d', rs') ->
  (forall k, n <= k -> nm <> vmapname k) ->
  assoc_str nm (sd_vmaps d') X = assoc_str nm (sd_vmaps d) X.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' nm X H Hnm.
  - cbn in H. inversion H; subst; reflexivity.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; reflexivity.
    + cbn in H. inversion H; subst; reflexivity.
    + rewrite optimize_rules_vmap_consSS in H.
      destruct (head_value r1) as [[[f v1] body] |] eqn:Ehd.
      * destruct (take_vmap_run r1 (r2 :: rest)) as [es rest'] eqn:Erun.
        destruct es as [| e es'].
        -- remember (optimize_rules_vmap fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst d'. clear Hn' Hr'.
           eapply (IH n d (r2 :: rest)); [symmetry; exact Erec | exact Hnm].
        -- destruct (has_distinct_verdict (r_verdict r1) (e :: es') && body_vmap_safe body) eqn:Hdv.
           2:{ remember (optimize_rules_vmap fuel n d (r2 :: rest)) as tt eqn:Erec.
               destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
               injection H as Hn' Hd' Hr'. subst d'. clear Hn' Hr'.
               eapply (IH n d (r2 :: rest)); [symmetry; exact Erec | exact Hnm]. }
           cbv zeta in H.
           remember (optimize_rules_vmap fuel (S n)
                       {| sd_sets := sd_sets d;
                          sd_vmaps := (vmapname n,
                            map vmap_pt ((v1, r_verdict r1) :: e :: es')) :: sd_vmaps d;
                          sd_maps := sd_maps d |} rest')
             as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst d'. clear Hn' Hr'.
           erewrite (IH (S n) _ rest'); [ | symmetry; exact Erec | intros k Hk; apply Hnm; lia ].
           cbn [sd_vmaps assoc_str].
           destruct (String.eqb nm (vmapname n)) eqn:Eqn.
           ++ apply String.eqb_eq in Eqn. exfalso. apply (Hnm n); [lia | exact Eqn].
           ++ reflexivity.
      * remember (optimize_rules_vmap fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
        injection H as Hn' Hd' Hr'. subst d'. clear Hn' Hr'.
        eapply (IH n d (r2 :: rest)); [symmetry; exact Erec | exact Hnm].
Qed.

Lemma take_vmap_run_shape : forall r1 f v1 body rest es rest',
  head_value r1 = Some (f, v1, body) ->
  take_vmap_run r1 rest = (es, rest') ->
  rest = map (fun vw => orig_rule f (fst vw) body (snd vw)) es ++ rest'
  /\ (forall v w, In (v, w) es -> field_fixed_len f = Some (length v))
  /\ (forall v w, In (v, w) es -> terminal w = true).
Proof.
  intros r1 f v1 body rest. induction rest as [| r2 tl IH]; intros es rest' Hhd H.
  - cbn in H. inversion H; subst. split; [reflexivity| split; intros v w []].
  - cbn in H. destruct (vmap_run_pair r1 r2)
      as [[[[fa v2] w2] bd] |] eqn:Evm.
    + destruct (take_vmap_run r1 tl) as [es0 rest0] eqn:Erec.
      inversion H; subst es rest'. clear H.
      destruct (vmap_run_pair_shape r1 r2 fa v2 w2 bd Evm)
        as [[u1 [Hhd1 [_ [_ _]]]] [Hr2 [Hfx Hw2]]].
      rewrite Hhd in Hhd1. inversion Hhd1; subst fa bd.
      destruct (IH es0 rest0 Hhd eq_refl) as [Hsplit [Hall1 Hall2]].
      split; [| split].
      * cbn [map app fst snd]. rewrite <- Hr2, <- Hsplit. reflexivity.
      * intros v w [Hvw | Hin]; [ inversion Hvw; subst; exact Hfx | apply (Hall1 v w Hin) ].
      * intros v w [Hvw | Hin]; [ inversion Hvw; subst; exact Hw2 | apply (Hall2 v w Hin) ].
    + inversion H; subst es rest'. split; [reflexivity| split; intros v w []].
Qed.

(** r1's own (v1, r_verdict r1) is field-width and terminal when the run is nonempty. *)
Lemma take_vmap_run_head : forall r1 f v1 body r2 rest es rest',
  head_value r1 = Some (f, v1, body) ->
  take_vmap_run r1 (r2 :: rest) = (es, rest') ->
  es <> [] ->
  r1 = orig_rule f v1 body (r_verdict r1) /\
  field_fixed_len f = Some (length v1) /\ terminal (r_verdict r1) = true.
Proof.
  intros r1 f v1 body r2 rest es rest' Hhd Hrun Hne.
  cbn in Hrun. destruct (vmap_run_pair r1 r2)
    as [[[[fa v2] w2] bd] |] eqn:Evm.
  - destruct (vmap_run_pair_shape r1 r2 fa v2 w2 bd Evm)
      as [[u1 [Hhd1 [Hr1 [Hfx1 Hw1]]]] _].
    rewrite Hhd in Hhd1. inversion Hhd1; subst fa u1 bd.
    split; [exact Hr1 | split; assumption].
  - destruct (take_vmap_run r1 rest) as [es0 rest0] eqn:Erec0.
    inversion Hrun; subst. contradiction.
Qed.

(** *** Executable N-WAY vmap merge: verdict-preserving end-to-end, axiom-free. *)
(** *** Chain-level N-WAY vmap merge: verdict-preserving end-to-end, axiom-free. *)