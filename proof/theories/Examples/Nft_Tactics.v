(** * Nft_Tactics: a readable predicate / notation / tactic layer for stating and
      proving per-configuration theorems about concrete .nft rulesets.

    Proofs about a concrete ruleset (e.g. [Optiplex_Antispoof.v], [Router_*.v],
    [Ruleset_Verified.v]) repeat two shapes:

      (a) "chain C, run on packet p, gives verdict V" — i.e.
          [forall h, fst (eval_table h fuel cs C e p) = V] on the canonical
          unified evaluator, either for a fully CONCRETE p (closed by
          [vm_compute]) or for a SYMBOLIC p constrained by field hypotheses
          (closed by the shared [Eval_Fw.eval_fw_core] rewrite/cbn engine after
          unfolding the chain definitions); and
      (b) "field F of p equals the typed value V" — i.e.
          [field_value F e p = encode V], the hypotheses those theorems take.

    This file gives those shapes NAMES (the predicates [accepts]/[drops]/[yields]
    /[field_is]/[match_fires]/[match_blocks]), readable NOTATIONS, and TACTICS
    ([nft_decide] for concrete packets, [nft_eval] for symbolic ones via an
    [autounfold] hint DB of chain definitions).

    SOUNDNESS (this layer changes NOTHING about what is proved): every predicate is
    a TRANSPARENT [Definition] that is *definitionally* its underlying
    [eval_table]/[field_value]/[eval_matchcond_body] statement.  The [*_spec]
    lemmas below pin that down (each is proved by [reflexivity]/[iff_refl]), so a
    goal stated with the notation is convertible to — and provably equivalent to —
    the raw statement.  The tactics only run reduction (cbn/vm_compute) and rewrite
    the user's own hypotheses; none of them can close a FALSE goal (demonstrated in
    [Nft_Config_Demo.v]). *)

From Stdlib Require Import List String NArith Arith Lia.
From Nft Require Import Bytes Verdict Packet Syntax Semantics Nftval Eval_Fw.
Import ListNotations.
Open Scope string_scope.

(* ================================================================== *)
(** * Predicates — names for the recurring statement shapes. *)

(** Chain [c] (in table [cs], with [fuel] traversal budget), run on packet [p],
    returns the named verdict. *)
(** NOTE on naming: the readable NOTATION tokens below ([accepts], [denies], …)
    become Coq keywords once declared, so they cannot also be definition names.
    The predicates therefore carry an [nft_] prefix; the notations render them
    keyword-free. *)
(** Stated over the canonical unified evaluator [eval_table], for EVERY hook:
    the config surface asserts the verdict is what the unified semantics
    computes, and — quantifying over the hook — that it is hook-independent
    (which holds of every write-free / limiter-tolerant config the surface is
    used on).  [eval_table] takes the hook as its first argument. *)
Definition nft_yields (fuel : nat) (cs : list (string * chain)) (c : chain)
                      (e : env) (p : packet) (v : verdict) : Prop :=
  forall h, fst (eval_table h fuel cs c e p) = v.

Definition nft_accepts (fuel : nat) (cs : list (string * chain)) (c : chain)
                       (e : env) (p : packet) : Prop := nft_yields fuel cs c e p Accept.
Definition nft_drops (fuel : nat) (cs : list (string * chain)) (c : chain)
                     (e : env) (p : packet) : Prop := nft_yields fuel cs c e p Drop.

(** "field [f] of packet [p] holds the register bytes of typed value [v]" —
    routes the literal through the central [Nftval.encode] (validity-checked
    datatypes) instead of a bare byte list. *)
Definition nft_field_is (f : field) (e : env) (p : packet) (v : nftval) : Prop :=
  field_value f e p = encode v.

(** A single match condition fires / does not fire on [p]. *)
Definition nft_match_fires  (m : matchcond) (e : env) (p : packet) : Prop :=
  eval_matchcond_body m e p = true.
Definition nft_match_blocks (m : matchcond) (e : env) (p : packet) : Prop :=
  eval_matchcond_body m e p = false.

(* ------------------------------------------------------------------ *)
(** ** Soundness anchors: each predicate is its underlying statement.

    These are the witnesses the reviewer checks — every predicate unfolds to the
    real [eval_table] / [field_value] / [eval_matchcond_body] proposition, so the
    readable layer cannot smuggle in a weaker claim. *)
Lemma nft_yields_spec : forall fuel cs c e p v,
  nft_yields fuel cs c e p v <-> forall h, fst (eval_table h fuel cs c e p) = v.
Proof. intros. unfold nft_yields. reflexivity. Qed.

Lemma nft_accepts_spec : forall fuel cs c e p,
  nft_accepts fuel cs c e p <-> forall h, fst (eval_table h fuel cs c e p) = Accept.
Proof. intros. unfold nft_accepts, nft_yields. reflexivity. Qed.

Lemma nft_drops_spec : forall fuel cs c e p,
  nft_drops fuel cs c e p <-> forall h, fst (eval_table h fuel cs c e p) = Drop.
Proof. intros. unfold nft_drops, nft_yields. reflexivity. Qed.

Lemma nft_field_is_spec : forall f e p v,
  nft_field_is f e p v <-> field_value f e p = encode v.
Proof. intros. unfold nft_field_is. reflexivity. Qed.

Lemma nft_match_fires_spec : forall m e p,
  nft_match_fires m e p <-> eval_matchcond_body m e p = true.
Proof. intros. unfold nft_match_fires. reflexivity. Qed.

Lemma nft_match_blocks_spec : forall m e p,
  nft_match_blocks m e p <-> eval_matchcond_body m e p = false.
Proof. intros. unfold nft_match_blocks. reflexivity. Qed.

(* ================================================================== *)
(** * Notations — a property reads close to the nftables intent. *)

Declare Scope nft_scope.
Delimit Scope nft_scope with nft.

(** "chain [c] accepts/drops/gives-[v] packet [p] in table [cs] with budget
    [fuel]".  [cs]/[fuel] are usually module-level definitions
    ([vmfilter_chains]/[vm_fuel], [firewall_chains]/[fw_fuel]), so this reads e.g.
    [vmfilter_output drops p in vmfilter_chains fuel vm_fuel]. *)
Notation "c 'accepts' p 'in' e 'under' cs 'budget' fuel" :=
  (nft_accepts fuel cs c e p) (at level 70, p at next level, e at next level) : nft_scope.
Notation "c 'denies' p 'in' e 'under' cs 'budget' fuel" :=
  (nft_drops fuel cs c e p) (at level 70, p at next level, e at next level) : nft_scope.
Notation "c 'gives' v 'on' p 'in' e 'under' cs 'budget' fuel" :=
  (nft_yields fuel cs c e p v) (at level 70, p at next level, e at next level) : nft_scope.

(** "field [f] of [p] (under shared env [e]) is [v]" — the typed field-value
    hypothesis.  The env matters only for env-reading fields (ct/rt/fib/numgen);
    a payload/meta field reads the same bytes under every [e]. *)
Notation "'fieldof' f e p '===' v" :=
  (nft_field_is f e p v)
    (at level 70, f at level 0, e at level 0, p at level 0, v at next level) : nft_scope.

Open Scope nft_scope.

(* ================================================================== *)
(** * Fuel-budget discharge — making the notations' [budget] provably inert.

    Every notation above carries a fuel budget, and the unified evaluator
    silently falls back to the chain POLICY when the budget runs out mid-jump — a
    verdict the kernel can never produce (nft rejects jump loops at load time; the
    kernel bounds the jump stack at 16).  Until M4 the adequacy of each module's
    budget was an UNSTATED side condition.  The lemmas here discharge it:
    once [Semantics.chain_ranked] holds (via [Semantics.chains_plain_ranked]
    for chains that never realise a jump/goto under the pinned env) and the budget
    is at least the computable [Semantics.sufficient_fuel cs (c_rules c)] (a
    [vm_compute]-able number), the stated property is the SAME at every adequate
    budget — so a theorem proved at one budget is fuel-free above the bound.
    Worked instance: [Tutorial_Proofs.tutorial_blocks_exactly_any_fuel]; the full
    rationale (including why naive fuel monotonicity is FALSE for the jump strand)
    sits on Semantics.v § "Fuel discipline for the unified evaluator", and the user
    guidance in proof/CONFIG_PROOFS.md § "Choosing the fuel budget". *)

Lemma nft_yields_fuel_indep : forall rank cs c e p v fuel fuel',
  (forall h, chain_ranked h rank cs e) ->
  sufficient_fuel cs (c_rules c) <= fuel ->
  sufficient_fuel cs (c_rules c) <= fuel' ->
  (nft_yields fuel cs c e p v <-> nft_yields fuel' cs c e p v).
Proof.
  intros rank cs c e p v fuel fuel' Hcr Hf Hf'. unfold nft_yields.
  split; intros H h; specialize (H h);
    [ rewrite (eval_table_fuel_indep h rank cs e (Hcr h) c p fuel' fuel Hf' Hf)
    | rewrite (eval_table_fuel_indep h rank cs e (Hcr h) c p fuel fuel' Hf Hf') ];
    exact H.
Qed.

Lemma nft_accepts_fuel_indep : forall rank cs c e p fuel fuel',
  (forall h, chain_ranked h rank cs e) ->
  sufficient_fuel cs (c_rules c) <= fuel ->
  sufficient_fuel cs (c_rules c) <= fuel' ->
  (nft_accepts fuel cs c e p <-> nft_accepts fuel' cs c e p).
Proof. intros. now apply nft_yields_fuel_indep with (rank := rank). Qed.

Lemma nft_drops_fuel_indep : forall rank cs c e p fuel fuel',
  (forall h, chain_ranked h rank cs e) ->
  sufficient_fuel cs (c_rules c) <= fuel ->
  sufficient_fuel cs (c_rules c) <= fuel' ->
  (nft_drops fuel cs c e p <-> nft_drops fuel' cs c e p).
Proof. intros. now apply nft_yields_fuel_indep with (rank := rank). Qed.

(* ================================================================== *)
(** * Write-freedom: why the [forall h] is provable.

    [nft_yields] quantifies the verdict over EVERY hook.  For a WRITE-FREE
    config (no meta/ct set, dynset, notrack, limiter/quota/connlimit anywhere
    in the evaluated table) the unified evaluator's verdict is hook-independent:
    every rule's [rule_step] leaves the state untouched
    ([Semantics.rule_step_writefree_state]) and — being nat-free — steps to the
    same verdict at every hook ([rule_step_natfree_hookindep]), so the whole
    traversal is the same at every hook.  The quantified statement is then
    exactly "the config's verdict is [v]".  [nft_writefree] is the one-[vm_compute]
    check that a config is in this class; a config with writes is OUTSIDE it and
    its per-hook verdict must be reasoned about directly on [eval_table] (see
    Regression/Setread_UnderJump.v for the divergence witness). *)

Definition nft_writefree (cs : list (string * chain)) (c : chain) : bool :=
  forallb rule_writefree (c_rules c) && chains_writefree cs.

(** A nat-free rule's terminal takes no hook-dependent NAT decision (its data
    plane is [r_nat] = None: [nat_drops] is [false], [apply_nat] is the
    identity), so it steps identically at every hook. *)
Lemma terminal_step_natfree_hookindep : forall (h1 h2 : hook_id) r e p,
  rule_natfree r = true ->
  terminal_step h1 r e p = terminal_step h2 r e p.
Proof.
  intros h1 h2 r e p Hnat. unfold rule_natfree in Hnat.
  unfold terminal_step, has_effect_terminal, nat_drops, apply_nat.
  destruct (r_nat r) as [n|]; [discriminate Hnat|]. reflexivity.
Qed.

Lemma end_step_natfree_hookindep : forall (h1 h2 : hook_id) r e p,
  rule_natfree r = true ->
  end_step h1 r e p = end_step h2 r e p.
Proof.
  intros h1 h2 r e p Hnat. unfold end_step.
  destruct (r_vmap r) as [vm|]; [| apply terminal_step_natfree_hookindep; exact Hnat].
  destruct (vmap_loadable (Some vm) p); [| reflexivity].
  cbv zeta.
  destruct (vm_keyf vm) as [[f ts]|].
  - destruct (assoc_verdict (apply_transforms ts (field_value f e p))
                            (e_vmap e (vm_name vm)));
      [reflexivity | apply terminal_step_natfree_hookindep; exact Hnat].
  - destruct (assoc_verdict
                (List.concat (map (fun f => field_value f e p) (vm_fields vm)))
                (e_vmap e (vm_name vm)));
      [reflexivity | apply terminal_step_natfree_hookindep; exact Hnat].
Qed.

(** A nat-free rule steps to the same result at every hook: the body walk is
    hook-free and the end takes no hook-dependent NAT decision. *)
Lemma rule_step_natfree_hookindep : forall (h1 h2 : hook_id) r e p,
  rule_natfree r = true ->
  rule_step h1 r e p = rule_step h2 r e p.
Proof.
  intros h1 h2 r e p Hnat. unfold rule_step.
  destruct (body_step (r_body r) e p) as [e' p'|e' p'|e' p']; try reflexivity.
  apply end_step_natfree_hookindep; exact Hnat.
Qed.

(** Hook-independence of the unified rule traversal on write-free rules: each
    [rule_step] leaves the state at [(e,p)] and — being nat-free — steps to the
    same verdict at every hook ([rule_step_natfree_hookindep]), so the whole fold
    agrees at any two hooks. *)
Lemma eval_rules_hookindep_writefree : forall (h1 h2 : hook_id) fuel cs rs e p,
  forallb rule_writefree rs = true ->
  chains_writefree cs = true ->
  eval_rules h1 fuel cs rs e p = eval_rules h2 fuel cs rs e p.
Proof.
  induction fuel as [| f IH]; intros cs rs e p Hrs Hcs; [reflexivity|].
  destruct rs as [| r rest]; [reflexivity|].
  cbn [forallb] in Hrs. apply Bool.andb_true_iff in Hrs. destruct Hrs as [Hr Hrest].
  assert (Hnat : rule_natfree r = true).
  { unfold rule_writefree, rule_mutfree in Hr.
    apply Bool.andb_true_iff in Hr as [_ Hn]. exact Hn. }
  cbn [eval_rules].
  rewrite (rule_step_natfree_hookindep h1 h2 r e p Hnat).
  destruct (rule_step h2 r e p) as [[v|] [e' p']]; [| now apply IH].
  destruct v as [ | | | tc cc | lo hi bp fo | n | n | ];
    try reflexivity; try (now apply IH).
  - (* Jump *)
    destruct (chain_lookup cs n) as [ch|] eqn:Hlk; [| now apply IH].
    rewrite (IH cs (c_rules ch) e' p' (chains_writefree_lookup cs n ch Hcs Hlk) Hcs).
    destruct (eval_rules h2 f cs (c_rules ch) e' p') as [[w|] [e2 p2]];
      [reflexivity | now apply IH].
  - (* Goto *)
    destruct (chain_lookup cs n) as [ch|] eqn:Hlk; [| reflexivity].
    apply IH; [eapply chains_writefree_lookup; eauto | exact Hcs].
Qed.

Lemma eval_table_hookindep_writefree : forall (h1 h2 : hook_id) fuel cs base e p,
  forallb rule_writefree (c_rules base) = true ->
  chains_writefree cs = true ->
  eval_table h1 fuel cs base e p = eval_table h2 fuel cs base e p.
Proof.
  intros h1 h2 fuel cs base e p Hb Hcs. unfold eval_table.
  now rewrite (eval_rules_hookindep_writefree h1 h2 fuel cs (c_rules base) e p Hb Hcs).
Qed.

(** For a write-free config the surface predicate is equivalent to the verdict
    at any single hook (the unified evaluator being hook-independent there). *)
Lemma nft_yields_writefree_at : forall h fuel cs c e p v,
  nft_writefree cs c = true ->
  (nft_yields fuel cs c e p v <-> fst (eval_table h fuel cs c e p) = v).
Proof.
  intros h fuel cs c e p v H.
  apply Bool.andb_true_iff in H. destruct H as [Hc Hcs].
  unfold nft_yields. split.
  - intros Hy. exact (Hy h).
  - intros Hh h'.
    rewrite (eval_table_hookindep_writefree h' h fuel cs c e p Hc Hcs).
    exact Hh.
Qed.

(* ================================================================== *)
(** * Tactics. *)

(** Unfold the readable predicates so the bare statement is exposed for the
    reduction engine / hypothesis rewrites. *)
Ltac nft_unfold :=
  unfold nft_accepts, nft_drops, nft_yields, nft_field_is,
         nft_match_fires, nft_match_blocks in *.

(** A hint DB of chain / fuel / table definitions.  Each per-config module
    registers its own chains with [Hint Unfold eval_table <fuel> <chains> :
    nft_chains], after which [nft_eval] needs no per-module unfold list. *)
Create HintDb nft_chains.
#[export] Hint Unfold eval_table : nft_chains.

(** [nft_decide]: discharge a fully CONCRETE configuration goal (closed packet,
    closed chains) — the [vm_compute; reflexivity] shape.  The surface predicate
    quantifies over the hook, so [intros] the hook first.  Also proves the
    boolean/field predicates and disequalities of concrete verdicts. *)
Ltac nft_decide :=
  nft_unfold; intros;
  try (vm_compute; reflexivity);
  try (vm_compute; discriminate).

(** [nft_eval Hpe]: discharge a SYMBOLIC configuration goal — packet constrained
    only by [e = <env>] ([Hpe]) and [field_value]/[read_payload_ok]
    hypotheses.  Unfolds the predicate, introduces the hook, [autounfold]s the
    registered chains, then runs the shared [Eval_Fw.eval_fw_core] engine over
    [eval_rules]. *)
Ltac nft_eval Hpe :=
  nft_unfold; intro;
  (* normalise any typed [encode] on the RHS of a field hypothesis to its byte
     literal (the reduction engine keeps [field_value] folded, so a residual
     [encode _]/[Pos.to_nat] in a vmap key would otherwise stall [cbn]). *)
  repeat match goal with
  | H : field_value ?f ?e ?p = encode ?v |- _ =>
      let r' := eval vm_compute in (encode v) in change (field_value f e p = r') in H
  end;
  autounfold with nft_chains;
  eval_fw_core Hpe.

(** [nft_field]: reduce a concrete [field_is]/[field_value] goal to its bytes. *)
Ltac nft_field := nft_unfold; vm_compute; reflexivity.

(* ================================================================== *)
(** * Exactness support — "this chain blocks EXACTLY that range".

    An exactness theorem is an IFF: the chain drops [p] *iff* the address is in
    the range.  The one-directional demos above never need to reason about the
    packet on the NON-matching side; the lemmas here supply that, so a user can
    prove an iff without touching the evaluator internals:

    - [nft_match_MEq_iff]          an [MEq] match is definitionally a PREFIX
                                   equation on the field's bytes;
    - [nft_payload_prefix] and its address instances [nft_saddr_prefix] /
      [nft_daddr_prefix]           the parser's k-byte prefix field (what
                                   `ip saddr a.b.c.0/24` lowers to) reads the
                                   first k bytes of the 4-byte address field;
    - [read_payload_ok_shorter]    well-formedness of the shorter prefix read
                                   follows from the natural 4-byte hypothesis;
    - [bytes3_eq_iff]/[bytes4_eq_iff]  byte-list equations <-> per-byte
                                   conjunctions (the range statement a user reads);
    - [nft_single_rule_drop_iff] / [nft_single_rule_accept_iff]
                                   a one-rule accept-policy chain drops iff its
                                   rule fires — the chain-level iff;
    - [nft_prefix_chain_drop_iff] / [nft_prefix_chain_accept_iff]
                                   the packaged headline: an accept-policy chain
                                   whose single rule drops on a payload-prefix
                                   match drops [p] IFF the prefix equation holds.

    Worked end-to-end instance: [Tutorial_Proofs.v] (for
    [rulesets/tutorial.nft]; guide: proof/CONFIG_PROOFS.md, "Tutorial"). *)

(** An [MEq] match fires iff the prefix equation holds ([MEq] is a prefix
    compare: [Semantics.eval_matchcond_body]). *)
Lemma nft_match_MEq_iff : forall f v e p,
  nft_match_fires (MEq f v) e p
  <-> firstn (List.length v) (field_value f e p) = v.
Proof.
  intros f v e p. unfold nft_match_fires. cbn [eval_matchcond_body].
  apply data_eqb_true_iff.
Qed.

(** A shorter payload read at the same offset is a [firstn] of a longer one
    (both are [firstn]s of the same [skipn]). *)
Lemma nft_payload_prefix : forall b off k w e p, k <= w ->
  field_value (FPayload b off k) e p = firstn k (field_value (FPayload b off w) e p).
Proof.
  intros b off k w e p Hkw. unfold field_value. cbn [field_load do_load].
  destruct b; unfold read_payload, slice;
    rewrite firstn_firstn, Nat.min_l by lia; reflexivity.
Qed.

(** Address instances: [FIp4Saddr]/[FIp4Daddr] are the 4-byte payload reads at
    network offsets 12/16, so their k-byte prefix fields are [firstn k] of them. *)
Lemma nft_saddr_prefix : forall k e p, k <= 4 ->
  field_value (FPayload PNetwork 12 k) e p = firstn k (field_value FIp4Saddr e p).
Proof.
  intros k e p Hk.
  change (field_value FIp4Saddr e p) with (field_value (FPayload PNetwork 12 4) e p).
  now apply nft_payload_prefix.
Qed.

Lemma nft_daddr_prefix : forall k e p, k <= 4 ->
  field_value (FPayload PNetwork 16 k) e p = firstn k (field_value FIp4Daddr e p).
Proof.
  intros k e p Hk.
  change (field_value FIp4Daddr e p) with (field_value (FPayload PNetwork 16 4) e p).
  now apply nft_payload_prefix.
Qed.

(** Reading fewer bytes at the same offset stays in bounds. *)
Lemma read_payload_ok_shorter : forall b off k w p, k <= w ->
  read_payload_ok b off w p = true -> read_payload_ok b off k p = true.
Proof.
  intros b off k w p Hkw H. unfold read_payload_ok in *.
  apply Bool.andb_true_iff in H as [Hl Hlen].
  apply Bool.andb_true_iff; split; [exact Hl|].
  apply Bool.negb_true_iff in Hlen. apply Bool.negb_true_iff.
  apply Nat.ltb_ge in Hlen. apply Nat.ltb_ge. lia.
Qed.

(** Byte-tuple equations, as the per-byte conjunctions a range statement uses. *)
Lemma bytes3_eq_iff : forall a b c x y z : nat,
  [a; b; c] = [x; y; z] <-> a = x /\ b = y /\ c = z.
Proof.
  split.
  - intro H. injection H. tauto.
  - intros (-> & -> & ->). reflexivity.
Qed.

Lemma bytes4_eq_iff : forall a b c d x y z w : nat,
  [a; b; c; d] = [x; y; z; w] <-> a = x /\ b = y /\ c = z /\ d = w.
Proof.
  split.
  - intro H. injection H. tauto.
  - intros (-> & -> & -> & ->). reflexivity.
Qed.

(** The verdict of an Accept-policy chain whose single rule is
    "payload-prefix match => Drop" (exactly what `ip saddr a.b.c.0/24 drop`
    parses to): the unified evaluator settles [Drop] when the prefix match fires
    and falls through to the [Accept] policy otherwise.  Hook-independent (a
    match-only rule with a static terminal), so it holds at every [h]. *)
Lemma nft_prefix_chain_verdict : forall h fuel cs b off len v e p,
  read_payload_ok b off len p = true ->
  fst (eval_table h (S fuel) cs
     {| c_policy := Accept;
        c_rules := [{| r_body := [BMatch (MEq (FPayload b off len) v)];
     r_outcome := OVerdict Drop; r_after := [] |}] |} e p)
  = (if data_eqb (firstn (List.length v) (field_value (FPayload b off len) e p)) v
     then Drop else Accept).
Proof.
  intros h fuel cs b off len v e p Hok.
  unfold eval_table. cbn [c_rules c_policy]. rewrite eru_cons.
  unfold rule_step, end_step, terminal_step, has_effect_terminal.
  cbn [body_step r_body body_res_state r_vmap r_outcome].
  unfold eval_matchcond, match_loadable, eval_matchcond_body,
    fields_loadable, field_loadable, load_ok.
  cbn -[field_value read_payload_ok data_eqb firstn].
  rewrite Hok.
  destruct (data_eqb (firstn (List.length v) (field_value (FPayload b off len) e p)) v);
    cbn -[eval_rules field_value data_eqb firstn];
    first [ reflexivity | rewrite eru_empty; reflexivity ].
Qed.

(** The packaged headline lemmas: an Accept-policy chain whose single rule is
    the payload-prefix match => Drop drops [p] IFF the prefix equation holds —
    and accepts [p] IFF it does not.  The only packet hypothesis is that the read
    is in bounds. *)
Lemma nft_prefix_chain_drop_iff : forall fuel cs b off len v e p,
  read_payload_ok b off len p = true ->
  (nft_drops (S fuel) cs
     {| c_policy := Accept;
        c_rules := [{| r_body := [BMatch (MEq (FPayload b off len) v)];
     r_outcome := OVerdict Drop; r_after := [] |}] |} e p
   <-> firstn (List.length v) (field_value (FPayload b off len) e p) = v).
Proof.
  intros fuel cs b off len v e p Hok. unfold nft_drops, nft_yields. split.
  - intros Hy. specialize (Hy Hinput).
    rewrite (nft_prefix_chain_verdict Hinput fuel cs b off len v e p Hok) in Hy.
    destruct (data_eqb (firstn (List.length v) (field_value (FPayload b off len) e p)) v)
      eqn:E; [ now apply data_eqb_true_iff | discriminate Hy ].
  - intros Heq h. rewrite (nft_prefix_chain_verdict h fuel cs b off len v e p Hok).
    replace (data_eqb (firstn (List.length v) (field_value (FPayload b off len) e p)) v)
      with true; [ reflexivity | symmetry; now apply data_eqb_true_iff ].
Qed.

Lemma nft_prefix_chain_accept_iff : forall fuel cs b off len v e p,
  read_payload_ok b off len p = true ->
  (nft_accepts (S fuel) cs
     {| c_policy := Accept;
        c_rules := [{| r_body := [BMatch (MEq (FPayload b off len) v)];
     r_outcome := OVerdict Drop; r_after := [] |}] |} e p
   <-> firstn (List.length v) (field_value (FPayload b off len) e p) <> v).
Proof.
  intros fuel cs b off len v e p Hok. unfold nft_accepts, nft_yields. split.
  - intros Hy Heq. specialize (Hy Hinput).
    rewrite (nft_prefix_chain_verdict Hinput fuel cs b off len v e p Hok) in Hy.
    replace (data_eqb (firstn (List.length v) (field_value (FPayload b off len) e p)) v)
      with true in Hy; [ discriminate Hy | symmetry; now apply data_eqb_true_iff ].
  - intros Hne h. rewrite (nft_prefix_chain_verdict h fuel cs b off len v e p Hok).
    destruct (data_eqb (firstn (List.length v) (field_value (FPayload b off len) e p)) v)
      eqn:E; [ apply data_eqb_true_iff in E; contradiction | reflexivity ].
Qed.
