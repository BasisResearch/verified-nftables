(** * Nft_Tactics: a readable predicate / notation / tactic layer for stating and
      proving per-configuration theorems about concrete .nft rulesets.

    Proofs about a concrete ruleset (e.g. [Optiplex_Antispoof.v], [Router_*.v],
    [Ruleset_Verified.v]) repeat two shapes:

      (a) "chain C, run on packet p, gives verdict V" — i.e.
          [eval_table fuel cs C e p = V], either for a fully CONCRETE p (closed by
          [vm_compute]) or for a SYMBOLIC p constrained by field hypotheses
          (closed by the shared [Eval_Fw.eval_fw_core] rewrite/cbn engine after
          unfolding the chain definitions); and
      (b) "field F of p equals the typed value V" — i.e.
          [field_value F e p = encode V], the hypotheses those theorems take.

    This file gives those shapes NAMES (the predicates [accepts]/[drops]/[yields]
    /[field_is]/[match_fires]/[match_blocks]), readable NOTATIONS, and TACTICS
    ([nft_decide] for concrete packets, [nft_eval] for symbolic ones via an
    [autounfold] hint DB of chain definitions, plus the [rule_fires_*]/[rule_skips]
    one-step lemmas).

    SOUNDNESS (this layer changes NOTHING about what is proved): every predicate is
    a TRANSPARENT [Definition] that is *definitionally* its underlying [eval_table]/
    [field_value]/[eval_matchcond_body] statement.  The [*_spec] lemmas below pin
    that down (each is proved by [reflexivity]/[iff_refl]), so a goal stated with
    the notation is convertible to — and provably equivalent to — the raw
    statement.  The tactics only run reduction (cbn/vm_compute) and rewrite the
    user's own hypotheses; none of them can close a FALSE goal (demonstrated in
    [Nft_Config_Demo.v]).  This file is purely ADDITIVE: it edits no existing
    definition and reproves no existing theorem differently. *)

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
Definition nft_yields (fuel : nat) (cs : list (string * chain)) (c : chain)
                      (e : env) (p : packet) (v : verdict) : Prop :=
  eval_table fuel cs c e p = v.

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
  nft_yields fuel cs c e p v <-> eval_table fuel cs c e p = v.
Proof. intros. unfold nft_yields. reflexivity. Qed.

Lemma nft_accepts_spec : forall fuel cs c e p,
  nft_accepts fuel cs c e p <-> eval_table fuel cs c e p = Accept.
Proof. intros. unfold nft_accepts, nft_yields. reflexivity. Qed.

Lemma nft_drops_spec : forall fuel cs c e p,
  nft_drops fuel cs c e p <-> eval_table fuel cs c e p = Drop.
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
(** * One-step chain lemmas (shared; generalise [Optiplex_Antispoof]'s local
      [erj_drop_first]/[erj_skip] so any per-config proof can thread a chain
      rule-by-rule).  [eval_rules_j] is [Global Opaque] (Eval_Fw.v); these step it. *)

(** A rule that LOADS, APPLIES, and yields a terminal [Drop] decides the chain. *)
Lemma rule_fires_drop : forall f cs r rest e p,
  rule_loadable r e p = true -> rule_applies r e p = true -> outcome r e p = Some Drop ->
  eval_rules_j (S f) cs (r :: rest) e p = Some Drop.
Proof.
  intros f cs r rest e p Hld Hap Hout.
  rewrite erj_cons, Hld, Hap, Hout. reflexivity.
Qed.

(** Likewise for a terminal [Accept]. *)
Lemma rule_fires_accept : forall f cs r rest e p,
  rule_loadable r e p = true -> rule_applies r e p = true -> outcome r e p = Some Accept ->
  eval_rules_j (S f) cs (r :: rest) e p = Some Accept.
Proof.
  intros f cs r rest e p Hld Hap Hout.
  rewrite erj_cons, Hld, Hap, Hout. reflexivity.
Qed.

(** A rule whose match does NOT apply is skipped (the chain continues at [rest]),
    regardless of loadability. *)
Lemma rule_skips : forall f cs r rest e p,
  rule_applies r e p = false ->
  eval_rules_j (S f) cs (r :: rest) e p = eval_rules_j f cs rest e p.
Proof.
  intros f cs r rest e p Hap.
  rewrite erj_cons, Hap, Bool.andb_false_r. reflexivity.
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
    closed chains) — the [vm_compute; reflexivity] shape.  Also proves the
    boolean/field predicates and disequalities of concrete verdicts. *)
Ltac nft_decide :=
  nft_unfold;
  try (vm_compute; reflexivity);
  try (vm_compute; discriminate).

(** [nft_eval Hpe]: discharge a SYMBOLIC configuration goal — packet constrained
    only by [e = <env>] ([Hpe]) and [field_value]/[read_payload_ok]
    hypotheses.  Unfolds the predicate, [autounfold]s the registered chains, then
    runs the shared [Eval_Fw.eval_fw_core] rewrite/cbn engine. *)
Ltac nft_eval Hpe :=
  nft_unfold;
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

(** A one-rule chain with Accept policy drops [p] IFF its rule fires (given the
    rule loads on [p] and its outcome is a terminal [Drop]). *)
Lemma nft_single_rule_drop_iff : forall fuel cs r e p,
  rule_loadable r e p = true ->
  outcome r e p = Some Drop ->
  (nft_drops (S fuel) cs {| c_policy := Accept; c_rules := [r] |} e p
   <-> rule_applies r e p = true).
Proof.
  intros fuel cs r e p Hld Hout.
  unfold nft_drops, nft_yields, eval_table. cbn [c_rules c_policy].
  rewrite erj_cons, Hld, Hout. cbn [andb].
  destruct (rule_applies r e p).
  - split; reflexivity.
  - rewrite erj_empty. split; discriminate.
Qed.

(** …and accepts [p] IFF its rule does NOT fire. *)
Lemma nft_single_rule_accept_iff : forall fuel cs r e p,
  rule_loadable r e p = true ->
  outcome r e p = Some Drop ->
  (nft_accepts (S fuel) cs {| c_policy := Accept; c_rules := [r] |} e p
   <-> rule_applies r e p = false).
Proof.
  intros fuel cs r e p Hld Hout.
  unfold nft_accepts, nft_yields, eval_table. cbn [c_rules c_policy].
  rewrite erj_cons, Hld, Hout. cbn [andb].
  destruct (rule_applies r e p).
  - split; discriminate.
  - rewrite erj_empty. split; reflexivity.
Qed.

(** The packaged headline lemmas: an Accept-policy chain whose single rule is
    "payload-prefix match => Drop" (exactly what `ip saddr a.b.c.0/24 drop`
    parses to) drops [p] IFF the prefix equation holds — and accepts [p] IFF it
    does not.  The only packet hypothesis is that the read is in bounds. *)
Lemma nft_prefix_chain_drop_iff : forall fuel cs b off len v e p,
  read_payload_ok b off len p = true ->
  (nft_drops (S fuel) cs
     {| c_policy := Accept;
        c_rules := [{| r_body := [BMatch (MEq (FPayload b off len) v)];
     r_outcome := OVerdict Drop; r_after := [] |}] |} e p
   <-> firstn (List.length v) (field_value (FPayload b off len) e p) = v).
Proof.
  intros fuel cs b off len v e p Hok.
  eapply iff_trans.
  { apply nft_single_rule_drop_iff.
    - unfold rule_loadable. cbn. now rewrite Hok.
    - reflexivity. }
  unfold rule_applies. cbn [r_body rule_applies_walk].
  unfold eval_matchcond. cbn [match_loadable].
  unfold field_loadable. cbn [field_load load_ok]. rewrite Hok.
  rewrite !Bool.andb_true_l, Bool.andb_true_r.
  apply data_eqb_true_iff.
Qed.

Lemma nft_prefix_chain_accept_iff : forall fuel cs b off len v e p,
  read_payload_ok b off len p = true ->
  (nft_accepts (S fuel) cs
     {| c_policy := Accept;
        c_rules := [{| r_body := [BMatch (MEq (FPayload b off len) v)];
     r_outcome := OVerdict Drop; r_after := [] |}] |} e p
   <-> firstn (List.length v) (field_value (FPayload b off len) e p) <> v).
Proof.
  intros fuel cs b off len v e p Hok.
  eapply iff_trans.
  { apply nft_single_rule_accept_iff.
    - unfold rule_loadable. cbn. now rewrite Hok.
    - reflexivity. }
  unfold rule_applies. cbn [r_body rule_applies_walk].
  unfold eval_matchcond. cbn [match_loadable eval_matchcond_body]. unfold Bytecode.eval_cmp.
  unfold field_loadable. cbn [field_load load_ok]. rewrite Hok.
  rewrite !Bool.andb_true_l, Bool.andb_true_r.
  split.
  - intros Hf He. apply data_eqb_true_iff in He. congruence.
  - intro Hne. destruct (data_eqb _ _) eqn:E; [|reflexivity].
    apply data_eqb_true_iff in E. contradiction.
Qed.
