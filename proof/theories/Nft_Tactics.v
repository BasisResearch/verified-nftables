(** * Nft_Tactics: a readable predicate / notation / tactic layer for stating and
      proving per-configuration theorems about concrete .nft rulesets.

    Proofs about a concrete ruleset (e.g. [Optiplex_Antispoof.v], [Router_*.v],
    [Ruleset_Verified.v]) repeat two shapes:

      (a) "chain C, run on packet p, gives verdict V" — i.e.
          [eval_table fuel cs C p = V], either for a fully CONCRETE p (closed by
          [vm_compute]) or for a SYMBOLIC p constrained by field hypotheses
          (closed by the shared [Eval_Fw.eval_fw_core] rewrite/cbn engine after
          unfolding the chain definitions); and
      (b) "field F of p equals the typed value V" — i.e.
          [field_value F p = encode V], the hypotheses those theorems take.

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

From Stdlib Require Import List String NArith.
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
                      (p : packet) (v : verdict) : Prop :=
  eval_table fuel cs c p = v.

Definition nft_accepts (fuel : nat) (cs : list (string * chain)) (c : chain)
                       (p : packet) : Prop := nft_yields fuel cs c p Accept.
Definition nft_drops (fuel : nat) (cs : list (string * chain)) (c : chain)
                     (p : packet) : Prop := nft_yields fuel cs c p Drop.

(** "field [f] of packet [p] holds the register bytes of typed value [v]" —
    routes the literal through the central [Nftval.encode] (validity-checked
    datatypes) instead of a bare byte list. *)
Definition nft_field_is (f : field) (p : packet) (v : nftval) : Prop :=
  field_value f p = encode v.

(** A single match condition fires / does not fire on [p]. *)
Definition nft_match_fires  (m : matchcond) (p : packet) : Prop :=
  eval_matchcond_body m p = true.
Definition nft_match_blocks (m : matchcond) (p : packet) : Prop :=
  eval_matchcond_body m p = false.

(* ------------------------------------------------------------------ *)
(** ** Soundness anchors: each predicate is its underlying statement.

    These are the witnesses the reviewer checks — every predicate unfolds to the
    real [eval_table] / [field_value] / [eval_matchcond_body] proposition, so the
    readable layer cannot smuggle in a weaker claim. *)
Lemma nft_yields_spec : forall fuel cs c p v,
  nft_yields fuel cs c p v <-> eval_table fuel cs c p = v.
Proof. intros. unfold nft_yields. reflexivity. Qed.

Lemma nft_accepts_spec : forall fuel cs c p,
  nft_accepts fuel cs c p <-> eval_table fuel cs c p = Accept.
Proof. intros. unfold nft_accepts, nft_yields. reflexivity. Qed.

Lemma nft_drops_spec : forall fuel cs c p,
  nft_drops fuel cs c p <-> eval_table fuel cs c p = Drop.
Proof. intros. unfold nft_drops, nft_yields. reflexivity. Qed.

Lemma nft_field_is_spec : forall f p v,
  nft_field_is f p v <-> field_value f p = encode v.
Proof. intros. unfold nft_field_is. reflexivity. Qed.

Lemma nft_match_fires_spec : forall m p,
  nft_match_fires m p <-> eval_matchcond_body m p = true.
Proof. intros. unfold nft_match_fires. reflexivity. Qed.

Lemma nft_match_blocks_spec : forall m p,
  nft_match_blocks m p <-> eval_matchcond_body m p = false.
Proof. intros. unfold nft_match_blocks. reflexivity. Qed.

(* ================================================================== *)
(** * Notations — a property reads close to the nftables intent. *)

Declare Scope nft_scope.
Delimit Scope nft_scope with nft.

(** "chain [c] accepts/drops/gives-[v] packet [p] in table [cs] with budget
    [fuel]".  [cs]/[fuel] are usually module-level definitions
    ([vmfilter_chains]/[vm_fuel], [firewall_chains]/[fw_fuel]), so this reads e.g.
    [vmfilter_output drops p in vmfilter_chains fuel vm_fuel]. *)
Notation "c 'accepts' p 'under' cs 'budget' fuel" :=
  (nft_accepts fuel cs c p) (at level 70, p at next level) : nft_scope.
Notation "c 'denies' p 'under' cs 'budget' fuel" :=
  (nft_drops fuel cs c p) (at level 70, p at next level) : nft_scope.
Notation "c 'gives' v 'on' p 'under' cs 'budget' fuel" :=
  (nft_yields fuel cs c p v) (at level 70, p at next level) : nft_scope.

(** "field [f] of [p] is [v]" — the typed field-value hypothesis. *)
Notation "'fieldof' f p '===' v" :=
  (nft_field_is f p v) (at level 70, f at level 0, p at level 0, v at next level) : nft_scope.

Open Scope nft_scope.

(* ================================================================== *)
(** * One-step chain lemmas (shared; generalise [Optiplex_Antispoof]'s local
      [erj_drop_first]/[erj_skip] so any per-config proof can thread a chain
      rule-by-rule).  [eval_rules_j] is [Global Opaque] (Eval_Fw.v); these step it. *)

(** A rule that LOADS, APPLIES, and yields a terminal [Drop] decides the chain. *)
Lemma rule_fires_drop : forall f cs r rest p,
  rule_loadable r p = true -> rule_applies r p = true -> outcome r p = Some Drop ->
  eval_rules_j (S f) cs (r :: rest) p = Some Drop.
Proof.
  intros f cs r rest p Hld Hap Hout.
  rewrite erj_cons, Hld, Hap, Hout. reflexivity.
Qed.

(** Likewise for a terminal [Accept]. *)
Lemma rule_fires_accept : forall f cs r rest p,
  rule_loadable r p = true -> rule_applies r p = true -> outcome r p = Some Accept ->
  eval_rules_j (S f) cs (r :: rest) p = Some Accept.
Proof.
  intros f cs r rest p Hld Hap Hout.
  rewrite erj_cons, Hld, Hap, Hout. reflexivity.
Qed.

(** A rule whose match does NOT apply is skipped (the chain continues at [rest]),
    regardless of loadability. *)
Lemma rule_skips : forall f cs r rest p,
  rule_applies r p = false ->
  eval_rules_j (S f) cs (r :: rest) p = eval_rules_j f cs rest p.
Proof.
  intros f cs r rest p Hap.
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
    only by [pkt_env p = <env>] ([Hpe]) and [field_value]/[read_payload_ok]
    hypotheses.  Unfolds the predicate, [autounfold]s the registered chains, then
    runs the shared [Eval_Fw.eval_fw_core] rewrite/cbn engine. *)
Ltac nft_eval Hpe :=
  nft_unfold;
  autounfold with nft_chains;
  eval_fw_core Hpe.

(** [nft_field]: reduce a concrete [field_is]/[field_value] goal to its bytes. *)
Ltac nft_field := nft_unfold; vm_compute; reflexivity.
