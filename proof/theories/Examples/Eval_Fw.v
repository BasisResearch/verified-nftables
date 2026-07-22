(** * Shared symbolic-evaluation engine for the worked-ruleset proofs.

    [Example_Ruleset.v] (hand-translated AST) and [Ruleset_Verified.v]
    (parser-emitted AST) both symbolically evaluate the canonical unified
    evaluator [eval_table_u] one rule at a time.  The rewrite/cbn engine that
    drives that is identical between them; only the leading [unfold] of the
    module's own chain definitions differs.  This file factors out the common
    core so the two cannot drift:

      - [eru_nil] / [eru_cons]: one-step unfolding lemmas for the fuel-recursive
        chain interpreter [eval_rules_u], proven while it is still transparent;
      - [Global Opaque eval_rules_u]: keep it folded thereafter so [cbn] reduces
        only the *current* rule (via its [rule_step]) rather than the whole
        fuel-bounded traversal tree;
      - [Ltac eval_fw_core_u]: the shared rewrite/cbn loop.

    Each module then defines its own [eval_fw] as just its chain [unfold] followed
    by [eval_fw_core_u]. *)

From Stdlib Require Import List.
From Nft Require Import Bytes Verdict Packet Syntax Semantics.
Import ListNotations.

(** One-step unfolding lemmas for the fuel-recursive chain interpreter.  We keep
    [eval_rules_u] opaque during evaluation and step it with these, so [cbn] only
    ever reduces the *current* rule's [rule_step] (rather than symbolically
    expanding the whole fuel-bounded traversal tree, which blows up).  The state
    half [(env * packet)] is threaded exactly as the fold defines it. *)
Lemma eru_nil : forall h n cs e p, eval_rules_u h (S n) cs [] e p = (None, (e, p)).
Proof. reflexivity. Qed.

Lemma eru_cons : forall h f cs r rest e p,
  eval_rules_u h (S f) cs (r :: rest) e p =
  match rule_step h r e p with
  | (Some v, (e', p')) =>
      match v with
      | Jump n =>
          match chain_lookup cs n with
          | Some ch =>
              match eval_rules_u h f cs (c_rules ch) e' p' with
              | (Some w, s) => (Some w, s)
              | (None, (e'', p'')) => eval_rules_u h f cs rest e'' p''
              end
          | None => eval_rules_u h f cs rest e' p'
          end
      | Goto n =>
          match chain_lookup cs n with
          | Some ch => eval_rules_u h f cs (c_rules ch) e' p'
          | None    => (None, (e', p'))
          end
      | Return => (None, (e', p'))
      | Continue => eval_rules_u h f cs rest e' p'
      | _ => (Some v, (e', p'))
      end
  | (None, (e', p')) => eval_rules_u h f cs rest e' p'
  end.
Proof. reflexivity. Qed.

(** Empty rule list returns [None] with the state untouched regardless of fuel
    (covers the [O] fuel case that [eru_nil] does not). *)
Lemma eru_empty : forall h m cs e p, eval_rules_u h m cs [] e p = (None, (e, p)).
Proof. destruct m; reflexivity. Qed.

(** [eval_rules_u] is NOT set [Opaque]: the mixed already-canonical proofs step
    it with an explicit [cbn [eval_rules_u]] whitelist.  The engine below keeps it
    folded with the [cbn -[eval_rules_u ...]] blacklist instead, so both idioms
    coexist. *)

(** The point-interval membership identity [data_in_iv key (k, k) = data_eqb k key]
    used by the router vmap classifications (to turn point-interval lookups into a
    cascade of byte-equality tests without concrete-byte case analysis on the key)
    now lives canonically as [Bytes.data_in_iv_point]; it is re-exported here via
    the [Bytes] import, so callers' [rewrite data_in_iv_point] is unchanged. *)

(** The shared engine: step one rule at a time, rewriting the per-packet field
    values from the hypotheses as each rule's [rule_step] is reached.
    [field_value] / [eval_rules_u] are kept folded so the field hypotheses can
    rewrite [field_value _ e p] and the recursion does not explode.  Callers
    [unfold] their own [eval_table_u]/chain definitions first, then invoke this
    with the [e = ...] (concrete-env) hypothesis. *)
Ltac eval_fw_core_u Hpe :=
  try rewrite Hpe in * |- *;
  repeat first
    [ rewrite Hpe
    | rewrite eru_nil
    | rewrite eru_cons
    | match goal with H : field_value _ _ _ = _ |- _ => rewrite H end
    | match goal with H : read_payload_ok _ _ _ _ = _ |- _ => rewrite H end
    | match goal with H : concat_set_mem _ _ = _ |- _ => rewrite H end
    | progress unfold rule_step, end_step, terminal_step, vmap_loadable,
        eval_matchcond, eval_matchcond_body, match_loadable,
        fields_loadable, field_loadable, load_ok
    | progress cbn -[eval_rules_u field_value read_payload_ok concat_set_mem] ];
  reflexivity.

(** ** Generic per-rule [rule_step] reductions, shared by the config-proof files.

    A field load never consults the limiter bucket [e_limit], so a limiter
    consumption is invisible to every subsequent field read. *)
Lemma field_value_set_limit : forall f e p s q,
  field_value f (set_limit e p s) q = field_value f e q.
Proof.
  intros f e p s q. unfold field_value, do_load, set_limit, env_limit_upd, with_e_limit.
  destruct (field_load f); try reflexivity.
Qed.

(** An empty-body single-key verdict-map rule: its one [rule_step] is the
    verdict-map lookup on the key field (state untouched — no body, no writer). *)
Lemma vmap_single_step : forall h e p f nm,
  field_loadable f p = true ->
  rule_step h {| r_body := []; r_outcome := OVmap {| vm_fields := []; vm_keyf := Some (f, []); vm_name := nm |}; r_after := [] |} e p
  = (match assoc_verdict (field_value f e p) (e_vmap e nm) with
     | Some v => Some v | None => None end, (e, p)).
Proof.
  intros h e p f nm H.
  unfold rule_step. cbn [r_body body_step].
  unfold end_step. cbn [r_vmap r_outcome vm_keyf vm_name vm_fields].
  unfold vmap_loadable. cbn [vm_keyf]. rewrite H.
  cbn [apply_transforms fold_left].
  destruct (assoc_verdict (field_value f e p) (e_vmap e nm)) as [v|]; [reflexivity|].
  unfold terminal_step.
  cbn [has_effect_terminal r_nat r_tproxy r_fwd r_queue r_outcome r_verdict].
  reflexivity.
Qed.

(** An empty-body concat-key verdict-map rule: the lookup is on the concatenation
    of the key fields. *)
Lemma vmap_concat_step : forall h e p fs nm,
  fields_loadable fs p = true ->
  rule_step h {| r_body := []; r_outcome := OVmap {| vm_fields := fs; vm_keyf := None; vm_name := nm |}; r_after := [] |} e p
  = (match assoc_verdict (List.concat (map (fun f => field_value f e p) fs)) (e_vmap e nm) with
     | Some v => Some v | None => None end, (e, p)).
Proof.
  intros h e p fs nm H.
  unfold rule_step. cbn [r_body body_step].
  unfold end_step. cbn [r_vmap r_outcome vm_keyf vm_name vm_fields].
  unfold vmap_loadable. cbn [vm_keyf vm_fields]. rewrite H.
  destruct (assoc_verdict (List.concat (map (fun f => field_value f e p) fs)) (e_vmap e nm)) as [v|];
    [reflexivity|].
  unfold terminal_step.
  cbn [has_effect_terminal r_nat r_tproxy r_fwd r_queue r_outcome r_verdict].
  reflexivity.
Qed.
