(** * Shared symbolic-evaluation engine for the worked-ruleset proofs.

    [Example_Ruleset.v] (hand-translated AST) and [Ruleset_Verified.v]
    (parser-emitted AST) both symbolically evaluate [eval_table] one rule at a
    time.  The rewrite/cbn engine that drives that is identical between them; only
    the leading [unfold] of the module's own chain definitions differs.  This file
    factors out the common core so the two cannot drift:

      - [erj_nil] / [erj_cons]: one-step unfolding lemmas for the fuel-recursive
        chain interpreter [eval_rules_j], proven while it is still transparent;
      - [Global Opaque eval_rules_j]: keep it folded thereafter so [cbn] reduces
        only the *current* rule rather than the whole fuel-bounded traversal tree;
      - [Ltac eval_fw_core]: the shared rewrite/cbn loop.

    Each module then defines its own [eval_fw] as just its chain [unfold] followed
    by [eval_fw_core]. *)

From Stdlib Require Import List.
From Nft Require Import Bytes Verdict Packet Syntax Semantics.
Import ListNotations.

(** One-step unfolding lemmas for the fuel-recursive chain interpreter.  We keep
    [eval_rules_j] opaque during evaluation and step it with these, so [cbn] only
    ever reduces the *current* rule (rather than symbolically expanding the whole
    fuel-bounded traversal tree, which blows up). *)
Lemma erj_nil : forall n cs e p, eval_rules_j (S n) cs [] e p = None.
Proof. reflexivity. Qed.

Lemma erj_cons : forall n cs r rest e p,
  eval_rules_j (S n) cs (r :: rest) e p =
  (if andb (rule_loadable r e p) (rule_applies r e p)
   then match outcome r e p with
        | None => eval_rules_j n cs rest e p
        | Some Return => None
        | Some (Jump m) =>
            match chain_lookup cs m with
            | Some ch => match eval_rules_j n cs (c_rules ch) e p with
                         | Some v => Some v | None => eval_rules_j n cs rest e p end
            | None => eval_rules_j n cs rest e p
            end
        | Some (Goto m) =>
            match chain_lookup cs m with
            | Some ch => eval_rules_j n cs (c_rules ch) e p | None => None end
        | Some Continue => eval_rules_j n cs rest e p
        | Some v => Some v
        end
   else eval_rules_j n cs rest e p).
Proof. reflexivity. Qed.

(** Empty rule list returns [None] regardless of fuel (covers the [O] fuel case
    that [erj_nil] does not). *)
Lemma erj_empty : forall m cs e p, eval_rules_j m cs [] e p = None.
Proof. destruct m; reflexivity. Qed.

Global Opaque eval_rules_j.

(** The point-interval membership identity [data_in_iv key (k, k) = data_eqb k key]
    used by the router vmap classifications (to turn point-interval lookups into a
    cascade of byte-equality tests without concrete-byte case analysis on the key)
    now lives canonically as [Bytes.data_in_iv_point]; it is re-exported here via
    the [Bytes] import, so callers' [rewrite data_in_iv_point] is unchanged. *)

(** The shared engine: step one rule at a time, rewriting the per-packet field
    values from the hypotheses as each match is reached.  [field_value] /
    [eval_rules_j] are kept folded so the field hypotheses can rewrite
    [field_value _ e p] and the recursion does not explode.  Callers [unfold]
    their own [eval_table]/chain definitions first, then invoke this with the
    [e = ...] (concrete-env) hypothesis. *)
Ltac eval_fw_core Hpe :=
  try rewrite Hpe in * |- *;
  repeat first
    [ rewrite Hpe
    | rewrite erj_nil
    | rewrite erj_cons
    | match goal with H : field_value _ _ _ = _ |- _ => rewrite H end
    | match goal with H : read_payload_ok _ _ _ _ = _ |- _ => rewrite H end
    | progress unfold rule_loadable, rule_applies, end_loadable, tail_loadable,
        terminal_loadable, vmap_loadable, body_item_loadable, match_loadable,
        fields_loadable, field_loadable, load_ok, eval_matchcond, eval_matchcond_body
    | progress cbn -[eval_rules_j field_value read_payload_ok] ];
  reflexivity.
