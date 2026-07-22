(** * Optimize: verified rewrites on the declarative DSL.

    Four semantics-preserving optimizations (the kind a firewall-minimizer such as
    diekmann's Iptables_Semantics performs), whose state-fold correctness is proved
    in [Optimize_MutEnv.v]:

      1. [dedup_rule] — remove duplicate match conditions within a rule (a
         conjunction is idempotent), shrinking the emitted bytecode.

      2. [simplify_rule] — rewrite a singleton range [lo <= x <= lo] to an
         equality test (a [range] expression becomes a single [cmp]).

      3. [prune_noops] — delete rules that have no matches, no statements, and a
         [Continue] verdict (they never affect any verdict).

      4. [dce] — dead-rule elimination: once a rule matches every packet and is
         terminal (no match conditions, verdict Accept/Drop), all later rules are
         unreachable and are dropped.

    [optimize_chain] runs dedup+simplify on every rule, prunes no-ops, then DCE;
    the theorem [optimize_chain_correct] shows the packet->verdict function is
    unchanged. *)

From Stdlib Require Import List PeanoNat Bool String.
From Nft Require Import Bytes Packet Verdict Syntax Bytecode Semantics.
Import ListNotations.

(** ** Decidable equality for match conditions (needed by [nodup]). *)

Definition field_eq_dec (a b : field) : {a = b} + {a <> b}.
Proof.
  decide equality;
    repeat (apply Nat.eq_dec || apply Bool.bool_dec || apply string_dec || decide equality).
Defined.
Definition transform_eq_dec (a b : transform) : {a = b} + {a <> b}.
Proof.
  decide equality;
    (apply Nat.eq_dec || apply Bool.bool_dec || apply (list_eq_dec Nat.eq_dec)).
Defined.

Definition limit_spec_eq_dec (a b : limit_spec) : {a = b} + {a <> b}.
Proof. decide equality; (apply Nat.eq_dec || apply Bool.bool_dec). Defined.

Definition quota_spec_eq_dec (a b : quota_spec) : {a = b} + {a <> b}.
Proof. decide equality; apply Nat.eq_dec. Defined.

Definition connlimit_spec_eq_dec (a b : connlimit_spec) : {a = b} + {a <> b}.
Proof. decide equality; apply Nat.eq_dec. Defined.

Definition matchcond_eq_dec (a b : matchcond) : {a = b} + {a <> b}.
Proof.
  decide equality;
    try (apply list_eq_dec; apply Nat.eq_dec);
    try (apply list_eq_dec; apply list_eq_dec; apply Nat.eq_dec);
    try (apply list_eq_dec; apply transform_eq_dec);
    try (apply list_eq_dec; decide equality;
           (apply field_eq_dec || (apply list_eq_dec; apply transform_eq_dec)));
    try (apply list_eq_dec; apply field_eq_dec);
    try apply field_eq_dec;
    try apply Bool.bool_dec;
    try apply string_dec;
    try apply limit_spec_eq_dec;
    try apply quota_spec_eq_dec;
    try apply connlimit_spec_eq_dec;
    try (decide equality).
Defined.

(** ** Helpers on rule bodies. *)

Definition body_stmts (b : list body_item) : list stmt :=
  flat_map (fun it => match it with BStmt s => s :: nil | BMatch _ => nil end) b.

Lemma body_matches_app : forall a b,
  body_matches (a ++ b) = body_matches a ++ body_matches b.
Proof. intros. unfold body_matches. apply flat_map_app. Qed.

Lemma body_matches_map_BMatch : forall l, body_matches (map BMatch l) = l.
Proof.
  unfold body_matches. induction l as [| m l IH]; simpl;
    [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma body_matches_map_BStmt : forall l, body_matches (map BStmt l) = nil.
Proof.
  unfold body_matches. induction l as [| s l IH]; simpl;
    [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma body_stmts_app : forall a b,
  body_stmts (a ++ b) = body_stmts a ++ body_stmts b.
Proof. intros. unfold body_stmts. apply flat_map_app. Qed.

Lemma body_stmts_map_BStmt : forall l, body_stmts (map BStmt l) = l.
Proof.
  unfold body_stmts. induction l as [| s l IH]; simpl;
    [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma body_stmts_map_BMatch : forall l, body_stmts (map BMatch l) = nil.
Proof.
  unfold body_stmts. induction l as [| m l IH]; simpl;
    [reflexivity | rewrite IH; reflexivity].
Qed.

(** ** Optimization 1: dead-rule elimination. *)

Definition is_empty {A} (l : list A) : bool :=
  match l with [] => true | _ => false end.

(** A rule that matches everything and stops chain traversal: an EMPTY body (no
    match conditions and no statements — so nothing can break / NFT_BREAK on any
    packet, making the rule unconditionally fire), a terminal static verdict, and
    no verdict-map (whose result could be a fall-through). *)
Definition shadows (r : rule) : bool :=
  is_empty (r_body r) && terminal (r_verdict r) &&
  (match r_vmap r with None => true | Some _ => false end) &&
  (match r_nat r with None => true | Some _ => false end) &&
  (match r_tproxy r with None => true | Some _ => false end) &&
  (match r_fwd r with None => true | Some _ => false end) &&
  (match r_queue r with None => true | Some _ => false end).

Fixpoint dce (rs : list rule) : list rule :=
  match rs with
  | [] => []
  | r :: rest => if shadows r then [r] else r :: dce rest
  end.

(** ** Optimization 2: intra-rule match deduplication. *)

(** Whether a body contains a SYN-proxy statement.  Such a statement is
    verdict-bearing AND position-sensitive (it STOPS traversal, making later
    items unreachable), so the match-reordering dedup performs is NOT verdict-
    preserving across it — [dedup_rule] therefore leaves such a rule untouched. *)
Definition body_has_synproxy (body : list body_item) : bool :=
  existsb (fun it => match it with BStmt (SSynproxy _ _) => true | _ => false end) body.

(** Deduplicate the match conditions; the statements are kept (after the matches).
    The reordering is irrelevant to the verdict (matches commute, statements are
    verdict-neutral) and the optimizer's output is not corpus-checked — EXCEPT when
    a SYN-proxy is present, whose STOP short-circuits later matches, so we then keep
    the rule unchanged. *)
(** A `notrack` statement is also position-sensitive: it forces IP_CT_UNTRACKED for
    the rest of the rule, so a `ct state` MATCH after it reads the untracked bit
    while one before it does not.  Reordering matches across a notrack is therefore
    NOT verdict-preserving, so [dedup_rule] leaves a notrack-bearing rule untouched
    too (mirrors the synproxy guard). *)
(** EFFECT-SAFETY GUARD (in addition to the synproxy/notrack position guards):
    dedup reorders the body — all (deduplicated) matches first, then the
    statements — which preserves the fold's verdict (matches commute and are
    read-only on a mut-free rule) but NOT the EFFECT on a write-bearing rule: a
    mutating statement moved past a match changes what the match reads in the
    state-threading fold ([body_step]), and [nodup] dropping a duplicate
    `limit` halves its bucket consumption.  So dedup now fires ONLY on
    [rule_mutfree] rules (no mutating statement, no consuming match, no NAT
    terminal), where the fold is state-invariant ([rule_step_state_mutfree]) —
    the per-rule verdict certificate is [fst_rule_step_dedup] and the
    effect-level pass lemma is [Optimize_MutEnv.eval_rules_mut_st_map_dedup]. *)
Definition dedup_rule (r : rule) : rule :=
  if body_has_synproxy (r_body r) || body_has_notrack (r_body r)
     || negb (rule_mutfree r) then r else
  {| r_body := map BMatch (nodup matchcond_eq_dec (body_matches (r_body r)))
               ++ map BStmt (body_stmts (r_body r));
     r_outcome := r_outcome r; r_after := r_after r |}.

(** With no synproxy in the body, [body_synproxy_stops] is [false]. *)
Lemma body_has_synproxy_false_stops : forall body p,
  body_has_synproxy body = false -> body_synproxy_stops body p = false.
Proof.
  induction body as [| it body IH]; intro p; [reflexivity|].
  unfold body_has_synproxy, body_synproxy_stops in *. cbn [existsb].
  destruct it as [m | s]; [cbn [orb]; apply IH|].
  destruct s; cbn; try (apply IH); [].
  (* SSynproxy: head true contradicts the hypothesis *)
  intro H; discriminate H.
Qed.

Lemma forallb_nodup :
  forall (A : Type) (dec : forall x y : A, {x = y} + {x <> y}) f (l : list A),
    forallb f (nodup dec l) = forallb f l.
Proof.
  intros A dec f l. destruct (forallb f l) eqn:E.
  - rewrite forallb_forall in E. apply forallb_forall.
    intros x Hx. apply E. apply nodup_In in Hx. exact Hx.
  - destruct (forallb f (nodup dec l)) eqn:E2; [| reflexivity].
    rewrite forallb_forall in E2.
    assert (forallb f l = true) as Hbad.
    { apply forallb_forall. intros x Hx. apply E2. apply nodup_In. exact Hx. }
    congruence.
Qed.

(** [existsb] of the synproxy-stop predicate over a list of [BMatch] is [false]. *)
Lemma existsb_synstop_map_BMatch : forall p ms,
  existsb (fun it => match it with BStmt (SSynproxy _ _) => synproxy_stops p | _ => false end)
    (map BMatch ms) = false.
Proof. intros p ms. induction ms as [| m ms IH]; [reflexivity|]. cbn [map existsb]. exact IH. Qed.

(** [existsb] of the synproxy-stop predicate over [map BStmt (body_stmts body)]
    is [false] when the body has no synproxy. *)
Lemma existsb_synstop_map_BStmt : forall p body,
  body_has_synproxy body = false ->
  existsb (fun it => match it with BStmt (SSynproxy _ _) => synproxy_stops p | _ => false end)
    (map BStmt (body_stmts body)) = false.
Proof.
  intros p body. unfold body_has_synproxy, body_stmts.
  induction body as [| it b IH]; [reflexivity|].
  cbn [existsb flat_map]. destruct it as [m | s].
  - cbn [orb]. exact IH.
  - cbn [map existsb]. destruct s; cbn [orb]; try exact IH; intro H; discriminate H.
Qed.

(** The dedup body (matches-then-statements) has no stopping synproxy exactly when
    the original body has no synproxy. *)
Lemma dedup_body_no_synproxy_stops : forall body p,
  body_has_synproxy body = false ->
  body_synproxy_stops (map BMatch (nodup matchcond_eq_dec (body_matches body))
                       ++ map BStmt (body_stmts body)) p = false.
Proof.
  intros body p Hsp. unfold body_synproxy_stops. rewrite existsb_app.
  rewrite existsb_synstop_map_BMatch, Bool.orb_false_l.
  apply existsb_synstop_map_BStmt; exact Hsp.
Qed.

(** [body_stmts] of a notrack-free body has no notrack, and a [map BMatch] list
    never does, so the dedup body (matches ++ stmts) is notrack-free too. *)
Lemma body_has_notrack_map_BMatch : forall ms,
  body_has_notrack (map BMatch ms) = false.
Proof. intros ms. induction ms as [| m ms IH]; [reflexivity|]. cbn [map]. exact IH. Qed.

Lemma body_has_notrack_map_BStmt_stmts : forall body,
  body_has_notrack body = false ->
  body_has_notrack (map BStmt (body_stmts body)) = false.
Proof.
  intros body. unfold body_has_notrack, body_stmts.
  induction body as [| it b IH]; [reflexivity|].
  cbn [existsb flat_map]. destruct it as [m | s].
  - cbn [orb]. exact IH.
  - cbn [map existsb]. destruct s; cbn [orb]; try exact IH; intro H; discriminate H.
Qed.

Lemma dedup_body_no_notrack : forall body,
  body_has_notrack body = false ->
  body_has_notrack (map BMatch (nodup matchcond_eq_dec (body_matches body))
                    ++ map BStmt (body_stmts body)) = false.
Proof.
  intros body Hnt. unfold body_has_notrack. rewrite existsb_app.
  fold (body_has_notrack (map BMatch (nodup matchcond_eq_dec (body_matches body)))).
  fold (body_has_notrack (map BStmt (body_stmts body))).
  rewrite body_has_notrack_map_BMatch, Bool.orb_false_l.
  apply body_has_notrack_map_BStmt_stmts; exact Hnt.
Qed.

(** The completion flag of a loadability-guarded body head. *)
Lemma bres_done_if : forall (c : bool) b e p,
  (match (if c then b else BRbreak e p) with BRdone _ _ => true | _ => false end)
  = c && match b with BRdone _ _ => true | _ => false end.
Proof. intros [] b e p; reflexivity. Qed.

(** On a mut-free body with no stopping synproxy and no notrack, the body fold
    COMPLETES ([BRdone]) exactly when every item loads and every match passes —
    read directly off [body_step], with no write-free projection function.  This
    is the fold-native content the match-reordering dedup preserves. *)
Lemma body_step_done_class : forall body e p,
  body_synproxy_stops body p = false ->
  body_has_notrack body = false ->
  forallb body_item_mutfree body = true ->
  (match body_step body e p with BRdone _ _ => true | _ => false end)
  = forallb (fun it => body_item_loadable it p) body
    && forallb (fun m => eval_matchcond m e p) (body_matches body).
Proof.
  induction body as [| it body IH]; intros e p Hsp Hnt Hmf; [reflexivity|].
  cbn [forallb] in Hmf. apply Bool.andb_true_iff in Hmf. destruct Hmf as [Hit Hmf].
  assert (Hspc : body_synproxy_stops (it :: body) p =
            (match it with BStmt (SSynproxy _ _) => synproxy_stops p | _ => false end)
            || body_synproxy_stops body p) by reflexivity.
  assert (Hntc : body_has_notrack (it :: body) =
            (match it with BStmt SNotrack => true | _ => false end)
            || body_has_notrack body) by reflexivity.
  rewrite Hspc in Hsp. rewrite Hntc in Hnt.
  (* split the load-forallb head off, tail folded *)
  assert (HLcons : forallb (fun it0 => body_item_loadable it0 p) (it :: body)
                 = body_item_loadable it p
                   && forallb (fun it0 => body_item_loadable it0 p) body) by reflexivity.
  rewrite HLcons.
  destruct it as [m | s].
  - cbn [orb] in Hsp, Hnt. cbn [body_item_mutfree] in Hit.
    assert (HMcons : body_matches (BMatch m :: body) = m :: body_matches body) by reflexivity.
    rewrite HMcons. cbn [forallb body_item_loadable].
    cbn [body_step]. rewrite (match_consume_free_id m e p Hit).
    rewrite bres_done_if, (IH e p Hsp Hnt Hmf).
    assert (Heq : eval_matchcond m e p
                  = match_loadable m p && eval_matchcond_body m e p) by reflexivity.
    rewrite Heq.
    destruct (match_loadable m p), (eval_matchcond_body m e p),
      (forallb (fun it0 => body_item_loadable it0 p) body),
      (forallb (fun m0 => eval_matchcond m0 e p) (body_matches body)); reflexivity.
  - assert (HMcons : body_matches (BStmt s :: body) = body_matches body) by reflexivity.
    rewrite HMcons.
    destruct s; cbn [body_item_mutfree is_mut_stmt negb] in Hit; try discriminate Hit;
      cbn [orb] in Hsp, Hnt; try discriminate Hnt;
      cbn [body_step body_item_loadable].
    all: try (rewrite bres_done_if, (IH e p Hsp Hnt Hmf), Bool.andb_assoc; reflexivity).
    (* SSynproxy: [Hsp] forces [synproxy_stops p = false] so the fold continues *)
    apply Bool.orb_false_iff in Hsp. destruct Hsp as [Hstop Hsp].
    cbn [body_item_loadable stmt_loadable].
    rewrite Hstop, bres_done_if, (IH e p Hsp Hnt Hmf), Bool.andb_assoc.
    reflexivity.
Qed.

(** [body_item_loadable] of a body splits into the matches' and statements'
    loadability, so dedup/reorder of the matches preserves it. *)
Lemma body_loadable_split : forall body p,
  forallb (fun it => body_item_loadable it p) body
  = forallb (fun m => match_loadable m p) (body_matches body)
    && forallb (fun s => stmt_loadable s p) (body_stmts body).
Proof.
  induction body as [| it body IH]; intros p; [reflexivity|].
  assert (Hbm : forall x l, body_matches (x :: l) =
            match x with BMatch m => m :: body_matches l | BStmt _ => body_matches l end)
    by (intros [m'|s'] l; reflexivity).
  assert (Hbs : forall x l, body_stmts (x :: l) =
            match x with BStmt s => s :: body_stmts l | BMatch _ => body_stmts l end)
    by (intros [m'|s'] l; reflexivity).
  destruct it as [m | s]; cbn [forallb body_item_loadable]; rewrite Hbm, Hbs;
    cbn [forallb]; rewrite IH;
    generalize (forallb (fun m0 => match_loadable m0 p) (body_matches body)) as bM;
    generalize (forallb (fun s0 => stmt_loadable s0 p) (body_stmts body)) as bS; intros bS bM.
  - destruct (match_loadable m p), bM, bS; reflexivity.
  - destruct (stmt_loadable s p), bM, bS; reflexivity.
Qed.

Lemma end_loadable_dedup : forall r e p, end_loadable (dedup_rule r) e p = end_loadable r e p.
Proof.
  intros r e p. unfold dedup_rule.
  destruct (body_has_synproxy (r_body r)); [reflexivity|].
  destruct (body_has_notrack (r_body r)); [reflexivity|].
  destruct (rule_mutfree r); [| reflexivity]. cbn [orb negb].
  unfold end_loadable, tail_loadable, terminal_loadable, vmap_loadable; reflexivity.
Qed.

(** The dedup rule's body is notrack-free when the original is (and not bailed). *)
Lemma dedup_body_no_notrack_rule : forall r,
  body_has_synproxy (r_body r) = false ->
  body_has_notrack (r_body r) = false ->
  body_has_notrack (r_body (dedup_rule r)) = false.
Proof.
  intros r Hsp Hnt. unfold dedup_rule. rewrite Hsp, Hnt.
  destruct (rule_mutfree r); cbn [orb negb r_body];
    [ apply dedup_body_no_notrack; exact Hnt | exact Hnt ].
Qed.

Lemma rule_loadable_dedup : forall r e p, rule_loadable (dedup_rule r) e p = rule_loadable r e p.
Proof.
  intros r e p. destruct (body_has_synproxy (r_body r)) eqn:Hsp.
  - (* dedup_rule = r *) unfold dedup_rule; rewrite Hsp; reflexivity.
  - destruct (body_has_notrack (r_body r)) eqn:Hnt.
    + (* dedup_rule = r *) unfold dedup_rule; rewrite Hsp, Hnt; reflexivity.
    + destruct (rule_mutfree r) eqn:Hmf;
        [| unfold dedup_rule; rewrite Hsp, Hnt, Hmf; reflexivity].
      unfold rule_loadable.
    (* both bodies are notrack-free, so [body_thread] collapses to [p] on each side *)
    assert (Htd : body_thread (r_body (dedup_rule r)) p = p)
      by (unfold body_thread; rewrite (dedup_body_no_notrack_rule r Hsp Hnt); reflexivity).
    assert (Htr : body_thread (r_body r) p = p)
      by (unfold body_thread; rewrite Hnt; reflexivity).
    rewrite Htd, Htr, end_loadable_dedup.
    (* both [body_synproxy_stops] sides are [false], so the [if] reduces to [end_loadable] *)
    assert (Hd : body_synproxy_stops (r_body (dedup_rule r)) p = false)
      by (unfold dedup_rule; rewrite Hsp, Hnt, Hmf; cbn [orb negb r_body];
          apply dedup_body_no_synproxy_stops; exact Hsp).
    rewrite Hd, (body_has_synproxy_false_stops _ p Hsp).
    f_equal.
    rewrite (body_loadable_walk_no_synproxy (r_body (dedup_rule r)) p Hd).
    rewrite (body_loadable_walk_no_synproxy (r_body r) p
               (body_has_synproxy_false_stops _ p Hsp)).
    unfold dedup_rule; rewrite Hsp, Hnt, Hmf; cbn [orb negb r_body].
    rewrite body_loadable_split.
    rewrite body_matches_app, body_matches_map_BMatch, body_matches_map_BStmt, app_nil_r.
    rewrite body_stmts_app, body_stmts_map_BMatch, body_stmts_map_BStmt. cbn [app].
    rewrite (forallb_nodup _ matchcond_eq_dec).
    symmetry. apply body_loadable_split.
Qed.

(** ** Optimization 3: singleton-range simplification (now disabled).

    A singleton range [lo <= x <= lo] would be an equality test — but since
    equality ([MEq]/[eval_cmp CEq]) is now a *prefix* match (length = the value's
    width, faithful to wildcard interface names), rewriting a full-width singleton
    range to an [MEq] is no longer semantics-preserving (a longer field value
    sharing the prefix would match the [MEq] but not the range).  So this pass is
    the identity; the verdict-preservation guarantee is unaffected, only a minor
    bytecode-shrinking normalisation is foregone. *)
Definition simplify_match (m : matchcond) : matchcond := m.

Lemma simplify_match_correct : forall m e p,
  eval_matchcond (simplify_match m) e p = eval_matchcond m e p.
Proof. reflexivity. Qed.

Definition simplify_item (it : body_item) : body_item :=
  match it with BMatch m => BMatch (simplify_match m) | BStmt s => BStmt s end.

Definition simplify_rule (r : rule) : rule :=
  {| r_body := map simplify_item (r_body r);
     r_outcome := r_outcome r; r_after := r_after r |}.

Lemma body_matches_simplify : forall b,
  body_matches (map simplify_item b) = map simplify_match (body_matches b).
Proof.
  unfold body_matches. induction b as [| it b IH]; [reflexivity |].
  destruct it as [m | s]; simpl; rewrite IH; reflexivity.
Qed.

(** [simplify_match]/[simplify_item] are the identity (the pass is disabled), so a
    simplified body equals the original — hence all the wrappers are trivial. *)
Lemma simplify_item_id : forall it, simplify_item it = it.
Proof. intros [m | s]; reflexivity. Qed.
Lemma map_simplify_item_id : forall b, map simplify_item b = b.
Proof. induction b as [| it b IH]; [reflexivity|]. cbn [map]. rewrite simplify_item_id, IH. reflexivity. Qed.

(** ** Optimization 4: no-op rule removal.

    A rule with no matches, no statements, a [Continue] verdict, and no
    map/nat/tproxy outcome contributes nothing to any packet's verdict (it is
    applied to every packet but always falls through), so it can be deleted
    outright.  Unlike [dce] (which drops rules *after* an unconditional terminal),
    this removes the no-op rule itself — useful for cleaning up after other
    rewrites.  Requiring the whole body empty (not just the matches) keeps a
    counter/log-only rule, whose side effect we must preserve. *)
Definition is_noop (r : rule) : bool :=
  is_empty (r_body r) && is_empty (r_after r) &&
  (match r_verdict r with Continue => true | _ => false end) &&
  (match r_vmap r with None => true | Some _ => false end) &&
  (match r_nat r with None => true | Some _ => false end) &&
  (match r_tproxy r with None => true | Some _ => false end) &&
  (match r_fwd r with None => true | Some _ => false end) &&
  (match r_queue r with None => true | Some _ => false end).

Definition prune_noops (rs : list rule) : list rule :=
  filter (fun r => negb (is_noop r)) rs.

(** ** The combined pass and its correctness. *)

Definition optimize_chain (c : chain) : chain :=
  {| c_policy := c_policy c;
     c_rules  := dce (prune_noops (map (fun r => simplify_rule (dedup_rule r)) (c_rules c))) |}.

