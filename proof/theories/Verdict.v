(** * Verdicts.

    A base chain ultimately maps a packet to a verdict:
      - [Accept] / [Drop] are *terminal*: they stop chain traversal;
      - [Continue] falls through to the next rule (it is the implicit verdict of
        a rule that only has match/non-verdict statements);
      - [Reject] / [Queue] are also terminal (they stop traversal here).  We
        model only their control-flow effect (stop), not their side effects
        (Reject also emits an ICMP/TCP-RST packet; Queue hands off to userspace
        with the given num/bypass/fanout) — those are out of the single-packet
        verdict model and are not differentially exercised by the corpus.

    [Jump]/[Goto]/[Return] (chain-to-chain control flow) are genuinely absent;
    adding them extends this type and the chain semantics without disturbing the
    register/cmp machinery the compiler proof is about. *)

From Stdlib Require Import PeanoNat String.

Inductive verdict : Type :=
| Accept
| Drop
| Continue
| Reject (typ code : nat)              (* reject with ICMP type/code *)
| Queue (lo hi : nat) (bypass fanout : bool)
| Jump (target : string)               (* call a user chain; resume here on return/fall-through *)
| Goto (target : string)               (* tail-call a user chain; do NOT resume here *)
| Return.                              (* pop back to the caller chain *)

(** A *terminal* verdict stops all chain traversal with that decision.  Continue
    falls through to the next rule; Jump/Goto/Return are control flow handled by
    the chain interpreter — none of these is terminal. *)
Definition terminal (v : verdict) : bool :=
  match v with
  | Accept | Drop | Reject _ _ | Queue _ _ _ _ => true
  | Continue | Jump _ | Goto _ | Return => false
  end.
