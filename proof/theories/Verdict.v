(** * Verdicts.

    A base chain ultimately maps a packet to a verdict.  We model the three
    verdicts needed for stateless filtering:
      - [Accept] / [Drop] are *terminal*: they stop chain traversal;
      - [Continue] falls through to the next rule (it is the implicit verdict of
        a rule that only has match/non-verdict statements).

    [Jump]/[Goto]/[Return]/[Reject]/[Queue] are deliberately omitted for now;
    they extend this type and the chain semantics without disturbing the
    register/cmp machinery that the compiler proof is really about. *)

Inductive verdict : Type :=
| Accept
| Drop
| Continue.

Definition terminal (v : verdict) : bool :=
  match v with
  | Accept | Drop => true
  | Continue      => false
  end.
