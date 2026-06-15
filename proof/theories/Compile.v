(** * Compile: the declarative DSL -> control-plane bytecode.

    This mirrors what [nft] does when lowering a rule to netlink expressions:
    each match becomes a load into register 1 followed by a [cmp] of register 1
    against the immediate, and the rule's verdict becomes a trailing
    [immediate].  Register 1 is reused across matches, exactly as nft does. *)

From Stdlib Require Import List.
From Nft Require Import Bytes Packet Verdict Syntax Bytecode.
Import ListNotations.

Definition compile_load (ld : loaddesc) (dst : reg) : instr :=
  match ld with
  | LMeta k        => IMetaLoad k dst
  | LPayload b o l => IPayloadLoad b o l dst
  end.

Definition compile_match (m : matchcond) : list instr :=
  match m with
  | MEq  f v => [compile_load (field_load f) 1; ICmp CEq 1 v]
  | MNeq f v => [compile_load (field_load f) 1; ICmp CNe 1 v]
  end.

Definition compile_rule (r : rule) : rule_prog :=
  flat_map compile_match (r_matches r) ++ [IImmediate (r_verdict r)].

Definition compile_chain (c : chain) : program :=
  map compile_rule (c_rules c).
