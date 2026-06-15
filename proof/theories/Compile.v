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
  | LCt k          => ICtLoad k dst
  | LExthdr ep h o l => IExthdrLoad ep h o l dst
  | LPayload b o l => IPayloadLoad b o l dst
  end.

Definition compile_transform (t : transform) : instr :=
  match t with
  | TBitAnd mask xor    => IBitwise 1 1 mask xor
  | TShift shl amt     => IBitShift 1 1 shl amt
  | TByteorder h sz len => IByteorder 1 1 h sz len
  end.

Fixpoint compile_transforms (ts : list transform) : list instr :=
  match ts with
  | []        => []
  | t :: ts'  => compile_transform t :: compile_transforms ts'
  end.

Definition compile_match (m : matchcond) : list instr :=
  match m with
  | MEq  f v => [compile_load (field_load f) 1; ICmp CEq 1 v]
  | MNeq f v => [compile_load (field_load f) 1; ICmp CNe 1 v]
  | MRange f neg lo hi =>
      [compile_load (field_load f) 1; IRange (if neg then CNe else CEq) 1 lo hi]
  | MMasked f neg mask xor v =>
      [compile_load (field_load f) 1; IBitwise 1 1 mask xor;
       ICmp (if neg then CNe else CEq) 1 v]
  | MSet f neg name elems =>
      [compile_load (field_load f) 1; ILookup 1 name neg elems]
  | MTransform f ts neg v =>
      compile_load (field_load f) 1 :: compile_transforms ts ++
      [ICmp (if neg then CNe else CEq) 1 v]
  | MLimit spec => [ILimit spec]
  end.

(** A [Continue] (fall-through) rule emits no verdict expression, exactly as
    [nft] does for a rule that only narrows; a terminal verdict emits an
    [immediate] into the verdict register. *)
Definition compile_stmt (s : stmt) : list instr :=
  match s with
  | SCounter p b => [ICounter p b]
  | SNotrack     => [INotrack]
  | SLog level   => [ILog level]
  end.

Definition verdict_tail (v : verdict) : list instr :=
  match v with
  | Continue        => []
  | Accept          => [IImmediate Accept]
  | Drop            => [IImmediate Drop]
  | Reject t c      => [IReject t c]
  | Queue lo hi b f => [IQueue lo hi b f]
  end.

Definition compile_rule (r : rule) : rule_prog :=
  flat_map compile_match (r_matches r) ++
  flat_map compile_stmt (r_stmts r) ++
  verdict_tail (r_verdict r).

Definition compile_chain (c : chain) : program :=
  map compile_rule (c_rules c).
