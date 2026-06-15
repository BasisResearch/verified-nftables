(** * Semantics: the meaning of both languages as packet -> verdict.

    Both the declarative DSL and the bytecode are given the *same* observable
    semantics — a function from a packet to the verdict the base chain produces —
    so "semantics preserving" is a literal equality of these functions. *)

From Stdlib Require Import List NArith Bool.
From Nft Require Import Bytes Packet Verdict Syntax Bytecode.
Import ListNotations.

(** ** Declarative semantics. *)

Definition apply_transform (t : transform) (d : data) : data :=
  match t with
  | TBitAnd mask xor    => data_bitops d mask xor
  | TShift shl amt     => data_shift shl amt d
  | TByteorder h sz len => data_byteorder h sz len d
  end.

Definition apply_transforms (ts : list transform) (d : data) : data :=
  fold_left (fun acc t => apply_transform t acc) ts d.

Definition eval_matchcond (m : matchcond) (p : packet) : bool :=
  match m with
  | MEq  f v => data_eqb (field_value f p) v
  | MNeq f v => negb (data_eqb (field_value f p) v)
  | MRange f neg lo hi =>
      eval_range (if neg then CNe else CEq) (field_value f p) lo hi
  | MMasked f neg mask xor v =>
      eval_cmp (if neg then CNe else CEq) (data_bitops (field_value f p) mask xor) v
  | MSet f neg _ elems =>
      xorb neg (data_mem (field_value f p) elems)
  | MTransform f ts neg v =>
      eval_cmp (if neg then CNe else CEq) (apply_transforms ts (field_value f p)) v
  | MLimit spec => pkt_limit p spec
  end.

(** A rule applies when all its match conditions hold (empty = matches all). *)
Definition rule_applies (r : rule) (p : packet) : bool :=
  forallb (fun m => eval_matchcond m p) (r_matches r).

(** Evaluate a rule list.  [None] means "fell through every rule"; [Some v]
    means a terminal verdict [v] was reached.  A [Continue] verdict on an
    applicable rule simply proceeds, exactly like a non-applicable rule. *)
Fixpoint eval_rules (rs : list rule) (p : packet) : option verdict :=
  match rs with
  | [] => None
  | r :: rest =>
      if rule_applies r p then
        match r_verdict r with
        | Continue => eval_rules rest p
        | v        => Some v
        end
      else eval_rules rest p
  end.

Definition eval_chain (c : chain) (p : packet) : verdict :=
  match eval_rules (c_rules c) p with
  | Some v => v
  | None   => c_policy c
  end.

(** ** Bytecode VM semantics. *)

(** Run one rule's program over a register file.  [None] means a [cmp] failed
    (the rule does not apply, like netfilter "breaking" out of the rule);
    [Some v] means an [immediate] set verdict [v]. *)
Fixpoint run_rule (rf : regfile) (is : rule_prog) (p : packet) : option verdict :=
  match is with
  | [] => None
  | IMetaLoad k dst :: rest =>
      run_rule (set_reg rf dst (pkt_meta p k)) rest p
  | ICtLoad k dst :: rest =>
      run_rule (set_reg rf dst (pkt_ct p k)) rest p
  | IExthdrLoad ep h o l dst :: rest =>
      run_rule (set_reg rf dst (pkt_eh p ep h o l)) rest p
  | IPayloadLoad b o l dst :: rest =>
      run_rule (set_reg rf dst (read_payload b o l p)) rest p
  | ICmp op src v :: rest =>
      if eval_cmp op (rf src) v then run_rule rf rest p else None
  | IRange op src lo hi :: rest =>
      if eval_range op (rf src) lo hi then run_rule rf rest p else None
  | IBitwise dst src mask xor :: rest =>
      run_rule (set_reg rf dst (data_bitops (rf src) mask xor)) rest p
  | IBitShift dst src shl amt :: rest =>
      run_rule (set_reg rf dst (data_shift shl amt (rf src))) rest p
  | IByteorder dst src h sz len :: rest =>
      run_rule (set_reg rf dst (data_byteorder h sz len (rf src))) rest p
  | ILookup src _ neg elems :: rest =>
      if xorb neg (data_mem (rf src) elems) then run_rule rf rest p else None
  | ILimit spec :: rest =>
      if pkt_limit p spec then run_rule rf rest p else None   (* over-limit breaks *)
  | ICounter _ _ :: rest => run_rule rf rest p   (* verdict-neutral *)
  | INotrack :: rest      => run_rule rf rest p
  | ILog _ :: rest        => run_rule rf rest p
  | IReject t c :: _ => Some (Reject t c)
  | IQueue lo hi b f :: _ => Some (Queue lo hi b f)
  | IImmediate v :: _ => Some v
  end.

(** Run a base chain's program: ordered per-rule programs, each from a fresh
    (empty) register file, stopping at the first terminal verdict. *)
Fixpoint run_program (prog : program) (p : packet) : option verdict :=
  match prog with
  | [] => None
  | rp :: rest =>
      match run_rule empty_rf rp p with
      | Some v => if terminal v then Some v else run_program rest p
      | None   => run_program rest p
      end
  end.

Definition run_chain (prog : program) (policy : verdict) (p : packet) : verdict :=
  match run_program prog p with
  | Some v => v
  | None   => policy
  end.
