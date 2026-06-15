(** * Compile: the declarative DSL -> control-plane bytecode.

    This mirrors what [nft] does when lowering a rule to netlink expressions:
    each match becomes a load into register 1 followed by a [cmp] of register 1
    against the immediate, and the rule's verdict becomes a trailing
    [immediate].  Register 1 is reused across matches, exactly as nft does. *)

From Stdlib Require Import List PeanoNat.
From Nft Require Import Bytes Packet Verdict Syntax Bytecode.
Import ListNotations.

Definition compile_load (ld : loaddesc) (dst : reg) : instr :=
  match ld with
  | LMeta k        => IMetaLoad k dst
  | LCt k          => ICtLoad k dst
  | LRt k          => IRtLoad k dst
  | LSocket k      => ISocketLoad k dst
  | LNumgen spec   => INumgen spec dst
  | LOsf           => IOsf dst
  | LExthdr ep h o l pr => IExthdrLoad ep h o l pr dst
  | LFib sel res   => IFibLoad sel res dst
  | LCtDir key dir => ICtDirLoad key dir dst
  | LInner t h fl desc w => IInnerLoad t h fl desc w dst
  | LPayload b o l => IPayloadLoad b o l dst
  end.

Definition compile_transform (t : transform) : instr :=
  match t with
  | TBitAnd mask xor    => IBitwise 1 1 mask xor
  | TShift shl amt     => IBitShift 1 1 shl amt
  | TByteorder h sz len => IByteorder 1 1 h sz len
  | TJhash l s m o      => IJhash 1 1 l s m o
  end.

Fixpoint compile_transforms (ts : list transform) : list instr :=
  match ts with
  | []        => []
  | t :: ts'  => compile_transform t :: compile_transforms ts'
  end.

(** ** Register allocation for concatenated lookup keys.

    nftables loads each concatenated field into its own 4-byte-aligned register
    "slot": slot 0 is displayed as reg 1, slot s>0 as reg 8+s.  A field of [len]
    bytes occupies [ceil(len/4)] slots (>=1).  The lookup then reads the
    concatenation starting at reg 1.  We reproduce this allocation exactly so the
    emitted bytecode is byte-identical to nft. *)
(** Byte width of a meta value (only matters for slot allocation when >4, i.e.
    the interface-name keys; everything <=4 occupies one slot regardless). *)
Definition meta_width (k : meta_key) : nat :=
  match k with
  | MKiifname | MKoifname | MKbri_iifname | MKbri_oifname => 16
  | MKibrhwaddr => 6
  | _ => 4
  end.

Definition load_width (ld : loaddesc) : nat :=
  match ld with
  | LMeta k            => meta_width k
  | LPayload _ _ len   => len
  | LExthdr _ _ _ len _ => len
  | LFib _ res         => match res with
                          | FRpresent => 1 | FRoifname => 16 | _ => 4
                          end
  | LInner _ _ _ _ w   => w
  | _                  => 4
  end.

Definition field_slots (f : field) : nat :=
  Nat.max 1 (Nat.div (load_width (field_load f) + 3) 4).

Definition reg_of_slot (s : nat) : reg := if Nat.eqb s 0 then 1 else 8 + s.

Fixpoint alloc_regs (slot : nat) (fields : list field) : list (field * reg) :=
  match fields with
  | []        => []
  | f :: rest => (f, reg_of_slot slot) :: alloc_regs (slot + field_slots f) rest
  end.

Definition load_fields (pairs : list (field * reg)) : list instr :=
  map (fun fr => compile_load (field_load (fst fr)) (snd fr)) pairs.

Definition compile_match (m : matchcond) : list instr :=
  match m with
  | MEq  f v => [compile_load (field_load f) 1; ICmp CEq 1 v]
  | MNeq f v => [compile_load (field_load f) 1; ICmp CNe 1 v]
  | MRange f neg lo hi =>
      [compile_load (field_load f) 1; IRange (if neg then CNe else CEq) 1 lo hi]
  | MMasked f neg mask xor v =>
      [compile_load (field_load f) 1; IBitwise 1 1 mask xor;
       ICmp (if neg then CNe else CEq) 1 v]
  | MCmp f op v => [compile_load (field_load f) 1; ICmp op 1 v]
  | MConcatSet fields neg name elems =>
      load_fields (alloc_regs 0 fields) ++
      [ILookup (map snd (alloc_regs 0 fields)) name neg elems]
  | MTransform f ts op v =>
      compile_load (field_load f) 1 :: compile_transforms ts ++
      [ICmp op 1 v]
  | MSetT f ts neg name elems =>
      compile_load (field_load f) 1 :: compile_transforms ts ++
      [ILookup [1] name neg elems]
  | MRangeT f ts neg lo hi =>
      compile_load (field_load f) 1 :: compile_transforms ts ++
      [IRange (if neg then CNe else CEq) 1 lo hi]
  | MLimit spec => [ILimit spec]
  | MQuota spec => [IQuota spec]
  end.

(** A [Continue] (fall-through) rule emits no verdict expression, exactly as
    [nft] does for a rule that only narrows; a terminal verdict emits an
    [immediate] into the verdict register. *)
(** Compile a value source into register 1 (immediate, or load + transforms). *)
Definition compile_vsrc (vs : vsrc) : list instr :=
  match vs with
  | VImm v      => [IImmediateData 1 v]
  | VField f ts => compile_load (field_load f) 1 :: compile_transforms ts
  | VMap fields name entries =>
      load_fields (alloc_regs 0 fields) ++
      [ILookupVal (map snd (alloc_regs 0 fields)) name 1 entries]
  end.

Definition compile_stmt (s : stmt) : list instr :=
  match s with
  | SCounter p b => [ICounter p b]
  | SNotrack     => [INotrack]
  | SLog level   => [ILog level]
  | SMangle vs b off len ct co cf =>
      compile_vsrc vs ++ [IPayloadWrite 1 b off len ct co cf]
  | SMetaSet k vs => compile_vsrc vs ++ [IMetaSet k 1]
  | SCtSet k vs   => compile_vsrc vs ++ [ICtSet k 1]
  end.

Definition verdict_tail (v : verdict) : list instr :=
  match v with
  | Continue        => []
  | Accept          => [IImmediate Accept]
  | Drop            => [IImmediate Drop]
  | Reject t c      => [IReject t c]
  | Queue lo hi b f => [IQueue lo hi b f]
  end.

(** A rule ends either with a verdict map lookup (loads of the key fields then a
    [lookup .. dreg 0]) or with the static verdict tail. *)
Definition compile_end (r : rule) : list instr :=
  match r_nat r with
  | Some n => map (fun rv => IImmediateData (fst rv) (snd rv)) (nat_imms n) ++
              [INat (nat_kind n) (nat_family n) (nat_amin n)
                    (nat_amax n) (nat_pmin n) (nat_pmax n) (nat_flags n)]
  | None =>
  match r_tproxy r with
  | Some t => map (fun rv => IImmediateData (fst rv) (snd rv)) (tp_imms t) ++
              [ITproxy (tp_family t) (tp_areg t) (tp_preg t)]
  | None =>
    match r_vmap r with
    | Some vm => load_fields (alloc_regs 0 (vm_fields vm)) ++
                 [IVmap (map snd (alloc_regs 0 (vm_fields vm))) (vm_name vm) (vm_entries vm)]
    | None    => verdict_tail (r_verdict r)
    end
  end
  end.

Definition compile_rule (r : rule) : rule_prog :=
  flat_map compile_match (r_matches r) ++
  flat_map compile_stmt (r_stmts r) ++
  compile_end r.

Definition compile_chain (c : chain) : program :=
  map compile_rule (c_rules c).
