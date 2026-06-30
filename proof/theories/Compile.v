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
  | LXfrm dir sp key => IXfrmLoad dir sp key dst
  | LTunnel key    => ITunnelLoad key dst
  | LSymhash m o   => ISymhash m o dst
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

(** A transform applied in place on an arbitrary register [r] (read [r], write
    [r]).  Used for concatenated lookup keys whose individual elements are
    transformed in their own slot register (not necessarily register 1). *)
Definition compile_transform_at (r : reg) (t : transform) : instr :=
  match t with
  | TBitAnd mask xor    => IBitwise r r mask xor
  | TShift shl amt      => IBitShift r r shl amt
  | TByteorder h sz len => IByteorder r r h sz len
  | TJhash l s m o      => IJhash r r l s m o
  end.

Definition compile_transforms_at (r : reg) (ts : list transform) : list instr :=
  map (compile_transform_at r) ts.

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

(** A 4-byte slot [s] occupies kernel sub-register [8 + s] (NFT_REG32_00 = 8),
    except slot 0 which is the first 16-byte register (reg 1).  These are the
    PHYSICAL register identities (monotonic in the slot), used for the
    non-clobbering concatenation proofs; the 16-byte-aligned DISPLAY naming
    (sub-reg 12/16/20 -> reg 2/3/4) is applied by the bytecode renderer. *)
Definition reg_of_slot (s : reg) : reg := if Nat.eqb s 0 then 1 else 8 + s.

Fixpoint alloc_regs (slot : nat) (fields : list field) : list (field * reg) :=
  match fields with
  | []        => []
  | f :: rest => (f, reg_of_slot slot) :: alloc_regs (slot + field_slots f) rest
  end.

Definition load_fields (pairs : list (field * reg)) : list instr :=
  map (fun fr => compile_load (field_load (fst fr)) (snd fr)) pairs.

(** Load a concatenation key whose elements may carry their own transform chain:
    each element [f] is loaded into its slot register [r] and then transformed in
    place by [ts] at [r], before moving on to the next slot. *)
Fixpoint load_fields_t (slot : nat) (elems : list (field * list transform)) : list instr :=
  match elems with
  | []            => []
  | (f, ts) :: rest =>
      let r := reg_of_slot slot in
      (compile_load (field_load f) r :: compile_transforms_at r ts)
        ++ load_fields_t (slot + field_slots f) rest
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
  | MCmp f op v => [compile_load (field_load f) 1; ICmp op 1 v]
  | MConcatSet fields neg name =>
      load_fields (alloc_regs 0 fields) ++
      [ILookup (map snd (alloc_regs 0 fields)) name neg]
  | MTransform f ts op v =>
      compile_load (field_load f) 1 :: compile_transforms ts ++
      [ICmp op 1 v]
  | MSetT f ts neg name =>
      compile_load (field_load f) 1 :: compile_transforms ts ++
      [ILookup [1] name neg]
  | MRangeT f ts neg lo hi =>
      compile_load (field_load f) 1 :: compile_transforms ts ++
      [IRange (if neg then CNe else CEq) 1 lo hi]
  | MLimit spec => [ILimit spec]
  | MQuota spec => [IQuota spec]
  | MConnlimit spec => [IConnlimit spec]
  | MConcatSetT elems neg name =>
      load_fields_t 0 elems ++
      [ILookup (map snd (alloc_regs 0 (map fst elems))) name neg]
  end.

(** A [Continue] (fall-through) rule emits no verdict expression, exactly as
    [nft] does for a rule that only narrows; a terminal verdict emits an
    [immediate] into the verdict register. *)
(** Compile a value source into register 1 (immediate, or load + transforms). *)
Definition compile_vsrc (vs : vsrc) : list instr :=
  match vs with
  | VImm v      => [IImmediateData 1 v]
  | VField f ts => compile_load (field_load f) 1 :: compile_transforms ts
  | VMap fields ts name =>
      load_fields (alloc_regs 0 fields) ++ compile_transforms ts ++
      [ILookupVal (map snd (alloc_regs 0 fields)) name 1]
  | VHash fields len seed modulus offset =>
      (* nft allocates the jhash output in reg 1 and the concatenated source from
         the next 128-bit register (slot 4); the hash reads it into reg 1 *)
      load_fields (alloc_regs 4 fields) ++
      [IJhash 1 (match map snd (alloc_regs 4 fields) with r :: _ => r | [] => 1 end)
              len seed modulus offset]
  | VOr srcs final =>
      match srcs with
      | []             => []
      | (f0, ts0) :: rest =>
          (compile_load (field_load f0) 1 :: compile_transforms_at 1 ts0) ++
          flat_map (fun e =>
            compile_load (field_load (fst e)) 2 :: compile_transforms_at 2 (snd e)
            ++ [IBitwiseOr 1 1 2]) rest ++
          compile_transforms_at 1 final
      end
  | VMapT elems name =>
      load_fields_t 0 elems ++
      [ILookupVal (map snd (alloc_regs 0 (map fst elems))) name 1]
  | VHashMap fields len seed modulus offset name =>
      load_fields (alloc_regs 4 fields) ++
      [IJhash 1 (match map snd (alloc_regs 4 fields) with r :: _ => r | [] => 1 end)
              len seed modulus offset] ++
      [ILookupVal [1] name 1]
  end.

(** dup register allocation: the address (if any) takes register 1; the device
    takes register 2 after an address, else register 1. *)
Definition dup_addr_present (addr : option data) : bool :=
  match addr with Some _ => true | None => false end.
Definition dup_dbase (addr : option data) : nat := if dup_addr_present addr then 2 else 1.
Definition dup_addrreg (addr : option data) : option nat :=
  if dup_addr_present addr then Some 1 else None.
Definition dup_devreg (addr dev : option data) : option nat :=
  match dev with Some _ => Some (dup_dbase addr) | None => None end.
Definition dup_imm_loads (addr dev : option data) : list (nat * data) :=
  (match addr with Some a => [(1, a)] | None => [] end)
  ++ (match dev with Some d => [(dup_dbase addr, d)] | None => [] end).
(** A [SDupSrc] immediate device lands in register 2 (after the reg-1 source). *)
Definition dupsrc_dev_loads (dev : option data) : list (nat * data) :=
  match dev with Some d => [(2, d)] | None => [] end.

(** dynset immediate-data layout: the data values occupy the registers after the
    key fields, each taking [data_slots] 4-byte slots. *)
Definition data_slots (v : data) : nat := Nat.max 1 (Nat.div (length v + 3) 4).
Fixpoint sum_field_slots (fs : list field) : nat :=
  match fs with [] => 0 | f :: rest => field_slots f + sum_field_slots rest end.
Fixpoint dynset_data_loads (slot : nat) (vals : list data) : list (nat * data) :=
  match vals with
  | [] => []
  | v :: rest => (reg_of_slot slot, v) :: dynset_data_loads (slot + data_slots v) rest
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
  | SCtSetDir key dir vs => compile_vsrc vs ++ [ICtSetDir key dir 1]
  | SObjref o n   => [IObjref o n]
  | SSynproxy m w => [ISynproxy m w]
  | SLast info    => [ILast info]
  | SDynset op name keyfs dataf =>
      (* keys then data, allocated contiguously: the data register follows the
         key registers exactly as nft places sreg_data after reg_key.  [keyregs]
         names only the KEY registers (the data register is [datareg]); [fdata] is
         [true] because the data here is a packet field (modelled). *)
      let pairs := alloc_regs 0 (keyfs ++ dataf) in
      load_fields pairs ++
      [IDynset op name (map snd (alloc_regs 0 keyfs))
         (match skipn (length keyfs) (map snd pairs) with
          | [] => None | r :: _ => Some r end)
         (match dataf with [] => false | _ => true end)]
  | SExthdrReset proto htype => [IExthdrReset proto htype]
  | SDup addr dev =>
      map (fun rv => IImmediateData (fst rv) (snd rv)) (dup_imm_loads addr dev)
      ++ [IDup (dup_devreg addr dev) (dup_addrreg addr)]
  | SObjrefMap keyfs name =>
      load_fields (alloc_regs 0 keyfs) ++
      [IObjrefMap (map snd (alloc_regs 0 keyfs)) name]
  | SDynsetImm op name keyfs data_vals =>
      load_fields (alloc_regs 0 keyfs) ++
      map (fun rv => IImmediateData (fst rv) (snd rv))
          (dynset_data_loads (sum_field_slots keyfs) data_vals) ++
      [IDynset op name (map snd (alloc_regs 0 keyfs))
         (Some (reg_of_slot (sum_field_slots keyfs))) false]
  | SExthdrWrite vs proto htype off len =>
      compile_vsrc vs ++ [IExthdrWrite proto htype off len 1]
  | SDupSrc src is_addr dev =>
      compile_vsrc src ++
      map (fun rv => IImmediateData (fst rv) (snd rv)) (dupsrc_dev_loads dev) ++
      [IDup (if is_addr then (match dev with Some _ => Some 2 | None => None end)
             else Some 1)
            (if is_addr then Some 1 else None)]
  end.

Definition verdict_tail (v : verdict) : list instr :=
  match v with
  | Continue        => []
  | Accept          => [IImmediate Accept]
  | Drop            => [IImmediate Drop]
  | Reject t c      => [IReject t c]
  | Queue lo hi b f => [IQueue lo hi b f]
  | Jump _ | Goto _ | Return => [IImmediate v]  (* jump/goto/return -> verdict-register immediate *)
  end.

(** The verdict-map prefix of a rule, if any: load the key, then [IVmap] (which
    on a miss falls through to the terminal below). *)
Definition compile_vmap (r : rule) : list instr :=
  match r_vmap r with
  | Some vm =>
      match vm_keyf vm with
      | Some (f, ts) =>
          compile_load (field_load f) 1 :: compile_transforms ts ++
          [IVmap [1] (vm_name vm)]
      | None =>
          load_fields (alloc_regs 0 (vm_fields vm)) ++
          [IVmap (map snd (alloc_regs 0 (vm_fields vm))) (vm_name vm)]
      end
  | None => []
  end.

(** The numeric NFPROTO the kernel uses for an address family qualifier (the
    register-free [fwd_family]/… string is lowered here). *)
Definition nfproto_of_family (s : String.string) : nat :=
  if String.eqb s nat_fam_ip6 then 10 else 2.

(** *** NAT register ALLOCATION (the compiler's job; the source [nat_spec] is
    register-free).  The primary address operand goes into register 1 (when there is
    one); a SECONDARY immediate lands in the next sequential register (reg 2/3),
    while a value taken from the operand's concat-MAP lands in slot 1 = register 9. *)
Definition nat_addr_present (n : nat_spec) : bool :=
  match nat_src n with Some _ => true | None =>
  match nat_map n with Some _ => true | None =>
  match nat_field n with Some _ => true | None =>
  match nat_addr_imm n with Some _ => true | None => false end end end end.

Definition optlen {A} (o : option A) : nat := match o with Some _ => 1 | None => 0 end.
(** The first register available for a SECONDARY operand: reg 2 after an address in
    reg 1, else reg 1 (a port-only NAT). *)
Definition nat_sec0 (n : nat_spec) : nat := if nat_addr_present n then 2 else 1.

(** [masq]/[redir] never translate an address: any operand (map/field/immediate)
    they carry is the PORT, loaded into register 1.  For these the operand reg is
    [proto_min], not [addr_min]. *)
Definition nat_portonly (n : nat_spec) : bool :=
  orb (String.eqb (nat_kind n) nat_masq_kind) (String.eqb (nat_kind n) nat_redir_kind).

Definition nat_amin_reg (n : nat_spec) : option nat :=
  if nat_portonly n then None
  else if nat_addr_present n then Some 1 else None.
Definition nat_amax_reg (n : nat_spec) : option nat :=
  match nat_extra n with
  | NXimm (Some _) _ _ => Some (nat_sec0 n)
  | NXmap_addr_max => Some 9
  | NXmap_full => Some (reg_of_slot 2)
  | _ => None end.
Definition nat_pmin_reg (n : nat_spec) : option nat :=
  match nat_extra n with
  | NXimm am (Some _) _ => Some (nat_sec0 n + optlen am)
  | NXmap_port => Some 9
  | NXmap_full => Some (reg_of_slot 1)
  | _ => if andb (nat_portonly n) (nat_addr_present n) then Some 1 else None end.
Definition nat_pmax_reg (n : nat_spec) : option nat :=
  match nat_extra n with
  | NXimm am pm (Some _) => Some (nat_sec0 n + optlen am + optlen pm)
  | NXmap_full => Some (reg_of_slot 3)
  | _ => None end.

(** The immediate loads for the secondary operands, in sequential registers. *)
Definition compile_nat_extra (n : nat_spec) : list instr :=
  match nat_extra n with
  | NXimm am pm px =>
      let r0 := nat_sec0 n in
      (match am with Some v => [IImmediateData r0 v] | None => [] end)
      ++ (match pm with Some v => [IImmediateData (r0 + optlen am) v] | None => [] end)
      ++ (match px with Some v => [IImmediateData (r0 + optlen am + optlen pm) v] | None => [] end)
  | _ => []
  end.

(** The primary address operand loads (into register 1). *)
Definition compile_nat_operand (n : nat_spec) : list instr :=
  match nat_src n with
  | Some vs => compile_vsrc vs
  | None =>
  match nat_map n with
  | Some (fields, ts, name) =>
      load_fields (alloc_regs 0 fields) ++ compile_transforms ts ++
      [ILookupValBr (map snd (alloc_regs 0 fields)) name 1]
  | None =>
  match nat_field n with
  | Some (f, ts) => compile_load (field_load f) 1 :: compile_transforms ts
  | None => match nat_addr_imm n with Some v => [IImmediateData 1 v] | None => [] end
  end end end.

(** tproxy register allocation: the address (if any) takes register 1; the port
    (immediate or symhash-map) takes register 2 after an address, else register 1. *)
Definition tp_addr_present (t : tproxy_spec) : bool :=
  match tp_addr t with Some _ => true | None => false end.
Definition tp_pbase (t : tproxy_spec) : nat := if tp_addr_present t then 2 else 1.
Definition tp_areg (t : tproxy_spec) : option nat :=
  if tp_addr_present t then Some 1 else None.
Definition tp_has_port (t : tproxy_spec) : bool :=
  match tp_portmap t with Some _ => true
  | None => match tp_port t with Some _ => true | None => false end end.
Definition tp_preg (t : tproxy_spec) : option nat :=
  if tp_has_port t then Some (tp_pbase t) else None.
(** The immediate operand loads (address in reg 1, an immediate port in [tp_pbase]). *)
Definition tp_imm_loads (t : tproxy_spec) : list (nat * data) :=
  (match tp_addr t with Some a => [(1, a)] | None => [] end)
  ++ (match tp_portmap t with
      | Some _ => []   (* port comes from the symhash map, not an immediate *)
      | None => match tp_port t with Some p => [(tp_pbase t, p)] | None => [] end
      end).

(** The terminal of a rule: a nat/tproxy/fwd/queue side effect, else the static
    verdict tail. *)
Definition compile_terminal (r : rule) : list instr :=
  match r_nat r with
  | Some n => (compile_nat_operand n ++ compile_nat_extra n) ++
              [INat (nat_kind n) (nat_family n) (nat_amin_reg n)
                    (nat_amax_reg n) (nat_pmin_reg n) (nat_pmax_reg n) (nat_flags n)]
  | None =>
  match r_tproxy r with
  | Some t => (match tp_portmap t with
               | Some (m, o, name) =>
                   map (fun rv => IImmediateData (fst rv) (snd rv)) (tp_imm_loads t)
                   ++ [ISymhash m o (tp_pbase t); ILookupVal [tp_pbase t] name (tp_pbase t)]
               | None => map (fun rv => IImmediateData (fst rv) (snd rv)) (tp_imm_loads t)
               end) ++
              [ITproxy (tp_family t) (tp_areg t) (tp_preg t)]
  | None =>
  match r_fwd r with
  | Some w => compile_vsrc (fwd_dev w)
              ++ (match fwd_addr w with Some a => [IImmediateData 2 a] | None => [] end)
              ++ [IFwd (Some 1)
                    (match fwd_addr w with Some _ => Some 2 | None => None end)
                    (match fwd_addr w with
                     | Some _ => Some (nfproto_of_family (fwd_family w)) | None => None end)]
  | None =>
  match r_queue r with
  | Some q => compile_vsrc (q_num q) ++
              [IQueueSreg 1 (q_bypass q) (q_fanout q)]
  | None => verdict_tail (r_verdict r)
  end
  end
  end
  end.

(** A rule ends with its verdict-map prefix (if any) followed by its terminal. *)
Definition compile_end (r : rule) : list instr :=
  compile_vmap r ++ compile_terminal r.

Definition compile_body_item (it : body_item) : list instr :=
  match it with
  | BMatch m => compile_match m
  | BStmt s  => compile_stmt s
  end.

Definition compile_rule (r : rule) : rule_prog :=
  flat_map compile_body_item (r_body r) ++
  compile_end r ++
  flat_map compile_stmt (r_after r).

Definition compile_chain (c : chain) : program :=
  map compile_rule (c_rules c).

(** Compile a chain environment (user-defined chains) name-by-name; the jump/goto
    targets in the bytecode are the same names, so lookups line up. *)
Definition compile_env (cs : list (String.string * chain)) : list (String.string * program) :=
  map (fun nc => (fst nc, compile_chain (snd nc))) cs.
