(** * RegsValid: the kernel register-file validator, mirrored over bytecode.

    W2 (register-file discipline).  The kernel admits a rule's expressions only
    after validating every register operand against the register file
    (net/netfilter/nf_tables_api.c):

      - [struct nft_regs] is a u32 array of NFT_REG32_NUM = 20 words
        (include/net/netfilter/nf_tables.h:109,119-124): 80 bytes total, the
        first 4 words aliasing the verdict, the remaining 16 words = 64 bytes
        being the general-purpose data registers NFT_REG32_00..NFT_REG32_15
        (aliased 4-at-a-time as the four 128-bit registers NFT_REG_1..NFT_REG_4).
      - [nft_parse_register] (nf_tables_api.c:11650) maps a netlink register
        NUMBER to its 32-bit word INDEX: NFT_REG_VERDICT..NFT_REG_4 (0..4) map
        to reg * NFT_REG_SIZE/NFT_REG32_SIZE = 4*reg; NFT_REG32_00..NFT_REG32_15
        (8..23, uapi nf_tables.h:30-45) map to reg + 4 - NFT_REG32_00 = reg - 4;
        anything else is -ERANGE.
      - [nft_validate_register_load] (nf_tables_api.c:11691): a LOAD of [len]
        bytes at word index [i] needs i >= NFT_REG_1*4 = 4 (never the verdict
        words), len >= 1, and i*NFT_REG32_SIZE + len <= sizeof(nft_regs.data)
        = 80.
      - [nft_validate_register_store] (nf_tables_api.c:5784): a STORE of a
        DATA value has exactly the same three bounds; only a VERDICT store may
        target word 0.
      - a [struct nft_data] VALUE (the immediate operand of cmp/bitwise/
        immediate/range) is at most NFT_REG_SIZE = 16 bytes ([nft_data_init]
        rejects longer values: nf_tables_api.c NFT_DATA_VALUE path), and never
        empty.

    This file states that validator as a boolean over [Bytecode.instr] —
    covering EVERY register operand of EVERY instruction — so that "every
    compiled program passes the kernel's register validator" is a checkable
    claim.  [Lower.lower_rule] admits a rule only if its compiled image
    satisfies [regs_valid] (fail-loud [LEregalloc], the frontend twin of nft's
    own evaluate-time register-allocation bound), which discharges the claim
    for every frontend-emitted program
    ([RegsValid_Proofs.lower_ruleset_default_regs_valid]) — BY CONSTRUCTION,
    no hypothesis.

    The per-instruction LENGTHS mirror what the kernel validates the operand
    with (each cited at its table).  Instructions whose operand length lives in
    a referenced SET OBJECT rather than in the expression (lookup/vmap/dynset/
    objref-map keys and map data registers: the kernel validates those against
    set->klen / set->dlen, nft_lookup.c:153,171, nft_dynset.c:227,238,
    nft_objref.c:175) are checked at word granularity ([data_reg_ok]): each
    named register must resolve to a general data word.  This loses nothing:
    every byte of such a key/data span is PUT THERE by a preceding load/
    immediate whose own store is validated at its full kernel width here, so a
    span that would overflow the file is already rejected at the instruction
    that writes it. *)

From Stdlib Require Import List Bool PeanoNat String.
From Nft Require Import Bytes Packet Verdict Syntax Bytecode.
Import ListNotations.

(* ================================================================== *)
(** ** The kernel constants (linux-6.18.33). *)

(** NFT_REG32_NUM u32 words in [struct nft_regs.data]
    (include/net/netfilter/nf_tables.h:109). *)
Definition nft_reg32_num : nat := 20.

(** sizeof_field(struct nft_regs, data) = 20 * NFT_REG32_SIZE bytes — the bound
    of nft_validate_register_load/store (nf_tables_api.c:11697,5800ff). *)
Definition nft_regfile_bytes : nat := 4 * nft_reg32_num.

(** A [struct nft_data] value is at most NFT_REG_SIZE = 16 bytes
    (uapi nf_tables.h:49; nft_data_init's NFT_DATA_VALUE path). *)
Definition nft_data_value_max : nat := 16.

(** [nft_parse_register] (nf_tables_api.c:11650): netlink register number ->
    32-bit word index.  0..4 are NFT_REG_VERDICT and the 128-bit NFT_REG_1..4
    (index 4*reg); 8..23 are NFT_REG32_00..NFT_REG32_15 (index reg - 4);
    5..7 and >= 24 are -ERANGE.  The bytecode carries netlink numbers
    ([Compile.reg_of_slot]: slot 0 -> reg 1, slot s > 0 -> reg 8+s). *)
Definition nft_reg_index (r : reg) : option nat :=
  if Nat.leb r 4 then Some (4 * r)
  else if Nat.leb 8 r && Nat.leb r 23 then Some (r - 4)
  else None.

(** [nft_validate_register_load] (nf_tables_api.c:11691): word index at least
    NFT_REG_1 * NFT_REG_SIZE/NFT_REG32_SIZE = 4, length nonzero, and
    index*4 + len within the 80-byte file. *)
Definition reg_load_ok (r : reg) (len : nat) : bool :=
  match nft_reg_index r with
  | Some i => Nat.leb 4 i && Nat.leb 1 len
              && Nat.leb (4 * i + len) nft_regfile_bytes
  | None => false
  end.

(** [nft_validate_register_store]'s DATA branch (nf_tables_api.c:5784): the
    same three bounds (a data store may not target the verdict words).  The
    verdict branch (NFT_REG_VERDICT + NFT_DATA_VERDICT) has no byte bounds;
    the only verdict-register writers in this bytecode are [IImmediate] and
    [IVmap]'s dreg-0, which carry verdicts structurally. *)
Definition reg_store_ok (r : reg) (len : nat) : bool := reg_load_ok r len.

(** A register whose transfer LENGTH is owned by a referenced set object
    (set->klen / set->dlen): the expression-level residue of the kernel check
    is that the register resolves to a general data word at all.  (The bytes of
    the span are store-validated at full width by the instructions that write
    them — see the header note.) *)
Definition data_reg_ok (r : reg) : bool := reg_load_ok r 1.

(** A [struct nft_data] immediate value: 1..16 bytes (nft_data_init). *)
Definition imm_value_ok (v : data) : bool :=
  Nat.leb 1 (List.length v) && Nat.leb (List.length v) nft_data_value_max.

Definition opt_reg_ok (chk : reg -> bool) (o : option reg) : bool :=
  match o with Some r => chk r | None => true end.

(* ================================================================== *)
(** ** Per-key kernel widths not already pinned by the [Syntax] tables.
    ([meta_width]/[ct_width]/[rt_width]/[socket_width]/[osf_width]/
    [numgen_width]/[symhash_width] are the W1 tables, each kernel-cited at its
    definition; the loads below reuse them so there is ONE width table per
    oracle.) *)

(** fib result store width, nft_fib.c:93-105 (nft_fib_init):
    NFT_FIB_RESULT_OIF -> sizeof(int) = 4, NFT_FIB_RESULT_OIFNAME ->
    IFNAMSIZ = 16, NFT_FIB_RESULT_ADDRTYPE -> sizeof(u32) = 4.  A presence
    check (`fib ... check`) is result OIF with the NFTA_FIB_F_PRESENT flag —
    validated at the same sizeof(int) = 4. *)
Definition fib_store_width (res : fib_result) : nat :=
  match res with
  | FRoif => 4
  | FRoifname => 16
  | FRtype => 4
  | FRpresent => 4
  end.

(** Directional ct tuple-column widths, nft_ct.c:445-499 (nft_ct_get_init;
    every one of these keys REQUIRES NFTA_CT_DIRECTION): src/dst are the
    full nf_conntrack_tuple u3 union (16 bytes — the ip4 sub-case is 4, we
    pin the union bound the inet/ip6 families validate); src_ip/dst_ip 4;
    src_ip6/dst_ip6 16; protocol 1 (u8, protonum); proto_src/proto_dst 2
    (u.all, u16); bytes/packets/avgpkt 8 (u64, nft_ct.c:483-487); zone 2
    (u16, nft_ct.c:489-492).  The key strings are the netlink-debug names
    the corpus and renderer share (extracted/codec.ml).  Unknown key -> width
    0 -> invalid (fail-loud, mirroring nft_ct_get_init's -EOPNOTSUPP). *)
Definition ctdir_width (key : string) : nat :=
  if String.eqb key "src"%string then 16
  else if String.eqb key "dst"%string then 16
  else if String.eqb key "src_ip"%string then 4
  else if String.eqb key "dst_ip"%string then 4
  else if String.eqb key "src_ip6"%string then 16
  else if String.eqb key "dst_ip6"%string then 16
  else if String.eqb key "protocol"%string then 1
  else if String.eqb key "proto_src"%string then 2
  else if String.eqb key "proto_dst"%string then 2
  else if String.eqb key "bytes"%string then 8
  else if String.eqb key "packets"%string then 8
  else if String.eqb key "avgpkt"%string then 8
  else if String.eqb key "zone"%string then 2
  else 0.

(** Directional ct SET widths, nft_ct.c:568-616 (nft_ct_set_init): the only
    settable key that ACCEPTS a direction is zone (u16 = 2; mark/labels/
    eventmask/secmark reject NFTA_CT_DIRECTION with -EINVAL).  Unknown/
    non-directional key -> 0 -> invalid. *)
Definition ctsetdir_width (key : string) : nat :=
  if String.eqb key "zone"%string then 2 else 0.

(** xfrm key store widths, nft_xfrm.c:56-67 (nft_xfrm_get_init): reqid/spi 4
    (u32), daddr4/saddr4 4 (in_addr), daddr6/saddr6 16 (in6_addr). *)
Definition xfrm_width (key : string) : nat :=
  if String.eqb key "reqid"%string then 4
  else if String.eqb key "spi"%string then 4
  else if String.eqb key "daddr4"%string then 4
  else if String.eqb key "saddr4"%string then 4
  else if String.eqb key "daddr6"%string then 16
  else if String.eqb key "saddr6"%string then 16
  else 0.

(** tunnel key store widths, nft_tunnel.c:87-92 (nft_tunnel_get_init):
    path 1 (u8 presence), id 4 (u32). *)
Definition tunnel_width (key : string) : nat :=
  if String.eqb key "id"%string then 4
  else if String.eqb key "path"%string then 1
  else 0.

(** tproxy address length, nft_tproxy.c:226-256 (nft_tproxy_init): family ip
    -> 4 (union nf_inet_addr.in), ip6 -> 16 (.in6); an address register with
    family NFPROTO_UNSPEC is -EINVAL (nft_tproxy.c:222-224), so any other
    family string admits NO address register. *)
Definition tproxy_alen (family : string) : option nat :=
  if String.eqb family "ip"%string then Some 4
  else if String.eqb family "ip6"%string then Some 16
  else None.

(** fwd address length by NFPROTO, nft_fwd_netdev.c:178-196 (nft_fwd_neigh_init):
    NFPROTO_IPV4 (2) -> 4, NFPROTO_IPV6 (10) -> 16, anything else
    -EOPNOTSUPP. *)
Definition fwd_alen (nfproto : nat) : option nat :=
  if Nat.eqb nfproto 2 then Some 4
  else if Nat.eqb nfproto 10 then Some 16
  else None.

(** NAT address length by the wire family, nft_nat.c:201-208 (nft_nat_init):
    NFPROTO_IPV4 -> sizeof(nf_nat_range.min_addr.ip) = 4, NFPROTO_IPV6 -> 16;
    any other family is -EAFNOSUPPORT, so an [NFinet] (runtime-dispatched)
    NAT admits NO address register — masquerade/redirect, the [NFinet]
    carriers, have no address operands at all (nft_masq.c/nft_redir.c). *)
Definition nat_alen (family : nat_af) : option nat :=
  match family with
  | NFip4 => Some 4
  | NFip6 => Some 16
  | NFinet => None
  end.

Definition addr_reg_ok (alen : option nat) (o : option reg) : bool :=
  match o with
  | None => true
  | Some r => match alen with Some al => reg_load_ok r al | None => false end
  end.

(* ================================================================== *)
(** ** The validator, one arm per [Bytecode.instr] constructor (NO catch-all:
    a new instruction must state its register discipline here or the build
    breaks).  Each length names the kernel init that validates it. *)

Definition instr_regs_ok (i : instr) : bool :=
  match i with
  (* dreg stores at the W1 kernel width tables:
     nft_meta.c:534 (len: nft_meta_get_init per-key table = [meta_width]),
     nft_ct.c:517 (nft_ct_get_init = [ct_width] for the direction-free keys),
     nft_rt.c:144 ([rt_width]), nft_socket.c:233 ([socket_width]). *)
  | IMetaLoad k dst   => reg_store_ok dst (meta_width k)
  | ICtLoad k dst     => reg_store_ok dst (ct_width k)
  | IRtLoad k dst     => reg_store_ok dst (rt_width k)
  | ISocketLoad k dst => reg_store_ok dst (socket_width k)
  (* nft_numgen.c:75,168: sizeof(u32) = [numgen_width]. *)
  | INumgen _ dst     => reg_store_ok dst numgen_width
  (* nft_osf.c:90: NFT_OSF_MAXGENRELEN = 16 = [osf_width]. *)
  | IOsf dst          => reg_store_ok dst osf_width
  (* nft_exthdr.c:541: dreg store at priv->len (the len attr; a presence
     check carries len = 1 on the wire, already in [len] here). *)
  | IExthdrLoad _ _ _ len _ dst => reg_store_ok dst len
  (* nft_tproxy.c:257-265: addr reg loads alen (family-determined; UNSPEC
     forbids an addr reg), port reg loads sizeof(u16) = 2. *)
  | ITproxy family areg preg =>
      addr_reg_ok (tproxy_alen family) areg
      && opt_reg_ok (fun r => reg_load_ok r 2) preg
  (* nft_fwd_netdev.c:55,191: dev reg loads sizeof(int) = 4; :196 addr reg
     loads the NFPROTO-determined length. *)
  | IFwd devreg addrreg nfproto =>
      opt_reg_ok (fun r => reg_load_ok r 4) devreg
      && (match addrreg with
          | None => true
          | Some r => match nfproto with
                      | Some np => addr_reg_ok (fwd_alen np) (Some r)
                      | None => false
                      end
          end)
  (* nft_queue.c:138: queue-number sreg loads sizeof(u32) = 4. *)
  | IQueueSreg sreg _ _ => reg_load_ok sreg 4
  (* nft_fib.c:110: dreg store at the result width. *)
  | IFibLoad _ res dst => reg_store_ok dst (fib_store_width res)
  (* No register operands (statement-only expressions). *)
  | IQuota _        => true
  | IConnlimit _    => true
  | IObjref _ _     => true
  | ISynproxy _ _   => true
  | ILast _         => true
  | IExthdrReset _ _ => true
  | ILimit _        => true
  | ICounter _ _    => true
  | INotrack        => true
  | ILog _          => true
  | IReject _ _     => true
  | IQueue _ _ _ _  => true
  (* nft_dynset.c:227,238: sreg_key/sreg_data load set->klen/set->dlen (set
     side); word-granular here, spans store-checked at their writers. *)
  | IDynset _ _ keyregs datareg _ =>
      forallb data_reg_ok keyregs && opt_reg_ok data_reg_ok datareg
  (* nft_dup_netdev.c:43 / nft_dup_ipv4.c/ipv6.c: dev reg loads sizeof(int)
     = 4; the addr reg loads 4 (ip) / 16 (ip6) — family not carried by the
     instruction, word-granular (the immediate that fills it is
     store-checked at its true width). *)
  | IDup devreg addrreg =>
      opt_reg_ok (fun r => reg_load_ok r 4) devreg
      && opt_reg_ok data_reg_ok addrreg
  (* nft_objref.c:175: sreg loads set->klen (set side). *)
  | IObjrefMap sregs _ => forallb data_reg_ok sregs
  (* nft_ct.c:630 (nft_ct_set_init): sreg loads the settable key's width;
     with a DIRECTION only zone (2) is admissible. *)
  | ICtSetDir key _ src => reg_load_ok src (ctsetdir_width key)
  (* nft_exthdr.c:591 (write path): sreg loads priv->len. *)
  | IExthdrWrite _ _ _ len src => reg_load_ok src len
  (* nft_ct.c:517 with NFTA_CT_DIRECTION: dreg stores the tuple-column
     width ([ctdir_width]). *)
  | ICtDirLoad key _ dst => reg_store_ok dst (ctdir_width key)
  (* nft_xfrm.c:91: dreg stores the key width. *)
  | IXfrmLoad _ _ key dst => reg_store_ok dst (xfrm_width key)
  (* nft_tunnel.c:106: dreg stores the key width. *)
  | ITunnelLoad key dst => reg_store_ok dst (tunnel_width key)
  (* nft_hash.c:137 (symhash): dreg stores sizeof(u32) = [symhash_width]. *)
  | ISymhash _ _ dst => reg_store_ok dst symhash_width
  (* nft_inner.c delegates to the wrapped meta/payload expression, which
     validates its own dreg at the wrapped width [w]. *)
  | IInnerLoad _ _ _ _ w dst => reg_store_ok dst w
  (* nft_payload.c:232: dreg stores priv->len. *)
  | IPayloadLoad _ _ len dst => reg_store_ok dst len
  (* nft_cmp.c:86: sreg loads desc.len = |v|; v is an nft_data value. *)
  | ICmp _ src v => reg_load_ok src (List.length v) && imm_value_ok v
  (* nft_range.c:78-90: sreg loads desc_from.len; from/to are nft_data
     values and must have EQUAL length (-EINVAL otherwise). *)
  | IRange _ src lo hi =>
      reg_load_ok src (List.length lo) && Nat.eqb (List.length lo) (List.length hi)
      && imm_value_ok lo && imm_value_ok hi
  (* nft_bitwise.c:255-264 (mask-xor form): sreg loads and dreg stores
     priv->len; mask and xor are nft_data values of exactly that length
     (nft_bitwise_init_mask_xor rejects a length mismatch). *)
  | IBitwise dst src mask xor =>
      reg_load_ok src (List.length mask) && reg_store_ok dst (List.length mask)
      && Nat.eqb (List.length xor) (List.length mask) && imm_value_ok mask && imm_value_ok xor
  (* nft_bitwise.c:226-264 (bool/shift forms): sreg/sreg2/dreg all transfer
     priv->len — carried by the surrounding expression's netlink LEN attr,
     not by this instruction; word-granular (the registers' contents are
     store-checked at their writers). *)
  | IBitwiseOr dst src1 src2 =>
      data_reg_ok dst && data_reg_ok src1 && data_reg_ok src2
  | IBitShift dst src _ _ => data_reg_ok dst && data_reg_ok src
  (* nft_byteorder.c:121-150: size must be 2, 4 or 8; sreg loads and dreg
     stores priv->len. *)
  | IByteorder dst src _ size len =>
      reg_load_ok src len && reg_store_ok dst len
      && (Nat.eqb size 2 || Nat.eqb size 4 || Nat.eqb size 8)
  (* nft_hash.c:95,113 (jhash): sreg loads the LEN attr; dreg stores
     sizeof(u32) = 4. *)
  | IJhash dst src len _ _ _ => reg_load_ok src len && reg_store_ok dst 4
  (* nft_lookup.c:153: sreg loads set->klen (set side).  A vmap's dreg is
     NFT_REG_VERDICT (verdict-typed store, no byte bounds). *)
  | ILookup srcs _ _ => forallb data_reg_ok srcs
  | IVmap srcs _     => forallb data_reg_ok srcs
  (* nft_immediate.c:67: dreg stores the nft_data value's length. *)
  | IImmediateData dst v => reg_store_ok dst (List.length v) && imm_value_ok v
  (* nft_payload.c:991 (set path): sreg loads priv->len. *)
  | IPayloadWrite src _ _ len _ _ _ => reg_load_ok src len
  (* nft_meta.c:658 (nft_meta_set_init): sreg loads the key's width — the
     same per-key table as the get path ([meta_width]). *)
  | IMetaSet k src => reg_load_ok src (meta_width k)
  (* nft_ct.c:630 (nft_ct_set_init, direction-free): sreg loads the key's
     width ([ct_width]). *)
  | ICtSet k src => reg_load_ok src (ct_width k)
  (* nft_lookup.c:153,171 (map form): key sreg loads set->klen, dreg stores
     set->dlen (both set side). *)
  | ILookupVal keys _ dreg =>
      forallb data_reg_ok keys && data_reg_ok dreg
  | ILookupValBr keys _ dreg =>
      forallb data_reg_ok keys && data_reg_ok dreg
  (* nft_nat.c:216-247: addr min/max regs load the family alen (NFinet
     admits none); proto min/max regs load sizeof(u16) = 2 — the same
     plen as nft_masq.c:46-64 / nft_redir.c:51-63. *)
  | INat _ family amin amax pmin pmax _ =>
      addr_reg_ok (nat_alen family) amin
      && addr_reg_ok (nat_alen family) amax
      && opt_reg_ok (fun r => reg_load_ok r 2) pmin
      && opt_reg_ok (fun r => reg_load_ok r 2) pmax
  (* Verdict-register immediate (NFT_REG_VERDICT, NFT_DATA_VERDICT branch of
     nft_validate_register_store: no byte bounds). *)
  | IImmediate _ => true
  end.

(** The validator over one rule's expressions and over a whole program. *)
Definition regs_valid (rp : rule_prog) : bool := forallb instr_regs_ok rp.
Definition regs_valid_prog (pr : program) : bool := forallb regs_valid pr.

(** [regs_valid] distributes over the compile-level concatenations. *)
Lemma regs_valid_app : forall a b,
  regs_valid (a ++ b) = regs_valid a && regs_valid b.
Proof. intros a b. apply forallb_app. Qed.
