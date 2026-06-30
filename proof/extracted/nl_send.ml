(* Nl_send — transmit a VERIFIED-compiled ruleset to the kernel over real netlink.

   The rule bytes this builds are a 1:1 serialisation of the verified
   [Compile.compile_chain] output (a [Bytecode.program] = list of instruction
   lists): each rule's instruction list is encoded, instruction by instruction,
   into the kernel's NFTA_RULE_EXPRESSIONS nlattr form, with the compiler's
   register numbers sent VERBATIM (the compiler's [reg_of_slot] already matches
   nft's NFT_REG_* / NFT_REG32_* numbering — see Compile.v).  The sender NEVER
   re-derives rules from the DSL; it only encodes what compile_chain produced.

   It also emits the *structural* netlink objects a ruleset needs around those
   verified rules — NEWTABLE / NEWCHAIN / NEWSET / NEWSETELEM — so a ruleset can
   be stood up from scratch (no preparatory `nft add`).  Those are metadata, not
   the verified bytecode: the set ELEMENT contents come from the verified
   optimizer's [Semantics.set_decls] (and the parsed named sets), and the
   table/chain framing is the parsed structure; none of it invents match logic.

   The whole ruleset is sent as ONE nfnetlink batch transaction (one
   BATCH_BEGIN/END), so the kernel applies it all-or-nothing — a failure on any
   message rolls the whole transaction back.

   Untrusted transport: like the renderer, this is glue, validated differentially
   against live `nft` (a netns round-trip via nl_send_test.sh), NOT part of the
   proof TCB.

   Trust boundary: for any instruction we do not know how to encode we raise
   [Unsupported "<instr>"] rather than silently dropping it — an honest failure
   instead of a wrong-but-quiet rule. *)

(* The extracted Coq modules (wrapped false) shadow several stdlib names
   (Bytes, String, List); pin them back to the real stdlib here. *)
module L = Stdlib.List
module Bytes = Stdlib.Bytes
module String = Stdlib.String

exception Unsupported of string

(* ------------------------------------------------------------------ *)
(* The one C primitive: open an AF_NETLINK/NETLINK_NETFILTER socket.    *)
(* (with NETLINK_EXT_ACK enabled, so rejections carry a readable text). *)
(* ------------------------------------------------------------------ *)
external nl_open : unit -> Unix.file_descr = "caml_nl_open"

(* ------------------------------------------------------------------ *)
(* Constants (verbatim from <linux/netfilter/nf_tables.h>, nfnetlink.h, *)
(* netlink.h, netfilter.h on this host — see nl_send_test.sh).          *)
(* ------------------------------------------------------------------ *)

(* netlink message flags *)
let nlm_f_request = 0x001
let nlm_f_ack     = 0x004
let nlm_f_create  = 0x400
let nlm_f_append  = 0x800

(* netlink reply message types *)
let nlmsg_error = 2

(* error-message ext-ack: NLM_F_ACK_TLVS / NLM_F_CAPPED in the ERROR header *)
let nlm_f_capped   = 0x100
let nlm_f_ack_tlvs = 0x200
let nlmsgerr_attr_msg = 1

(* nfnetlink batch + subsystem *)
let nfnl_subsys_nftables = 10
let nfnl_msg_batch_begin = 16   (* NLMSG_MIN_TYPE *)
let nfnl_msg_batch_end   = 17

(* nf_tables message types (low byte; high byte = subsys) *)
let nft_msg_newtable   = 0
let nft_msg_newchain   = 3
let nft_msg_newrule    = 6
let nft_msg_newset     = 9
let nft_msg_newsetelem = 12
let msg_type m = (nfnl_subsys_nftables lsl 8) lor m

(* nla nested flag *)
let nla_f_nested = 0x8000

(* nft rule / expr / list attributes *)
let nfta_rule_table       = 1
let nfta_rule_chain       = 2
let nfta_rule_expressions = 4
let nfta_list_elem        = 1
let nfta_expr_name        = 1
let nfta_expr_data        = 2

(* generic data attributes *)
let nfta_data_value   = 1
let nfta_data_verdict = 2
let nfta_verdict_code  = 1
let nfta_verdict_chain = 2

(* table / chain / hook *)
let nfta_table_name   = 1
let nfta_chain_table  = 1
let nfta_chain_name   = 3
let nfta_chain_hook   = 4
let nfta_chain_policy = 5
let nfta_chain_type   = 7
let nfta_hook_hooknum  = 1
let nfta_hook_priority = 2

(* set / set-elem *)
let nfta_set_table     = 1
let nfta_set_name      = 2
let nfta_set_flags     = 3
let nfta_set_key_type  = 4
let nfta_set_key_len   = 5
let nfta_set_data_type = 6
let nfta_set_data_len  = 7
let nfta_set_id        = 10
let nft_set_constant   = 0x2
let nft_set_map        = 0x8
let nfta_set_elem_key       = 1
let nfta_set_elem_data      = 2
let nfta_set_elem_list_table    = 1
let nfta_set_elem_list_set      = 2
let nfta_set_elem_list_elements = 3
let nfta_set_elem_list_set_id   = 4
(* NFT_DATA_VERDICT magic data-type for verdict maps *)
let nft_data_verdict = 0xffffff00

(* registers *)
let nft_reg_verdict = 0

(* meta (per <nf_tables.h>: UNSPEC=0, DREG=1, KEY=2, SREG=3) *)
let nfta_meta_dreg = 1
let nfta_meta_key  = 2
let nfta_meta_sreg = 3

(* payload *)
let nfta_payload_dreg        = 1
let nfta_payload_base        = 2
let nfta_payload_offset      = 3
let nfta_payload_len         = 4
let nfta_payload_sreg        = 5
let nfta_payload_csum_type   = 6
let nfta_payload_csum_offset = 7
let nfta_payload_csum_flags  = 8

(* cmp *)
let nfta_cmp_sreg = 1
let nfta_cmp_op   = 2
let nfta_cmp_data = 3

(* range *)
let nfta_range_sreg      = 1
let nfta_range_op        = 2
let nfta_range_from_data = 3
let nfta_range_to_data   = 4

(* immediate *)
let nfta_immediate_dreg = 1
let nfta_immediate_data = 2

(* lookup *)
let nfta_lookup_set   = 1
let nfta_lookup_sreg  = 2
let nfta_lookup_dreg  = 3
let nfta_lookup_flags = 4
let nft_lookup_f_inv  = 1

(* bitwise *)
let nfta_bitwise_sreg  = 1
let nfta_bitwise_dreg  = 2
let nfta_bitwise_len   = 3
let nfta_bitwise_mask  = 4
let nfta_bitwise_xor   = 5
let nfta_bitwise_op    = 6
let nfta_bitwise_data  = 7
let nfta_bitwise_sreg2 = 8
let nft_bitwise_lshift = 1
let nft_bitwise_rshift = 2
let nft_bitwise_or     = 4

(* byteorder *)
let nfta_byteorder_sreg = 1
let nfta_byteorder_dreg = 2
let nfta_byteorder_op   = 3
let nfta_byteorder_len  = 4
let nfta_byteorder_size = 5

(* ct *)
let nfta_ct_dreg      = 1
let nfta_ct_key       = 2
let nfta_ct_direction = 3
let nfta_ct_sreg      = 4

(* nat *)
let nfta_nat_type          = 1
let nfta_nat_family        = 2
let nfta_nat_reg_addr_min  = 3
let nfta_nat_reg_addr_max  = 4
let nfta_nat_reg_proto_min = 5
let nfta_nat_reg_proto_max = 6
let nfta_nat_flags         = 7
let nft_nat_snat = 0
let nft_nat_dnat = 1
let nfta_masq_flags          = 1
let nfta_masq_reg_proto_min  = 2
let nfta_masq_reg_proto_max  = 3
let nfta_redir_reg_proto_min = 1
let nfta_redir_reg_proto_max = 2
let nfta_redir_flags         = 3

(* counter (64-bit) *)
let nfta_counter_bytes   = 1
let nfta_counter_packets = 2

(* limit *)
let nfta_limit_rate  = 1
let nfta_limit_unit  = 2
let nfta_limit_burst = 3
let nfta_limit_type  = 4
let nfta_limit_flags = 5
let nft_limit_pkts      = 0
let nft_limit_pkt_bytes = 1

(* reject *)
let nfta_reject_type      = 1
let nfta_reject_icmp_code = 2

(* log *)
let nfta_log_prefix = 2

(* fib *)
let nfta_fib_dreg   = 1
let nfta_fib_result = 2
let nfta_fib_flags  = 3
let fib_f_saddr   = 1
let fib_f_daddr   = 2
let fib_f_mark    = 4
let fib_f_iif     = 8
let fib_f_oif     = 16
let fib_f_present = 32
let nft_fib_result_oif      = 1
let nft_fib_result_oifname  = 2
let nft_fib_result_addrtype = 3

(* queue *)
let nfta_queue_num       = 1
let nfta_queue_total     = 2
let nfta_queue_flags     = 3
let nfta_queue_sreg_qnum = 4
let nft_queue_flag_bypass = 0x1
let nft_queue_flag_cpu_fanout = 0x2

(* netfilter base verdicts / nft pseudo-verdicts (as 32-bit two's complement) *)
let nf_drop      = 0
let nf_accept    = 1
let nft_continue = -1
let nft_jump     = -3
let nft_goto     = -4
let nft_return   = -5

(* nfproto (nfgenmsg.nfgen_family) *)
let nfproto_inet   = 1
let nfproto_ipv4   = 2
let nfproto_arp    = 3
let nfproto_netdev = 5
let nfproto_bridge = 7
let nfproto_ipv6   = 10

(* DSL table family string -> nfgen_family *)
let nfproto_of_family = function
  | "ip"     -> nfproto_ipv4
  | "ip6"    -> nfproto_ipv6
  | "inet"   -> nfproto_inet
  | "arp"    -> nfproto_arp
  | "bridge" -> nfproto_bridge
  | "netdev" -> nfproto_netdev
  | other    -> raise (Unsupported ("address family " ^ other))

(* netfilter hook name -> NF_INET_* hooknum *)
let hooknum_of_name = function
  | "prerouting"  -> 0
  | "input"       -> 1
  | "forward"     -> 2
  | "output"      -> 3
  | "postrouting" -> 4
  | "ingress"     -> 5
  | other         -> raise (Unsupported ("hook " ^ other))

(* nft_meta_keys: Packet.meta_key -> kernel enum value (exact, from the host
   header — note iif=4, oif=5, iifname=6, oifname=7, iiftype=8). *)
let nl_meta_key : Packet.meta_key -> int = function
  | Packet.MKlen          -> 0
  | Packet.MKprotocol     -> 1
  | Packet.MKpriority     -> 2
  | Packet.MKmark         -> 3
  | Packet.MKiif          -> 4
  | Packet.MKoif          -> 5
  | Packet.MKiifname      -> 6
  | Packet.MKoifname      -> 7
  | Packet.MKiiftype      -> 8
  | Packet.MKoiftype      -> 9
  | Packet.MKskuid        -> 10
  | Packet.MKskgid        -> 11
  | Packet.MKrtclassid    -> 13
  | Packet.MKnfproto      -> 15
  | Packet.MKl4proto      -> 16
  | Packet.MKbri_iifname  -> 17
  | Packet.MKbri_oifname  -> 18
  | Packet.MKpkttype      -> 19
  | Packet.MKcpu          -> 20
  | Packet.MKiifgroup     -> 21
  | Packet.MKoifgroup     -> 22
  | Packet.MKcgroup       -> 23
  | Packet.MKprandom      -> 24
  | Packet.MKsecpath      -> 25
  | Packet.MKbri_iifpvid  -> 28
  | Packet.MKbri_iifvproto-> 29
  | Packet.MKtime         -> 30  (* NFT_META_TIME_NS *)
  | Packet.MKday          -> 31  (* NFT_META_TIME_DAY *)
  | Packet.MKhour         -> 32  (* NFT_META_TIME_HOUR *)
  | Packet.MKsdif         -> 33
  | Packet.MKsdifname     -> 34
  | Packet.MKbroute       -> 35  (* NFT_META_BRI_BROUTE *)
  | Packet.MKibrhwaddr    -> 37  (* NFT_META_BRI_IIFHWADDR *)

(* nft_ct_keys: Packet.ct_key -> kernel enum value (exact, from the host header) *)
let nl_ct_key : Packet.ct_key -> int = function
  | Packet.CKstate      -> 0
  | Packet.CKdirection  -> 1
  | Packet.CKstatus     -> 2
  | Packet.CKmark       -> 3
  | Packet.CKexpiration -> 5
  | Packet.CKhelper     -> 6
  | Packet.CKl3proto    -> 7
  | Packet.CKproto      -> 10
  | Packet.CKlabel      -> 13
  | Packet.CKpackets    -> 14
  | Packet.CKbytes      -> 15
  | Packet.CKavgpkt     -> 16
  | Packet.CKzone       -> 17
  | Packet.CKevent      -> 18
  | Packet.CKid         -> 23

(* a directional ct key given by string name (e.g. "saddr") + a direction *)
let ct_dir_num = function "reply" -> 1 | _ -> 0
let ct_key_of_name n = match Codec.ct_of_name n with
  | Some k -> nl_ct_key k
  | None ->
      (match n with
       | "saddr" | "src"       -> 8   (* NFT_CT_SRC *)
       | "daddr" | "dst"       -> 9   (* NFT_CT_DST *)
       | "proto-src"           -> 11  (* NFT_CT_PROTO_SRC *)
       | "proto-dst"           -> 12  (* NFT_CT_PROTO_DST *)
       | other -> raise (Unsupported ("ct directional key " ^ other)))

(* nft payload base: Packet.pbase -> NFT_PAYLOAD_*_HEADER *)
let nl_pbase : Packet.pbase -> int = function
  | Packet.PLink      -> 0
  | Packet.PNetwork   -> 1
  | Packet.PTransport -> 2
  | Packet.PInner     -> 3
  | Packet.PTunnel    -> 4

(* nft_cmp_ops *)
let nl_cmpop : Bytecode.cmpop -> int = function
  | Bytecode.CEq -> 0
  | Bytecode.CNe -> 1
  | Bytecode.CLt -> 2
  | Bytecode.CLe -> 3
  | Bytecode.CGt -> 4
  | Bytecode.CGe -> 5

(* nft_range_ops: range carries an eq/neq op; anything but != is EQ *)
let nl_rangeop : Bytecode.cmpop -> int = function
  | Bytecode.CNe -> 1   (* NFT_RANGE_NEQ *)
  | _            -> 0   (* NFT_RANGE_EQ  *)

(* ------------------------------------------------------------------ *)
(* Byte emitters.  Netlink message/attr headers are HOST byte order    *)
(* (little-endian on x86_64); nft attribute scalars are BIG-endian     *)
(* (libnftnl htonl's them); data values are raw kernel-order bytes.     *)
(* ------------------------------------------------------------------ *)

let le16 v =
  let b = Bytes.create 2 in
  Bytes.set b 0 (Char.chr (v land 0xff));
  Bytes.set b 1 (Char.chr ((v lsr 8) land 0xff));
  Bytes.unsafe_to_string b

let le32 v =
  let v = v land 0xffffffff in
  let b = Bytes.create 4 in
  Bytes.set b 0 (Char.chr (v land 0xff));
  Bytes.set b 1 (Char.chr ((v lsr 8) land 0xff));
  Bytes.set b 2 (Char.chr ((v lsr 16) land 0xff));
  Bytes.set b 3 (Char.chr ((v lsr 24) land 0xff));
  Bytes.unsafe_to_string b

let be16 v =
  let b = Bytes.create 2 in
  Bytes.set b 0 (Char.chr ((v lsr 8) land 0xff));
  Bytes.set b 1 (Char.chr (v land 0xff));
  Bytes.unsafe_to_string b

(* big-endian 32-bit scalar, two's complement for negative verdicts *)
let be32 v =
  let v = v land 0xffffffff in
  let b = Bytes.create 4 in
  Bytes.set b 0 (Char.chr ((v lsr 24) land 0xff));
  Bytes.set b 1 (Char.chr ((v lsr 16) land 0xff));
  Bytes.set b 2 (Char.chr ((v lsr 8) land 0xff));
  Bytes.set b 3 (Char.chr (v land 0xff));
  Bytes.unsafe_to_string b

(* big-endian 64-bit scalar (counter bytes/packets, limit rate/unit) *)
let be64 v =
  let b = Bytes.create 8 in
  for i = 0 to 7 do
    Bytes.set b i (Char.chr ((v asr ((7 - i) * 8)) land 0xff))
  done;
  Bytes.unsafe_to_string b

(* a Bytecode.data (int list, kernel-order bytes) -> raw string, in list order
   (NOT byte-swapped: the compiler already produced kernel-comparison order). *)
let data_to_string (d : int list) : string =
  let b = Buffer.create (L.length d) in
  L.iter (fun x -> Buffer.add_char b (Char.chr (x land 0xff))) d;
  Buffer.contents b

let nla_align n = (n + 3) land (lnot 3)

(* one nlattr: {u16 len (incl 4-byte header, NOT padding); u16 type}; payload
   padded out to NLA_ALIGN(4). *)
let attr typ payload =
  let len = 4 + String.length payload in
  let pad = nla_align len - len in
  le16 len ^ le16 typ ^ payload ^ String.make pad '\000'

let attr_u8 typ v        = attr typ (String.make 1 (Char.chr (v land 0xff)))
let attr_be16 typ v      = attr typ (be16 v)
let attr_u32 typ v       = attr typ (be32 v)
let attr_u64 typ v       = attr typ (be64 v)
let attr_str typ s       = attr typ (s ^ "\000")
let attr_nested typ body = attr (typ lor nla_f_nested) body
let attr_data_value d    = attr nfta_data_value (data_to_string d)

(* struct nfgenmsg { u8 family; u8 version=0; __be16 res_id } *)
let nfgenmsg ~family ~res_id =
  String.make 1 (Char.chr (family land 0xff)) ^ "\000" ^ be16 res_id

(* struct nlmsghdr {u32 len; u16 type; u16 flags; u32 seq; u32 pid=0} + payload.
   Payloads are already 4-aligned, so len is too. *)
let nlmsg ~typ ~flags ~seq payload =
  let len = 16 + String.length payload in
  le32 len ^ le16 typ ^ le16 flags ^ le32 seq ^ le32 0 ^ payload

(* ------------------------------------------------------------------ *)
(* Per-instruction expression encoding: instr -> (expr-name, expr-data).*)
(* expr-data is the nested NFTA_EXPR_DATA body (concatenated attrs).     *)
(* ------------------------------------------------------------------ *)

let instr_name : Bytecode.instr -> string = function
  | Bytecode.IMetaLoad _ -> "IMetaLoad"   | Bytecode.ICtLoad _ -> "ICtLoad"
  | Bytecode.IRtLoad _ -> "IRtLoad"       | Bytecode.ISocketLoad _ -> "ISocketLoad"
  | Bytecode.INumgen _ -> "INumgen"       | Bytecode.IOsf _ -> "IOsf"
  | Bytecode.IExthdrLoad _ -> "IExthdrLoad" | Bytecode.ITproxy _ -> "ITproxy"
  | Bytecode.IFwd _ -> "IFwd"             | Bytecode.IQueueSreg _ -> "IQueueSreg"
  | Bytecode.IFibLoad _ -> "IFibLoad"     | Bytecode.IQuota _ -> "IQuota"
  | Bytecode.IConnlimit _ -> "IConnlimit" | Bytecode.IObjref _ -> "IObjref"
  | Bytecode.ISynproxy _ -> "ISynproxy"   | Bytecode.ILast _ -> "ILast"
  | Bytecode.IDynset _ -> "IDynset"       | Bytecode.IExthdrReset _ -> "IExthdrReset"
  | Bytecode.IDup _ -> "IDup"             | Bytecode.IObjrefMap _ -> "IObjrefMap"
  | Bytecode.ICtSetDir _ -> "ICtSetDir"   | Bytecode.IExthdrWrite _ -> "IExthdrWrite"
  | Bytecode.ICtDirLoad _ -> "ICtDirLoad" | Bytecode.IXfrmLoad _ -> "IXfrmLoad"
  | Bytecode.ITunnelLoad _ -> "ITunnelLoad" | Bytecode.ISymhash _ -> "ISymhash"
  | Bytecode.IInnerLoad _ -> "IInnerLoad" | Bytecode.IPayloadLoad _ -> "IPayloadLoad"
  | Bytecode.ICmp _ -> "ICmp"             | Bytecode.IRange _ -> "IRange"
  | Bytecode.IBitwise _ -> "IBitwise"     | Bytecode.IBitwiseOr _ -> "IBitwiseOr"
  | Bytecode.IBitShift _ -> "IBitShift"   | Bytecode.IByteorder _ -> "IByteorder"
  | Bytecode.IJhash _ -> "IJhash"         | Bytecode.ILookup _ -> "ILookup"
  | Bytecode.IVmap _ -> "IVmap"           | Bytecode.IImmediateData _ -> "IImmediateData"
  | Bytecode.IPayloadWrite _ -> "IPayloadWrite" | Bytecode.IMetaSet _ -> "IMetaSet"
  | Bytecode.ICtSet _ -> "ICtSet"         | Bytecode.ILookupVal _ -> "ILookupVal"
  | Bytecode.ILookupValBr _ -> "ILookupValBr"
  | Bytecode.INat _ -> "INat"             | Bytecode.ILimit _ -> "ILimit"
  | Bytecode.ICounter _ -> "ICounter"     | Bytecode.INotrack -> "INotrack"
  | Bytecode.ILog _ -> "ILog"             | Bytecode.IReject _ -> "IReject"
  | Bytecode.IQueue _ -> "IQueue"         | Bytecode.IImmediate _ -> "IImmediate"

(* the NFTA_VERDICT_* body of a verdict (the inside of NFTA_DATA_VERDICT) *)
let verdict_data (v : Verdict.verdict) : string = match v with
  | Verdict.Accept   -> attr_u32 nfta_verdict_code nf_accept
  | Verdict.Drop     -> attr_u32 nfta_verdict_code nf_drop
  | Verdict.Continue -> attr_u32 nfta_verdict_code nft_continue
  | Verdict.Return   -> attr_u32 nfta_verdict_code nft_return
  | Verdict.Jump n   -> attr_u32 nfta_verdict_code nft_jump ^ attr_str nfta_verdict_chain n
  | Verdict.Goto n   -> attr_u32 nfta_verdict_code nft_goto ^ attr_str nfta_verdict_chain n
  | Verdict.Reject _ ->
      (* a reject is its OWN expression (IReject), never a verdict-register code *)
      raise (Unsupported "IImmediate(Reject): reject is not an immediate verdict")
  | Verdict.Queue _  ->
      raise (Unsupported "IImmediate(Queue): queue is not an immediate verdict")

(* require a non-empty source-register list; the compiler always supplies one,
   but rather than fabricate a register (a wrong-but-quiet rule) we fail loud. *)
let sreg0 ctx = function
  | x :: _ -> x
  | []     -> raise (Unsupported (ctx ^ ": empty source-register list"))

let encode_instr (ins : Bytecode.instr) : string * string =
  match ins with
  | Bytecode.IMetaLoad (k, r) ->
      ("meta",
       attr_u32 nfta_meta_dreg r ^ attr_u32 nfta_meta_key (nl_meta_key k))
  | Bytecode.IMetaSet (k, src) ->
      ("meta",
       attr_u32 nfta_meta_sreg src ^ attr_u32 nfta_meta_key (nl_meta_key k))
  | Bytecode.IPayloadLoad (b, off, len, r) ->
      ("payload",
       attr_u32 nfta_payload_dreg r
       ^ attr_u32 nfta_payload_base (nl_pbase b)
       ^ attr_u32 nfta_payload_offset off
       ^ attr_u32 nfta_payload_len len)
  | Bytecode.IPayloadWrite (src, b, off, len, ct, co, cf) ->
      ("payload",
       attr_u32 nfta_payload_sreg src
       ^ attr_u32 nfta_payload_base (nl_pbase b)
       ^ attr_u32 nfta_payload_offset off
       ^ attr_u32 nfta_payload_len len
       ^ attr_u32 nfta_payload_csum_type ct
       ^ attr_u32 nfta_payload_csum_offset co
       ^ attr_u32 nfta_payload_csum_flags cf)
  | Bytecode.ICmp (op, r, v) ->
      ("cmp",
       attr_u32 nfta_cmp_sreg r
       ^ attr_u32 nfta_cmp_op (nl_cmpop op)
       ^ attr_nested nfta_cmp_data (attr_data_value v))
  | Bytecode.IRange (op, r, lo, hi) ->
      ("range",
       attr_u32 nfta_range_sreg r
       ^ attr_u32 nfta_range_op (nl_rangeop op)
       ^ attr_nested nfta_range_from_data (attr_data_value lo)
       ^ attr_nested nfta_range_to_data (attr_data_value hi))
  | Bytecode.IImmediate v ->
      let vbody = attr_nested nfta_data_verdict (verdict_data v) in
      ("immediate",
       attr_u32 nfta_immediate_dreg nft_reg_verdict
       ^ attr_nested nfta_immediate_data vbody)
  | Bytecode.IImmediateData (dst, v) ->
      ("immediate",
       attr_u32 nfta_immediate_dreg dst
       ^ attr_nested nfta_immediate_data (attr_data_value v))
  | Bytecode.ILookup (srcs, name, neg) ->
      let sreg = sreg0 "ILookup" srcs in
      let base =
        attr_str nfta_lookup_set name ^ attr_u32 nfta_lookup_sreg sreg in
      ("lookup",
       if neg then base ^ attr_u32 nfta_lookup_flags nft_lookup_f_inv else base)
  | Bytecode.ILookupVal (keys, name, dreg) | Bytecode.ILookupValBr (keys, name, dreg) ->
      let sreg = sreg0 "ILookupVal" keys in
      ("lookup",
       attr_str nfta_lookup_set name
       ^ attr_u32 nfta_lookup_sreg sreg
       ^ attr_u32 nfta_lookup_dreg dreg)
  | Bytecode.IVmap (srcs, name) ->
      let sreg = sreg0 "IVmap" srcs in
      ("lookup",
       attr_str nfta_lookup_set name
       ^ attr_u32 nfta_lookup_sreg sreg
       ^ attr_u32 nfta_lookup_dreg nft_reg_verdict)
  | Bytecode.IBitwise (dst, src, mask, xor) ->
      ("bitwise",
       attr_u32 nfta_bitwise_sreg src
       ^ attr_u32 nfta_bitwise_dreg dst
       ^ attr_u32 nfta_bitwise_len (L.length mask)
       ^ attr_nested nfta_bitwise_mask (attr_data_value mask)
       ^ attr_nested nfta_bitwise_xor (attr_data_value xor))
  | Bytecode.IBitwiseOr (dst, s1, s2) ->
      (* boolean OR of two source registers (len inferred = 4: the kernel
         requires a length; the optimizer only mints reg-wide OR) *)
      ("bitwise",
       attr_u32 nfta_bitwise_sreg s1
       ^ attr_u32 nfta_bitwise_sreg2 s2
       ^ attr_u32 nfta_bitwise_dreg dst
       ^ attr_u32 nfta_bitwise_len 4
       ^ attr_u32 nfta_bitwise_op nft_bitwise_or)
  | Bytecode.IBitShift (dst, src, shl, amt) ->
      ("bitwise",
       attr_u32 nfta_bitwise_sreg src
       ^ attr_u32 nfta_bitwise_dreg dst
       ^ attr_u32 nfta_bitwise_len 4
       ^ attr_u32 nfta_bitwise_op (if shl then nft_bitwise_lshift else nft_bitwise_rshift)
       ^ attr_nested nfta_bitwise_data (attr_data_value [ (amt lsr 24) land 0xff;
                                                          (amt lsr 16) land 0xff;
                                                          (amt lsr 8) land 0xff;
                                                          amt land 0xff ]))
  | Bytecode.IByteorder (dst, src, hton, sz, len) ->
      ("byteorder",
       attr_u32 nfta_byteorder_sreg src
       ^ attr_u32 nfta_byteorder_dreg dst
       ^ attr_u32 nfta_byteorder_op (if hton then 1 else 0)
       ^ attr_u32 nfta_byteorder_len len
       ^ attr_u32 nfta_byteorder_size sz)
  | Bytecode.ICtLoad (k, r) ->
      ("ct", attr_u32 nfta_ct_dreg r ^ attr_u32 nfta_ct_key (nl_ct_key k))
  | Bytecode.ICtSet (k, src) ->
      ("ct", attr_u32 nfta_ct_key (nl_ct_key k) ^ attr_u32 nfta_ct_sreg src)
  | Bytecode.ICtDirLoad (key, dir, r) ->
      ("ct",
       attr_u32 nfta_ct_dreg r
       ^ attr_u32 nfta_ct_key (ct_key_of_name key)
       ^ attr_u32 nfta_ct_direction (ct_dir_num dir))
  | Bytecode.ICtSetDir (key, dir, src) ->
      ("ct",
       attr_u32 nfta_ct_key (ct_key_of_name key)
       ^ attr_u32 nfta_ct_sreg src
       ^ attr_u32 nfta_ct_direction (ct_dir_num dir))
  | Bytecode.INat (kind, family, amin, amax, pmin, pmax, flags) ->
      let regopt typ = function Some r -> attr_u32 typ r | None -> "" in
      let flagopt typ = if flags > 0 then attr_u32 typ flags else "" in
      (match kind with
       | "snat" | "dnat" ->
           let typ = if kind = "dnat" then nft_nat_dnat else nft_nat_snat in
           ("nat",
            attr_u32 nfta_nat_type typ
            ^ attr_u32 nfta_nat_family (nfproto_of_family family)
            ^ regopt nfta_nat_reg_addr_min amin
            ^ regopt nfta_nat_reg_addr_max amax
            ^ regopt nfta_nat_reg_proto_min pmin
            ^ regopt nfta_nat_reg_proto_max pmax
            ^ flagopt nfta_nat_flags)
       | "masq" ->
           ("masq",
            flagopt nfta_masq_flags
            ^ regopt nfta_masq_reg_proto_min pmin
            ^ regopt nfta_masq_reg_proto_max pmax)
       | "redir" ->
           ("redir",
            regopt nfta_redir_reg_proto_min pmin
            ^ regopt nfta_redir_reg_proto_max pmax
            ^ flagopt nfta_redir_flags)
       | other -> raise (Unsupported ("INat kind " ^ other)))
  | Bytecode.ICounter (p, b) ->
      ("counter", attr_u64 nfta_counter_bytes b ^ attr_u64 nfta_counter_packets p)
  | Bytecode.ILimit s ->
      let unit_secs = match s.Packet.ls_unit with
        | 0 -> 1 | 1 -> 60 | 2 -> 3600 | 3 -> 86400 | 4 -> 604800 | _ -> 1 in
      ("limit",
       attr_u64 nfta_limit_rate s.Packet.ls_rate
       ^ attr_u64 nfta_limit_unit unit_secs
       ^ attr_u32 nfta_limit_burst s.Packet.ls_burst
       ^ attr_u32 nfta_limit_type
           (if s.Packet.ls_bytes then nft_limit_pkt_bytes else nft_limit_pkts)
       ^ attr_u32 nfta_limit_flags s.Packet.ls_flags)
  | Bytecode.IReject (t, c) ->
      ("reject", attr_u32 nfta_reject_type t ^ attr_u8 nfta_reject_icmp_code c)
  | Bytecode.ILog opts ->
      ("log", if opts = "" then "" else attr_str nfta_log_prefix opts)
  | Bytecode.INotrack -> ("notrack", "")
  | Bytecode.IFibLoad (sel, res, r) ->
      let toks = L.map String.trim (String.split_on_char '.' sel) in
      let has s = L.mem s toks in
      let flags =
        (if has "saddr" then fib_f_saddr else 0)
        lor (if has "daddr" then fib_f_daddr else 0)
        lor (if has "mark" then fib_f_mark else 0)
        lor (if has "iif" then fib_f_iif else 0)
        lor (if has "oif" then fib_f_oif else 0)
        lor (match res with Packet.FRpresent -> fib_f_present | _ -> 0) in
      let result = match res with
        | Packet.FRoif | Packet.FRpresent -> nft_fib_result_oif
        | Packet.FRoifname                -> nft_fib_result_oifname
        | Packet.FRtype                   -> nft_fib_result_addrtype in
      ("fib",
       attr_u32 nfta_fib_dreg r
       ^ attr_u32 nfta_fib_result result
       ^ attr_u32 nfta_fib_flags flags)
  | Bytecode.IQueue (lo, hi, byp, fan) ->
      (* NFTA_QUEUE_NUM/TOTAL/FLAGS are NLA_U16 (ntohs in nft_queue.c) *)
      let flags =
        (if byp then nft_queue_flag_bypass else 0)
        lor (if fan then nft_queue_flag_cpu_fanout else 0) in
      ("queue",
       attr_be16 nfta_queue_num lo
       ^ attr_be16 nfta_queue_total (hi - lo + 1)
       ^ (if flags > 0 then attr_be16 nfta_queue_flags flags else ""))
  | Bytecode.IQueueSreg (sreg, byp, fan) ->
      let flags =
        (if byp then nft_queue_flag_bypass else 0)
        lor (if fan then nft_queue_flag_cpu_fanout else 0) in
      ("queue",
       attr_u32 nfta_queue_sreg_qnum sreg
       ^ (if flags > 0 then attr_be16 nfta_queue_flags flags else ""))
  | other -> raise (Unsupported (instr_name other))

(* one NFTA_LIST_ELEM = nested { NFTA_EXPR_NAME=string, NFTA_EXPR_DATA=nested } *)
let encode_elem (ins : Bytecode.instr) : string =
  let (name, data) = encode_instr ins in
  attr_nested nfta_list_elem
    (attr_str nfta_expr_name name ^ attr_nested nfta_expr_data data)

let encode_exprs (rp : Bytecode.rule_prog) : string =
  String.concat "" (L.map encode_elem rp)

(* ------------------------------------------------------------------ *)
(* Structural objects: table / chain / set / set-elem / rule messages. *)
(* A [msg] is a body to be sealed with a seq + nlmsghdr at batch time.  *)
(* ------------------------------------------------------------------ *)

type msg = { m_type : int; m_flags : int; m_payload : string }

let create_flags = nlm_f_request lor nlm_f_create lor nlm_f_ack
let rule_flags   = nlm_f_request lor nlm_f_create lor nlm_f_append lor nlm_f_ack

let msg_table ~family ~table : msg =
  { m_type = msg_type nft_msg_newtable; m_flags = create_flags;
    m_payload = nfgenmsg ~family ~res_id:0 ^ attr_str nfta_table_name table }

(* base = Some (chain-type, hooknum, priority); None for a jump-target chain *)
let msg_chain ~family ~table ~name ~base ~policy : msg =
  let body =
    nfgenmsg ~family ~res_id:0
    ^ attr_str nfta_chain_table table
    ^ attr_str nfta_chain_name name
    ^ (match base with
       | Some (ctype, hooknum, prio) ->
           attr_nested nfta_chain_hook
             (attr_u32 nfta_hook_hooknum hooknum
              ^ attr_u32 nfta_hook_priority prio)
           ^ attr_str nfta_chain_type ctype
           ^ (match policy with Some p -> attr_u32 nfta_chain_policy p | None -> "")
       | None -> "") in
  { m_type = msg_type nft_msg_newchain; m_flags = create_flags; m_payload = body }

(* a set/map/vmap definition.  [klen]/[dlen] in bytes; [dtype] = Some magic for
   a verdict map, [Some 0]/[None] for a data map's generic data, [None] for a
   plain membership set. *)
let msg_set ~family ~table ~name ~set_id ~flags ~klen ~dtype ~dlen : msg =
  let body =
    nfgenmsg ~family ~res_id:0
    ^ attr_str nfta_set_table table
    ^ attr_str nfta_set_name name
    ^ attr_u32 nfta_set_flags flags
    ^ attr_u32 nfta_set_key_type 0
    ^ attr_u32 nfta_set_key_len klen
    ^ (match dtype with Some t -> attr_u32 nfta_set_data_type t | None -> "")
    ^ (match dlen with Some l -> attr_u32 nfta_set_data_len l | None -> "")
    ^ attr_u32 nfta_set_id set_id in
  { m_type = msg_type nft_msg_newset; m_flags = create_flags; m_payload = body }

(* a single set element: a key, optionally with data (verdict or value bytes) *)
type elemdata = EVerdict of Verdict.verdict | EBytes of int list
type elem = { ek : int list; ed : elemdata option }

let encode_set_elem (e : elem) : string =
  let key = attr_nested nfta_set_elem_key (attr_data_value e.ek) in
  let dat = match e.ed with
    | None -> ""
    | Some (EBytes b) -> attr_nested nfta_set_elem_data (attr_data_value b)
    | Some (EVerdict v) ->
        attr_nested nfta_set_elem_data (attr_nested nfta_data_verdict (verdict_data v)) in
  attr_nested nfta_list_elem (key ^ dat)

let msg_setelems ~family ~table ~set ~set_id (elems : elem list) : msg =
  let body =
    nfgenmsg ~family ~res_id:0
    ^ attr_str nfta_set_elem_list_table table
    ^ attr_str nfta_set_elem_list_set set
    ^ attr_u32 nfta_set_elem_list_set_id set_id
    ^ attr_nested nfta_set_elem_list_elements
        (String.concat "" (L.map encode_set_elem elems)) in
  { m_type = msg_type nft_msg_newsetelem; m_flags = create_flags; m_payload = body }

let msg_rule ~family ~table ~chain (rp : Bytecode.rule_prog) : msg =
  let body =
    nfgenmsg ~family ~res_id:0
    ^ attr_str nfta_rule_table table
    ^ attr_str nfta_rule_chain chain
    ^ attr_nested nfta_rule_expressions (encode_exprs rp) in
  { m_type = msg_type nft_msg_newrule; m_flags = rule_flags; m_payload = body }

(* ------------------------------------------------------------------ *)
(* Whole NFNL batch: BEGIN ; <msgs> ; END.  Returns (bytes, end_seq).   *)
(* All messages ride in one transaction (atomic all-or-nothing apply).  *)
(* ------------------------------------------------------------------ *)

let build_batch (msgs : msg list) : string * int =
  let seq = ref 0 in
  let next () = incr seq; !seq in
  let begin_msg =
    nlmsg ~typ:nfnl_msg_batch_begin
      ~flags:(nlm_f_request lor nlm_f_ack) ~seq:(next ())
      (nfgenmsg ~family:0 ~res_id:nfnl_subsys_nftables) in
  let body =
    L.map (fun m -> nlmsg ~typ:m.m_type ~flags:m.m_flags ~seq:(next ()) m.m_payload)
      msgs in
  let end_seq = next () in
  let end_msg =
    nlmsg ~typ:nfnl_msg_batch_end
      ~flags:(nlm_f_request lor nlm_f_ack) ~seq:end_seq
      (nfgenmsg ~family:0 ~res_id:nfnl_subsys_nftables) in
  (String.concat "" (begin_msg :: body @ [ end_msg ]), end_seq)

(* ------------------------------------------------------------------ *)
(* Dry-run hexdump.                                                     *)
(* ------------------------------------------------------------------ *)

let hexdump (buf : string) : string =
  let n = String.length buf in
  let b = Buffer.create (n * 4) in
  let i = ref 0 in
  while !i < n do
    Buffer.add_string b (Printf.sprintf "%04x: " !i);
    for j = 0 to 15 do
      if !i + j < n then Buffer.add_string b (Printf.sprintf "%02x " (Char.code buf.[!i + j]))
      else Buffer.add_string b "   "
    done;
    Buffer.add_char b ' ';
    for j = 0 to 15 do
      if !i + j < n then begin
        let c = Char.code buf.[!i + j] in
        Buffer.add_char b (if c >= 32 && c < 127 then Char.chr c else '.')
      end
    done;
    Buffer.add_char b '\n';
    i := !i + 16
  done;
  Buffer.contents b

(* ------------------------------------------------------------------ *)
(* Send + parse the kernel's ACK/ERROR replies.                         *)
(* ------------------------------------------------------------------ *)

(* unsigned little-endian 32-bit read *)
let rd_u32 s o =
  (Char.code s.[o])
  lor (Char.code s.[o + 1] lsl 8)
  lor (Char.code s.[o + 2] lsl 16)
  lor (Char.code s.[o + 3] lsl 24)

let rd_u16 s o = (Char.code s.[o]) lor (Char.code s.[o + 1] lsl 8)

(* find the NLMSGERR_ATTR_MSG string in an ERROR message's ext-ack TLVs, if the
   kernel attached one.  [o]=offset of the error nlmsghdr, [len]=its length. *)
let ext_ack_msg (s : string) (o : int) (len : int) : string option =
  let n = String.length s in
  let flags = rd_u16 s (o + 6) in
  if flags land nlm_f_ack_tlvs = 0 then None
  else begin
    (* payload: s32 error ; struct nlmsghdr orig ; [orig payload unless CAPPED] *)
    let orig_len = rd_u32 s (o + 16 + 4) in
    let tlv_start =
      if flags land nlm_f_capped <> 0 then o + 16 + 4 + 16
      else o + 16 + 4 + nla_align orig_len in
    let stop = min n (o + len) in
    let res = ref None and p = ref tlv_start in
    while !p + 4 <= stop do
      let alen = rd_u16 s !p and atyp = rd_u16 s (!p + 2) in
      if alen < 4 || !p + alen > stop then p := stop
      else begin
        if atyp land 0x3fff = nlmsgerr_attr_msg then begin
          let dl = alen - 4 in
          let raw = String.sub s (!p + 4) dl in
          (* strip a trailing NUL *)
          let raw = if dl > 0 && raw.[dl - 1] = '\000'
                    then String.sub raw 0 (dl - 1) else raw in
          res := Some raw
        end;
        p := !p + nla_align alen
      end
    done;
    !res
  end

(* parse a datagram of one-or-more nlmsghdrs; return (seq, signed-error,
   ext-ack-msg) for every NLMSG_ERROR (error 0 = positive ack). *)
let parse_acks (s : string) : (int * int * string option) list =
  let n = String.length s in
  let acc = ref [] in
  let o = ref 0 in
  while !o + 16 <= n do
    let len = rd_u32 s !o in
    let typ = rd_u16 s (!o + 4) in
    let seq = rd_u32 s (!o + 8) in
    if len < 16 || !o + len > n then o := n  (* malformed; stop *)
    else begin
      if typ = nlmsg_error then begin
        let raw = rd_u32 s (!o + 16) in
        let err = if raw >= 0x80000000 then raw - 0x100000000 else raw in
        let m = if err <> 0 then ext_ack_msg s !o len else None in
        acc := (seq, err, m) :: !acc
      end;
      o := !o + nla_align len
    end
  done;
  L.rev !acc

let errno_name = function
  | 1 -> "EPERM" | 2 -> "ENOENT" | 12 -> "ENOMEM" | 16 -> "EBUSY"
  | 17 -> "EEXIST" | 22 -> "EINVAL" | 95 -> "EOPNOTSUPP" | e -> string_of_int e

(* write the batch and collect kernel acks until we've seen the BATCH_END ack
   (or an error, or a read timeout). *)
let send_bytes (buf : string) (end_seq : int) : (int * int * string option) list =
  let fd = nl_open () in
  let cleanup () = (try Unix.close fd with _ -> ()) in
  (try
     let _ = Unix.write_substring fd buf 0 (String.length buf) in
     let acc = ref [] in
     let continue = ref true in
     while !continue do
       match Unix.select [ fd ] [] [] 3.0 with
       | [], _, _ -> continue := false   (* timeout: stop *)
       | _ ->
           let b = Bytes.create 65536 in
           let r = Unix.read fd b 0 65536 in
           if r = 0 then continue := false
           else begin
             (if (try Sys.getenv "NFTC_NL_DEBUG" <> "" with Not_found -> false)
              then prerr_string (hexdump (Bytes.sub_string b 0 r)));
             let acks = parse_acks (Bytes.sub_string b 0 r) in
             acc := !acc @ acks;
             (* stop once the final batch-end ack or any error has arrived *)
             if L.exists (fun (sq, e, _) -> sq = end_seq || e <> 0) acks then
               continue := false
           end
     done;
     cleanup ();
     !acc
   with e -> cleanup (); raise e)

(* ------------------------------------------------------------------ *)
(* Exit codes (documented contract for the CLI / nl_send_test.sh):      *)
(*   4 = an instruction could not be encoded (Unsupported, raised here, *)
(*       caught in nftc_cli) ; 5 = the kernel REJECTED the batch ;      *)
(*       6 = committed but the kernel never ACKed within the timeout.   *)
(* ------------------------------------------------------------------ *)
let exit_kernel_reject = 5
let exit_no_ack        = 6

(* Send (or dry-run) a whole batch of structural+rule messages atomically.
   [desc] is a one-line human summary for the dry run. *)
let send_batch ~commit ~desc (msgs : msg list) : unit =
  let (buf, end_seq) = build_batch msgs in
  if not commit then begin
    Printf.printf
      "# DRY RUN: would send 1 NFNL batch (%s; %d object message(s), %d bytes) via NETLINK_NETFILTER\n"
      desc (L.length msgs) (String.length buf);
    print_string (hexdump buf)
  end
  else begin
    let acks = send_bytes buf end_seq in
    let failures = L.filter (fun (_, e, _) -> e <> 0) acks in
    match failures with
    | [] ->
        if acks = [] then begin
          Printf.eprintf
            "nftc: committed batch (%s) but got NO kernel ack within 3s (could not confirm)\n"
            desc;
          exit exit_no_ack
        end else
          Printf.printf "# committed batch (%s): kernel acked, no error\n" desc
    | _ ->
        L.iter
          (fun (seq, e, m) ->
            Printf.eprintf "nftc: kernel rejected batch (seq %d): error %d (%s)%s\n"
              seq (-e) (errno_name (-e))
              (match m with Some s -> " — " ^ s | None -> ""))
          failures;
        exit exit_kernel_reject
  end
