(* Nl_send — transmit a VERIFIED-compiled chain to the kernel over real netlink.

   The bytes this builds are a 1:1 serialisation of the verified
   [Compile.compile_chain] output (a [Bytecode.program] = list of instruction
   lists): each rule's instruction list is encoded, instruction by instruction,
   into the kernel's NFTA_RULE_EXPRESSIONS nlattr form, with the compiler's
   register numbers sent VERBATIM (the compiler's [reg_of_slot] already matches
   nft's NFT_REG_* / NFT_REG32_* numbering — see Compile.v).  The sender NEVER
   re-derives rules from the DSL; it only encodes what compile_chain produced.

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

(* nfnetlink batch + subsystem *)
let nfnl_subsys_nftables = 10
let nfnl_msg_batch_begin = 16   (* NLMSG_MIN_TYPE *)
let nfnl_msg_batch_end   = 17

(* nf_tables message types (low byte; high byte = subsys) *)
let nft_msg_newrule = 6
let newrule_type    = (nfnl_subsys_nftables lsl 8) lor nft_msg_newrule

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
let nfta_verdict_code = 1

(* registers *)
let nft_reg_verdict = 0

(* meta (per <nf_tables.h>: UNSPEC=0, DREG=1, KEY=2, SREG=3) *)
let nfta_meta_dreg = 1
let nfta_meta_key  = 2

(* payload *)
let nfta_payload_dreg   = 1
let nfta_payload_base   = 2
let nfta_payload_offset = 3
let nfta_payload_len    = 4

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
let nfta_lookup_flags = 4
let nft_lookup_f_inv  = 1

(* bitwise *)
let nfta_bitwise_sreg = 1
let nfta_bitwise_dreg = 2
let nfta_bitwise_len  = 3
let nfta_bitwise_mask = 4
let nfta_bitwise_xor  = 5

(* netfilter base verdicts / nft pseudo-verdicts (as 32-bit two's complement) *)
let nf_drop      = 0
let nf_accept    = 1
let nft_continue = -1
let nft_return   = -5

(* nfproto (nfgenmsg.nfgen_family) — default IPv4 for `ip` tables; the CLI
   loses the parsed family before reaching us, so this is a documented default
   overridable via the optional [?family] argument. *)
let nfproto_ipv4 = 2

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

let attr_u32 typ v       = attr typ (be32 v)
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
  | Bytecode.INat _ -> "INat"             | Bytecode.ILimit _ -> "ILimit"
  | Bytecode.ICounter _ -> "ICounter"     | Bytecode.INotrack -> "INotrack"
  | Bytecode.ILog _ -> "ILog"             | Bytecode.IReject _ -> "IReject"
  | Bytecode.IQueue _ -> "IQueue"         | Bytecode.IImmediate _ -> "IImmediate"

(* verdict code for an immediate verdict (reg 0); chain-targeting and the
   reject/queue-as-immediate cases need extra attrs we don't emit -> Unsupported *)
let verdict_code (v : Verdict.verdict) : int = match v with
  | Verdict.Accept   -> nf_accept
  | Verdict.Drop     -> nf_drop
  | Verdict.Continue -> nft_continue
  | Verdict.Return   -> nft_return
  | Verdict.Jump _   -> raise (Unsupported "IImmediate(Jump): needs NFTA_VERDICT_CHAIN")
  | Verdict.Goto _   -> raise (Unsupported "IImmediate(Goto): needs NFTA_VERDICT_CHAIN")
  | Verdict.Reject _ -> raise (Unsupported "IImmediate(Reject)")
  | Verdict.Queue _  -> raise (Unsupported "IImmediate(Queue)")

let encode_instr (ins : Bytecode.instr) : string * string =
  match ins with
  | Bytecode.IMetaLoad (k, r) ->
      ("meta",
       attr_u32 nfta_meta_dreg r ^ attr_u32 nfta_meta_key (nl_meta_key k))
  | Bytecode.IPayloadLoad (b, off, len, r) ->
      ("payload",
       attr_u32 nfta_payload_dreg r
       ^ attr_u32 nfta_payload_base (nl_pbase b)
       ^ attr_u32 nfta_payload_offset off
       ^ attr_u32 nfta_payload_len len)
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
      let vbody = attr_nested nfta_data_verdict (attr_u32 nfta_verdict_code (verdict_code v)) in
      ("immediate",
       attr_u32 nfta_immediate_dreg nft_reg_verdict
       ^ attr_nested nfta_immediate_data vbody)
  | Bytecode.IImmediateData (dst, v) ->
      ("immediate",
       attr_u32 nfta_immediate_dreg dst
       ^ attr_nested nfta_immediate_data (attr_data_value v))
  | Bytecode.ILookup (srcs, name, neg) ->
      let sreg = match srcs with x :: _ -> x | [] -> 1 in
      let base =
        attr_str nfta_lookup_set name ^ attr_u32 nfta_lookup_sreg sreg in
      ("lookup",
       if neg then base ^ attr_u32 nfta_lookup_flags nft_lookup_f_inv else base)
  | Bytecode.IBitwise (dst, src, mask, xor) ->
      ("bitwise",
       attr_u32 nfta_bitwise_sreg src
       ^ attr_u32 nfta_bitwise_dreg dst
       ^ attr_u32 nfta_bitwise_len (L.length mask)
       ^ attr_nested nfta_bitwise_mask (attr_data_value mask)
       ^ attr_nested nfta_bitwise_xor (attr_data_value xor))
  | other -> raise (Unsupported (instr_name other))

(* one NFTA_LIST_ELEM = nested { NFTA_EXPR_NAME=string, NFTA_EXPR_DATA=nested } *)
let encode_elem (ins : Bytecode.instr) : string =
  let (name, data) = encode_instr ins in
  attr_nested nfta_list_elem
    (attr_str nfta_expr_name name ^ attr_nested nfta_expr_data data)

let encode_exprs (rp : Bytecode.rule_prog) : string =
  String.concat "" (L.map encode_elem rp)

(* ------------------------------------------------------------------ *)
(* Whole NFNL batch: BEGIN ; NEWRULE* ; END.  Returns (bytes, end_seq). *)
(* ------------------------------------------------------------------ *)

let build_batch ~family ~table ~chain (prog : Bytecode.program)
  : string * int =
  let seq = ref 0 in
  let next () = incr seq; !seq in
  let begin_msg =
    nlmsg ~typ:nfnl_msg_batch_begin
      ~flags:(nlm_f_request lor nlm_f_ack) ~seq:(next ())
      (nfgenmsg ~family:0 ~res_id:nfnl_subsys_nftables) in
  let rule_msgs =
    L.map
      (fun rp ->
        let payload =
          nfgenmsg ~family ~res_id:0
          ^ attr_str nfta_rule_table table
          ^ attr_str nfta_rule_chain chain
          ^ attr_nested nfta_rule_expressions (encode_exprs rp) in
        nlmsg ~typ:newrule_type
          ~flags:(nlm_f_request lor nlm_f_create lor nlm_f_append lor nlm_f_ack)
          ~seq:(next ()) payload)
      prog in
  let end_seq = next () in
  let end_msg =
    nlmsg ~typ:nfnl_msg_batch_end
      ~flags:(nlm_f_request lor nlm_f_ack) ~seq:end_seq
      (nfgenmsg ~family:0 ~res_id:nfnl_subsys_nftables) in
  (String.concat "" (begin_msg :: rule_msgs @ [ end_msg ]), end_seq)

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

(* parse a datagram of one-or-more nlmsghdrs; return (seq, signed-error) for
   every NLMSG_ERROR (error 0 = positive ack). *)
let parse_acks (s : string) : (int * int) list =
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
        acc := (seq, err) :: !acc
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
let send_bytes (buf : string) (end_seq : int) : (int * int) list =
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
             let acks = parse_acks (Bytes.sub_string b 0 r) in
             acc := !acc @ acks;
             (* stop once the final batch-end ack or any error has arrived *)
             if L.exists (fun (sq, e) -> sq = end_seq || e <> 0) acks then
               continue := false
           end
     done;
     cleanup ();
     !acc
   with e -> cleanup (); raise e)

(* ------------------------------------------------------------------ *)
(* Public entry point (signature compatible with nftc_cli.ml).          *)
(*   ?family defaults to NFPROTO_IPV4 (the `ip` family) since the CLI    *)
(*   drops the parsed address family before calling us.                 *)
(* ------------------------------------------------------------------ *)

let send_chain ?(family = nfproto_ipv4) ~table ~chain ~commit
    (prog : Bytecode.program) : unit =
  let (buf, end_seq) = build_batch ~family ~table ~chain prog in
  if not commit then begin
    Printf.printf
      "# DRY RUN: would send NFNL batch -> table %s chain %s (%d rule(s), %d bytes) via NETLINK_NETFILTER\n"
      table chain (L.length prog) (String.length buf);
    L.iteri
      (fun i rp ->
        Printf.printf "#  rule %d:\n" i;
        L.iter (fun ins -> Printf.printf "#    %s\n" (Codec.render_instr ins)) rp)
      prog;
    print_string (hexdump buf)
  end
  else begin
    let acks = send_bytes buf end_seq in
    let failures = L.filter (fun (_, e) -> e <> 0) acks in
    match failures with
    | [] ->
        if acks = [] then
          Printf.eprintf
            "nftc: sent %d rule(s) to %s/%s but got NO kernel ack within 3s (could not confirm)\n"
            (L.length prog) table chain
        else
          Printf.printf "# committed %d rule(s) to %s/%s (kernel acked, no error)\n"
            (L.length prog) table chain
    | _ ->
        L.iter
          (fun (seq, e) ->
            Printf.eprintf "nftc: kernel rejected batch (seq %d): error %d (%s)\n"
              seq (-e) (errno_name (-e)))
          failures;
        exit 5
  end
