(** * Surface.Symbols: nft's symbolic-constant tables as Coq data.

    Every symbol table the UNVERIFIED frontend keeps ([extracted/nft_lower.ml]
    [sym_*], [tcpopt_num]/[tcpopt_field], [syslog_level], the reject-code
    tables, [nat_flag_bit], the ct directions) as Coq definitions — NUMERIC
    values (N), not bytes: the byte encoding of a symbol is
    [Nftval.encode (resolve_num dt n)] (Surface.Typecheck), so width and
    byteorder come from the datatype lattice, never from the table.

    Names are [dt_syms_*] / [dt_*], deliberately DISTINCT from the OCaml
    [sym_*] names, so the M-C "no symbol tables in OCaml" greps of the later
    milestones are unambiguous.

    Ground truth (cited per table): nftables src/datatype.c, src/ct.c,
    src/proto.c, src/meta.c, src/fib.c, src/icmp.c-family symbol tables at
    /tmp/nftables-src, kernel UAPI headers in
    /home/yiyun/Experiments/linux-6.18.33, and the golden corpus payloads —
    the same citations the OCaml tables carry today. *)

From Stdlib Require Import List PeanoNat Bool NArith String Ascii.
From Nft Require Import Bytes Nftval Datatype.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope N_scope.

(* ------------------------------------------------------------------ *)
(** ** The per-datatype symbol tables. *)

(** Ethertypes (ETH_P_*, linux/if_ether.h; nft src/datatype.c ethertype
    aliases + src/proto.c).  2-byte network-order values. *)
Definition dt_syms_ethertype : list (string * N) :=
  [ ("ip", 0x0800); ("ip4", 0x0800); ("ipv4", 0x0800); ("arp", 0x0806);
    ("ip6", 0x86dd); ("ipv6", 0x86dd); ("vlan", 0x8100);
    ("8021q", 0x8100); ("8021ad", 0x88a8) ].

(** IP protocol numbers (IPPROTO_*, linux/in.h; getprotobyname aliases the
    frontend accepts, e.g. `ipv6-icmp`). *)
Definition dt_syms_inet_proto : list (string * N) :=
  [ ("icmp", 1); ("igmp", 2); ("tcp", 6); ("udp", 17); ("udplite", 136);
    ("dccp", 33); ("gre", 47); ("esp", 50); ("ah", 51); ("icmpv6", 58);
    ("ipv6-icmp", 58); ("comp", 108); ("sctp", 132) ].

(** meta nfproto: the NFPROTO_* L3 family constants (linux/netfilter.h;
    datatype.c nfproto_tbl lists ipv4/ipv6, the rest are the family constants
    the frontend also accepts — see nft_lower.ml sym_nfproto's rationale). *)
Definition dt_syms_nfproto : list (string * N) :=
  [ ("inet", 1); ("ipv4", 2); ("arp", 3); ("netdev", 5);
    ("bridge", 7); ("ipv6", 10) ].

(** ct state bits (nft src/ct.c ct_state_tbl; the golden register word is the
    4-byte big-endian OR of the selected bits). *)
Definition dt_syms_ct_state : list (string * N) :=
  [ ("invalid", 0x01); ("established", 0x02); ("related", 0x04);
    ("new", 0x08); ("untracked", 0x40) ].

(** ct status bits (IPS_*, nf_conntrack_common.h; nft ct.c ct_status_tbl). *)
Definition dt_syms_ct_status : list (string * N) :=
  [ ("expected", 0x01); ("seen-reply", 0x02); ("assured", 0x04);
    ("confirmed", 0x08); ("snat", 0x10); ("dnat", 0x20); ("dying", 0x200) ].

(** TCP flag bits (proto.c TCPHDR_FIN 0x01 .. TCPHDR_CWR 0x80). *)
Definition dt_syms_tcp_flag : list (string * N) :=
  [ ("fin", 0x01); ("syn", 0x02); ("rst", 0x04); ("psh", 0x08);
    ("ack", 0x10); ("urg", 0x20); ("ecn", 0x40); ("cwr", 0x80) ].

(** ICMP types (nft src/proto.c icmp_type_tbl). *)
Definition dt_syms_icmp_type : list (string * N) :=
  [ ("echo-reply", 0); ("destination-unreachable", 3); ("source-quench", 4);
    ("redirect", 5); ("echo-request", 8); ("router-advertisement", 9);
    ("router-solicitation", 10); ("time-exceeded", 11);
    ("parameter-problem", 12); ("timestamp-request", 13);
    ("timestamp-reply", 14); ("info-request", 15); ("info-reply", 16);
    ("address-mask-request", 17); ("address-mask-reply", 18) ].

(** ICMPv6 types (nft icmpv6 type table). *)
Definition dt_syms_icmpv6_type : list (string * N) :=
  [ ("destination-unreachable", 1); ("packet-too-big", 2);
    ("time-exceeded", 3); ("parameter-problem", 4); ("echo-request", 128);
    ("echo-reply", 129); ("mld-listener-query", 130);
    ("mld-listener-report", 131); ("mld-listener-done", 132);
    ("mld-listener-reduction", 132); ("nd-router-solicit", 133);
    ("nd-router-advert", 134); ("nd-neighbor-solicit", 135);
    ("nd-neighbor-advert", 136); ("nd-redirect", 137);
    ("router-renumbering", 138); ("ind-neighbor-solicit", 141);
    ("ind-neighbor-advert", 142); ("mld2-listener-report", 143) ].

(** DSCP codepoints (6-bit raw field values: csN = 8N, afXY, ef 46, be 0,
    le 1 — RFC 2474/3246/8622; nft dscp_type symbol table). *)
Definition dt_syms_dscp : list (string * N) :=
  [ ("cs0", 0); ("cs1", 8); ("cs2", 16); ("cs3", 24); ("cs4", 32);
    ("cs5", 40); ("cs6", 48); ("cs7", 56);
    ("af11", 10); ("af12", 12); ("af13", 14); ("af21", 18); ("af22", 20);
    ("af23", 22); ("af31", 26); ("af32", 28); ("af33", 30); ("af41", 34);
    ("af42", 36); ("af43", 38); ("ef", 46); ("be", 0); ("le", 1) ].

(** IGMP message types (nft igmp.c igmp_type_tbl). *)
Definition dt_syms_igmp_type : list (string * N) :=
  [ ("membership-query", 0x11); ("membership-report-v1", 0x12);
    ("membership-report-v2", 0x16); ("leave-group", 0x17);
    ("membership-report-v3", 0x22) ].

(** ICMP code names (icmp_code_tbl). *)
Definition dt_syms_icmp_code : list (string * N) :=
  [ ("net-unreachable", 0); ("host-unreachable", 1); ("prot-unreachable", 2);
    ("port-unreachable", 3); ("frag-needed", 4); ("net-prohibited", 9);
    ("host-prohibited", 10); ("admin-prohibited", 13) ].

(** ICMPv6 code names (icmpv6_code_tbl). *)
Definition dt_syms_icmpv6_code : list (string * N) :=
  [ ("no-route", 0); ("admin-prohibited", 1); ("addr-unreachable", 3);
    ("port-unreachable", 4); ("policy-fail", 5); ("reject-route", 6) ].

(** Mobility-header types (mh.c mh_type_tbl). *)
Definition dt_syms_mh_type : list (string * N) :=
  [ ("binding-refresh-request", 0); ("home-test-init", 1);
    ("careof-test-init", 2); ("home-test", 3); ("careof-test", 4);
    ("binding-update", 5); ("binding-acknowledgement", 6);
    ("binding-error", 7); ("fast-binding-update", 8);
    ("fast-binding-acknowledgement", 9); ("fast-binding-advertisement", 10);
    ("experimental-mobility-header", 11); ("home-agent-switch-message", 12) ].

(** Packet types (PACKET_*, linux/if_packet.h; meta.c pkttype_type_tbl). *)
Definition dt_syms_pkttype : list (string * N) :=
  [ ("host", 0); ("unicast", 0); ("broadcast", 1); ("multicast", 2);
    ("other", 3); ("otherhost", 3) ].

(** ARP operation codes (ARPOP_*, linux/if_arp.h; arp.c arp_op_tbl). *)
Definition dt_syms_arp_op : list (string * N) :=
  [ ("request", 1); ("reply", 2); ("rrequest", 3); ("rreply", 4);
    ("inrequest", 8); ("inreply", 9); ("nak", 10) ].

(** /etc/services subset (same coverage as the frontend's sym_service). *)
Definition dt_syms_inet_service : list (string * N) :=
  [ ("ftp-data", 20); ("ftp", 21); ("ssh", 22); ("telnet", 23); ("smtp", 25);
    ("domain", 53); ("bootps", 67); ("bootpc", 68); ("tftp", 69);
    ("http", 80); ("www", 80); ("pop3", 110); ("ntp", 123); ("imap", 143);
    ("snmp", 161); ("bgp", 179); ("https", 443); ("submission", 587);
    ("imaps", 993); ("pop3s", 995); ("mysql", 3306); ("rdp", 3389);
    ("nfs", 2049); ("syncthing", 22000); ("wireguard", 51820);
    ("openvpn", 1194); ("http-alt", 8080); ("https-alt", 8443);
    ("domain-s", 853); ("socks", 1080); ("printer", 515); ("ipp", 631);
    ("ldap", 389); ("ldaps", 636); ("smtps", 465); ("sip", 5060);
    ("kerberos", 88); ("rsync", 873); ("irc", 6667); ("xmpp-client", 5222) ].

(** fib route types (RTN_*, linux/rtnetlink.h; fib.c addrtype_tbl).  Values
    are the plain enum codes — the HOST-endian register layout ([2;0;0;0] for
    local) is [dt_byteorder DTfib_addrtype = BoHost] + [Nftval.VFibType],
    not a table property. *)
Definition dt_syms_fib_addrtype : list (string * N) :=
  [ ("unspec", 0); ("unicast", 1); ("local", 2); ("broadcast", 3);
    ("anycast", 4); ("multicast", 5); ("blackhole", 6); ("unreachable", 7);
    ("prohibit", 8); ("throw", 9); ("nat", 10); ("xresolve", 11) ].

(** ct direction (IP_CT_DIR_ORIGINAL 0 / _REPLY 1; ct.c ct_dir_tbl). *)
Definition dt_syms_ct_dir : list (string * N) :=
  [ ("original", 0); ("reply", 1) ].

(* ------------------------------------------------------------------ *)
(** ** Symbol lookup with the evaluate.c discipline.

    A symbol is looked up in the tables of its context datatype AND the types
    on its basetype chain (expr_evaluate_symbol -> symbol_parse walks the
    basetype links); if no table knows it, the literal falls back to being
    PARSED AS AN INTEGER at the basetype ("integer-literal fallback"),
    provided the chain reaches an integer at all.  The Menhir lexer already
    tokenises numerals, so the decimal fallback fires only for symbol-typed
    trees built programmatically — kept for the discipline's completeness. *)

Definition dt_symtable (dt : dtype) : list (string * N) :=
  match dt with
  | DTethertype    => dt_syms_ethertype
  | DTinet_proto   => dt_syms_inet_proto
  | DTnfproto      => dt_syms_nfproto
  | DTct_state     => dt_syms_ct_state
  | DTct_status    => dt_syms_ct_status
  | DTtcp_flag     => dt_syms_tcp_flag
  | DTicmp_type    => dt_syms_icmp_type
  | DTicmpv6_type  => dt_syms_icmpv6_type
  | DTdscp         => dt_syms_dscp
  | DTigmp_type    => dt_syms_igmp_type
  | DTicmp_code    => dt_syms_icmp_code
  | DTicmpv6_code  => dt_syms_icmpv6_code
  | DTmh_type      => dt_syms_mh_type
  | DTpkttype      => dt_syms_pkttype
  | DTarp_op       => dt_syms_arp_op
  | DTinet_service => dt_syms_inet_service
  | DTfib_addrtype => dt_syms_fib_addrtype
  | DTct_dir       => dt_syms_ct_dir
  | _              => []
  end.

Fixpoint assoc_str {A : Type} (key : string) (tbl : list (string * A))
  : option A :=
  match tbl with
  | [] => None
  | (k, v) :: rest => if String.eqb key k then Some v else assoc_str key rest
  end.

(** Decimal digits of a symbol, as an N — the integer-literal fallback's
    parser ([None] on the empty string or any non-digit). *)
Fixpoint parse_dec_digits (cs : list nat) (acc : N) : option N :=
  match cs with
  | [] => Some acc
  | c :: rest =>
      if (48 <=? c)%nat && (c <=? 57)%nat
      then parse_dec_digits rest (acc * 10 + N.of_nat (c - 48)%nat)
      else None
  end.
Definition parse_dec (s : string) : option N :=
  match s with
  | EmptyString => None
  | _ => parse_dec_digits (Nftval.sbytes s) 0
  end.

(** [lookup_symbol dt s]: the numeric value of symbol [s] in context [dt] —
    own table first, then the chain's tables, then the basetype-integer
    fallback.  Range/width admission is NOT here: the caller re-checks the
    returned number against [dt]'s width (Typecheck.resolve_num), so a table
    can never smuggle an over-wide value past the lattice. *)
Definition lookup_symbol (dt : dtype) (s : string) : option N :=
  match
    (fix walk (chain : list dtype) : option N :=
       match chain with
       | [] => None
       | d :: rest => match assoc_str s (dt_symtable d) with
                      | Some n => Some n
                      | None => walk rest
                      end
       end) (basechain dt)
  with
  | Some n => Some n
  | None => match int_basetype dt with
            | Some _ => parse_dec s        (* integer-literal fallback *)
            | None => None
            end
  end.

(* ------------------------------------------------------------------ *)
(** ** Beyond-datatype tables (statement operands), mirrored for the later
    lowering milestones exactly as nft_lower.ml keeps them today. *)

(** TCP option kind numbers (`tcp option <name> ...`; RFC 793 + successors,
    nft tcpopt.c).  A numeric name (`tcp option 42`) parses via [parse_dec]. *)
Definition dt_tcpopt_num_tbl : list (string * N) :=
  [ ("eol", 0); ("nop", 1); ("maxseg", 2); ("mss", 2); ("window", 3);
    ("sack-perm", 4); ("sack", 5); ("sack0", 5); ("sack1", 5); ("sack2", 5);
    ("sack3", 5); ("timestamp", 8); ("md5sig", 19); ("mptcp", 30);
    ("fastopen", 34) ].
Definition dt_tcpopt_num (name : string) : option N :=
  match assoc_str name dt_tcpopt_num_tbl with
  | Some n => Some n
  | None => parse_dec name
  end.

(** Field position (off, len-bytes) within a TCP option; `left`/`right` on a
    multi-block SACK step by one 8-byte block (nft tcpopt.c templates). *)
Definition dt_tcpopt_sackn (name : string) : nat :=
  if String.eqb name "sack1" then 1
  else if String.eqb name "sack2" then 2
  else if String.eqb name "sack3" then 3
  else 0.
Definition dt_tcpopt_field (name field : string) : option (nat * nat) :=
  let sackn := dt_tcpopt_sackn name in
  if String.eqb field "kind" then Some (0, 1)%nat
  else if String.eqb field "length" then Some (1, 1)%nat
  else if String.eqb field "size" then Some (2, 2)%nat      (* maxseg size    *)
  else if String.eqb field "count" then Some (2, 1)%nat     (* window shift   *)
  else if String.eqb field "left" then Some (2 + 8 * sackn, 4)%nat
  else if String.eqb field "right" then Some (6 + 8 * sackn, 4)%nat
  else if String.eqb field "tsval" then Some (2, 4)%nat
  else if String.eqb field "tsecr" then Some (6, 4)%nat
  else None.

(** Syslog levels (`log level <name>`; syslog(3) + nft's audit extension). *)
Definition dt_syslog_level : list (string * N) :=
  [ ("emerg", 0); ("alert", 1); ("crit", 2); ("err", 3); ("warn", 4);
    ("warning", 4); ("notice", 5); ("info", 6); ("debug", 7); ("audit", 8) ].

(** Reject codes: (kernel nft_reject type, code).  Types: ICMP_UNREACH 0,
    TCP_RST 1, ICMPX_UNREACH 2 (linux/netfilter/nf_tables.h). *)
Definition dt_icmp_reject_code : list (string * N) :=
  [ ("net-unreachable", 0); ("host-unreachable", 1); ("prot-unreachable", 2);
    ("port-unreachable", 3); ("net-prohibited", 9); ("host-prohibited", 10);
    ("admin-prohibited", 13) ].
Definition dt_icmpv6_reject_code : list (string * N) :=
  [ ("no-route", 0); ("admin-prohibited", 1); ("addr-unreachable", 3);
    ("port-unreachable", 4); ("policy-fail", 5); ("reject-route", 6) ].
Definition dt_icmpx_reject_code : list (string * N) :=
  [ ("no-route", 0); ("port-unreachable", 1); ("host-unreachable", 2);
    ("admin-prohibited", 3) ].
(** Family default for a bare `reject` (evaluate.c stmt_reject_default):
    ip -> icmp port-unreach (0,3); ip6 -> icmpv6 port-unreach (0,4);
    dual/L2 -> icmpx port-unreach (2,1); `tcp reset` -> (1,0). *)
Definition dt_reject_default (family : string) : N * N :=
  if String.eqb family "ip" then (0, 3)
  else if String.eqb family "ip6" then (0, 4)
  else (2, 1).

(** NAT flag bits (NF_NAT_RANGE_*, linux/netfilter/nf_nat.h): a port range
    additionally sets PROTO_SPECIFIED 0x2 at the lowering. *)
Definition dt_nat_flag : list (string * N) :=
  [ ("random", 0x04); ("persistent", 0x08); ("fully-random", 0x10) ].

(* ------------------------------------------------------------------ *)
(** ** Non-vacuity witnesses. *)

(** The acceptance pair: `established` and 2 are the SAME ct_state number. *)
Example lookup_ct_state_established : lookup_symbol DTct_state "established" = Some 2.
Proof. reflexivity. Qed.

(** A service name in a ct_state context is REJECTED (no table on the
    ct_state chain knows it, and it is not a numeral) — `ct state https`
    is the illtyped-suite case. *)
Example lookup_ct_state_https : lookup_symbol DTct_state "https" = None.
Proof. reflexivity. Qed.

(** The same word IS a symbol in its own context. *)
Example lookup_service_https : lookup_symbol DTinet_service "https" = Some 443.
Proof. reflexivity. Qed.

(** The integer-literal fallback (evaluate.c): a numeral string parses at any
    integer-basetyped context, and does NOT parse where the chain ends at
    string (an ifname). *)
Example lookup_fallback_443 : lookup_symbol DTinet_service "443" = Some 443.
Proof. reflexivity. Qed.
Example lookup_no_fallback_ifname : lookup_symbol DTifname "443" = None.
Proof. reflexivity. Qed.

(** fib type `local` is the RTN_LOCAL code 2 (the register layout [2;0;0;0]
    is byteorder, not table, business). *)
Example lookup_fib_local : lookup_symbol DTfib_addrtype "local" = Some 2.
Proof. reflexivity. Qed.

(** Every table value fits its owning datatype's declared bit width — no
    table can smuggle an over-wide register value past the lattice.  (dscp's
    values are 6-bit codepoints, checked at 6 bits.) *)
Example tables_fit_their_dtype :
  forallb (fun dt => forallb (fun '(_, n) => n <? 2 ^ N.of_nat (dt_width dt))
                             (dt_symtable dt))
          [DTethertype; DTinet_proto; DTnfproto; DTct_state; DTct_status;
           DTtcp_flag; DTicmp_type; DTicmpv6_type; DTdscp; DTigmp_type;
           DTicmp_code; DTicmpv6_code; DTmh_type; DTpkttype; DTarp_op;
           DTinet_service; DTfib_addrtype; DTct_dir] = true.
Proof. vm_compute. reflexivity. Qed.
