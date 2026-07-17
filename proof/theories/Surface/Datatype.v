(** * Surface.Datatype: nft's datatype lattice — widths, byteorders, basetype
    coercion chains — as Coq definitions.

    This file is the Coq counterpart of the width/byteorder decisions that
    today live in the UNVERIFIED [extracted/nft_lower.ml] `kind` table
    ([width_of_kind]/[host_endian_kind]/[typed_atom]), modelled on nftables'
    own datatype table:

      ground truth   /tmp/nftables-src/src/datatype.c (the corpus checkout),
                     src/ct.c, src/meta.c, src/proto.c, src/fib.c
      register bytes the golden corpus (tests/py/*.t.payload) and IR.Nftval's
                     verified [encode] — [dt_byteorder] below describes the
                     REGISTER byte order [encode] produces, which the corpus
                     round-trip (2532/2532) pins against real nft.

    Basetype chains (datatype.c's [.basetype] links) drive nft's typing
    discipline (src/evaluate.c): symbol lookup falls back to parsing the
    literal at the basetype ("integer-literal fallback"), and cross-type
    expressions are admitted only when the types meet on a chain.  The three
    chains the TODO names are:

      ct_state      -> bitmask 4 -> integer 4        (ct.c:48-56)
      inet_service  -> integer 2, big-endian         (datatype.c:871-877)
      mark          -> integer 4, HOST-endian        (datatype.c:1031-1038)

    A NOTE on [DTinteger]/[DThostint] widths: nft's [integer_type]
    (datatype.c:487) is SIZELESS — a polymorphic literal takes the width and
    byteorder its context demands (expr_evaluate_* in evaluate.c).  We index
    the integer basetype by its context width in BYTES so the chain's endpoint
    carries exactly the width/byteorder the encoder needs; this is the
    context-instantiated view of the same discipline, not a new type system. *)

From Stdlib Require Import List PeanoNat Bool NArith String.
From Nft Require Import Bytes.
Import ListNotations.
Local Open Scope string_scope.

(* ------------------------------------------------------------------ *)
(** ** Register byte order.

    [BoBig]: the value's register bytes are network order (big-endian), or the
    type is a verbatim byte string (addresses, MAC, ifname) whose wire order IS
    its register order.  [BoHost]: the kernel stores the value as a NATIVE
    integer (BYTEORDER_HOST_ENDIAN) — little-endian on the x86/ARM64-LE hosts
    the gates run on, exactly like [Nftval.VHostInt]/[VFibType].

    Types whose register is a single byte are [BoBig] by convention (byteorder
    of one byte is degenerate); the multi-byte HOST-endian set is precisely
    {mark, ifindex, fib_addrtype} + the generic host integers — the same set
    as nft_lower.ml's [host_endian_kind] + [KNumLe]. *)
Inductive byteorder : Type := BoBig | BoHost.

Definition byteorder_eqb (a b : byteorder) : bool :=
  match a, b with BoBig, BoBig | BoHost, BoHost => true | _, _ => false end.

(* ------------------------------------------------------------------ *)
(** ** The datatype enum.

    One constructor per datatype the frontend distinguishes: nft_lower.ml's 24
    `kind`s, the declared-set type atoms ([bytes_of_typeatom]: ipv4_addr,
    ipv6_addr, ifname, iface_index, inet_service, inet_proto, ether_addr,
    mark), and the chain-interior types (bitmask, string) needed to state the
    basetype links.  Kind correspondence in each comment. *)
Inductive dtype : Type :=
| DTinteger  (w : nat)  (* KNum w:   TYPE_INTEGER at w bytes, big-endian       *)
| DThostint  (w : nat)  (* KNumLe w: integer at w bytes, HOST-endian register  *)
| DTbitmask  (w : nat)  (* TYPE_BITMASK (datatype.c:444): chain interior       *)
| DTstring              (* TYPE_STRING (datatype.c:551): chain interior        *)
| DTipv4                (* KIp4:     ipaddr_type,  32 bit BE (datatype.c:663)  *)
| DTipv6                (* KIp6:     ip6addr_type, 128 bit BE (datatype.c:729) *)
| DTether               (* ether_addr atom / arp *addr ether: etheraddr_type,
                           48 bit (proto.c:1141), basetype lladdr -> integer   *)
| DTifname              (* KIfname:  ifname_type, IFNAMSIZ*8 bit, basetype
                           STRING (meta.c:369-376) — hence NOT integer-coercible *)
| DTifindex             (* KIfindex: ifindex_type, 32 bit HOST (meta.c:151)    *)
| DTinet_service        (* KPort:    inet_service_type, 16 bit BE (datatype.c:871) *)
| DTinet_proto          (* KL4proto: inet_protocol_type, 8 bit (datatype.c:800) *)
| DTnfproto             (* KNfproto: nfproto_type, 8 bit (datatype.c:435)      *)
| DTethertype           (* KEthertype: ethertype_type, 16 bit BE (proto.c)     *)
| DTct_state            (* KCtstate: ct_state_type, 32 bit, basetype BITMASK
                           (ct.c:48-56)                                        *)
| DTct_status           (* KCtstatus: ct_status_type, 32 bit, basetype BITMASK
                           (ct.c:113-121)                                      *)
| DTct_dir              (* KCtdir:   ct direction, 8 bit enum (ct.c ct_dir_tbl) *)
| DTmark                (* KMark:    mark_type, 32 bit HOST (datatype.c:1031)  *)
| DTpkttype             (* KPkttype: pkttype_type, 8 bit (meta.c)              *)
| DTfib_addrtype        (* KFibType: fib_addr_type, 32 bit HOST (fib.c:46-54)  *)
| DTtcp_flag            (* KTcpflag: tcp_flag_type, 8 bit, basetype BITMASK
                           (proto.c:583-589)                                   *)
| DTdscp                (* dscp_type: a 6-BIT codepoint (proto.c) — the raw
                           value of the `ip dscp` sub-byte bitfield            *)
| DTtime                (* time_type (datatype.c time_type): a duration whose
                           surface literal is in SECONDS but whose kernel
                           register is MILLISECONDS, HOST-endian 32 bit — nft's
                           time_parse scales *1000, matching the kernel's
                           jiffies_to_msecs store (net/netfilter/nft_ct.c
                           nft_ct_get_eval NFT_CT_EXPIRATION).  Carried by
                           `ct expiration`.                                    *)
| DTicmp_type           (* KIcmp:     icmp_type_type, 8 bit                    *)
| DTicmp_code           (* KIcmpcode: icmp_code_type, 8 bit                    *)
| DTicmpv6_type         (* KIcmpv6:   icmp6_type_type, 8 bit                   *)
| DTicmpv6_code         (* KIcmp6code: icmpv6_code_type, 8 bit                 *)
| DTigmp_type           (* KIgmp:     igmp_type_type, 8 bit                    *)
| DTmh_type             (* KMhtype:   mh_type_type, 8 bit                      *)
| DTarp_op.             (* KArpop:    arpop_type, 16 bit network order (arp.c) *)

(** Lower-case abbreviations, so gates/tests and later milestones can name
    dtypes without touching constructor spelling. *)
Definition dt_integer (w : nat) : dtype := DTinteger w.
Definition dt_hostint (w : nat) : dtype := DThostint w.
Definition dt_ipv4 : dtype := DTipv4.
Definition dt_ipv6 : dtype := DTipv6.
Definition dt_ether : dtype := DTether.
Definition dt_ifname : dtype := DTifname.
Definition dt_ifindex : dtype := DTifindex.
Definition dt_inet_service : dtype := DTinet_service.
Definition dt_inet_proto : dtype := DTinet_proto.
Definition dt_nfproto : dtype := DTnfproto.
Definition dt_ethertype : dtype := DTethertype.
Definition dt_ct_state : dtype := DTct_state.
Definition dt_ct_status : dtype := DTct_status.
Definition dt_ct_dir : dtype := DTct_dir.
Definition dt_mark : dtype := DTmark.
Definition dt_pkttype : dtype := DTpkttype.
Definition dt_fib_addrtype : dtype := DTfib_addrtype.
Definition dt_tcp_flag : dtype := DTtcp_flag.
Definition dt_dscp : dtype := DTdscp.

Definition dtype_eqb (a b : dtype) : bool :=
  match a, b with
  | DTinteger w1, DTinteger w2 => Nat.eqb w1 w2
  | DThostint w1, DThostint w2 => Nat.eqb w1 w2
  | DTbitmask w1, DTbitmask w2 => Nat.eqb w1 w2
  | DTstring, DTstring | DTipv4, DTipv4 | DTipv6, DTipv6
  | DTether, DTether | DTifname, DTifname | DTifindex, DTifindex
  | DTinet_service, DTinet_service | DTinet_proto, DTinet_proto
  | DTnfproto, DTnfproto | DTethertype, DTethertype
  | DTct_state, DTct_state | DTct_status, DTct_status | DTct_dir, DTct_dir
  | DTmark, DTmark | DTpkttype, DTpkttype
  | DTfib_addrtype, DTfib_addrtype | DTtcp_flag, DTtcp_flag | DTdscp, DTdscp
  | DTtime, DTtime
  | DTicmp_type, DTicmp_type | DTicmp_code, DTicmp_code
  | DTicmpv6_type, DTicmpv6_type | DTicmpv6_code, DTicmpv6_code
  | DTigmp_type, DTigmp_type | DTmh_type, DTmh_type | DTarp_op, DTarp_op => true
  | _, _ => false
  end.

Lemma dtype_eqb_eq : forall a b, dtype_eqb a b = true <-> a = b.
Proof.
  destruct a, b; simpl; split; intro H;
    try discriminate; try reflexivity;
    try (apply Nat.eqb_eq in H; subst; reflexivity);
    try (injection H as ->; apply Nat.eqb_refl).
Qed.

Lemma dtype_eqb_refl : forall a, dtype_eqb a a = true.
Proof. intro a. apply dtype_eqb_eq. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(** ** Width (bits) and register width (bytes).

    [dt_width] is the datatype's declared size in BITS (matching datatype.c's
    [.size] fields); [dt_bytes] the register byte width the encoder uses —
    [dt_width/8] rounded up, so the sole sub-byte type ([DTdscp], 6 bits)
    still occupies its 1-byte register before the bitfield shift. *)
Definition dt_width (dt : dtype) : nat :=
  match dt with
  | DTinteger w | DThostint w | DTbitmask w => 8 * w
  | DTstring        => 0     (* variable: string_type carries no .size        *)
  | DTipv4          => 32
  | DTipv6          => 128
  | DTether         => 48
  | DTifname        => 128   (* IFNAMSIZ(16) * 8 (meta.c:374)                 *)
  | DTifindex       => 32
  | DTinet_service  => 16
  | DTinet_proto    => 8
  | DTnfproto       => 8
  | DTethertype     => 16
  | DTct_state      => 32
  | DTct_status     => 32
  | DTct_dir        => 8
  | DTmark          => 32
  | DTpkttype       => 8
  | DTfib_addrtype  => 32
  | DTtcp_flag      => 8
  | DTdscp          => 6     (* the one sub-byte datatype (proto.c dscp_type) *)
  | DTtime          => 32    (* ct expiration register: 4-byte ms, host-order *)
  | DTicmp_type | DTicmp_code | DTicmpv6_type | DTicmpv6_code
  | DTigmp_type | DTmh_type => 8
  | DTarp_op        => 16
  end.

Definition dt_bytes (dt : dtype) : nat := Nat.div (dt_width dt + 7) 8.

(** The register byte order of [Nftval.encode] for this datatype's values.
    HOST-endian exactly for the [VHostInt]/[VFibType]-encoded set: the generic
    host integers, mark, ifindex, fib_addrtype (nft_lower.ml [host_endian_kind]
    + [KNumLe]; kernel: BYTEORDER_HOST_ENDIAN in meta.c:155/datatype.c:1037/
    fib.c:50).  NOTE for the auditor: datatype.c also declares ct_state/
    ct_status BYTEORDER_HOST_ENDIAN — that is the byteorder of nft's INTERNAL
    mpz constant; the netlink register bytes the golden corpus pins (e.g.
    `ct state established` compares [0;0;0;2]) are the 4-byte big-endian word,
    which is what [Nftval.VCtState] encodes and what this function reports. *)
Definition dt_byteorder (dt : dtype) : byteorder :=
  match dt with
  | DThostint _ | DTmark | DTifindex | DTfib_addrtype | DTtime => BoHost
  | _ => BoBig
  end.

(* ------------------------------------------------------------------ *)
(** ** Basetype chains (datatype.c's [.basetype] links). *)
Definition basetype_of (dt : dtype) : option dtype :=
  match dt with
  | DTinteger _ => None                       (* the chain's endpoint          *)
  | DThostint w => Some (DTinteger w)         (* byteorder_conversion admits
                                                 host<->BE integers (evaluate.c) *)
  | DTbitmask w => Some (DTinteger w)         (* datatype.c:449                *)
  | DTstring    => None
  | DTipv4      => Some (DTinteger 4)         (* datatype.c:669                *)
  | DTipv6      => Some (DTinteger 16)        (* datatype.c:735                *)
  | DTether     => Some (DTinteger 6)         (* etheraddr -> lladdr -> integer
                                                 (proto.c:1147, datatype.c:606);
                                                 lladdr is width-polymorphic so
                                                 it is elided from the chain   *)
  | DTifname    => Some DTstring              (* meta.c:375 — a STRING, so an
                                                 ifname is NOT integer-coercible:
                                                 `iifname & 0xff` is ill-typed *)
  | DTifindex   => Some (DThostint 4)         (* meta.c:157 + HOST byteorder   *)
  | DTinet_service => Some (DTinteger 2)      (* datatype.c:877 + BIG_ENDIAN   *)
  | DTinet_proto   => Some (DTinteger 1)      (* datatype.c:805                *)
  | DTnfproto      => Some (DTinteger 1)      (* datatype.c:440                *)
  | DTethertype    => Some (DTinteger 2)
  | DTct_state     => Some (DTbitmask 4)      (* ct.c:54                       *)
  | DTct_status    => Some (DTbitmask 4)      (* ct.c:119                      *)
  | DTct_dir       => Some (DTinteger 1)      (* ct.c:85                       *)
  | DTmark         => Some (DThostint 4)      (* datatype.c:1038 + HOST        *)
  | DTpkttype      => Some (DTinteger 1)
  | DTfib_addrtype => Some (DThostint 4)      (* fib.c:52 + HOST               *)
  | DTtcp_flag     => Some (DTbitmask 1)      (* proto.c:589                   *)
  | DTdscp         => Some (DTinteger 1)
  | DTtime         => Some (DThostint 4)      (* time_type -> host integer 4  *)
  | DTicmp_type | DTicmp_code | DTicmpv6_type | DTicmpv6_code
  | DTigmp_type | DTmh_type => Some (DTinteger 1)
  | DTarp_op       => Some (DTinteger 2)
  end.

(** The chain from [dt] to its root (self first).  The longest real chain is
    ct_state -> bitmask -> integer (3 types); ifname -> string (2); fuel 4
    strictly dominates every [basetype_of] chain. *)
Fixpoint basechain_from (fuel : nat) (dt : dtype) : list dtype :=
  match fuel with
  | O => []
  | S k => dt :: match basetype_of dt with
                 | Some b => basechain_from k b
                 | None => []
                 end
  end.
Definition basechain (dt : dtype) : list dtype := basechain_from 4 dt.

(** [coercible a b]: [b] lies on [a]'s basetype chain (reflexive-transitive
    walk).  This is the admissibility test evaluate.c applies when two typed
    expressions meet (a set reference against a selector, a symbol against its
    context). *)
Definition coercible (a b : dtype) : bool :=
  existsb (dtype_eqb b) (basechain a).

Lemma coercible_refl : forall dt, coercible dt dt = true.
Proof.
  intro dt. unfold coercible, basechain. simpl basechain_from.
  destruct (basetype_of dt); simpl; rewrite dtype_eqb_refl; reflexivity.
Qed.

(** Two dtypes are COMPATIBLE when either reaches the other on its chain —
    the symmetric closure used for set-reference admission (`ip daddr @set`
    checks the selector's dtype against the set's declared dtype). *)
Definition dt_compat (a b : dtype) : bool := coercible a b || coercible b a.

(** [int_basetype dt]: the first integer-shaped type on [dt]'s chain, with its
    width (bytes) and byteorder — [None] when the chain never reaches an
    integer (string-based types).  This is what "basetype-integer fallback"
    parses a literal AT: `ct state 2` reads 2 at (4, big-endian) through
    ct_state -> bitmask 4 -> integer 4; `mark 0x99` reads at (4, host). *)
Fixpoint int_basetype_from (fuel : nat) (dt : dtype) : option (nat * byteorder) :=
  match fuel with
  | O => None
  | S k =>
      match dt with
      | DTinteger w => Some (w, BoBig)
      | DThostint w => Some (w, BoHost)
      | _ => match basetype_of dt with
             | Some b => int_basetype_from k b
             | None => None
             end
      end
  end.
Definition int_basetype (dt : dtype) : option (nat * byteorder) :=
  int_basetype_from 4 dt.

(* ------------------------------------------------------------------ *)
(** ** Polymorphic integer literals.

    [numeric_dtype dt]: the datatype admits an integer-literal SPELLING in the
    frontend.  This is [int_basetype] minus the address/link-layer types,
    whose literals are dedicated LEXICAL forms (dotted quad, colon-hex MAC) —
    the grammar never delivers them as integers, and the frontend's
    [typed_atom] rejects a numeric IP/MAC (nft itself would basetype-parse
    them; carrying that leniency adds an encode path no ruleset exercises, so
    the checker refuses it — fail-loud, cf. M-A). *)
Definition numeric_dtype (dt : dtype) : bool :=
  match dt with
  | DTipv4 | DTipv6 | DTether | DTifname | DTstring => false
  | DTbitmask _ => false     (* chain-interior: no surface spelling *)
  | _ => match int_basetype dt with Some _ => true | None => false end
  end.

(** [lit_fits n dt]: the polymorphic literal [n] fits [dt]'s declared BIT
    width.  Bit-precise so the 6-bit [DTdscp] admits 0..63 only — nft rejects
    `ip dscp 64` ("Value 64 exceeds valid range 0-63"); byte-masking it (the
    OCaml [typed_atom] `land 0xff` habit) would silently corrupt.  *)
Definition lit_fits (n : nat) (dt : dtype) : bool :=
  numeric_dtype dt &&
  match dt with
  | DTtime => (N.of_nat n * 1000 <? 256 ^ 4)%N   (* the SCALED ms value fits  *)
  | _ => (N.of_nat n <? 2 ^ N.of_nat (dt_width dt))%N
  end.

(* ------------------------------------------------------------------ *)
(** ** Non-vacuity witnesses (the lattice is a real restriction). *)

(** The three TODO chains, verbatim. *)
Example chain_ct_state :
  basechain DTct_state = [DTct_state; DTbitmask 4; DTinteger 4].
Proof. reflexivity. Qed.
Example chain_inet_service :
  basechain DTinet_service = [DTinet_service; DTinteger 2]
  /\ dt_byteorder DTinet_service = BoBig.
Proof. split; reflexivity. Qed.
Example chain_mark :
  basechain DTmark = [DTmark; DThostint 4; DTinteger 4]
  /\ dt_byteorder DTmark = BoHost.
Proof. split; reflexivity. Qed.

(** ifname bottoms out at STRING: no integer basetype, so bitwise arithmetic
    over an ifname is ill-typed (the `iifname & 0xff` rejection's root). *)
Example ifname_not_integer : int_basetype DTifname = None.
Proof. reflexivity. Qed.
Example mark_is_host_integer : int_basetype DTmark = Some (4, BoHost).
Proof. reflexivity. Qed.

(** [coercible] is not the full relation: an ifname does not coerce to an
    integer, and an integer does not coerce to ct_state (chains are directed). *)
Example not_coercible_ifname_int : coercible DTifname (DTinteger 4) = false.
Proof. reflexivity. Qed.
Example not_coercible_int_ctstate : coercible (DTinteger 4) DTct_state = false.
Proof. reflexivity. Qed.
Example coercible_ctstate_int : coercible DTct_state (DTinteger 4) = true.
Proof. reflexivity. Qed.

(** [lit_fits] is bit-precise (64 does not fit the 6-bit dscp; 63 does;
    300 does not fit the 8-bit inet_proto). *)
Example lit_fits_dscp_63 : lit_fits 63 DTdscp = true.
Proof. reflexivity. Qed.
Example lit_fits_dscp_64 : lit_fits 64 DTdscp = false.
Proof. reflexivity. Qed.
Example lit_fits_proto_300 : lit_fits 300 DTinet_proto = false.
Proof. reflexivity. Qed.
