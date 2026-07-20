(** * Surface.Lower: the VERIFIED scalar-match lowering (M2).

    [lower_match] consumes the M1 surface AST (one selector key path + its
    right-hand side, defines already expanded) and produces the TYPED term
    ([Typed.txmatch]) whose verified elaboration [Typed.elab_tx] is the byte
    IR the compiler consumes.  With this file the OCaml frontend stops
    constructing byte-level match conditions for every SCALAR shape:

      - typed atoms (eq / neq), CIDR prefixes, ifname wildcards
        (the four M0 scalar shapes, BUILT here instead of in OCaml);
      - inclusive ranges — plain big-endian, and the mark/ifindex/fib-type
        `byteorder hton` ranges;
      - bitmask forms (ct state / ct status / tcp flags): the 4-operator
        dispatch, single values and bare comma OR-lists;
      - sub-byte bitfields (ip dscp / ip6 flowlabel / tcp doff / vlan / frag),
        mask and shifted compare value COMPUTED from Selector.v's numeric
        bit specs;
      - fib / exthdr / tcp-option presence tests;
      - explicit bitwise matches (`<sel> and|or|xor <mask> <op> <v>`,
        [lower_bitmatch]);
      - implicit protocol-dependency guards: [dep_guard] encodes the guard
        VALUE (family-aware: inet nfproto vs L2 `meta protocol` ethertype vs
        single-L3 no-op), and [discharge] computes which pending guards an
        explicit match satisfies.

    Dispatch ORDER and admission mirror extracted/nft_lower.ml's historical
    lowering byte-for-byte (the golden corpus, byteorder-gate and difftest
    pin the bytes end-to-end); where this lowering is STRICTER, nft itself
    refuses the input too, and each case fails LOUD with an [lerr] — never a
    silent OCaml byte fallback (mandate M-A).  Set-shaped right-hand sides
    (brace sets, @references, concatenations) are the M3 milestone and are
    routed by the driver to the untyped set path; if one reaches this
    lowering it is an [lerr], not a guess.

    Typing discipline: every operand resolves through
    [Typecheck.resolve_value] (symbol tables walking the basetype chain with
    the integer-literal fallback), so `ct state 2` and `ct state established`
    lower to the IDENTICAL typed term, and anything the M1 checker rejects
    (width overflow, cross-type operands, `iifname & 0xff`) cannot lower. *)

From Stdlib Require Import List PeanoNat Bool NArith String Ascii.
From Nft Require Import Bytes Packet Verdict Bytecode Syntax Nftval
  Ast Datatype Symbols Selector Typecheck Typed.
Import ListNotations.
Local Open Scope string_scope.

(* ------------------------------------------------------------------ *)
(** ** Fail-loud errors (the scalar slice of nft_lower.ml's refusal list). *)

Inductive lerr : Type :=
| LEnotScalar                    (* concatenated keys: the set path (M3)     *)
| LEsetShaped                    (* set/ref rhs mis-routed to the scalar path *)
| LEselector   (kp : skeypath)   (* unknown selector key path                *)
| LEatom       (ctx : string)    (* value does not resolve at the selector's
                                    datatype (unknown symbol / spelling /
                                    width overflow / unresolved $var)        *)
| LEcommaNonBitmask              (* bare comma list over a non-bitmask type  *)
| LEbitfieldRhs (ctx : string)   (* set/range/symbol over a sub-byte bitfield *)
| LEbitfieldRange (ctx : string) (* bitfield value exceeds the field's bits  *)
| LEprefixLen                    (* CIDR length exceeds the field width      *)
| LEexthdr     (proto : string)  (* unknown IPv6 extension header            *)
| LEtcpopt     (name : string)   (* unknown TCP option                       *)
| LEbitwiseNonInteger            (* bitwise over a non-integer-basetype
                                    selector — the `iifname & 0xff` rejection *)
| LEbitwiseOp  (op : string)     (* unknown bitwise operator                 *)
| LEbitwiseRhs                   (* bitwise rhs is not a single value        *)
| LEvlanNetdev                   (* vlan match in netdev family (iiftype
                                    guard byte-order — honest refusal)       *)
| LEtcpflagSet                   (* tcp flags brace-set (brace-vs-OR ambiguity) *)
| LEconcatArity                  (* concat element arity <> declared key      *)
| LEsettype    (atom : string)   (* unknown declared set type atom            *)
(* --- M4: the statement / terminal / driver slice of the refusal list --- *)
| LEundefVar   (name : string)   (* `$name` with no `define`                  *)
| LEmetaSet    (name : string)   (* `meta <k> set` on an unsettable/unknown key *)
| LEctSet      (name : string)   (* `ct <k> set` on an unsettable/unknown key  *)
| LEnatFlag    (name : string)   (* unknown NAT flag word                      *)
| LEtproxyTarget                 (* tproxy target is not an IPv4 literal       *)
| LEreject     (ctx : string)    (* unknown `reject with ...` type/code        *)
| LElimitUnit  (name : string)   (* unknown `limit ... /<unit>`                *)
| LEmultiVmap                    (* more than one verdict map in a rule        *)
| LEvmapStatic                   (* verdict map combined with a static verdict *)
| LEmultiOutcome                 (* >1 terminal outcome (vmap / nat / tproxy)  *)
| LEvalueMap                     (* value map (non-verdict data) not lowered   *)
| LEconcatRhs                    (* concatenated match without a set/ref rhs   *)
| LEhook       (name : string)   (* base chain bound to an unknown netfilter hook *)
| LEnumgen.                      (* incremental `numgen` (no source surface; the
                                    mutation strand's VM-side counter sweep has no
                                    DSL twin, so such a rule is refused instead of
                                    silently leaving the verified domain) *)

Definition lerr_message (e : lerr) : string :=
  match e with
  | LEnotScalar => "internal: concatenated match reached the scalar lowering"
  | LEsetShaped => "internal: set-shaped rhs reached the scalar lowering"
  | LEselector kp => "selector: " ++ String.concat " " kp
  | LEatom ctx => "value does not type at its selector (" ++ ctx ++ ")"
  | LEcommaNonBitmask =>
      "comma list rhs is only valid for bitmask selectors (ct state / tcp flags); use a `{ ... }` set instead"
  | LEbitfieldRhs ctx => "bitfield selector value: " ++ ctx
  | LEbitfieldRange ctx => "bitfield value exceeds the field's bit width: " ++ ctx
  | LEprefixLen => "prefix length exceeds the field width"
  | LEexthdr p => "exthdr " ++ p
  | LEtcpopt n => "tcp option " ++ n
  | LEbitwiseNonInteger =>
      "bitwise mask over a selector with no integer basetype"
  | LEbitwiseOp op => "bitwise op " ++ op
  | LEbitwiseRhs => "bitwise mask match needs a single-value rhs"
  | LEvlanNetdev => "vlan match in netdev family (iiftype guard byte-order)"
  | LEtcpflagSet =>
      "tcp flags set/list form is ambiguous (brace-set vs OR-mask); use a single `tcp flags X` / `tcp flags ! X` / `tcp flags == X`"
  | LEconcatArity => "concatenated element arity does not match the declared key"
  | LEsettype a => "set element type: " ++ a
  | LEundefVar n => "undefined variable $" ++ n
  | LEmetaSet n => "meta key is not settable: " ++ n
  | LEctSet n => "ct key is not settable: " ++ n
  | LEnatFlag n => "nat flag " ++ n
  | LEtproxyTarget => "tproxy target is not an IPv4 literal"
  | LEreject c => "reject with " ++ c
  | LElimitUnit n => "limit unit " ++ n
  | LEmultiVmap => "more than one verdict map in a rule"
  | LEvmapStatic => "verdict map combined with a static verdict"
  | LEmultiOutcome => "rule with more than one outcome (vmap/nat/tproxy)"
  | LEvalueMap => "value maps (non-verdict map data) not yet lowered"
  | LEconcatRhs => "concatenated match needs a set/ref rhs"
  | LEhook n => "base chain bound to an unknown netfilter hook: " ++ n
  | LEnumgen => "incremental numgen has no source surface (rule refused)"
  end.

Inductive lres (A : Type) : Type :=
| LOk  (a : A)
| LErr (e : lerr).
Arguments LOk  {A}.
Arguments LErr {A}.

(* ------------------------------------------------------------------ *)
(** ** Implicit-dependency guard encoding ([dep_guard]) and discharge.

    nft inserts implicit protocol guards before a load (payload.c
    payload_gen_dependency); WHICH guard (and whether any) depends on the
    chain's FAMILY: `meta nfproto` in inet, `meta protocol == <ethertype>` in
    the L2 families (bridge/netdev), nothing in a single-L3 family (ip/ip6/
    arp).  The guard's register VALUE is encoded here, in Coq, from the
    numeric [Selector.depspec]; the per-rule dedup STATE (nft emits one
    network-layer guard per rule, and value-keyed guards once) stays a driver
    loop over the [(field, key)] pairs this function returns. *)

Inductive dep_action : Type :=
| DAnone
| DAguard (layer_keyed : bool) (f : field) (key : data) (tm : txmatch).
(* [layer_keyed]: dedup by FIELD alone (one network-layer guard per rule,
   whatever the value — golden inet/icmp.t.payload emits nfproto ONCE for
   `meta nfproto ipv4 icmpv6 type ...`); otherwise dedup by (field, value). *)

Definition guard (layer : bool) (f : field) (w : nat) (n : N) : dep_action :=
  DAguard layer f (N_to_data w n) (TXEq f (VInteger w n)).

(** A guard whose register is HOST-endian (little-endian immediate): `meta
    iiftype` is BYTEORDER_HOST_ENDIAN (nft src/meta.c arphrd_type / the
    NFT_META_IIFTYPE template), so `meta iiftype == ARPHRD_ETHER` must compare a
    host-order immediate ([1;0] for value 1) — a big-endian [0;1] would read as
    256 and the guard would wrongly BREAK on real ethernet (it only happened to
    break correctly on non-ethernet devices because neither value equals the
    device's iiftype).  [Nftval.encode (VHostInt w n)] is the little-endian
    register encoding. *)
Definition guard_host (layer : bool) (f : field) (w : nat) (n : N) : dep_action :=
  DAguard layer f (Nftval.encode (VHostInt w n)) (TXEq f (VHostInt w n)).

(** The L2 families pin an ip/ip6 network match by the LINK-layer ethertype
    (`meta protocol ==`) instead of the NFPROTO guard: IPv4 (2) -> 0x0800,
    IPv6 (10) -> 0x86dd (golden arp.t.payload.netdev / bridge payloads). *)
Definition nfproto_ethertype (fam : nat) : option N :=
  if Nat.eqb fam 2 then Some 0x0800%N
  else if Nat.eqb fam 10 then Some 0x86dd%N
  else None.

Definition family_is_inet (fam : string) : bool := String.eqb fam "inet".
Definition family_is_l2 (fam : string) : bool :=
  String.eqb fam "bridge" || String.eqb fam "netdev".

(** The in-frame-ethertype network guard `payload load 2b @ link header + off`:
    proto_eth (bridge LL) and proto_vlan carry a PAYLOAD protocol_key template
    (no meta_key), so their next-protocol dependency reads the ethertype out of
    the frame rather than off `skb->protocol` (src/proto.c proto_eth.protocol_key
    = ETHHDR_TYPE @ 12, proto_vlan.protocol_key = VLANHDR_TYPE @ 16).  The read
    differs from `meta protocol` on vlan-tagged frames, where nft_payload pretends
    the tag was not offloaded (net/netfilter/nft_payload.c nft_payload_copy_vlan). *)
Definition net_ll_guard (off : nat) (et : N) : dep_action :=
  DAguard true (FPayload PLink off 2) (N_to_data 2 et)
          (TXEq (FPayload PLink off 2) (VInteger 2 et)).

(** The L2 in-frame ethertype offset: +16 once a vlan tag has been matched (the
    protocol context is proto_vlan), else +12 (proto_eth). *)
Definition ll_net_off (vlan : bool) : nat := if vlan then 16 else 12.

(** [vlan]: a vlan tag (ethertype 0x8100) has already been matched in this rule,
    shifting subsequent in-frame protocol reads past the 4-byte tag. *)
Definition dep_guard (fam : string) (vlan : bool) (d : depspec) : lres dep_action :=
  match d with
  | DepL4 proto => LOk (guard false FMetaL4proto 1 (N.of_nat proto))
  | DepNfproto f =>
      if family_is_inet fam then LOk (guard true FMetaNfproto 1 (N.of_nat f))
      else if family_is_l2 fam then
        match nfproto_ethertype f with
        | Some et =>
            (* a DIRECT network selector (`ip saddr`) reaches the ethertype via
               proto_netdev's `meta protocol` — UNLESS a vlan tag shifted the
               protocol context to proto_vlan, an in-frame `payload @ link+16`. *)
            if vlan then LOk (net_ll_guard 16 et)
            else LOk (guard true FMetaProtocol 2 et)
        | None => LOk DAnone
        end
      else LOk DAnone                (* single-L3 family: no guard emitted *)
  | DepNetLL f =>
      (* a network guard synthesised UNDER the link header (`icmp type`): bridge's
         proto_eth reads the in-frame ethertype (`payload @ link+12`, or +16 past a
         vlan tag); netdev's proto_netdev and inet's proto_inet still use the meta
         template (`meta protocol` / `meta nfproto`) — src/payload.c
         payload_gen_special_dependency + proto_eth/proto_netdev/proto_inet. *)
      if family_is_inet fam then LOk (guard true FMetaNfproto 1 (N.of_nat f))
      else if String.eqb fam "bridge" then
        match nfproto_ethertype f with
        | Some et => LOk (net_ll_guard (ll_net_off vlan) et)
        | None => LOk DAnone
        end
      else if String.eqb fam "netdev" then
        match nfproto_ethertype f with
        | Some et =>
            if vlan then LOk (net_ll_guard 16 et)
            else LOk (guard true FMetaProtocol 2 et)
        | None => LOk DAnone
        end
      else LOk DAnone                (* single-L3 family: no guard emitted *)
  | DepL2proto et =>
      if family_is_l2 fam then LOk (guard false FMetaProtocol 2 et)
      else LOk DAnone
  | DepIiftype t =>
      (* the `meta iiftype == ARPHRD_ETHER` link guard: a no-op only in
         bridge (an inherently-ethernet family) *)
      if String.eqb fam "bridge" then LOk DAnone
      else LOk (guard_host false FMetaIiftype 2 (N.of_nat t))
  | DepEther et =>
      (* In netdev nft would ALSO prepend an iiftype guard whose host-endian
         immediate this pipeline renders in the wrong byte order vs the
         golden; rather than emit an unverified guard we refuse vlan in
         netdev (fail-loud; bridge — the tested family — needs only the
         ether-type guard). *)
      if String.eqb fam "netdev" then LErr LEvlanNetdev
      else LOk (guard false FEtherType 2 et)
  | DepIcmpType t => LOk (guard false FIcmpType 1 (N.of_nat t))
  end.

(** An EXPLICIT equality match on a field nft also uses as an implicit guard
    discharges that guard for the rest of the rule (nft dedups exactly this
    way: `meta l4proto 6 tcp dport 22` emits the guard once); `ip protocol N`
    fixes the packet's L4 protocol, discharging the l4proto guard (golden
    icmpX.t: `ip protocol icmp icmp type ...` has no l4proto load). *)
Definition discharge (mc : matchcond) : list (field * data) :=
  match mc with
  | MEq f v =>
      match f with
      | FMetaL4proto | FMetaNfproto | FMetaProtocol
      | FMetaIiftype | FEtherType => [(f, v)]
      | FIp4Protocol => [(FMetaL4proto, v)]
      | _ => []
      end
  | _ => []
  end.

(* ------------------------------------------------------------------ *)
(** ** Scalar value lowering. *)

Definition lowered : Type := list depspec * txmatch.

(** Resolve one atom at the selector's datatype, or fail loud. *)
Definition atom (dt : dtype) (v : svalue) (ctx : string) : lres nftval :=
  match resolve_value dt v with
  | Some tv => LOk tv
  | None => LErr (LEatom ctx)
  end.

(** The bare-comma OR-list members, resolved at the (bitmask) datatype. *)
Fixpoint resolve_bits (dt : dtype) (vs : list svalue) : lres (list N) :=
  match vs with
  | [] => LOk []
  | v :: rest =>
      match resolve_value dt v with
      | Some tv => match resolve_bits dt rest with
                   | LOk ns => LOk (val_N tv :: ns)
                   | LErr e => LErr e
                   end
      | None => LErr (LEatom "comma-list member")
      end
  end.

(** The datatypes whose bare comma list / single-value form is the implicit
    bitmask (evaluate.c expr_evaluate_list requires a TYPE_BITMASK basetype;
    ct_state additionally escapes the OP_IMPLICIT->OP_EQ rewrite). *)
Definition bitmask_dtype (dt : dtype) : bool :=
  match dt with
  | DTct_state | DTct_status | DTtcp_flag => true
  | _ => false
  end.

(** A CIDR length must fit the field width (nft: "Prefix length N is
    invalid"; the historical frontend silently saturated the mask). *)
Definition prefix_len_ok (dt : dtype) (len : nat) : bool :=
  (len <=? dt_width dt)%nat.

(** One SINGLE scalar value at a selector — the dispatch order mirrors the
    historical frontend exactly (see each branch's rationale):
    tcp-flags first (a range/set spelled there is a refusal, not a range),
    then ranges, prefixes, the ct-state/ct-status implicit-bitmask pair,
    the ifname wildcard, and finally the typed atom. *)
Definition lower_value (f : field) (dt : dtype) (deps : list depspec)
                       (op : srelop) (neg : bool) (v : svalue)
  : lres lowered :=
  if dtype_eqb dt DTtcp_flag then
    (* tcp_flag_type has basetype bitmask and does NOT get the
       OP_IMPLICIT->OP_EQ rewrite: the four written operators differ
       (inet/tcp.t:69-74; see Typed.elab_tcpflags_ops) *)
    match atom dt v "tcp flags" with
    | LOk tv => LOk (deps, TXBitmask f dt op [val_N tv])
    | LErr e => LErr e
    end
  else
  match v with
  | SVRange a b =>
      match atom dt a "range low bound", atom dt b "range high bound" with
      | LOk lo, LOk hi => LOk (deps, TXRange f dt neg lo hi)
      | LErr e, _ => LErr e
      | _, LErr e => LErr e
      end
  | SVPrefix base len =>
      match base with
      | SVIp4 _ | SVIp6 _ _ =>
          match atom dt base "CIDR base address" with
          | LOk tv =>
              if prefix_len_ok dt len
              then LOk (deps, TXPrefix f (if neg then CNe else CEq) tv len)
              else LErr LEprefixLen
          | LErr e => LErr e
          end
      | _ => LErr (LEatom "CIDR over a non-address value")
      end
  | _ =>
      if bitmask_dtype dt then
        (* ct state / ct status single value: positive stays the implicit
           bitmask test `(field & X) != 0` (golden ct.t.payload:35-40);
           the negated spelling is a plain register inequality (ct.t:7-10) *)
        match atom dt v "ct state/status" with
        | LOk tv => LOk (deps, TXBitmask f dt
                                 (if neg then SOpNe else SOpImplicit)
                                 [val_N tv])
        | LErr e => LErr e
        end
      else
        match atom dt v (String.concat " " ["selector atom"]) with
        | LOk tv =>
            match tv with
            | VIfname pre =>
                (* a SHORT resolved ifname is the trailing-`*` wildcard
                   spelling: positive -> the dedicated short-prefix shape;
                   negated / exact 16-byte names -> the typed atom *)
                if (List.length pre <? Typecheck.ifnamsiz)%nat && negb neg
                then LOk (deps, TXWildcard f pre)
                else LOk (deps, if neg then TXNeq f tv else TXEq f tv)
            | _ => LOk (deps, if neg then TXNeq f tv else TXEq f tv)
            end
        | LErr e => LErr e
        end
  end.

(* ------------------------------------------------------------------ *)
(** ** Sub-byte bitfields. *)

Definition bf_raw (spec : bitfield_spec) (kp : skeypath) (v : svalue)
  : lres N :=
  match v with
  | SVNum n => LOk (N.of_nat n)
  | SVSym s =>
      if bf_dscp spec then
        match assoc_str s dt_syms_dscp with
        | Some n => LOk n
        | None => LErr (LEatom ("dscp value " ++ s))
        end
      else LErr (LEbitfieldRhs (String.concat " " kp))
  | _ => LErr (LEbitfieldRhs (String.concat " " kp))
  end.

Definition lower_bitfield (spec : bitfield_spec) (kp : skeypath) (r : srhs)
  : lres lowered :=
  match sr_payload r with
  | SSEvalue v =>
      match bf_raw spec kp v with
      | LOk n =>
          (* bit-precise admission: nft refuses `ip dscp 64` ("value 64
             exceeds valid range 0-63"); the historical frontend silently
             truncated the shifted bytes *)
          if (n <? 2 ^ N.of_nat (bf_bits spec))%N
          then LOk (bf_deps spec, TXBitfield spec (sr_neg r) n)
          else LErr (LEbitfieldRange (String.concat " " kp))
      | LErr e => LErr e
      end
  | _ =>
      (* a set/range over a bitfield needs a bitwise-then-lookup shape not
         modelled yet; refuse rather than mis-encode *)
      LErr (LEbitfieldRhs (String.concat " " kp))
  end.

(* ------------------------------------------------------------------ *)
(** ** Presence tests (`missing` / `exists`). *)

Definition presence_payload (se : ssetexpr) : option bool :=
  match se with
  | SSEvalue (SVSym s) =>
      if String.eqb s "exists" then Some true
      else if String.eqb s "missing" then Some false
      else None
  | _ => None
  end.

(** `fib <sel> <res> missing|exists`: the fib PRESENT flag (0/1) compared to
    0 — `missing` is eq, `exists` neq; the chosen result column is irrelevant
    under the present flag.  `exthdr <p>` / `tcp option <n>`: the exthdr
    walker's 1-byte present flag compared to 1 (exists) / 0 (missing) —
    golden ip6/exthdr.t.payload, any/tcpopt.t.payload.

    The surface COMPARISON operator [neg] (`!=`) is threaded through: nft emits
    `cmp neq` for `exthdr hbh != exists` (src/statement.c / the exthdr
    expression's OP_NEQ), which our historical frontend dropped — matching the
    exact COMPLEMENT of the intended packet set (reports/corpus-divergence-bugs
    class D).  For the exthdr/tcpopt eq-1 present form the surface `!=` is the
    flag's negation directly; for the fib neq-0 present form it XORs with the
    exists/missing polarity (a `!=` flips `exists`<->`missing`). *)
Definition lower_presence (kp : skeypath) (ex neg : bool)
  : option (lres lowered) :=
  match kp with
  | k :: rest =>
      if String.eqb k "fib" then
        match rest with
        | sel :: _res :: nil =>
            Some (LOk ([], TXFlag (FFib sel FRpresent) (xorb ex neg) 0))
        | _ => None
        end
      else if String.eqb k "exthdr" then
        match rest with
        | proto :: nil =>
            Some match exthdr_htype proto with
                 | Some h => LOk (dep_ip6,
                                  TXFlag (FExthdr EPipv6 h 0 1 true) neg
                                         (if ex then 1%N else 0%N))
                 | None => LErr (LEexthdr proto)
                 end
        | _ => None
        end
      else if String.eqb k "tcpopt" then
        match rest with
        | name :: nil =>
            Some match dt_tcpopt_num name with
                 | Some n => LOk ([],
                                  TXFlag (FExthdr EPtcpopt (N.to_nat n) 0 1 true)
                                         neg (if ex then 1%N else 0%N))
                 | None => LErr (LEtcpopt name)
                 end
        | _ => None
        end
      else None
  | [] => None
  end.

(* ------------------------------------------------------------------ *)
(** ** The match entries. *)

Definition lower_rhs (f : field) (dt : dtype) (deps : list depspec) (r : srhs)
  : lres lowered :=
  match sr_payload r with
  | SSElist vs =>
      (* a bare comma list is NOT a set: evaluate.c expr_evaluate_list
         requires a TYPE_BITMASK basetype and OR-folds all members into one
         constant, then the single-value operator dispatch applies *)
      if bitmask_dtype dt then
        match resolve_bits dt vs with
        | LOk bits => LOk (deps, TXBitmask f dt (sr_op r) bits)
        | LErr e => LErr e
        end
      else LErr LEcommaNonBitmask
  | SSEvalue v => lower_value f dt deps (sr_op r) (sr_neg r) v
  | SSEset _ | SSEref _ => LErr LEsetShaped
  end.

Definition lower_single (kp : skeypath) (r : srhs) : lres lowered :=
  match presence_payload (sr_payload r) with
  | Some ex =>
      match lower_presence kp ex (sr_neg r) with
      | Some res => res
      | None =>
          (* not a presence-bearing key path: `missing`/`exists` fall through
             as ordinary barewords (e.g. an interface literally named so) *)
          match bitfield kp with
          | Some spec => lower_bitfield spec kp r
          | None => match selector kp with
                    | Some (f, dt, deps) => lower_rhs f dt deps r
                    | None => LErr (LEselector kp)
                    end
          end
      end
  | None =>
      match bitfield kp with
      | Some spec => lower_bitfield spec kp r
      | None => match selector kp with
                | Some (f, dt, deps) => lower_rhs f dt deps r
                | None => LErr (LEselector kp)
                end
      end
  end.

(** The scalar-match entry point: ONE selector key path (concatenations are
    set lookups — the M3 untyped path).  Defines are expanded by the caller;
    family enters only at guard materialisation ([dep_guard]). *)
Definition lower_match (m : smatch) : lres lowered :=
  match sm_keys m with
  | kp :: nil => lower_single kp (sm_rhs m)
  | _ => LErr LEnotScalar
  end.

(** Explicit bitwise matches: `<sel> and|or|xor <mask> [==|!=] <value>`.
    nft realises them as `bitwise reg = (reg & mask) ^ xor ; cmp` with
      and m : (m, 0)     or m : (~m, m)     xor m : (~0, m)
    (golden any/meta.t.payload `meta mark and 0x3`, any/ct.t.payload
    `ct mark or 0x23`); admitted only over an integer-basetype selector —
    ifname's chain ends at STRING, so `iifname & 0xff` is ill-typed. *)
Definition lower_bitmatch (kp : skeypath) (op : string) (mask : svalue)
                          (r : srhs) : lres lowered :=
  match selector kp with
  | None => LErr (LEselector kp)
  | Some (f, dt, deps) =>
      match int_basetype dt with
      | None => LErr LEbitwiseNonInteger
      | Some _ =>
          let obop :=
            if String.eqb op "and" then Some BOand
            else if String.eqb op "or" then Some BOor
            else if String.eqb op "xor" then Some BOxor
            else None in
          match obop with
          | None => LErr (LEbitwiseOp op)
          | Some bop =>
              match sr_op r with
              | SOpBang =>
                  (* `<sel> & <mask> ! <v>` is an nft SYNTAX error (`!` only
                     exists in the flagcmp form `tcp flags ! fin,rst`) —
                     inet/tcp.t:90 pins it `;fail`; mirror tc_bitmatch. *)
                  LErr (LEbitwiseOp "!")
              | _ =>
                  match sr_payload r with
                  | SSEvalue v =>
                      match atom dt mask "bitwise mask",
                            atom dt v "bitwise value"
                      with
                      | LOk mv, LOk vv =>
                          LOk (deps, TXBitwise f dt bop (sr_neg r) mv vv)
                      | LErr e, _ => LErr e
                      | _, LErr e => LErr e
                      end
                  | _ => LErr LEbitwiseRhs
                  end
              end
          end
      end
  end.

(* ================================================================== *)
(** ** M3: verified composite immediates — set / map / vmap elements.

    Every set/map/vmap byte composition the frontend used to do in OCaml is
    now built HERE, verified: point / range / CIDR (net+broadcast) element
    intervals, the big-endian re-encoded interval path for host-endian fields,
    declared-set type atoms, concatenated tuples with 4-byte register-slot
    padding (and the FLAT unpadded vmap-key asymmetry), and the content-dedup
    `__setN` interning as a state-passing fold.  The OCaml frontend loses every
    [interval_of_value]/[bytes_of_typeatom]/[pad_to_slot]/[prefix_mask] and no
    longer constructs [MSetT]/[MConcatSet]; it threads the [lstate] below and
    reads back the set declarations. *)

(** Bytewise OR: `(a & ~b) ^ b = a | b` per byte (the nft broadcast operand
    `net | ~mask`; the numeric identity is [Lower_Proofs.land_not_xor_is_or]). *)
Definition data_or (a b : data) : data := data_bitops a (Typed.data_not b) b.

(** The CIDR net/broadcast interval — the ONE Coq expansion, built from the
    SAME [Typed.prefix_mask]/[Typed.data_and] arithmetic that
    [Typed.prefix_expand] uses (their membership agreement is
    [Lower_Proofs.cidr_interval_agrees_prefix_expand], killing the
    two-implementations tension).  net = base & mask;
    broadcast = net | ~mask. *)
Definition cidr_interval (v : nftval) (plen : nat) : data * data :=
  let bytes := Nftval.encode v in
  let w := List.length bytes in
  let mask := prefix_mask w plen in
  let net := data_and bytes mask in
  (net, data_or net (Typed.data_not mask)).

(** *** Source views of a set-declaration element.

    A declared set element is either a POINT or an INTERVAL; the environment
    stores closed intervals, a point as the degenerate [v,v] pair.  [SEl] and
    [SRange] are the source-term views of those two shapes, so a generated
    declaration reads [SEl v] / [SRange lo hi] instead of a degenerate pair.
    They are definitional: [SEl v = (v, v)] and [SRange lo hi = (lo, hi)] hold
    by [reflexivity], so every consumer of the interval pairs is unchanged. *)
Definition SEl (v : data) : data * data := (v, v).
Definition SRange (lo hi : data) : data * data := (lo, hi).

Lemma SEl_iv : forall v, SEl v = (v, v).
Proof. reflexivity. Qed.
Lemma SRange_iv : forall lo hi, SRange lo hi = (lo, hi).
Proof. reflexivity. Qed.

(** One element's register encoding: big-endian re-encoded on the host-endian
    interval path ([Typed.encode_be]), the ordinary register encoding
    otherwise. *)
Definition el_encode (be : bool) (tv : nftval) : data :=
  if be then Typed.encode_be tv else Nftval.encode tv.

(** One set element's byte interval at a datatype: a point is the degenerate
    [b,b]; a range is the per-endpoint encoding; a CIDR is [cidr_interval]
    (always big-endian — an address is network order regardless of [be]). *)
Definition value_interval (dt : dtype) (be : bool) (v : svalue) : lres (data * data) :=
  match v with
  | SVRange lo hi =>
      match resolve_value dt lo, resolve_value dt hi with
      | Some a, Some b => LOk (el_encode be a, el_encode be b)
      | _, _ => LErr (LEatom "set range bound")
      end
  | SVPrefix base plen =>
      match base with
      | SVIp4 _ | SVIp6 _ _ =>
          match resolve_value dt base with
          | Some tv => LOk (cidr_interval tv plen)
          | None => LErr (LEatom "set CIDR base")
          end
      | _ => LErr (LEatom "CIDR over a non-address set element")
      end
  | _ =>
      match resolve_value dt v with
      | Some tv => let b := el_encode be tv in LOk (b, b)
      | None => LErr (LEatom "set element")
      end
  end.

(** A single-field set forces nft's `byteorder hton` path exactly when its
    field is host-endian AND it has an interval element (a range or CIDR); an
    exact-only set is an unordered memcmp lookup with no conversion. *)
Definition set_has_interval (elems : list svalue) : bool :=
  existsb (fun v => match v with SVRange _ _ | SVPrefix _ _ => true | _ => false end)
          elems.

Fixpoint map_lres {A B : Type} (f : A -> lres B) (xs : list A) : lres (list B) :=
  match xs with
  | [] => LOk []
  | x :: r =>
      match f x with
      | LOk y => match map_lres f r with LOk ys => LOk (y :: ys) | LErr e => LErr e end
      | LErr e => LErr e
      end
  end.

(** Per-field intervals of a concatenated element (each field big-endian eq;
    the arity is checked by the caller). *)
Fixpoint concat_intervals (dts : list dtype) (vs : list svalue)
  : lres (list (data * data)) :=
  match dts, vs with
  | [], [] => LOk []
  | dt :: dts', v :: vs' =>
      match value_interval dt false v with
      | LOk iv =>
          match concat_intervals dts' vs' with
          | LOk r => LOk (iv :: r)
          | LErr e => LErr e
          end
      | LErr e => LErr e
      end
  | _, _ => LErr LEconcatArity
  end.

(** Register-slot padding of ONE field's bytes: NFT_SET_CONCAT lays each field
    in its own 4-byte register slot ([Bytes.reg_slot]), field bytes at the
    front + trailing zeros.  The historical [pad_to_slot], now verified. *)
Definition pad_slot (d : data) : data :=
  (d ++ repeat 0 (reg_slot (List.length d) - List.length d))%list.

(** A concatenated SET element's [lo,hi]: per-field bounds, each slot-padded,
    concatenated.  (Concat sets pad; concat VMAP keys do NOT — [concat_flat].) *)
Definition concat_padded (ivs : list (data * data)) : data * data :=
  (List.concat (map (fun p => pad_slot (fst p)) ivs),
   List.concat (map (fun p => pad_slot (snd p)) ivs)).

(** A concatenated VMAP key's [lo,hi]: the FLAT (unpadded) per-field
    concatenation — [assoc_verdict] tests the flat key with [data_in_iv]. *)
Definition concat_flat (ivs : list (data * data)) : data * data :=
  (List.concat (map fst ivs), List.concat (map snd ivs)).

Definition concat_elem_padded (dts : list dtype) (v : svalue) : lres (data * data) :=
  match v with
  | SVConcat vs =>
      if Nat.eqb (List.length vs) (List.length dts)
      then match concat_intervals dts vs with
           | LOk ivs => LOk (concat_padded ivs)
           | LErr e => LErr e
           end
      else LErr LEconcatArity
  | _ => LErr LEconcatArity
  end.

Definition concat_elem_flat (dts : list dtype) (v : svalue) : lres (data * data) :=
  match v with
  | SVConcat vs =>
      if Nat.eqb (List.length vs) (List.length dts)
      then match concat_intervals dts vs with
           | LOk ivs => LOk (concat_flat ivs)
           | LErr e => LErr e
           end
      else LErr LEconcatArity
  | _ => LErr LEconcatArity
  end.

(* ------------------------------------------------------------------ *)
(** ** Declared set type atoms -> datatypes ([bytes_of_typeatom]'s domain). *)

Definition typeatom_dtype (a : string) : option dtype :=
  if String.eqb a "ipv4_addr" then Some DTipv4
  else if String.eqb a "ipv6_addr" then Some DTipv6
  else if String.eqb a "ifname" then Some DTifname
  else if String.eqb a "iface_index" then Some DTifindex
  else if String.eqb a "inet_service" then Some DTinet_service
  else if String.eqb a "inet_proto" then Some DTinet_proto
  else if String.eqb a "ether_addr" then Some DTether
  else if String.eqb a "mark" then Some DTmark
  else None.

Fixpoint typeatoms_dtypes (types : list string) : lres (list dtype) :=
  match types with
  | [] => LOk []
  | t :: r =>
      match typeatom_dtype t with
      | Some dt => match typeatoms_dtypes r with
                   | LOk dts => LOk (dt :: dts)
                   | LErr e => LErr e
                   end
      | None => LErr (LEsettype t)
      end
  end.

(** One declared-set element to an interval: single-typed (range/CIDR-on-ip/
    point) or a slot-padded concatenation matching the declared arity. *)
Definition decl_elem_interval (types : list string) (v : svalue) : lres (data * data) :=
  match types with
  | [t] =>
      match typeatom_dtype t with
      | Some dt => match v with
                   | SVConcat _ => LErr LEconcatArity
                   | _ => value_interval dt false v
                   end
      | None => LErr (LEsettype t)
      end
  | _ =>
      match typeatoms_dtypes types with
      | LOk dts => concat_elem_padded dts v
      | LErr e => LErr e
      end
  end.

(* ------------------------------------------------------------------ *)
(** ** The interning state (content-dedup `__setN`/`__mapN` fold).

    The byte-relevant slice of the driver state: the fresh-name counter and the
    named set / verdict-map / value-map contents.  Named declarations and
    anonymous inline sets share ONE set list, so an anonymous set with the same
    contents as a declared set reuses the declared name (nft set identity by
    contents).  Naming is decimal ([nat_dec] extracts to [string_of_int]) to
    keep the generated `__set0`/`__map0` identifiers byte-identical. *)

Record lstate : Type := mkLstate {
  ls_ctr   : nat;
  ls_sets  : list (String.string * list (data * data));
  ls_vmaps : list (String.string * list (data * data * verdict));
  ls_maps  : list (String.string * list (data * data)) }.

Definition ls0 : lstate := mkLstate 0 [] [] [].

(** Decimal rendering of a nat (extracted to OCaml [string_of_int]; the Coq
    body is a faithful decimal used only by vm_compute, never trusted). *)
Definition dec_digit (n : nat) : String.string :=
  String.String (Ascii.ascii_of_nat (48 + n)) String.EmptyString.
Fixpoint dec_aux (fuel n : nat) : String.string :=
  match fuel with
  | O => String.EmptyString
  | S f =>
      if Nat.ltb n 10 then dec_digit n
      else String.append (dec_aux f (Nat.div n 10)) (dec_digit (Nat.modulo n 10))
  end.
Definition nat_dec (n : nat) : String.string := dec_aux (S n) n.

Definition data_pair_eqb (p q : data * data) : bool :=
  andb (data_eqb (fst p) (fst q)) (data_eqb (snd p) (snd q)).
Fixpoint ivs_eqb (a b : list (data * data)) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => andb (data_pair_eqb x y) (ivs_eqb a' b')
  | _, _ => false
  end.

Definition set_name (st : lstate) : String.string :=
  String.append "__set" (nat_dec (ls_ctr st)).
Definition map_name (st : lstate) : String.string :=
  String.append "__map" (nat_dec (ls_ctr st)).

(** Intern an encoded interval list, deduplicated by CONTENT against every
    existing (named or anonymous) set. *)
Definition intern_set (st : lstate) (elems : list (data * data))
  : String.string * lstate :=
  match find (fun ne => ivs_eqb (snd ne) elems) (ls_sets st) with
  | Some (name, _) => (name, st)
  | None =>
      let name := set_name st in
      (name, mkLstate (S (ls_ctr st)) ((name, elems) :: ls_sets st)
                      (ls_vmaps st) (ls_maps st))
  end.

Definition fresh_map (st : lstate) : String.string * lstate :=
  (map_name st,
   mkLstate (S (ls_ctr st)) (ls_sets st) (ls_vmaps st) (ls_maps st)).

Definition add_set (st : lstate) (name : String.string)
    (elems : list (data * data)) : lstate :=
  mkLstate (ls_ctr st) ((name, elems) :: ls_sets st) (ls_vmaps st) (ls_maps st).
Definition add_vmap (st : lstate) (name : String.string)
    (ents : list (data * data * verdict)) : lstate :=
  mkLstate (ls_ctr st) (ls_sets st) ((name, ents) :: ls_vmaps st) (ls_maps st).
Definition add_map (st : lstate) (name : String.string)
    (ents : list (data * data)) : lstate :=
  mkLstate (ls_ctr st) (ls_sets st) (ls_vmaps st) ((name, ents) :: ls_maps st).

(* ------------------------------------------------------------------ *)
(** ** The set / vmap / declaration lowering entry points (OCaml calls these;
    it never constructs an [MSetT]/[MConcatSet] nor composes a byte). *)

(** Inline `{...}` set over a single field: the interval bytes are built and
    interned here, and the interval-over-host-endian-field case takes the
    `byteorder hton` [MSetT] path with big-endian bounds. *)
Definition lower_anon_set (st : lstate) (f : field) (dt : dtype) (neg : bool)
    (elems : list svalue) : lres (lstate * matchcond) :=
  if dtype_eqb dt DTtcp_flag then LErr LEtcpflagSet else
  let be := andb (Typed.range_hton dt) (set_has_interval elems) in
  match map_lres (value_interval dt be) elems with
  | LErr e => LErr e
  | LOk ivs =>
      let '(name, st') := intern_set st ivs in
      if be then
        let w := dt_bytes dt in
        LOk (st', MSetT f [TByteorder true w w] neg name)
      else LOk (st', MConcatSet [f] neg name)
  end.

(** A named-set / concatenated-set `@name` reference (no bytes composed). *)
Definition lower_set_ref (fields : list field) (neg : bool) (name : String.string)
  : matchcond := MConcatSet fields neg name.

(** Inline concatenated `{...}` set: per-field slot-padded intervals, interned. *)
Definition lower_concat_set (st : lstate) (fields : list field) (dts : list dtype)
    (neg : bool) (elems : list svalue) : lres (lstate * matchcond) :=
  match map_lres (concat_elem_padded dts) elems with
  | LErr e => LErr e
  | LOk ivs =>
      let '(name, st') := intern_set st ivs in
      LOk (st', MConcatSet fields neg name)
  end.

(** Verdict-map entries (single-field key): each key's [lo,hi] interval + its
    verdict. *)
Fixpoint vmap_entries_single (dt : dtype) (entries : list (svalue * verdict))
  : lres (list (data * data * verdict)) :=
  match entries with
  | [] => LOk []
  | (v, sv) :: r =>
      match value_interval dt false v with
      | LOk (lo, hi) =>
          match vmap_entries_single dt r with
          | LOk rest => LOk ((lo, hi, sv) :: rest)
          | LErr e => LErr e
          end
      | LErr e => LErr e
      end
  end.

(** Verdict-map entries (concatenated key): the FLAT per-field key concatenation
    (the model's [assoc_verdict] key), NOT slot-padded. *)
Fixpoint vmap_entries_concat (dts : list dtype) (entries : list (svalue * verdict))
  : lres (list (data * data * verdict)) :=
  match entries with
  | [] => LOk []
  | (v, sv) :: r =>
      match concat_elem_flat dts v with
      | LOk (lo, hi) =>
          match vmap_entries_concat dts r with
          | LOk rest => LOk ((lo, hi, sv) :: rest)
          | LErr e => LErr e
          end
      | LErr e => LErr e
      end
  end.

(** A declared set's elements. *)
Definition decl_set_elems (types : list string) (elems : list svalue)
  : lres (list (data * data)) := map_lres (decl_elem_interval types) elems.

(** A declared verdict-map's entries. *)
Fixpoint decl_vmap_ents (types : list string) (elems : list (svalue * verdict))
  : lres (list (data * data * verdict)) :=
  match elems with
  | [] => LOk []
  | (v, sv) :: r =>
      match decl_elem_interval types v with
      | LOk (lo, hi) =>
          match decl_vmap_ents types r with
          | LOk rest => LOk ((lo, hi, sv) :: rest)
          | LErr e => LErr e
          end
      | LErr e => LErr e
      end
  end.

(* ================================================================== *)
(** ** M4: statement immediates, NAT / tproxy / reject terminals, and the
    whole-ruleset driver.  With this the OCaml frontend composes NO byte at
    all — it injects the surface tree (Nft_inject) and calls [lower_ruleset];
    every value->byte decision (statement-set register widths, NAT/tproxy
    address+port immediates and flag bits, reject family-default type/code
    tables, syslog level canonicalisation, limit assembly) and every refusal
    (an [lerr] constructor) lives HERE, verified. *)

(** lres monadic bind. *)
Definition lbind {A B : Type} (m : lres A) (k : A -> lres B) : lres B :=
  match m with LOk a => k a | LErr e => LErr e end.
Notation "x <-- m ;; k" := (lbind m (fun x => k))
  (at level 61, right associativity).

(* ---------- small string utilities (space split / assoc) ---------- *)

Definition spc : Ascii.ascii := Ascii.ascii_of_nat 32.

(** [split_on c s]: split [s] at every occurrence of [c], KEEPING empty
    tokens — the semantics of OCaml [String.split_on_char] (n separators give
    n+1 pieces), so [canon_log_opts]/[reject] word matching is faithful. *)
Fixpoint split_on (c : Ascii.ascii) (s : string) : list string :=
  match s with
  | EmptyString => EmptyString :: nil
  | String a rest =>
      if Ascii.eqb a c then EmptyString :: split_on c rest
      else match split_on c rest with
           | w :: ws => String a w :: ws
           | nil => (String a EmptyString) :: nil   (* unreachable *)
           end
  end.

Fixpoint find_str {A : Type} (n : string) (l : list (string * A)) : option A :=
  match l with
  | nil => None
  | (k, v) :: r => if String.eqb k n then Some v else find_str n r
  end.

(* ---------- define ($var) expansion (structural; fail-loud) ---------- *)

Fixpoint resolve_sv (fuel : nat) (defs : list (string * svalue)) (v : svalue)
  : lres svalue :=
  match fuel with
  | O => LErr (LEundefVar "<define recursion bound>")
  | S fu =>
      match v with
      | SVVar n =>
          match find_str n defs with
          | Some v' => resolve_sv fu defs v'
          | None => LErr (LEundefVar n)
          end
      | SVPrefix b l =>
          b' <-- resolve_sv fu defs b ;; LOk (SVPrefix b' l)
      | SVRange a b =>
          a' <-- resolve_sv fu defs a ;;
          b' <-- resolve_sv fu defs b ;; LOk (SVRange a' b')
      | SVConcat vs =>
          vs' <-- map_lres (resolve_sv fu defs) vs ;; LOk (SVConcat vs')
      | SVSet vs =>
          vs' <-- map_lres (resolve_sv fu defs) vs ;; LOk (SVSet vs')
      | SVOr vs =>
          vs' <-- map_lres (resolve_sv fu defs) vs ;; LOk (SVOr vs')
      | _ => LOk v
      end
  end.

Definition resolve_setexpr (fuel : nat) (defs : list (string * svalue))
    (se : ssetexpr) : lres ssetexpr :=
  match se with
  | SSEvalue v => v' <-- resolve_sv fuel defs v ;; LOk (SSEvalue v')
  | SSElist vs => vs' <-- map_lres (resolve_sv fuel defs) vs ;; LOk (SSElist vs')
  | SSEset vs => vs' <-- map_lres (resolve_sv fuel defs) vs ;; LOk (SSEset vs')
  | SSEref n => LOk (SSEref n)
  end.

Definition resolve_rhs (fuel : nat) (defs : list (string * svalue)) (r : srhs)
  : lres srhs :=
  se' <-- resolve_setexpr fuel defs (sr_payload r) ;;
  LOk (mkSrhs (sr_op r) (sr_neg r) se').

(* ---------- statement immediates: `meta <k> set` / `ct <k> set` ----------
   The register WIDTH the kernel uses when STORING a value is key-specific and
   HOST-endian (net/netfilter/nft_ct.c, nft_meta.c): the immediate is a
   [VHostInt] of that width, encoded little-endian.  This REPLACES the OCaml
   [meta_set_kind]/[ct_set_kind] width tables and the [enc_atom] encode path. *)

Definition meta_set_key (name : string) : option (meta_key * nat) :=
  if String.eqb name "mark" then Some (MKmark, 4)
  else if String.eqb name "priority" then Some (MKpriority, 4)
  else if String.eqb name "pkttype" then Some (MKpkttype, 1)
  else None.

Definition ct_set_key (name : string) : option (ct_key * nat) :=
  if String.eqb name "zone" then Some (CKzone, 2)
  else if String.eqb name "label" then Some (CKlabel, 16)
  else if String.eqb name "mark" then Some (CKmark, 4)
  else if String.eqb name "event" then Some (CKevent, 4)
  else None.

(** The verified typed immediate: the set value resolved at a HOST-endian
    integer of the key's register width (little-endian encode). *)
Definition set_imm (w : nat) (v : svalue) (ctx : string) : lres vsrc :=
  match resolve_value (DThostint w) v with
  | Some tv => LOk (VImm (Nftval.encode tv))
  | None => LErr (LEatom ctx)
  end.

Definition lower_meta_set (name : string) (v : svalue) : lres stmt :=
  match meta_set_key name with
  | Some (k, w) => vs <-- set_imm w v "meta set value" ;; LOk (SMetaSet k vs)
  | None => LErr (LEmetaSet name)
  end.

(** `ct label set <k>`: a ct label is a BIT POSITION in the 128-bit label
    bitmap (nft src/ct.c ct_label_type / the kernel nf_connlabels_replace sets
    ONE bit), NOT a literal integer register.  nft builds the value by
    `mpz_setbit(value, k)` then serialises the 16-byte register with
    `mpz_export_data(..., BYTEORDER_HOST_ENDIAN, 16)` (src/ct.c
    ct_label_type_parse; ct_label_type.byteorder = BYTEORDER_HOST_ENDIAN).
    Host-endian export of a single 16-byte word writes the LEAST-significant
    byte FIRST, so bit k lands in byte [k/8] at bit [k mod 8]: `ct label set
    127` -> byte 15 = 0x80 (register bytes `00..00 80`), which live nft dumps as
    `immediate 0x00000000 0x00000000 0x00000000 0x80000000`.  [N_to_data 16] is
    big-endian [N] arithmetic (so [2^127] does NOT wrap — unlike the historical
    OCaml `lsl` on a 63-bit int, bug N's shift-wrap half), and [List.rev] turns
    that big-endian bitmap into the host-endian byte layout the kernel stores.
    A numeric literal is the bit index (0..127); symbolic label names resolve
    against a live registry we do not model, so they are refused (fail-loud). *)
Definition ct_label_imm (v : svalue) : lres vsrc :=
  match v with
  | SVNum k =>
      if (k <? 128)%nat
      then LOk (VImm (List.rev (N_to_data 16 (2 ^ N.of_nat k))))
      else LErr (LEctSet "label bit index exceeds 127")
  | _ => LErr (LEctSet "label (symbolic name registry not modelled)")
  end.

Definition lower_ct_set (name : string) (v : svalue) : lres stmt :=
  if String.eqb name "label"
  then vs <-- ct_label_imm v ;; LOk (SCtSet CKlabel vs)
  else match ct_set_key name with
       | Some (k, w) => vs <-- set_imm w v "ct set value" ;; LOk (SCtSet k vs)
       | None => LErr (LEctSet name)
       end.

(* ---------- log canonicalisation (syslog level symbol table) ---------- *)

Definition syslog_level (name : string) : option nat :=
  if String.eqb name "emerg" then Some 0
  else if String.eqb name "alert" then Some 1
  else if String.eqb name "crit" then Some 2
  else if String.eqb name "err" then Some 3
  else if String.eqb name "warn" then Some 4
  else if String.eqb name "warning" then Some 4
  else if String.eqb name "notice" then Some 5
  else if String.eqb name "info" then Some 6
  else if String.eqb name "debug" then Some 7
  else if String.eqb name "audit" then Some 8
  else None.

(** `log level <name>` renders with the NUMERIC level; every other log-option
    form (prefix / group / ...) is left verbatim (as the golden does). *)
Definition canon_log_opts (opts : string) : string :=
  match split_on spc opts with
  | lvl :: name :: nil =>
      if String.eqb lvl "level"
      then match syslog_level name with
           | Some n => String.append "level " (nat_dec n)
           | None => opts
           end
      else opts
  | _ => opts
  end.

(* ---------- limit ---------- *)

Definition limit_unit (u : string) : option nat :=
  if String.eqb u "second" then Some 0
  else if String.eqb u "minute" then Some 1
  else if String.eqb u "hour" then Some 2
  else if String.eqb u "day" then Some 3
  else if String.eqb u "week" then Some 4
  else None.

(** `limit rate R/<unit> [over] [burst B] [bytes]`: bit 0 of [ls_flags] is
    NFT_LIMIT_F_INV ("over").  The 2^40 extracted-int seam guard stays at the
    OCaml injection boundary (see Extract.v); every rate/burst here is a bound
    [nat]. *)
Definition limit_spec (rate : nat) (u : string) (over : bool)
    (burst : nat) (byte_rate : bool) : lres Packet.limit_spec :=
  match limit_unit u with
  | Some un =>
      LOk {| Packet.ls_rate := rate; Packet.ls_unit := un;
             Packet.ls_burst := burst; Packet.ls_bytes := byte_rate;
             Packet.ls_flags := (if over then 1 else 0) |}
  | None => LErr (LElimitUnit u)
  end.

(* ---------- reject: family-default and explicit type/code ---------- *)

Definition reject_words (opts : string) : list string :=
  filter (fun w => negb (String.eqb w EmptyString) && negb (String.eqb w "type"))
         (split_on spc opts).

Definition icmp_reject_code (name : string) : option nat :=
  if String.eqb name "net-unreachable" then Some 0
  else if String.eqb name "host-unreachable" then Some 1
  else if String.eqb name "prot-unreachable" then Some 2
  else if String.eqb name "port-unreachable" then Some 3
  else if String.eqb name "net-prohibited" then Some 9
  else if String.eqb name "host-prohibited" then Some 10
  else if String.eqb name "admin-prohibited" then Some 13
  else None.

Definition icmpv6_reject_code (name : string) : option nat :=
  if String.eqb name "no-route" then Some 0
  else if String.eqb name "admin-prohibited" then Some 1
  else if String.eqb name "addr-unreachable" then Some 3
  else if String.eqb name "port-unreachable" then Some 4
  else if String.eqb name "policy-fail" then Some 5
  else if String.eqb name "reject-route" then Some 6
  else None.

Definition icmpx_reject_code (name : string) : option nat :=
  if String.eqb name "no-route" then Some 0
  else if String.eqb name "port-unreachable" then Some 1
  else if String.eqb name "host-unreachable" then Some 2
  else if String.eqb name "admin-prohibited" then Some 3
  else None.

(** The reject (type, code) for a chain of [family], mirroring evaluate.c
    stmt_reject_default: a BARE reject is family-defaulted (ip icmp
    port-unreach (0,3); ip6 icmpv6 port-unreach (0,4); L2/dual icmpx
    port-unreach (2,1)); `tcp reset` is (1,0). *)
Definition reject_type_code (family : string) (opts : string)
  : lres (nat * nat) :=
  match reject_words opts with
  | nil =>
      if String.eqb family "ip" then LOk (0, 3)
      else if String.eqb family "ip6" then LOk (0, 4)
      else LOk (2, 1)
  | w1 :: rest =>
      if String.eqb w1 "tcp" then
        match rest with
        | w2 :: _ => if String.eqb w2 "reset" then LOk (1, 0)
                     else LErr (LEreject opts)
        | _ => LErr (LEreject opts)
        end
      else match rest with
        | name :: _ =>
            if String.eqb w1 "icmp" then
              match icmp_reject_code name with Some c => LOk (0, c) | None => LErr (LEreject opts) end
            else if String.eqb w1 "icmpv6" then
              match icmpv6_reject_code name with Some c => LOk (0, c) | None => LErr (LEreject opts) end
            else if String.eqb w1 "icmpx" then
              match icmpx_reject_code name with Some c => LOk (2, c) | None => LErr (LEreject opts) end
            else LErr (LEreject opts)
        | nil => LErr (LEreject opts)
        end
  end.

(** The protocol guard a `reject with ...` needs: a `reject with icmp/icmpv6
    <x>` needs the network guard in a dual-stack family (icmp -> ipv4, icmpv6
    -> ipv6; a no-op in single-L3 ip/ip6); a `reject with tcp reset` needs
    `meta l4proto 6` (DepL4 6) — the kernel [nft_reject] eval sends the RST
    UNCONDITIONALLY of L4 protocol (net/netfilter/nft_reject.c
    nft_reject_eval), so nft prepends the TCP guard (evaluate.c
    stmt_reject_gen_dependency -> NFT_META_L4PROTO) to keep a TCP-RST reject
    from firing on non-TCP packets; our historical frontend dropped it
    (reports/corpus-divergence-bugs class E, packet-proven). *)
Definition reject_dep (opts : string) : list depspec :=
  match reject_words opts with
  | w1 :: _ =>
      if String.eqb w1 "icmp" then [DepNfproto 2]
      else if String.eqb w1 "icmpv6" then [DepNfproto 10]
      else if String.eqb w1 "tcp" then [DepL4 6]   (* tcp reset -> l4proto tcp *)
      else nil
  | nil => nil
  end.

(* ---------- NAT / tproxy immediates ---------- *)

Definition nat_l3_family (family : string) : nat_af :=
  if String.eqb family "ip6" then NFip6
  else if String.eqb family "inet" then NFinet
  else NFip4.

(** 2-byte big-endian port (the compiler loads it into the proto register). *)
Definition port_bytes (p : nat) : data := N_to_data 2 (N.of_nat p).

(** NAT flag words -> the kernel NF_NAT_RANGE_* bitmask (nf_nat.h). *)
Definition nat_flag_bit (name : string) : option nat :=
  if String.eqb name "random" then Some 4
  else if String.eqb name "persistent" then Some 8
  else if String.eqb name "fully-random" then Some 16
  else None.

Fixpoint nat_flags_of (fs : list string) : lres nat :=
  match fs with
  | nil => LOk 0
  | f :: r =>
      match nat_flag_bit f with
      | Some b => rest <-- nat_flags_of r ;; LOk (Nat.lor b rest)
      | None => LErr (LEnatFlag f)
      end
  end.

Definition empty_nat (kind : nat_op) (fam : nat_af) (extra : nat_2nd) (flags : nat)
  : nat_spec :=
  {| nat_addr_imm := None; nat_field := None; nat_map := None; nat_src := None;
     nat_extra := extra; nat_kind := kind; nat_family := fam; nat_flags := flags |}.

Definition masq_spec (family : string) (flags : nat) : nat_spec :=
  empty_nat NKmasq (nat_l3_family family) NXnone flags.

(** `snat/dnat to <ipv4>[:<port>]`: only an IPv4 LITERAL target is modelled;
    a resolvable non-literal (defined symbol/map/concat we don't lower) stays a
    bare terminal Accept ([None]).  An undefined `$var` already failed loud at
    [resolve_sv]. *)
Definition addr_nat_spec (kind : nat_op) (port : option nat) (flags : nat)
    (v : svalue) : option nat_spec :=
  match v with
  | SVIp4 b =>
      let '(extra, f) :=
        match port with
        | Some p => (NXimm None (Some (port_bytes p)) None, Nat.lor flags 2)
        | None => (NXnone, flags)
        end in
      Some {| nat_addr_imm := Some b; nat_field := None; nat_map := None;
              nat_src := None; nat_extra := extra; nat_kind := kind;
              nat_family := NFip4; nat_flags := f |}
  | _ => None
  end.

(** Port-only `snat/dnat to :<port>`: no address operand (PROTO_SPECIFIED). *)
Definition portonly_nat_spec (family : string) (kind : nat_op) (flags : nat)
    (port : nat) : nat_spec :=
  empty_nat kind (nat_l3_family family)
            (NXimm None (Some (port_bytes port)) None) (Nat.lor flags 2).

Definition redir_spec (flags : nat) (port : option nat) : nat_spec :=
  match port with
  | Some p => empty_nat NKredir NFip4 (NXimm None (Some (port_bytes p)) None) (Nat.lor flags 2)
  | None => empty_nat NKredir NFip4 NXnone flags
  end.

(** `tproxy [ip|ip6] to <ipv4>[:<port>]` — an explicit ip/ip6 qualifier wins;
    otherwise the enclosing table's L3 family (ip/ip6), or "" for a multi-L3
    (inet/bridge/netdev) table.  Only an IPv4 literal target is modelled. *)
Definition mk_tproxy (family qual : string) (addr : option svalue)
    (port : option nat) : lres tproxy_spec :=
  let tp_fam :=
    if negb (String.eqb qual "") then qual
    else if String.eqb family "ip" then "ip"
    else if String.eqb family "ip6" then "ip6"
    else "" in
  match addr with
  | None => LOk {| tp_addr := None; tp_port := option_map port_bytes port;
                   tp_portmap := None; tp_family := tp_fam |}
  | Some (SVIp4 b) => LOk {| tp_addr := Some b; tp_port := option_map port_bytes port;
                             tp_portmap := None; tp_family := tp_fam |}
  | Some _ => LErr LEtproxyTarget
  end.

(* ---------- verdict / statement lowering ---------- *)

Definition lower_sverdict (v : sverdict) : verdict :=
  match v with
  | SVaccept => Accept
  | SVdrop => Drop
  | SVcontinue => Continue
  | SVreturn => Return
  | SVjump c => Jump c
  | SVgoto c => Goto c
  | SVqueue lo hi byp fan => Queue lo hi byp fan
  | SVreject _ => Reject 0 0
  end.

(** One statement to a [stmt] (or [None] for verdict-neutral metadata /
    terminal NAT, which the driver handles as a rule OUTCOME).  Values are
    already define-expanded by the caller. *)
Definition lower_stmt (s : sstmt) : lres (option stmt) :=
  match s with
  | StComment _ => LOk None
  | StCounter pkts bytes => LOk (Some (SCounter pkts bytes))
      (* `counter packets N bytes N` — the initial values reach the compiled
         [SCounter] (kernel: nft_counter_init seeds the counter from the
         declaration; net/netfilter/nft_counter.c) *)
  | StObjref k name => LOk (Some (SObjref (objkind_otype k) name))
      (* `counter name X` / `quota name X` / `ct helper set X` etc. -> an
         objref carrying the NFT_OBJECT_* type (src/statement.c objref_stmt) *)
  | StLog opts => LOk (Some (SLog (canon_log_opts opts)))
  | StNotrack => LOk (Some SNotrack)
  | StMetaSet k v => st <-- lower_meta_set k v ;; LOk (Some st)
  | StCtSet k v => st <-- lower_ct_set k v ;; LOk (Some st)
  | StLimit _ _ _ _ _ => LOk None       (* intercepted as MLimit by the driver *)
  | StMasquerade _ | StSnat _ _ _ | StDnat _ _ _
  | StRedirect _ _ | StTproxy _ _ _ => LOk None   (* terminal outcome *)
  end.

(* ------------------------------------------------------------------ *)
(** ** Byte-pin witnesses (vm_compute): the verified lowering produces the
    HISTORICAL bytes the golden corpus / byteorder-gate / difftest check
    end-to-end.  Two spellings of one constant hit the identical typed term
    (the M-B same-typed-term guarantee, now at the LOWERING level). *)

Definition mrhs (op : srelop) (neg : bool) (se : ssetexpr) : srhs :=
  mkSrhs op neg se.

(** `ct state 2` and `ct state established` lower to the SAME typed term. *)
Example lower_ct_state_same_term :
  lower_match (mkSmatch [["ct"; "state"]]
                 (mrhs SOpImplicit false (SSEvalue (SVSym "established"))))
  = lower_match (mkSmatch [["ct"; "state"]]
                   (mrhs SOpImplicit false (SSEvalue (SVNum 2))))
  /\ lower_match (mkSmatch [["ct"; "state"]]
                    (mrhs SOpImplicit false (SSEvalue (SVNum 2))))
     = LOk ([], TXBitmask FCtState DTct_state SOpImplicit [2%N]).
Proof. vm_compute. split; reflexivity. Qed.

(** ...and its elaboration is the documented implicit-bitmask bytes. *)
Example lower_ct_state_bytes :
  match lower_match (mkSmatch [["ct"; "state"]]
                       (mrhs SOpImplicit false (SSEvalue (SVSym "established"))))
  with
  | LOk (deps, tx) => (deps, elab_tx tx)
  | LErr _ => ([], MEq FCtState [])
  end
  = ([], MMasked FCtState CNe [0;0;0;2] [0;0;0;0] [0;0;0;0]).
Proof. vm_compute. reflexivity. Qed.

(** The comma OR-list `ct state new,established` (evaluate.c mpz_ior). *)
Example lower_ct_state_comma :
  lower_match (mkSmatch [["ct"; "state"]]
                 (mrhs SOpImplicit false
                    (SSElist [SVSym "new"; SVSym "established"])))
  = LOk ([], TXBitmask FCtState DTct_state SOpImplicit [8%N; 2%N]).
Proof. vm_compute. reflexivity. Qed.

(** `tcp dport ssh-https` — symbol-resolved big-endian range with the tcp
    l4proto guard. *)
Example lower_port_range :
  lower_match (mkSmatch [["tcp"; "dport"]]
                 (mrhs SOpImplicit false
                    (SSEvalue (SVRange (SVSym "ssh") (SVSym "https")))))
  = LOk ([DepL4 6],
         TXRange FThDport DTinet_service false (VPort 22) (VPort 443)).
Proof. vm_compute. reflexivity. Qed.

(** `ct mark 0x32-0x45` — the hton path with big-endian bounds. *)
Example lower_ctmark_range :
  match lower_match (mkSmatch [["ct"; "mark"]]
                       (mrhs SOpImplicit false
                          (SSEvalue (SVRange (SVNum 0x32) (SVNum 0x45)))))
  with LOk (_, tx) => elab_tx tx | LErr _ => MEq FCtMark [] end
  = MRangeT FCtMark [TByteorder true 4 4] false [0;0;0;0x32] [0;0;0;0x45].
Proof. vm_compute. reflexivity. Qed.

(** `ip dscp cs1` — mask/shift computed in Coq, the golden 0xfc / 0x20. *)
Example lower_dscp_cs1 :
  match lower_single ["ip"; "dscp"]
          (mrhs SOpImplicit false (SSEvalue (SVSym "cs1")))
  with LOk (deps, tx) => Some (deps, elab_tx tx) | LErr _ => None end
  = Some ([DepNfproto 2],
          MMasked (FPayload PNetwork 1 1) CEq [0xfc] [0] [0x20]).
Proof. vm_compute. reflexivity. Qed.

(** `ip dscp 64` is REFUSED (nft: value exceeds range 0-63); the historical
    frontend silently truncated. *)
Example lower_dscp_64_refused :
  lower_single ["ip"; "dscp"] (mrhs SOpImplicit false (SSEvalue (SVNum 64)))
  = LErr (LEbitfieldRange "ip dscp").
Proof. vm_compute. reflexivity. Qed.

(** Every bitfield mask/shift re-derived in Coq equals the frontend's old
    hand-written byte table (all 13 rows). *)
Example bitfield_masks_pin :
  map (fun kp => match bitfield kp with
                 | Some s => bf_mask s
                 | None => []
                 end)
      [["ip";"version"]; ["ip";"hdrlength"]; ["ip";"dscp"]; ["ip6";"dscp"];
       ["ip6";"flowlabel"]; ["tcp";"doff"]; ["vlan";"id"]; ["vlan";"pcp"];
       ["vlan";"dei"]; ["vlan";"cfi"]; ["frag";"frag-off"];
       ["frag";"reserved2"]; ["frag";"more-fragments"]]
  = [[0xf0]; [0x0f]; [0xfc]; [0x0f;0xc0]; [0x0f;0xff;0xff]; [0xf0];
     [0x0f;0xff]; [0xe0]; [0x10]; [0x10]; [0xff;0xf8]; [0x06]; [0x01]].
Proof. vm_compute. reflexivity. Qed.

(** Presence forms. *)
Example lower_fib_missing :
  lower_single ["fib"; "daddr"; "type"]
    (mrhs SOpImplicit false (SSEvalue (SVSym "missing")))
  = LOk ([], TXFlag (FFib "daddr" FRpresent) false 0).
Proof. vm_compute. reflexivity. Qed.
Example lower_exthdr_exists :
  lower_single ["exthdr"; "frag"]
    (mrhs SOpImplicit false (SSEvalue (SVSym "exists")))
  = LOk ([DepNfproto 10], TXFlag (FExthdr EPipv6 44 0 1 true) false 1).
Proof. vm_compute. reflexivity. Qed.

(** Class D regression: `exthdr hbh != exists` threads the `!=` (neg = true)
    so the present-flag compare is `cmp NEQ 0x01`, the COMPLEMENT of the
    historical `cmp eq 0x01` (which silently dropped the operator). *)
Example lower_exthdr_neq_exists :
  match lower_single ["exthdr"; "hbh"]
          (mrhs SOpNe true (SSEvalue (SVSym "exists")))
  with LOk (deps, tx) => (deps, tx, elab_tx tx) | LErr _ => ([], TXFlag FCtId false 0, MEq FCtId []) end
  = ([DepNfproto 10], TXFlag (FExthdr EPipv6 0 0 1 true) true 1,
     MNeq (FExthdr EPipv6 0 0 1 true) [1]).
Proof. vm_compute. reflexivity. Qed.

(** Class D regression, the CORPUS-INVISIBLE twin: `tcp option sack != exists`
    (tcpopt 5) is `cmp NEQ 0x01` too — no corpus block exercises it, so this is
    its only guard. *)
Example lower_tcpopt_neq_exists :
  match lower_single ["tcpopt"; "sack"]
          (mrhs SOpNe true (SSEvalue (SVSym "exists")))
  with LOk (deps, tx) => (deps, tx, elab_tx tx) | LErr _ => ([], TXFlag FCtId false 0, MEq FCtId []) end
  = ([], TXFlag (FExthdr EPtcpopt 5 0 1 true) true 1,
     MNeq (FExthdr EPtcpopt 5 0 1 true) [1]).
Proof. vm_compute. reflexivity. Qed.
Example lower_tcpopt_exists_positive :
  match lower_single ["tcpopt"; "sack"]
          (mrhs SOpImplicit false (SSEvalue (SVSym "exists")))
  with LOk (_, tx) => elab_tx tx | LErr _ => MEq FCtId [] end
  = MEq (FExthdr EPtcpopt 5 0 1 true) [1].
Proof. vm_compute. reflexivity. Qed.

(** Class B regression: `meta length 33-45` (a [DThostint 4] ordered range)
    takes the mandatory hton path — `byteorder hton` + big-endian bounds — not
    the historical plain host-LE [MRange]. *)
Example lower_metalen_range :
  match lower_single ["meta"; "length"]
          (mrhs SOpImplicit false (SSEvalue (SVRange (SVNum 33) (SVNum 45))))
  with LOk (_, tx) => elab_tx tx | LErr _ => MEq FMetaLen [] end
  = MRangeT FMetaLen [TByteorder true 4 4] false [0;0;0;33] [0;0;0;45].
Proof. vm_compute. reflexivity. Qed.

(** Class C regression: `ct expiration 33-45` — SECONDS scaled to MILLISECONDS
    (33->33000, 45->45000) AND the hton path (host-endian ct register).
    33000 = 0x80e8, 45000 = 0xafc8 (golden any/ct.t.payload). *)
Example lower_ctexpiration_range :
  match lower_single ["ct"; "expiration"]
          (mrhs SOpImplicit false (SSEvalue (SVRange (SVNum 33) (SVNum 45))))
  with LOk (_, tx) => elab_tx tx | LErr _ => MEq FCtExpiration [] end
  = MRangeT FCtExpiration [TByteorder true 4 4] false
      [0;0;0x80;0xe8] [0;0;0xaf;0xc8].
Proof. vm_compute. reflexivity. Qed.
Example lower_ctexpiration_neq :
  match lower_single ["ct"; "expiration"]
          (mrhs SOpNe true (SSEvalue (SVNum 233)))
  with LOk (_, tx) => elab_tx tx | LErr _ => MEq FCtExpiration [] end
  = MNeq FCtExpiration [0x28;0x8e;0x03;0x00].    (* 233000 host-endian (LE) *)
Proof. vm_compute. reflexivity. Qed.

(** Class E regression: `reject with tcp reset` carries the `meta l4proto 6`
    guard so the RST cannot fire on non-TCP; a bare/icmp reject does not. *)
Example reject_dep_tcp_reset : reject_dep "tcp reset" = [DepL4 6].
Proof. reflexivity. Qed.
Example reject_dep_bare : reject_dep "" = [].
Proof. reflexivity. Qed.

(** Class N regression: `ct label set 127` sets BIT 127 of the 128-bit bitmap
    and serialises it host-endian (src/ct.c mpz_export_data BYTEORDER_HOST_ENDIAN)
    — so bit 127 lands in byte 15 (register bytes `00..00 0x80`), NOT the literal
    16-byte integer 127 and NOT the big-endian byte-0 layout.  Live nft dumps
    this immediate as `0x00000000 0x00000000 0x00000000 0x80000000`; the kernel
    reads it back as `ct label set 127`.  [N_to_data 16] is [N] arithmetic, so
    2^127 does not wrap (the OCaml `lsl`-on-63-bit shift-wrap half of bug N is
    dead). *)
Example lower_ct_label_set_127 :
  lower_ct_set "label" (SVNum 127)      (* bit 127 = MSB = byte 15 host-endian *)
  = LOk (SCtSet CKlabel (VImm [0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;128])).
Proof. vm_compute. reflexivity. Qed.
Example lower_ct_label_set_0 :
  lower_ct_set "label" (SVNum 0)        (* bit 0 = LSB = byte 0 host-endian *)
  = LOk (SCtSet CKlabel (VImm [1;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0])).
Proof. vm_compute. reflexivity. Qed.
Example lower_ct_label_set_overflow :
  lower_ct_set "label" (SVNum 128)
  = LErr (LEctSet "label bit index exceeds 127").
Proof. vm_compute. reflexivity. Qed.

(** The wildcard/exact ifname split survives the verified path. *)
Example lower_ifname_wildcard :
  lower_match (mkSmatch [["iifname"]]
                 (mrhs SOpImplicit false (SSEvalue (SVStr "dummy*"))))
  = LOk ([], TXWildcard FMetaIifname [100;117;109;109;121]).
Proof. vm_compute. reflexivity. Qed.
Example lower_ifname_exact :
  lower_match (mkSmatch [["iifname"]]
                 (mrhs SOpImplicit false (SSEvalue (SVStr "eth0"))))
  = LOk ([], TXEq FMetaIifname
           (VIfname [101;116;104;48; 0;0;0;0; 0;0;0;0; 0;0;0;0])).
Proof. vm_compute. reflexivity. Qed.

(** `iifname & 0xff` cannot lower (no integer basetype — M-B acceptance). *)
Example lower_bitmatch_ifname_refused :
  lower_bitmatch ["iifname"] "and" (SVNum 255)
    (mrhs SOpEq false (SSEvalue (SVNum 1)))
  = LErr LEbitwiseNonInteger.
Proof. vm_compute. reflexivity. Qed.

(** `meta mark and 0x3 == 0x1` lowers; guard values are Coq-encoded. *)
Example lower_bitmatch_mark :
  lower_bitmatch ["meta"; "mark"] "and" (SVNum 3)
    (mrhs SOpEq false (SSEvalue (SVNum 1)))
  = LOk ([], TXBitwise FMetaMark DTmark BOand false
               (VHostInt 4 3) (VHostInt 4 1)).
Proof. vm_compute. reflexivity. Qed.

(** Compound flag masks: `tcp flags & (fin|syn|rst|ack) == syn | ack` — the
    parenthesized OR mask and the bare OR compare value each arrive as an
    UNRESOLVED [SVOr] group; the symbol lookup and the OR-fold both happen in
    [Typecheck.resolve_value], so the lowering sees 0x17/0x12 already folded
    (golden inet/tcp.t.payload:441-447: `bitwise reg1 = (reg1 & 0x17) ^ 0x00;
    cmp eq reg1 0x12`, over the tcp dep). *)
Example lower_bitmatch_tcpflags_compound :
  lower_bitmatch ["tcp"; "flags"] "and"
    (SVOr [SVSym "fin"; SVSym "syn"; SVSym "rst"; SVSym "ack"])
    (mrhs SOpEq false (SSEvalue (SVOr [SVSym "syn"; SVSym "ack"])))
  = LOk (dep_l4 "tcp", TXBitwise FTcpFlags DTtcp_flag BOand false
                         (VInteger 1 0x17) (VInteger 1 0x12)).
Proof. vm_compute. reflexivity. Qed.

(** `tcp flags & (...) ! syn` stays an nft syntax error (inet/tcp.t:90). *)
Example lower_bitmatch_bang_refused :
  lower_bitmatch ["tcp"; "flags"] "and"
    (SVOr [SVSym "fin"; SVSym "syn"; SVSym "rst"; SVSym "ack"])
    (mrhs SOpBang true (SSEvalue (SVSym "syn")))
  = LErr (LEbitwiseOp "!").
Proof. vm_compute. reflexivity. Qed.

(** Guard encoding: the icmp selector's two guards (nfproto THEN l4proto),
    family-aware — real matches in inet, none in the single-L3 ip family. *)
Example dep_guard_icmp_inet :
  map (dep_guard "inet" false) (dep_l4 "icmp")
  = [LOk (DAguard true FMetaNfproto [2]
            (TXEq FMetaNfproto (VInteger 1 2)));
     LOk (DAguard false FMetaL4proto [1]
            (TXEq FMetaL4proto (VInteger 1 1)))].
Proof. vm_compute. reflexivity. Qed.
Example dep_guard_ip_family_noop :
  dep_guard "ip" false (DepNfproto 2) = LOk DAnone.
Proof. vm_compute. reflexivity. Qed.
Example dep_guard_bridge_ethertype :
  dep_guard "bridge" false (DepNfproto 2)
  = LOk (DAguard true FMetaProtocol [8; 0]
           (TXEq FMetaProtocol (VInteger 2 0x0800))).
Proof. vm_compute. reflexivity. Qed.
Example dep_guard_vlan_netdev_refused :
  dep_guard "netdev" false (DepEther 0x8100) = LErr LEvlanNetdev.
Proof. vm_compute. reflexivity. Qed.

(** Class-G regression pins (bridge/netdev in-frame ethertype network guard).
    A transport-implied network guard (`icmp type`) in bridge reads the ethertype
    with `payload load 2b @ link header + 12`, NOT `meta protocol`
    (golden bridge/icmpX.t.payload). *)
Example dep_guard_bridge_netll_icmp :
  dep_guard "bridge" false (DepNetLL 2)
  = LOk (DAguard true (FPayload PLink 12 2) [8; 0]
           (TXEq (FPayload PLink 12 2) (VInteger 2 0x0800))).
Proof. vm_compute. reflexivity. Qed.
(** In netdev the same transport-implied guard uses proto_netdev's `meta protocol`
    (golden any/icmpX.t.netdev.payload). *)
Example dep_guard_netdev_netll_icmp :
  dep_guard "netdev" false (DepNetLL 2)
  = LOk (DAguard true FMetaProtocol [8; 0]
           (TXEq FMetaProtocol (VInteger 2 0x0800))).
Proof. vm_compute. reflexivity. Qed.
(** After a vlan tag (proto_vlan context) the ethertype read moves to +16, in
    BOTH L2 families, for a DIRECT `ip` network selector too
    (golden bridge/vlan.t.payload{,.netdev}). *)
Example dep_guard_bridge_vlan_ip :
  dep_guard "bridge" true (DepNfproto 2)
  = LOk (DAguard true (FPayload PLink 16 2) [8; 0]
           (TXEq (FPayload PLink 16 2) (VInteger 2 0x0800))).
Proof. vm_compute. reflexivity. Qed.
Example dep_guard_netdev_vlan_ip :
  dep_guard "netdev" true (DepNfproto 2)
  = LOk (DAguard true (FPayload PLink 16 2) [8; 0]
           (TXEq (FPayload PLink 16 2) (VInteger 2 0x0800))).
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(** ** M3 byte-pin witnesses: the set/map/vmap composition and its interning
    produce the HISTORICAL bytes (golden corpus / gen-check pin them e2e). *)

(** Decimal naming computes as expected (extraction uses [string_of_int]). *)
Example nat_dec_pins : (nat_dec 0, nat_dec 7, nat_dec 42) = ("0", "7", "42").
Proof. vm_compute. reflexivity. Qed.

(** A ct-state set `{ established, related }` interns as `__set0` over
    big-endian 4-byte points (no hton — an exact set). *)
Example lower_anon_set_ctstate :
  lower_anon_set ls0 FCtState DTct_state false
    [SVSym "established"; SVSym "related"]
  = LOk (mkLstate 1 [("__set0", [([0;0;0;2],[0;0;0;2]); ([0;0;0;4],[0;0;0;4])])] [] [],
         MConcatSet [FCtState] false "__set0").
Proof. vm_compute. reflexivity. Qed.

(** `ct state 2` and `ct state established` intern the IDENTICAL bytes. *)
Example lower_anon_set_same_bytes :
  lower_anon_set ls0 FCtState DTct_state false [SVSym "established"]
  = lower_anon_set ls0 FCtState DTct_state false [SVNum 2].
Proof. vm_compute. reflexivity. Qed.

(** A mark set `{ 0x100-0x200 }` over the host-endian mark field takes the hton
    [MSetT] path with BIG-endian interval bounds. *)
Example lower_anon_set_mark_interval :
  lower_anon_set ls0 FMetaMark DTmark false [SVRange (SVNum 0x100) (SVNum 0x200)]
  = LOk (mkLstate 1
           [("__set0", [([0;0;1;0],[0;0;2;0])])] [] [],
         MSetT FMetaMark [TByteorder true 4 4] false "__set0").
Proof. vm_compute. reflexivity. Qed.

(** An exact mark set `{ 0x99 }` stays the memcmp [MConcatSet] path with the
    host-endian (little-endian) point bytes — no hton. *)
Example lower_anon_set_mark_exact :
  lower_anon_set ls0 FMetaMark DTmark false [SVNum 0x99]
  = LOk (mkLstate 1 [("__set0", [([0x99;0;0;0],[0x99;0;0;0])])] [] [],
         MConcatSet [FMetaMark] false "__set0").
Proof. vm_compute. reflexivity. Qed.

(** A tcp-flags brace set is refused (brace-vs-OR ambiguity — fail loud). *)
Example lower_anon_set_tcpflags_refused :
  lower_anon_set ls0 FTcpFlags DTtcp_flag false [SVSym "syn"; SVSym "ack"]
  = LErr LEtcpflagSet.
Proof. vm_compute. reflexivity. Qed.

(** A single-field port set with a range `{ 22, 80-88 }`. *)
Example lower_anon_set_port_range :
  lower_anon_set ls0 FThDport DTinet_service false
    [SVNum 22; SVRange (SVNum 80) (SVNum 88)]
  = LOk (mkLstate 1
           [("__set0", [([0;22],[0;22]); ([0;80],[0;88])])] [] [],
         MConcatSet [FThDport] false "__set0").
Proof. vm_compute. reflexivity. Qed.

(** A CIDR set element `{ 192.168.0.0/16 }` expands to net .. broadcast. *)
Example lower_anon_set_cidr :
  lower_anon_set ls0 FIp4Saddr DTipv4 false [SVPrefix (SVIp4 [192;168;0;0]) 16]
  = LOk (mkLstate 1
           [("__set0", [([192;168;0;0],[192;168;255;255])])] [] [],
         MConcatSet [FIp4Saddr] false "__set0").
Proof. vm_compute. reflexivity. Qed.

(** A concatenated SET element `1.2.3.4 . eth0` is per-field slot-padded: the
    4-byte address fills its slot, the 16-byte ifname its slots (4+16 = 20). *)
Example lower_concat_set_padded :
  lower_concat_set ls0 [FIp4Daddr; FMetaOifname] [DTipv4; DTifname] false
    [SVConcat [SVIp4 [1;2;3;4]; SVStr "eth0"]]
  = LOk (mkLstate 1
           [("__set0", [([1;2;3;4; 101;116;104;48; 0;0;0;0; 0;0;0;0; 0;0;0;0],
                         [1;2;3;4; 101;116;104;48; 0;0;0;0; 0;0;0;0; 0;0;0;0])])] [] [],
         MConcatSet [FIp4Daddr; FMetaOifname] false "__set0").
Proof. vm_compute. reflexivity. Qed.

(** A concatenated VMAP key `tcp . 22` is FLAT (unpadded): 1-byte protocol +
    2-byte port = 3 bytes, no slot padding. *)
Example vmap_entries_concat_flat :
  vmap_entries_concat [DTinet_proto; DTinet_service]
    [(SVConcat [SVSym "tcp"; SVNum 22], Verdict.Accept)]
  = LOk [([6;0;22],[6;0;22], Verdict.Accept)].
Proof. vm_compute. reflexivity. Qed.

(** Interning dedups by content: the SAME set interned twice keeps one name. *)
Example intern_dedup :
  let '(n1, st1) := intern_set ls0 [([0;22],[0;22])] in
  let '(n2, st2) := intern_set st1 [([0;22],[0;22])] in
  (n1, n2, ls_ctr st2) = ("__set0", "__set0", 1).
Proof. vm_compute. reflexivity. Qed.

(** A declared concatenated set element with a per-field CIDR. *)
Example decl_set_concat_cidr :
  decl_set_elems ["ipv4_addr"; "inet_service"]
    [SVConcat [SVPrefix (SVIp4 [10;0;0;0]) 8; SVNum 53]]
  = LOk [([10;0;0;0; 0;53; 0;0], [10;255;255;255; 0;53; 0;0])].
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(** ** M4: the whole-ruleset driver [lower_ruleset].

    Mirrors the historical OCaml [lower_rule]/[lower_chain]/[lower] loop
    exactly (clause order, dependency-guard dedup, discharge, outcome
    assembly, declaration-then-chain interning order) but composes NO byte:
    every match/set/statement/terminal value is the verified lowering above.
    The OCaml frontend becomes [Nft_inject] (pure structural injection + the
    ifindex oracle) plus a call to this function. *)

(* ---------- guard-field equality (the small fixed set of dep fields) ---------- *)

(** Only the implicit-guard fields ever enter the per-rule dedup set (from
    [dep_guard]/[discharge]): the L3/L2/L4 protocol and link guards.  A total
    equality on them (others never occur, so [false] is correct). *)
Definition gfield_eqb (a b : field) : bool :=
  match a, b with
  | FMetaL4proto, FMetaL4proto => true
  | FMetaNfproto, FMetaNfproto => true
  | FMetaProtocol, FMetaProtocol => true
  | FMetaIiftype, FMetaIiftype => true
  | FEtherType, FEtherType => true
  | _, _ => false
  end.

Definition pair_mem (p : field * data) (l : list (field * data)) : bool :=
  existsb (fun q => andb (gfield_eqb (fst q) (fst p)) (data_eqb (snd q) (snd p))) l.

Fixpoint dedup_add (news deps : list (field * data)) : list (field * data) :=
  match news with
  | nil => deps
  | p :: r => dedup_add r (if pair_mem p deps then deps else p :: deps)
  end.

(* ---------- file-level and rule-level lowering state ---------- *)

Record fstate : Type := mkFstate {
  fs_ls    : lstate;                       (* interning (threaded) *)
  fs_typed : list (matchcond * txmatch);   (* typed views (per lowered match) *)
  fs_deps  : list matchcond }.             (* which matchconds are dep guards *)

Record rloc : Type := mkRloc {
  rl_body    : list body_item;      (* reversed accumulation *)
  rl_deps    : list (field * data); (* guard dedup set *)
  rl_verdict : verdict;
  rl_vmap    : option vmap_spec;
  rl_nat     : option nat_spec;
  rl_tproxy  : option tproxy_spec }.

Definition rl0 : rloc := mkRloc nil nil Continue None None None.

Definition rl_with_verdict (v : verdict) (rl : rloc) : rloc :=
  mkRloc (rl_body rl) (rl_deps rl) v (rl_vmap rl) (rl_nat rl) (rl_tproxy rl).
Definition rl_with_nat (n : option nat_spec) (rl : rloc) : rloc :=
  mkRloc (rl_body rl) (rl_deps rl) (rl_verdict rl) (rl_vmap rl) n (rl_tproxy rl).
Definition rl_with_tproxy (t : option tproxy_spec) (rl : rloc) : rloc :=
  mkRloc (rl_body rl) (rl_deps rl) (rl_verdict rl) (rl_vmap rl) (rl_nat rl) t.
Definition rl_with_vmap (m : option vmap_spec) (rl : rloc) : rloc :=
  mkRloc (rl_body rl) (rl_deps rl) (rl_verdict rl) m (rl_nat rl) (rl_tproxy rl).
Definition rl_push (bi : body_item) (rl : rloc) : rloc :=
  mkRloc (bi :: rl_body rl) (rl_deps rl) (rl_verdict rl) (rl_vmap rl) (rl_nat rl) (rl_tproxy rl).
Definition rl_set_deps (d : list (field * data)) (rl : rloc) : rloc :=
  mkRloc (rl_body rl) d (rl_verdict rl) (rl_vmap rl) (rl_nat rl) (rl_tproxy rl).

(** Register a Coq-lowered typed match, remembering its typed source view. *)
Definition fs_coq_mc (fs : fstate) (tx : txmatch) : matchcond * fstate :=
  let mc := elab_tx tx in
  (mc, mkFstate (fs_ls fs) ((mc, tx) :: fs_typed fs) (fs_deps fs)).

(** Register a synthesized dependency guard (typed + tagged as a dep). *)
Definition fs_reg_dep (fs : fstate) (tm : txmatch) : matchcond * fstate :=
  let mc := elab_tx tm in
  (mc, mkFstate (fs_ls fs) ((mc, tm) :: fs_typed fs) (mc :: fs_deps fs)).

(* ---------- implicit dependency guard materialisation ---------- *)

(** nft emits ONE network-layer guard per rule, whatever SHAPE it takes: the L2
    in-frame ethertype guard has three interchangeable spellings — `meta protocol`
    (proto_netdev), `payload @ link+12` (proto_eth) and `payload @ link+16`
    (proto_vlan) — that all pin the same protocol base, so a later network guard is
    dropped once ANY of them is present (payload.c pctx->protocol[base] is set once).
    [layer_class f] is the set of fields that share [f]'s protocol layer for the
    once-per-layer dedup; the inet `meta nfproto` guard is its own class. *)
Definition layer_class (f : field) : list field :=
  match f with
  | FMetaNfproto => [FMetaNfproto]
  | FMetaProtocol | FPayload PLink 12 2 | FPayload PLink 16 2 =>
      [FMetaProtocol; FPayload PLink 12 2; FPayload PLink 16 2]
  | _ => [f]
  end.

Definition push_guard (da : dep_action) (rl : rloc) (fs : fstate) : rloc * fstate :=
  match da with
  | DAnone => (rl, fs)
  | DAguard layer f key tm =>
      let dup :=
        if layer then existsb (fun p => existsb (gfield_eqb (fst p)) (layer_class f)) (rl_deps rl)
        else existsb (fun p => andb (gfield_eqb (fst p) f) (data_eqb (snd p) key)) (rl_deps rl) in
      if dup then (rl, fs)
      else let '(mc, fs') := fs_reg_dep fs tm in
           (rl_push (BMatch mc) (rl_set_deps ((f, key) :: rl_deps rl) rl), fs')
  end.

(** A vlan tag (`ether type == 0x8100`, whether from the `vlan` selector's
    [DepEther] guard or an explicit `ether type vlan` discharged into the dedup
    set) shifts subsequent in-frame protocol reads past the 4-byte tag: nft's
    proto context becomes proto_vlan.  Detected from the per-rule guard set. *)
Definition rloc_vlan (rl : rloc) : bool :=
  existsb (fun p => andb (gfield_eqb (fst p) FEtherType)
                         (data_eqb (snd p) (N_to_data 2 0x8100)))
          (rl_deps rl).

Fixpoint ensure_dep (family : string) (ds : list depspec) (rl : rloc) (fs : fstate)
  : lres (rloc * fstate) :=
  match ds with
  | nil => LOk (rl, fs)
  | d :: rest =>
      match dep_guard family (rloc_vlan rl) d with
      | LErr e => LErr e
      | LOk da => let '(rl', fs') := push_guard da rl fs in
                  ensure_dep family rest rl' fs'
      end
  end.

(* ---------- selector helpers ---------- *)

Definition sel_deps (kp : skeypath) : list depspec :=
  match selector kp with Some (_, _, d) => d | None => nil end.

Definition sel_field_dt (kp : skeypath) : lres (field * dtype) :=
  match selector kp with
  | Some (f, dt, _) => LOk (f, dt)
  | None => LErr (LEselector kp)
  end.

(* ---------- the ifindex oracle hook (iif/oif interface NAME -> index) ---------- *)

Definition is_iifoif (kp : skeypath) : bool :=
  match kp with
  | ("iif" :: nil) | ("oif" :: nil) => true
  | ("meta" :: "iif" :: nil) | ("meta" :: "oif" :: nil) => true
  | _ => false
  end.

Definition oracle_name_rewrite (oracle : string -> option nat)
    (kp : skeypath) (v : svalue) : svalue :=
  if is_iifoif kp then
    match v with
    | SVSym s | SVStr s => match oracle s with Some n => SVNum n | None => v end
    | _ => v
    end
  else v.

(* ---------- one match clause ---------- *)

Definition driver_match (oracle : string -> option nat) (fuel : nat)
    (defs : list (string * svalue)) (m : smatch) (fs : fstate)
  : lres (list depspec * matchcond * fstate) :=
  let neg := sr_neg (sm_rhs m) in
  r <-- resolve_rhs fuel defs (sm_rhs m) ;;
  match sm_keys m with
  | kp :: nil =>
      match sr_payload r with
      | SSEref name =>
          match selector kp with
          | Some (f, _, deps) => LOk (deps, lower_set_ref [f] neg name, fs)
          | None => LErr (LEselector kp)
          end
      | SSEset elems =>
          match selector kp with
          | Some (f, dt, deps) =>
              match lower_anon_set (fs_ls fs) f dt neg elems with
              | LOk (ls', mc) => LOk (deps, mc, mkFstate ls' (fs_typed fs) (fs_deps fs))
              | LErr e => LErr e
              end
          | None => LErr (LEselector kp)
          end
      | SSEvalue (SVSet elems) =>
          match selector kp with
          | Some (f, dt, deps) =>
              match lower_anon_set (fs_ls fs) f dt neg elems with
              | LOk (ls', mc) => LOk (deps, mc, mkFstate ls' (fs_typed fs) (fs_deps fs))
              | LErr e => LErr e
              end
          | None => LErr (LEselector kp)
          end
      | SSEvalue v =>
          let v' := oracle_name_rewrite oracle kp v in
          match lower_match (mkSmatch (kp :: nil)
                              (mkSrhs (sr_op r) neg (SSEvalue v'))) with
          | LOk (deps, tx) => let '(mc, fs') := fs_coq_mc fs tx in LOk (deps, mc, fs')
          | LErr e => LErr e
          end
      | SSElist _ =>
          match lower_match (mkSmatch (kp :: nil) r) with
          | LOk (deps, tx) => let '(mc, fs') := fs_coq_mc fs tx in LOk (deps, mc, fs')
          | LErr e => LErr e
          end
      end
  | kps =>
      infos <-- map_lres sel_field_dt kps ;;
      let fields := map fst infos in
      let dts := map snd infos in
      let dep := List.concat (map sel_deps kps) in
      match sr_payload r with
      | SSEref nm => LOk (dep, lower_set_ref fields neg nm, fs)
      | SSEset elems =>
          match lower_concat_set (fs_ls fs) fields dts neg elems with
          | LOk (ls', mc) => LOk (dep, mc, mkFstate ls' (fs_typed fs) (fs_deps fs))
          | LErr e => LErr e
          end
      | SSEvalue (SVConcat vs) =>
          match lower_concat_set (fs_ls fs) fields dts neg (SVConcat vs :: nil) with
          | LOk (ls', mc) => LOk (dep, mc, mkFstate ls' (fs_typed fs) (fs_deps fs))
          | LErr e => LErr e
          end
      | SSElist _ => LErr LEconcatRhs
      | SSEvalue _ => LErr LEconcatRhs
      end
  end.

(* ---------- statement value resolution + terminal handling ---------- *)

Definition resolve_optsv (fuel : nat) (defs : list (string * svalue))
    (o : option svalue) : lres (option svalue) :=
  match o with
  | None => LOk None
  | Some v => v' <-- resolve_sv fuel defs v ;; LOk (Some v')
  end.

Definition resolve_stmt (fuel : nat) (defs : list (string * svalue)) (s : sstmt)
  : lres sstmt :=
  match s with
  | StMetaSet k v => v' <-- resolve_sv fuel defs v ;; LOk (StMetaSet k v')
  | StCtSet k v => v' <-- resolve_sv fuel defs v ;; LOk (StCtSet k v')
  | StSnat a p f => a' <-- resolve_optsv fuel defs a ;; LOk (StSnat a' p f)
  | StDnat a p f => a' <-- resolve_optsv fuel defs a ;; LOk (StDnat a' p f)
  | StTproxy fam a p => a' <-- resolve_optsv fuel defs a ;; LOk (StTproxy fam a' p)
  | _ => LOk s
  end.

(** Terminal NAT/tproxy statements set the rule verdict (Accept) and the
    nat/tproxy outcome; [s] has its address already define-expanded. *)
Definition lower_terminal (family : string) (s : sstmt) (rl : rloc) : lres rloc :=
  let acc := rl_with_verdict Accept rl in
  match s with
  | StMasquerade fs =>
      flags <-- nat_flags_of fs ;; LOk (rl_with_nat (Some (masq_spec family flags)) acc)
  | StSnat (Some v) port fs =>
      flags <-- nat_flags_of fs ;; LOk (rl_with_nat (addr_nat_spec NKsnat port flags v) acc)
  | StDnat (Some v) port fs =>
      flags <-- nat_flags_of fs ;; LOk (rl_with_nat (addr_nat_spec NKdnat port flags v) acc)
  | StSnat None (Some port) fs =>
      flags <-- nat_flags_of fs ;; LOk (rl_with_nat (Some (portonly_nat_spec family NKsnat flags port)) acc)
  | StDnat None (Some port) fs =>
      flags <-- nat_flags_of fs ;; LOk (rl_with_nat (Some (portonly_nat_spec family NKdnat flags port)) acc)
  | StSnat None None _ => LOk acc
  | StDnat None None _ => LOk acc
  | StRedirect port fs =>
      flags <-- nat_flags_of fs ;; LOk (rl_with_nat (Some (redir_spec flags port)) acc)
  | StTproxy qual addr port =>
      tp <-- mk_tproxy family qual addr port ;; LOk (rl_with_tproxy (Some tp) acc)
  | _ => LOk rl
  end.

Definition lower_clause (oracle : string -> option nat) (fuel : nat)
    (family : string) (defs : list (string * svalue))
    (cl : sclause) (rl : rloc) (fs : fstate) : lres (rloc * fstate) :=
  match cl with
  | CVerdict (SVreject opts) =>
      p <-- ensure_dep family (reject_dep opts) rl fs ;;
      let '(rl1, fs1) := p in
      tc <-- reject_type_code family opts ;;
      let '(rt, rc) := tc in
      LOk (rl_with_verdict (Reject rt rc) rl1, fs1)
  | CVerdict v => LOk (rl_with_verdict (lower_sverdict v) rl, fs)
  | CMatch m =>
      r <-- driver_match oracle fuel defs m fs ;;
      let '(dep, mc, fs1) := r in
      p <-- ensure_dep family dep rl fs1 ;;
      let '(rl1, fs2) := p in
      LOk (rl_set_deps (dedup_add (discharge mc) (rl_deps rl1)) (rl_push (BMatch mc) rl1), fs2)
  | CBitmatch kp op mask r0 =>
      mask' <-- resolve_sv fuel defs mask ;;
      r' <-- resolve_rhs fuel defs r0 ;;
      match lower_bitmatch kp op mask' r' with
      | LErr e => LErr e
      | LOk (dep, tx) =>
          p <-- ensure_dep family dep rl fs ;;
          let '(rl1, fs1) := p in
          let '(mc, fs2) := fs_coq_mc fs1 tx in
          LOk (rl_push (BMatch mc) rl1, fs2)
      end
  | CVmap kps entries =>
      match rl_vmap rl with
      | Some _ => LErr LEmultiVmap
      | None =>
          infos <-- map_lres sel_field_dt kps ;;
          let fields := map fst infos in
          let dts := map snd infos in
          p <-- ensure_dep family (List.concat (map sel_deps kps)) rl fs ;;
          let '(rl1, fs1) := p in
          let '(name, ls') := fresh_map (fs_ls fs1) in
          coqents <-- map_lres (fun ve => let '(v, sv) := ve in
                        v' <-- resolve_sv fuel defs v ;; LOk (v', lower_sverdict sv)) entries ;;
          ents <-- (match dts with
                    | dt :: nil => vmap_entries_single dt coqents
                    | _ => vmap_entries_concat dts coqents
                    end) ;;
          let ls2 := add_vmap ls' name ents in
          let vm := match fields with
                    | f :: nil => {| vm_fields := nil; vm_keyf := Some (f, nil); vm_name := name |}
                    | _ => {| vm_fields := fields; vm_keyf := None; vm_name := name |}
                    end in
          LOk (rl_with_vmap (Some vm) rl1, mkFstate ls2 (fs_typed fs1) (fs_deps fs1))
      end
  | CVmapRef kps name =>
      match rl_vmap rl with
      | Some _ => LErr LEmultiVmap
      | None =>
          infos <-- map_lres sel_field_dt kps ;;
          let fields := map fst infos in
          p <-- ensure_dep family (List.concat (map sel_deps kps)) rl fs ;;
          let '(rl1, fs1) := p in
          let vm := match fields with
                    | f :: nil => {| vm_fields := nil; vm_keyf := Some (f, nil); vm_name := name |}
                    | _ => {| vm_fields := fields; vm_keyf := None; vm_name := name |}
                    end in
          LOk (rl_with_vmap (Some vm) rl1, fs1)
      end
  | CObjrefMap _ kps _ =>
      (* `counter name <key> map { v : "obj" }`: load the (concatenated) key
         fields and emit a verdict-neutral objref-map statement against a fresh
         anonymous map name (src/statement.c objref_stmt: NFT_EXPR_OBJREF with
         set_id).  The map's element->object bindings are a verdict-neutral side
         effect not read by the semantics, so they are not interned into the
         verdict environment (documented model boundary, DEVELOPMENT.md). *)
      infos <-- map_lres sel_field_dt kps ;;
      let fields := map fst infos in
      p <-- ensure_dep family (List.concat (map sel_deps kps)) rl fs ;;
      let '(rl1, fs1) := p in
      let '(name, ls') := fresh_map (fs_ls fs1) in
      LOk (rl_push (BStmt (SObjrefMap fields name)) rl1,
           mkFstate ls' (fs_typed fs1) (fs_deps fs1))
  | CStmt (StLimit rate u over burst byte_rate) =>
      ls <-- limit_spec rate u over burst byte_rate ;;
      LOk (rl_push (BMatch (MLimit ls)) rl, fs)
  | CStmt s0 =>
      s <-- resolve_stmt fuel defs s0 ;;
      rl1 <-- lower_terminal family s rl ;;
      ms <-- lower_stmt s ;;
      match ms with
      | Some st => LOk (rl_push (BStmt st) rl1, fs)
      | None => LOk (rl1, fs)
      end
  end.

Fixpoint lower_clauses (oracle : string -> option nat) (fuel : nat)
    (family : string) (defs : list (string * svalue))
    (cls : list sclause) (rl : rloc) (fs : fstate) : lres (rloc * fstate) :=
  match cls with
  | nil => LOk (rl, fs)
  | cl :: rest =>
      p <-- lower_clause oracle fuel family defs cl rl fs ;;
      let '(rl', fs') := p in lower_clauses oracle fuel family defs rest rl' fs'
  end.

Definition is_continue (v : verdict) : bool :=
  match v with Continue => true | _ => false end.

Definition assemble_outcome (rl : rloc) : lres outcome :=
  match rl_vmap rl, rl_nat rl, rl_tproxy rl with
  | Some _, _, Some _ => LErr LEmultiOutcome
  | _, Some _, Some _ => LErr LEmultiOutcome
  | Some vm, Some ns, None => LOk (OVmapNat vm ns)
  | Some vm, None, None =>
      if is_continue (rl_verdict rl) then LOk (OVmap vm) else LErr LEvmapStatic
  | None, Some ns, None => LOk (ONat ns)
  | None, None, Some tp => LOk (OTproxy tp)
  | None, None, None =>
      match rl_verdict rl with Continue => LOk ONone | v => LOk (OVerdict v) end
  end.

Definition lower_rule (oracle : string -> option nat) (fuel : nat)
    (family : string) (defs : list (string * svalue))
    (cls : srule) (fs : fstate) : lres (rule * fstate) :=
  p <-- lower_clauses oracle fuel family defs cls rl0 fs ;;
  let '(rl, fs') := p in
  outc <-- assemble_outcome rl ;;
  let r := {| r_body := rev (rl_body rl); r_outcome := outc; r_after := nil |} in
  (* fail-loud admission: every rule the lowering EMITS is numgen-free, which
     discharges the mutation strand's [rule_numgen_free] hypothesis for every
     frontend program ([Lower_Proofs.lower_ruleset_numgen_free]). *)
  if rule_numgen_free r then LOk (r, fs') else LErr LEnumgen.

(* ---------- chains ---------- *)

Definition chain_hookinfo (items : list schain_item)
  : option (string * string * bool * nat) :=
  fold_left (fun acc it => match it with
                           | ITypeHook ct h pn pr => Some (ct, h, pn, pr)
                           | _ => acc end) items None.

(** The six netfilter hooks a base chain may bind.  An unknown hook name is a
    fail-loud [LEhook] in the lowering (below), so every hook string that
    survives into [lr_hooks] is one of these — and the [hook_id] resolution the
    Gen files perform on it is total by construction. *)
Definition is_known_hook (h : string) : bool :=
  existsb (String.eqb h)
    ["prerouting"; "input"; "forward"; "output"; "postrouting"; "ingress"].

Fixpoint lower_chain_items (oracle : string -> option nat) (fuel : nat)
    (family : string) (defs : list (string * svalue)) (items : list schain_item)
    (pol : option verdict) (rules : list rule) (fs : fstate)
  : lres (option verdict * list rule * fstate) :=
  match items with
  | nil => LOk (pol, rules, fs)
  | ITypeHook _ _ _ _ :: rest =>
      lower_chain_items oracle fuel family defs rest pol rules fs
  | IPolicy v :: rest =>
      lower_chain_items oracle fuel family defs rest (Some (lower_sverdict v)) rules fs
  | IRule cls :: rest =>
      p <-- lower_rule oracle fuel family defs cls fs ;;
      let '(r, fs') := p in
      lower_chain_items oracle fuel family defs rest pol (r :: rules) fs'
  end.

Definition lower_chain (oracle : string -> option nat) (fuel : nat)
    (family : string) (defs : list (string * svalue)) (sc : schain) (fs : fstate)
  : lres ((string * chain) * option (string * string * bool * nat) * fstate) :=
  let hookinfo := chain_hookinfo (sc_items sc) in
  let is_base := match hookinfo with Some _ => true | None => false end in
  _ <-- (match hookinfo with
         | Some (_, h, _, _) => if is_known_hook h then LOk tt else LErr (LEhook h)
         | None => LOk tt end) ;;
  p <-- lower_chain_items oracle fuel family defs (sc_items sc) None nil fs ;;
  let '(pol, rules, fs') := p in
  let c_policy := match pol with
                  | Some v => v
                  | None => if is_base then Accept else Continue end in
  LOk ((sc_name sc, {| c_policy := c_policy; c_rules := rev rules |}), hookinfo, fs').

(* ---------- declarations (pass 2) ---------- *)

Definition lower_setdecl (fuel : nat) (defs : list (string * svalue))
    (sd : ssetdecl) (fs : fstate) : lres fstate :=
  let types := sd_type sd in
  if sd_is_map sd then
    if existsb (fun e => match snd e with Some _ => true | None => false end)
               (sd_elements sd) then
      ents <-- map_lres (fun e => let '(key, d) := e in
                 key' <-- resolve_sv fuel defs key ;;
                 LOk (key', match d with Some v => lower_sverdict v | None => Continue end))
               (sd_elements sd) ;;
      vents <-- decl_vmap_ents types ents ;;
      LOk (mkFstate (add_vmap (fs_ls fs) (sd_name sd) vents) (fs_typed fs) (fs_deps fs))
    else match sd_elements sd with
         | nil => LOk (mkFstate (add_map (fs_ls fs) (sd_name sd) nil) (fs_typed fs) (fs_deps fs))
         | _ => LErr LEvalueMap
         end
  else
    keys <-- map_lres (fun e => resolve_sv fuel defs (fst e)) (sd_elements sd) ;;
    elems <-- decl_set_elems types keys ;;
    LOk (mkFstate (add_set (fs_ls fs) (sd_name sd) elems) (fs_typed fs) (fs_deps fs)).

Fixpoint lower_table_setdecls (fuel : nat) (defs : list (string * svalue))
    (items : list stable_item) (fs : fstate) : lres fstate :=
  match items with
  | nil => LOk fs
  | TSet sd :: rest =>
      fs' <-- lower_setdecl fuel defs sd fs ;; lower_table_setdecls fuel defs rest fs'
  | _ :: rest => lower_table_setdecls fuel defs rest fs
  end.

Fixpoint lower_setdecls_top (fuel : nat) (defs : list (string * svalue))
    (rs : sruleset) (fs : fstate) : lres fstate :=
  match rs with
  | nil => LOk fs
  | TopTable t :: rest =>
      fs' <-- lower_table_setdecls fuel defs (st_items t) fs ;;
      lower_setdecls_top fuel defs rest fs'
  | _ :: rest => lower_setdecls_top fuel defs rest fs
  end.

(* ---------- chains (pass 3) ---------- *)

Fixpoint lower_table_chains (oracle : string -> option nat) (fuel : nat)
    (defs : list (string * svalue)) (family : string) (items : list stable_item)
    (chains : list (string * chain))
    (hooks : list (string * string * string * bool * nat)) (fs : fstate)
  : lres (list (string * chain) * list (string * string * string * bool * nat) * fstate) :=
  match items with
  | nil => LOk (rev chains, rev hooks, fs)
  | TChain sc :: rest =>
      p <-- lower_chain oracle fuel family defs sc fs ;;
      let '(namedchain, hookinfo, fs') := p in
      let hooks' := match hookinfo with
                    | Some (ct, h, pn, pr) => (fst namedchain, ct, h, pn, pr) :: hooks
                    | None => hooks end in
      lower_table_chains oracle fuel defs family rest (namedchain :: chains) hooks' fs'
  | _ :: rest => lower_table_chains oracle fuel defs family rest chains hooks fs
  end.

Fixpoint lower_tables (oracle : string -> option nat) (fuel : nat)
    (defs : list (string * svalue)) (rs : sruleset)
    (tables : list (string * string * list (string * chain)))
    (allhooks : list (string * string * list (string * string * string * bool * nat)))
    (fs : fstate)
  : lres (list (string * string * list (string * chain)) *
          list (string * string * list (string * string * string * bool * nat)) * fstate) :=
  match rs with
  | nil => LOk (rev tables, rev allhooks, fs)
  | TopTable t :: rest =>
      p <-- lower_table_chains oracle fuel defs (st_family t) (st_items t) nil nil fs ;;
      let '(chains, hooks, fs') := p in
      lower_tables oracle fuel defs rest
        ((st_family t, st_name t, chains) :: tables)
        ((st_family t, st_name t, hooks) :: allhooks) fs'
  | _ :: rest => lower_tables oracle fuel defs rest tables allhooks fs
  end.

(* ---------- top level ---------- *)

Definition collect_defines (rs : sruleset) : list (string * svalue) :=
  fold_left (fun acc tl => match tl with TopDefine n v => (n, v) :: acc | _ => acc end)
            rs nil.

Record lowered_ruleset : Type := mkLoweredRuleset {
  lr_tables : list (string * string * list (string * chain));
  lr_hooks  : list (string * string * list (string * string * string * bool * nat));
  lr_sets   : list (string * list (data * data));
  lr_vmaps  : list (string * list (data * data * verdict));
  lr_maps   : list (string * list (data * data));
  lr_typed  : list (matchcond * txmatch);
  lr_deps   : list matchcond }.

(** The M4 entry point: [oracle] resolves iif/oif interface NAMES to indices
    (the sole host-dependent residue, supplied by the OCaml frontend); the
    ruleset is the pure structural injection of the surface tree.  No byte is
    composed outside Coq. *)
Definition lower_ruleset (oracle : string -> option nat) (rs : sruleset)
  : lres lowered_ruleset :=
  let defs := collect_defines rs in
  let fuel := S (Nat.add (Nat.mul (List.length defs) 4) 16) in
  fs1 <-- lower_setdecls_top fuel defs rs (mkFstate ls0 nil nil) ;;
  res <-- lower_tables oracle fuel defs rs nil nil fs1 ;;
  let '(tables, hooks, fs2) := res in
  LOk {| lr_tables := tables; lr_hooks := hooks;
         lr_sets := rev (ls_sets (fs_ls fs2));
         lr_vmaps := rev (ls_vmaps (fs_ls fs2));
         lr_maps := rev (ls_maps (fs_ls fs2));
         lr_typed := fs_typed fs2;
         lr_deps := fs_deps fs2 |}.

(* ================================================================== *)
(** ** M6: the fail-loud gate and the structural projections the Gen files use.

    [lower_ok] is the boolean the generated [_lowers_ok] Example asserts: if the
    surface ruleset fails to lower for ANY reason (unknown selector/symbol,
    out-of-reach construct, …) it is [false] and `make proofs` fails on the
    Example — a refused construct can never silently fall back to OCaml bytes.

    [lower_or_empty] is the total view the Gen file's [_lowered] definition
    reduces (via [Eval vm_compute]); the projections below carve the per-table
    chains / hooks / declarations out of it so every downstream identifier
    ([filter_chains], [filter_input], [decls], …) keeps its exact name while its
    BYTES are produced by this verified lowering, not written by hand. *)

Definition lower_ok (oracle : string -> option nat) (rs : sruleset) : bool :=
  match lower_ruleset oracle rs with LOk _ => true | LErr _ => false end.

Definition empty_lowered : lowered_ruleset :=
  {| lr_tables := nil; lr_hooks := nil; lr_sets := nil;
     lr_vmaps := nil; lr_maps := nil; lr_typed := nil; lr_deps := nil |}.

Definition lower_or_empty (oracle : string -> option nat) (rs : sruleset)
  : lowered_ruleset :=
  match lower_ruleset oracle rs with LOk lr => lr | LErr _ => empty_lowered end.

Definition empty_chain : chain := {| c_policy := Continue; c_rules := nil |}.

(** The chains of the named table (empty if there is no such table). *)
Definition lr_chains_of (lr : lowered_ruleset) (tbl : string)
  : list (string * chain) :=
  fold_right (fun t acc =>
       let '(_, name, ch) := t in
       if String.eqb name tbl then ch else acc) nil (lr_tables lr).

(** One named chain of a named table ([empty_chain] if absent). *)
Definition lr_chain_of (lr : lowered_ruleset) (tbl cn : string) : chain :=
  match find (fun p => String.eqb (fst p) cn) (lr_chains_of lr tbl) with
  | Some p => snd p
  | None => empty_chain
  end.

(** The raw hook records of a named table (family, name-tagged). *)
Definition lr_hookinfo_of (lr : lowered_ruleset) (tbl : string)
  : list (string * string * string * bool * nat) :=
  fold_right (fun t acc =>
       let '(_, name, hs) := t in
       if String.eqb name tbl then hs else acc) nil (lr_hooks lr).
