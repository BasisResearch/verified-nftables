(** * Surface.Lower: the VERIFIED scalar-match lowering (M2).

    [lower_match] consumes the M1 surface AST (one selector key path + its
    right-hand side, defines already expanded) and produces the TYPED term
    ([Typed.txmatch]) whose verified elaboration [Typed.elab_tx] is the byte
    IR the compiler consumes.  With this file the OCaml frontend stops
    constructing byte-level match conditions for every SCALAR shape:

      - typed atoms (eq / neq), CIDR prefixes, ifname wildcards
        (the four Elab shapes, now BUILT here instead of in OCaml);
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

From Stdlib Require Import List PeanoNat Bool NArith String.
From Nft Require Import Bytes Packet Verdict Bytecode Syntax Nftval Elab
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
| LEvlanNetdev.                  (* vlan match in netdev family (iiftype
                                    guard byte-order — honest refusal)       *)

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
| DAguard (layer_keyed : bool) (f : field) (key : data) (tm : Elab.tmatch).
(* [layer_keyed]: dedup by FIELD alone (one network-layer guard per rule,
   whatever the value — golden inet/icmp.t.payload emits nfproto ONCE for
   `meta nfproto ipv4 icmpv6 type ...`); otherwise dedup by (field, value). *)

Definition guard (layer : bool) (f : field) (w : nat) (n : N) : dep_action :=
  DAguard layer f (N_to_data w n) (Elab.TMEq f (VInteger w n)).

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

Definition dep_guard (fam : string) (d : depspec) : lres dep_action :=
  match d with
  | DepL4 proto => LOk (guard false FMetaL4proto 1 (N.of_nat proto))
  | DepNfproto f =>
      if family_is_inet fam then LOk (guard true FMetaNfproto 1 (N.of_nat f))
      else if family_is_l2 fam then
        match nfproto_ethertype f with
        | Some et => LOk (guard true FMetaProtocol 2 et)
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
      else LOk (guard false FMetaIiftype 2 (N.of_nat t))
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
      | SVIp4 _ | SVIp6 _ =>
          match atom dt base "CIDR base address" with
          | LOk tv =>
              if prefix_len_ok dt len
              then LOk (deps,
                        TXElab (Elab.MPrefix f (if neg then CNe else CEq) tv len))
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
                then LOk (deps, TXElab (Elab.MWildcard f pre))
                else LOk (deps, TXElab (if neg then Elab.TMNeq f tv
                                        else Elab.TMEq f tv))
            | _ => LOk (deps, TXElab (if neg then Elab.TMNeq f tv
                                      else Elab.TMEq f tv))
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
    golden ip6/exthdr.t.payload, any/tcpopt.t.payload. *)
Definition lower_presence (kp : skeypath) (ex : bool) : option (lres lowered) :=
  match kp with
  | k :: rest =>
      if String.eqb k "fib" then
        match rest with
        | sel :: _res :: nil =>
            Some (LOk ([], TXFlag (FFib sel FRpresent) ex 0))
        | _ => None
        end
      else if String.eqb k "exthdr" then
        match rest with
        | proto :: nil =>
            Some match exthdr_htype proto with
                 | Some h => LOk (dep_ip6,
                                  TXFlag (FExthdr EPipv6 h 0 1 true) false
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
                                         false (if ex then 1%N else 0%N))
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
      match lower_presence kp ex with
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
              match sr_payload r with
              | SSEvalue v =>
                  match atom dt mask "bitwise mask", atom dt v "bitwise value"
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

(** The wildcard/exact ifname split survives the verified path. *)
Example lower_ifname_wildcard :
  lower_match (mkSmatch [["iifname"]]
                 (mrhs SOpImplicit false (SSEvalue (SVStr "dummy*"))))
  = LOk ([], TXElab (Elab.MWildcard FMetaIifname [100;117;109;109;121])).
Proof. vm_compute. reflexivity. Qed.
Example lower_ifname_exact :
  lower_match (mkSmatch [["iifname"]]
                 (mrhs SOpImplicit false (SSEvalue (SVStr "eth0"))))
  = LOk ([], TXElab (Elab.TMEq FMetaIifname
           (VIfname [101;116;104;48; 0;0;0;0; 0;0;0;0; 0;0;0;0]))).
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

(** Guard encoding: the icmp selector's two guards (nfproto THEN l4proto),
    family-aware — real matches in inet, none in the single-L3 ip family. *)
Example dep_guard_icmp_inet :
  map (dep_guard "inet") (dep_l4 "icmp")
  = [LOk (DAguard true FMetaNfproto [2]
            (Elab.TMEq FMetaNfproto (VInteger 1 2)));
     LOk (DAguard false FMetaL4proto [1]
            (Elab.TMEq FMetaL4proto (VInteger 1 1)))].
Proof. vm_compute. reflexivity. Qed.
Example dep_guard_ip_family_noop :
  dep_guard "ip" (DepNfproto 2) = LOk DAnone.
Proof. vm_compute. reflexivity. Qed.
Example dep_guard_bridge_ethertype :
  dep_guard "bridge" (DepNfproto 2)
  = LOk (DAguard true FMetaProtocol [8; 0]
           (Elab.TMEq FMetaProtocol (VInteger 2 0x0800))).
Proof. vm_compute. reflexivity. Qed.
Example dep_guard_vlan_netdev_refused :
  dep_guard "netdev" (DepEther 0x8100) = LErr LEvlanNetdev.
Proof. vm_compute. reflexivity. Qed.
