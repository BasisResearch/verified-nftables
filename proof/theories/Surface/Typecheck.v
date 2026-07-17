(** * Surface.Typecheck: nft's typing discipline over the untyped surface tree.

    [resolve_value : dtype -> svalue -> option nftval] normalises SPELLING
    into the typed value domain: a symbolic constant and its numeric form hit
    the IDENTICAL [Nftval.nftval] (`ct state established` = `ct state 2` =
    [VCtState 2]), with symbol lookup walking the basetype chain and falling
    back to basetype-integer parsing (src/evaluate.c expr_evaluate_symbol,
    src/datatype.c symbol_parse — see Surface.Symbols.lookup_symbol).

    [typecheck_ruleset : sruleset -> bool] then checks a whole surface file:
    every match/vmap/bitwise/statement operand must resolve at its selector's
    datatype (Surface.Selector), set references must be declared at a
    chain-compatible datatype, bare comma lists are admitted only over
    bitmask-basetype selectors (evaluate.c expr_evaluate_list), and bitwise
    expressions only over integer-basetype selectors — `iifname & 0xff` is
    ill-typed because ifname's chain ends at STRING.

    SCOPE.  This checker is about TYPES: which (selector, value) pairs nft's
    frontend admits.  Deliberately NOT here:
      - lowering limitations that are fail-loud refusals of well-typed nft
        (tcp-flags brace sets, vlan-in-netdev, non-literal NAT targets in a
        map): those stay `lerr`s of the lowering they belong to;
      - `limit` magnitude bounds: the 2^40 ExtrOcamlNatInt seam guard lives
        at the injection boundary (extracted/nft_inject.ml) and the parser
        (`limit_value`), cf. theories/Compiler/Extract.v.

    Where this checker is STRICTER than the OCaml frontend, nft itself is the
    ground truth and each case is a frontend bug the checker refuses to
    reproduce (noted inline): width-overflow literals (`ip protocol 300` —
    typed_atom's `land 0xff` masks, nft errors "value exceeds valid range"),
    prefix lengths beyond the field width, over-IFNAMSIZ interface names,
    numeric IP/MAC spellings. *)

From Stdlib Require Import List PeanoNat Bool NArith Lia.
(* String is EXPORTED (and string_scope opened globally below): importing
   Typecheck must let a gate write `resolve_value dt_ct_state (SVSym
   "established")` verbatim — the coqtop acceptance check does exactly that,
   and the string-literal notation activates on IMPORT of Strings.String. *)
From Stdlib Require Export String.
From Nft Require Import Bytes Packet Verdict Bytecode Syntax Nftval.
(* Export the surface layers: importing Typecheck is importing the whole
   typed-surface interface (AST constructors, dtype lattice, symbol tables,
   selector map) — the gates and later milestones name them through here. *)
From Nft Require Export Ast Datatype Symbols Selector.
Import ListNotations.
(* exported: importing Typecheck gives the whole surface interface, string
   literals included (the parse-test/coqtop gates Compute over it) *)
#[global] Open Scope string_scope.

(* ------------------------------------------------------------------ *)
(** ** Interface-name register bytes (the three compile forms).

    nft compiles an interface name three ways (nft_lower.ml [ifname_bytes];
    golden any/meta.t.payload:198-230): an EXACT name is the full 16-byte
    (IFNAMSIZ) zero-padded register compare; a trailing UNESCAPED `*` is a
    SHORT compare of just the prefix bytes (the wildcard); an escaped `\*` is
    a literal `*` in an exact name.  Names that cannot fit the 16-byte
    register are refused (the kernel cannot hold them; the OCaml zero_pad
    silently left them unpadded). *)
Definition ifnamsiz : nat := 16.

Definition ifname_exact (b : data) : option data :=
  if (List.length b <=? ifnamsiz)%nat then Some (pad16 b) else None.

Definition ifname_bytes (s : string) : option data :=
  match rev (sbytes s) with
  | c1 :: rest1 =>
      if Nat.eqb c1 42 (* '*' *) then
        match rest1 with
        | c2 :: rest2 =>
            if Nat.eqb c2 92 (* '\' *) then
              (* "...\*": escaped star — a LITERAL '*' ends an exact name *)
              ifname_exact (rev (42 :: rest2))
            else
              (* "...*": wildcard — the SHORT prefix bytes, unpadded *)
              let b := rev rest1 in
              if (List.length b <? ifnamsiz)%nat then Some b else None
        | [] => Some []            (* "*" alone: the empty wildcard prefix *)
        end
      else ifname_exact (sbytes s)
  | [] => ifname_exact (sbytes s)  (* "" : the all-zero register *)
  end.

(* ------------------------------------------------------------------ *)
(** ** Numeric resolution: dtype + number -> typed value.

    The single place a NUMBER becomes a typed value; both the numeric
    spelling ([SVNum]) and every symbol-table hit route through it, so the
    two spellings CANNOT diverge ([symbol_numeric_same_term] below).  The
    width admission is bit-precise ([dt_width]): `ip protocol 300` and
    `ip dscp 64` are refused, exactly as nft refuses them. *)
Definition fits (dt : dtype) (n : N) : bool :=
  match dt with
  | DTtime => (n * 1000 <? 256 ^ 4)%N   (* the SCALED ms value fits 4 bytes  *)
  | _ => (n <? 2 ^ N.of_nat (dt_width dt))%N
  end.

Definition resolve_num (dt : dtype) (n : N) : option nftval :=
  if negb (fits dt n) then None else
  match dt with
  | DTinteger w    => Some (VInteger w n)
  | DThostint w    => Some (VHostInt w n)
  | DTbitmask _    => None       (* chain-interior: no surface spelling      *)
  | DTstring       => None
  | DTipv4 | DTipv6 | DTether | DTifname => None
      (* address/name literals are LEXICAL forms (dotted quad, colon-hex,
         bareword); the frontend's typed_atom refuses their numeric
         spelling, and so do we — fail-loud over leniency (nft itself would
         basetype-parse a numeric address; no corpus rule uses that). *)
  | DTifindex      => Some (VHostInt 4 n)
  | DTinet_service => Some (VPort n)
  | DTinet_proto   => Some (VInteger 1 n)
  | DTnfproto      => Some (VInteger 1 n)
  | DTethertype    => Some (VInteger 2 n)
  | DTct_state     => Some (VCtState n)
  | DTct_status    => Some (VInteger 4 n)
  | DTct_dir       => Some (VInteger 1 n)
  | DTmark         => Some (VHostInt 4 n)
  | DTpkttype      => Some (VInteger 1 n)
  | DTfib_addrtype => Some (VFibType n)
  | DTtcp_flag     => Some (VInteger 1 n)
  | DTdscp         => Some (VInteger 1 n)
  | DTtime         => Some (VHostInt 4 (n * 1000))
      (* nft's time_type parses SECONDS and stores MILLISECONDS (time_parse
         *1000; src/datatype.c); the register is host-endian 4-byte, so the
         literal [n] seconds becomes [VHostInt 4 (n*1000)].  [fits DTtime]
         bounds the SCALED value against the 4-byte register, so an
         overflowing duration is refused rather than silently wrapped. *)
  | DTicmp_type | DTicmp_code | DTicmpv6_type | DTicmpv6_code
  | DTigmp_type | DTmh_type => Some (VInteger 1 n)
  | DTarp_op       => Some (VInteger 2 n)
  end.

(** [lit_fits] (Datatype.v) agrees with the numeric spelling's admission. *)
Lemma resolve_num_lit_fits : forall dt n,
  lit_fits n dt = true -> resolve_num dt (N.of_nat n) <> None.
Proof.
  intros dt n H. unfold lit_fits in H.
  apply andb_prop in H as [Hn Hf]. unfold resolve_num.
  assert (Hfits : fits dt (N.of_nat n) = true) by (unfold fits; exact Hf).
  rewrite Hfits. cbn [negb].
  destruct dt; simpl in Hn; try discriminate Hn; discriminate.
Qed.

(** Symbolic resolution: names for ifname/ifindex, symbol tables (walking
    the basetype chain, with the integer-literal fallback) for the rest. *)
Definition resolve_sym (dt : dtype) (s : string) : option nftval :=
  match dt with
  | DTifname  => option_map VIfname (ifname_bytes s)
  | DTifindex =>
      (* nft resolves iif/oif names against the LIVE host (if_nametoindex);
         only "lo" = 1 is a kernel invariant (first registered device).  The
         general case is the ifindex ORACLE parameter of the M4 lowering;
         until then any other name is refused, like nft_lower.nametoindex. *)
      if String.eqb s "lo" then Some (VHostInt 4 1) else None
  | _ => match lookup_symbol dt s with
         | Some n => resolve_num dt n
         | None => None
         end
  end.

Definition resolve_value (dt : dtype) (v : svalue) : option nftval :=
  match v with
  | SVNum n => resolve_num dt (N.of_nat n)
  | SVSym s => resolve_sym dt s
  | SVStr s =>
      (* a quoted string is a NAME; nft admits it only in name positions *)
      match dt with
      | DTifname  => option_map VIfname (ifname_bytes s)
      | DTifindex => if String.eqb s "lo" then Some (VHostInt 4 1) else None
      | _ => None
      end
  | SVIp4 b => match dt with
               | DTipv4 => if Nat.eqb (List.length b) 4 then Some (VIpv4 b) else None
               | _ => None
               end
  | SVIp6 l r => match dt with
                 | DTipv6 =>
                     match sip6_bytes l r with
                     | Some b => if Nat.eqb (List.length b) 16
                                 then Some (VIpv6 b) else None
                     | None => None
                     end
                 | _ => None
                 end
      (* NOTE: typed_atom also maps a bare IPv4 literal in an ip6 context to
         a raw 4-byte VIpv6 ("v4-mapped").  That value is not [wf] (an IPv6
         register is 16 bytes) and nft's own spelling for it is the mapped
         `::ffff:a.b.c.d` form, so the checker refuses the shortcut. *)
  | SVMac b => match dt with
               | DTether => if Nat.eqb (List.length b) 6 then Some (VEther b) else None
               | _ => None
               end
  | _ => None      (* $var (unexpanded), prefix/range/concat/set: not atoms *)
  end.

(* ------------------------------------------------------------------ *)
(** ** THEOREMS: the resolver embodies the kind table's decisions. *)

(** Every resolved value is well-formed — EXCEPT the deliberate sub-width
    ifname wildcard, whose SHORT prefix compare is the construct's meaning
    (Typed.TXWildcard).  The disjunct is tight: a wildcard's bytes are strictly
    shorter than the register. *)
Lemma pad16_length : forall d,
  (List.length d <= 16)%nat -> List.length (pad16 d) = 16%nat.
Proof.
  intros d H. unfold pad16. rewrite length_app, repeat_length. lia.
Qed.

Lemma ifname_exact_len : forall d b,
  ifname_exact d = Some b -> List.length b = 16%nat.
Proof.
  intros d b H. unfold ifname_exact in H.
  destruct (List.length d <=? ifnamsiz)%nat eqn:Hl; [|discriminate].
  injection H as <-. apply pad16_length, Nat.leb_le, Hl.
Qed.

Lemma ifname_bytes_len : forall s b,
  ifname_bytes s = Some b ->
  List.length b = 16%nat \/ (List.length b < 16)%nat.
Proof.
  intros s b H. unfold ifname_bytes in H.
  destruct (rev (sbytes s)) as [|c1 rest1].
  - left. eapply ifname_exact_len, H.
  - destruct (Nat.eqb c1 42).
    + destruct rest1 as [|c2 rest2].
      * injection H as <-. right. cbn. unfold ifnamsiz. lia.
      * destruct (Nat.eqb c2 92).
        -- left. eapply ifname_exact_len, H.
        -- destruct (List.length (rev (c2 :: rest2)) <? ifnamsiz)%nat eqn:Hl;
             [|discriminate].
           injection H as <-. right. apply Nat.ltb_lt, Hl.
    + left. eapply ifname_exact_len, H.
Qed.

(** 2^(8w) = 256^w: the bit-precise admission implies the byte-width wf. *)
Lemma fits_pow_bytes : forall w n,
  (n < 2 ^ N.of_nat (8 * w))%N -> (n < 256 ^ N.of_nat w)%N.
Proof.
  intros w n H.
  replace (256 ^ N.of_nat w)%N with (2 ^ N.of_nat (8 * w))%N; [exact H|].
  rewrite Nat2N.inj_mul. change 256%N with (2 ^ 8)%N.
  now rewrite <- N.pow_mul_r.
Qed.

Theorem resolve_num_wf : forall dt n x,
  resolve_num dt n = Some x -> Nftval.wf x.
Proof.
  intros dt n x H. unfold resolve_num in H.
  destruct (fits dt n) eqn:Hf; simpl in H; [|discriminate].
  destruct dt; try discriminate; injection H as <-; cbn [Nftval.wf];
    unfold fits in Hf; cbn [dt_width] in Hf; apply N.ltb_lt in Hf.
  (* the parametric integer/host-integer widths *)
  1-2: apply (fits_pow_bytes _ _ Hf).
  (* the fixed-width datatypes AND DTtime (whose [fits] already bounds the
     scaled ms value by 256^4): convert the bit/scaled bound to the byte bound *)
  all: try (eapply N.lt_le_trans; [exact Hf|]; vm_compute; discriminate).
Qed.

(** Every resolved number encodes at exactly its datatype's register width —
    the Coq counterpart of nft_lower's [width_of_kind], as a theorem. *)
Lemma div8_bytes : forall w, Nat.div (8 * w + 7) 8 = w.
Proof.
  intro w. rewrite Nat.mul_comm, Nat.div_add_l by lia.
  now rewrite Nat.div_small by lia.
Qed.

Theorem resolve_num_width : forall dt n x,
  resolve_num dt n = Some x ->
  List.length (Nftval.encode x) = dt_bytes dt.
Proof.
  intros dt n x H. unfold resolve_num in H.
  destruct (fits dt n); simpl in H; [|discriminate].
  destruct dt; try discriminate; injection H as <-;
    cbn [Nftval.encode]; unfold dt_bytes; cbn [dt_width];
    try (rewrite length_rev); rewrite N_to_data_length;
    try apply eq_sym, div8_bytes; reflexivity.
Qed.

(** Every resolved number is stored in exactly its datatype's REGISTER BYTE
    ORDER — the Coq counterpart of [host_endian_kind], as a theorem: the
    host-endian-encoded values ([VHostInt]/[VFibType]) are precisely the
    [BoHost] datatypes. *)
Definition host_encoded (x : nftval) : bool :=
  match x with VHostInt _ _ | VFibType _ => true | _ => false end.

Theorem resolve_num_byteorder : forall dt n x,
  resolve_num dt n = Some x ->
  host_encoded x = byteorder_eqb (dt_byteorder dt) BoHost.
Proof.
  intros dt n x H. unfold resolve_num in H.
  destruct (fits dt n); simpl in H; [|discriminate].
  destruct dt; try discriminate; injection H as <-; reflexivity.
Qed.

(** SAME-TYPED-TERM GUARANTEE (general form): whenever a symbol has a table
    value, its resolution IS the numeric spelling's resolution.  (ifname /
    ifindex resolve names, not table symbols; their tables are empty.) *)
Theorem symbol_numeric_same_term : forall dt s n,
  lookup_symbol dt s = Some n ->
  dt <> DTifname -> dt <> DTifindex ->
  resolve_value dt (SVSym s) = resolve_value dt (SVNum (N.to_nat n)).
Proof.
  intros dt s n Hl Hif Hix. cbn [resolve_value].
  rewrite N2Nat.id.
  destruct dt; try congruence; cbn [resolve_sym]; rewrite Hl; reflexivity.
Qed.

Theorem resolve_value_wf : forall dt v x,
  resolve_value dt v = Some x ->
  Nftval.wf x \/ exists pre, x = VIfname pre /\ (List.length pre < 16)%nat.
Proof.
  intros dt v x H. destruct v; simpl in H.
  - (* SVNum *) left. eapply resolve_num_wf, H.
  - (* SVSym *)
    unfold resolve_sym in H. destruct dt; cbv beta iota in H;
      try (destruct (lookup_symbol _ s) as [n|];
           [ left; eapply resolve_num_wf; exact H | discriminate H ]).
    + (* DTifname *)
      destruct (ifname_bytes s) as [b|] eqn:Hb; simpl in H; [|discriminate H].
      injection H as <-.
      destruct (ifname_bytes_len _ _ Hb) as [He|Hw].
      * left. exact He.
      * right. exists b. auto.
    + (* DTifindex *)
      destruct (String.eqb s "lo"); [|discriminate H].
      injection H as <-. left. cbn. lia.
  - (* SVStr *)
    destruct dt; cbv beta iota in H; try discriminate H.
    + destruct (ifname_bytes s) as [b|] eqn:Hb; simpl in H; [|discriminate H].
      injection H as <-.
      destruct (ifname_bytes_len _ _ Hb) as [He|Hw];
        [left; exact He | right; exists b; auto].
    + destruct (String.eqb s "lo"); [|discriminate H].
      injection H as <-. left. cbn. lia.
  - (* SVIp4 *) destruct dt; cbv beta iota in H; try discriminate H.
    destruct (Nat.eqb (List.length b) 4) eqn:Hl; [|discriminate H].
    injection H as <-. left. apply Nat.eqb_eq in Hl. exact Hl.
  - (* SVIp6 *) destruct dt; cbv beta iota in H; try discriminate H.
    destruct (sip6_bytes _ _) as [b|] eqn:Hb; [|discriminate H].
    destruct (Nat.eqb (List.length b) 16) eqn:Hl; [|discriminate H].
    injection H as <-. left. apply Nat.eqb_eq in Hl. exact Hl.
  - (* SVMac *) destruct dt; cbv beta iota in H; try discriminate H.
    destruct (Nat.eqb (List.length b) 6) eqn:Hl; [|discriminate H].
    injection H as <-. left. apply Nat.eqb_eq in Hl. exact Hl.
  - discriminate. - discriminate. - discriminate. - discriminate. - discriminate.
Qed.

(** Axiom-freedom (informational; the enforcement point is `make axioms`). *)
Print Assumptions resolve_num_width.
Print Assumptions resolve_num_byteorder.
Print Assumptions symbol_numeric_same_term.
Print Assumptions resolve_value_wf.

(* ------------------------------------------------------------------ *)
(** ** Define expansion (`$name`), fueled.

    nft substitutes defines before evaluation; the OCaml [resolve_var]
    recurses unboundedly (and would loop on a cyclic define) — here fuel
    bounds the walk by the total define size, so a cycle is a clean [None]
    (ill-typed), never divergence. *)
Fixpoint svalue_size (v : svalue) : nat :=
  match v with
  | SVPrefix v' _ => S (svalue_size v')
  | SVRange a b => S (svalue_size a + svalue_size b)
  | SVConcat vs =>
      S ((fix sz (l : list svalue) : nat :=
            match l with [] => 0%nat | x :: r => (svalue_size x + sz r)%nat end) vs)
  | SVSet vs =>
      S ((fix sz (l : list svalue) : nat :=
            match l with [] => 0%nat | x :: r => (svalue_size x + sz r)%nat end) vs)
  | _ => 1%nat
  end.

Definition defs_ctx : Type := list (string * svalue).

Fixpoint expand_var (defs : defs_ctx) (fuel : nat) (v : svalue)
  : option svalue :=
  match fuel with
  | O => None
  | S k =>
      match v with
      | SVVar n => match assoc_str n defs with
                   | Some v' => expand_var defs k v'
                   | None => None                       (* undefined $name *)
                   end
      | SVPrefix v' l => match expand_var defs k v' with
                         | Some x => Some (SVPrefix x l)
                         | None => None
                         end
      | SVRange a b => match expand_var defs k a, expand_var defs k b with
                       | Some x, Some y => Some (SVRange x y)
                       | _, _ => None
                       end
      | SVConcat vs =>
          match (fix go (l : list svalue) : option (list svalue) :=
                   match l with
                   | [] => Some []
                   | x :: r => match expand_var defs k x, go r with
                               | Some x', Some r' => Some (x' :: r')
                               | _, _ => None
                               end
                   end) vs with
          | Some vs' => Some (SVConcat vs')
          | None => None
          end
      | SVSet vs =>
          match (fix go (l : list svalue) : option (list svalue) :=
                   match l with
                   | [] => Some []
                   | x :: r => match expand_var defs k x, go r with
                               | Some x', Some r' => Some (x' :: r')
                               | _, _ => None
                               end
                   end) vs with
          | Some vs' => Some (SVSet vs')
          | None => None
          end
      | _ => Some v
      end
  end.

(** Adequate fuel: expansion depth <= the value's size + every define's size
    (fuel is NOT split across siblings, so a sum over defines dominates any
    acyclic chain; a cyclic chain exhausts it and fails loudly). *)
Definition defs_fuel (defs : defs_ctx) : nat :=
  fold_right (fun '(_, dv) acc => (S (svalue_size dv) + acc)%nat) 1%nat defs.
Definition sexpand (defs : defs_ctx) (v : svalue) : option svalue :=
  expand_var defs (svalue_size v + defs_fuel defs) v.

(* ------------------------------------------------------------------ *)
(** ** Composite values at a selector datatype. *)

Definition check_atom (dt : dtype) (v : svalue) : bool :=
  match resolve_value dt v with Some _ => true | None => false end.

(** CIDR prefixes exist for the address types only, with the prefix length
    bounded by the field width (nft: "Prefix length N is invalid").  The
    OCaml [prefix_mask] silently saturates an oversized length. *)
Definition prefix_ok (dt : dtype) (base : svalue) (len : nat) : bool :=
  match base with
  | SVIp4 _ => dtype_eqb dt DTipv4 && check_atom dt base && (len <=? 32)%nat
  | SVIp6 _ _ => dtype_eqb dt DTipv6 && check_atom dt base && (len <=? 128)%nat
  | _ => false
  end.

(** A set/vmap ELEMENT: a point atom, an inclusive range (both endpoints at
    the selector's datatype), or a CIDR prefix. *)
Definition check_elem (dt : dtype) (v : svalue) : bool :=
  match v with
  | SVRange a b => check_atom dt a && check_atom dt b
  | SVPrefix base len => prefix_ok dt base len
  | _ => check_atom dt v
  end.

(** A single-selector VALUE: an element, or a define that expanded to a whole
    set (each member an element). *)
Definition check_value (dt : dtype) (v : svalue) : bool :=
  match v with
  | SVSet vs => forallb (check_elem dt) vs
  | _ => check_elem dt v
  end.

(** Bare comma lists are typed ONLY over bitmask-basetype selectors
    (evaluate.c:1871 expr_evaluate_list requires TYPE_BITMASK basetype):
    ct_state / ct_status / tcp_flag. *)
Definition bitmask_basetype (dt : dtype) : bool :=
  existsb (fun d => match d with DTbitmask _ => true | _ => false end)
          (basechain dt).

(* ------------------------------------------------------------------ *)
(** ** Declared sets/maps: the declaration context. *)

Definition decl_ctx : Type := list (string * list string).

(** Declared set type atoms (mirror of nft_lower's [bytes_of_typeatom]
    coverage; an unknown atom is refused). *)
Definition atom_dtype (a : string) : option dtype :=
  if String.eqb a "ipv4_addr" then Some DTipv4
  else if String.eqb a "ipv6_addr" then Some DTipv6
  else if String.eqb a "ifname" then Some DTifname
  else if String.eqb a "iface_index" then Some DTifindex
  else if String.eqb a "inet_service" then Some DTinet_service
  else if String.eqb a "inet_proto" then Some DTinet_proto
  else if String.eqb a "ether_addr" then Some DTether
  else if String.eqb a "mark" then Some DTmark
  else None.

(** Pointwise: the declared atoms are chain-compatible with the selector
    datatypes ([dt_compat]: either coerces to the other). *)
Fixpoint atoms_compat (atoms : list string) (dts : list dtype) : bool :=
  match atoms, dts with
  | [], [] => true
  | a :: ar, d :: dr => match atom_dtype a with
                        | Some ad => dt_compat ad d && atoms_compat ar dr
                        | None => false
                        end
  | _, _ => false
  end.

(** A set/map REFERENCE (`@name`) must be declared in the same table with a
    chain-compatible (concatenated) type — an undeclared reference is how a
    typo'd `@nmae` slips through, and nft itself errors on it. *)
Definition ref_compat (decls : decl_ctx) (name : string) (dts : list dtype)
  : bool :=
  match assoc_str name decls with
  | Some atoms => atoms_compat atoms dts
  | None => false
  end.

(* ------------------------------------------------------------------ *)
(** ** Matches. *)

(** The datatypes of a (possibly concatenated) selector key list. *)
Fixpoint sel_dtypes (kps : list skeypath) : option (list dtype) :=
  match kps with
  | [] => Some []
  | kp :: rest => match selector kp, sel_dtypes rest with
                  | Some (_, dt, _), Some dts => Some (dt :: dts)
                  | _, _ => None
                  end
  end.

Fixpoint check_concat_elem (dts : list dtype) (vs : list svalue) : bool :=
  match dts, vs with
  | [], [] => true
  | dt :: dr, v :: vr => check_elem dt v && check_concat_elem dr vr
  | _, _ => false
  end.

Definition expanded_check (defs : defs_ctx) (chk : svalue -> bool)
                          (v : svalue) : bool :=
  match sexpand defs v with Some v' => chk v' | None => false end.

(** The rhs of a SINGLE selector at datatype [dt]. *)
Definition tc_rhs (defs : defs_ctx) (decls : decl_ctx) (dt : dtype)
                  (r : srhs) : bool :=
  match sr_payload r with
  | SSEvalue v => expanded_check defs (check_value dt) v
  | SSEset vs => forallb (expanded_check defs (check_elem dt)) vs
  | SSElist vs => bitmask_basetype dt
                  && forallb (expanded_check defs (check_atom dt)) vs
  | SSEref name => ref_compat decls name [dt]
  end.

(** `missing`/`exists` right-hand sides (presence tests). *)
Definition presence_rhs (se : ssetexpr) : bool :=
  match se with
  | SSEvalue (SVSym s) => String.eqb s "missing" || String.eqb s "exists"
  | _ => false
  end.

(** A sub-byte bitfield selector: a single numeric value within the field's
    BIT width, or (for the dscp fields) a dscp codepoint symbol; sets/ranges
    over a bitfield are refused (mirroring the lowering — the masked
    lookup/range shape is not modelled). *)
Definition tc_bitfield (defs : defs_ctx) (spec : bitfield_spec) (r : srhs)
  : bool :=
  match sr_payload r with
  | SSEvalue v =>
      match sexpand defs v with
      | Some (SVNum n) => (N.of_nat n <? 2 ^ N.of_nat (bf_bits spec))%N
      | Some (SVSym s) =>
          bf_dscp spec
          && match assoc_str s dt_syms_dscp with
             | Some _ => true | None => false
             end
      | _ => false
      end
  | _ => false
  end.

(** One single-keypath match: presence forms, bitfields, then the selector
    table (mirroring lower_match's dispatch order). *)
Definition tc_single (defs : defs_ctx) (decls : decl_ctx)
                     (kp : skeypath) (r : srhs) : bool :=
  if presence_rhs (sr_payload r) then
    match kp with
    | [k; _sel; _res] => String.eqb k "fib"      (* fib <sel> <res> missing *)
    | [k; proto] =>
        if String.eqb k "exthdr" then
          match exthdr_htype proto with Some _ => true | None => false end
        else if String.eqb k "tcpopt" then
          match dt_tcpopt_num proto with Some _ => true | None => false end
        else false
    | _ => false
    end
  else
    match bitfield kp with
    | Some spec => tc_bitfield defs spec r
    | None =>
        match selector kp with
        | Some (_, dt, _) => tc_rhs defs decls dt r
        | None => false
        end
    end.

(** A concatenated match: every keypath resolves; the rhs is a set of
    arity-matching concat elements, a compatible declared reference, or one
    concat value. *)
Definition tc_concat (defs : defs_ctx) (decls : decl_ctx)
                     (kps : list skeypath) (se : ssetexpr) : bool :=
  match sel_dtypes kps with
  | None => false
  | Some dts =>
      match se with
      | SSEref name => ref_compat decls name dts
      | SSEset vs =>
          forallb (expanded_check defs
                     (fun v => match v with
                               | SVConcat parts => check_concat_elem dts parts
                               | _ => false
                               end)) vs
      | SSEvalue v =>
          expanded_check defs
            (fun v' => match v' with
                       | SVConcat parts => check_concat_elem dts parts
                       | _ => false
                       end) v
      | SSElist _ => false      (* bare commas never type at a concat key *)
      end
  end.

(** A verdict map (single or concatenated key). *)
Definition tc_vmap (defs : defs_ctx) (kps : list skeypath)
                   (entries : list (svalue * sverdict)) : bool :=
  match sel_dtypes kps with
  | Some [dt] =>
      forallb (fun '(v, _) => expanded_check defs (check_elem dt) v) entries
  | Some dts =>
      forallb (fun '(v, _) =>
                 expanded_check defs
                   (fun v' => match v' with
                              | SVConcat parts => check_concat_elem dts parts
                              | _ => false
                              end) v) entries
  | None => false
  end.

Definition tc_vmapref (decls : decl_ctx) (kps : list skeypath)
                      (name : string) : bool :=
  match sel_dtypes kps with
  | Some dts => ref_compat decls name dts
  | None => false
  end.

(** Bitwise mask matches (`<sel> and|or|xor <mask> <relop> <val>`): admitted
    ONLY over an integer-basetype selector — THE `iifname & 0xff` rejection:
    ifname's chain ends at STRING ([Datatype.ifname_not_integer]), so there
    is no integer to mask. *)
Definition tc_bitmatch (defs : defs_ctx) (kp : skeypath) (op : string)
                       (mask : svalue) (r : srhs) : bool :=
  match selector kp with
  | Some (_, dt, _) =>
      (match int_basetype dt with Some _ => true | None => false end)
      && (String.eqb op "and" || String.eqb op "or" || String.eqb op "xor")
      && expanded_check defs (check_atom dt) mask
      && match sr_payload r with
         | SSEvalue v => expanded_check defs (check_atom dt) v
         | _ => false
         end
  | None => false
  end.

(* ------------------------------------------------------------------ *)
(** ** Statements. *)

Definition nat_flags_ok (fs : list string) : bool :=
  forallb (fun f => match assoc_str f dt_nat_flag with
                    | Some _ => true | None => false
                    end) fs.

Definition port_arg_ok (p : option nat) : bool :=
  match p with Some n => (N.of_nat n <? 65536)%N | None => true end.

(** A NAT/tproxy target address must expand to an address literal — the
    OCaml lowering silently DEGRADES a resolvable non-literal target to a
    bare terminal accept; the checker refuses it instead (fail-loud). *)
Definition nat_addr_ok (defs : defs_ctx) (addr : option svalue) : bool :=
  match addr with
  | None => true
  | Some v => match sexpand defs v with
              | Some v' => check_atom DTipv4 v' || check_atom DTipv6 v'
              | None => false
              end
  end.

(** Settable meta/ct keys, at the kernel's STORE register width/byteorder
    (nft_lower ct_set_kind/meta_set_kind; nft_meta.c nft_meta_set_eval,
    nft_ct.c nft_ct_set_eval — all host-endian registers). *)
Definition meta_set_dtype (key : string) : option dtype :=
  if String.eqb key "mark" then Some (DThostint 4)
  else if String.eqb key "priority" then Some (DThostint 4)
  else if String.eqb key "pkttype" then Some (DThostint 1)
  else None.
Definition ct_set_dtype (key : string) : option dtype :=
  if String.eqb key "zone" then Some (DThostint 2)
  else if String.eqb key "label" then Some (DThostint 16)
  else if String.eqb key "mark" then Some (DThostint 4)
  else if String.eqb key "event" then Some (DThostint 4)
  else None.

(** A table's declared objects (name -> kind), the mirror of [decl_ctx] for
    named-set references: a `counter name X` / `quota name X` / `ct helper set X`
    reference must name an object DECLARED in the same table, WITH THE MATCHING
    kind (referencing a quota as a counter is rejected — mirrors nft's
    "object X of type counter does not exist" load error). *)
Definition obj_ctx : Type := list (string * sobjkind).

Definition objkind_declared (objs : obj_ctx) (name : string) (k : sobjkind) : bool :=
  existsb (fun '(n, k') =>
             String.eqb n name && Nat.eqb (objkind_otype k') (objkind_otype k))
          objs.

Definition tc_stmt (defs : defs_ctx) (objs : obj_ctx) (s : sstmt) : bool :=
  match s with
  | StObjref k name => objkind_declared objs name k
  | StComment _ | StCounter _ _ | StLog _ | StNotrack => true
  | StLimit _ _ _ _ _ => true
      (* magnitudes are seam-guarded at injection + in the parser; typing
         adds nothing here (see the header's SCOPE note) *)
  | StMasquerade fs => nat_flags_ok fs
  | StSnat addr port fs =>
      nat_addr_ok defs addr && port_arg_ok port && nat_flags_ok fs
  | StDnat addr port fs =>
      nat_addr_ok defs addr && port_arg_ok port && nat_flags_ok fs
  | StRedirect port fs => port_arg_ok port && nat_flags_ok fs
  | StTproxy fam addr port =>
      (String.eqb fam "" || String.eqb fam "ip" || String.eqb fam "ip6")
      && nat_addr_ok defs addr && port_arg_ok port
  | StMetaSet key v =>
      match meta_set_dtype key with
      | Some dt => expanded_check defs (check_atom dt) v
      | None => false
      end
  | StCtSet key v =>
      match ct_set_dtype key with
      | Some dt => expanded_check defs (check_atom dt) v
      | None => false
      end
  end.

(* ------------------------------------------------------------------ *)
(** ** Clauses, rules, declarations, tables, rulesets. *)

(** An objref verdict-map (`counter name <key> map { v : "obj" }`): the key
    values type against the (concatenated) key selector — exactly as a [CVmap]
    key does — and every datum names an object DECLARED with the reference's
    kind (an undeclared / wrong-kind datum is rejected). *)
Definition tc_objrefmap (defs : defs_ctx) (objs : obj_ctx) (k : sobjkind)
                        (kps : list skeypath)
                        (entries : list (svalue * string)) : bool :=
  match sel_dtypes kps with
  | Some [dt] =>
      forallb (fun '(v, on) =>
                 expanded_check defs (check_elem dt) v && objkind_declared objs on k)
              entries
  | Some dts =>
      forallb (fun '(v, on) =>
                 expanded_check defs
                   (fun v' => match v' with
                              | SVConcat parts => check_concat_elem dts parts
                              | _ => false
                              end) v
                 && objkind_declared objs on k) entries
  | None => false
  end.

(** A verdict's own well-formedness (independent of any data typing): the
    `queue num` argument is a 16-bit queue index (kernel nf_queue: the queue
    number field is a __u16; evaluate.c stmt_evaluate_queue caps it), so an
    out-of-range `queue num 65536` is refused. *)
Definition sverdict_valid (v : sverdict) : bool :=
  match v with
  | SVqueue lo hi _ _ => andb (Nat.leb lo 65535) (Nat.leb hi 65535)
  | _ => true
  end.

Definition typecheck_clause (defs : defs_ctx) (decls : decl_ctx) (objs : obj_ctx)
                            (cl : sclause) : bool :=
  match cl with
  | CMatch m =>
      match sm_keys m with
      | [] => false
      | [kp] => tc_single defs decls kp (sm_rhs m)
      | kps => tc_concat defs decls kps (sr_payload (sm_rhs m))
      end
  | CVmap keys entries =>
      tc_vmap defs keys entries
      && forallb (fun '(_, sv) => sverdict_valid sv) entries
  | CVmapRef keys name => tc_vmapref decls keys name
  | CVerdict v => sverdict_valid v
  | CStmt s => tc_stmt defs objs s
  | CObjrefMap k keys entries => tc_objrefmap defs objs k keys entries
  | CBitmatch kp op mask r => tc_bitmatch defs kp op mask r
  end.

Definition typecheck_rule (defs : defs_ctx) (decls : decl_ctx) (objs : obj_ctx)
                          (r : srule) : bool :=
  forallb (typecheck_clause defs decls objs) r.

(** A declared set/map: known type atoms; every element types at the declared
    (concatenated) datatype; a MAP with elements must be a VERDICT map (value
    maps with inline data are not lowered — mirror of lower_setdecl). *)
Fixpoint atoms_dtypes (atoms : list string) : option (list dtype) :=
  match atoms with
  | [] => Some []
  | a :: rest => match atom_dtype a, atoms_dtypes rest with
                 | Some dt, Some dts => Some (dt :: dts)
                 | _, _ => None
                 end
  end.

Definition tc_setdecl (defs : defs_ctx) (sd : ssetdecl) : bool :=
  match atoms_dtypes (sd_type sd) with
  | None => false
  | Some dts =>
      forallb (fun '(v, _) =>
                 expanded_check defs
                   (fun v' => match dts with
                              | [dt] => check_elem dt v'
                              | _ => match v' with
                                     | SVConcat parts => check_concat_elem dts parts
                                     | _ => false
                                     end
                              end) v)
              (sd_elements sd)
      && (if sd_is_map sd then
            match sd_elements sd with
            | [] => true
            | elems => existsb (fun '(_, d) => match d with
                                               | Some _ => true | None => false
                                               end) elems
            end
          else true)
  end.

Definition typecheck_chain (defs : defs_ctx) (decls : decl_ctx) (objs : obj_ctx)
                           (c : schain) : bool :=
  forallb (fun it => match it with
                     | IRule r => typecheck_rule defs decls objs r
                     | _ => true
                     end) (sc_items c).

Definition decls_of_table (t : stable) : decl_ctx :=
  fold_right (fun it acc => match it with
                            | TSet sd => (sd_name sd, sd_type sd) :: acc
                            | _ => acc
                            end) [] (st_items t).

Definition objs_of_table (t : stable) : obj_ctx :=
  fold_right (fun it acc => match it with
                            | TObj n k => (n, k) :: acc
                            | _ => acc
                            end) [] (st_items t).

Definition typecheck_table (defs : defs_ctx) (t : stable) : bool :=
  let decls := decls_of_table t in
  let objs := objs_of_table t in
  forallb (fun it => match it with
                     | TSet sd => tc_setdecl defs sd
                     | TChain c => typecheck_chain defs decls objs c
                     | TObj _ _ => true
                     end) (st_items t).

(** Defines are collected file-wide first (mirror of lower's pass 1); a later
    duplicate SHADOWS an earlier one (Hashtbl.replace semantics), hence the
    fold_left prepend. *)
Definition defines_of (f : sruleset) : defs_ctx :=
  fold_left (fun acc tl => match tl with
                           | TopDefine n v => (n, v) :: acc
                           | _ => acc
                           end) f [].

Definition typecheck_ruleset (f : sruleset) : bool :=
  let defs := defines_of f in
  forallb (fun tl => match tl with
                     | TopTable t => typecheck_table defs t
                     | TopInclude _ => false   (* must be driver-expanded *)
                     | _ => true
                     end) f.

(* ------------------------------------------------------------------ *)
(** ** PINNED acceptance witnesses (vm_compute; the T1 acceptance tests). *)

(** `ct state 2` and `ct state established` are the SAME typed term. *)
Example ct_state_symbol_numeric_same_term :
  resolve_value dt_ct_state (SVSym "established")
    = resolve_value dt_ct_state (SVNum 2)
  /\ resolve_value dt_ct_state (SVNum 2) = Some (VCtState 2).
Proof. vm_compute. split; reflexivity. Qed.

(** `iifname & 0xff` is REJECTED (ifname has no integer basetype)... *)
Example reject_iifname_and_0xff :
  typecheck_clause [] [] []
    (CBitmatch ["iifname"] "and" (SVNum 255)
       (mkSrhs SOpEq false (SSEvalue (SVNum 1)))) = false.
Proof. vm_compute. reflexivity. Qed.

(** ...while the SAME expression over an integer-basetype selector types
    (the rejection is the selector's chain, not the clause shape). *)
Example accept_mark_and_0x3 :
  typecheck_clause [] [] []
    (CBitmatch ["mark"] "and" (SVNum 3)
       (mkSrhs SOpEq false (SSEvalue (SVNum 1)))) = true.
Proof. vm_compute. reflexivity. Qed.

(** More rejection witnesses (each an illtyped-suite case). *)
Example reject_ct_state_https :
  typecheck_clause [] [] []
    (CMatch (mkSmatch [["ct"; "state"]]
       (mkSrhs SOpImplicit false (SSEvalue (SVSym "https"))))) = false.
Proof. vm_compute. reflexivity. Qed.
Example reject_ip_protocol_300 :
  typecheck_clause [] [] []
    (CMatch (mkSmatch [["ip"; "protocol"]]
       (mkSrhs SOpImplicit false (SSEvalue (SVNum 300))))) = false.
Proof. vm_compute. reflexivity. Qed.
Example reject_comma_list_on_ports :
  (* bare comma list over a NON-bitmask selector (evaluate.c:1871) *)
  typecheck_clause [] [] []
    (CMatch (mkSmatch [["tcp"; "dport"]]
       (mkSrhs SOpImplicit false (SSElist [SVNum 22; SVNum 80])))) = false.
Proof. vm_compute. reflexivity. Qed.
Example accept_comma_list_on_ct_state :
  typecheck_clause [] [] []
    (CMatch (mkSmatch [["ct"; "state"]]
       (mkSrhs SOpImplicit false
          (SSElist [SVSym "new"; SVSym "established"])))) = true.
Proof. vm_compute. reflexivity. Qed.
Example reject_set_ref_type_mismatch :
  (* an ipv4_addr set referenced from an inet_service selector *)
  typecheck_clause [] [("addrs", ["ipv4_addr"])] []
    (CMatch (mkSmatch [["tcp"; "dport"]]
       (mkSrhs SOpImplicit false (SSEref "addrs")))) = false.
Proof. vm_compute. reflexivity. Qed.
Example accept_set_ref_matching :
  typecheck_clause [] [("addrs", ["ipv4_addr"])] []
    (CMatch (mkSmatch [["ip"; "daddr"]]
       (mkSrhs SOpImplicit false (SSEref "addrs")))) = true.
Proof. vm_compute. reflexivity. Qed.

(** Named-object references type against the table's declared objects.  A
    reference to a declared object of the matching kind is accepted; an
    undeclared name, or a declared name of the WRONG kind, is rejected — the
    `counter name`/`quota name`/`ct helper set` existence+kind check. *)
Example objref_declared_accepts :
  typecheck_clause [] [] [("cnt1", OKcounter)]
    (CStmt (StObjref OKcounter "cnt1")) = true.
Proof. vm_compute. reflexivity. Qed.
Example objref_undeclared_rejects :
  typecheck_clause [] [] []
    (CStmt (StObjref OKcounter "cnt1")) = false.
Proof. vm_compute. reflexivity. Qed.
Example objref_wrong_kind_rejects :
  (* declared as a COUNTER, referenced as a QUOTA *)
  typecheck_clause [] [] [("cnt1", OKcounter)]
    (CStmt (StObjref OKquota "cnt1")) = false.
Proof. vm_compute. reflexivity. Qed.
Example objrefmap_declared_accepts :
  typecheck_clause [] [] [("cnt1", OKcounter); ("cnt2", OKcounter)]
    (CObjrefMap OKcounter [["tcp"; "dport"]]
       [(SVNum 443, "cnt1"); (SVNum 80, "cnt2")]) = true.
Proof. vm_compute. reflexivity. Qed.
Example objrefmap_undeclared_rejects :
  typecheck_clause [] [] [("cnt1", OKcounter)]
    (CObjrefMap OKcounter [["tcp"; "dport"]]
       [(SVNum 443, "cnt1"); (SVNum 80, "nope")]) = false.
Proof. vm_compute. reflexivity. Qed.

(** The per-dtype width/byteorder table, one row per nft_lower `kind` (the
    24-kind table: 22 fixed kinds + the KNum/KNumLe families at a
    representative width) — [dt_bytes] in bytes, [true] = host-endian
    register.  The OCaml side of this parity is re-checked EXECUTABLY against
    [enc_atom] by parse-test's KIND-PARITY gate. *)
Example kind_table_widths_and_byteorders :
  map (fun dt => (dt_bytes dt, byteorder_eqb (dt_byteorder dt) BoHost))
      [DTifname; DTifindex; DTipv4; DTipv6; DTinet_service; DTinet_proto;
       DTnfproto; DTethertype; DTct_state; DTct_status; DTmark;
       DTicmp_type; DTicmpv6_type; DTpkttype; DTfib_addrtype; DTtcp_flag;
       DTinteger 2; DTigmp_type; DTicmp_code; DTicmpv6_code; DTmh_type;
       DTct_dir; DTarp_op; DThostint 2]
  = [(16, false); (4, true);  (4, false); (16, false); (2, false);
     (1, false);  (1, false); (2, false); (4, false);  (4, false);
     (4, true);   (1, false); (1, false); (1, false);  (4, true);
     (1, false);  (2, false); (1, false); (1, false);  (1, false);
     (1, false);  (1, false); (2, false); (2, true)].
Proof. vm_compute. reflexivity. Qed.

(** Wildcard and exact interface names take their two documented shapes. *)
Example ifname_exact_eth0 :
  resolve_value DTifname (SVStr "eth0")
  = Some (VIfname [101;116;104;48; 0;0;0;0; 0;0;0;0; 0;0;0;0]).
Proof. vm_compute. reflexivity. Qed.
Example ifname_wildcard_dummy :
  resolve_value DTifname (SVStr "dummy*")
  = Some (VIfname [100;117;109;109;121]).
Proof. vm_compute. reflexivity. Qed.
