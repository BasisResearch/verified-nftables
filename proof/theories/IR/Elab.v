(** * Elab: the TYPED source-match layer, verifiably elaborated onto the byte IR.

    A generated source term ([*_Gen.v]) does not carry raw register bytes: its
    immediates are TYPED values ([Nftval.nftval] — [VIpv4]/[VPort]/[VIfname]/
    [VCtState]/[VHostInt]/…), its CIDR matches carry the prefix length, and its
    interface-name wildcards are a dedicated shape.  [elab_m] is the TOTAL,
    VERIFIED elaboration of a typed match onto the byte-level [matchcond] IR the
    compiler consumes; [elab_matchcond_correct] proves the elaborated term
    evaluates exactly as the typed semantics [eval_tmatch] on every env/packet.
    The per-field byte encoding (endianness, widths) is [Nftval.encode].

    SCOPE — what is and is not covered.  [tmatch] has exactly FOUR shapes
    (typed eq / neq / CIDR-prefix / ifname-wildcard), so "the typed->bytes step
    is proved" holds for THOSE matches plus every per-atom [encode] call the
    frontend makes ([enc_atom] = [encode] o [typed_atom]).  It does NOT cover
    the immediates the frontend COMPOSES outside [elab_m]: set/map element
    intervals (nft_lower.ml's [interval_of_value] does its own OCaml CIDR
    net/broadcast expansion — distinct from the verified [prefix_expand]),
    range endpoints (incl. [enc_atom_be]'s host-endian reversal), vmap keys,
    NAT/tproxy target addresses/ports, mangle/vsrc immediates, and bitwise
    masks.  Those remain unverified frontend bytes, checked by the untrusted
    differential gates (corpus/validate/parse-test/e2e), not by this theorem.

    The CIDR alignment special-case lives HERE, verified, not in the frontend:
    nft shortens a byte-aligned prefix on a plain payload field to a load of
    just the prefix bytes plus a direct cmp (`ip saddr a.b.c.0/24` =>
    `payload load 3b @ network+12 ; cmp eq`), and keeps the full-width
    `load ; bitwise & mask ; cmp` form for every other prefix (golden
    {ip,ip6}.t.payload) — [prefix_expand] makes that decision. *)

From Stdlib Require Import List PeanoNat Bool NArith String.
From Nft Require Import Bytes Packet Verdict Bytecode Syntax Semantics Nftval.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(** ** Typed match conditions (the surface shapes with typed immediates). *)

Inductive tmatch : Type :=
| TMEq  (f : field) (v : nftval)     (* equality against a typed immediate *)
| TMNeq (f : field) (v : nftval)     (* inequality against a typed immediate *)
| MPrefix (f : field) (op : cmpop) (v : nftval) (plen : nat)
                                     (* CIDR: the top [plen] bits of [f] equal
                                        (op = CEq) / differ from (op = CNe) the
                                        network part of [v] *)
| MWildcard (f : field) (prefix : data).
                                     (* trailing-`*` interface-name wildcard /
                                        ct-tuple CIDR: the field's LEADING bytes
                                        equal [prefix] (a genuinely SHORT
                                        compare — the one surface construct
                                        whose meaning is a prefix match) *)

(* ------------------------------------------------------------------ *)
(** ** The verified CIDR expansion (the alignment decision, in Coq). *)

(** The truncated-load field of a byte-aligned prefix on a plain payload
    address (or the identity for a conntrack-tuple address, whose symbolic
    `ct load` keeps the full-width load and shortens only the compare). *)
Definition payload_prefix_field (f : field) (nbytes : nat) : option field :=
  match f with
  | FIp4Saddr => Some (FPayload PNetwork 12 nbytes)
  | FIp4Daddr => Some (FPayload PNetwork 16 nbytes)
  | FIp6Saddr => Some (FPayload PNetwork 8  nbytes)
  | FIp6Daddr => Some (FPayload PNetwork 24 nbytes)
  | FCtDir k d => Some (FCtDir k d)
  | _ => None
  end.

(** Byte [i] of a big-endian prefix mask: the top [min b 8] bits set. *)
Definition mask_byte (b : nat) : nat := 256 - Nat.pow 2 (8 - Nat.min b 8).

(** The [w]-byte big-endian mask with the top [plen] bits set. *)
Definition prefix_mask (w plen : nat) : data :=
  map (fun i => mask_byte (plen - 8 * i)) (seq 0 w).

(** Pointwise AND (an all-zero xor [data_bitops]). *)
Definition data_and (a mask : data) : data :=
  data_bitops a mask (repeat 0 (List.length a)).

(** Expand a CIDR prefix to the byte IR: a byte-aligned prefix strictly inside
    the field's width on a plain payload address shortens to a truncated-load
    direct compare; every other prefix keeps the full-width masked compare. *)
Definition prefix_expand (f : field) (op : cmpop) (v : nftval) (plen : nat)
  : matchcond :=
  let bytes := encode v in
  let w := List.length bytes in
  let mask := prefix_mask w plen in
  let net := data_and bytes mask in
  if (0 <? plen) && (plen <? 8 * w) && (Nat.eqb (Nat.modulo plen 8) 0)
  then match payload_prefix_field f (Nat.div plen 8) with
       | Some f' =>
           let short := firstn (Nat.div plen 8) net in
           match op with CNe => MNeq f' short | _ => MEq f' short end
       | None => MMasked f op mask (repeat 0 w) net
       end
  else MMasked f op mask (repeat 0 w) net.

(* ------------------------------------------------------------------ *)
(** ** The elaboration and its correctness. *)

Definition elab_m (m : tmatch) : matchcond :=
  match m with
  | TMEq f v  => MEq  f (encode v)
  | TMNeq f v => MNeq f (encode v)
  | MPrefix f op v plen => prefix_expand f op v plen
  | MWildcard f prefix => MEq f prefix
  end.

(** The TYPED semantics: what each typed shape means against a packet.
    [TMEq]/[TMNeq] compare the field's leading [encode v] bytes against the
    typed value's register encoding (for a full-width typed value this is the
    full-width register compare — [Nftval.meq_encode_full_width]); [MWildcard]
    is the genuine short prefix compare; [MPrefix] means exactly its verified
    expansion (the kernel evaluates the expanded form; there is no other
    ground truth for the alignment split). *)
Definition eval_tmatch (m : tmatch) (e : env) (p : packet) : bool :=
  match m with
  | TMEq f v =>
      field_loadable f p
      && data_eqb (firstn (List.length (encode v)) (field_value f e p)) (encode v)
  | TMNeq f v =>
      field_loadable f p
      && negb (data_eqb (firstn (List.length (encode v)) (field_value f e p)) (encode v))
  | MPrefix f op v plen => eval_matchcond (prefix_expand f op v plen) e p
  | MWildcard f prefix =>
      field_loadable f p
      && data_eqb (firstn (List.length prefix) (field_value f e p)) prefix
  end.

(** HEADLINE-adjacent: the elaboration is evaluation-exact — reasoning about a
    typed source term IS reasoning about the byte IR the compiler consumes. *)
Theorem elab_matchcond_correct : forall m e p,
  eval_matchcond (elab_m m) e p = eval_tmatch m e p.
Proof. intros [] e p; reflexivity. Qed.

(** Axiom-freedom guard (build-time): prints "Closed under the global context". *)
Print Assumptions elab_matchcond_correct.

(* ------------------------------------------------------------------ *)
(** ** Source views of a set-declaration element.

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

(* ------------------------------------------------------------------ *)
(** ** Concrete-shape witnesses (the elaboration is the documented lowering). *)

(** `ip saddr 192.168.100.0/24` — byte-aligned: truncated 3-byte load + cmp. *)
Example prefix_aligned_24 :
  elab_m (MPrefix FIp4Saddr CEq (VIpv4 [192;168;100;0]) 24)
  = MEq (FPayload PNetwork 12 3) [192;168;100].
Proof. vm_compute. reflexivity. Qed.

(** `ip saddr 10.0.0.0/20` — unaligned: full-width mask + cmp. *)
Example prefix_unaligned_20 :
  elab_m (MPrefix FIp4Saddr CEq (VIpv4 [10;0;0;0]) 20)
  = MMasked FIp4Saddr CEq [255;255;240;0] [0;0;0;0] [10;0;0;0].
Proof. vm_compute. reflexivity. Qed.

(** A typed port equality elaborates to the 2-byte big-endian register cmp. *)
Example elab_port_22 : elab_m (TMEq FThDport (VPort 22)) = MEq FThDport [0;22].
Proof. vm_compute. reflexivity. Qed.

(** A wildcard `iifname "dummy*"` is the short 5-byte prefix compare. *)
Example elab_wildcard :
  elab_m (MWildcard FMetaIifname (sbytes "dummy"))
  = MEq FMetaIifname [100;117;109;109;121].
Proof. vm_compute. reflexivity. Qed.
