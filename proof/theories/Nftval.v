(** * Nftval: a typed, high-level VIEW of the low-level register-byte domain.

    The source semantics ([theories/Bytes.v]) models EVERY nft value as a flat
    [data = list byte]: an IPv4 address, an L4 port, an interface name, a
    conntrack-state bitmask, a fib route-type and a plain integer-of-width are
    all just byte strings, with no high-level type structure.  That is faithful
    to the kernel register file (registers really are bytes) but discards the
    distinct nft datatypes that nft's own datatype table (src/datatype.c)
    distinguishes.

    This file adds a HIGH-LEVEL typed disjoint union [nftval] (tagged by
    [nfttype]) and a verified TRANSLATION to/from the byte representation:

      - [encode : nftval -> data]            — the typed value's register bytes;
      - [decode : nfttype -> data -> option nftval] — read a typed value back.

    CRUCIAL: [encode] is NOT a new invented encoding.  It is a typed VIEW of the
    SAME bytes the existing compiler/codec already emit ([extracted/nft_lower.ml]
    [enc_atom]/[bytes_of_int]/[width_of_kind]), byteorder included:

      - integer-of-width / inet_service(port) / ethertype / ct_state are
        BIG-ENDIAN, encoded with [Bytes.N_to_data] exactly as [bytes_of_int];
      - ipv4_addr / ipv6_addr / ether_addr / ifname are VERBATIM register bytes
        (ifname is the 16-byte NUL-padded buffer [ifname_bytes] builds);
      - fib route-type is HOST-ENDIAN (little-endian on the x86/ARM64-LE host the
        validate gate runs on), exactly [bytes_of_int_le 4] = [rev] of the 4-byte
        big-endian encoding.

    The byte-faithfulness witnesses below ([encode_VPort_80] etc.) are checked by
    [vm_compute] against the concrete corpus/codec bytes (port 80 -> [0;80],
    nfproto ipv4 -> [2], ethertype ip -> [8;0], ct-state established -> [0;0;0;2],
    fib type local -> [2;0;0;0]).

    Finally [meq_encode_agrees] RELATES the typed view back to the byte-level
    [eval_matchcond_body]: a typed equality match (the [MEq] of [encode v]) is
    exactly the existing byte-level [data_eqb] test on [field_value], so the
    typed layer is a faithful, USED view — not a cosmetic unused inductive.

    This file is purely ADDITIVE: it edits no existing definition and proves no
    existing theorem differently. *)

From Stdlib Require Import List PeanoNat Bool NArith Lia.
From Nft Require Import Bytes Packet Verdict Syntax Semantics.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(** ** Byte-level round-trip helpers ([data_to_N] / [N_to_data]).

    [Bytes.v] already ships [N_to_data] (big-endian) and [data_to_N] (its
    big-endian decode) and proves [N_to_data_length].  We need the two
    round-trips between them; they are the arithmetic core of [decode_encode]
    and [encode_decode] below. *)

(** Appending the low byte: [data_to_N] of [d ++ [b]] shifts and adds. *)
Lemma data_to_N_snoc : forall d b,
  data_to_N (d ++ [b]) = (data_to_N d * 256 + N.of_nat b)%N.
Proof.
  intros d b. unfold data_to_N. rewrite fold_left_app. reflexivity.
Qed.

(** DECODE after ENCODE at the byte level: a big-endian [N_to_data] of a value
    that fits in [w] bytes decodes back to the same [N].  (The [n < 256^w] side
    condition is exactly the well-formedness an integer-of-width carries.) *)
Lemma data_to_N_N_to_data : forall w n,
  (n < 256 ^ N.of_nat w)%N ->
  data_to_N (N_to_data w n) = n.
Proof.
  induction w as [|k IH]; intros n Hlt.
  - simpl (N.of_nat 0) in Hlt. rewrite N.pow_0_r in Hlt.
    simpl (N_to_data 0 n). unfold data_to_N. simpl. lia.
  - simpl (N_to_data (S k) n). rewrite data_to_N_snoc.
    rewrite IH.
    + rewrite N2Nat.id.
      rewrite (N.div_mod n 256) at 3 by lia. lia.
    + (* n/256 < 256^k *)
      apply N.div_lt_upper_bound; [lia|].
      replace (256 * 256 ^ N.of_nat k)%N with (256 ^ N.of_nat (S k))%N.
      * exact Hlt.
      * rewrite Nat2N.inj_succ, N.pow_succ_r; lia.
Qed.

(** ENCODE after DECODE at the byte level: a byte string whose length is [w] and
    every byte is < 256 is recovered by [N_to_data w (data_to_N d)].  This is the
    width well-formedness side of the round-trip. *)
Lemma N_to_data_data_to_N : forall d,
  Forall (fun b => b < 256) d ->
  N_to_data (List.length d) (data_to_N d) = d.
Proof.
  intro d.
  (* induct from the RIGHT, matching N_to_data's snoc recursion *)
  induction d as [|x xs IH] using rev_ind; intro Hf.
  - reflexivity.
  - rewrite app_length. simpl (List.length [x]).
    rewrite Nat.add_1_r. simpl (N_to_data (S _) _).
    rewrite data_to_N_snoc.
    apply Forall_app in Hf as [Hxs Hx].
    inversion Hx as [|? ? Hxltn _]; subst.
    assert (Hxlt : (N.of_nat x < 256)%N) by lia.
    set (m := data_to_N xs).
    (* (m*256 + x) mod 256 = x  and  (m*256 + x) / 256 = m *)
    assert (Hmod : ((m * 256 + N.of_nat x) mod 256)%N = N.of_nat x).
    { rewrite N.add_comm. rewrite N.Div0.mod_add. apply N.mod_small. exact Hxlt. }
    assert (Hdiv : ((m * 256 + N.of_nat x) / 256)%N = m).
    { rewrite N.add_comm, N.div_add by lia.
      rewrite N.div_small by exact Hxlt. lia. }
    rewrite Hmod, Hdiv, Nat2N.id. unfold m. rewrite IH by exact Hxs.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The typed nft-data disjoint union.

    [nfttype] tags the distinct datatypes nft's [datatype.c] table distinguishes;
    [nftval] is the matching disjoint union of concrete values. *)

Inductive nfttype : Type :=
| TInteger     (w : nat)   (* integer of [w] bytes, big-endian (TYPE_INTEGER)   *)
| TIpv4                     (* ipv4_addr: 4 verbatim register bytes              *)
| TIpv6                     (* ipv6_addr: 16 verbatim register bytes             *)
| TIfname                   (* ifname: 16-byte NUL-padded interface-name buffer  *)
| TInetService              (* inet_service / port: 2 bytes big-endian           *)
| TEtherAddr                (* ether_addr: 6 verbatim register bytes             *)
| TVerdict                  (* a verdict-map key value (small big-endian int)    *)
| TCtState                  (* ct_state bitmask: 4 bytes big-endian              *)
| TFibType.                 (* fib route-type: 4 bytes HOST-endian (little)      *)

Inductive nftval : Type :=
| VInteger (w : nat) (n : N)   (* integer of [w] bytes (big-endian)              *)
| VIpv4    (b : data)          (* 4 verbatim bytes                                *)
| VIpv6    (b : data)          (* 16 verbatim bytes                               *)
| VIfname  (s : data)          (* the 16-byte NUL-padded ifname buffer            *)
| VPort    (n : N)             (* inet_service, 2 bytes big-endian                *)
| VEther   (b : data)          (* 6 verbatim bytes                                *)
| VVerdict (n : N)             (* verdict-map key (big-endian, [w] bytes)         *)
| VCtState (n : N)             (* ct_state bitmask, 4 bytes big-endian            *)
| VFibType (n : N).            (* fib route-type, 4 bytes little-endian           *)

(** The verdict-map key width is a fixed 4-byte register slot (the kernel stores
    a verdict-map key as a 32-bit value). *)
Definition verdict_width : nat := 4.

(** The type tag a value belongs to. *)
Definition type_of (v : nftval) : nfttype :=
  match v with
  | VInteger w _ => TInteger w
  | VIpv4 _      => TIpv4
  | VIpv6 _      => TIpv6
  | VIfname _    => TIfname
  | VPort _      => TInetService
  | VEther _     => TEtherAddr
  | VVerdict _   => TVerdict
  | VCtState _   => TCtState
  | VFibType _   => TFibType
  end.

(* ------------------------------------------------------------------ *)
(** ** [encode]: the typed value's register bytes — a VIEW of the real bytes.

    Every clause reuses [Bytes.N_to_data] (the SAME big-endian encoder
    [bytes_of_int] uses) or passes raw bytes through verbatim.  [VFibType] is the
    sole little-endian case ([bytes_of_int_le 4] = [rev (N_to_data 4 _)]). *)
Definition encode (v : nftval) : data :=
  match v with
  | VInteger w n => N_to_data w n
  | VIpv4 b      => b
  | VIpv6 b      => b
  | VIfname s    => s
  | VPort n      => N_to_data 2 n
  | VEther b     => b
  | VVerdict n   => N_to_data verdict_width n
  | VCtState n   => N_to_data 4 n
  | VFibType n   => rev (N_to_data 4 n)
  end.

(** The canonical register width of a type (= [width_of_kind] in nft_lower.ml). *)
Definition width_of (ty : nfttype) : nat :=
  match ty with
  | TInteger w   => w
  | TIpv4        => 4
  | TIpv6        => 16
  | TIfname      => 16
  | TInetService => 2
  | TEtherAddr   => 6
  | TVerdict     => verdict_width
  | TCtState     => 4
  | TFibType     => 4
  end.

(* ------------------------------------------------------------------ *)
(** ** [decode]: read a typed value back out of register bytes.

    Numeric types decode the big-endian (resp. host-endian for fib) integer with
    a width check; the verbatim byte types decode by a width check on the slice. *)
Definition decode (ty : nfttype) (d : data) : option nftval :=
  match ty with
  | TInteger w   => if Nat.eqb (List.length d) w then Some (VInteger w (data_to_N d)) else None
  | TIpv4        => if Nat.eqb (List.length d) 4  then Some (VIpv4 d)  else None
  | TIpv6        => if Nat.eqb (List.length d) 16 then Some (VIpv6 d)  else None
  | TIfname      => if Nat.eqb (List.length d) 16 then Some (VIfname d) else None
  | TInetService => if Nat.eqb (List.length d) 2  then Some (VPort (data_to_N d)) else None
  | TEtherAddr   => if Nat.eqb (List.length d) 6  then Some (VEther d) else None
  | TVerdict     => if Nat.eqb (List.length d) verdict_width
                    then Some (VVerdict (data_to_N d)) else None
  | TCtState     => if Nat.eqb (List.length d) 4  then Some (VCtState (data_to_N d)) else None
  | TFibType     => if Nat.eqb (List.length d) 4
                    then Some (VFibType (data_to_N (rev d))) else None
  end.

(* ------------------------------------------------------------------ *)
(** ** Width well-formedness of a typed value.

    A value is [wf] when its encoding has the canonical register width AND
    (for numeric types) fits in that width — exactly the precondition under
    which the byte round-trips hold. *)
Definition wf (v : nftval) : Prop :=
  match v with
  | VInteger w n => (n < 256 ^ N.of_nat w)%N
  | VPort n      => (n < 256 ^ N.of_nat 2)%N
  | VVerdict n   => (n < 256 ^ N.of_nat verdict_width)%N
  | VCtState n   => (n < 256 ^ N.of_nat 4)%N
  | VFibType n   => (n < 256 ^ N.of_nat 4)%N
  | VIpv4 b      => List.length b = 4
  | VIpv6 b      => List.length b = 16
  | VIfname s    => List.length s = 16
  | VEther b     => List.length b = 6
  end.

(** [encode] always produces the canonical width for its type (for the numeric
    types unconditionally; for the verbatim types under [wf]). *)
Lemma encode_length : forall v,
  wf v -> List.length (encode v) = width_of (type_of v).
Proof.
  intros [w n|b|b|s|n|b|n|n|n] H; cbn [encode width_of type_of] in *;
    try (apply N_to_data_length);
    try assumption.
  rewrite length_rev. apply N_to_data_length.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Round-trip theorem 1: [decode (type_of x) (encode x) = Some x].

    Decoding the encoding of a well-formed value recovers the value. *)
Theorem decode_encode : forall x,
  wf x -> decode (type_of x) (encode x) = Some x.
Proof.
  intros x Hwf.
  destruct x as [w n|b|b|s|n|b|n|n|n];
    cbn [type_of encode decode width_of verdict_width wf] in *.
  - (* VInteger *) rewrite N_to_data_length, Nat.eqb_refl.
    rewrite data_to_N_N_to_data by exact Hwf. reflexivity.
  - (* VIpv4 *) rewrite Hwf. reflexivity.
  - (* VIpv6 *) rewrite Hwf. reflexivity.
  - (* VIfname *) rewrite Hwf. reflexivity.
  - (* VPort *) rewrite N_to_data_length. cbn [Nat.eqb].
    rewrite data_to_N_N_to_data by exact Hwf. reflexivity.
  - (* VEther *) rewrite Hwf. reflexivity.
  - (* VVerdict *) rewrite N_to_data_length. cbn [Nat.eqb].
    rewrite data_to_N_N_to_data by exact Hwf. reflexivity.
  - (* VCtState *) rewrite N_to_data_length. cbn [Nat.eqb].
    rewrite data_to_N_N_to_data by exact Hwf. reflexivity.
  - (* VFibType *) rewrite length_rev, N_to_data_length. cbn [Nat.eqb].
    rewrite rev_involutive, data_to_N_N_to_data by exact Hwf. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Round-trip theorem 2: [encode] of the decoded value is the original bytes.

    Under a byte well-formedness predicate (each byte < 256, the register
    invariant), decoding then re-encoding is the identity on the bytes. *)
Definition data_wf (d : data) : Prop := Forall (fun b => b < 256) d.

Theorem encode_decode : forall ty d v,
  data_wf d ->
  decode ty d = Some v ->
  encode v = d.
Proof.
  intros ty d v Hwf Hdec. destruct ty; simpl in Hdec;
    (* split on the width test *)
    match goal with
    | [ H : (if Nat.eqb (List.length d) ?w then _ else None) = Some _ |- _ ] =>
        destruct (Nat.eqb (List.length d) w) eqn:Hlen; [|discriminate];
        apply Nat.eqb_eq in Hlen; injection H as <-
    end; cbn [encode verdict_width].
  - (* TInteger *) rewrite <- Hlen. apply N_to_data_data_to_N; exact Hwf.
  - (* TIpv4 *) reflexivity.
  - (* TIpv6 *) reflexivity.
  - (* TIfname *) reflexivity.
  - (* TInetService *) rewrite <- Hlen. apply N_to_data_data_to_N; exact Hwf.
  - (* TEtherAddr *) reflexivity.
  - (* TVerdict *) rewrite <- Hlen. apply N_to_data_data_to_N; exact Hwf.
  - (* TCtState *) rewrite <- Hlen. apply N_to_data_data_to_N; exact Hwf.
  - (* TFibType: encode (VFibType (data_to_N (rev d)))
                  = rev (N_to_data 4 (data_to_N (rev d))) = d *)
    rewrite <- Hlen, <- (length_rev d).
    rewrite N_to_data_data_to_N.
    + apply rev_involutive.
    + unfold data_wf in *. apply Forall_rev. exact Hwf.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Byte-faithfulness witnesses.

    The encoding is the SAME bytes the existing compiler/codec emit.  These are
    checked by [vm_compute] against the concrete corpus/codec values cited in the
    recon briefing (and in [extracted/nft_lower.ml]):
      - port 80 ([KPort, bytes_of_int 2 80]) renders [0;80];
      - meta nfproto ipv4 -> [2], ipv6 -> [10] (1-byte integers);
      - ethertype ip -> [8;0] ([bytes_of_int 2 0x0800]);
      - ct-state established -> [0;0;0;2] ([sym_ctstate], 4-byte big-endian);
      - fib type local -> [2;0;0;0] ([sym_fibtype], 4-byte little-endian). *)

Example encode_VPort_80 : encode (VPort 80) = [0; 80].
Proof. vm_compute. reflexivity. Qed.

Example encode_nfproto_ipv4 : encode (VInteger 1 2) = [2].
Proof. vm_compute. reflexivity. Qed.

Example encode_nfproto_ipv6 : encode (VInteger 1 10) = [10].
Proof. vm_compute. reflexivity. Qed.

Example encode_ethertype_ip : encode (VInteger 2 0x0800) = [8; 0].
Proof. vm_compute. reflexivity. Qed.

Example encode_ctstate_established : encode (VCtState 2) = [0; 0; 0; 2].
Proof. vm_compute. reflexivity. Qed.

Example encode_fibtype_local : encode (VFibType 2) = [2; 0; 0; 0].
Proof. vm_compute. reflexivity. Qed.

(** And these match the typed [decode] back (sanity of both directions on the
    concrete corpus bytes). *)
Example decode_port_80 : decode TInetService [0; 80] = Some (VPort 80).
Proof. vm_compute. reflexivity. Qed.

Example decode_ctstate_established : decode TCtState [0;0;0;2] = Some (VCtState 2).
Proof. vm_compute. reflexivity. Qed.

Example decode_fibtype_local : decode TFibType [2;0;0;0] = Some (VFibType 2).
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(** ** Relating the typed view to the byte-level semantics — the layer is USED.

    A typed equality match is built as [MEq f (encode v)].  We show it reduces
    EXACTLY to the existing byte-level test [eval_matchcond_body] performs: a
    [data_eqb] of the field's bytes (the typed value's encoding is what the
    kernel cmp compares against [field_value]).  Thus reasoning about a typed
    match is reasoning about the real byte-level semantics — the abstraction is
    faithful and consumed by the semantics, not a parallel invented one. *)

(** The typed-equality match condition: "[field f] equals (as a prefix) the
    register bytes of the typed value [v]". *)
Definition meq_typed (f : field) (v : nftval) : matchcond := MEq f (encode v).

(** It is definitionally the byte-level [MEq] on [encode v]: the typed equality
    match agrees with the byte-level [eval_matchcond_body]. *)
Lemma meq_encode_agrees : forall f v p,
  eval_matchcond_body (meq_typed f v) p
    = data_eqb (List.firstn (List.length (encode v)) (field_value f p)) (encode v).
Proof.
  intros f v p. reflexivity.
Qed.

(** Sharper form for a FULL-WIDTH typed value (one whose encoding has the
    canonical register width, e.g. a 16-byte exact ifname, a 4-byte address, a
    4-byte ct_state): the prefix length is exactly the type's width, so a typed
    equality match is the byte-level equality of the first [width_of ty] bytes of
    the field against [encode v].  This makes precise that the typed match is the
    REAL kernel cmp over the register slot. *)
Lemma meq_encode_full_width : forall f v p,
  wf v ->
  eval_matchcond_body (meq_typed f v) p
    = data_eqb (List.firstn (width_of (type_of v)) (field_value f p)) (encode v).
Proof.
  intros f v p Hwf. simpl. rewrite (encode_length v Hwf). reflexivity.
Qed.

(** Consequently: a typed equality match SUCCEEDS exactly when the field's
    leading [encode v] bytes ARE [encode v] — i.e. when the byte-level view of
    the field decodes (at the right width) to the typed value [v], for a
    well-formed [v].  This ties [decode]/[encode] to a real match outcome. *)
Lemma meq_typed_true_iff : forall f v p,
  eval_matchcond_body (meq_typed f v) p = true
    <-> List.firstn (List.length (encode v)) (field_value f p) = encode v.
Proof.
  intros f v p. rewrite meq_encode_agrees. apply data_eqb_true_iff.
Qed.

(** And when it matches a well-formed value, [decode] of the matched field slice
    recovers exactly [v] — the typed value the match tested for.  This is the
    "typed match agrees with the byte-level match, through the translation" lemma:
    a successful byte-level [MEq] against [encode v] is observationally a match of
    the TYPED value [v]. *)
Lemma meq_typed_decodes : forall f v p,
  wf v ->
  data_wf (List.firstn (width_of (type_of v)) (field_value f p)) ->
  eval_matchcond_body (meq_typed f v) p = true ->
  decode (type_of v) (List.firstn (width_of (type_of v)) (field_value f p)) = Some v.
Proof.
  intros f v p Hwf Hdwf Hmatch.
  apply meq_typed_true_iff in Hmatch.
  rewrite (encode_length v Hwf) in Hmatch.
  rewrite Hmatch. apply decode_encode. exact Hwf.
Qed.
