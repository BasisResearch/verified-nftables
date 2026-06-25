(** * Bytes: the value domain shared by the DSL and the bytecode.

    nftables registers and immediates hold byte strings.  A "payload load"
    reads [len] bytes from a header; a "cmp" compares a register's bytes to an
    immediate.  We therefore model a value as a [list byte], with byte = [N]
    (we never need the 0..255 bound for the equivalence proofs; only equality
    of byte strings matters). *)

From Stdlib Require Import List PeanoNat Bool NArith Lia.
Import ListNotations.

(** A byte is modelled as a [nat]; only equality of byte strings matters for the
    proofs, and [nat] extracts cleanly to an OCaml [int] for the glue code. *)
Definition byte := nat.

(** A [data] is a byte string: a loaded register value or a compared immediate. *)
Definition data := list byte.

(** Boolean equality on byte strings (decidable; used by [cmp]). *)
Definition data_eqb (a b : data) : bool :=
  if list_eq_dec Nat.eq_dec a b then true else false.

Lemma data_eqb_refl : forall a, data_eqb a a = true.
Proof. intros a. unfold data_eqb. destruct (list_eq_dec Nat.eq_dec a a); congruence. Qed.

Lemma data_eqb_true_iff : forall a b, data_eqb a b = true <-> a = b.
Proof.
  intros a b. unfold data_eqb. destruct (list_eq_dec Nat.eq_dec a b); split; congruence.
Qed.

(** Membership of a byte string in a set (the semantics of an nftables set
    lookup). *)
Definition data_mem (x : data) (s : list data) : bool :=
  existsb (data_eqb x) s.

(** Map lookup: the data value a key maps to ([] if absent). *)
Fixpoint map_lookup_data (k : data) (entries : list (data * data)) : data :=
  match entries with
  | [] => []
  | (k', v) :: rest => if data_eqb k k' then v else map_lookup_data k rest
  end.

(** Bytewise [(a & mask) ^ xor], the operation an nftables [bitwise] expression
    performs (used to model prefix/masked matches such as a /24). *)
Definition byte_and (a b : byte) : byte := Nat.land a b.
Definition byte_xor (a b : byte) : byte := Nat.lxor a b.
Definition byte_or  (a b : byte) : byte := Nat.lor a b.

(** Bytewise OR of two values, the operation an nftables register-to-register
    [bitwise ... | ...] expression performs (used when a value is composed by
    OR-ing several field sources, e.g. [meta mark | meta iif]). *)
Fixpoint data_or (a b : data) : data :=
  match a, b with
  | x :: xs, y :: ys => byte_or x y :: data_or xs ys
  | _, _ => []
  end.

Fixpoint data_bitops (a mask xor : data) : data :=
  match a, mask, xor with
  | x :: xs, m :: ms, e :: es => byte_xor (byte_and x m) e :: data_bitops xs ms es
  | _, _, _ => []
  end.

(** Byte-string <-> big-endian [N], used to model shifts faithfully. *)
Definition data_to_N (d : data) : N :=
  fold_left (fun acc b => (acc * 256 + N.of_nat b)%N) d 0%N.

Fixpoint N_to_data (len : nat) (n : N) : data :=
  match len with
  | 0 => []
  | S k => N_to_data k (N.div n 256) ++ [N.to_nat (N.modulo n 256)]
  end.

Lemma N_to_data_length : forall len n, List.length (N_to_data len n) = len.
Proof.
  induction len; intro n; simpl; [reflexivity|].
  rewrite length_app, IHlen; simpl; lia.
Qed.

(** Left/right bit shift of a register value (preserving its byte width). *)
Definition data_shift (shl : bool) (amt : nat) (d : data) : data :=
  N_to_data (length d)
    (if shl then N.shiftl (data_to_N d) (N.of_nat amt)
             else N.shiftr (data_to_N d) (N.of_nat amt)).

(** ** Internet checksum incremental update (RFC 1624).

    The Internet checksum (IPv4 header [check], TCP/UDP [check]) is the 16-bit
    one's-complement of the one's-complement sum of the 16-bit words of the
    checksummed region.  When NAT rewrites a field (an address word or a port)
    the kernel does NOT recompute the whole sum; it does an INCREMENTAL update —
    [csum_replace4]/[inet_proto_csum_replace2] (lib/checksum.c) compute, per
    RFC 1624 eqn. 3:

        HC' = ~(~HC + ~m + m')

    where [HC] is the old checksum, [m] the old value of the changed 16-bit
    word(s) and [m'] the new value, all reduced into 16 bits with the
    one's-complement end-around carry.  [csum_fold16] folds an arbitrary-width
    one's-complement accumulator back into 16 bits (the end-around carry: while
    there are bits above bit 15, add them back in). *)
Definition mask16 (n : N) : N := N.land n 65535.
Definition not16 (n : N) : N := N.lxor n 65535.

(** Fold a wide one's-complement accumulator into 16 bits by repeatedly adding
    the carry (high bits) back into the low 16 — bounded by [fuel] iterations
    (two passes always suffice for sums of a handful of 16-bit words). *)
Fixpoint csum_fold16_fuel (fuel : nat) (n : N) : N :=
  match fuel with
  | 0 => mask16 n
  | S k =>
      let lo := mask16 n in
      let hi := N.shiftr n 16 in
      if N.eqb hi 0 then lo else csum_fold16_fuel k (lo + hi)
  end.
Definition csum_fold16 (n : N) : N := csum_fold16_fuel 4 n.

(** The new 16-bit checksum after replacing the 16-bit word [oldw] by [neww]
    in a region whose old checksum is [oldck] (all taken as 16-bit values):
    [HC' = ~(~HC + ~m + m')], folded into 16 bits (RFC 1624 eqn. 3). *)
Definition csum_replace16 (oldck oldw neww : N) : N :=
  mask16 (not16 (csum_fold16 (not16 (mask16 oldck)
                              + not16 (mask16 oldw)
                              + mask16 neww))).

(** Replace a sequence of consecutive 16-bit words [olds]/[news] in [oldck],
    applying [csum_replace16] left-to-right (the kernel sums multiple words for
    an IPv6 address or for the L4 pseudo-header that covers the L3 address). *)
Fixpoint csum_replace_words (oldck : N) (olds news : list N) : N :=
  match olds, news with
  | o :: os, n :: ns => csum_replace_words (csum_replace16 oldck o n) os ns
  | _, _ => oldck
  end.

(** Split a big-endian byte string into its 16-bit words (pairs of bytes; a
    trailing odd byte is treated as the high byte of a final word, mirroring the
    checksum's right-zero-padding). *)
Fixpoint data_to_words16 (d : data) : list N :=
  match d with
  | [] => []
  | [b] => [N.shiftl (N.of_nat b) 8]
  | hi :: lo :: rest => (N.shiftl (N.of_nat hi) 8 + N.of_nat lo)%N :: data_to_words16 rest
  end.

(** Big-endian 2-byte encoding of a 16-bit checksum value. *)
Definition csum_to_data (n : N) : data := N_to_data 2 (mask16 n).
(** The 16-bit value of a big-endian 2-byte checksum field. *)
Definition csum_of_data (d : data) : N := mask16 (data_to_N d).

Lemma csum_to_data_length : forall n, List.length (csum_to_data n) = 2.
Proof. intro n. unfold csum_to_data. apply N_to_data_length. Qed.

(** Incrementally update a 2-byte checksum field [ck] for a field change from
    [old] to [new] (both byte strings of the same length, split into 16-bit
    words) — the model of [csum_replace4] (4-byte address: two 16-bit words) and
    [inet_proto_csum_replace2] (2-byte port: one word).  Returns the new 2-byte
    checksum field. *)
Definition csum_update_field (ck old new : data) : data :=
  csum_to_data (csum_replace_words (csum_of_data ck)
                                   (data_to_words16 old) (data_to_words16 new)).

Lemma csum_update_field_length : forall ck old new,
  List.length (csum_update_field ck old new) = 2.
Proof. intros. unfold csum_update_field. apply csum_to_data_length. Qed.

(** Jenkins-hash transform ([hash ... = jhash(reg, len, seed) % mod offset]).
    The real jhash is a specific mixing function; we model it as a deterministic
    function of the input bytes, seed, modulus and offset, bounded into
    [offset, offset+modulus) — faithful in *structure* (deterministic, input- and
    seed-dependent, mod-bounded), an abstraction of the exact mixing. *)
Definition data_jhash (len seed modulus offset : nat) (d : data) : data :=
  N_to_data 4
    (N.of_nat offset +
     N.modulo (data_to_N d + N.of_nat seed) (N.of_nat (S modulus))).

(** Byte-order conversion (ntoh/hton).  nftables' byteorder expression carries
    TWO independent widths: [size], the per-element width to byte-swap (2, 4 or
    8 bytes), and [len], the total number of bytes processed.  The kernel
    (net/netfilter/nft_byteorder.c) byte-swaps each [size]-byte element and
    iterates [len/size] times — e.g. a 16-byte IPv6 value with size=8 swaps two
    8-byte halves; a 6-byte MAC with size=2 swaps three 2-byte elements.  ntoh
    and hton are the same per-element byte reversal for a single conversion.  We
    therefore reverse each [size]-byte chunk of the register value (the element
    width), processing the first [len] bytes.  [fuel] (= [length d]) bounds the
    recursion so it is structural even when [size = 0]. *)
Fixpoint byteorder_chunks (fuel size : nat) (d : data) : data :=
  match fuel with
  | 0 => d
  | S f =>
      match d with
      | [] => []
      | _ :: _ => rev (firstn size d) ++ byteorder_chunks f size (skipn size d)
      end
  end.

Definition data_byteorder (hton : bool) (size len : nat) (d : data) : data :=
  byteorder_chunks (length d) size d.

(** Regression: a 4-byte value with size=len=4 (the only width the parser emits
    today: host-endian KMark/KIfindex) is a single full 4-byte reversal —
    unchanged by the size/len distinction. *)
Lemma data_byteorder_4_4 :
  data_byteorder true 4 4 [0;1;2;3] = [3;2;1;0].
Proof. reflexivity. Qed.

(** Regression / fidelity: a 16-byte IPv6 value at the kernel's widths
    (size=8, len=16) swaps each 8-byte HALF independently (per-element swap,
    len/size = 2 iterations), NOT the whole value.  This is the kernel's
    nft_byteorder.c behaviour (case 8: be64 over len/8 elements). *)
Lemma data_byteorder_ipv6_per_element :
  data_byteorder true 8 16 [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15]
    = [7;6;5;4;3;2;1;0; 15;14;13;12;11;10;9;8].
Proof. reflexivity. Qed.

(** And it is NOT the full reversal the old [len]-chunking produced. *)
Lemma data_byteorder_ipv6_not_full_reverse :
  data_byteorder true 8 16 [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15]
    <> rev [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15].
Proof. vm_compute. discriminate. Qed.

(** A 6-byte MAC at the kernel's widths (size=2, len=6) swaps each 2-byte
    element (ntohs over len/2 = 3 elements). *)
Lemma data_byteorder_mac_per_element :
  data_byteorder true 2 6 [0;1;2;3;4;5] = [1;0; 3;2; 5;4].
Proof. reflexivity. Qed.

(** Big-endian (most-significant-byte-first) lexicographic order on byte
    strings; for equal-length network-order values this is numeric order.
    Used by range matches. *)
Fixpoint data_le (a b : data) : bool :=
  match a, b with
  | [], _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys => if Nat.eqb x y then data_le xs ys else Nat.leb x y
  end.

(** Antisymmetry: [a <= b] and [b <= a] together are exactly equality.  Used to
    prove that a singleton range [lo <= x <= lo] is the same test as [x = lo]. *)
Lemma data_le_antisym : forall a b, andb (data_le a b) (data_le b a) = data_eqb a b.
Proof.
  induction a as [| x xs IH]; intros [| y ys].
  - reflexivity.
  - reflexivity.
  - cbn [data_le andb]. symmetry.
    destruct (data_eqb (x::xs) nil) eqn:E;
      [apply data_eqb_true_iff in E; discriminate | reflexivity].
  - cbn [data_le]. rewrite (Nat.eqb_sym y x).
    destruct (Nat.eqb x y) eqn:Exy.
    + apply Nat.eqb_eq in Exy; subst y. rewrite IH.
      destruct (data_eqb xs ys) eqn:E.
      * apply data_eqb_true_iff in E; subst ys. symmetry. apply data_eqb_refl.
      * symmetry. apply Bool.not_true_is_false.
        rewrite data_eqb_true_iff. intro Hc. inversion Hc; subst ys.
        rewrite data_eqb_refl in E; discriminate.
    + apply Nat.eqb_neq in Exy.
      assert (data_eqb (x::xs) (y::ys) = false) as ->.
      { apply Bool.not_true_is_false. rewrite data_eqb_true_iff.
        intro Hc; inversion Hc; congruence. }
      destruct (Nat.leb x y) eqn:Lxy, (Nat.leb y x) eqn:Lyx; cbn; try reflexivity.
      apply Nat.leb_le in Lxy, Lyx.
      exfalso. apply Exy. apply Nat.le_antisymm; assumption.
Qed.

(** Set membership over an *interval* set: each element is a closed range
    [lo, hi] (an exact element is the degenerate [x, x]; a prefix/CIDR like
    10.0.0.0/8 is [10.0.0.0, 10.255.255.255]).  Membership is [lo <= x <= hi]
    by big-endian order — so a point set reduces to equality ([data_le_antisym])
    while interval/prefix sets are faithfully expressible. *)
Definition data_in_iv (x : data) (iv : data * data) : bool :=
  andb (data_le (fst iv) x) (data_le x (snd iv)).
Definition set_mem (x : data) (s : list (data * data)) : bool :=
  existsb (data_in_iv x) s.

(** ** Per-field (cross-product) membership for CONCATENATED sets.

    A concatenated set (NFT_SET_CONCAT) is NOT one flat lexicographic interval
    over the concatenated key: the kernel is told each field's length
    (NFTA_SET_FIELD_LEN, nf_tables.h) and the pipapo backend matches EACH FIELD
    against its OWN [lo,hi] independently — the set is the CROSS-PRODUCT of the
    per-field intervals.  So for `ip daddr . tcp dport { 10.0.0.0/8 . 10-23 }`
    the element is {daddr in [10.0.0.0,10.255.255.255]} x {dport in [10,23]},
    and a packet matches iff BOTH hold (a flat lexicographic test over the
    concatenation is an unsound over-approximation).

    The stored element bound [lo] (resp. [hi]) is the per-field concatenation of
    the per-field lower (resp. upper) bounds, laid out with the SAME per-field
    widths as the packet's per-field values [vals].  We split [lo]/[hi] by those
    widths and test each field's slice independently. *)

(** Split [d] into successive chunks of the given byte [widths].  Every chunk
    but the LAST takes exactly its width; the final field takes ALL remaining
    bytes.  Giving the last field the remainder means that for a SINGLE field the
    chunk is the whole bound [d] (no truncation), so the per-field test on one
    field coincides definitionally with the flat [data_in_iv] — single-field
    interval/point sets are byte-for-byte unchanged.  For a well-formed
    multi-field bound (the per-field concatenation) the remainder of the last
    split is exactly that last field's bytes, so this matches the kernel. *)
Fixpoint split_by (widths : list nat) (d : data) : list data :=
  match widths with
  | [] => []
  | [_] => [d]
  | w :: ws => firstn w d :: split_by ws (skipn w d)
  end.

(** ** Register-slot layout of a concatenated set key.

    The kernel and nftables userspace lay out a concatenated set key by placing
    each field in its OWN 32-bit register slot (NFT_REG32_SIZE = 4 bytes,
    include/linux/netfilter/nf_tables.h:50): each field contributes
    [netlink_padded_len] = its byte length ROUNDED UP to a multiple of 4
    (include/netlink.h:122-127), and the packet lookup key advances by a whole
    [netlink_register_space] register per field (src/netlink_linearize.c:120-128,
    src/evaluate.c:5192).  So a 1-byte [ct direction] occupies a full 4-byte
    slot, a 2-byte port occupies a full 4-byte slot, etc.; e.g. the element of
    `{ original . 0x12345678 }` is the 8-byte key [00 00 00 00][12 34 56 78].
    Within a slot the field's bytes sit at the FRONT (low offset), with zero
    padding in the trailing bytes — verified by the golden corpus, which displays
    a 2-byte dport=80 in its slot as [00 50](.. 00 00 padding) and a 1-byte
    ct-state=8 as [00 00 00 08] only because state is itself a 4-byte field.
    This project's own bytecode/codec layer already uses one register slot per
    field (codec.ml:167).

    [reg_slot n] rounds [n] up to the next multiple of [NFT_REG32_SIZE] = 4.
    (The ifname kind is 16 bytes, already a multiple of 4, so the generic
    round-up handles it too.) *)
Definition reg_slot (n : nat) : nat := 4 * Nat.div (n + 3) 4.

(** One field's interval test: [lo_i <= val_i <= hi_i] in big-endian order. *)
Definition field_in_iv (val : data) (lohi : data * data) : bool :=
  andb (data_le (fst lohi) val) (data_le val (snd lohi)).

(** A list of per-field values matches one concatenated element [iv=(lo,hi)] iff
    every field's value lies in its own per-field interval.

    [lo] and [hi] are the per-field concatenation of the per-field bounds, each
    field laid out in its 4-byte register SLOT (so a sub-4-byte non-last field is
    followed by the kernel's zero padding — the source of standing worklist #4).
    We split [lo]/[hi] by the per-field SLOT widths (= [reg_slot] of each field's
    raw length), then for each field compare only the field's real bytes
    ([firstn (length val)] of its slot) against the field value, discarding the
    trailing register padding.

    For a SINGLE field, [split_by [reg_slot w] d = [d]] (last-takes-remainder),
    the stored bound has length exactly [length val], and [firstn (length val) d
    = d], so this coincides definitionally with the flat [data_in_iv] — see
    [concat_in_iv_single]. *)
Definition concat_in_iv (vals : list data) (iv : data * data) : bool :=
  match vals with
  | [v] =>
      (* SINGLE field: no register padding is possible (there is no following
         field), so the stored bound IS the field's bytes; test it directly.
         This keeps single-field interval/point sets byte-for-byte identical to
         the flat [data_in_iv] and makes [concat_in_iv_single] hold for ALL
         bounds (used by the single-register [ILookup] correctness proof). *)
      field_in_iv v iv
  | _ =>
      let slots := map (fun v => reg_slot (@length byte v)) vals in
      let los := split_by slots (fst iv) in
      let his := split_by slots (snd iv) in
      forallb (fun t => let '(val, (lo, hi)) := t in
                 field_in_iv val (firstn (@length byte val) lo,
                                  firstn (@length byte val) hi))
              (combine vals (combine los his))
  end.

(** Membership of a per-field-decomposed key in a concatenated set: some element
    whose per-field intervals all contain the corresponding field value. *)
Definition concat_set_mem (vals : list data) (s : list (data * data)) : bool :=
  existsb (concat_in_iv vals) s.

(** ** Regression: for a SINGLE field, per-field membership coincides DEFINITIONALLY
    with the old flat [set_mem] — the last (here only) field takes the whole bound,
    so no truncation happens and [concat_in_iv [v] (lo,hi) = data_in_iv v (lo,hi)].
    This guarantees single-field interval/point sets are byte-for-byte unchanged
    (and is what makes the compiled single-register [ILookup] still match the DSL
    [MSetT]/single-field [MConcatSet]). *)
Lemma concat_in_iv_single : forall (v lo hi : data),
  concat_in_iv [v] (lo, hi) = data_in_iv v (lo, hi).
Proof.
  intros v lo hi. unfold concat_in_iv, data_in_iv, field_in_iv. reflexivity.
Qed.

Lemma concat_set_mem_single : forall (v : data) (s : list (data * data)),
  concat_set_mem [v] s = set_mem v s.
Proof.
  intros v s. unfold concat_set_mem, set_mem.
  induction s as [| [lo hi] s' IH]; cbn [existsb]; [reflexivity|].
  rewrite concat_in_iv_single, IH. reflexivity.
Qed.

Lemma data_eqb_sym : forall a b, data_eqb a b = data_eqb b a.
Proof.
  intros a b. unfold data_eqb.
  destruct (list_eq_dec Nat.eq_dec a b), (list_eq_dec Nat.eq_dec b a); congruence.
Qed.
