(* Regression for the concatenated interval/range set fix.

   A concatenated set (NFT_SET_CONCAT) is matched FIELD-BY-FIELD: the kernel is
   told each field's length (NFTA_SET_FIELD_LEN, nf_tables.h:369-373) and the
   pipapo backend matches each field against its OWN [lo,hi] independently — the
   set is the CROSS-PRODUCT of the per-field intervals, NOT one flat
   lexicographic interval over the concatenated key.  (evaluate.c:1819 records
   field_len[]; netlink_linearize.c:126-129 gives each field its own register
   slot.)  Golden 2-D range element tests/py/inet/sets.t.payload.inet:32:
     element 0a000000 . 000a - 0affffff . 0017
   i.e. daddr in 10.0.0.0/8 and dport in [10,23].

   The model evaluates MConcatSet membership per-field via [concat_set_mem]
   (Bytes.v), and the parser stores each element as the per-field concatenation
   lo = (lo_1 ++ .. ++ lo_n), hi = (hi_1 ++ .. ++ hi_n).  The naive flat
   alternative —
     set_mem (concat (map field_value fields)) (e_set ...)
   a flat big-endian lexicographic test over the WHOLE concatenation — is an
   UNSOUND over-approximation: it accepts packets the kernel drops.

   Concrete witness: the 2-D element
     lo = 10.0.0.0 . dport 10,  hi = 10.255.255.255 . dport 23
   and a packet with daddr = 10.0.0.5, dport = 100.
   Per-field: daddr IS in [10.0.0.0, 10.255.255.255] but dport 100 is NOT in
   [10,23] -> kernel REJECTS.  Flat lexicographic: lo <= key <= hi -> ACCEPTS.
   The theorems below prove the per-field test rejects it (sound) while the flat
   test accepts it (refuting that alternative), and that single-field sets
   behave identically under both. *)

From Stdlib Require Import List Bool.
From Nft Require Import Bytes.
Import ListNotations.

(* daddr 4 bytes (10.0.0.0/8 = [10.0.0.0, 10.255.255.255]) . dport 2 bytes [10,23].
   The kernel lays each field in its OWN 4-byte register slot (NFT_REG32_SIZE
   round-up; see [reg_slot] in Bytes.v): daddr fills its 4-byte slot exactly, and
   the 2-byte dport sits at the FRONT of a 4-byte slot followed by two zero
   padding bytes — verified by the golden corpus, which displays a 2-byte
   dport=80 in its slot as 0050. *)
Definition lo : data := [10;0;0;0] ++ [0;10;0;0].
Definition hi : data := [10;255;255;255] ++ [0;23;0;0].
Definition the_set : list (data * data) := [(lo, hi)].

(* per-field value list for daddr 10.0.0.5, dport 100 *)
Definition vals_bad : list data := [[10;0;0;5]; [0;100]].
(* both fields in range: daddr 10.0.0.5, dport 20 *)
Definition vals_good : list data := [[10;0;0;5]; [0;20]].
(* daddr out of range: 11.0.0.5, dport 20 *)
Definition vals_dout : list data := [[11;0;0;5]; [0;20]].

(* the flat key of the refuted alternative (concatenation of the per-field values) *)
Definition key_bad : data := List.concat vals_bad.

(* THE REFUTED ALTERNATIVE: a flat lexicographic [set_mem] over the concatenated
   key ACCEPTS the bad packet the kernel drops. *)
Theorem old_flat_wrongly_accepts : set_mem key_bad the_set = true.
Proof. vm_compute. reflexivity. Qed.

(* THE MODEL: per-field membership REJECTS it (dport 100 not in [10,23]) — sound. *)
Theorem per_field_rejects_bad : concat_set_mem vals_bad the_set = false.
Proof. vm_compute. reflexivity. Qed.

(* per-field ACCEPTS only when BOTH fields are in their own interval. *)
Theorem per_field_accepts_good : concat_set_mem vals_good the_set = true.
Proof. vm_compute. reflexivity. Qed.

(* per-field REJECTS when the first field is out of range (regardless of dport). *)
Theorem per_field_rejects_dout : concat_set_mem vals_dout the_set = false.
Proof. vm_compute. reflexivity. Qed.

(* The two tests observably differ exactly on the witness. *)
Theorem fix_changes_behaviour :
  concat_set_mem vals_bad the_set <> set_mem key_bad the_set.
Proof. vm_compute. discriminate. Qed.

(* Regression: single-field sets are byte-for-byte identical under both tests
   (per-field on one field IS the flat test). *)
Theorem single_field_unchanged : forall (v : data) (s : list (data * data)),
  concat_set_mem [v] s = set_mem v s.
Proof. exact concat_set_mem_single. Qed.

(* A single-field interval/point set example. *)
Theorem single_field_example :
  concat_set_mem [[10;0;0;5]] [([10;0;0;0],[10;255;255;255])] = true
  /\ concat_set_mem [[11;0;0;5]] [([10;0;0;0],[10;255;255;255])] = false.
Proof. split; vm_compute; reflexivity. Qed.

(* ** Register-slot padding for a SUB-4-BYTE NON-LAST field.

   The kernel pads each field UP to its 4-byte register slot, so the element of
   `ct direction . ct mark { original . 0x12345678 }` is the 8-byte key
   [00 00 00 00][12 34 56 78]: a 1-byte ct-direction in a full 4-byte slot
   (golden tests/py/any/ct.t.payload:482-490, `ct load direction => reg 1`,
   `ct load mark => reg 9` — the 4-byte mark jumps to the NEXT 4-byte slot, NOT
   byte-contiguous after the 1-byte direction).

   The model splits the stored element by the 4-byte SLOT widths, so fed the
   kernel's actual element bytes it returns the kernel's verdict.  The refuted
   alternative (split by RAW field widths [1;4], last-takes-remainder) expects the
   contiguous 5-byte layout [00][12 34 56 78] and REJECTS the kernel's padded
   element — a provable verdict divergence.  These theorems pin the slot split. *)

(* per-field values: ct direction=0 (1 byte), ct mark=0x12345678 (4 bytes) *)
Definition ct_vals : list data := [ [0]; [18;52;86;120] ].
(* the KERNEL element: each field in a 4-byte slot (direction zero-padded) *)
Definition ct_kern_elem : data := [0;0;0;0; 18;52;86;120].
Definition ct_kern_set : list (data * data) := [(ct_kern_elem, ct_kern_elem)].

(* The model ACCEPTS the kernel-faithful padded element (the kernel
   matches this packet against `{original . 0x12345678}`). *)
Theorem ct_kern_padded_accepted :
  concat_set_mem ct_vals ct_kern_set = true.
Proof. vm_compute. reflexivity. Qed.

(* And it correctly REJECTS when EITHER the (sub-4-byte) direction slot or the
   mark slot disagrees: direction=1 vs the element's 0-slot, and a wrong mark. *)
Theorem ct_kern_padded_rejects_other :
  concat_set_mem [ [1]; [18;52;86;120] ] ct_kern_set = false        (* dir 1 <> 0 *)
  /\ concat_set_mem [ [0]; [135;101;67;33] ] ct_kern_set = false.   (* mark 0x87654321 *)
Proof. split; vm_compute; reflexivity. Qed.

(* A non-last sub-4-byte range field is range-tested within its slot:
   ct direction . ct mark { original-reply . 0x12345678 } has direction in
   [0,1] (slot [00 00 00 00]..[01 00 00 00]); direction 1 still matches. *)
Theorem ct_kern_slot_range :
  concat_set_mem [ [1]; [18;52;86;120] ]
    [([0;0;0;0; 18;52;86;120],[1;0;0;0; 18;52;86;120])] = true.
Proof. vm_compute. reflexivity. Qed.
