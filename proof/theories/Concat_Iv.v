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

   The old model evaluated MConcatSet membership as
     set_mem (concat (map field_value fields)) (e_set ...)
   a flat big-endian lexicographic test over the WHOLE concatenation, which is an
   UNSOUND over-approximation: it accepts packets the kernel drops.  The fix
   evaluates per-field via [concat_set_mem] (Bytes.v), and the parser stores each
   element as the per-field concatenation lo = (lo_1 ++ .. ++ lo_n),
   hi = (hi_1 ++ .. ++ hi_n).

   Concrete witness (the red agent's): the 2-D element
     lo = 10.0.0.0 . dport 10,  hi = 10.255.255.255 . dport 23
   and a packet with daddr = 10.0.0.5, dport = 100.
   Per-field: daddr IS in [10.0.0.0, 10.255.255.255] but dport 100 is NOT in
   [10,23] -> kernel REJECTS.  Flat lexicographic: lo <= key <= hi -> ACCEPTS.
   The theorems below prove the new per-field test rejects it (sound) while the
   old flat test accepted it (the bug), and that single-field sets are
   unchanged. *)

From Stdlib Require Import List Bool.
From Nft Require Import Bytes.
Import ListNotations.

(* daddr 4 bytes (10.0.0.0/8 = [10.0.0.0, 10.255.255.255]) . dport 2 bytes [10,23] *)
Definition lo : data := [10;0;0;0] ++ [0;10].
Definition hi : data := [10;255;255;255] ++ [0;23].
Definition the_set : list (data * data) := [(lo, hi)].

(* per-field value list for daddr 10.0.0.5, dport 100 *)
Definition vals_bad : list data := [[10;0;0;5]; [0;100]].
(* both fields in range: daddr 10.0.0.5, dport 20 *)
Definition vals_good : list data := [[10;0;0;5]; [0;20]].
(* daddr out of range: 11.0.0.5, dport 20 *)
Definition vals_dout : list data := [[11;0;0;5]; [0;20]].

(* the flat key the OLD model built (concatenation of the per-field values) *)
Definition key_bad : data := List.concat vals_bad.

(* THE BUG: the old flat lexicographic test ACCEPTS the bad packet. *)
Theorem old_flat_wrongly_accepts : set_mem key_bad the_set = true.
Proof. vm_compute. reflexivity. Qed.

(* THE FIX: per-field membership REJECTS it (dport 100 not in [10,23]) — sound. *)
Theorem per_field_rejects_bad : concat_set_mem vals_bad the_set = false.
Proof. vm_compute. reflexivity. Qed.

(* per-field ACCEPTS only when BOTH fields are in their own interval. *)
Theorem per_field_accepts_good : concat_set_mem vals_good the_set = true.
Proof. vm_compute. reflexivity. Qed.

(* per-field REJECTS when the first field is out of range (regardless of dport). *)
Theorem per_field_rejects_dout : concat_set_mem vals_dout the_set = false.
Proof. vm_compute. reflexivity. Qed.

(* The fix changes observable behaviour exactly on the bug witness. *)
Theorem fix_changes_behaviour :
  concat_set_mem vals_bad the_set <> set_mem key_bad the_set.
Proof. vm_compute. discriminate. Qed.

(* Regression: single-field sets are byte-for-byte unchanged (per-field on one
   field IS the old flat test). *)
Theorem single_field_unchanged : forall (v : data) (s : list (data * data)),
  concat_set_mem [v] s = set_mem v s.
Proof. exact concat_set_mem_single. Qed.

(* A single-field interval/point set still behaves as before. *)
Theorem single_field_example :
  concat_set_mem [[10;0;0;5]] [([10;0;0;0],[10;255;255;255])] = true
  /\ concat_set_mem [[11;0;0;5]] [([10;0;0;0],[10;255;255;255])] = false.
Proof. split; vm_compute; reflexivity. Qed.
