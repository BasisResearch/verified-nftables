(** * Regression: a non-wildcard interface-name match is an EXACT 16-byte compare.

    Real nftables stores the interface-name register as the full IFNAMSIZ=16-byte
    buffer and compares a literal NON-wildcard name in full, zero-padded.  The
    kernel emits a 16-byte cmp for the exact form and a SHORT cmp only for a
    trailing-'*' wildcard:

      meta iifname "dummy0"  =>  cmp eq reg1 0x64756d6d 0x79300000 0x00000000 0x00000000
                                 (golden any/meta.t.payload:198-199; "dummy0"+10 zero bytes)
      meta iifname "dummy*"  =>  cmp eq reg1 0x64756d6d 0x79
                                 (golden any/meta.t.payload:224-225; just the "dummy" prefix)

    The parser previously lowered EVERY non-wildcard name to its bare ASCII bytes
    (no zero pad).  The model evaluates MEq as a prefix compare
    [data_eqb (firstn (length v) field) v], so an unpadded literal collapsed both
    kernel encodings into ONE prefix match: `iifname "dummy0"` would then match an
    interface named "dummy0extra", which the kernel's full 16-byte compare rejects.
    This is the UNSOUND over-approximation fixed in nft_lower.ml (ifname_bytes now
    zero-pads a non-wildcard name to 16 bytes; a trailing unescaped '*' still emits
    the short prefix; an escaped trailing '\*' is a literal '*' and is padded).

    Here we pin the now-correct behaviour: the exact 16-byte register value is the
    only one that matches, and a same-prefix interface is rejected. *)

From Stdlib Require Import List Bool.
From Nft Require Import Bytes Packet Verdict Syntax Semantics.
Import ListNotations.

Definition e0 : env :=
  {| e_set := fun _ => []; e_vmap := fun _ => []; e_map := fun _ => [];
     e_routes := []; e_rt := fun _ => []; e_limit := fun _ => 0;
     e_quota := fun _ => 0; e_ifaddr := fun _ => []; e_ifaddr6 := fun _ => []; e_connlimit := fun _ => 0;
     e_ct := fun _ _ => []; e_nat := fun _ => None |}.

Definition pkt_ifn (nm : data) : packet :=
  {| pkt_env := e0;
     pkt_meta := fun k => match k with MKiifname => nm | _ => [] end;
     pkt_ct := fun _ => []; pkt_sock := fun _ => []; pkt_eh := fun _ _ _ _ _ => [];
     pkt_lh := []; pkt_nh := []; pkt_th := []; pkt_ih := []; pkt_tnl := [];
     pkt_fibkey := fun _ => []; pkt_numgen := fun _ => []; pkt_osf := [];
     pkt_tunnel := fun _ => []; pkt_symhash := fun _ _ => [];
     pkt_xfrm := fun _ _ _ => []; pkt_ctdir := fun _ _ => [];
     pkt_inner := fun _ _ _ _ => []; pkt_have_l4 := false; pkt_fragoff := 0; pkt_flow := []; pkt_untracked := false; pkt_ctdir_orig := true |}.

(* "dummy0" as the FIXED fix now emits it: 16-byte zero-padded (IFNAMSIZ). *)
Definition iif_dummy0_16 : data :=
  [100;117;109;109;121;48; 0;0;0;0; 0;0;0;0; 0;0].
Definition m_exact := MEq FMetaIifname iif_dummy0_16.

(* A trailing-'*' wildcard `iifname "dummy*"` still emits the SHORT 5-byte prefix. *)
Definition m_wild := MEq FMetaIifname [100;117;109;109;121].

(* the 16-byte register of an interface literally named "dummy0" *)
Definition reg_dummy0 : data := iif_dummy0_16.
(* the 16-byte register of the DISTINCT interface "dummy0e" ("dummy0extra" truncated
   into the 16-byte buffer) — a real, different interface the kernel rejects. *)
Definition reg_dummy0e : data :=
  [100;117;109;109;121;48;101;120;116;114;97; 0;0;0;0;0].

(** The exact 16-byte match accepts the interface it names. *)
Theorem exact_matches_dummy0 :
  eval_matchcond m_exact (pkt_ifn reg_dummy0) = true.
Proof. vm_compute. reflexivity. Qed.

(** The exact 16-byte match REJECTS a same-prefix but distinct interface — this
    is the soundness the fix restores (the old unpadded literal accepted it). *)
Theorem exact_rejects_prefix_iface :
  eval_matchcond m_exact (pkt_ifn reg_dummy0e) = false.
Proof. vm_compute. reflexivity. Qed.

(** The OLD (buggy) unpadded encoding would have wrongly accepted the distinct
    interface: a 6-byte prefix value matches both registers.  We exhibit this to
    document the bug class the fix closes. *)
Definition m_buggy := MEq FMetaIifname [100;117;109;109;121;48].
Theorem old_unpadded_wrongly_accepts_prefix :
  eval_matchcond m_buggy (pkt_ifn reg_dummy0e) = true.
Proof. vm_compute. reflexivity. Qed.

(** The fix genuinely changes behaviour: on the distinct interface, the padded
    exact match and the old unpadded match disagree. *)
Theorem fix_changes_behaviour :
  eval_matchcond m_exact (pkt_ifn reg_dummy0e)
    <> eval_matchcond m_buggy (pkt_ifn reg_dummy0e).
Proof. vm_compute. discriminate. Qed.

(** A trailing-'*' wildcard correctly remains a PREFIX match: `iifname "dummy*"`
    matches any interface whose name starts with "dummy" (kernel short cmp). *)
Theorem wildcard_is_prefix :
  eval_matchcond m_wild (pkt_ifn reg_dummy0e) = true
  /\ eval_matchcond m_wild (pkt_ifn reg_dummy0) = true.
Proof. split; vm_compute; reflexivity. Qed.
