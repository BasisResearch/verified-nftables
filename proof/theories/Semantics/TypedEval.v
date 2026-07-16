(** * Semantics.TypedEval: the INDEPENDENT typed semantics of the new scalar
    match shapes (M2 seed of the T2 typed evaluator).

    Every clause here reads the field's register bytes, DECODES them as a
    number, and compares NUMERICALLY in [N] — never through the byte encoding
    the elaboration produces.  INDEPENDENCE is enforced mechanically: this
    file is whole-word-grep-clean of the encoding-side vocabulary (the M2
    acceptance gate greps this file for the five banned words and requires
    zero hits).  All reasoning that connects this semantics to the byte IR
    lives in Surface/Lower_Proofs.v ([txmatch_erasure] and the per-shape
    erasure theorems), where it costs real obligations: byte-lexicographic
    order vs numeric order (same-width big-endian only), the host-endian
    `hton` re-encoding (the historical core-byteorder bug class), and the
    bitwise-AND/XOR-vs-[N.land]/[N.lxor] distribution over byte strings.

    The semantics is PARTIAL ([option bool]); [None] is STUCK, and stuckness
    arises ONLY from type-incoherence:
      - the loaded register bytes do not decode at the shape's datatype
        (wrong width, or a non-byte in the modelled register);
      - an operand's width disagrees with the datatype's register width, or
        an operand does not fit its own declared width;
      - an operand's register byteorder disagrees with the datatype's
        (a host-endian value where the datatype stores big-endian);
      - a range over a register form with NO adjudicated numeric meaning
        (the plain host-endian [DThostint] range class — see
        [Typed.range_hton]'s rationale).
    A field whose LOAD breaks ([field_loadable] = false) is [Some false] —
    the kernel's NFT_BREAK rule-skip — never stuck.  Stuckness is REACHABLE:
    concrete [Example]s below exhibit stuck terms next to [Some]-valued ones
    on the same packet.

    The four M0 shapes ([TXElab]: typed eq / neq / prefix / wildcard) keep
    their Elab.v semantics verbatim ([Elab.eval_tmatch], whose agreement with
    the byte IR is the DEFINITIONAL consistency check
    [Elab.elab_matchcond_correct]); replacing THEM with independent numeric
    clauses is the T2/M5 milestone, not this one. *)

From Stdlib Require Import List PeanoNat Bool NArith String.
From Nft Require Import Bytes Packet Verdict Bytecode Syntax Nftval Elab
  Ast Datatype Selector Typed.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(** ** Numeric register reads. *)

(** Read a [w]-byte big-endian register value as a number: the bytes must
    have exactly the width and be genuine bytes; otherwise the value is
    undecodable and the read is stuck. *)
Definition read_be_N (w : nat) (d : data) : option N :=
  if Nat.eqb (List.length d) w && bytes_wfb d
  then Some (data_to_N d) else None.

(** Read a register value at a DATATYPE: host-endian datatypes store the
    number least-significant-byte first, so their numeric value is the
    big-endian reading of the REVERSED bytes. *)
Definition read_dt_N (dt : dtype) (d : data) : option N :=
  if byteorder_eqb (dt_byteorder dt) BoHost
  then read_be_N (dt_bytes dt) (rev d)
  else read_be_N (dt_bytes dt) d.

(** An operand fits a datatype's register: its own width is the register
    width, it fits that width, and its register byteorder is the datatype's
    (a host-endian-encoded value at a big-endian datatype — or vice versa —
    is incoherent: the register compare would read it in the wrong order). *)
Definition operand_ok (dt : dtype) (v : nftval) : bool :=
  Nat.eqb (val_width v) (dt_bytes dt)
  && val_wfb v
  && Bool.eqb (host_val v) (byteorder_eqb (dt_byteorder dt) BoHost).

(** Range bounds on the hton path are re-encoded big-endian regardless of the
    value's own register byteorder ([Typed.encode_be] normalises), so the
    byteorder-coherence conjunct is dropped there. *)
Definition bound_ok (dt : dtype) (v : nftval) : bool :=
  Nat.eqb (val_width v) (dt_bytes dt) && val_wfb v.

(* ------------------------------------------------------------------ *)
(** ** M3: the INDEPENDENT numeric membership of set / concat elements.

    A set element is a closed interval; membership of a DECODED register value
    is the numeric test [lo <= x <= hi] in [N] — never through the byte
    encoding or [data_le].  [set_mem_N] lifts it over an element list; the
    agreement with the byte-level [set_mem] over the ENCODED intervals is
    [Lower_Proofs.set_interval_erasure] (its obligation is byte-lexicographic
    order = numeric order, same-width big-endian — the M2 [data_le_num] lemma).

    For a CONCATENATED key each field is tested against its OWN decoded
    interval ([field_mem_N]); the byte side splits the slot-padded key by the
    per-field register slots and truncates the padding
    ([Lower_Proofs.concat_key_erasure]). *)

Definition iv_mem_N (x : N) (iv : data * data) : bool :=
  andb (data_to_N (fst iv) <=? x)%N (x <=? data_to_N (snd iv))%N.

Definition set_mem_N (x : N) (s : list (data * data)) : bool :=
  existsb (iv_mem_N x) s.

(** One field of a concatenated key: its decoded value against its decoded
    per-field interval bounds (the [firstn] takes only the field's real bytes,
    discarding the register-slot padding, before decoding). *)
Definition field_mem_N (fw : nat) (fx : N) (iv : data * data) : bool :=
  andb (data_to_N (firstn fw (fst iv)) <=? fx)%N
       (fx <=? data_to_N (firstn fw (snd iv)))%N.

(* ------------------------------------------------------------------ *)
(** ** The typed evaluator. *)

Definition eval_txm (t : txmatch) (e : env) (p : packet) : option bool :=
  match t with
  | TXElab m =>
      (* the four M0 shapes: Elab.v's semantics, verbatim (see header) *)
      Some (Elab.eval_tmatch m e p)

  | TXRange f dt neg lo hi =>
      if negb (field_loadable f p) then Some false else
      if negb (bound_ok dt lo && bound_ok dt hi) then None else
      if range_hton dt then
        (* mark / ifindex / fib_addrtype: the kernel-adjudicated hton path —
           the register is converted to network order, so the comparison is
           numeric on the host-endian reading of the loaded bytes *)
        match read_dt_N dt (field_value f e p) with
        | Some x => Some (xorb neg (andb (val_N lo <=? x)%N (x <=? val_N hi)%N))
        | None => None
        end
      else if byteorder_eqb (dt_byteorder dt) BoBig then
        (* big-endian registers: byte-lexicographic IS numeric (the
           range_erasure_be obligation) — but only against big-endian-encoded
           bounds, so a host-endian-encoded bound is incoherent here *)
        if host_val lo || host_val hi then None else
        match read_dt_N dt (field_value f e p) with
        | Some x => Some (xorb neg (andb (val_N lo <=? x)%N (x <=? val_N hi)%N))
        | None => None
        end
      else
        (* the UNADJUDICATED class: a plain range over a [DThostint] register
           (meta skuid/length/..., ct id/zone/...) byte-compares little-endian
           bytes lexicographically — that has no numeric meaning, and this
           semantics refuses to invent one (see Typed.range_hton).  STUCK. *)
        None

  | TXBitmask f dt op bits =>
      if negb (field_loadable f p) then Some false else
      if negb (byteorder_eqb (dt_byteorder dt) BoBig) then None else
      let m := bm_fold bits in
      if negb (m <? 256 ^ N.of_nat (dt_bytes dt))%N then None else
      match read_dt_N dt (field_value f e p) with
      | Some x =>
          Some match op with
               | SOpImplicit => negb (N.land x m =? 0)%N  (* (x & m) <> 0 *)
               | SOpBang     => (N.land x m =? 0)%N       (* (x & m) == 0 *)
               | SOpEq       => (x =? m)%N
               | SOpNe       => negb (x =? m)%N
               end
      | None => None
      end

  | TXBitfield spec neg v =>
      if negb (field_loadable (bf_field spec) p) then Some false else
      (* the field's bits must fit the loaded bytes and the value the field *)
      if negb ((bf_bits spec + bf_shift spec <=? 8 * bf_bytes spec)%nat
               && (v <? 2 ^ N.of_nat (bf_bits spec))%N) then None else
      match read_be_N (bf_bytes spec) (field_value (bf_field spec) e p) with
      | Some x =>
          Some (xorb neg
                  (N.land (N.shiftr x (N.of_nat (bf_shift spec)))
                          (N.ones (N.of_nat (bf_bits spec))) =? v)%N)
      | None => None
      end

  | TXBitwise f dt bop neg mask v =>
      if negb (field_loadable f p) then Some false else
      if negb (operand_ok dt mask && operand_ok dt v) then None else
      match read_dt_N dt (field_value f e p) with
      | Some x =>
          let r := match bop with
                   | BOand => N.land x (val_N mask)
                   | BOor  => N.lor  x (val_N mask)
                   | BOxor => N.lxor x (val_N mask)
                   end in
          Some (xorb neg (r =? val_N v)%N)
      | None => None
      end

  | TXFlag f neg v =>
      if negb (field_loadable f p) then Some false else
      if negb (v <? 256)%N then None else
      match read_be_N 1 (field_value f e p) with
      | Some x => Some (xorb neg (x =? v)%N)
      | None => None
      end
  end.

(* ------------------------------------------------------------------ *)
(** ** The semantics is REAL: concrete matches evaluate, and stuckness is
    REACHABLE (the M-D witnesses). *)

(** An environment whose conntrack table holds ESTABLISHED state and a
    host-endian ct mark 0x40 for every flow, and a TCP packet whose flags
    byte is SYN|ACK (0x12) and whose transport dport is 443. *)
Definition tev_env : env :=
  {| e_set := fun _ => []; e_vmap := fun _ => []; e_map := fun _ => [];
     e_routes := []; e_rt := fun _ => []; e_limit := fun _ => 0;
     e_quota := fun _ => 0; e_ifaddrs := fun _ => []; e_ifaddrs6 := fun _ => [];
     e_connlimit := fun _ => [];
     e_ct := fun _ k => match k with
                        | CKstate => [0;0;0;2]      (* established           *)
                        | CKmark  => [0x40;0;0;0]   (* host-endian 0x40      *)
                        | _ => []
                        end;
     e_nat := fun _ => None; e_numgen := fun _ => 0 |}.

Definition tev_pkt : packet :=
  {| pkt_meta := fun _ => [];
     pkt_sock := fun _ => []; pkt_eh := fun _ _ _ _ _ => [];
     pkt_lh := []; pkt_nh := [];
     (*        0 1 2 3–dport─┐                        flags(13)         *)
     pkt_th := [0;0;1;187;0;0;0;0;0;0;0;0;0;0x12];
     pkt_ih := []; pkt_tnl := [];
     pkt_fibkey := fun _ => []; pkt_numgen := fun _ => []; pkt_osf := [];
     pkt_tunnel := fun _ => []; pkt_symhash := fun _ _ => [];
     pkt_xfrm := fun _ _ _ => []; pkt_ctdir := fun _ _ => [];
     pkt_inner := fun _ _ _ _ => []; pkt_have_l2 := true; pkt_have_l4 := true;
     pkt_fragoff := 0; pkt_flow := []; pkt_untracked := false;
     pkt_ctdir_orig := true; pkt_ct_present := true |}.

(** `tcp flags syn` (implicit bitmask) matches the SYN|ACK packet;
    the explicit equality `tcp flags == syn` does NOT — numerically. *)
Example tev_tcpflags_implicit :
  eval_txm (TXBitmask FTcpFlags DTtcp_flag SOpImplicit [2%N]) tev_env tev_pkt
  = Some true.
Proof. vm_compute. reflexivity. Qed.
Example tev_tcpflags_eq :
  eval_txm (TXBitmask FTcpFlags DTtcp_flag SOpEq [2%N]) tev_env tev_pkt
  = Some false.
Proof. vm_compute. reflexivity. Qed.

(** `ct state established` matches; `tcp dport 100-200` does not (443). *)
Example tev_ct_state :
  eval_txm (TXBitmask FCtState DTct_state SOpImplicit [2%N]) tev_env tev_pkt
  = Some true.
Proof. vm_compute. reflexivity. Qed.
Example tev_port_range :
  eval_txm (TXRange FThDport DTinet_service false (VPort 100) (VPort 200))
           tev_env tev_pkt
  = Some false.
Proof. vm_compute. reflexivity. Qed.
Example tev_port_range_hit :
  eval_txm (TXRange FThDport DTinet_service false (VPort 400) (VPort 500))
           tev_env tev_pkt
  = Some true.
Proof. vm_compute. reflexivity. Qed.

(** `ct mark 0x32-0x45` on the hton path: the register holds host-endian
    [0x40;0;0;0], numerically 0x40 — inside the range. *)
Example tev_ctmark_range :
  eval_txm (TXRange FCtMark DTmark false (VHostInt 4 0x32) (VHostInt 4 0x45))
           tev_env tev_pkt
  = Some true.
Proof. vm_compute. reflexivity. Qed.

(** STUCK (reachable), three distinct incoherences on the SAME packet:
    - a range over a plain host-endian register class (meta skuid) — the
      unadjudicated byte-lex-over-little-endian form has no numeric meaning;
    - a width-incoherent comparison (a 2-byte port bound against the 4-byte
      ct mark register);
    - an undecodable stored value (the ct zone register bytes are absent —
      the flow table holds nothing for CKzone, so the 2-byte decode fails). *)
Example tev_stuck_hostint_range :
  eval_txm (TXRange FMetaSkuid (DThostint 4) false
              (VHostInt 4 2001) (VHostInt 4 2005)) tev_env tev_pkt
  = None.
Proof. vm_compute. reflexivity. Qed.
Example tev_stuck_width_mismatch :
  eval_txm (TXRange FCtMark DTmark false (VPort 22) (VPort 80)) tev_env tev_pkt
  = None.
Proof. vm_compute. reflexivity. Qed.
Example tev_stuck_undecodable :
  eval_txm (TXBitwise (FCtGen CKzone) (DThostint 2) BOand false
              (VHostInt 2 1) (VHostInt 2 1)) tev_env tev_pkt
  = None.
Proof. vm_compute. reflexivity. Qed.

(** A byteorder-incoherent operand is stuck: a HOST-endian-encoded value used
    as a bound of a BIG-endian port range. *)
Example tev_stuck_byteorder :
  eval_txm (TXRange FThDport DTinet_service false
              (VHostInt 2 100) (VHostInt 2 200)) tev_env tev_pkt
  = None.
Proof. vm_compute. reflexivity. Qed.

(** An unloadable field is a rule-skip ([Some false]), NEVER stuck: the same
    dport range on a packet with no transport header. *)
Example tev_unloadable_is_false :
  eval_txm (TXRange FThDport DTinet_service false (VPort 100) (VPort 200))
           tev_env
           (let p := tev_pkt in
            {| pkt_meta := pkt_meta p; pkt_sock := pkt_sock p;
               pkt_eh := pkt_eh p; pkt_lh := pkt_lh p; pkt_nh := pkt_nh p;
               pkt_th := []; pkt_ih := pkt_ih p; pkt_tnl := pkt_tnl p;
               pkt_fibkey := pkt_fibkey p; pkt_numgen := pkt_numgen p;
               pkt_osf := pkt_osf p; pkt_tunnel := pkt_tunnel p;
               pkt_symhash := pkt_symhash p; pkt_xfrm := pkt_xfrm p;
               pkt_ctdir := pkt_ctdir p; pkt_inner := pkt_inner p;
               pkt_have_l2 := true; pkt_have_l4 := false; pkt_fragoff := 0;
               pkt_flow := []; pkt_untracked := false; pkt_ctdir_orig := true;
               pkt_ct_present := true |})
  = Some false.
Proof. vm_compute. reflexivity. Qed.
