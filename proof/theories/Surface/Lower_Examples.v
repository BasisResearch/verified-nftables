(** * Surface.Lower_Examples: M4 non-vacuity witnesses.

    Pinned [vm_compute] witnesses that the verified statement / NAT / tproxy
    immediate lowering produces the HISTORICAL bytes the golden corpus checks
    end-to-end, and that the datatype lattice's width/byteorder decisions are
    exercised in Coq (the coverage that the deleted OCaml KIND-PARITY test used
    to pin against the now-removed OCaml `kind` table).  These are WITNESSES —
    reflexivity is expected and appropriate (there is no independent evaluator
    for a statement immediate to erase against). *)

From Stdlib Require Import List NArith String.
From Nft Require Import Bytes Packet Verdict Bytecode Syntax Nftval Elab
  Ast Datatype Symbols Selector Typecheck Typed Lower.
Import ListNotations.
Local Open Scope string_scope.

(** `dnat to 1.2.3.4:8080` — the IPv4-literal address goes into [nat_addr_imm],
    the port (8080 = 0x1f90) into [nat_extra] as a big-endian 2-byte immediate,
    and a specified port sets NF_NAT_RANGE_PROTO_SPECIFIED (flags bit 0x2). *)
Example lower_dnat_addr_port_example :
  addr_nat_spec NKdnat (Some 8080) 0 (SVIp4 [1;2;3;4])
  = Some {| nat_addr_imm := Some [1;2;3;4]; nat_field := None; nat_map := None;
            nat_src := None; nat_extra := NXimm None (Some [31;144]) None;
            nat_kind := NKdnat; nat_family := NFip4; nat_flags := 2 |}.
Proof. vm_compute. reflexivity. Qed.

(** `ct mark set 0x64` — the ct-mark register is a 4-byte HOST-endian value, so
    the immediate is the little-endian encoding [0x64;0;0;0]. *)
Example lower_ct_mark_set_example :
  lower_ct_set "mark" (SVNum 100) = LOk (SCtSet CKmark (VImm [100;0;0;0])).
Proof. vm_compute. reflexivity. Qed.

(** `tproxy ip to 10.0.0.99:3128` — IPv4-literal target address + big-endian
    port (3128 = 0x0c38), family "ip". *)
Example lower_tproxy_port_example :
  mk_tproxy "ip" "" (Some (SVIp4 [10;0;0;99])) (Some 3128)
  = LOk {| tp_addr := Some [10;0;0;99]; tp_port := Some [12;56];
           tp_portmap := None; tp_family := "ip" |}.
Proof. vm_compute. reflexivity. Qed.

(** Coverage: the datatype lattice's width AND byteorder decisions, exercised
    through the sole verified encode path [Nftval.encode (resolve_value dt v)].
    Spans big-endian (inet_service 2B, ct_state 4B, ipv4 4B, inet_proto 1B,
    ether 6B) and HOST-endian (mark 4B LE, fib_addrtype 4B LE) registers, so a
    width or byteorder regression flips a pinned byte. *)
Example kind_encode_coverage :
  map (fun p => match resolve_value (fst p) (snd p) with
                | Some tv => Some (Nftval.encode tv)
                | None => None end)
    [ (DTinet_service, SVSym "https");
      (DTmark, SVNum 258);
      (DTfib_addrtype, SVSym "local");
      (DTct_state, SVSym "established");
      (DTinet_proto, SVSym "tcp");
      (DTipv4, SVIp4 [192;168;0;1]);
      (DTether, SVMac [0;1;2;3;4;5]) ]
  = [ Some [1;187]; Some [2;1;0;0]; Some [2;0;0;0]; Some [0;0;0;2];
      Some [6]; Some [192;168;0;1]; Some [0;1;2;3;4;5] ].
Proof. vm_compute. reflexivity. Qed.

(** Fail-loud at the statement boundary: an unsettable meta key and an unknown
    NAT flag are explicit [lerr]s (never a silent OCaml byte). *)
Example lower_meta_set_unsettable_refused :
  lower_meta_set "iifname" (SVNum 1) = LErr (LEmetaSet "iifname").
Proof. vm_compute. reflexivity. Qed.

Example nat_flags_unknown_refused :
  nat_flags_of ["bogus"] = LErr (LEnatFlag "bogus").
Proof. vm_compute. reflexivity. Qed.

(** `tproxy` to a non-IPv4-literal target is refused (fail-loud), not guessed. *)
Example tproxy_nonliteral_refused :
  mk_tproxy "ip" "" (Some (SVSym "somehost")) (Some 3128) = LErr LEtproxyTarget.
Proof. vm_compute. reflexivity. Qed.
