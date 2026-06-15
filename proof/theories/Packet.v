(** * Packet: the object both languages observe.

    nftables matches inspect two kinds of data:
      - metadata computed by the kernel (e.g. [l4proto], the L4 protocol number),
        accessed by a [meta] expression keyed by a [meta_key];
      - raw header bytes, accessed by a [payload] expression as
        (base, offset, length) where base is the network or transport header.

    We model a packet as a metadata function plus the network/transport header
    byte strings.  This is faithful to how nft's bytecode reads a packet, and it
    is the *single* packet representation used by BOTH the declarative semantics
    and the bytecode VM, so the equivalence theorem is about real behaviour, not
    an artefact of two different packet models. *)

From Stdlib Require Import List NArith.
From Nft Require Import Bytes.
Import ListNotations.

(** Metadata keys (numeric kernel metadata).  Adding a key is just a new
    constructor — the compiler proof is generic over [meta_key]. *)
Inductive meta_key : Type :=
| MKl4proto | MKnfproto | MKprotocol | MKmark
| MKiif | MKoif | MKiiftype | MKoiftype | MKiifname | MKoifname
| MKlen | MKpkttype | MKcpu | MKskuid | MKskgid | MKpriority.

(** Conntrack keys (read by a [ct load] expression). *)
Inductive ct_key : Type :=
| CKstate | CKstatus | CKmark | CKdirection | CKexpiration | CKid.

(** Protocol an [exthdr load] reads from (IPv6 extension headers / TCP options). *)
Inductive exthdr_proto : Type :=
| EPipv6 | EPtcpopt.

(** Payload bases: which header a [payload load] reads from. *)
Inductive pbase : Type :=
| PLink
| PNetwork
| PTransport
| PInner
| PTunnel.

Record packet : Type := {
  pkt_meta : meta_key -> data;   (* kernel-computed metadata *)
  pkt_ct   : ct_key -> data;     (* conntrack state *)
  pkt_eh   : exthdr_proto -> nat -> nat -> nat -> data;  (* exthdr: proto htype off len *)
  pkt_lh   : list byte;          (* link-header bytes (e.g. Ethernet) *)
  pkt_nh   : list byte;          (* network-header bytes (e.g. IPv4/IPv6) *)
  pkt_th   : list byte;          (* transport-header bytes (e.g. TCP/UDP) *)
  pkt_ih   : list byte;          (* inner-header bytes (tunnelled packet) *)
  pkt_tnl  : list byte;          (* tunnel-header bytes *)
}.

(** Read [len] bytes at [off] from a header byte string. *)
Definition slice (bs : list byte) (off len : nat) : data :=
  firstn len (skipn off bs).

(** A payload read, shared by the DSL field semantics and the bytecode VM. *)
Definition read_payload (b : pbase) (off len : nat) (p : packet) : data :=
  match b with
  | PLink      => slice (pkt_lh p) off len
  | PNetwork   => slice (pkt_nh p) off len
  | PTransport => slice (pkt_th p) off len
  | PInner     => slice (pkt_ih p) off len
  | PTunnel    => slice (pkt_tnl p) off len
  end.
