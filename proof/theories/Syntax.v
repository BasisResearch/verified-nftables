(** * Syntax: the declarative nftables DSL.

    This is the high-level, human-facing surface that [nft] accepts:
    a ruleset is a list of tables, a table a list of named chains, a chain a
    policy plus an ordered list of rules, and a rule a conjunction of match
    conditions terminated by a verdict.

    Each high-level [field] (e.g. "tcp dport") *denotes* a concrete way to read
    the packet, given by [field_load].  This denotation is the single source of
    truth shared by the semantics (which reads the field from the packet) and
    the compiler (which emits a load instruction for it).  A bug in an offset
    would therefore show up either in the equivalence proof or — against the
    real kernel — in differential testing; it cannot hide. *)

From Stdlib Require Import List NArith String.
From Nft Require Import Bytes Packet Verdict.
Import ListNotations.

(** How to read a field's value out of a packet. *)
Inductive loaddesc : Type :=
| LMeta    (k : meta_key)
| LPayload (b : pbase) (off len : nat).

(** The high-level header/metadata fields the DSL can match on. *)
Inductive field : Type :=
| FMetaL4proto          (* meta l4proto *)
| FIpSaddr              (* ip saddr   : network header, offset 12, 4 bytes *)
| FIpDaddr              (* ip daddr   : network header, offset 16, 4 bytes *)
| FTcpSport             (* tcp sport  : transport header, offset 0, 2 bytes *)
| FTcpDport.            (* tcp dport  : transport header, offset 2, 2 bytes *)

(** The denotation of each field as a load.  These offsets/lengths mirror the
    IPv4 and TCP header layouts that [nft] itself uses (validated against
    [nft --debug=netlink]). *)
Definition field_load (f : field) : loaddesc :=
  match f with
  | FMetaL4proto => LMeta MKl4proto
  | FIpSaddr     => LPayload PNetwork 12 4
  | FIpDaddr     => LPayload PNetwork 16 4
  | FTcpSport    => LPayload PTransport 0 2
  | FTcpDport    => LPayload PTransport 2 2
  end.

(** Evaluate a load against a packet. *)
Definition do_load (ld : loaddesc) (p : packet) : data :=
  match ld with
  | LMeta k         => pkt_meta p k
  | LPayload b o l  => read_payload b o l p
  end.

(** The value of a field in a packet. *)
Definition field_value (f : field) (p : packet) : data :=
  do_load (field_load f) p.

(** A match condition: equality / inequality of a field against an immediate. *)
Inductive matchcond : Type :=
| MEq  (f : field) (v : data)
| MNeq (f : field) (v : data).

(** A rule: a conjunction of match conditions and a verdict. *)
Record rule : Type := {
  r_matches : list matchcond;
  r_verdict : verdict;
}.

(** A base chain: a default policy and an ordered list of rules. *)
Record chain : Type := {
  c_policy : verdict;
  c_rules  : list rule;
}.

(** Organisational layers (carried through to the control-plane command list;
    the packet-filtering theorem is stated per base chain). *)
Record table : Type := {
  t_name   : string;
  t_chains : list (string * chain);
}.

Definition ruleset := list table.
