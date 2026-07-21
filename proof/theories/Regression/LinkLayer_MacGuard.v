(** Link-layer (L2 / `ether`) payload load — the mac-header-present guard.

    ── Kernel truth ─────────────────────────────────────────────────────────────
    nft_payload_eval (net/netfilter/nft_payload.c), the LINK-LAYER base case:

        case NFT_PAYLOAD_LL_HEADER:
            if (!skb_mac_header_was_set(skb) || skb_mac_header_len(skb) == 0)
                goto err;                     // <-- NFT_BREAK: rule does NOT match
            ...
            offset = skb_mac_header(skb) - skb->data;
            break;

    So an `ether saddr` / `ether daddr` / `ether type` (all NFT_PAYLOAD_LL_HEADER
    loads) BREAKS the rule whenever the skb has no MAC header — the standard case
    for LOCALLY-GENERATED packets at the `output`/`postrouting` hooks, where the L2
    header has not yet been built.  A broken load makes the match FAIL (just like a
    transport load on a fragment / no-L4 packet), so the rule is SKIPPED and the
    chain falls through to its policy.

    Concretely, the kernel behaviour of

        chain output { type filter hook output priority 0; policy accept;
                       ether saddr aa:bb:cc:dd:ee:ff drop }

    on a locally-generated packet (no MAC header) is ACCEPT (the `ether saddr` load
    BREAKs -> rule skipped -> policy accept).

    ── Model ────────────────────────────────────────────────────────────────────
    The packet record carries [pkt_have_l2 : bool] (= skb_mac_header_was_set(skb)
    && skb_mac_header_len(skb) != 0), and [read_payload_ok] gates the PLink base on
    it, mirroring the existing L4 guard ([pkt_have_l4]/[pkt_fragoff]) on
    PTransport/PInner:

        read_payload_ok PLink off len p
          = pkt_have_l2 p && negb (length (pkt_lh p) <? off+len)

    So a locally-generated packet ([pkt_have_l2 := false]) BREAKs every `ether`
    load, the rule is skipped, and the chain ACCEPTS — matching the kernel.  An
    L2-bearing packet ([pkt_have_l2 := true]) reads the link header.

    Regression gate: [ether_load_breaks_without_mac_header],
    [model_accepts_like_kernel]/[_mut], and [model_drops_with_mac_header] lock in
    the guard; a model regression to an unguarded L2 read (an `ether saddr` rule
    dropping a locally-generated packet the kernel accepts) makes them
    unprovable. *)

From Stdlib Require Import List String NArith.
From Nft Require Import Bytes Packet Verdict Syntax Semantics.
Import ListNotations.

(* Pins below hold at EVERY netfilter hook [h] (no rule here carries a NAT
   terminal, so the hook is inert); the section generalizes each statement. *)
Section AtHook.
Context (h : hook_id).

(* `ether saddr aa:bb:cc:dd:ee:ff` lowers to MEq FEtherSaddr <6 bytes>
   (FEtherSaddr = LPayload PLink 6 6). *)
Definition src_mac : data := [0xaa;0xbb;0xcc;0xdd;0xee;0xff].

Definition ether_saddr_drop : rule :=
  {| r_body := [ BMatch (MEq FEtherSaddr src_mac) ];
     r_outcome := OVerdict Drop; r_after := [] |}.

(* The output base chain, policy accept (the common default). *)
Definition output_chain : chain :=
  {| c_policy := Accept; c_rules := [ ether_saddr_drop ] |}.

Definition env0 : env :=
  {| e_set := fun _ => []; e_vmap := fun _ => []; e_map := fun _ => [];
     e_routes := []; e_rt := fun _ => []; e_limit := fun _ => 0;
     e_quota := fun _ => 0; e_ifaddrs := fun _ => []; e_ifaddrs6 := fun _ => [];
     e_connlimit := fun _ => []; e_ct := fun _ _ => []; e_nat := fun _ => None;
     e_numgen := fun _ => 0 |}.

(* A LOCALLY-GENERATED output packet: skb_mac_header_was_set(skb) is FALSE here
   (pkt_have_l2 := false), so any `ether` load goto-err's (NFT_BREAK).  We still
   hand it a 14-byte [pkt_lh] (full ethernet layout: 6 dst, 6 src, 2 type) whose
   SOURCE-MAC bytes [6..12) are exactly src_mac — to show the guard, not the byte
   length, is what makes the load BREAK. *)
Definition locally_generated : packet :=
  {| pkt_meta := fun _ => [];
     pkt_sock := fun _ => []; pkt_eh := fun _ _ _ _ _ => [];
     pkt_lh := [0;0;0;0;0;0] ++ src_mac ++ [0x08;0x00];   (* 14-byte L2 header *)
     pkt_nh := []; pkt_th := []; pkt_ih := [];
     pkt_tnl := []; pkt_fibkey := fun _ => []; pkt_numgen := fun _ => [];
     pkt_osf := []; pkt_tunnel := fun _ => []; pkt_symhash := fun _ _ => [];
     pkt_xfrm := fun _ _ _ => []; pkt_ctdir := fun _ _ => [];
     pkt_inner := fun _ _ _ _ => [];
     pkt_have_l2 := false;                     (* no MAC header built *)
     pkt_have_l4 := false; pkt_fragoff := 0;
     pkt_flow := [1;2;3;4]; pkt_untracked := false; pkt_ctdir_orig := true; pkt_ct_present := true |}.

(* The SAME packet but WITH a built MAC header (e.g. a forwarded/ingress packet at
   prerouting/forward): the `ether saddr` load succeeds and the rule DROPS. *)
Definition has_l2 : packet :=
  {| pkt_meta := fun _ => [];
     pkt_sock := fun _ => []; pkt_eh := fun _ _ _ _ _ => [];
     pkt_lh := [0;0;0;0;0;0] ++ src_mac ++ [0x08;0x00];
     pkt_nh := []; pkt_th := []; pkt_ih := [];
     pkt_tnl := []; pkt_fibkey := fun _ => []; pkt_numgen := fun _ => [];
     pkt_osf := []; pkt_tunnel := fun _ => []; pkt_symhash := fun _ _ => [];
     pkt_xfrm := fun _ _ _ => []; pkt_ctdir := fun _ _ => [];
     pkt_inner := fun _ _ _ _ => [];
     pkt_have_l2 := true;                      (* MAC header present *)
     pkt_have_l4 := false; pkt_fragoff := 0;
     pkt_flow := [1;2;3;4]; pkt_untracked := false; pkt_ctdir_orig := true; pkt_ct_present := true |}.

(* The `ether saddr` load BREAKs on a packet with no MAC header — it is NOT
   loadable in the model, mirroring the kernel's goto-err. *)
Lemma ether_load_breaks_without_mac_header :
  field_loadable FEtherSaddr locally_generated = false.
Proof. vm_compute. reflexivity. Qed.

(* Consequently the rule is SKIPPED and the chain falls through to its accept
   policy — exactly the kernel verdict; an unguarded L2 read would Drop here. *)
Theorem model_accepts_like_kernel :
  eval_chain output_chain env0 locally_generated = Accept.
Proof. vm_compute. reflexivity. Qed.

(* The same property holds via the stateful evaluator. *)
Theorem model_accepts_like_kernel_mut :
  eval_chain_mut h output_chain env0 locally_generated = Accept.
Proof. vm_compute. reflexivity. Qed.

(* With a built MAC header the load succeeds and the rule legitimately DROPS,
   so the L2 guard has not made the model vacuous. *)
Lemma ether_load_ok_with_mac_header :
  field_loadable FEtherSaddr has_l2 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem model_drops_with_mac_header :
  eval_chain output_chain env0 has_l2 = Drop.
Proof. vm_compute. reflexivity. Qed.

(* For contrast: the analogous TRANSPORT load DOES carry its own guard — the model
   correctly fails a transport read on a no-L4 packet.  Both layers now guard. *)
Lemma transport_load_correctly_breaks :
  field_loadable FThDport locally_generated = false.
Proof. vm_compute. reflexivity. Qed.

End AtHook.
