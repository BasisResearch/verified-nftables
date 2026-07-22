(** * Tutorial_Proofs: "this ruleset blocks EXACTLY 192.168.100.0/24".

    The worked instance for the tutorial in proof/CONFIG_PROOFS.md.  The ruleset
    is [rulesets/tutorial.nft]:

<<
      table ip tutorial {
        chain input {
          type filter hook input priority 0; policy accept;
          ip saddr 192.168.100.0/24 drop
        }
      }
>>

    [Tutorial_Gen.v] is the PARSER's output for that file (make gen), so what we
    prove below is a property of the parsed ruleset — and, via
    [Correct.compile_table_u_correct], of the compiled netlink bytecode.

    The headline is an EXACTNESS statement, universally quantified over packets
    AND over the four source-address bytes:

      the chain drops p  <->  p's source address is in 192.168.100.0/24
                              (i.e. its first three bytes are 192.168.100 —
                               192.168.100.0 through 192.168.100.255)

    Both directions in one iff: no in-range packet escapes, and no out-of-range
    packet is caught.  The proof uses only the [Nft_Tactics] exactness layer —
    no evaluator internals. *)

From Stdlib Require Import List String NArith Arith Lia.
From Nft Require Import Bytes Verdict Packet Syntax Semantics Nftval Eval_Fw
                        Tutorial_Gen Nft_Tactics.
Import ListNotations.
Open Scope string_scope.

(** Traversal budget: any successor works for this jump-free single-rule chain. *)
Definition tut_fuel : nat := 16.

(** Register the chains so the generic tactics need no per-module unfold list. *)
#[local] Hint Unfold tut_fuel tutorial_chains tutorial_input : nft_chains.

(** The tutorial chain reads no shared state (no ct/set/map/fib), so its
    verdict is the same under EVERY env; the theorems below quantify over an
    arbitrary [e], and the concrete examples use the empty [tut_env]. *)
Definition tut_env : env :=
  {| e_set := fun _ => []; e_vmap := fun _ => []; e_map := fun _ => [];
     e_routes := []; e_rt := fun _ => []; e_ifaddrs := fun _ => [];
     e_ifaddrs6 := fun _ => []; e_limit := fun _ => 0; e_quota := fun _ => 0;
     e_connlimit := fun _ => []; e_ct := fun _ _ => [];
     e_nat := fun _ => None; e_numgen := fun _ => 0 |}.

(* ================================================================== *)
(** ** The headline: the chain drops a packet IFF its source is in the range.

    Hypotheses: the packet's IPv4 source address field holds bytes [a.b.c.d]
    (routed through the typed [ip4] constructor), and the 4-byte read is in
    bounds (the packet actually carries an IPv4 header).  NOTE the env [e] is
    fully universal: the verdict is independent of conntrack/set state. *)
Theorem tutorial_blocks_exactly : forall (e : env) (p : packet) (a b c d : nat),
  fieldof FIp4Saddr e p === ip4 a b c d ->
  read_payload_ok PNetwork 12 4 p = true ->
  ( tutorial_input denies p in e under tutorial_chains budget tut_fuel
    <-> a = 192 /\ b = 168 /\ c = 100 ).
Proof.
  intros e p a b c d Hs Hok.
  (* the rule's 3-byte prefix read is in bounds because the 4-byte one is *)
  assert (Hok3 : read_payload_ok PNetwork 12 3 p = true)
    by (apply read_payload_ok_shorter with (w := 4); [lia | exact Hok]).
  (* chain-level iff: drops <-> the 3-byte prefix equation *)
  eapply iff_trans.
  { apply (nft_prefix_chain_drop_iff 15 tutorial_chains _ _ _ _ _ _ Hok3). }
  (* the prefix field is the first 3 bytes of the saddr, which Hs names *)
  rewrite (nft_saddr_prefix 3) by lia.
  (* [vm_compute], not [cbn]: the goal mixes a closed prefix (elaborated from
     [MPrefix], reducible to [192;168;100]) with [encode (ip4 a b c d)] over
     VARIABLE bytes; cbn diverges on that mix, vm_compute is instant. *)
  unfold nft_field_is in Hs. rewrite Hs. vm_compute.
  (* [a; b; c] = [192; 168; 100]  <->  a = 192 /\ b = 168 /\ c = 100 *)
  apply bytes3_eq_iff.
Qed.
Print Assumptions tutorial_blocks_exactly.

(** The complement, from the same layer: everything OUTSIDE the range is
    accepted (the chain's policy).  Together with [tutorial_blocks_exactly]
    this pins the chain's entire behaviour. *)
Theorem tutorial_accepts_rest : forall (e : env) (p : packet) (a b c d : nat),
  fieldof FIp4Saddr e p === ip4 a b c d ->
  read_payload_ok PNetwork 12 4 p = true ->
  ( tutorial_input accepts p in e under tutorial_chains budget tut_fuel
    <-> ~ (a = 192 /\ b = 168 /\ c = 100) ).
Proof.
  intros e p a b c d Hs Hok.
  assert (Hok3 : read_payload_ok PNetwork 12 3 p = true)
    by (apply read_payload_ok_shorter with (w := 4); [lia | exact Hok]).
  eapply iff_trans.
  { apply (nft_prefix_chain_accept_iff 15 tutorial_chains _ _ _ _ _ _ Hok3). }
  rewrite (nft_saddr_prefix 3) by lia.
  (* vm_compute for the same reason as in [tutorial_blocks_exactly] above *)
  unfold nft_field_is in Hs. rewrite Hs. vm_compute.
  split; intros Hn Hc; apply Hn; [now apply bytes3_eq_iff | now apply bytes3_eq_iff].
Qed.
Print Assumptions tutorial_accepts_rest.

(* ================================================================== *)
(** ** The budget is inert: the same exactness at EVERY adequate fuel.

    [tut_fuel = 16] was an eyeballed budget.  The M4 fuel-adequacy layer
    removes the eyeball: the tutorial chain never realises a jump ([chains_plain]
    computes [true] under every env, since its one rule's terminal is the
    static [Drop]), so [Semantics.chain_ranked_u] holds by [vm_compute],
    [sufficient_fuel] computes to 4, and the headline holds VERBATIM at every
    fuel >= 4 — [tutorial_blocks_exactly] is the [fuel = tut_fuel] instance.
    See Semantics.v § "Fuel discipline for the unified evaluator" for why the bound
    is needed at all (the policy fallback on exhaustion). *)

Lemma tutorial_ranked : forall e h, chain_ranked_u h (fun _ => O) tutorial_chains e.
Proof. intros e h. apply chains_plain_ranked_u. vm_compute. reflexivity. Qed.

Example tutorial_sufficient_fuel :
  sufficient_fuel tutorial_chains (c_rules tutorial_input) = 4.
Proof. reflexivity. Qed.

Theorem tutorial_blocks_exactly_any_fuel :
  forall (e : env) (p : packet) (a b c d : nat) (fuel : nat),
  sufficient_fuel tutorial_chains (c_rules tutorial_input) <= fuel ->
  fieldof FIp4Saddr e p === ip4 a b c d ->
  read_payload_ok PNetwork 12 4 p = true ->
  ( tutorial_input denies p in e under tutorial_chains budget fuel
    <-> a = 192 /\ b = 168 /\ c = 100 ).
Proof.
  intros e p a b c d fuel Hf Hs Hok.
  eapply iff_trans.
  { apply (nft_drops_fuel_indep (fun _ => O) tutorial_chains tutorial_input e p
             fuel tut_fuel (tutorial_ranked e) Hf).
    rewrite tutorial_sufficient_fuel. unfold tut_fuel. lia. }
  exact (tutorial_blocks_exactly e p a b c d Hs Hok).
Qed.
Print Assumptions tutorial_blocks_exactly_any_fuel.

(* ================================================================== *)
(** ** Satisfiability / anti-vacuity: concrete packets on both sides.

    The symbolic theorems above would be vacuously true if no packet satisfied
    their hypotheses.  [mk_tut] builds a real IPv4 packet with source [a.b.c.d];
    the [Example]s below run the actual evaluator on it ([nft_decide] =
    [vm_compute]), on an address inside the range and one outside. *)
Definition mk_tut (a b c d : nat) : packet :=
  {|
     pkt_meta := fun _ => []; pkt_sock := fun _ => [];
     pkt_eh := fun _ _ _ _ _ => []; pkt_lh := [];
     (* a 20-byte IPv4 header: version/ihl .. proto, then saddr, then daddr *)
     pkt_nh := ([69; 0; 0; 40; 0; 0; 0; 0; 64; 6; 0; 0]
                  ++ [a; b; c; d] ++ [10; 0; 0; 1])%list;
     pkt_th := []; pkt_ih := []; pkt_tnl := [];
     pkt_fibkey := fun _ => []; pkt_numgen := fun _ => []; pkt_osf := [];
     pkt_tunnel := fun _ => []; pkt_symhash := fun _ _ => [];
     pkt_xfrm := fun _ _ _ => []; pkt_ctdir := fun _ _ => [];
     pkt_inner := fun _ _ _ _ => [];
     pkt_have_l2 := true; pkt_have_l4 := true; pkt_fragoff := 0;
     pkt_flow := []; pkt_untracked := false;
     pkt_ctdir_orig := true; pkt_ct_present := true |}.

(** [mk_tut] really satisfies the theorems' hypotheses (for ANY bytes). *)
Example mk_tut_saddr : forall a b c d,
  fieldof FIp4Saddr tut_env (mk_tut a b c d) === ip4 a b c d.
Proof. intros. reflexivity. Qed.

Example mk_tut_ok : forall a b c d,
  read_payload_ok PNetwork 12 4 (mk_tut a b c d) = true.
Proof. intros. reflexivity. Qed.

(** In-range source: dropped.  Out-of-range sources (next /24 over, and a
    far-away address): accepted. *)
Example tut_blocked_192_168_100_7 :
  tutorial_input denies (mk_tut 192 168 100 7) in tut_env
    under tutorial_chains budget tut_fuel.
Proof. nft_decide. Qed.

Example tut_passes_192_168_101_7 :
  tutorial_input accepts (mk_tut 192 168 101 7) in tut_env
    under tutorial_chains budget tut_fuel.
Proof. nft_decide. Qed.

Example tut_passes_8_8_8_8 :
  tutorial_input accepts (mk_tut 8 8 8 8) in tut_env
    under tutorial_chains budget tut_fuel.
Proof. nft_decide. Qed.

(** And the false claim is refutable — the boundary really is the /24: the
    tactic layer cannot "prove" that an out-of-range packet is dropped. *)
Example tut_next_slash24_not_blocked :
  ~ (tutorial_input denies (mk_tut 192 168 101 7) in tut_env
       under tutorial_chains budget tut_fuel).
Proof. intro H. nft_unfold. specialize (H Hinput). vm_compute in H. discriminate. Qed.

(** NOT an unfinished proof: this [Goal] deliberately states the FALSE claim
    refuted above, and [Fail now nft_decide] succeeds precisely because the
    tactic CANNOT close it — the build breaks if [nft_decide] ever "proves" a
    false property.  [Abort] discards the goal, so nothing unproven enters the
    environment (checked: every named result in this file [Print Assumptions]es
    to "Closed under the global context").  Same pattern as
    [Nft_Demo_Concrete.demo_nft_decide_cannot_prove_false]. *)
Goal tutorial_input denies (mk_tut 192 168 101 7) in tut_env
       under tutorial_chains budget tut_fuel.
Proof. Fail now nft_decide. Abort.

(* ================================================================== *)
(** ** The tutorial config is write-free, so every verdict above — stated over
    the canonical unified evaluator [eval_table_u] at every hook — is
    hook-independent ([Nft_Tactics.eval_table_u_hookindep_writefree]);
    [nft_writefree] is the check. *)
Example tutorial_license :
  nft_writefree tutorial_chains tutorial_input = true.
Proof. vm_compute. reflexivity. Qed.
