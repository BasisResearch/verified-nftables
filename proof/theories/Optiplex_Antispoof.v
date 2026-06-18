(** * Anti-spoofing: a proven security property of optiplex.nft's bridge filter.

    [../../optiplex.nft] is a real, in-use IPv4/IPv6 firewall.  Its `bridge
    vmfilter` table binds each container's IP to the bridge port it lives behind,
    via two declared sets and, in the bridge `output` chain (policy accept):

      meta obrname br.20 ip daddr @vmaddrs ip daddr . oifname != @vmantispoof drop

    Operationally: for a frame leaving bridge port br.20 whose destination is a
    known VM address (`ip daddr @vmaddrs`) but whose (destination, output-iface)
    pair is NOT the bound pair (`ip daddr . oifname != @vmantispoof`), DROP.  This
    stops one container impersonating another's IP: traffic to a VM's address may
    only ever exit that VM's own veth.

    Crucially, we do NOT hand-translate the ruleset here.  [Optiplex_Gen.v] is the
    Menhir frontend's OUTPUT: the parser (extracted/nft_*.ml) reads
    ../../optiplex.nft and emits the chains ([vmfilter_output], ...) and the
    set/map declarations ([decls]/[gen_env]) as the Coq terms below.  So the chain
    these theorems are about IS the parser's output — there is no eyeballed step
    between the `.nft` text and the theorem.  Via [compile_table_correct] every
    property transports to the installed netlink bytecode. *)

From Stdlib Require Import List String Ascii NArith.
From Nft Require Import Bytes Verdict Packet Syntax Semantics Optiplex_Gen.
Import ListNotations.
Open Scope string_scope.

(** ** Wire-value notation, only to *state* the hypotheses about a packet.
    These do not define the ruleset (that comes from [Optiplex_Gen]); they only
    name the bytes a given packet's fields hold. *)
Definition ip4 (a b c d : nat) : data := [a; b; c; d].
Fixpoint sbytes (s : string) : data :=
  match s with EmptyString => [] | String c r => nat_of_ascii c :: sbytes r end.

(* the field a `meta obrname` match reads (output bridge-port name) *)
Definition Fobrname : field := FMetaGen MKbri_oifname.

(* the output chain takes no jumps; fuel need only cover its two rules *)
Definition vm_fuel : nat := 4.

(** ** Stepping lemmas for the fuel-bounded interpreter. *)
Lemma erj_drop_first : forall f cs r rest p,
  rule_loadable r p = true -> rule_applies r p = true -> outcome r p = Some Drop ->
  eval_rules_j (S f) cs (r :: rest) p = Some Drop.
Proof. intros f cs r rest p Hld Hap Hout. cbn. rewrite Hld, Hap, Hout. reflexivity. Qed.

Lemma erj_skip : forall f cs r rest p,
  rule_applies r p = false ->
  eval_rules_j (S f) cs (r :: rest) p = eval_rules_j f cs rest p.
Proof. intros f cs r rest p Hap. cbn. rewrite Hap, Bool.andb_false_r. reflexivity. Qed.

(** ** The general anti-spoofing theorem (about the PARSED chain [vmfilter_output]).

    For ANY frame leaving bridge port br.20 whose destination is a protected VM
    address but whose (destination, output-interface) pair is not the bound pair,
    the parsed ruleset's verdict is [Drop] — stated directly in terms of the two
    set memberships, so it holds for every such address/interface. *)
Theorem antispoof_general : forall p,
  pkt_env p = gen_env ->
  field_value Fobrname p = sbytes "br.20" ->
  read_payload_ok PNetwork 16 4 p = true ->     (* the ip daddr load succeeds *)
  set_mem (field_value FIp4Daddr p) (e_set gen_env "vmaddrs") = true ->
  set_mem (field_value FIp4Daddr p ++ field_value FMetaOifname p)%list
          (e_set gen_env "vmantispoof") = false ->
  eval_table vm_fuel vmfilter_chains vmfilter_output p = Drop.
Proof.
  intros p Henv Hobr Hok Hin Hpair. unfold Fobrname in Hobr.
  unfold eval_table, vm_fuel, vmfilter_output. cbn [c_rules c_policy].
  erewrite erj_drop_first; [ reflexivity | | | reflexivity ].
  (* rule_loadable (the antispoof rule) p = true: only the ip daddr payload load
     can break, discharged by [Hok]. *)
  - unfold rule_loadable, end_loadable, tail_loadable, terminal_loadable, vmap_loadable,
      body_item_loadable, match_loadable, fields_loadable, field_loadable, load_ok.
    cbn -[read_payload_ok]. rewrite Hok. reflexivity.
  (* rule_applies (the antispoof rule) p = true.  [cbn -[field_value pkt_env]]
     reduces forallb/body_matches/eval_matchcond but keeps [field_value]/[pkt_env]
     wrapped, so the field-value and env hypotheses can rewrite them. *)
  - unfold rule_applies, rule_applies_walk, eval_matchcond, match_loadable, eval_matchcond_body,
      fields_loadable, field_loadable, load_ok.
    cbn -[field_value pkt_env read_payload_ok].
    rewrite ?Hok, Hobr, ?app_nil_r, Henv, Hin, Hpair. vm_compute. reflexivity.
Qed.

(** ** Concrete witness 1 — the spoofing attempt is blocked.

    The container behind `inc-vikun` (vikunja, real address .14) sends a frame to
    budget's address 192.168.51.20.  The pair (192.168.51.20 . inc-vikun) is NOT
    in vmantispoof, so the frame is dropped: vikunja cannot impersonate budget. *)
Theorem vikunja_cannot_spoof_budget : forall p,
  pkt_env p = gen_env ->
  field_value Fobrname p = sbytes "br.20" ->
  read_payload_ok PNetwork 16 4 p = true ->            (* a well-formed IPv4 header *)
  field_value FIp4Daddr p = ip4 192 168 51 20 ->      (* budget's address *)
  field_value FMetaOifname p = sbytes "inc-vikun" ->   (* vikunja's interface *)
  eval_table vm_fuel vmfilter_chains vmfilter_output p = Drop.
Proof.
  intros p Henv Hobr Hok Hdaddr Hoif. apply antispoof_general; auto.
  - rewrite Hdaddr. vm_compute. reflexivity.
  - rewrite Hdaddr, Hoif. vm_compute. reflexivity.
Qed.

(** A second spoof: gentoo (behind vb-gentoo) trying to take hass's .10. *)
Theorem gentoo_cannot_spoof_hass : forall p,
  pkt_env p = gen_env ->
  field_value Fobrname p = sbytes "br.20" ->
  read_payload_ok PNetwork 16 4 p = true ->
  field_value FIp4Daddr p = ip4 192 168 51 10 ->       (* hass's address *)
  field_value FMetaOifname p = sbytes "vb-gentoo" ->    (* gentoo's interface *)
  eval_table vm_fuel vmfilter_chains vmfilter_output p = Drop.
Proof.
  intros p Henv Hobr Hok Hdaddr Hoif. apply antispoof_general; auto.
  - rewrite Hdaddr. vm_compute. reflexivity.
  - rewrite Hdaddr, Hoif. vm_compute. reflexivity.
Qed.

(** ** Concrete witness 2 — legitimate traffic is allowed.

    Budget's own frame (to .20, leaving its bound interface inc-budge) is NOT
    dropped: the (.20 . inc-budge) pair IS in vmantispoof, so the negated match
    fails, the rule does not fire, and the frame falls through to `policy accept`.
    The rule blocks *only* spoofing, not the legitimate binding. *)
Theorem budget_legitimate_allowed : forall p,
  pkt_env p = gen_env ->
  field_value Fobrname p = sbytes "br.20" ->
  read_payload_ok PNetwork 16 4 p = true ->
  field_value FIp4Daddr p = ip4 192 168 51 20 ->
  field_value FMetaOifname p = sbytes "inc-budge" ->    (* its OWN interface *)
  eval_table vm_fuel vmfilter_chains vmfilter_output p = Accept.
Proof.
  intros p Henv Hobr Hok Hdaddr Hoif. unfold Fobrname in Hobr.
  unfold eval_table, vm_fuel, vmfilter_output. cbn [c_rules c_policy].
  (* antispoof rule does not apply: the pair IS bound, so the `!=` match is false *)
  erewrite erj_skip.
  2:{ unfold rule_applies, rule_applies_walk, eval_matchcond, match_loadable, eval_matchcond_body,
        fields_loadable, field_loadable, load_ok.
      cbn -[field_value pkt_env read_payload_ok].
      rewrite ?Hok, Hobr, ?app_nil_r, Henv, Hdaddr, Hoif. vm_compute. reflexivity. }
  (* hass rule does not apply either: obrname is br.20, not br.1 *)
  erewrite erj_skip.
  2:{ unfold rule_applies, rule_applies_walk, eval_matchcond, match_loadable, eval_matchcond_body,
        fields_loadable, field_loadable, load_ok.
      cbn -[field_value pkt_env read_payload_ok]. rewrite ?Hok, Hobr.
      vm_compute. reflexivity. }
  reflexivity.
Qed.

(** Every theorem above is about [eval_table], the specification; via
    [compile_table_correct] (Correct.v) the same verdict holds of the compiled
    netlink bytecode, exactly as Example_Ruleset.v shows for smtp_dropped. *)
