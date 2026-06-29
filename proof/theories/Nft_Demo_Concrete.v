(** * Nft_Demo_Concrete: re-express CONCRETE per-config theorems with Nft_Tactics,
      and witness that the tactics CANNOT prove a false property.

    [Router_Private.v] proves verdicts for fully concrete LAN packets ([pkt_lan_dns]
    etc.) against the parser-emitted router chains by [vm_compute].  Here we
    re-state two of them through the [Nft_Tactics] layer (readable conclusion,
    single [nft_decide]) and — crucially for the soundness review — show the same
    tactic FAILS to prove the FALSE claim that the unlisted SMTP packet is
    accepted, and that the claim is in fact refutable.

    SOUNDNESS: [demo_*_def] pin the readable forms to the raw [eval_table]
    statements ([reflexivity]); [demo_smtp_not_accepted] refutes the false
    property; [demo_nft_decide_cannot_prove_false] shows [nft_decide] leaves the
    false goal OPEN (so it cannot be used to "prove" it).  All axiom-free. *)

From Stdlib Require Import List String NArith.
From Nft Require Import Bytes Verdict Packet Syntax Semantics Nftval Eval_Fw
                       Router_Gen Router_Input Router_Private Nft_Tactics.
Import ListNotations.
Open Scope string_scope.

(* ------------------------------------------------------------------ *)
(** ** The readable layer is DEFINITIONALLY the raw statement. *)

Example demo_c_accepts_def :
  (global_inbound accepts pkt_lan_dns under global_chains budget in_fuel)
  = (eval_table in_fuel global_chains global_inbound pkt_lan_dns = Accept).
Proof. reflexivity. Qed.

Example demo_c_denies_def :
  (global_inbound denies pkt_lan_smtp under global_chains budget in_fuel)
  = (eval_table in_fuel global_chains global_inbound pkt_lan_smtp = Drop).
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(** ** Re-expressed concrete theorems (mirror [Router_Private]). *)

(** dns over udp (a listed service) is accepted. *)
Theorem demo_dns_accepted :
  global_inbound accepts pkt_lan_dns under global_chains budget in_fuel.
Proof. nft_decide. Qed.
Print Assumptions demo_dns_accepted.

(** smtp (unlisted, not icmp) is dropped — the LAN-exposure security crux. *)
Theorem demo_smtp_denied :
  global_inbound denies pkt_lan_smtp under global_chains budget in_fuel.
Proof. nft_decide. Qed.
Print Assumptions demo_smtp_denied.

(* ------------------------------------------------------------------ *)
(** ** The tactics do NOT prove false properties.

    The false claim "smtp is accepted" is REFUTABLE, and [nft_decide] cannot
    close it. *)

Theorem demo_smtp_not_accepted :
  ~ (global_inbound accepts pkt_lan_smtp under global_chains budget in_fuel).
Proof. intro H. nft_unfold. vm_compute in H. discriminate. Qed.

(** [nft_decide] does NOT close the false goal: the wrapped attempt fails
    (leaving the goal open is a *non*-completion, so [now nft_decide] errors and
    [Fail] succeeds).  This is the anti-vacuity witness the review demands. *)
Goal global_inbound accepts pkt_lan_smtp under global_chains budget in_fuel.
Proof. Fail now nft_decide. Abort.
