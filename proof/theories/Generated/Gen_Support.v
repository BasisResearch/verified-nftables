(** * Generated.Gen_Support: the Semantics-level projections the Gen files use.

    [theories/Surface/Lower.v] defines [lower_ruleset] and the [Syntax]-only
    carve-outs ([lr_chains_of], [lr_chain_of], [lr_hookinfo_of]).  Those live
    below [Semantics] in the build order, so the projections that build
    [set_decls] and [hooked_chain] records — which are [Semantics] types — cannot
    live there.  This tiny module (compiled AFTER Semantics, BEFORE the four
    Generated/*_Gen.v) holds them, so each Gen file's

        Definition decls       := Eval vm_compute in lr_set_decls  _lowered.
        Definition filter_hooks := Eval vm_compute in lr_hooks_of  _lowered "filter".

    reduce the verified lowering's output into the exact identifiers the
    downstream proofs already reference — no hand-written bytes in the Gen file.

    This module is NOT extracted (it is used only inside the Coq Gen files). *)

From Stdlib Require Import List String ZArith.
From Nft Require Import Bytes Verdict Packet Bytecode Syntax Semantics.
From Nft Require Import Surface.Lower.
Import ListNotations.
Local Open Scope string_scope.

(** Map a validated netfilter hook NAME to its [hook_id] constructor.  Every
    string reaching here has already passed [Lower.is_known_hook] (the lowering
    fails loud on any other), so the final catch-all is unreachable for a
    successfully-lowered ruleset; it is present only to keep the function total. *)
Definition hook_id_of_string (h : string) : hook_id :=
  if String.eqb h "prerouting"  then Hprerouting
  else if String.eqb h "input"       then Hinput
  else if String.eqb h "forward"     then Hforward
  else if String.eqb h "output"      then Houtput
  else if String.eqb h "postrouting" then Hpostrouting
  else Hingress.

(** The set / map / vmap declarations, straight from the lowering's interning
    output (the same lists [gen_env] reads by name). *)
Definition lr_set_decls (lr : lowered_ruleset) : set_decls :=
  {| sd_sets  := lr_sets  lr;
     sd_vmaps := lr_vmaps lr;
     sd_maps  := lr_maps  lr |}.

(** The base-chain hook registrations of one table, as [hooked_chain] records:
    the hook id and (sign-magnitude → signed) priority come from the lowering's
    [lr_hooks]; [hc_env] is the table's whole chain environment and [hc_base] the
    named base chain, both projected from the same lowering. *)
Definition lr_hooks_of (lr : lowered_ruleset) (tbl : string)
  : list hooked_chain :=
  map (fun hk : string * string * string * bool * nat =>
         let '(cn, ct, h, pn, pr) := hk in
         {| hc_hook := hook_id_of_string h;
            hc_prio := if pn then Z.opp (Z.of_nat pr) else Z.of_nat pr;
            hc_env  := lr_chains_of lr tbl;
            hc_base := lr_chain_of lr tbl cn |})
      (lr_hookinfo_of lr tbl).
