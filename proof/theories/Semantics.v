(** * Semantics: the meaning of both languages as packet -> verdict.

    Both the declarative DSL and the bytecode are given the *same* observable
    semantics — a function from a packet to the verdict the base chain produces —
    so "semantics preserving" is a literal equality of these functions. *)

From Stdlib Require Import List NArith Bool.
From Nft Require Import Bytes Packet Verdict Syntax Bytecode.
Import ListNotations.

(** ** Declarative semantics. *)

Definition apply_transform (t : transform) (d : data) : data :=
  match t with
  | TBitAnd mask xor    => data_bitops d mask xor
  | TShift shl amt     => data_shift shl amt d
  | TByteorder h sz len => data_byteorder h sz len d
  | TJhash l s m o      => data_jhash l s m o d
  end.

Definition apply_transforms (ts : list transform) (d : data) : data :=
  fold_left (fun acc t => apply_transform t acc) ts d.

Definition eval_matchcond (m : matchcond) (p : packet) : bool :=
  match m with
  | MEq  f v => data_eqb (field_value f p) v
  | MNeq f v => negb (data_eqb (field_value f p) v)
  | MRange f neg lo hi =>
      eval_range (if neg then CNe else CEq) (field_value f p) lo hi
  | MMasked f neg mask xor v =>
      eval_cmp (if neg then CNe else CEq) (data_bitops (field_value f p) mask xor) v
  | MCmp f op v => eval_cmp op (field_value f p) v
  | MConcatSet fields neg _ elems =>
      (* The lookup key is the concatenation of the field values.  NOTE: the
         kernel pads each concatenated field up to its 4-byte register slot, so
         for sub-4-byte fields the real set key has inter-field padding this
         model omits.  This affects only the runtime membership result when
         [elems] is populated; the control-plane round-trip never populates
         [elems] (the set contents live in a separate NEWSET object), so the
         compiler theorem is unaffected.  Faithful for 4-byte-aligned fields. *)
      xorb neg (data_mem (concat (map (fun f => field_value f p) fields)) elems)
  | MTransform f ts op v =>
      eval_cmp op (apply_transforms ts (field_value f p)) v
  | MSetT f ts neg _ elems =>
      xorb neg (data_mem (apply_transforms ts (field_value f p)) elems)
  | MRangeT f ts neg lo hi =>
      eval_range (if neg then CNe else CEq) (apply_transforms ts (field_value f p)) lo hi
  | MLimit spec => pkt_limit p spec
  | MQuota spec => pkt_quota p spec
  end.

(** A rule applies when all its match conditions hold (empty = matches all). *)
Definition rule_applies (r : rule) (p : packet) : bool :=
  forallb (fun m => eval_matchcond m p) (r_matches r).

(** Look up a key in a verdict map's entries. *)
Fixpoint assoc_verdict (key : data) (entries : list (data * verdict)) : option verdict :=
  match entries with
  | [] => None
  | (k, v) :: rest => if data_eqb key k then Some v else assoc_verdict key rest
  end.

(** A rule's outcome (when it applies): a [Some v] (verdict reached) or [None]
    (fall through), for a static verdict or a verdict-map lookup. *)
Definition outcome (r : rule) (p : packet) : option verdict :=
  match r_nat r with
  | Some _ => Some Accept   (* NAT is terminal accept (translation is a side effect) *)
  | None =>
  match r_tproxy r with
  | Some _ => Some Accept   (* tproxy is terminal accept (redirect is a side effect) *)
  | None =>
    match r_vmap r with
    | Some vm => assoc_verdict (concat (map (fun f => field_value f p) (vm_fields vm)))
                               (vm_entries vm)
    | None    => match r_verdict r with Continue => None | v => Some v end
    end
  end
  end.

(** Evaluate a rule list.  [None] means "fell through every rule"; [Some v]
    means a terminal verdict [v] was reached.  A [Continue] verdict on an
    applicable rule simply proceeds, exactly like a non-applicable rule. *)
Fixpoint eval_rules (rs : list rule) (p : packet) : option verdict :=
  match rs with
  | [] => None
  | r :: rest =>
      if rule_applies r p then
        match outcome r p with
        | Some v => if terminal v then Some v else eval_rules rest p
        | None   => eval_rules rest p
        end
      else eval_rules rest p
  end.

Definition eval_chain (c : chain) (p : packet) : verdict :=
  match eval_rules (c_rules c) p with
  | Some v => v
  | None   => c_policy c
  end.

(** ** Bytecode VM semantics. *)

(** Run one rule's program over a register file.  [None] means a [cmp] failed
    (the rule does not apply, like netfilter "breaking" out of the rule);
    [Some v] means an [immediate] set verdict [v]. *)
Fixpoint run_rule (rf : regfile) (is : rule_prog) (p : packet) : option verdict :=
  match is with
  | [] => None
  | IMetaLoad k dst :: rest =>
      run_rule (set_reg rf dst (pkt_meta p k)) rest p
  | ICtLoad k dst :: rest =>
      run_rule (set_reg rf dst (pkt_ct p k)) rest p
  | IRtLoad k dst :: rest =>
      run_rule (set_reg rf dst (pkt_rt p k)) rest p
  | ISocketLoad k dst :: rest =>
      run_rule (set_reg rf dst (pkt_sock p k)) rest p
  | INumgen spec dst :: rest =>
      run_rule (set_reg rf dst (pkt_numgen p spec)) rest p
  | IOsf dst :: rest =>
      run_rule (set_reg rf dst (pkt_osf p)) rest p
  | IExthdrLoad ep h o l pr dst :: rest =>
      run_rule (set_reg rf dst (pkt_eh p ep h o l pr)) rest p
  | IFibLoad sel res dst :: rest =>
      run_rule (set_reg rf dst (pkt_fib p sel res)) rest p
  | ICtDirLoad key dir dst :: rest =>
      run_rule (set_reg rf dst (pkt_ctdir p key dir)) rest p
  | IXfrmLoad dir sp key dst :: rest =>
      run_rule (set_reg rf dst (pkt_xfrm p dir sp key)) rest p
  | IInnerLoad t h fl desc _ dst :: rest =>
      run_rule (set_reg rf dst (pkt_inner p t h fl desc)) rest p
  | IPayloadLoad b o l dst :: rest =>
      run_rule (set_reg rf dst (read_payload b o l p)) rest p
  | ICmp op src v :: rest =>
      if eval_cmp op (rf src) v then run_rule rf rest p else None
  | IRange op src lo hi :: rest =>
      if eval_range op (rf src) lo hi then run_rule rf rest p else None
  | IBitwise dst src mask xor :: rest =>
      run_rule (set_reg rf dst (data_bitops (rf src) mask xor)) rest p
  | IBitShift dst src shl amt :: rest =>
      run_rule (set_reg rf dst (data_shift shl amt (rf src))) rest p
  | IByteorder dst src h sz len :: rest =>
      run_rule (set_reg rf dst (data_byteorder h sz len (rf src))) rest p
  | IJhash dst src l s m o :: rest =>
      run_rule (set_reg rf dst (data_jhash l s m o (rf src))) rest p
  | ILookup srcs _ neg elems :: rest =>
      if xorb neg (data_mem (concat (map rf srcs)) elems) then run_rule rf rest p else None
  | IVmap srcs _ entries :: _ =>
      assoc_verdict (concat (map rf srcs)) entries   (* verdict from the map, or None *)
  | IImmediateData dst v :: rest =>
      run_rule (set_reg rf dst v) rest p
  (* Set/mangle: verdict-neutral.  The written value (the operand register) is a
     packet/meta/ct side effect outside the single-packet verdict model, so it is
     dropped here.  The proof therefore certifies these statements preserve the
     verdict; that the emitted bytecode writes the *right* value is covered by the
     differential corpus, not by Rocq. *)
  | IPayloadWrite _ _ _ _ _ _ _ :: rest => run_rule rf rest p
  | IMetaSet _ _ :: rest => run_rule rf rest p
  | ICtSet _ _ :: rest => run_rule rf rest p
  | ILookupVal keys _ dreg entries :: rest =>
      run_rule (set_reg rf dreg (map_lookup_data (concat (map rf keys)) entries)) rest p
  | INat _ _ _ _ _ _ _ :: _ => Some Accept   (* terminal *)
  | ITproxy _ _ _ :: _ => Some Accept        (* terminal redirect *)
  | ILimit spec :: rest =>
      if pkt_limit p spec then run_rule rf rest p else None   (* over-limit breaks *)
  | IQuota spec :: rest =>
      if pkt_quota p spec then run_rule rf rest p else None   (* over-quota breaks *)
  | ICounter _ _ :: rest => run_rule rf rest p   (* verdict-neutral *)
  | INotrack :: rest      => run_rule rf rest p
  | ILog _ :: rest        => run_rule rf rest p
  | IObjref _ _ :: rest   => run_rule rf rest p   (* verdict-neutral *)
  | ISynproxy _ _ :: rest => run_rule rf rest p
  | ILast _ :: rest       => run_rule rf rest p
  | IDynset _ _ _ :: rest => run_rule rf rest p   (* verdict-neutral *)
  | IExthdrReset _ _ :: rest => run_rule rf rest p (* verdict-neutral *)
  | IReject t c :: _ => Some (Reject t c)
  | IQueue lo hi b f :: _ => Some (Queue lo hi b f)
  | IImmediate v :: _ => Some v
  end.

(** Run a base chain's program: ordered per-rule programs, each from a fresh
    (empty) register file, stopping at the first terminal verdict. *)
Fixpoint run_program (prog : program) (p : packet) : option verdict :=
  match prog with
  | [] => None
  | rp :: rest =>
      match run_rule empty_rf rp p with
      | Some v => if terminal v then Some v else run_program rest p
      | None   => run_program rest p
      end
  end.

Definition run_chain (prog : program) (policy : verdict) (p : packet) : verdict :=
  match run_program prog p with
  | Some v => v
  | None   => policy
  end.
