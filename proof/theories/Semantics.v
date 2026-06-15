(** * Semantics: the meaning of both languages as packet -> verdict.

    Both the declarative DSL and the bytecode are given the *same* observable
    semantics — a function from a packet to the verdict the base chain produces —
    so "semantics preserving" is a literal equality of these functions. *)

From Stdlib Require Import List NArith Bool.
From Nft Require Import Bytes Packet Verdict Syntax Bytecode.
Import ListNotations.
(* [String] is left UNimported (it shadows List's [concat]/[length]); the chain
   environment uses the qualified [String.string] / [String.eqb]. *)

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
  | MConcatSet fields neg name =>
      (* membership of the concatenated key in the *named* set, whose contents are
         read from the runtime environment [pkt_env p], not inlined in the rule.
         NOTE: the kernel pads each concatenated field to its 4-byte register
         slot; this model omits that inter-field padding (faithful for
         4-byte-aligned fields). *)
      xorb neg (data_mem (List.concat (map (fun f => field_value f p) fields))
                         (e_set (pkt_env p) name))
  | MTransform f ts op v =>
      eval_cmp op (apply_transforms ts (field_value f p)) v
  | MSetT f ts neg name =>
      xorb neg (data_mem (apply_transforms ts (field_value f p))
                         (e_set (pkt_env p) name))
  | MRangeT f ts neg lo hi =>
      eval_range (if neg then CNe else CEq) (apply_transforms ts (field_value f p)) lo hi
  | MLimit spec => pkt_limit p spec
  | MQuota spec => pkt_quota p spec
  | MConnlimit spec => pkt_connlimit p spec
  | MConcatSetT elems neg name =>
      (* like [MConcatSet] but each element is transformed before concatenation;
         contents read from the named set in [pkt_env p] *)
      xorb neg (data_mem
        (List.concat (map (fun fe => apply_transforms (snd fe) (field_value (fst fe) p)) elems))
        (e_set (pkt_env p) name))
  end.

(** A rule applies when all its match conditions hold (empty = matches all).
    Statements in the body are verdict-neutral and ignored here. *)
Definition rule_applies (r : rule) (p : packet) : bool :=
  forallb (fun m => eval_matchcond m p) (body_matches (r_body r)).

(** The *value* a value-source computes into register 1 — the operand of a
    set/mangle/NAT statement.  This is the value-level meaning the verdict proof
    previously delegated to the corpus; [run_vsrc_value] (in Correct) proves the
    compiled operand leaves exactly this in reg 1, which is the foundation for
    modelling mutation (Phase B): a `meta mark set vs` writes [eval_vsrc vs p].
    (Defined to mirror the bytecode, incl. its simplifications — faithfulness of
    e.g. jhash-over-concatenation to the kernel is a separate, Phase-D, matter.) *)
Definition eval_vsrc (vs : vsrc) (p : packet) : data :=
  match vs with
  | VImm v      => v
  | VField f ts => apply_transforms ts (field_value f p)
  | VMap fields ts name =>
      let key := match fields with
                 | [] => apply_transforms ts []
                 | f0 :: frest =>
                     List.concat (apply_transforms ts (field_value f0 p)
                                  :: map (fun f => field_value f p) frest)
                 end in
      map_lookup_data key (e_map (pkt_env p) name)
  | VHash fields len seed modulus offset =>
      data_jhash len seed modulus offset
        (match fields with [] => [] | f0 :: _ => field_value f0 p end)
  | VOr srcs final =>
      match srcs with
      | [] => []
      | base :: rest =>
          apply_transforms final
            (fold_left
               (fun acc e => data_or acc (apply_transforms (snd e) (field_value (fst e) p)))
               rest (apply_transforms (snd base) (field_value (fst base) p)))
      end
  | VMapT elems name =>
      map_lookup_data
        (List.concat (map (fun fe => apply_transforms (snd fe) (field_value (fst fe) p)) elems))
        (e_map (pkt_env p) name)
  | VHashMap fields len seed modulus offset name =>
      map_lookup_data
        (data_jhash len seed modulus offset
           (match fields with [] => [] | f0 :: _ => field_value f0 p end))
        (e_map (pkt_env p) name)
  end.

(** Look up a key in a verdict map's entries. *)
Fixpoint assoc_verdict (key : data) (entries : list (data * verdict)) : option verdict :=
  match entries with
  | [] => None
  | (k, v) :: rest => if data_eqb key k then Some v else assoc_verdict key rest
  end.

(** The terminal outcome of a rule once any verdict map has fallen through: a
    [nat]/[tproxy]/[fwd]/[queue] side effect accepts, otherwise the static
    verdict ([Continue] = fall through). *)
Definition terminal_outcome (r : rule) (p : packet) : option verdict :=
  match r_nat r with
  | Some _ => Some Accept   (* NAT is terminal accept (translation is a side effect) *)
  | None =>
  match r_tproxy r with
  | Some _ => Some Accept   (* tproxy is terminal accept (redirect is a side effect) *)
  | None =>
  match r_fwd r with
  | Some _ => Some Accept   (* fwd is terminal accept (forward is a side effect) *)
  | None =>
  match r_queue r with
  | Some _ => Some Accept   (* queue is terminal accept (hand-off is a side effect) *)
  | None => match r_verdict r with Continue => None | v => Some v end
  end
  end
  end
  end.

(** A rule's outcome (when it applies): a [Some v] (verdict reached) or [None]
    (fall through).  A verdict map is evaluated first: a hit gives its verdict, a
    miss falls through to the terminal outcome (so a rule may carry both a vmap
    and a trailing redirect/masquerade). *)
Definition outcome (r : rule) (p : packet) : option verdict :=
  match r_vmap r with
  | Some vm =>
      let key := match vm_keyf vm with
                 | Some (f, ts) => apply_transforms ts (field_value f p)
                 | None => List.concat (map (fun f => field_value f p) (vm_fields vm))
                 end in
      match assoc_verdict key (e_vmap (pkt_env p) (vm_name vm)) with
      | Some v => Some v
      | None   => terminal_outcome r p
      end
  | None => terminal_outcome r p
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
  | ITunnelLoad key dst :: rest =>
      run_rule (set_reg rf dst (pkt_tunnel p key)) rest p
  | ISymhash m o dst :: rest =>
      run_rule (set_reg rf dst (pkt_symhash p m o)) rest p
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
  | IBitwiseOr dst src1 src2 :: rest =>
      run_rule (set_reg rf dst (data_or (rf src1) (rf src2))) rest p
  | IBitShift dst src shl amt :: rest =>
      run_rule (set_reg rf dst (data_shift shl amt (rf src))) rest p
  | IByteorder dst src h sz len :: rest =>
      run_rule (set_reg rf dst (data_byteorder h sz len (rf src))) rest p
  | IJhash dst src l s m o :: rest =>
      run_rule (set_reg rf dst (data_jhash l s m o (rf src))) rest p
  | ILookup srcs name neg :: rest =>
      (* set membership: contents read from the named set in [pkt_env p] *)
      if xorb neg (data_mem (List.concat (map rf srcs)) (e_set (pkt_env p) name))
      then run_rule rf rest p else None
  | IVmap srcs name :: rest =>
      (* a verdict map: a hit terminates with that verdict; a miss falls through
         to the rest (e.g. a trailing redirect/masquerade), exactly as nft does.
         Entries are read by [name] from [pkt_env p]. *)
      match assoc_verdict (List.concat (map rf srcs)) (e_vmap (pkt_env p) name) with
      | Some v => Some v
      | None   => run_rule rf rest p
      end
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
  | ILookupVal keys name dreg :: rest =>
      run_rule (set_reg rf dreg (map_lookup_data (List.concat (map rf keys))
                                                 (e_map (pkt_env p) name))) rest p
  | INat _ _ _ _ _ _ _ :: _ => Some Accept   (* terminal *)
  | ITproxy _ _ _ :: _ => Some Accept        (* terminal redirect *)
  | IFwd _ _ _ :: _ => Some Accept           (* terminal forward *)
  | IQueueSreg _ _ _ :: _ => Some Accept     (* terminal queue *)
  | ILimit spec :: rest =>
      if pkt_limit p spec then run_rule rf rest p else None   (* over-limit breaks *)
  | IQuota spec :: rest =>
      if pkt_quota p spec then run_rule rf rest p else None   (* over-quota breaks *)
  | IConnlimit spec :: rest =>
      if pkt_connlimit p spec then run_rule rf rest p else None   (* over-limit breaks *)
  | ICounter _ _ :: rest => run_rule rf rest p   (* verdict-neutral *)
  | INotrack :: rest      => run_rule rf rest p
  | ILog _ :: rest        => run_rule rf rest p
  | IObjref _ _ :: rest   => run_rule rf rest p   (* verdict-neutral *)
  | ISynproxy _ _ :: rest => run_rule rf rest p
  | ILast _ :: rest       => run_rule rf rest p
  | IDynset _ _ _ _ :: rest => run_rule rf rest p   (* verdict-neutral *)
  | IExthdrReset _ _ :: rest => run_rule rf rest p (* verdict-neutral *)
  | IDup _ _ :: rest      => run_rule rf rest p   (* verdict-neutral *)
  | IObjrefMap _ _ :: rest => run_rule rf rest p  (* verdict-neutral *)
  | ICtSetDir _ _ _ :: rest => run_rule rf rest p (* verdict-neutral *)
  | IExthdrWrite _ _ _ _ _ :: rest => run_rule rf rest p (* verdict-neutral *)
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

(** ** Phase B: in-traversal mutation (meta/ct set visible to later rules).

    A `meta mark set X` does not change *this* rule's verdict, but it mutates the
    packet's metadata that a *later* rule reads.  Modelling this requires threading
    a mutated packet across rules.  We do so additively, leaving the verdict-only
    semantics above intact: [run_rule_writes] is the VM's meta/ct effect over a
    rule's bytecode (mirrors [run_rule] but returns the mutated packet), [dsl_writes]
    is the declarative effect, and [eval_chain_mut]/[run_chain_mut] thread them. *)

Definition meta_eq_dec : forall a b : meta_key, {a = b} + {a <> b}.
Proof. decide equality. Defined.
Definition ct_eq_dec : forall a b : ct_key, {a = b} + {a <> b}.
Proof. decide equality. Defined.
Definition meta_eqb (a b : meta_key) : bool := if meta_eq_dec a b then true else false.
Definition ct_eqb (a b : ct_key) : bool := if ct_eq_dec a b then true else false.

(** Update one metadata / conntrack key, leaving every other field of the packet
    (incl. the named-set environment) unchanged. *)
Definition set_meta (p : packet) (k : meta_key) (v : data) : packet :=
  {| pkt_env := pkt_env p;
     pkt_meta := (fun k' => if meta_eqb k k' then v else pkt_meta p k');
     pkt_ct := pkt_ct p; pkt_rt := pkt_rt p; pkt_sock := pkt_sock p;
     pkt_eh := pkt_eh p; pkt_lh := pkt_lh p; pkt_nh := pkt_nh p; pkt_th := pkt_th p;
     pkt_ih := pkt_ih p; pkt_tnl := pkt_tnl p; pkt_limit := pkt_limit p;
     pkt_quota := pkt_quota p; pkt_connlimit := pkt_connlimit p;
     pkt_numgen := pkt_numgen p; pkt_osf := pkt_osf p; pkt_fib := pkt_fib p;
     pkt_tunnel := pkt_tunnel p; pkt_symhash := pkt_symhash p; pkt_xfrm := pkt_xfrm p;
     pkt_ctdir := pkt_ctdir p; pkt_inner := pkt_inner p |}.
Definition set_ct (p : packet) (k : ct_key) (v : data) : packet :=
  {| pkt_env := pkt_env p; pkt_meta := pkt_meta p;
     pkt_ct := (fun k' => if ct_eqb k k' then v else pkt_ct p k');
     pkt_rt := pkt_rt p; pkt_sock := pkt_sock p;
     pkt_eh := pkt_eh p; pkt_lh := pkt_lh p; pkt_nh := pkt_nh p; pkt_th := pkt_th p;
     pkt_ih := pkt_ih p; pkt_tnl := pkt_tnl p; pkt_limit := pkt_limit p;
     pkt_quota := pkt_quota p; pkt_connlimit := pkt_connlimit p;
     pkt_numgen := pkt_numgen p; pkt_osf := pkt_osf p; pkt_fib := pkt_fib p;
     pkt_tunnel := pkt_tunnel p; pkt_symhash := pkt_symhash p; pkt_xfrm := pkt_xfrm p;
     pkt_ctdir := pkt_ctdir p; pkt_inner := pkt_inner p |}.

(** The VM's meta/ct effect of running one rule's bytecode: mirrors [run_rule]'s
    register threading, but instead of a verdict it returns the packet with the
    [IMetaSet]/[ICtSet] writes applied (in execution order; a write only happens
    once the matches before it have passed — a failed cmp/lookup/limit returns the
    packet unchanged, exactly as the verdict run breaks). *)
Fixpoint run_rule_writes (rf : regfile) (is : list instr) (p : packet) : packet :=
  match is with
  | [] => p
  | IMetaLoad k dst :: rest => run_rule_writes (set_reg rf dst (pkt_meta p k)) rest p
  | ICtLoad k dst :: rest => run_rule_writes (set_reg rf dst (pkt_ct p k)) rest p
  | IRtLoad k dst :: rest => run_rule_writes (set_reg rf dst (pkt_rt p k)) rest p
  | ISocketLoad k dst :: rest => run_rule_writes (set_reg rf dst (pkt_sock p k)) rest p
  | INumgen spec dst :: rest => run_rule_writes (set_reg rf dst (pkt_numgen p spec)) rest p
  | IOsf dst :: rest => run_rule_writes (set_reg rf dst (pkt_osf p)) rest p
  | IExthdrLoad ep h o l pr dst :: rest =>
      run_rule_writes (set_reg rf dst (pkt_eh p ep h o l pr)) rest p
  | IFibLoad sel res dst :: rest => run_rule_writes (set_reg rf dst (pkt_fib p sel res)) rest p
  | ICtDirLoad key dir dst :: rest => run_rule_writes (set_reg rf dst (pkt_ctdir p key dir)) rest p
  | IXfrmLoad dir sp key dst :: rest => run_rule_writes (set_reg rf dst (pkt_xfrm p dir sp key)) rest p
  | ITunnelLoad key dst :: rest => run_rule_writes (set_reg rf dst (pkt_tunnel p key)) rest p
  | ISymhash m o dst :: rest => run_rule_writes (set_reg rf dst (pkt_symhash p m o)) rest p
  | IInnerLoad t h fl desc _ dst :: rest =>
      run_rule_writes (set_reg rf dst (pkt_inner p t h fl desc)) rest p
  | IPayloadLoad b o l dst :: rest => run_rule_writes (set_reg rf dst (read_payload b o l p)) rest p
  | ICmp op src v :: rest => if eval_cmp op (rf src) v then run_rule_writes rf rest p else p
  | IRange op src lo hi :: rest => if eval_range op (rf src) lo hi then run_rule_writes rf rest p else p
  | IBitwise dst src mask xor :: rest => run_rule_writes (set_reg rf dst (data_bitops (rf src) mask xor)) rest p
  | IBitwiseOr dst src1 src2 :: rest => run_rule_writes (set_reg rf dst (data_or (rf src1) (rf src2))) rest p
  | IBitShift dst src shl amt :: rest => run_rule_writes (set_reg rf dst (data_shift shl amt (rf src))) rest p
  | IByteorder dst src h sz len :: rest => run_rule_writes (set_reg rf dst (data_byteorder h sz len (rf src))) rest p
  | IJhash dst src l s m o :: rest => run_rule_writes (set_reg rf dst (data_jhash l s m o (rf src))) rest p
  | ILookup srcs name neg :: rest =>
      if xorb neg (data_mem (List.concat (map rf srcs)) (e_set (pkt_env p) name))
      then run_rule_writes rf rest p else p
  | IVmap srcs name :: rest =>
      match assoc_verdict (List.concat (map rf srcs)) (e_vmap (pkt_env p) name) with
      | Some _ => p   (* terminal verdict: traversal stops, no later-rule effect *)
      | None   => run_rule_writes rf rest p
      end
  | IImmediateData dst v :: rest => run_rule_writes (set_reg rf dst v) rest p
  | IPayloadWrite _ _ _ _ _ _ _ :: rest => run_rule_writes rf rest p
  | IMetaSet k src :: rest => run_rule_writes rf rest (set_meta p k (rf src))
  | ICtSet k src :: rest => run_rule_writes rf rest (set_ct p k (rf src))
  | ILookupVal keys name dreg :: rest =>
      run_rule_writes (set_reg rf dreg (map_lookup_data (List.concat (map rf keys))
                                                        (e_map (pkt_env p) name))) rest p
  | INat _ _ _ _ _ _ _ :: _ => p
  | ITproxy _ _ _ :: _ => p
  | IFwd _ _ _ :: _ => p
  | IQueueSreg _ _ _ :: _ => p
  | ILimit spec :: rest => if pkt_limit p spec then run_rule_writes rf rest p else p
  | IQuota spec :: rest => if pkt_quota p spec then run_rule_writes rf rest p else p
  | IConnlimit spec :: rest => if pkt_connlimit p spec then run_rule_writes rf rest p else p
  | ICounter _ _ :: rest => run_rule_writes rf rest p
  | INotrack :: rest => run_rule_writes rf rest p
  | ILog _ :: rest => run_rule_writes rf rest p
  | IObjref _ _ :: rest => run_rule_writes rf rest p
  | ISynproxy _ _ :: rest => run_rule_writes rf rest p
  | ILast _ :: rest => run_rule_writes rf rest p
  | IDynset _ _ _ _ :: rest => run_rule_writes rf rest p
  | IExthdrReset _ _ :: rest => run_rule_writes rf rest p
  | IDup _ _ :: rest => run_rule_writes rf rest p
  | IObjrefMap _ _ :: rest => run_rule_writes rf rest p
  | ICtSetDir _ _ _ :: rest => run_rule_writes rf rest p
  | IExthdrWrite _ _ _ _ _ :: rest => run_rule_writes rf rest p
  | IReject _ _ :: _ => p
  | IQueue _ _ _ _ :: _ => p
  | IImmediate _ :: _ => p
  end.

(** Is a value-source "simple" (immediate or field)?  These are exactly the
    operands for which the proof establishes value-correctness ([eval_vsrc] =
    the register the bytecode leaves), so the mutation theorem is stated for
    rules whose set-statement operands are simple — the common `meta mark set
    <const>` / `ct mark set <field>` shapes, incl. the set-then-match bug. *)
Definition simple_vsrc (vs : vsrc) : bool :=
  match vs with VImm _ | VField _ _ => true | _ => false end.
Definition simple_writes (r : rule) : bool :=
  forallb (fun it => match it with
                     | BStmt (SMetaSet _ vs) | BStmt (SCtSet _ vs) => simple_vsrc vs
                     | _ => true end) (r_body r).

(** The declarative meta/ct effect of one rule: when it applies, fold its set
    statements (in body order, later overrides earlier) writing [eval_vsrc vs];
    the operand is evaluated against the packet mutated so far, matching the VM
    (whose operand loads read the already-mutated packet). *)
Definition dsl_writes (r : rule) (p : packet) : packet :=
  if rule_applies r p then
    fold_left (fun acc it => match it with
                             | BStmt (SMetaSet k vs) => set_meta acc k (eval_vsrc vs acc)
                             | BStmt (SCtSet k vs)   => set_ct acc k (eval_vsrc vs acc)
                             | _ => acc end) (r_body r) p
  else p.

(** Mutation-aware rule-list evaluation: a non-terminal applicable rule threads
    its writes to the rest, so a later rule observes an earlier `set`. *)
Fixpoint eval_rules_mut (rs : list rule) (p : packet) : option verdict :=
  match rs with
  | [] => None
  | r :: rest =>
      if rule_applies r p then
        match outcome r p with
        | Some v => if terminal v then Some v else eval_rules_mut rest (dsl_writes r p)
        | None   => eval_rules_mut rest (dsl_writes r p)
        end
      else eval_rules_mut rest p
  end.

Fixpoint run_program_mut (prog : program) (p : packet) : option verdict :=
  match prog with
  | [] => None
  | rp :: rest =>
      match run_rule empty_rf rp p with
      | Some v => if terminal v then Some v else run_program_mut rest (run_rule_writes empty_rf rp p)
      | None   => run_program_mut rest (run_rule_writes empty_rf rp p)
      end
  end.

Definition eval_chain_mut (c : chain) (p : packet) : verdict :=
  match eval_rules_mut (c_rules c) p with Some v => v | None => c_policy c end.
Definition run_chain_mut (prog : program) (policy : verdict) (p : packet) : verdict :=
  match run_program_mut prog p with Some v => v | None => policy end.

(** ** Multi-chain control flow: jump / goto / return + user-defined chains.

    A [jump n] calls chain [n] and *resumes* the caller after it (on the callee's
    fall-through or a [return]); a [goto n] tail-calls [n] and does NOT resume; a
    [return] pops to the caller.  A terminal verdict (accept/drop/reject/queue)
    reached anywhere stops the whole traversal.  Recursion through the named chain
    environment is not structurally terminating (nft rejects jump loops), so the
    interpreters are *fuel-bounded*; the correctness theorem holds for every fuel. *)

Fixpoint chain_lookup (cs : list (String.string * chain)) (n : String.string) : option chain :=
  match cs with
  | [] => None
  | (m, ch) :: rest => if String.eqb n m then Some ch else chain_lookup rest n
  end.

Fixpoint prog_lookup (cs : list (String.string * program)) (n : String.string) : option program :=
  match cs with
  | [] => None
  | (m, prg) :: rest => if String.eqb n m then Some prg else prog_lookup rest n
  end.

(** DSL semantics under a chain environment [cs] (the user-defined chains). *)
Fixpoint eval_rules_j (fuel : nat) (cs : list (String.string * chain))
                      (rs : list rule) (p : packet) : option verdict :=
  match fuel with
  | O => None
  | S fuel' =>
    match rs with
    | [] => None
    | r :: rest =>
      if rule_applies r p then
        match outcome r p with
        | None => eval_rules_j fuel' cs rest p
        | Some Return => None
        | Some (Jump n) =>
            match chain_lookup cs n with
            | Some ch => match eval_rules_j fuel' cs (c_rules ch) p with
                         | Some v => Some v
                         | None   => eval_rules_j fuel' cs rest p
                         end
            | None => eval_rules_j fuel' cs rest p
            end
        | Some (Goto n) =>
            match chain_lookup cs n with
            | Some ch => eval_rules_j fuel' cs (c_rules ch) p
            | None    => None
            end
        | Some Continue => eval_rules_j fuel' cs rest p
        | Some v => Some v
        end
      else eval_rules_j fuel' cs rest p
    end
  end.

Definition eval_table (fuel : nat) (cs : list (String.string * chain))
                      (base : chain) (p : packet) : verdict :=
  match eval_rules_j fuel cs (c_rules base) p with
  | Some v => v
  | None   => c_policy base
  end.

(** Bytecode VM under a compiled chain environment [cs]; mirrors [eval_rules_j]. *)
Fixpoint run_rules_j (fuel : nat) (cs : list (String.string * program))
                     (prog : program) (p : packet) : option verdict :=
  match fuel with
  | O => None
  | S fuel' =>
    match prog with
    | [] => None
    | rp :: rest =>
      match run_rule empty_rf rp p with
      | None => run_rules_j fuel' cs rest p
      | Some Return => None
      | Some (Jump n) =>
          match prog_lookup cs n with
          | Some prg => match run_rules_j fuel' cs prg p with
                        | Some v => Some v
                        | None   => run_rules_j fuel' cs rest p
                        end
          | None => run_rules_j fuel' cs rest p
          end
      | Some (Goto n) =>
          match prog_lookup cs n with
          | Some prg => run_rules_j fuel' cs prg p
          | None     => None
          end
      | Some Continue => run_rules_j fuel' cs rest p
      | Some v => Some v
      end
    end
  end.

Definition run_table (fuel : nat) (cs : list (String.string * program))
                     (base : program) (policy : verdict) (p : packet) : verdict :=
  match run_rules_j fuel cs base p with
  | Some v => v
  | None   => policy
  end.
