(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** RTL function inlining: semantic preservation *)

Require Import Coqlib Wfsimpl Maps Errors Integers.
Require Import AST Linking Values Memory Globalenvs Events Smallstep.
Require Import Op Registers RTL.
Require Import Inlining Inliningspec.
Require Import sflib.
Require SimMemInj.

Definition match_prog (prog tprog: program) :=
  match_program (fun cunit f tf => transf_fundef (funenv_program cunit) f = OK tf) eq prog tprog.

Lemma transf_program_match:
  forall prog tprog, transf_program prog = OK tprog -> match_prog prog tprog.
Proof.
  intros. eapply match_transform_partial_program_contextual; eauto.
Qed.

Section INLINING.

Variable prog tprog: program.
Hypothesis TRANSF: match_prog prog tprog.

Section CORELEMMA.

Variable se tse: Senv.t.
Hypothesis (MATCH_SENV: Senv.equiv se tse).
Variable ge tge: genv.
Hypothesis SECOMPATSRC: senv_genv_compat se ge.
Hypothesis SECOMPATTGT: senv_genv_compat tse tge.

Hypothesis (GENV_COMPAT: genv_compat ge prog).

Hypothesis (MATCH_GENV: Genv.match_genvs (match_globdef (fun cunit f tf => transf_fundef (funenv_program cunit) f = OK tf) eq prog) ge tge).

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof (Genv.find_symbol_match_genv MATCH_GENV).

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof (Genv.senv_match_genv MATCH_GENV).

Lemma functions_translated:
  forall (v: val) (f: fundef),
  Genv.find_funct ge v = Some f ->
  exists cu f', Genv.find_funct tge v = Some f' /\ transf_fundef (funenv_program cu) f = OK f' /\ linkorder cu prog.
Proof (Genv.find_funct_match_genv MATCH_GENV).

Lemma function_ptr_translated:
  forall (b: block) (f: fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists cu f', Genv.find_funct_ptr tge b = Some f' /\ transf_fundef (funenv_program cu) f = OK f' /\ linkorder cu prog.
Proof (Genv.find_funct_ptr_match_genv MATCH_GENV).

Lemma sig_function_translated:
  forall cu f f', transf_fundef (funenv_program cu) f = OK f' -> funsig f' = funsig f.
Proof.
  intros. destruct f; Errors.monadInv H.
  exploit transf_function_spec; eauto. intros SP; inv SP. auto.
  auto.
Qed.

(** ** Properties of contexts and relocations *)

Remark sreg_below_diff:
  forall ctx r r', Plt r' ctx.(dreg) -> sreg ctx r <> r'.
Proof.
  intros. zify. unfold sreg; rewrite shiftpos_eq. extlia.
Qed.

Remark context_below_diff:
  forall ctx1 ctx2 r1 r2,
  context_below ctx1 ctx2 -> Ple r1 ctx1.(mreg) -> sreg ctx1 r1 <> sreg ctx2 r2.
Proof.
  intros. red in H. zify. unfold sreg; rewrite ! shiftpos_eq. extlia.
Qed.

Remark context_below_lt:
  forall ctx1 ctx2 r, context_below ctx1 ctx2 -> Ple r ctx1.(mreg) -> Plt (sreg ctx1 r) ctx2.(dreg).
Proof.
  intros. red in H. unfold Plt; zify. unfold sreg; rewrite shiftpos_eq.
  extlia.
Qed.

(*
Remark context_below_le:
  forall ctx1 ctx2 r, context_below ctx1 ctx2 -> Ple r ctx1.(mreg) -> Ple (sreg ctx1 r) ctx2.(dreg).
Proof.
  intros. red in H. unfold Ple; zify. unfold sreg; rewrite shiftpos_eq.
  extlia.
Qed.
*)

(** ** Agreement between register sets before and after inlining. *)

Definition agree_regs (F: meminj) (ctx: context) (rs rs': regset) :=
  (forall r, Ple r ctx.(mreg) -> Val.inject F rs#r rs'#(sreg ctx r))
/\(forall r, Plt ctx.(mreg) r -> rs#r = Vundef).

Definition val_reg_charact (F: meminj) (ctx: context) (rs': regset) (v: val) (r: reg) :=
  (Plt ctx.(mreg) r /\ v = Vundef) \/ (Ple r ctx.(mreg) /\ Val.inject F v rs'#(sreg ctx r)).

Remark Plt_Ple_dec:
  forall p q, {Plt p q} + {Ple q p}.
Proof.
  intros. destruct (plt p q). left; auto. right; extlia.
Qed.

Lemma agree_val_reg_gen:
  forall F ctx rs rs' r, agree_regs F ctx rs rs' -> val_reg_charact F ctx rs' rs#r r.
Proof.
  intros. destruct H as [A B].
  destruct (Plt_Ple_dec (mreg ctx) r).
  left. rewrite B; auto.
  right. auto.
Qed.

Lemma agree_val_regs_gen:
  forall F ctx rs rs' rl,
  agree_regs F ctx rs rs' -> list_forall2 (val_reg_charact F ctx rs') rs##rl rl.
Proof.
  induction rl; intros; constructor; auto. apply agree_val_reg_gen; auto.
Qed.

Lemma agree_val_reg:
  forall F ctx rs rs' r, agree_regs F ctx rs rs' -> Val.inject F rs#r rs'#(sreg ctx r).
Proof.
  intros. exploit agree_val_reg_gen; eauto. instantiate (1 := r). intros [[A B] | [A B]].
  rewrite B; auto.
  auto.
Qed.

Lemma agree_val_regs:
  forall F ctx rs rs' rl, agree_regs F ctx rs rs' -> Val.inject_list F rs##rl rs'##(sregs ctx rl).
Proof.
  induction rl; intros; simpl. constructor. constructor; auto. apply agree_val_reg; auto.
Qed.

Lemma agree_set_reg:
  forall F ctx rs rs' r v v',
  agree_regs F ctx rs rs' ->
  Val.inject F v v' ->
  Ple r ctx.(mreg) ->
  agree_regs F ctx (rs#r <- v) (rs'#(sreg ctx r) <- v').
Proof.
  unfold agree_regs; intros. destruct H. split; intros.
  repeat rewrite Regmap.gsspec.
  destruct (peq r0 r). subst r0. rewrite peq_true. auto.
  rewrite peq_false. auto. apply shiftpos_diff; auto.
  rewrite Regmap.gso. auto. extlia.
Qed.

Lemma agree_set_reg_undef:
  forall F ctx rs rs' r v',
  agree_regs F ctx rs rs' ->
  agree_regs F ctx (rs#r <- Vundef) (rs'#(sreg ctx r) <- v').
Proof.
  unfold agree_regs; intros. destruct H. split; intros.
  repeat rewrite Regmap.gsspec.
  destruct (peq r0 r). subst r0. rewrite peq_true. auto.
  rewrite peq_false. auto. apply shiftpos_diff; auto.
  rewrite Regmap.gsspec. destruct (peq r0 r); auto.
Qed.

Lemma agree_set_reg_undef':
  forall F ctx rs rs' r,
  agree_regs F ctx rs rs' ->
  agree_regs F ctx (rs#r <- Vundef) rs'.
Proof.
  unfold agree_regs; intros. destruct H. split; intros.
  rewrite Regmap.gsspec.
  destruct (peq r0 r). subst r0. auto. auto.
  rewrite Regmap.gsspec. destruct (peq r0 r); auto.
Qed.

Lemma agree_regs_invariant:
  forall F ctx rs rs1 rs2,
  agree_regs F ctx rs rs1 ->
  (forall r, Ple ctx.(dreg) r -> Plt r (ctx.(dreg) + ctx.(mreg)) -> rs2#r = rs1#r) ->
  agree_regs F ctx rs rs2.
Proof.
  unfold agree_regs; intros. destruct H. split; intros.
  rewrite H0. auto.
  apply shiftpos_above.
  eapply Pos.lt_le_trans. apply shiftpos_below. extlia.
  apply H1; auto.
Qed.

Lemma agree_regs_incr:
  forall F ctx rs1 rs2 F',
  agree_regs F ctx rs1 rs2 ->
  inject_incr F F' ->
  agree_regs F' ctx rs1 rs2.
Proof.
  intros. destruct H. split; intros. eauto. auto.
Qed.

Remark agree_regs_init:
  forall F ctx rs, agree_regs F ctx (Regmap.init Vundef) rs.
Proof.
  intros; split; intros. rewrite Regmap.gi; auto. rewrite Regmap.gi; auto.
Qed.

Lemma agree_regs_init_regs:
  forall F ctx rl vl vl',
  Val.inject_list F vl vl' ->
  (forall r, In r rl -> Ple r ctx.(mreg)) ->
  agree_regs F ctx (init_regs vl rl) (init_regs vl' (sregs ctx rl)).
Proof.
  induction rl; simpl; intros.
  apply agree_regs_init.
  inv H. apply agree_regs_init.
  apply agree_set_reg; auto.
Qed.

(** ** Executing sequences of moves *)

Lemma tr_moves_init_regs:
  forall F stk f sp m ctx1 ctx2, context_below ctx1 ctx2 ->
  forall rdsts rsrcs vl pc1 pc2 rs1,
  tr_moves f.(fn_code) pc1 (sregs ctx1 rsrcs) (sregs ctx2 rdsts) pc2 ->
  (forall r, In r rdsts -> Ple r ctx2.(mreg)) ->
  list_forall2 (val_reg_charact F ctx1 rs1) vl rsrcs ->
  exists rs2,
    star step tse tge (State stk f sp pc1 rs1 m)
               E0 (State stk f sp pc2 rs2 m)
  /\ agree_regs F ctx2 (init_regs vl rdsts) rs2
  /\ forall r, Plt r ctx2.(dreg) -> rs2#r = rs1#r.
Proof.
  induction rdsts; simpl; intros.
(* rdsts = nil *)
  inv H0. exists rs1; split. apply star_refl. split. apply agree_regs_init. auto.
(* rdsts = a :: rdsts *)
  inv H2. inv H0.
  exists rs1; split. apply star_refl. split. apply agree_regs_init. auto.
  simpl in H0. inv H0.
  exploit IHrdsts; eauto. intros [rs2 [A [B C]]].
  exists (rs2#(sreg ctx2 a) <- (rs2#(sreg ctx1 b1))).
  split. eapply star_right. eauto. eapply exec_Iop; eauto. traceEq.
  split. destruct H3 as [[P Q] | [P Q]].
  subst a1. eapply agree_set_reg_undef; eauto.
  eapply agree_set_reg; eauto. rewrite C; auto.  apply context_below_lt; auto.
  intros. rewrite Regmap.gso. auto. apply not_eq_sym. eapply sreg_below_diff; eauto.
  destruct H2; discriminate.
Qed.

(** ** Memory invariants *)

(** A stack location is private if it is not the image of a valid
   location and we have full rights on it. *)

Definition loc_private (F: meminj) (m m': mem) (sp: block) (ofs: Z) : Prop :=
  Mem.perm m' sp ofs Cur Freeable /\
  (forall b delta, F b = Some(sp, delta) -> ~Mem.perm m b (ofs - delta) Max Nonempty).

(** Likewise, for a range of locations. *)

Definition range_private (F: meminj) (m m': mem) (sp: block) (lo hi: Z) : Prop :=
  forall ofs, lo <= ofs < hi -> loc_private F m m' sp ofs.

Lemma range_private_tgt_private
      sm blk lo hi
      (MWF: SimMemInj.wf' sm)
      (PRIVTGT: range_private sm.(SimMemInj.inj) sm.(SimMemInj.src) sm.(SimMemInj.tgt) blk lo hi):
    forall ofs (BDD: lo <= ofs < hi), <<PRIVTGT: (SimMemInj.tgt_private sm) blk ofs>>.
Proof.
  ii. repeat red. specialize (PRIVTGT ofs BDD). red in PRIVTGT. des.
  esplits; eauto. red. eauto with mem.
Qed.

Lemma range_private_invariant:
  forall F m m' sp lo hi F1 m1 m1',
  range_private F m m' sp lo hi ->
  (forall b delta ofs,
      F1 b = Some(sp, delta) ->
      Mem.perm m1 b ofs Max Nonempty ->
      lo <= ofs + delta < hi ->
      F b = Some(sp, delta) /\ Mem.perm m b ofs Max Nonempty) ->
  (forall ofs, Mem.perm m' sp ofs Cur Freeable -> Mem.perm m1' sp ofs Cur Freeable) ->
  range_private F1 m1 m1' sp lo hi.
Proof.
  intros; red; intros. exploit H; eauto. intros [A B]. split; auto.
  intros; red; intros. exploit H0; eauto. lia. intros [P Q].
  eelim B; eauto.
Qed.

Lemma range_private_perms:
  forall F m m' sp lo hi,
  range_private F m m' sp lo hi ->
  Mem.range_perm m' sp lo hi Cur Freeable.
Proof.
  intros; red; intros. eapply H; eauto.
Qed.

Lemma range_private_alloc_left:
  forall F m m' sp' base hi sz m1 sp F1,
  range_private F m m' sp' base hi ->
  Mem.alloc m 0 sz = (m1, sp) ->
  F1 sp = Some(sp', base) ->
  (forall b, b <> sp -> F1 b = F b) ->
  range_private F1 m1 m' sp' (base + Z.max sz 0) hi.
Proof.
  intros; red; intros.
  exploit (H ofs). generalize (Z.le_max_r sz 0). lia. intros [A B].
  split; auto. intros; red; intros.
  exploit Mem.perm_alloc_inv; eauto.
  destruct (eq_block b sp); intros.
  subst b. rewrite H1 in H4; inv H4.
  rewrite Zmax_spec in H3. destruct (zlt 0 sz); lia.
  rewrite H2 in H4; auto. eelim B; eauto.
Qed.

Lemma range_private_free_left:
  forall F m m' sp base sz hi b m1,
  range_private F m m' sp (base + Z.max sz 0) hi ->
  Mem.free m b 0 sz = Some m1 ->
  F b = Some(sp, base) ->
  Mem.inject F m m' ->
  range_private F m1 m' sp base hi.
Proof.
  intros; red; intros.
  destruct (zlt ofs (base + Z.max sz 0)) as [z|z].
  red; split.
  replace ofs with ((ofs - base) + base) by lia.
  eapply Mem.perm_inject; eauto.
  eapply Mem.free_range_perm; eauto.
  rewrite Zmax_spec in z. destruct (zlt 0 sz); lia.
  intros; red; intros. destruct (eq_block b b0).
  subst b0. rewrite H1 in H4; inv H4.
  eelim Mem.perm_free_2; eauto. rewrite Zmax_spec in z. destruct (zlt 0 sz); lia.
  exploit Mem.mi_no_overlap; eauto.
  apply Mem.perm_cur_max. apply Mem.perm_implies with Freeable; auto with mem.
  eapply Mem.free_range_perm. eauto.
  instantiate (1 := ofs - base). rewrite Zmax_spec in z. destruct (zlt 0 sz); lia.
  eapply Mem.perm_free_3; eauto.
  intros [A | A]. congruence. lia.

  exploit (H ofs). lia. intros [A B]. split. auto.
  intros; red; intros. eelim B; eauto. eapply Mem.perm_free_3; eauto.
Qed.

Lemma range_private_extcall:
  forall F F' m1 m2 m1' m2' sp base hi,
  range_private F m1 m1' sp base hi ->
  (forall b ofs p,
     Mem.valid_block m1 b -> Mem.perm m2 b ofs Max p -> Mem.perm m1 b ofs Max p) ->
  Mem.unchanged_on (loc_out_of_reach F m1) m1' m2' ->
  Mem.inject F m1 m1' ->
  inject_incr F F' ->
  inject_separated F F' m1 m1' ->
  Mem.valid_block m1' sp ->
  range_private F' m2 m2' sp base hi.
Proof.
  intros until hi; intros RP PERM UNCH INJ INCR SEP VB.
  red; intros. exploit RP; eauto. intros [A B].
  split. eapply Mem.perm_unchanged_on; eauto.
  intros. red in SEP. destruct (F b) as [[sp1 delta1] |] eqn:?.
  exploit INCR; eauto. intros EQ; rewrite H0 in EQ; inv EQ.
  red; intros; eelim B; eauto. eapply PERM; eauto.
  red. destruct (plt b (Mem.nextblock m1)); auto.
  exploit Mem.mi_freeblocks; eauto. congruence.
  exploit SEP; eauto. tauto.
Qed.

(** ** Relating global environments *)

Inductive match_globalenvs (F: meminj) (bound: block): Prop :=
  | mk_match_globalenvs
      (DOMAIN: forall b, Plt b bound -> F b = Some(b, 0))
      (IMAGE: forall b1 b2 delta, F b1 = Some(b2, delta) -> Plt b2 bound -> b1 = b2)
      (SYMBOLS: forall id b, Genv.find_symbol ge id = Some b -> Plt b bound)
      (FUNCTIONS: forall b fd, Genv.find_funct_ptr ge b = Some fd -> Plt b bound)
      (VARINFOS: forall b gv, Genv.find_var_info ge b = Some gv -> Plt b bound).

Lemma find_function_ptr_agree:
  forall ros rs fptr F ctx rs' bound,
  find_function_ptr ge ros rs = fptr ->
  agree_regs F ctx rs rs' ->
  match_globalenvs F bound ->
  exists tfptr,
  find_function_ptr tge (sros ctx ros) rs' = tfptr /\ Val.inject F fptr tfptr.
Proof.
  intros. destruct ros as [r | id]; simpl in *.
- (* register *)
  clarify. esplits; eauto. eapply agree_val_reg; eauto.
- (* symbol *)
  rewrite symbols_preserved. destruct (Genv.find_symbol ge id) eqn:T; clarify; esplits; eauto.
  inv H1. exploit DOMAIN; eauto.
Qed.

Lemma find_inlined_function:
  forall fenv id rs f fptr,
  fenv_compat prog fenv ->
  find_function_ptr ge (inr id) rs = fptr ->
  fenv!id = Some f ->
  <<FPTR: Genv.find_funct ge fptr = Some (Internal f)>>.
Proof.
  intros.
  apply H in H1. apply GENV_COMPAT in H1. destruct H1 as (b & A & B).
  simpl in H0. unfold fundef in *. rewrite A in H0.
  clarify. ss. des_ifs. unfold Genv.find_funct_ptr. des_ifs.
Qed.

Lemma functions_injected
      j v tv f
      (SRC: Genv.find_funct ge v = Some f)
      (INJ: Val.inject j v tv)
      (MATCH: exists bound, match_globalenvs j bound):
    exists cunit tf, <<TGT: Genv.find_funct tge tv = Some tf>> /\
                     <<TRANSF: transf_fundef (funenv_program cunit) f = OK tf>> /\
                     <<LINK: linkorder cunit prog>>.
Proof.
  des. inv MATCH. unfold Genv.find_funct in *. des_ifs_safe. inv INJ.
  exploit FUNCTIONS; eauto. intro BD.
  exploit DOMAIN; eauto. i; des. clarify. des_ifs.
  exploit functions_translated; eauto.
  { rewrite Genv.find_funct_find_funct_ptr. eauto. }
  eauto.
Qed.

(** Translation of builtin arguments. *)

Lemma tr_builtin_arg:
  forall F bound ctx rs rs' sp sp' m m',
  match_globalenvs F bound ->
  agree_regs F ctx rs rs' ->
  F sp = Some(sp', ctx.(dstk)) ->
  Mem.inject F m m' ->
  forall a v,
  eval_builtin_arg ge (fun r => rs#r) (Vptr sp Ptrofs.zero) m a v ->
  exists v', eval_builtin_arg tge (fun r => rs'#r) (Vptr sp' Ptrofs.zero) m' (sbuiltinarg ctx a) v'
          /\ Val.inject F v v'.
Proof.
  intros until m'; intros MG AG SP MI. induction 1; simpl.
- exists rs'#(sreg ctx x); split. constructor. eapply agree_val_reg; eauto.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- exploit Mem.loadv_inject; eauto.
  instantiate (1 := Vptr sp' (Ptrofs.add ofs (Ptrofs.repr (dstk ctx)))).
  simpl. econstructor; eauto. rewrite Ptrofs.add_zero_l; auto.
  intros (v' & A & B). exists v'; split; auto. constructor. simpl. rewrite Ptrofs.add_zero_l; auto.
- econstructor; split. constructor. simpl. econstructor; eauto. rewrite ! Ptrofs.add_zero_l; auto.
- assert (Val.inject F (Senv.symbol_address ge id ofs) (Senv.symbol_address tge id ofs)).
  { unfold Senv.symbol_address; simpl; unfold Genv.symbol_address.
    rewrite symbols_preserved. destruct (Genv.find_symbol ge id) as [b|] eqn:FS; auto.
    inv MG. econstructor. eauto. rewrite Ptrofs.add_zero; auto. }
  exploit Mem.loadv_inject; eauto. intros (v' & A & B).
  exists v'; eauto with barg.
- econstructor; split. constructor.
  unfold Senv.symbol_address; simpl; unfold Genv.symbol_address.
  rewrite symbols_preserved. destruct (Genv.find_symbol ge id) as [b|] eqn:FS; auto.
  inv MG. econstructor. eauto. rewrite Ptrofs.add_zero; auto.
- destruct IHeval_builtin_arg1 as (v1' & A1 & B1).
  destruct IHeval_builtin_arg2 as (v2' & A2 & B2).
  econstructor; split. eauto with barg. apply Val.longofwords_inject; auto.
- destruct IHeval_builtin_arg1 as (v1' & A1 & B1).
  destruct IHeval_builtin_arg2 as (v2' & A2 & B2).
  econstructor; split. eauto with barg.
  destruct Archi.ptr64; auto using Val.add_inject, Val.addl_inject.
Qed.

Lemma tr_builtin_args:
  forall F bound ctx rs rs' sp sp' m m',
  match_globalenvs F bound ->
  agree_regs F ctx rs rs' ->
  F sp = Some(sp', ctx.(dstk)) ->
  Mem.inject F m m' ->
  forall al vl,
  eval_builtin_args ge (fun r => rs#r) (Vptr sp Ptrofs.zero) m al vl ->
  exists vl', eval_builtin_args tge (fun r => rs'#r) (Vptr sp' Ptrofs.zero) m' (map (sbuiltinarg ctx) al) vl'
          /\ Val.inject_list F vl vl'.
Proof.
  induction 5; simpl.
- exists (@nil val); split; constructor.
- exploit tr_builtin_arg; eauto. intros (v1' & A & B).
  destruct IHlist_forall2 as (vl' & C & D).
  exists (v1' :: vl'); split; constructor; auto.
Qed.

(** ** Relating stacks *)

Inductive match_stacks (F: meminj) (m m': mem) (sm0: SimMemInj.t') :
             list stackframe -> list stackframe -> block -> Prop :=
  | match_stacks_nil: forall bound1 bound
        (SYMBINJ: symbols_inject F se tse)
        (HI: bound1 = ge.(Genv.genv_next))
        (MG: match_globalenvs F bound1)
        (BELOW: Ple bound1 bound),
      match_stacks F m m' sm0 nil nil bound
  | match_stacks_cons: forall res f sp pc rs stk f' sp' rs' stk' bound fenv ctx
        (MS: match_stacks_inside F m m' sm0 stk stk' f' ctx sp' rs')
        (DISJ: sm0.(SimMemInj.tgt_external) /2\ (fun blk _ => sp' = blk)  <2= bot2)
        (COMPAT: fenv_compat prog fenv)
        (FB: tr_funbody fenv f'.(fn_stacksize) ctx f f'.(fn_code))
        (AG: agree_regs F ctx rs rs')
        (SP: F sp = Some(sp', ctx.(dstk)))
        (PRIV: range_private F m m' sp' (ctx.(dstk) + ctx.(mstk)) f'.(fn_stacksize))
        (SSZ1: 0 <= f'.(fn_stacksize) < Ptrofs.max_unsigned)
        (SSZ2: forall ofs, Mem.perm m' sp' ofs Max Nonempty -> 0 <= ofs <= f'.(fn_stacksize))
        (RES: Ple res ctx.(mreg))
        (BELOW: Plt sp' bound),
      match_stacks F m m' sm0
                   (Stackframe res f (Vptr sp Ptrofs.zero) pc rs :: stk)
                   (Stackframe (sreg ctx res) f' (Vptr sp' Ptrofs.zero) (spc ctx pc) rs' :: stk')
                   bound
  | match_stacks_untailcall: forall stk res f' sp' rpc rs' stk' bound ctx
        (MS: match_stacks_inside F m m' sm0 stk stk' f' ctx sp' rs')
        (DISJ: sm0.(SimMemInj.tgt_external) /2\ (fun blk _ => sp' = blk)  <2= bot2)
        (PRIV: range_private F m m' sp' ctx.(dstk) f'.(fn_stacksize))
        (SSZ1: 0 <= f'.(fn_stacksize) < Ptrofs.max_unsigned)
        (SSZ2: forall ofs, Mem.perm m' sp' ofs Max Nonempty -> 0 <= ofs <= f'.(fn_stacksize))
        (RET: ctx.(retinfo) = Some (rpc, res))
        (BELOW: Plt sp' bound),
      match_stacks F m m' sm0
                   stk
                   (Stackframe res f' (Vptr sp' Ptrofs.zero) rpc rs' :: stk')
                   bound

with match_stacks_inside (F: meminj) (m m': mem) (sm0: SimMemInj.t') :
        list stackframe -> list stackframe -> function -> context -> block -> regset -> Prop :=
  | match_stacks_inside_base: forall stk stk' f' ctx sp' rs'
        (MS: match_stacks F m m' sm0 stk stk' sp')
        (DISJ: sm0.(SimMemInj.tgt_external) /2\ (fun blk _ => sp' = blk)  <2= bot2)
        (BB: (SimMemInj.tgt_parent_nb sm0 <= sp')%positive)
        (RET: ctx.(retinfo) = None)
        (DSTK: ctx.(dstk) = 0),
      match_stacks_inside F m m' sm0 stk stk' f' ctx sp' rs'
  | match_stacks_inside_inlined: forall res f sp pc rs stk stk' f' fenv ctx sp' rs' ctx'
        (MS: match_stacks_inside F m m' sm0 stk stk' f' ctx' sp' rs')
        (DISJ: sm0.(SimMemInj.tgt_external) /2\ (fun blk _ => sp' = blk)  <2= bot2)
        (BB: (SimMemInj.tgt_parent_nb sm0 <= sp')%positive)
        (COMPAT: fenv_compat prog fenv)
        (FB: tr_funbody fenv f'.(fn_stacksize) ctx' f f'.(fn_code))
        (AG: agree_regs F ctx' rs rs')
        (SP: F sp = Some(sp', ctx'.(dstk)))
        (PAD: range_private F m m' sp' (ctx'.(dstk) + ctx'.(mstk)) ctx.(dstk))
        (RES: Ple res ctx'.(mreg))
        (RET: ctx.(retinfo) = Some (spc ctx' pc, sreg ctx' res))
        (BELOW: context_below ctx' ctx)
        (SBELOW: context_stack_call ctx' ctx),
      match_stacks_inside F m m' sm0 (Stackframe res f (Vptr sp Ptrofs.zero) pc rs :: stk)
                                 stk' f' ctx sp' rs'.

(** Properties of match_stacks *)

Section MATCH_STACKS.

Variable F: meminj.
Variables m m': mem.

Lemma match_stacks_symbols_inject:
  forall stk stk' bound sm0,
  match_stacks F m m' sm0 stk stk' bound -> symbols_inject F se tse
with match_stacks_inside_symbols_inject:
  forall stk stk' f ctx sp rs' sm0,
  match_stacks_inside F m m' sm0 stk stk' f ctx sp rs' -> symbols_inject F se tse.
Proof. induction 1; eauto. induction 1; eauto. Qed.

Lemma match_stacks_globalenvs:
  forall stk stk' bound sm0,
  match_stacks F m m' sm0 stk stk' bound -> exists b, match_globalenvs F b
with match_stacks_inside_globalenvs:
  forall stk stk' f ctx sp rs' sm0,
  match_stacks_inside F m m' sm0 stk stk' f ctx sp rs' -> exists b, match_globalenvs F b.
Proof.
  induction 1; eauto.
  induction 1; eauto.
Qed.

Lemma match_globalenvs_preserves_globals:
  forall b, match_globalenvs F b -> meminj_preserves_globals ge F.
Proof.
  intros. inv H. red. split. eauto. split. eauto.
  intros. symmetry. eapply IMAGE; eauto.
Qed.

Lemma match_stacks_inside_globals:
  forall stk stk' f ctx sp rs' sm0,
  match_stacks_inside F m m' sm0 stk stk' f ctx sp rs' -> meminj_preserves_globals ge F.
Proof.
  intros. exploit match_stacks_inside_globalenvs; eauto. intros [b A].
  eapply match_globalenvs_preserves_globals; eauto.
Qed.

Lemma match_stacks_bound:
  forall stk stk' bound bound1 sm0,
  match_stacks F m m' sm0 stk stk' bound ->
  Ple bound bound1 ->
  match_stacks F m m' sm0 stk stk' bound1.
Proof.
  intros. inv H.
  apply match_stacks_nil with ge.(Genv.genv_next); auto. eapply Ple_trans; eauto.
  eapply match_stacks_cons; eauto. eapply Pos.lt_le_trans; eauto.
  eapply match_stacks_untailcall; eauto. eapply Pos.lt_le_trans; eauto.
Qed.

Variable F1: meminj.
Variables m1 m1': mem.
Hypothesis INCR: inject_incr F F1.

Lemma match_stacks_invariant:
  forall stk stk' bound sm0, match_stacks F m m' sm0 stk stk' bound ->
  forall (INJ: forall b1 b2 delta,
               F1 b1 = Some(b2, delta) -> Plt b2 bound -> F b1 = Some(b2, delta))
         (PERM1: forall b1 b2 delta ofs,
               F1 b1 = Some(b2, delta) -> Plt b2 bound ->
               Mem.perm m1 b1 ofs Max Nonempty -> Mem.perm m b1 ofs Max Nonempty)
         (PERM2: forall b ofs, Plt b bound ->
               Mem.perm m' b ofs Cur Freeable -> Mem.perm m1' b ofs Cur Freeable)
         (PERM3: forall b ofs k p, Plt b bound ->
               Mem.perm m1' b ofs k p -> Mem.perm m' b ofs k p),
  match_stacks F1 m1 m1' sm0 stk stk' bound

with match_stacks_inside_invariant:
  forall stk stk' f' ctx sp' rs1 sm0,
  match_stacks_inside F m m' sm0 stk stk' f' ctx sp' rs1 ->
  forall rs2
         (RS: forall r, Plt r ctx.(dreg) -> rs2#r = rs1#r)
         (INJ: forall b1 b2 delta,
               F1 b1 = Some(b2, delta) -> Ple b2 sp' -> F b1 = Some(b2, delta))
         (PERM1: forall b1 b2 delta ofs,
               F1 b1 = Some(b2, delta) -> Ple b2 sp' ->
               Mem.perm m1 b1 ofs Max Nonempty -> Mem.perm m b1 ofs Max Nonempty)
         (PERM2: forall b ofs, Ple b sp' ->
               Mem.perm m' b ofs Cur Freeable -> Mem.perm m1' b ofs Cur Freeable)
         (PERM3: forall b ofs k p, Ple b sp' ->
               Mem.perm m1' b ofs k p -> Mem.perm m' b ofs k p),
  match_stacks_inside F1 m1 m1' sm0 stk stk' f' ctx sp' rs2.

Proof.
  induction 1; intros.
  (* nil *)
  apply match_stacks_nil with (bound1 := bound1).
  { eapply symbols_inject_incr; eauto.
    - i. inv SECOMPATSRC. rewrite NB in *.
      inv MG. exploit DOMAIN; eauto. i; clarify.
      exploit INCR; eauto. i; clarify.
    - i. inv SECOMPATTGT. rewrite NB in *.
      erewrite INJ; eauto.
      inv MATCH_GENV. rewrite mge_next in *. extlia.
  }
  { ss. }
  inv MG. constructor; auto.
  intros. apply IMAGE with delta. eapply INJ; eauto. eapply Pos.lt_le_trans; eauto.
  auto. auto.
  (* cons *)
  apply match_stacks_cons with (fenv := fenv) (ctx := ctx); auto.
  eapply match_stacks_inside_invariant; eauto.
  intros; eapply INJ; eauto; extlia.
  intros; eapply PERM1; eauto; extlia.
  intros; eapply PERM2; eauto; extlia.
  intros; eapply PERM3; eauto; extlia.
  eapply agree_regs_incr; eauto.
  eapply range_private_invariant; eauto.
  (* untailcall *)
  apply match_stacks_untailcall with (ctx := ctx); auto.
  eapply match_stacks_inside_invariant; eauto.
  intros; eapply INJ; eauto; extlia.
  intros; eapply PERM1; eauto; extlia.
  intros; eapply PERM2; eauto; extlia.
  intros; eapply PERM3; eauto; extlia.
  eapply range_private_invariant; eauto.

  induction 1; intros.
  (* base *)
  eapply match_stacks_inside_base; eauto.
  eapply match_stacks_invariant; eauto.
  intros; eapply INJ; eauto; extlia.
  intros; eapply PERM1; eauto; extlia.
  intros; eapply PERM2; eauto; extlia.
  intros; eapply PERM3; eauto; extlia.
  (* inlined *)
  apply match_stacks_inside_inlined with (fenv := fenv) (ctx' := ctx'); auto.
  apply IHmatch_stacks_inside; auto.
  intros. apply RS. red in BELOW. extlia.
  apply agree_regs_incr with F; auto.
  apply agree_regs_invariant with rs'; auto.
  intros. apply RS. red in BELOW. extlia.
  eapply range_private_invariant; eauto.
    intros. split. eapply INJ; eauto. extlia. eapply PERM1; eauto. extlia.
    intros. eapply PERM2; eauto. extlia.
Qed.

Lemma match_stacks_empty:
  forall stk stk' bound sm0,
  match_stacks F m m' sm0 stk stk' bound -> stk = nil -> stk' = nil
with match_stacks_inside_empty:
  forall stk stk' f ctx sp rs sm0,
  match_stacks_inside F m m' sm0 stk stk' f ctx sp rs -> stk = nil -> stk' = nil /\ ctx.(retinfo) = None.
Proof.
  induction 1; intros.
  auto.
  discriminate.
  exploit match_stacks_inside_empty; eauto. intros [A B]. congruence.
  induction 1; intros.
  split. eapply match_stacks_empty; eauto. auto.
  discriminate.
Qed.

Lemma match_stacks_le: forall
      sm0 sm1 F m m' stk stk' bound
      (MS: match_stacks F m m' sm0 stk stk' bound)
      (LE: SimMemInj.le' sm0 sm1),
    <<MS: match_stacks F m m' sm1 stk stk' bound>>
with match_stacks_inside_le: forall
      sm0 sm1 F m m' stk stk' f' ctx sp' rs'
      (MS: match_stacks_inside F m m' sm0 stk stk' f' ctx sp' rs')
      (LE: SimMemInj.le' sm0 sm1),
    <<MS: match_stacks_inside F m m' sm1 stk stk' f' ctx sp' rs'>>.
Proof.
  - induction 1; ii; ss; econs; eauto; try (eapply match_stacks_inside_le; eauto).
    all: ii; des; eapply DISJ; eauto; esplits; eauto; inv LE; congruence.
  - induction 1; ii; ss.
    + econs; eauto; try (eapply match_stacks_le; eauto); inv LE; try congruence.
      ii; des; eapply DISJ; eauto; esplits; eauto; congruence.
    + econs 2; eauto; try (eapply match_stacks_inside_le; eauto); inv LE; try congruence.
      ii; des; eapply DISJ; eauto; esplits; eauto; congruence.
Qed.

End MATCH_STACKS.

(** Preservation by assignment to a register *)

Lemma match_stacks_inside_set_reg:
  forall F m m' stk stk' f' ctx sp' rs' r v sm0,
  match_stacks_inside F m m' sm0 stk stk' f' ctx sp' rs' ->
  match_stacks_inside F m m' sm0 stk stk' f' ctx sp' (rs'#(sreg ctx r) <- v).
Proof.
  intros. eapply match_stacks_inside_invariant; eauto.
  intros. apply Regmap.gso. zify. unfold sreg; rewrite shiftpos_eq. extlia.
Qed.

Lemma match_stacks_inside_set_res:
  forall F m m' stk stk' f' ctx sp' rs' res v sm0,
  match_stacks_inside F m m' sm0 stk stk' f' ctx sp' rs' ->
  match_stacks_inside F m m' sm0 stk stk' f' ctx sp' (regmap_setres (sbuiltinres ctx res) v rs').
Proof.
  intros. destruct res; simpl; auto.
  apply match_stacks_inside_set_reg; auto.
Qed.

(** Preservation by a memory store *)

Lemma match_stacks_inside_store:
  forall F m m' stk stk' f' ctx sp' rs' chunk b ofs v m1 chunk' b' ofs' v' m1' sm0,
  match_stacks_inside F m m' sm0 stk stk' f' ctx sp' rs' ->
  Mem.store chunk m b ofs v = Some m1 ->
  Mem.store chunk' m' b' ofs' v' = Some m1' ->
  match_stacks_inside F m1 m1' sm0 stk stk' f' ctx sp' rs'.
Proof.
  intros.
  eapply match_stacks_inside_invariant; eauto with mem.
Qed.

(** Preservation by an allocation *)

Lemma match_stacks_inside_alloc_left:
  forall F m m' stk stk' f' ctx sp' rs' sm0,
  match_stacks_inside F m m' sm0 stk stk' f' ctx sp' rs' ->
  forall sz m1 b F1 delta,
  Mem.alloc m 0 sz = (m1, b) ->
  inject_incr F F1 ->
  F1 b = Some(sp', delta) ->
  (forall b1, b1 <> b -> F1 b1 = F b1) ->
  delta >= ctx.(dstk) ->
  match_stacks_inside F1 m1 m' sm0 stk stk' f' ctx sp' rs'.
Proof.
  induction 1; intros.
  (* base *)
  eapply match_stacks_inside_base; eauto.
  eapply match_stacks_invariant; eauto.
  intros. destruct (eq_block b1 b).
  subst b1. rewrite H1 in H4; inv H4. eelim Plt_strict; eauto.
  rewrite H2 in H4; auto.
  intros. exploit Mem.perm_alloc_inv; eauto. destruct (eq_block b1 b); intros; auto.
  subst b1. rewrite H1 in H4. inv H4. eelim Plt_strict; eauto.
  (* inlined *)
  eapply match_stacks_inside_inlined; eauto.
  eapply IHmatch_stacks_inside; eauto. destruct SBELOW. lia.
  eapply agree_regs_incr; eauto.
  eapply range_private_invariant; eauto.
  intros. exploit Mem.perm_alloc_inv; eauto. destruct (eq_block b0 b); intros.
  subst b0. rewrite H2 in H5; inv H5. elimtype False; extlia.
  rewrite H3 in H5; auto.
Qed.

(** Preservation by freeing *)

Lemma match_stacks_free_left:
  forall F m m' stk stk' sp b lo hi m1 sm0,
  match_stacks F m m' sm0 stk stk' sp ->
  Mem.free m b lo hi = Some m1 ->
  match_stacks F m1 m' sm0 stk stk' sp.
Proof.
  intros. eapply match_stacks_invariant; eauto.
  intros. eapply Mem.perm_free_3; eauto.
Qed.

Lemma match_stacks_free_right:
  forall F m m' stk stk' sp lo hi m1' sm0,
  match_stacks F m m' sm0 stk stk' sp ->
  Mem.free m' sp lo hi = Some m1' ->
  match_stacks F m m1' sm0 stk stk' sp.
Proof.
  intros. eapply match_stacks_invariant; eauto.
  intros. eapply Mem.perm_free_1; eauto with ordered_type.
  intros. eapply Mem.perm_free_3; eauto.
Qed.

Lemma min_alignment_sound:
  forall sz n, (min_alignment sz | n) -> Mem.inj_offset_aligned n sz.
Proof.
  intros; red; intros. unfold min_alignment in H.
  assert (2 <= sz -> (2 | n)). intros.
    destruct (zle sz 1). extlia.
    destruct (zle sz 2). auto.
    destruct (zle sz 4). apply Z.divide_trans with 4; auto. exists 2; auto.
    apply Z.divide_trans with 8; auto. exists 4; auto.
  assert (4 <= sz -> (4 | n)). intros.
    destruct (zle sz 1). extlia.
    destruct (zle sz 2). extlia.
    destruct (zle sz 4). auto.
    apply Z.divide_trans with 8; auto. exists 2; auto.
  assert (8 <= sz -> (8 | n)). intros.
    destruct (zle sz 1). extlia.
    destruct (zle sz 2). extlia.
    destruct (zle sz 4). extlia.
    auto.
  destruct chunk; simpl in *; auto.
  apply Z.divide_1_l.
  apply Z.divide_1_l.
  apply H2; lia.
  apply H2; lia.
Qed.

(** Preservation by external calls *)

Section EXTCALL.

Variables F1 F2: meminj.
Variables m1 m2 m1' m2': mem.
Hypothesis MAXPERM: forall b ofs p, Mem.valid_block m1 b -> Mem.perm m2 b ofs Max p -> Mem.perm m1 b ofs Max p.
Hypothesis MAXPERM': forall b ofs p, Mem.valid_block m1' b -> Mem.perm m2' b ofs Max p -> Mem.perm m1' b ofs Max p.
Hypothesis UNCHANGED: Mem.unchanged_on (loc_out_of_reach F1 m1) m1' m2'.
Hypothesis INJ: Mem.inject F1 m1 m1'.
Hypothesis INCR: inject_incr F1 F2.
Hypothesis SEP: inject_separated F1 F2 m1 m1'.

Lemma match_stacks_extcall:
  forall stk stk' bound sm0,
  match_stacks F1 m1 m1' sm0 stk stk' bound ->
  Ple bound (Mem.nextblock m1') ->
  match_stacks F2 m2 m2' sm0 stk stk' bound
with match_stacks_inside_extcall:
  forall stk stk' f' ctx sp' rs' sm0,
  match_stacks_inside F1 m1 m1' sm0 stk stk' f' ctx sp' rs' ->
  Plt sp' (Mem.nextblock m1') ->
  match_stacks_inside F2 m2 m2' sm0 stk stk' f' ctx sp' rs'.
Proof.
  induction 1; intros.
  apply match_stacks_nil with bound1; auto.
    { eapply symbols_inject_incr; eauto; i; destruct (F1 b) eqn:T;
        try by (destruct p; exploit INCR; eauto; i; clarify).
      - inv SECOMPATSRC. rewrite NB in *. inv MG. exploit DOMAIN; eauto. i; clarify.
      - exploit SEP; eauto. i; des. clarify. inv SECOMPATTGT. rewrite NB in *.
        inv MATCH_GENV. rewrite mge_next in *. unfold Mem.valid_block in *. extlia.
    }
    inv MG. constructor; intros; eauto.
    destruct (F1 b1) as [[b2' delta']|] eqn:?.
    exploit INCR; eauto. intros EQ; rewrite H0 in EQ; inv EQ. eapply IMAGE; eauto.
    exploit SEP; eauto. intros [A B]. elim B. red. extlia.
  eapply match_stacks_cons; eauto.
    eapply match_stacks_inside_extcall; eauto. extlia.
    eapply agree_regs_incr; eauto.
    eapply range_private_extcall; eauto. red; extlia.
    intros. apply SSZ2; auto. apply MAXPERM'; auto. red; extlia.
  eapply match_stacks_untailcall; eauto.
    eapply match_stacks_inside_extcall; eauto. extlia.
    eapply range_private_extcall; eauto. red; extlia.
    intros. apply SSZ2; auto. apply MAXPERM'; auto. red; extlia.
  induction 1; intros.
  eapply match_stacks_inside_base; eauto.
    eapply match_stacks_extcall; eauto. extlia.
  eapply match_stacks_inside_inlined; eauto.
    eapply agree_regs_incr; eauto.
    eapply range_private_extcall; eauto.
Qed.

End EXTCALL.

(** Change of context corresponding to an inlined tailcall *)

Lemma align_unchanged:
  forall n amount, amount > 0 -> (amount | n) -> align n amount = n.
Proof.
  intros. destruct H0 as [p EQ]. subst n. unfold align. decEq.
  apply Zdiv_unique with (b := amount - 1). lia. lia.
Qed.

Lemma match_stacks_inside_inlined_tailcall:
  forall fenv F m m' stk stk' f' ctx sp' rs' ctx' f sm0,
  match_stacks_inside F m m' sm0 stk stk' f' ctx sp' rs' ->
  context_below ctx ctx' ->
  context_stack_tailcall ctx f ctx' ->
  ctx'.(retinfo) = ctx.(retinfo) ->
  range_private F m m' sp' ctx.(dstk) f'.(fn_stacksize) ->
  forall (MYDISJ: sm0.(SimMemInj.tgt_external) /2\ (fun blk _ => sp' = blk) <2= bot2),
  tr_funbody fenv f'.(fn_stacksize) ctx' f f'.(fn_code) ->
  match_stacks_inside F m m' sm0 stk stk' f' ctx' sp' rs'.
Proof.
  intros. inv H.
  (* base *)
  eapply match_stacks_inside_base; eauto. congruence.
  rewrite H1. rewrite DSTK. apply align_unchanged. apply min_alignment_pos. apply Z.divide_0_r.
  (* inlined *)
  assert (dstk ctx <= dstk ctx'). rewrite H1. apply align_le. apply min_alignment_pos.
  eapply match_stacks_inside_inlined; eauto.
  red; intros. destruct (zlt ofs (dstk ctx)). apply PAD; lia. apply H3. inv H4. extlia.
  congruence.
  unfold context_below in *. extlia.
  unfold context_stack_call in *. lia.
Qed.

(** ** Relating states *)

Inductive match_states: RTL.state -> RTL.state -> SimMemInj.t' -> Prop :=
  | match_regular_states: forall stk f sp pc rs m stk' f' sp' rs' m' F fenv ctx
        sm0 (MCOMPAT: SimMemInj.mcompat sm0 m m' F)
        (MWF: SimMemInj.wf' sm0)
        (MS: match_stacks_inside F m m' sm0 stk stk' f' ctx sp' rs')
        (COMPAT: fenv_compat prog fenv)
        (FB: tr_funbody fenv f'.(fn_stacksize) ctx f f'.(fn_code))
        (AG: agree_regs F ctx rs rs')
        (SP: F sp = Some(sp', ctx.(dstk)))
        (MINJ: Mem.inject F m m')
        (VB: Mem.valid_block m' sp')
        (PRIV: range_private F m m' sp' (ctx.(dstk) + ctx.(mstk)) f'.(fn_stacksize))
        (SSZ1: 0 <= f'.(fn_stacksize) < Ptrofs.max_unsigned)
        (SSZ2: forall ofs, Mem.perm m' sp' ofs Max Nonempty -> 0 <= ofs <= f'.(fn_stacksize)),
      match_states (State stk f (Vptr sp Ptrofs.zero) pc rs m)
                   (State stk' f' (Vptr sp' Ptrofs.zero) (spc ctx pc) rs' m') sm0
  | match_call_states: forall stk fptr sg tfptr args m stk' args' m' F
        sm0 (MCOMPAT: SimMemInj.mcompat sm0 m m' F)
        (MWF: SimMemInj.wf' sm0)
        (MS: match_stacks F m m' sm0 stk stk' (Mem.nextblock m'))
        (FPTR: Val.inject F fptr tfptr)
        (VINJ: Val.inject_list F args args')
        (MINJ: Mem.inject F m m'),
      match_states (Callstate stk fptr sg args m)
                   (Callstate stk' tfptr sg args' m') sm0
  | match_call_regular_states: forall stk fptr sg f vargs m stk' f' sp' rs' m' F fenv ctx ctx' pc' pc1' rargs
        sm0 (MCOMPAT: SimMemInj.mcompat sm0 m m' F)
        (MWF: SimMemInj.wf' sm0)
        (MS: match_stacks_inside F m m' sm0 stk stk' f' ctx sp' rs')
        (FPTR: Genv.find_funct ge fptr = Some (Internal f))
        (COMPAT: fenv_compat prog fenv)
        (FB: tr_funbody fenv f'.(fn_stacksize) ctx f f'.(fn_code))
        (BELOW: context_below ctx' ctx)
        (NOP: f'.(fn_code)!pc' = Some(Inop pc1'))
        (MOVES: tr_moves f'.(fn_code) pc1' (sregs ctx' rargs) (sregs ctx f.(fn_params)) (spc ctx f.(fn_entrypoint)))
        (VINJ: list_forall2 (val_reg_charact F ctx' rs') vargs rargs)
        (MINJ: Mem.inject F m m')
        (VB: Mem.valid_block m' sp')
        (PRIV: range_private F m m' sp' ctx.(dstk) f'.(fn_stacksize))
        (SSZ1: 0 <= f'.(fn_stacksize) < Ptrofs.max_unsigned)
        (SSZ2: forall ofs, Mem.perm m' sp' ofs Max Nonempty -> 0 <= ofs <= f'.(fn_stacksize)),
      match_states (Callstate stk fptr sg vargs m)
                   (State stk' f' (Vptr sp' Ptrofs.zero) pc' rs' m') sm0
  | match_return_states: forall stk v m stk' v' m' F
        sm0 (MCOMPAT: SimMemInj.mcompat sm0 m m' F)
        (MWF: SimMemInj.wf' sm0)
        (MS: match_stacks F m m' sm0 stk stk' (Mem.nextblock m'))
        (VINJ: Val.inject F v v')
        (MINJ: Mem.inject F m m'),
      match_states (Returnstate stk v m)
                   (Returnstate stk' v' m') sm0
  | match_return_regular_states: forall stk v m stk' f' sp' rs' m' F ctx pc' or rinfo
        sm0 (MCOMPAT: SimMemInj.mcompat sm0 m m' F)
        (MWF: SimMemInj.wf' sm0)
        (MS: match_stacks_inside F m m' sm0 stk stk' f' ctx sp' rs')
        (RET: ctx.(retinfo) = Some rinfo)
        (AT: f'.(fn_code)!pc' = Some(inline_return ctx or rinfo))
        (VINJ: match or with None => v = Vundef | Some r => Val.inject F v rs'#(sreg ctx r) end)
        (MINJ: Mem.inject F m m')
        (VB: Mem.valid_block m' sp')
        (PRIV: range_private F m m' sp' ctx.(dstk) f'.(fn_stacksize))
        (SSZ1: 0 <= f'.(fn_stacksize) < Ptrofs.max_unsigned)
        (SSZ2: forall ofs, Mem.perm m' sp' ofs Max Nonempty -> 0 <= ofs <= f'.(fn_stacksize)),
      match_states (Returnstate stk v m)
                   (State stk' f' (Vptr sp' Ptrofs.zero) pc' rs' m') sm0.

(** ** Forward simulation *)

Definition measure (S: RTL.state) : nat :=
  match S with
  | State _ _ _ _ _ _ => 1%nat
  | Callstate _ _ _ _ _ => 0%nat
  | Returnstate _ _ _ => 0%nat
  end.

Lemma tr_funbody_inv:
  forall fenv sz cts f c pc i,
  tr_funbody fenv sz cts f c -> f.(fn_code)!pc = Some i -> tr_instr fenv sz cts pc i c.
Proof.
  intros. inv H. eauto.
Qed.

Theorem step_simulation:
  forall S1 t S2,
  step se ge S1 t S2 ->
  forall S1' sm0 (MS: match_states S1 S1' sm0),
  (exists S2', plus step tse tge S1' t S2' /\ exists sm1, match_states S2 S2' sm1 /\ <<MLE: SimMemInj.le' sm0 sm1>>)
  \/ (measure S2 < measure S1 /\ t = E0 /\ exists sm1, match_states S2 S1' sm1 /\ <<MLE: SimMemInj.le' sm0 sm1>>)%nat.
Proof.
  induction 1; intros; inv MS.

- (* nop *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  left; econstructor; split.
  eapply plus_one. eapply exec_Inop; eauto.
  SimMemInj.spl. econstructor; eauto.

- (* op *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  exploit eval_operation_inject.
    eapply match_stacks_inside_globals; eauto.
    eexact SP.
    instantiate (2 := rs##args). instantiate (1 := rs'##(sregs ctx args)). eapply agree_val_regs; eauto.
    eexact MINJ. eauto.
  fold (sop ctx op). intros [v' [A B]].
  left; econstructor; split.
  eapply plus_one. eapply exec_Iop; eauto. erewrite eval_operation_preserved; eauto.
  exact symbols_preserved.
  SimMemInj.spl. econstructor; eauto.
  apply match_stacks_inside_set_reg; auto.
  apply agree_set_reg; auto.

- (* load *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  exploit eval_addressing_inject.
    eapply match_stacks_inside_globals; eauto.
    eexact SP.
    instantiate (2 := rs##args). instantiate (1 := rs'##(sregs ctx args)). eapply agree_val_regs; eauto.
    eauto.
  fold (saddr ctx addr). intros [a' [P Q]].
  exploit Mem.loadv_inject; eauto. intros [v' [U V]].
  assert (eval_addressing tge (Vptr sp' Ptrofs.zero) (saddr ctx addr) rs' ## (sregs ctx args) = Some a').
  rewrite <- P. apply eval_addressing_preserved. exact symbols_preserved.
  left; econstructor; split.
  eapply plus_one. eapply exec_Iload; eauto.
  SimMemInj.spl. econstructor; eauto.
  apply match_stacks_inside_set_reg; auto.
  apply agree_set_reg; auto.

- (* store *)
  inv MCOMPAT. exploit tr_funbody_inv; eauto. intros TR; inv TR.
  exploit eval_addressing_inject.
    eapply match_stacks_inside_globals; eauto.
    eexact SP.
    instantiate (2 := rs##args). instantiate (1 := rs'##(sregs ctx args)). eapply agree_val_regs; eauto.
    eauto.
  fold saddr. intros [a' [P Q]].
  exploit SimMemInj.storev_mapped; eauto. eapply agree_val_reg; eauto. i; des.
  exploit Mem.storev_mapped_inject; eauto. eapply agree_val_reg; eauto.
  intros [m1' [U V]].
  assert (eval_addressing tge (Vptr sp' Ptrofs.zero) (saddr ctx addr) rs' ## (sregs ctx args) = Some a').
    rewrite <- P. apply eval_addressing_preserved. exact symbols_preserved.
  left; econstructor; split.
  eapply plus_one. eapply exec_Istore; eauto.
  destruct a; simpl in H1; try discriminate.
  destruct a'; simpl in U; try discriminate.
  exists sm1; esplits; eauto.
  econstructor; eauto.
  { SimMemInj.compat_tac. }
  eapply match_stacks_inside_store; eauto.
  eapply match_stacks_inside_le; eauto.
  eapply Mem.store_valid_block_1; eauto.
  eapply range_private_invariant; eauto.
  intros; split; auto. eapply Mem.perm_store_2; eauto.
  intros; eapply Mem.perm_store_1; eauto.
  intros. eapply SSZ2. eapply Mem.perm_store_2; eauto.

- (* call *)
  clear H1.
  exploit match_stacks_inside_globalenvs; eauto. intros [bound G].
  exploit find_function_ptr_agree; eauto. intros (tfptr & A & B).
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
+ (* not inlined *)
  left; econstructor; split.
  eapply plus_one. eapply exec_Icall; eauto. constructor.
  SimMemInj.spl. econstructor; eauto.
  eapply match_stacks_cons; eauto; try (by inv MS0; ss).
  inversion FPTR. eauto.
  eapply agree_val_regs; eauto.
+ (* inlined *)
  exploit find_inlined_function; eauto. intro FFPTR.
  right; split. simpl; lia. split. auto.
  SimMemInj.spl. inversion FPTR. econstructor; eauto.
  eapply match_stacks_inside_inlined; eauto; try (by inv MS0; ss).
  red; intros. apply PRIV. inv H13. destruct H16. extlia.
  apply agree_val_regs_gen; auto.
  red; intros; apply PRIV. destruct H16. lia.

- (* tailcall *)
  clear H1. exploit match_stacks_inside_globalenvs; eauto. intros [bound G].
  exploit find_function_ptr_agree; eauto. intros (tfptr & A & B).
  assert (PRIV': range_private F m' m'0 sp' (dstk ctx) f'.(fn_stacksize)).
  { eapply range_private_free_left; eauto. inv FB. rewrite <- H4. auto. }
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
+ (* within the original function *)
  inv MS0; try congruence.
  assert (X: { m1' | Mem.free m'0 sp' 0 (fn_stacksize f') = Some m1'}).
    apply Mem.range_perm_free. red; intros.
    destruct (zlt ofs f.(fn_stacksize)).
    replace ofs with (ofs + dstk ctx) by lia. eapply Mem.perm_inject; eauto.
    eapply Mem.free_range_perm; eauto. lia.
    inv FB. eapply range_private_perms; eauto. extlia.
  destruct X as [m1' FREE].
  left; econstructor; split.
  eapply plus_one. eapply exec_Itailcall; eauto. constructor.
  inv MCOMPAT. exploit SimMemInj.free_left; eauto. i; des.
  exploit SimMemInj.free_right; eauto.
  { rewrite MTGT. eauto. }
  { apply range_private_tgt_private; eauto. rewrite <- DSTK; ss. rpapply PRIV'; ss. }
  { ii. eapply DISJ; eauto. inv MLE. rewrite TGTPARENTEQ. eauto. }
  i; des. SimMemInj.spl_exact sm2.
  econstructor; eauto.
  { instantiate (1:= sm0.(SimMemInj.inj)). SimMemInj.compat_tac. }
  eapply match_stacks_bound with (bound := sp').
  do 2 (eapply match_stacks_le; eauto).
  eapply match_stacks_invariant; eauto.
    intros. eapply Mem.perm_free_3; eauto.
    intros. eapply Mem.perm_free_1; eauto with ordered_type.
    intros. eapply Mem.perm_free_3; eauto.
  erewrite Mem.nextblock_free; eauto. red in VB; extlia.
  inversion FPTR. eauto.
  eapply agree_val_regs; eauto.
  eapply Mem.free_right_inject; eauto. eapply Mem.free_left_inject; eauto.
  (* show that no valid location points into the stack block being freed *)
  intros. rewrite DSTK in PRIV'. exploit (PRIV' (ofs + delta)). lia. intros [P Q].
  eelim Q; eauto. replace (ofs + delta - delta) with ofs by lia.
  apply Mem.perm_max with k. apply Mem.perm_implies with p; auto with mem.
+ (* turned into a call *)
  left; econstructor; split.
  eapply plus_one. eapply exec_Icall; eauto. econstructor.
  inv MCOMPAT. exploit SimMemInj.free_left; eauto. i; des. SimMemInj.spl_exact sm1.
  econstructor; eauto.
  { instantiate (1:= sm0.(SimMemInj.inj)). SimMemInj.compat_tac. }
  eapply match_stacks_untailcall; eauto.
  eapply match_stacks_inside_le; eauto.
  eapply match_stacks_inside_invariant; eauto.
    intros. eapply Mem.perm_free_3; eauto.
    { inv MLE. inv MS0; eauto with congruence. }
  inversion FPTR. eauto.
  eapply agree_val_regs; eauto.
  eapply Mem.free_left_inject; eauto.
+ (* inlined *)
  exploit find_inlined_function; eauto. intro FFPTR.
  right; split. simpl; lia. split. auto.
  inv MCOMPAT. exploit SimMemInj.free_left; eauto. i; des. SimMemInj.spl_exact sm1.
  econstructor; eauto.
  { instantiate (1:= sm0.(SimMemInj.inj)). SimMemInj.compat_tac. }
  eapply match_stacks_inside_inlined_tailcall; eauto.
  eapply match_stacks_inside_le; eauto.
  eapply match_stacks_inside_invariant; eauto.
    intros. eapply Mem.perm_free_3; eauto.
    { inv MLE. inv MS0; eauto with congruence. }
  inversion FPTR. eauto.
  apply agree_val_regs_gen; auto.
  eapply Mem.free_left_inject; eauto.
  red; intros; apply PRIV'.
    assert (dstk ctx <= dstk ctx'). red in H14; rewrite H14. apply align_le. apply min_alignment_pos.
    lia.

- (* builtin *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  exploit match_stacks_inside_globalenvs; eauto. intros [bound MG].
  exploit match_stacks_inside_symbols_inject; eauto. intro SYMBINJ.
  exploit tr_builtin_args; eauto. intros (vargs' & P & Q).
  exploit external_call_mem_inject_gen; eauto.
  intros [F1 [v1 [m1' [A [B [C [D [E [J K]]]]]]]]].
  left; econstructor; split.
  eapply plus_one. eapply exec_Ibuiltin; eauto.
  exploit SimMemInj.external_call; try by (inv MCOMPAT; eauto). i; des. SimMemInj.spl_exact sm1.
  econstructor.
    { instantiate (1 := F1). SimMemInj.compat_tac. }
    { eauto. }
    eapply match_stacks_inside_set_res.
    eapply match_stacks_inside_extcall with (F1 := F) (F2 := F1) (m1 := m) (m1' := m'0); eauto.
    intros; eapply external_call_max_perm; eauto.
    intros; eapply external_call_max_perm; eauto.
    { eapply match_stacks_inside_le; eauto. }
  auto. eauto. auto.
  destruct res; simpl; [apply agree_set_reg;auto|idtac|idtac]; eapply agree_regs_incr; eauto.
  auto. auto.
  eapply external_call_valid_block; eauto.
  eapply range_private_extcall; eauto.
    intros; eapply external_call_max_perm; eauto.
  auto.
  intros. apply SSZ2. eapply external_call_max_perm; eauto.

- (* cond *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  assert (eval_condition cond rs'##(sregs ctx args) m' = Some b).
    eapply eval_condition_inject; eauto. eapply agree_val_regs; eauto.
  left; econstructor; split.
  eapply plus_one. eapply exec_Icond; eauto.
  SimMemInj.spl. destruct b; econstructor; eauto.

- (* jumptable *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  assert (Val.inject F rs#arg rs'#(sreg ctx arg)). eapply agree_val_reg; eauto.
  rewrite H0 in H2; inv H2.
  left; econstructor; split.
  eapply plus_one. eapply exec_Ijumptable; eauto.
  rewrite list_nth_z_map. rewrite H1. simpl; reflexivity.
  SimMemInj.spl. econstructor; eauto.

- (* return *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
+ (* not inlined *)
  assert (PRIV': range_private F m' m'0 sp' (dstk ctx) f'.(fn_stacksize)).
  { eapply range_private_free_left; eauto. inv FB. rewrite <- H4. auto. }
  inv MS0; try congruence.
  assert (X: { m1' | Mem.free m'0 sp' 0 (fn_stacksize f') = Some m1'}).
    apply Mem.range_perm_free. red; intros.
    destruct (zlt ofs f.(fn_stacksize)).
    replace ofs with (ofs + dstk ctx) by lia. eapply Mem.perm_inject; eauto.
    eapply Mem.free_range_perm; eauto. lia.
    inv FB. eapply range_private_perms; eauto.
    generalize (Zmax_spec (fn_stacksize f) 0). destruct (zlt 0 (fn_stacksize f)); lia.
  destruct X as [m1' FREE].
  left; econstructor; split.
  eapply plus_one. eapply exec_Ireturn; eauto.
  inv MCOMPAT. exploit SimMemInj.free_left; eauto. i; des. exploit SimMemInj.free_right; eauto.
  { rewrite MTGT. eauto. }
  { apply range_private_tgt_private; eauto. rewrite <- DSTK; ss. rpapply PRIV'; ss. }
  { ii. eapply DISJ; eauto. inv MLE. rewrite TGTPARENTEQ. eauto. }
  i; des. SimMemInj.spl_exact sm2. econstructor; eauto.
  { instantiate (1:= sm0.(SimMemInj.inj)). SimMemInj.compat_tac. }
  eapply match_stacks_bound with (bound := sp').
  do 2 (eapply match_stacks_le; eauto).
  eapply match_stacks_invariant; eauto.
    intros. eapply Mem.perm_free_3; eauto.
    intros. eapply Mem.perm_free_1; eauto with ordered_type.
    intros. eapply Mem.perm_free_3; eauto.
  erewrite Mem.nextblock_free; eauto. red in VB; extlia.
  destruct or; simpl. apply agree_val_reg; auto. auto.
  eapply Mem.free_right_inject; eauto. eapply Mem.free_left_inject; eauto.
  (* show that no valid location points into the stack block being freed *)
  intros. inversion FB; subst.
  rewrite DSTK in PRIV'. exploit (PRIV' (ofs + delta)). lia. intros [A B].
  eelim B; eauto. replace (ofs + delta - delta) with ofs by lia.
  apply Mem.perm_max with k. apply Mem.perm_implies with p; auto with mem.

+ (* inlined *)
  right. split. simpl. lia. split. auto.
  inv MCOMPAT. exploit SimMemInj.free_left; eauto. i; des.
  SimMemInj.spl_exact sm1. econstructor; eauto.
  { instantiate (1:= sm0.(SimMemInj.inj)). SimMemInj.compat_tac. }
  eapply match_stacks_inside_le; eauto.
  eapply match_stacks_inside_invariant; eauto.
    intros. eapply Mem.perm_free_3; eauto.
  destruct or; simpl. apply agree_val_reg; auto. auto.
  eapply Mem.free_left_inject; eauto.
  inv FB. rewrite H4 in PRIV. eapply range_private_free_left; eauto.

- (* internal function, not inlined *)
  exploit functions_injected; eauto. eapply match_stacks_globalenvs; eauto. intros (cunit & fd' & TFPTR & FD & LINK). des.
  assert (A: exists f', tr_function cunit f f' /\ fd' = Internal f').
  { Errors.monadInv FD. exists x. split; auto. eapply transf_function_spec; eauto. }
  destruct A as [f' [TR1 EQ]].
  assert (TR: tr_function prog f f').
  { eapply tr_function_linkorder; eauto. }
  inversion TR; subst.
  exploit Mem.alloc_parallel_inject. eauto. eauto. apply Z.le_refl.
    instantiate (1 := fn_stacksize f'). inv H1. extlia.
  intros [F' [m1' [sp' [A [B [C [D E]]]]]]].
  left; econstructor; split.
  eapply plus_one. eapply exec_function_internal; eauto.
  rewrite H6. exploit SimMemInj.alloc_parallel; eauto. { inv MCOMPAT; eauto. } apply Z.le_refl.
  instantiate (1 := fn_stacksize f'). inv H1. extlia.
  intro SM. desH SM. SimMemInj.spl_exact sm1.
  assert(INJEQ: F' = sm1.(SimMemInj.inj)).
  { apply Axioms.functional_extensionality. i. inv MCOMPAT. destruct (eq_block x stk); clarify; try congruence.
    rewrite E; ss. rewrite INJ0; ss. }
  econstructor; eauto. { inv MCOMPAT; ss. SimMemInj.compat_tac. }
  apply match_stacks_inside_base.
  assert (SP: sp' = Mem.nextblock m'0) by (eapply Mem.alloc_result; eauto).
  rewrite <- SP in MS0.
  eapply match_stacks_le; eauto.
  eapply match_stacks_invariant; eauto.
    intros. destruct (eq_block b1 stk).
    subst b1. rewrite D in H8; inv H8. eelim Plt_strict; eauto.
    rewrite E in H8; auto.
    intros. exploit Mem.perm_alloc_inv. eexact H. eauto.
    destruct (eq_block b1 stk); intros; auto.
    subst b1. rewrite D in H8; inv H8. eelim Plt_strict; eauto.
    intros. eapply Mem.perm_alloc_1; eauto.
    intros. exploit Mem.perm_alloc_inv. eexact A. eauto.
    rewrite dec_eq_false; auto with ordered_type.
  { inv MLE. rewrite <- TGTPARENTEQ. ii. des. clarify.
    exploit Mem.alloc_result; eauto. i; clarify.
    inv MWF. eapply TGTEXT in PR. r in PR. des.
    unfold SimMemInj.valid_blocks, Mem.valid_block in *. extlia.
  }
  { inv MWF. inv MCOMPAT. ss. clarify.
    inv MLE. rewrite <- TGTPARENTEQNB. etransitivity; eauto.
    exploit Mem.alloc_result; eauto. i; clarify. reflexivity.
  }
  auto. eauto.
  rewrite H5. apply agree_regs_init_regs. eauto. auto. inv H1; auto. congruence. auto.
  eapply Mem.valid_new_block; eauto.
  red; intros. split.
  eapply Mem.perm_alloc_2; eauto. inv H1; extlia.
  intros; red; intros. exploit Mem.perm_alloc_inv. eexact H. eauto.
  destruct (eq_block b stk); intros.
  subst. rewrite D in H9; inv H9. inv H1; extlia.
  rewrite E in H9; auto. eelim Mem.fresh_block_alloc. eexact A. eapply Mem.mi_mappedblocks; eauto.
  auto.
  intros. exploit Mem.perm_alloc_inv; eauto.
  { erewrite SimMemInj.mcompat_tgt in ALCTGT; eauto. rewrite ALCTGT in *. clarify. eauto. }
  rewrite dec_eq_true. lia.

- (* internal function, inlined *)
  assert(TMP: exists cunit fd', <<LINK: linkorder cunit prog>> /\ <<FD: transf_fundef (funenv_program cunit) (Internal f) = OK fd'>>).
  { exploit functions_translated; try apply FPTR; eauto. i; des. esplits; eauto. } desH TMP. clarify.
  inversion FB; subst.
  exploit Mem.alloc_left_mapped_inject.
    eauto.
    eauto.
    (* sp' is valid *)
    instantiate (1 := sp'). auto.
    (* offset is representable *)
    instantiate (1 := dstk ctx). generalize (Z.le_max_r (fn_stacksize f) 0). lia.
    (* size of target block is representable *)
    intros. right. exploit SSZ2; eauto with mem. inv FB; lia.
    (* we have full permissions on sp' at and above dstk ctx *)
    intros. apply Mem.perm_cur. apply Mem.perm_implies with Freeable; auto with mem.
    eapply range_private_perms; eauto. extlia.
    (* offset is aligned *)
    replace (fn_stacksize f - 0) with (fn_stacksize f) by lia.
    inv FB. apply min_alignment_sound; auto.
    (* nobody maps to (sp, dstk ctx...) *)
    intros. exploit (PRIV (ofs + delta')); eauto. extlia.
    intros [A B]. eelim B; eauto.
    replace (ofs + delta' - delta') with ofs by lia.
    apply Mem.perm_max with k. apply Mem.perm_implies with p; auto with mem.
  intros [F' [A [B [C D]]]].
  exploit tr_moves_init_regs; eauto. intros [rs'' [P [Q R]]].
  left; econstructor; split.
  eapply plus_left. eapply exec_Inop; eauto. eexact P. traceEq.
  assert(MLE: SimMemInj.le' sm0
              (SimMemInj.mk m' m'0 F' sm0.(SimMemInj.src_external) sm0.(SimMemInj.tgt_external)
                            sm0.(SimMemInj.src_parent_nb) sm0.(SimMemInj.tgt_parent_nb) sm0.(SimMemInj.src_ge_nb) sm0.(SimMemInj.tgt_ge_nb))).
  {
    inv MCOMPAT.
    assert(FROZEN: SimMemInj.frozen (SimMemInj.inj sm0) F' (SimMemInj.src_parent_nb sm0) (SimMemInj.tgt_parent_nb sm0)).
    { - econs; ss; eauto. ii. des.
      assert(b_src = stk).
      { apply Classical_Prop.NNPP. ii. rewrite D in NEW0; ss. clarify. }
      clarify. esplits.
      + inv MWF. exploit Mem.alloc_result; eauto. i; clarify.
      + inv MS0; ss. }
    econs; ss; eauto.
    - eapply Mem.alloc_unchanged_on; eauto.
    - eapply Mem.unchanged_on_refl.
    - eapply SimMemInj.frozen_shortened; eauto; try apply MWF.
    - ii. eapply Mem.perm_alloc_4; eauto. ii. subst. eapply Mem.fresh_block_alloc; eauto.
  }
  SimMemInj.spl_approx sm0. econstructor.
  { SimMemInj.compat_tac. }
  { inv MCOMPAT.
    inv MWF. econs; ss; eauto.
    - etransitivity; eauto. unfold SimMemInj.src_private. ss. ii; des. esplits; eauto.
      { red in PR. red. rewrite D; eauto. ii; clarify. red in PR0. eapply Mem.fresh_block_alloc; eauto. }
      { unfold SimMemInj.valid_blocks in *. clear - H PR0. eauto with mem. }
    - unfold SimMemInj.tgt_private. ss. ii; des. esplits; eauto.
      + ii. assert (b0 <> stk).
        { ii. clarify; inv MS0; eapply DISJ; eauto. }
        rr in TGTEXT. specialize (TGTEXT x0 x1 PR). des.
        exploit TGTEXT; eauto; [erewrite <-D|]; eauto with mem.
      + apply TGTEXT in PR. red in PR. des. ss.
    - etransitivity; eauto. exploit Mem.nextblock_alloc; eauto. intro NB. rewrite NB. extlia.
  }
  eapply match_stacks_inside_alloc_left; try apply MS0; eauto.
  eapply match_stacks_inside_le; eauto.
  eapply match_stacks_inside_invariant; eauto.
  lia.
  eauto. auto.
  apply agree_regs_incr with F; auto.
  auto. auto. auto.
  rewrite H2. eapply range_private_alloc_left; eauto.
  auto. auto.

- (* external function *)
  exploit functions_injected; eauto. eapply match_stacks_globalenvs; eauto. intros (cunit & fd' & TFPTR & FD & LINK). des.
  exploit match_stacks_globalenvs; eauto. intros [bound MG].
  exploit match_stacks_symbols_inject; eauto. intro SYMBINJ.
  exploit external_call_mem_inject_gen; eauto.
  intros [F1 [v1 [m1' [A [B [C [D [E [J K]]]]]]]]].
  simpl in FD. inv FD.
  left; econstructor; split.
  eapply plus_one. eapply exec_function_external; eauto.
  exploit SimMemInj.external_call; try by (inv MCOMPAT; eauto). i; des. SimMemInj.spl_exact sm1.
  econstructor.
    { instantiate (1 := F1). SimMemInj.compat_tac. }
    { eauto. }
    eapply match_stacks_bound with (Mem.nextblock m'0).
    eapply match_stacks_extcall with (F1 := F) (F2 := F1) (m1 := m) (m1' := m'0); eauto.
    intros; eapply external_call_max_perm; eauto.
    intros; eapply external_call_max_perm; eauto.
    { eapply match_stacks_le; eauto. }
    extlia.
    eapply external_call_nextblock; eauto.
    auto. auto.
- clarify.

- (* return from noninlined function *)
  inv MS0.
+ (* normal case *)
  left; econstructor; split.
  eapply plus_one. eapply exec_return.
  SimMemInj.spl. econstructor; eauto.
  apply match_stacks_inside_set_reg; auto.
  apply agree_set_reg; auto.
+ (* untailcall case *)
  inv MS; try congruence.
  rewrite RET in RET0; inv RET0.
  left; econstructor; split.
  eapply plus_one. eapply exec_return.
  SimMemInj.spl. eapply match_regular_states. eauto. auto.
  eapply match_stacks_inside_set_reg; eauto.
  eauto. auto.
  apply agree_set_reg; auto.
  auto. auto. auto.
  red; intros. destruct (zlt ofs (dstk ctx)). apply PAD; lia. apply PRIV; lia.
  auto. auto.

- (* return from inlined function *)
  inv MS0; try congruence. rewrite RET0 in RET; inv RET.
  unfold inline_return in AT.
  assert (PRIV': range_private F m m' sp' (dstk ctx' + mstk ctx') f'.(fn_stacksize)).
    red; intros. destruct (zlt ofs (dstk ctx)). apply PAD. lia. apply PRIV. lia.
  destruct or.
+ (* with a result *)
  left; econstructor; split.
  eapply plus_one. eapply exec_Iop; eauto. simpl. reflexivity.
  SimMemInj.spl. econstructor; eauto. apply match_stacks_inside_set_reg; auto. apply agree_set_reg; auto.
+ (* without a result *)
  left; econstructor; split.
  eapply plus_one. eapply exec_Inop; eauto.
  SimMemInj.spl. econstructor; eauto. subst vres. apply agree_set_reg_undef'; auto.
Unshelve.
  all: by (try eapply SimMemInj.inject_separated_frozen; eauto).
Qed.

End CORELEMMA.

Section WHOLE.

Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Let MATCH_GENV: Genv.match_genvs (match_globdef (fun cunit f tf => transf_fundef (funenv_program cunit) f = OK tf) eq prog) ge tge.
Proof. apply Genv.globalenvs_match; auto. Qed.

Let GENV_COMPAT: genv_compat ge prog.
Proof. apply genv_compat_match. Qed.

Let match_states := match_states ge tge.
Lemma transf_initial_states:
  forall st1, initial_state prog st1 -> exists st2, initial_state tprog st2 /\ exists sm, match_states ge st1 st2 sm.
Proof.
  intros. inv H.
  eexists (Callstate nil _ _ nil m0); split.
  econstructor; eauto.
    eapply (Genv.init_mem_match TRANSF); eauto.
    erewrite symbols_preserved; eauto. replace (prog_main tprog) with (prog_main prog). eauto.
    symmetry; eapply match_program_main; eauto.
  exists (SimMemInj.mk m0 m0 (Mem.flat_inj (Mem.nextblock m0)) bot2 bot2 1%positive 1%positive 1%positive 1%positive).
  econstructor; eauto.
  { SimMemInj.compat_tac. }
  { econs; ss; eauto; try extlia. eapply Genv.initmem_inject; eauto. }
  all: s.
  apply match_stacks_nil with (Mem.nextblock m0).
  { erewrite <- Genv.init_mem_genv_next; eauto. eapply (init_symbols_inject MATCH_GENV). }
  { erewrite <- Genv.init_mem_genv_next; eauto. unfold ge. ss. }
  constructor; intros.
    unfold Mem.flat_inj. apply pred_dec_true; auto.
    unfold Mem.flat_inj in H. destruct (plt b1 (Mem.nextblock m0)); congruence.
    eapply Genv.find_symbol_not_fresh; eauto.
    eapply Genv.find_funct_ptr_not_fresh; eauto.
    eapply Genv.find_var_info_not_fresh; eauto.
    apply Ple_refl.
    { unfold Mem.flat_inj. exploit Genv.find_symbol_not_fresh; eauto. intro P. econs; ss; des_ifs. rewrite Ptrofs.add_zero_l. ss. }
  eapply Genv.initmem_inject; eauto.
Qed.

Lemma transf_final_states:
  forall st1 st2 r,
  (exists sm, match_states ge st1 st2 sm) -> final_state st1 r -> final_state st2 r.
Proof.
  intros. des. inv H0. inv H.
  exploit match_stacks_empty; eauto. intros EQ; subst. inv VINJ. constructor.
  exploit match_stacks_inside_empty; eauto. intros [A B]. congruence.
Qed.

Theorem transf_program_correct:
  forward_simulation (semantics prog) (semantics tprog).
Proof.
  eapply forward_simulation_star with (match_states := fun s1 s2 => exists sm, match_states ge s1 s2 sm).
  apply senv_preserved; auto.
  eexact transf_initial_states.
  eexact transf_final_states.
  { i. des. exploit step_simulation; eauto. i; des; eauto. }
Qed.

End WHOLE.

End INLINING.
