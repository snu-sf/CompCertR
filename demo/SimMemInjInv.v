Require Import Coqlib.
Require Import Memory.
Require Import Values.
Require Import Maps.
Require Import Events.
Require Import Globalenvs.
Require Import AST.
Require Import sflib.

Require Import Integers Linking.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ClassicalChoice.
Require Import Coq.Logic.ChoiceFacts.
Require Import SimMemInj.

Set Implicit Arguments.




Record memblk_invariant :=
  memblk_invarant_mk
    {
      load_values: (memory_chunk -> Z -> option val) -> Prop;
      permissions: memory_chunk -> Z -> permission -> Prop;
    }.

Section MEMINJINV.

Variable P_src : memblk_invariant.
Variable P_tgt : memblk_invariant.

Record t' :=
  mk
    { minj :> SimMemInj.t';
      mem_inv_src: block -> Prop;
      mem_inv_tgt: block -> Prop;
    }.

Inductive inv_sat_blk (P: memblk_invariant) blk (m: mem): Prop :=
| inv_sat_blk_intro
    (PERMISSIONS:
       forall chunk ofs p (INVAR: P.(permissions) chunk ofs p),
         Mem.valid_access m chunk blk ofs p)
    (LOADVALS: P.(load_values) (fun chunk => Mem.load chunk m blk))
.

(* Definition inv_sat_mem (invar: memory_invariant) (m: mem) : Prop := *)
(*   forall blk inv_blk (INVAR: invar blk inv_blk), inv_sat_blk blk inv_blk m.   *)

Definition inv_sat_mem (P: memblk_invariant) (invar: block -> Prop) (m: mem) : Prop :=
  forall blk (INVAR: invar blk), inv_sat_blk P blk m.

Inductive wf' (sm0: t'): Prop :=
| wf_intro
    (WF: SimMemInj.wf' sm0)
    (SATSRC: inv_sat_mem P_src sm0.(mem_inv_src) sm0.(src))
    (SATTGT: inv_sat_mem P_tgt sm0.(mem_inv_tgt) sm0.(tgt))
    (* (TGTINV: forall blk ofs (EXT: sm0.(tgt_external) blk ofs), ~ sm0.(mem_inv) blk) *)
    (INVRANGESRC: forall blk ofs (INV: sm0.(mem_inv_src) blk),
        loc_unmapped (inj sm0) blk ofs /\ ~ sm0.(src_external) blk ofs /\
        Plt blk sm0.(src_parent_nb))
    (INVRANGETGT: forall blk ofs (INV: sm0.(mem_inv_tgt) blk),
        loc_out_of_reach (inj sm0) (src sm0) blk ofs /\ ~ sm0.(tgt_external) blk ofs /\
        Plt blk sm0.(tgt_parent_nb))
.

(* Inductive wf' (sm0: t'): Prop := *)
(* | wf_intro *)
(*     (WF: SimMemInj.wf' sm0) *)
(*     (SATSRC: inv_sat_mem P_src sm0.(mem_inv_src) sm0.(src)) *)
(*     (SATTGT: inv_sat_mem P_tgt sm0.(mem_inv_tgt) sm0.(tgt)) *)
(*     (* (TGTINV: forall blk ofs (EXT: sm0.(tgt_external) blk ofs), ~ sm0.(mem_inv) blk) *) *)
(*     (INVRANGESRC: forall blk ofs (INV: sm0.(mem_inv_src) blk), *)
(*         SimMemInj.src_private sm0 blk ofs /\ ~ sm0.(src_external) blk ofs /\ *)
(*         Plt blk sm0.(src_parent_nb)) *)
(*     (INVRANGETGT: forall blk ofs (INV: sm0.(mem_inv_tgt) blk), *)
(*         SimMemInj.tgt_private sm0 blk ofs /\ ~ sm0.(tgt_external) blk ofs /\ *)
(*         Plt blk sm0.(tgt_parent_nb)) *)
(* . *)

Lemma private_unchanged_on_invariant P invar m0 m1
      (INVAR: inv_sat_mem P invar m0)
      (INVRANGE: invar <1= Mem.valid_block m0)
      (UNCH: Mem.unchanged_on (fun blk _ => invar blk) m0 m1)
  :
    inv_sat_mem P invar m1.
Proof.
  ii. exploit INVAR; eauto. intros SAT.
  inv SAT. econs.
  - ii. exploit PERMISSIONS; eauto. i.
    unfold Mem.valid_access in *. des. split; auto.
    ii. eapply Mem.perm_unchanged_on; eauto.
  - rpapply LOADVALS. extensionality chunk. extensionality ofs.
    eapply Mem.load_unchanged_on_1; eauto.
Qed.

Inductive le' (mrel0 mrel1: t'): Prop :=
| le_intro
    (MLE: SimMemInj.le' mrel0 mrel1)
    (MINVEQSRC: mrel0.(mem_inv_src) = mrel1.(mem_inv_src))
    (MINVEQTGT: mrel0.(mem_inv_tgt) = mrel1.(mem_inv_tgt))
.

Global Program Instance le'_PreOrder: RelationClasses.PreOrder le'.
Next Obligation.
  econs; ss; eauto. reflexivity.
Qed.
Next Obligation.
  ii. inv H. inv H0. econs; eauto.
  - etransitivity; eauto.
  - etransitivity; eauto.
  - etransitivity; eauto.
Qed.

Lemma le_inj_wf_wf minj_old minj_new inv_src inv_tgt
      (MLE: SimMemInj.le' minj_old minj_new)
      (WF: wf' (mk minj_old inv_src inv_tgt))
      (MWF: SimMemInj.wf' minj_new)
      (SATSRC: inv_sat_mem P_src inv_src minj_new.(src))
      (SATTGT: inv_sat_mem P_tgt inv_tgt minj_new.(tgt))
  :
    wf' (mk minj_new inv_src inv_tgt)
.
Proof.
  inv WF. inv WF0. econs; ss; eauto.
  - ii. inv MLE. exploit INVRANGESRC; eauto.
    rewrite SRCPARENTEQ. rewrite SRCPARENTEQNB in *. i. des. splits; eauto.
    destruct (inj minj_new blk) eqn:BLK; auto.
    destruct p. inv FROZEN. exploit NEW_IMPLIES_OUTSIDE; eauto.
    i. des. exfalso. eapply (Plt_strict blk).
    eapply Plt_Ple_trans; eauto.
  - ii. inv MLE. exploit INVRANGETGT; eauto.
    rewrite TGTPARENTEQ. rewrite TGTPARENTEQNB in *. i. des. splits; eauto.
    ii. destruct (inj minj_old b0) eqn:BLK; auto.
    + destruct p. dup BLK. eapply INCR in BLK. clarify.
      exploit H; eauto. eapply MAXSRC; eauto.
      eapply Mem.valid_block_inject_1; eauto.
    + inv FROZEN. exploit NEW_IMPLIES_OUTSIDE; eauto.
      i. des. eapply (Plt_strict blk); eauto.
      eapply Plt_Ple_trans; eauto.
Qed.

End MEMINJINV.

Definition top_inv: memblk_invariant := memblk_invarant_mk
                                          (fun _ => True) (fun _ _ _ => False).

Lemma top_inv_satisfied_always m minv
  :
    inv_sat_mem top_inv minv m.
Proof. econs; ss. Qed.
Hint Resolve top_inv_satisfied_always.

Record mcompat (sm0: t') (m_src0 m_tgt0: mem) (F: meminj): Prop := mkmcompat {
  mcompat_src: sm0.(src) = m_src0;
  mcompat_tgt: sm0.(tgt) = m_tgt0;
  mcompat_inj: sm0.(inj) = F;
}.

Ltac compat_tac := ss; econs; eauto; try congruence.
Ltac spl := esplits; [|reflexivity].
Ltac spl_approx sm :=
  eexists (mk (SimMemInj.mk _ _ _ sm.(src_external) sm.(tgt_external) sm.(src_parent_nb) sm.(tgt_parent_nb)) sm.(mem_inv_src) sm.(mem_inv_tgt)); splits; eauto.
Ltac spl_approx2 sm :=
  eexists (mk _ sm.(mem_inv_src) sm.(mem_inv_tgt)); splits; eauto.
Ltac spl_exact sm :=
  exists sm; splits; [|try etransitivity; eauto; try reflexivity; eauto].
Ltac spl_exact2 sm :=
  eexists (mk sm _ _); splits; [|try etransitivity; eauto; try reflexivity; eauto].
