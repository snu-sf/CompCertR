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
      
Set Implicit Arguments.



Section MEMINJINV.

  Definition memblk_invariant := (memory_chunk -> Z -> option val) -> Prop.

  Variable P : memblk_invariant.

  Record t' :=
    mk
      { src : mem;
        tgt : mem;
        inj : meminj;
        mem_inv: block -> Prop;
      }.

  Definition inv_sat_blk blk (invar: memblk_invariant) (m: mem): Prop :=
    invar (fun chunk ofs =>
             if (Mem.valid_access_dec m chunk blk ofs Writable)
             then Mem.load chunk m blk ofs
             else None).

  (* Definition inv_sat_mem (invar: memory_invariant) (m: mem) : Prop := *)
  (*   forall blk inv_blk (INVAR: invar blk inv_blk), inv_sat_blk blk inv_blk m.   *)

  Definition inv_sat_mem (invar: block -> Prop) (m: mem) : Prop :=
    forall blk (INVAR: invar blk), inv_sat_blk blk P m.

  Inductive wf' (sm0: t'): Prop :=
  | wf_intro
      (WF: Mem.inject sm0.(inj) sm0.(src) sm0.(tgt))
      (SAT: inv_sat_mem sm0.(mem_inv) sm0.(tgt))
      (INVRANGE: forall blk ofs (INV: sm0.(mem_inv) blk),
          loc_out_of_reach sm0.(inj) sm0.(src) blk ofs /\ Mem.valid_block sm0.(tgt) blk)
      (* (INVRANGE: forall blk ofs invar (INV: sm0.(mem_inv) blk invar),         *)
      (*     loc_out_of_reach sm0.(inj) sm0.(src) blk ofs /\ Mem.valid_block sm0.(tgt) blk) *)
  .

  Lemma unchanged_on_invariant invar m0 m1
        (INVAR: inv_sat_mem invar m0)
        (INVRANGE: invar <1= Mem.valid_block m0)
        (UNCH: Mem.unchanged_on (fun blk _ => invar blk) m0 m1)
    :
      inv_sat_mem invar m1.
  Proof.
    ii. exploit INVAR; eauto. intros SAT.
    unfold inv_sat_blk in *. rpapply SAT.
    extensionality chunk. extensionality ofs.
    des_ifs.
    - eapply Mem.load_unchanged_on_1; eauto.
    - exfalso. apply n. inv v. split; auto.
      ii. eapply Mem.perm_unchanged_on_2; eauto.
    - exfalso. apply n. inv v. split; auto.
      ii. eapply Mem.perm_unchanged_on; eauto.
  Qed.

  Inductive le' (mrel0 mrel1: t'): Prop :=
  | le_intro
      (SRCNBLE: Ple mrel0.(src).(Mem.nextblock) mrel1.(src).(Mem.nextblock))
      (TGTNBLE: Ple mrel0.(tgt).(Mem.nextblock) mrel1.(tgt).(Mem.nextblock))
      (INCR: inject_incr mrel0.(inj) mrel1.(inj))
      (FROZEN: inject_separated
                 (mrel0.(inj)) (mrel1.(inj))
                 (mrel0.(src)) (mrel0.(tgt)))
      (MINVEQ: mrel0.(mem_inv) = mrel1.(mem_inv))
      (MAXSRC: forall
          b ofs
          (VALID: Mem.valid_block mrel0.(src) b)
        ,
          <<MAX: Mem.perm mrel1.(src) b ofs Max <1= Mem.perm mrel0.(src) b ofs Max>>)
      (MAXTGT: forall
          b ofs
          (VALID: Mem.valid_block mrel0.(tgt) b)
        ,
          <<MAX: Mem.perm mrel1.(tgt) b ofs Max <1= Mem.perm mrel0.(tgt) b ofs Max>>)
  .

  Global Program Instance le'_PreOrder: RelationClasses.PreOrder le'.
  Next Obligation.
    econs; ss; eauto.
    - reflexivity.
    - reflexivity.
    - ii. clarify.
  Qed.
  Next Obligation.
    ii. inv H. inv H0. econs; eauto.
    - etransitivity; eauto.
    - etransitivity; eauto.
    - eapply inject_incr_trans; eauto.
    - ii. destruct (inj y b1) as [[b3 delta0]|] eqn:DELTA.
      + dup DELTA. eapply INCR0 in DELTA. clarify.
        exploit FROZEN; eauto.
      + dup DELTA. exploit FROZEN0; eauto. i. des.
        unfold Mem.valid_block in *. split; ii.
        * eapply H1. eapply Plt_Ple_trans; eauto.
        * eapply H2. eapply Plt_Ple_trans; eauto.
    - etransitivity; eauto.
    - ii. eapply MAXSRC; eauto. eapply MAXSRC0; eauto.
      eapply Plt_Ple_trans; eauto.
    - ii. eapply MAXTGT; eauto. eapply MAXTGT0; eauto.
      eapply Plt_Ple_trans; eauto.
  Qed.
  
  Lemma mem_inv_le sm0 sm1
        (MLE: le' sm0 sm1)
    :
      sm0.(mem_inv) <1= sm1.(mem_inv).
  Proof.
    inv MLE. rewrite MINVEQ. auto.
  Qed.

  Lemma unchanged_on_mle sm0 m_src1 m_tgt1 j1
        (WF: wf' sm0)
        (INJECT: Mem.inject j1 m_src1 m_tgt1)
        (INCR: inject_incr sm0.(inj) j1)
        (SEP: inject_separated sm0.(inj) j1 sm0.(src) sm0.(tgt))
        (UNCHSRC: Mem.unchanged_on
                    (loc_unmapped sm0.(inj))
                    sm0.(src) m_src1)
        (UNCHTGT: Mem.unchanged_on
                    (loc_out_of_reach sm0.(inj) sm0.(src))
                    sm0.(tgt) m_tgt1)
        (MAXSRC: forall
            b ofs
            (VALID: Mem.valid_block sm0.(src) b)
          ,
            <<MAX: Mem.perm m_src1 b ofs Max <1= Mem.perm sm0.(src) b ofs Max>>)
        (MAXTGT: forall
            b ofs
            (VALID: Mem.valid_block sm0.(tgt) b)
          ,
            <<MAX: Mem.perm m_tgt1 b ofs Max <1= Mem.perm sm0.(tgt) b ofs Max>>)
    :
      (<<MLE: le' sm0 (mk m_src1 m_tgt1 j1 sm0.(mem_inv))>>) /\
      (<<MWF: wf' (mk m_src1 m_tgt1 j1 sm0.(mem_inv))>>).
  Proof.               
    split.
    - econs; ss; eauto.
      + eapply Mem.unchanged_on_nextblock; eauto.
      + eapply Mem.unchanged_on_nextblock; eauto.
    - inv WF. econs; ss; eauto.
      + eapply unchanged_on_invariant; eauto.
        * ii. eapply INVRANGE; eauto. apply 0.
        * eapply Mem.unchanged_on_implies; eauto.
          i. eapply INVRANGE; eauto.
      + i. exploit INVRANGE; eauto. i. des. split.
        * ii. destruct (inj sm0 b0) as [[blk0 delta0]|] eqn:DELTA.
          { dup DELTA. apply INCR in DELTA. clarify.
            eapply INVRANGE; eauto. eapply MAXSRC; eauto.
            eapply Mem.valid_block_inject_1; eauto. }
          { exploit SEP; eauto. i. des. clarify. }
        * eapply Plt_Ple_trans; eauto.
          eapply Mem.unchanged_on_nextblock; eauto.

          Unshelve. apply 0.
  Qed.          
  
End MEMINJINV.

Record mcompat (sm0: t') (m_src0 m_tgt0: mem) (F: meminj): Prop := mkmcompat {
  mcompat_src: sm0.(src) = m_src0;
  mcompat_tgt: sm0.(tgt) = m_tgt0;
  mcompat_inj: sm0.(inj) = F;
}.

Ltac compat_tac := ss; econs; eauto; try congruence.
Ltac spl := esplits; [|reflexivity].
Ltac spl_approx sm :=
  eexists (mk _ _ _ sm.(mem_inv)); splits; eauto.
Ltac spl_exact sm :=
  exists sm; splits; [|try etransitivity; eauto; try reflexivity; eauto].