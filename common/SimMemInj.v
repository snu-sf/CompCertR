Require Import Coqlib.
Require Import Memory.
Require Import Values.
Require Import Maps.
Require Import Events.
Require Import Globalenvs.
Require Import AST.
Require Import sflib.
Require Import RelationClasses.
From Paco Require Import paco.

Require Import Integers Linking.

Set Implicit Arguments.

Hint Extern 998 => xomega : xomega.
Hint Extern 999 => congruence : congruence.

Definition less1 X0 (p q: X0 -> Prop) := (forall x0 (PR: p x0 : Prop), q x0 : Prop).
Definition less2 X0 X1 (p q: X0 -> X1 -> Prop) := (forall x0 x1 (PR: p x0 x1 : Prop), q x0 x1 : Prop).
Definition less3 X0 X1 X2 (p q: X0 -> X1 -> X2 -> Prop) := (forall x0 x1 x2 (PR: p x0 x1 x2 : Prop), q x0 x1 x2 : Prop).
Definition less4 X0 X1 X2 X3 (p q: X0 -> X1 -> X2 -> X3 -> Prop) := (forall x0 x1 x2 x3 (PR: p x0 x1 x2 x3 : Prop), q x0 x1 x2 x3 : Prop).

Notation "p <1= q" := (less1 p q) (at level 50).
Notation "p <2= q" := (less2 p q) (at level 50).
Notation "p <3= q" := (less3 p q) (at level 50).
Notation "p <4= q" := (less4 p q) (at level 50).

Global Program Instance less1_PreOrder X0: PreOrder (@less1 X0).
Next Obligation. ii. ss. Qed.
Next Obligation. ii. eapply H0; eauto. Qed.
Global Program Instance less2_PreOrder X0 X1: PreOrder (@less2 X0 X1).
Next Obligation. ii. ss. Qed.
Next Obligation. ii. eapply H0; eauto. Qed.
Global Program Instance less3_PreOrder X0 X1 X2: PreOrder (@less3 X0 X1 X2).
Next Obligation. ii. ss. Qed.
Next Obligation. ii. eapply H0; eauto. Qed.
Global Program Instance less4_PreOrder X0 X1 X2 X3 : PreOrder (@less4 X0 X1 X2 X3).
Next Obligation. ii. ss. Qed.
Next Obligation. ii. eapply H0; eauto. Qed.
Hint Unfold less1 less2 less3 less4.


(* Copied from CRELLVM *)
Inductive frozen (f_old f_new: meminj) (bound_src bound_tgt: block): Prop :=
| frozen_intro
    (NEW_IMPLIES_OUTSIDE:
       forall b_src b_tgt delta
              (NEW: f_old b_src = None /\ f_new b_src = Some(b_tgt, delta)),
         <<OUTSIDE_SRC: (bound_src <= b_src)%positive>> /\ <<OUTSIDE_TGT: (bound_tgt <= b_tgt)%positive>>)
.

Remark inject_separated_frozen
       f_old f_new m_src m_tgt
  :
    Events.inject_separated f_old f_new m_src m_tgt <->
    frozen f_old f_new m_src.(Mem.nextblock) m_tgt.(Mem.nextblock)
.
Proof.
  unfold Events.inject_separated in *.
  unfold Mem.valid_block in *.
  split; i.
  - econs; eauto.
    i. des.
    hexploit H; eauto. i; des.
    splits; xomega.
  - inv H.
    exploit NEW_IMPLIES_OUTSIDE; eauto.
    i; des.
    split; xomega.
Qed.

Lemma frozen_preserves_src
      f_old f_new
      (INJECT: inject_incr f_old f_new)
      bound_src bound_tgt
      (FROZEN: frozen f_old f_new bound_src bound_tgt)
      b_src
      (INSIDE: (b_src < bound_src)%positive)
  :
    <<PRESERVED: f_old b_src = f_new b_src>>
.
Proof.
  inv FROZEN.
  destruct (f_old b_src) eqn:T0; ss;
    destruct (f_new b_src) eqn:T1; ss.
  - destruct p, p0; ss.
    exploit INJECT; eauto; []; i; des.
    clarify.
  - destruct p; ss.
    exploit INJECT; eauto; []; i; des.
    clarify.
  - destruct p; ss.
    exploit NEW_IMPLIES_OUTSIDE; eauto; []; i; des.
    exfalso.
    xomega.
Qed.

Lemma frozen_preserves_tgt
      f_old f_new
      (INJECT: inject_incr f_old f_new)
      bound_src bound_tgt
      (FROZEN: frozen f_old f_new bound_src bound_tgt)
      b_tgt
      (INSIDE: (b_tgt < bound_tgt)%positive)
  :
    <<PRESERVED: forall b_src delta (NOW: f_new b_src = Some (b_tgt, delta)),
      <<OLD: f_old b_src = Some (b_tgt, delta)>> >>
.
Proof.
  inv FROZEN.
  ii.
  destruct (f_old b_src) eqn:T; ss.
  - destruct p; ss.
    exploit INJECT; eauto; []; i; des.
    clarify.
  - exfalso.
    exploit NEW_IMPLIES_OUTSIDE; eauto; []; i; des.
    xomega.
Qed.

Lemma frozen_shortened
      f_old f_new
      bd_src0 bd_tgt0
      (FROZEN: frozen f_old f_new bd_src0 bd_tgt0)
      bd_src1 bd_tgt1
      (SHORT_SRC: (bd_src1 <= bd_src0)%positive)
      (SHORT_TGT: (bd_tgt1 <= bd_tgt0)%positive)
  :
    <<FROZEN: frozen f_old f_new bd_src1 bd_tgt1>>
.
Proof.
  inv FROZEN.
  econs; eauto.
  ii. des.
  hexploit NEW_IMPLIES_OUTSIDE; eauto; []; i; des. clear NEW_IMPLIES_OUTSIDE.
  split; ss.
  - red. etransitivity; eauto.
  - red. etransitivity; eauto.
Qed.

Lemma frozen_refl
      f
      bound_src bound_tgt
  :
    <<FROZEN: frozen f f bound_src bound_tgt>>
.
Proof.
  econs; eauto. i; des. clarify.
Qed.

Lemma loc_unmapped_frozen
      F F'
      fbound_src fbound_tgt
      (FROZEN : frozen F F' fbound_src fbound_tgt)
      b ofs
      (BOUND: Plt b fbound_src)
      (UNMAPPED: loc_unmapped F b ofs)
  :
    loc_unmapped F' b ofs
.
Proof.
  unfold loc_unmapped in *.
  destruct (F' b) eqn:T; ss.
  destruct p; ss.
  inv FROZEN.
  exploit NEW_IMPLIES_OUTSIDE; eauto.
  i; des. xomega.
Qed.

Lemma loc_out_of_reach_frozen
      F F'
      fbound_src fbound_tgt
      (INCR: inject_incr F F')
      (FROZEN : frozen F F' fbound_src fbound_tgt)
      b ofs
      (BOUND: Plt b fbound_tgt)
      m0 m1
      (UNMAPPED: loc_out_of_reach F m0 b ofs)
      (MAXPERM: forall b0 delta (MAPPED: F b0 = Some (b, delta)),
          Mem.perm m1 b0 (ofs - delta) Max Nonempty -> Mem.perm m0 b0 (ofs - delta) Max Nonempty)
  :
    loc_out_of_reach F' m1 b ofs
.
Proof.
  unfold loc_out_of_reach in *.
  i.
  exploit frozen_preserves_tgt; eauto.
  i. des.
  hexploit UNMAPPED; eauto.
Qed.


Section MEMINJ.

(* Local Existing Instance Val.mi_normal. *)
(* Variable gbound_src gbound_tgt: block. *)

Record t' := mk {
  src: mem;
  tgt: mem;
  inj: meminj;
  src_external: block -> Z -> Prop;
  tgt_external: block -> Z -> Prop;
  src_parent_nb: block;
  tgt_parent_nb: block;
}.

Definition valid_blocks (m: mem): block -> Z -> Prop := fun b _ => m.(Mem.valid_block) b.
Hint Unfold valid_blocks.

Definition src_private (sm: t'): block -> Z -> Prop :=
  loc_unmapped sm.(inj) /2\ sm.(src).(valid_blocks)
.

Definition tgt_private (sm: t'): block -> Z -> Prop :=
  loc_out_of_reach sm.(inj) sm.(src) /2\ sm.(tgt).(valid_blocks)
.

Hint Unfold src_private tgt_private.

Inductive wf' (sm0: t'): Prop :=
| wf_intro
    (PUBLIC: Mem.inject sm0.(inj) sm0.(src) sm0.(tgt))
    (SRCEXT: sm0.(src_external) <2= sm0.(src_private))
    (TGTEXT: sm0.(tgt_external) <2= sm0.(tgt_private))
    (SRCLE: (sm0.(src_parent_nb) <= sm0.(src).(Mem.nextblock))%positive)
    (TGTLE: (sm0.(tgt_parent_nb) <= sm0.(tgt).(Mem.nextblock))%positive)
.

Inductive le' (mrel0 mrel1: t'): Prop :=
| le_intro
    (INCR: inject_incr mrel0.(inj) mrel1.(inj))
    (SRCUNCHANGED: Mem.unchanged_on mrel0.(src_external) mrel0.(src) mrel1.(src))
    (TGTUNCHANGED: Mem.unchanged_on mrel0.(tgt_external) mrel0.(tgt) mrel1.(tgt))
    (SRCPARENTEQ: mrel0.(src_external) = mrel1.(src_external))
    (SRCPARENTEQNB: mrel0.(src_parent_nb) = mrel1.(src_parent_nb))
    (TGTPARENTEQ: mrel0.(tgt_external) = mrel1.(tgt_external))
    (TGTPARENTEQNB: mrel0.(tgt_parent_nb) = mrel1.(tgt_parent_nb))
    (FROZEN: frozen mrel0.(inj) mrel1.(inj) (mrel0.(src_parent_nb))
                                            (mrel0.(tgt_parent_nb)))
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
  econs; eauto; try reflexivity; try apply Mem.unchanged_on_refl; eauto.
  eapply frozen_refl; eauto.
Qed.
Next Obligation.
  ii. inv H; inv H0.
  des; clarify.
  econs; eauto with mem congruence.
  + eapply inject_incr_trans; eauto.
  + eapply Mem.unchanged_on_trans; eauto with congruence.
  + eapply Mem.unchanged_on_trans; eauto with congruence.
  + econs; eauto.
    ii; des.
    destruct (inj y b_src) eqn:T.
    * destruct p.
      exploit INCR0; eauto. i; clarify.
      inv FROZEN.
      hexploit NEW_IMPLIES_OUTSIDE; eauto.
    * inv FROZEN0.
      hexploit NEW_IMPLIES_OUTSIDE; eauto; []; i; des.
      split; ss; red; etransitivity; eauto.
      { rewrite <- SRCPARENTEQNB. reflexivity. }
      { rewrite <- TGTPARENTEQNB. reflexivity. }
  + i. r. etransitivity.
    { eapply MAXSRC0; eauto. eapply Plt_Ple_trans; eauto with mem.
      eapply Mem.unchanged_on_nextblock; eauto. } (* added *)
    eapply MAXSRC; eauto.
  + i. r. etransitivity.
    { eapply MAXTGT0; eauto. eapply Plt_Ple_trans; eauto with mem.
      eapply Mem.unchanged_on_nextblock; eauto. } (* added *)
    eapply MAXTGT; eauto.
Qed.

Definition lift' (mrel0: t'): t' :=
  (mk mrel0.(src) mrel0.(tgt) mrel0.(inj)
      mrel0.(src_private) mrel0.(tgt_private)
      mrel0.(src).(Mem.nextblock) mrel0.(tgt).(Mem.nextblock))
.

Definition unlift' (mrel0 mrel1: t'): t' :=
  (mk mrel1.(src) mrel1.(tgt) mrel1.(inj)
      mrel0.(src_external) mrel0.(tgt_external)
      mrel0.(src_parent_nb) mrel0.(tgt_parent_nb))
.

Lemma unlift_spec : forall mrel0 mrel1 : t',
                  le' (lift' mrel0) mrel1 -> wf' mrel0 -> le' mrel0 (unlift' mrel0 mrel1).
Proof.
  i.
  inv H; ss.
  econs; ss; eauto; ii; des; ss.
  - eapply Mem.unchanged_on_implies; eauto.
    ii. eapply H0; eauto.
  - eapply Mem.unchanged_on_implies; eauto.
    ii. eapply H0; eauto.
  - inv H0. ss.
    eapply frozen_shortened; eauto.
Qed.

Lemma unlift_wf : forall mrel0 mrel1 : t',
                wf' mrel0 ->
                wf' mrel1 -> le' (lift' mrel0) mrel1 -> wf' (unlift' mrel0 mrel1).
Proof.
  i.
  inv H. inv H0. inv H1.
  des; clarify.
  econs; ss; try etransitivity; eauto. (* eauto did well here *)
  - (* etransitivity; eauto. *)
    rewrite SRCPARENTEQ.
    etransitivity; eauto.

    (* u. bar. i; des. esplits; eauto. *)
    (* + eapply loc_unmapped_frozen; eauto. *)
    (* + unfold Mem.valid_block in *. xomega. *)
  - (* etransitivity; eauto. *)
    rewrite TGTPARENTEQ.
    etransitivity; eauto.
  - inv SRCUNCHANGED; ss.
  - inv TGTUNCHANGED; ss.
Qed.

Lemma after_private_src
      sm0 sm1
      (FROZEN: frozen sm0.(inj) sm1.(inj) sm0.(src).(Mem.nextblock) sm0.(tgt).(Mem.nextblock))
      (MLE: le' sm0.(lift') sm1)
  :
    sm0.(src_private) <2= sm1.(src_private)
.
Proof.
  inv MLE. inv SRCUNCHANGED. ss.
  unfold src_private, valid_blocks; ii; des; esplits; eauto.
  - eapply loc_unmapped_frozen; eauto.
  - unfold Mem.valid_block in *. xomega.
Qed.

Lemma after_private_tgt
      sm0 sm1
      (FROZEN: frozen sm0.(inj) sm1.(inj) sm0.(src).(Mem.nextblock) sm0.(tgt).(Mem.nextblock))
      (MWF: wf' sm0)
      (MLE: le' sm0.(lift') sm1)
  :
    sm0.(tgt_private) <2= sm1.(tgt_private)
.
Proof.
  inv MLE. inv TGTUNCHANGED. ss.
  unfold tgt_private, valid_blocks; ii; des; esplits; eauto.
  - eapply loc_out_of_reach_frozen; eauto.
    ii.
    assert(VALID: Mem.valid_block (src sm0) b0).
    { apply Classical_Prop.NNPP. ii. exploit Mem.mi_freeblocks; try apply MWF; eauto. ii. clarify. }
    eapply MAXSRC; eauto.
  - unfold Mem.valid_block in *. xomega.
Qed.

Section ORIGINALS.

Lemma store_mapped
      sm0 chunk v_src v_tgt blk_src ofs blk_tgt delta m_src0
      (MWF: wf' sm0)
      (STRSRC: Mem.store chunk sm0.(src) blk_src ofs v_src = Some m_src0)
      (SIMBLK: sm0.(inj) blk_src = Some (blk_tgt, delta))
      (SIMV: Val.inject sm0.(inj) v_src v_tgt)
  :
    exists sm1,
      (<<MSRC: sm1.(src) = m_src0>>)
      /\ (<<MINJ: sm1.(inj) = sm0.(inj)>>)
      /\ (<<STRTGT: Mem.store chunk sm0.(tgt) blk_tgt (ofs + delta) v_tgt = Some sm1.(tgt)>>)
      /\ (<<MWF: wf' sm1>>)
      /\ (<<MLE: le' sm0 sm1>>)
.
Proof.
  exploit Mem.store_mapped_inject; try apply MWF; eauto. i; des.
  inv MWF.
  eexists (mk _ _ _ _ _ _ _).
  esplits; ss; eauto; cycle 1.
  - econs; ss; eauto.
    + eapply Mem.store_unchanged_on; eauto.
      ii. apply SRCEXT in H2. red in H2. des. red in H2. clarify.
    + eapply Mem.store_unchanged_on; eauto.
      ii. apply TGTEXT in H2. red in H2. des. red in H2.
      eapply H2; eauto. clear - STRSRC H1 H4.
      apply Mem.store_valid_access_3 in STRSRC. destruct STRSRC.
      eauto with mem xomega.
    + eapply frozen_refl.
    + ii. eapply Mem.perm_store_2; eauto.
    + ii. eapply Mem.perm_store_2; eauto.
  - econs; ss; eauto.
    + etransitivity; eauto. unfold src_private. ss. ii; des. esplits; eauto.
      unfold valid_blocks in *. eauto with mem.
    + etransitivity; eauto. unfold tgt_private. ss. ii; des. esplits; eauto.
      { ii. eapply PR. eauto with mem. eauto with mem. }
      unfold valid_blocks in *. eauto with mem.
    + etransitivity; eauto. erewrite <- Mem.nextblock_store; eauto. xomega.
    + etransitivity; eauto. erewrite <- Mem.nextblock_store; eauto. xomega.
Qed.

Lemma storev_mapped
      sm0 chunk v_src v_tgt addr_src addr_tgt m_src0
      (MWF: wf' sm0)
      (STRSRC: Mem.storev chunk sm0.(src) addr_src v_src = Some m_src0)
      (SIMADDR: Val.inject sm0.(inj) addr_src addr_tgt)
      (SIMV: Val.inject sm0.(inj) v_src v_tgt)
  :
    exists sm1,
      (<<MSRC: sm1.(src) = m_src0>>)
      /\ (<<MINJ: sm1.(inj) = sm0.(inj)>>)
      /\ (<<STRTGT: Mem.storev chunk sm0.(tgt) addr_tgt v_tgt = Some sm1.(tgt)>>)
      /\ (<<MWF: wf' sm1>>)
      /\ (<<MLE: le' sm0 sm1>>)
.
Proof.
  exploit Mem.storev_mapped_inject; try apply MWF; eauto. i; des.
  unfold Mem.storev in STRSRC. des_ifs. inv SIMADDR. exploit store_mapped; eauto. i; des.
  exists sm1. esplits; eauto. unfold Mem.storev.
  hexploit (size_chunk_pos chunk); eauto. intro SZ.
  assert(Ptrofs.unsigned i + delta = Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr delta))).
  { rewrite <- Ptrofs.repr_unsigned with (i := i). rewrite Ptrofs.Ptrofs_add_repr.
    rewrite Ptrofs.unsigned_repr; [|eapply Ptrofs.unsigned_range_2]. rewrite Ptrofs.unsigned_repr; eauto.
    eapply Mem.mi_representable; eauto.
    left. eapply Mem.perm_store_1; eauto. eapply Mem.perm_implies; [|eauto with mem]. eapply Mem.perm_cur_max.
    eapply Mem.store_valid_access_3 in STRSRC. destruct STRSRC. eapply H1. omega.
  }
  rewrite <- H1. eauto.
Qed.

Lemma free_parallel
      sm0 lo hi blk_src blk_tgt delta m_src0
      (MWF: wf' sm0)
      (FREESRC: Mem.free sm0.(src) blk_src lo hi = Some m_src0)
      (SIMBLK: sm0.(inj) blk_src = Some (blk_tgt, delta))
  :
    exists sm1,
      (<<MSRC: sm1.(src) = m_src0>>)
      /\ (<<MINJ: sm1.(inj) = sm0.(inj)>>)
      /\ (<<FREETGT: Mem.free sm0.(tgt) blk_tgt (lo + delta) (hi + delta) = Some sm1.(tgt)>>)
      /\ (<<MWF: wf' sm1>>)
      /\ (<<MLE: le' sm0 sm1>>)
.
Proof.
  exploit Mem.free_parallel_inject; try apply MWF; eauto. i; des.
  inv MWF.
  eexists (mk _ _ _ _ _ _ _).
  esplits; ss; eauto; cycle 1.
  - econs; ss; eauto.
    + eapply Mem.free_unchanged_on; eauto.
      ii. apply SRCEXT in H2. red in H2. des. red in H2. clarify.
    + eapply Mem.free_unchanged_on; eauto.
      ii. apply TGTEXT in H2. red in H2. des. red in H2.
      eapply H2; eauto. clear - FREESRC H1 H4.
      apply Mem.free_range_perm in FREESRC. eauto with mem xomega.
    + eapply frozen_refl.
    + ii. eapply Mem.perm_free_3; eauto.
    + ii. eapply Mem.perm_free_3; eauto.
  - econs; ss; eauto.
    + etransitivity; eauto. unfold src_private. ss. ii; des. esplits; eauto.
      unfold valid_blocks in *. eauto with mem.
    + etransitivity; eauto. unfold tgt_private. ss. ii; des. esplits; eauto.
      { ii. eapply PR. eauto with mem. eauto with mem. }
      unfold valid_blocks in *. eauto with mem.
    + etransitivity; eauto. erewrite <- Mem.nextblock_free; eauto. xomega.
    + etransitivity; eauto. erewrite <- Mem.nextblock_free; eauto. xomega.
Qed.

Lemma free_left
      sm0 lo hi blk_src blk_tgt delta m_src0
      (MWF: wf' sm0)
      (FREESRC: Mem.free sm0.(src) blk_src lo hi = Some m_src0)
      (SIMBLK: sm0.(inj) blk_src = Some (blk_tgt, delta))
  :
    exists sm1,
      (<<MSRC: sm1.(src) = m_src0>>)
      /\ (<<MTGT: sm1.(tgt) = sm0.(tgt)>>)
      /\ (<<MINJ: sm1.(inj) = sm0.(inj)>>)
      /\ (<<MWF: wf' sm1>>)
      /\ (<<MLE: le' sm0 sm1>>)
.
Proof.
  exploit Mem.free_left_inject; try apply MWF; eauto. i; des.
  inv MWF.
  eexists (mk _ _ _ _ _ _ _).
  esplits; ss; eauto; cycle 1.
  - econs; ss; eauto.
    + eapply Mem.free_unchanged_on; eauto.
      ii. apply SRCEXT in H1. red in H1. des. red in H1. clarify.
    + eapply Mem.unchanged_on_refl.
    + eapply frozen_refl.
    + ii. eapply Mem.perm_free_3; eauto.
  - econs; ss; eauto.
    + etransitivity; eauto. unfold src_private. ss. ii; des. esplits; eauto.
      unfold valid_blocks in *. eauto with mem.
    + etransitivity; eauto. unfold tgt_private. ss. ii; des. esplits; eauto.
      { ii. eapply PR. eauto with mem. eauto with mem. }
    + etransitivity; eauto. erewrite <- Mem.nextblock_free; eauto. xomega.
Qed.

Lemma free_right
      sm0 lo hi blk_tgt m_tgt0
      (MWF: wf' sm0)
      (FREETGT: Mem.free sm0.(tgt) blk_tgt lo hi = Some m_tgt0)
      (PRIVTGT: forall ofs (BDD: lo <= ofs < hi), sm0.(tgt_private) blk_tgt ofs)
      (EXTTGT: forall ofs : Z, lo <= ofs < hi -> ~ tgt_external sm0 blk_tgt ofs)
  :
    exists sm1,
      (<<MSRC: sm1.(src) = sm0.(src)>>)
      /\ (<<MTGT: sm1.(tgt) = m_tgt0>>)
      /\ (<<MINJ: sm1.(inj) = sm0.(inj)>>)
      /\ (<<MWF: wf' sm1>>)
      /\ (<<MLE: le' sm0 sm1>>)
.
Proof.
  exploit Mem.free_right_inject; try apply MWF; eauto.
  { ii. eapply PRIVTGT in H1. red in H1. des. red in H1. eapply H1; eauto.
    replace (ofs + delta - delta) with ofs by omega. eauto with mem.
  }
  i; des.
  inv MWF.
  eexists (mk _ _ _ _ _ _ _).
  esplits; ss; eauto; cycle 1.
  - econs; ss; eauto.
    + eapply Mem.unchanged_on_refl.
    + eapply Mem.free_unchanged_on; eauto.
    + eapply frozen_refl.
    + ii. eapply Mem.perm_free_3; eauto.
  - econs; ss; eauto.
    + etransitivity; eauto. unfold tgt_private. ss. ii; des. esplits; eauto.
      unfold valid_blocks in *. eauto with mem.
    + etransitivity; eauto. erewrite <- Mem.nextblock_free; eauto. xomega.
Qed.

Lemma alloc_parallel
      sm0 lo_src hi_src lo_tgt hi_tgt blk_src m_src0
      (MWF: wf' sm0)
      (ALCSRC: Mem.alloc sm0.(src) lo_src hi_src = (m_src0, blk_src))
      (LO: lo_tgt <= lo_src)
      (HI: hi_src <= hi_tgt)
  :
    exists sm1 blk_tgt ,
      (<<MSRC: sm1.(src) = m_src0>>)
      /\ (<<ALCTGT: Mem.alloc sm0.(tgt) lo_tgt hi_tgt = (sm1.(tgt), blk_tgt)>>)
      /\ (<<INJ: sm1.(inj) blk_src = Some (blk_tgt, 0) /\ forall b, b <> blk_src -> sm1.(inj) b = sm0.(inj) b>>)
      /\ (<<MWF: wf' sm1>>)
      /\ (<<MLE: le' sm0 sm1>>)
.
Proof.
  exploit Mem.alloc_parallel_inject; try apply MWF; eauto. i; des.
  inv MWF.
  eexists (mk _ _ f' _ _ _ _). exists b2.
  esplits; ss; eauto; cycle 1.
  - econs; ss; eauto.
    + eapply Mem.alloc_unchanged_on; eauto.
    + eapply Mem.alloc_unchanged_on; eauto.
    + econs. ii. des.
      destruct (eq_block b_src blk_src).
      * subst. rewrite H2 in NEW0. clarify.
        eapply Mem.alloc_result in ALCSRC. rewrite ALCSRC.
        eapply Mem.alloc_result in H. rewrite H. esplits; eauto.
      * rewrite H3 in NEW0; eauto. clarify.
    + ii. eapply Mem.perm_alloc_4; eauto.
      ii. subst b. eapply Mem.fresh_block_alloc; try eapply ALCSRC; eauto.
    + ii. eapply Mem.perm_alloc_4; eauto.
      ii. subst b. eapply Mem.fresh_block_alloc; eauto.
  - econs; ss; eauto.
    + etransitivity; eauto. unfold src_private. ss. ii; des. esplits; eauto.
      { destruct (eq_block x0 blk_src).
        - subst x0. exfalso. eapply Mem.fresh_block_alloc; try eapply ALCSRC; eauto.
        - r. rewrite H3; eauto. }
      unfold valid_blocks in *. eauto with mem.
    + etransitivity; eauto. unfold tgt_private. ss. ii; des. esplits; eauto.
      { ii. destruct (eq_block b0 blk_src).
        - subst b0. clarify. eapply Mem.fresh_block_alloc; eauto.
        - eapply PR. rewrite <- H3; eauto. eauto with mem. }
      unfold valid_blocks in *. eauto with mem.
    + etransitivity; eauto. eapply Mem.nextblock_alloc in ALCSRC. rewrite ALCSRC. xomega.
    + etransitivity; eauto. eapply Mem.nextblock_alloc in H. rewrite H. xomega.
Qed.

Lemma external_call
      sm0 ef se vargs t vres m_src0 tse vargs' vres' m_tgt0 f'
      (MWF: wf' sm0)
      (EXTCALLSRC: external_call ef se vargs sm0.(src) t vres m_src0)
      (EXTCALLTGT: external_call ef tse vargs' sm0.(tgt) t vres' m_tgt0)
      (MEMINJ: Mem.inject f' m_src0 m_tgt0)
      (UNCHANGSRC: Mem.unchanged_on (loc_unmapped sm0.(inj)) sm0.(src) m_src0)
      (UNCHANGTGT: Mem.unchanged_on (loc_out_of_reach sm0.(inj) sm0.(src)) sm0.(tgt) m_tgt0)
      (INJINCR: inject_incr sm0.(inj) f')
      (INJSEP: inject_separated sm0.(inj) f' sm0.(src) sm0.(tgt))
  :
    exists sm1,
      (<<MSRC: sm1.(src) = m_src0>>)
      /\ (<<MTGT: sm1.(tgt) = m_tgt0>>)
      /\ (<<MINJ: sm1.(inj) = f'>>)
      /\ (<<MWF: wf' sm1>>)
      /\ (<<MLE: le' sm0 sm1>>)
.
Proof.
  inv MWF.
  assert (LE_LIFTED: le' sm0.(lift')
                               (mk m_src0 m_tgt0 f' sm0.(src_private) sm0.(tgt_private)
                                                                            sm0.(src).(Mem.nextblock) sm0.(tgt).(Mem.nextblock))).
  { econs; ss; eauto.
    - econs; i; eapply UNCHANGSRC; eauto; eapply H.
    - econs; i; eapply UNCHANGTGT; eauto; eapply H.
    - eapply inject_separated_frozen; eauto.
    - ii. eapply external_call_max_perm; eauto.
    - ii. eapply external_call_max_perm; eauto.
  }
  eexists (mk _ _ _ sm0.(src_external) sm0.(tgt_external) sm0.(src_parent_nb) sm0.(tgt_parent_nb)); eauto.
  esplits; ss; eauto.
  - econs; ss; eauto.
    + etransitivity; eauto. eapply (after_private_src _ LE_LIFTED).
    + etransitivity; eauto. eapply (after_private_tgt _ _ LE_LIFTED).
    + eapply Ple_trans; eauto. eapply UNCHANGSRC.
    + eapply Ple_trans; eauto; eapply UNCHANGTGT.
  - exploit unlift_spec; eauto. econs; eauto.
Unshelve.
  all: by (try eapply inject_separated_frozen; eauto).
Qed.

End ORIGINALS.

Record mcompat (sm0: t') (m_src0 m_tgt0: mem) (F: meminj): Prop := mkmcompat {
  mcompat_src: sm0.(src) = m_src0;
  mcompat_tgt: sm0.(tgt) = m_tgt0;
  mcompat_inj: sm0.(inj) = F;
}.

End MEMINJ.

Hint Unfold valid_blocks.
Hint Unfold src_private tgt_private.

Ltac compat_tac := ss; econs; eauto; try congruence.

Ltac spl := esplits; [|reflexivity].
Ltac spl_approx sm :=
  eexists (mk _ _ _ sm.(src_external) sm.(tgt_external) sm.(src_parent_nb) sm.(tgt_parent_nb)); splits; eauto.
Ltac spl_exact sm :=
  exists sm; splits; [|try etransitivity; eauto; try reflexivity; eauto].
