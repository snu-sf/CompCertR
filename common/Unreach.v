Require Import Coqlib Maps.
Require Import AST Linking.
Require Import Values Memory Globalenvs Events.
Require Import RelationClasses.
Require Import sflib.

Set Implicit Arguments.



Record t := mk {
  unreach:> block -> bool; (* for finiteness' `j` function. *)
  ge_nb: block;
  nb: block;
}.

Notation "'prange' '#' hi" := (fun blk => Plt blk hi) (at level 50, no associativity).
Notation "'prange' lo '#'" := (fun blk => Ple lo blk) (at level 50, no associativity).
Notation "'prange' lo hi" := (fun blk => Ple lo blk /\ Plt blk hi) (at level 50, no associativity).

Inductive wf (su: t): Prop :=
| wf_intro
  (WFLO: su <1= prange su.(ge_nb) #)
  (WFHI: su <1= prange # su.(nb)).

(* One strong point of definiton compared to inductive:
elimination of multiple predicate requires
- (inductive) multiple "inv"
- (definition) unfold __ in *; des *)
Definition hle_old (su0 su1: t): Prop :=
  (<<PRIV: su0.(unreach) <1= su1.(unreach)>>)
  /\ (<<OLD: su1.(unreach) /1\ (prange # su0.(nb)) <1= su0.(unreach)>>)
  /\ (<<NB: Ple su0.(nb) su1.(nb)>>)
  /\ (<<GENB: su0.(ge_nb) = su1.(ge_nb)>>).

Definition hle (su0 su1: t): Prop :=
  (<<OLD: forall blk (LT: Plt blk su0.(nb)), su0 blk = su1 blk>>)
  /\ (<<NB: Ple su0.(nb) su1.(nb)>>)
  /\ (<<GENB: su0.(ge_nb) = su1.(ge_nb)>>).

Lemma hle_old_hle: forall su0 su1, hle_old su0 su1 -> hle su0 su1.
Proof.
  split; i; rr in H; des; rr; esplits; eauto.
  - ii. destruct (su1 blk) eqn:T; ss.
    + exploit OLD; eauto.
    + destruct (su0 blk) eqn:T2; ss. exploit PRIV; eauto.
Qed.
Lemma hle_hle_old: forall su0 su1 (WF: wf su0), hle su0 su1 -> hle_old su0 su1.
Proof.
  split; i; rr in H; des; rr; esplits; eauto.
  - i. erewrite <- OLD; eauto.
    inv WF. exploit WFHI; eauto.
  - i. des. erewrite OLD; eauto.
Qed.

Lemma hle_update
      (su0 su1 su2: t)
      (EQ: forall blk (LT: Plt blk su0.(nb)), su1 blk = su2 blk)
      (NB: Ple su1.(nb) su2.(nb))
      (GENB: su1.(ge_nb) = su2.(ge_nb))
      (HLE: hle su0 su1):
    <<HLE: hle su0 su2>>.
Proof.
  rr in HLE. des. rr. esplits; eauto; try xomega. rewrite <- GENB. ss.
Qed.

Lemma hle_old_update
      (su0 su1 su2: t)
      (EQ: forall blk (LT: Plt blk su0.(nb)), su1 blk = su2 blk)
      (NB: Ple su1.(nb) su2.(nb))
      (GENB: su1.(ge_nb) = su2.(ge_nb))
      (HLE: hle_old su0 su1)
      (WF: wf su0):
    <<HLE: hle_old su0 su2>>.
Proof.
  rr in HLE. rr. des. esplits; eauto.
  - inv WF. i. exploit PRIV; eauto. i. erewrite <- EQ; eauto.
  - i; des. erewrite <- EQ in PR; eauto.
  - rewrite <- NB. xomega.
  - rewrite <- GENB. ss.
Qed.

Global Program Instance hle_old_PreOrder: PreOrder hle_old.
Next Obligation.
  rr. ii; des. esplits; eauto.
  - ii. des; ss.
  - xomega.
Qed.
Next Obligation.
  ii; des.
  unfold hle_old in *. des.
  esplits; eauto; try xomega.
  - ii. des; ss. eapply OLD0; eauto. esplits; eauto. eapply OLD; eauto. esplits; eauto. xomega.
  - congruence.
Qed.

Global Program Instance hle_PreOrder: PreOrder hle.
Next Obligation.
  rr. ii; des. esplits; eauto. reflexivity.
Qed.
Next Obligation.
  ii; des. unfold hle in *. des. esplits; eauto; try xomega.
  - ii. rewrite <- OLD; ss; try xomega. rewrite OLD0; ss.
  - congruence.
Qed.

Inductive mle (su: t) (m0 m1: Memory.mem): Prop :=
| mle_intro
    (PERM: forall blk ofs
        (VALID: m0.(Mem.valid_block) blk),
        m1.(Mem.perm) blk ofs Max <1= m0.(Mem.perm) blk ofs Max)
    (RO: Mem.unchanged_on m0.(loc_not_writable) m0 m1)
    (PRIV: Mem.unchanged_on (fun _ => su).(Basics.flip) m0 m1).

Global Program Instance mle_PreOrder su: PreOrder (mle su).
Next Obligation.
  rr. ii. econs; eauto with mem.
Qed.
Next Obligation.
  ii. inv H. inv H0. econs; ss; eauto.
  - ii. eapply PERM; eauto. eapply PERM0; eauto. unfold Mem.valid_block in *. inv RO. xomega.
  - eapply Mem_unchanged_on_trans_strong; eauto.
    eapply Mem.unchanged_on_implies; try apply RO0; eauto.
    ii. des. rr in H. eapply H; eauto.
  - eapply Mem.unchanged_on_trans; eauto.
Qed.

Lemma store_mle
      chunk m0 blk ofs v m1 (su: t)
      (STR: Mem.store chunk m0 blk ofs v = Some m1)
      (SU: ~su blk):
    <<MLE: mle su m0 m1>>.
Proof.
  econs; eauto.
  - ii. eauto with mem.
  - (* Copied from Events.volatile_store_readonly *)
    eapply Mem.store_unchanged_on; eauto.
    exploit Mem.store_valid_access_3; eauto. intros [P Q].
    intros. unfold loc_not_writable. red; intros. elim H0.
    apply Mem.perm_cur_max. apply P. auto.
  - eapply Mem.store_unchanged_on; eauto.
Qed.

Lemma free_mle
      m0 blk lo hi m1 (su: t)
      (FREE: Mem.free m0 blk lo hi = Some m1)
      (SU: ~su blk):
    <<MLE: mle su m0 m1>>.
Proof.
  econs; eauto.
  - ii. eauto with mem.
  - (* Copied from Events.extcall_free_ok *)
    inv FREE. eapply Mem.free_unchanged_on; eauto.
    intros. red; intros. elim H1.
    apply Mem.perm_cur_max. apply Mem.perm_implies with Freeable; auto with mem.
    eapply Mem.free_range_perm; eauto.
  - eapply Mem.free_unchanged_on; eauto.
Qed.

Lemma storebytes_mle
      m0 blk ofs mvs m1 (su: t)
      (STR: Mem.storebytes m0 blk ofs mvs = Some m1)
      (SU: ~su blk):
    <<MLE: mle su m0 m1>>.
Proof.
  econs; eauto.
  - ii. eauto with mem.
  - (* Copied from Events.volatile_store_readonly *)
    inv STR. eapply Mem.storebytes_unchanged_on; eauto.
    intros. red; intros. elim H1.
    apply Mem.perm_cur_max.
    eapply Mem.storebytes_range_perm; eauto.
  - eapply Mem.storebytes_unchanged_on; eauto.
Qed.

Lemma alloc_mle
      m0 lo hi m1 blk (su: t)
      (ALC: Mem.alloc m0 lo hi = (m1, blk)):
    <<MLE: mle su m0 m1>>.
Proof.
  econs; eauto.
  - ii. eauto with mem.
  - eapply Mem.alloc_unchanged_on; eauto.
  - eapply Mem.alloc_unchanged_on; eauto.
Qed.

Lemma mle_monotone
      m0 m1 (su0 su1: t)
      (LE: su0 <1= su1)
      (MLE: su1.(mle) m0 m1):
    <<MLE: su0.(mle) m0 m1>>.
Proof.
  inv MLE. econs; eauto. eapply Mem.unchanged_on_implies; eauto. unfold Basics.flip in *. rr. ii. eapply LE; eauto.
Qed.

Ltac nb_tac :=
  repeat
    multimatch goal with
    | [ H: nb _ = _ |- _ ] => rewrite H in *
    | [ H: ge_nb _ = _ |- _ ] => rewrite H in *
    end.
