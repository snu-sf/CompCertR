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

(** Elimination of unreferenced static definitions *)

Require Import FSets Coqlib Maps Ordered Iteration Errors.
Require Import AST Linking.
Require Import Integers Values Memory Globalenvs Events Smallstep.
Require Import Op Registers RTL.
Require Import Unreadglob.
Require Import sflib.
Require SimMemInjInv.

Module ISF := FSetFacts.Facts(IS).
Module ISP := FSetProperties.Properties(IS).

Definition IS_to_idset (used: IS.t): ident -> bool := fun elt => IS.mem elt used.
Hint Unfold IS_to_idset.
Coercion IS_to_idset: IS.t >-> Funclass.

(** * Relational specification of the transformation *)

(** The transformed program is obtained from the original program
  by keeping only the global definitions that belong to a given
  set [u] of names.  *)

Record match_prog_1 (used: ident -> bool) (p tp: program) : Prop := {
  match_prog_main:
    tp.(prog_main) = p.(prog_main);
  match_prog_public:
    tp.(prog_public) = p.(prog_public);
  match_prog_def:
    forall id,
       (prog_defmap tp)!id = if used id then (option_map (map_globdef used) ((prog_defmap p)!id)) else None;
  match_prog_unique:
    list_norepet (prog_defs_names tp)
}.

(** This set [u] (as "used") must be closed under references, and
  contain the entry point and the public identifiers of the program. *)

Definition ref_function (f: function) (id: ident) : Prop :=
  exists pc i, f.(fn_code)!pc = Some i /\ In id (ref_instruction i).

Definition ref_fundef (fd: fundef) (id: ident) : Prop :=
  match fd with Internal f => ref_function f id | External ef => False end.

Definition ref_init (il: list init_data) (id: ident) : Prop :=
  exists ofs, In (Init_addrof id ofs) il.

Definition ref_def (gd: globdef fundef unit) (id: ident) : Prop :=
  match gd with
  | Gfun fd => ref_fundef fd id
  | Gvar gv => ref_init gv.(gvar_init) id
  end.

Record valid_used_set (p: program) (used: ident -> bool) : Prop := {
  used_closed: forall id gd id',
    used id -> (prog_defmap p)!id = Some gd -> ref_def gd id' ->
    used id';
  used_main:
    used p.(prog_main);
  used_public: forall id,
    In id p.(prog_public) -> used id;
  used_defined: forall id,
    used id -> In id (prog_defs_names p) \/ id = p.(prog_main)
}.

Definition used_set (tp: program): ident -> bool :=
  fun id => in_dec Pos.eq_dec id (tp.(prog_main) :: (tp.(prog_defs_names)))
.

Definition match_prog (p tp: program) : Prop :=
  exists used: ident -> bool, valid_used_set p used /\ match_prog_1 used p tp /\ check_program p
        /\ <<EXACT: used = used_set tp>>.

Definition match_prog_weak (p tp: program) : Prop :=
  exists used: ident -> bool, valid_used_set p used /\ match_prog_1 used p tp /\ check_program p.

Lemma match_prog_weakening
  :
    match_prog <2= match_prog_weak
.
Proof.
  i. inv PR. des. econs; eauto.
Qed.

(** * Properties of the static analysis *)

(** Monotonic evolution of the workset. *)

Inductive workset_incl (w1 w2: workset) : Prop :=
  workset_incl_intro:
    forall (SEEN: IS.Subset w1.(w_seen) w2.(w_seen))
           (TODO: List.incl w1.(w_todo) w2.(w_todo))
           (TRACK: forall id, IS.In id w2.(w_seen) ->
                      IS.In id w1.(w_seen) \/ List.In id w2.(w_todo)),
    workset_incl w1 w2.

Lemma seen_workset_incl:
  forall w1 w2 id, workset_incl w1 w2 -> IS.In id w1 -> IS.In id w2.
Proof.
  intros. destruct H. auto.
Qed.

Lemma workset_incl_refl: forall w, workset_incl w w.
Proof.
  intros; split. red; auto. red; auto. auto.
Qed.

Lemma workset_incl_trans:
  forall w1 w2 w3, workset_incl w1 w2 -> workset_incl w2 w3 -> workset_incl w1 w3.
Proof.
  intros. destruct H, H0; split.
  red; eauto.
  red; eauto.
  intros. edestruct TRACK0; eauto. edestruct TRACK; eauto.
Qed.

Lemma add_workset_incl:
  forall id w, workset_incl w (add_workset id w).
Proof.
  unfold add_workset; intros. destruct (IS.mem id w) eqn:MEM.
- apply workset_incl_refl.
- split; simpl.
  + red; intros. apply IS.add_2; auto.
  + red; simpl; auto.
  + intros. destruct (ident_eq id id0); auto. apply IS.add_3 in H; auto.
Qed.

Lemma addlist_workset_incl:
  forall l w, workset_incl w (addlist_workset l w).
Proof.
  induction l; simpl; intros.
  apply workset_incl_refl.
  eapply workset_incl_trans. apply add_workset_incl. eauto.
Qed.

Lemma add_ref_function_incl:
  forall f w, workset_incl w (add_ref_function f w).
Proof.
  unfold add_ref_function; intros. apply PTree_Properties.fold_rec.
- auto.
- apply workset_incl_refl.
- intros. apply workset_incl_trans with a; auto.
  unfold add_ref_instruction. apply addlist_workset_incl.
Qed.

Lemma add_ref_globvar_incl:
  forall gv w, workset_incl w (add_ref_globvar gv w).
Proof.
  unfold add_ref_globvar; intros.
  revert w. induction (gvar_init gv); simpl; intros.
  apply workset_incl_refl.
  eapply workset_incl_trans; [ | eauto ].
  unfold add_ref_init_data.
  destruct a; (apply workset_incl_refl || apply add_workset_incl).
Qed.

Lemma add_ref_definition_incl:
  forall pm id w, workset_incl w (add_ref_definition pm id w).
Proof.
  unfold add_ref_definition; intros.
  destruct (pm!id) as [[[] | ? ] | ].
  apply add_ref_function_incl.
  apply workset_incl_refl.
  apply add_ref_globvar_incl.
  apply workset_incl_refl.
Qed.

Lemma initial_workset_incl:
  forall p, workset_incl {| w_seen := IS.empty; w_todo := nil |} (initial_workset p).
Proof.
  unfold initial_workset; intros.
  eapply workset_incl_trans. 2: apply add_workset_incl.
  generalize {| w_seen := IS.empty; w_todo := nil |}. induction (prog_public p); simpl; intros.
  apply workset_incl_refl.
  eapply workset_incl_trans. apply add_workset_incl. apply IHl.
Qed.

(** Soundness properties for functions that add identifiers to the workset *)

Lemma seen_add_workset:
  forall id (w: workset), IS.In id (add_workset id w).
Proof.
  unfold add_workset; intros.
  destruct (IS.mem id w) eqn:MEM.
  apply IS.mem_2; auto.
  simpl. apply IS.add_1; auto.
Qed.

Lemma seen_addlist_workset:
  forall id l (w: workset),
  In id l -> IS.In id (addlist_workset l w).
Proof.
  induction l; simpl; intros.
  tauto.
  destruct H. subst a.
  eapply seen_workset_incl. apply addlist_workset_incl. apply seen_add_workset.
  apply IHl; auto.
Qed.

Lemma seen_add_ref_function:
  forall id f w,
  ref_function f id -> IS.In id (add_ref_function f w).
Proof.
  intros until w. unfold ref_function, add_ref_function. apply PTree_Properties.fold_rec; intros.
- destruct H1 as (pc & i & A & B). apply H0; auto. exists pc, i; split; auto. rewrite H; auto.
- destruct H as (pc & i & A & B). rewrite PTree.gempty in A; discriminate.
- destruct H2 as (pc & i & A & B). rewrite PTree.gsspec in A. destruct (peq pc k).
  + inv A. unfold add_ref_instruction. apply seen_addlist_workset; auto.
  + unfold add_ref_instruction. eapply seen_workset_incl. apply addlist_workset_incl.
    apply H1. exists pc, i; auto.
Qed.

Lemma seen_add_ref_definition:
  forall pm id gd id' w,
  pm!id = Some gd -> ref_def gd id' -> IS.In id' (add_ref_definition pm id w).
Proof.
  unfold add_ref_definition; intros. rewrite H. red in H0; destruct gd as [[f|ef]|gv].
  apply seen_add_ref_function; auto.
  contradiction.
  destruct H0 as (ofs & IN).
  unfold add_ref_globvar.
  assert (forall l (w: workset),
          IS.In id' w \/ In (Init_addrof id' ofs) l ->
          IS.In id' (fold_left add_ref_init_data l w)).
  {
    induction l; simpl; intros.
    tauto.
    apply IHl. intuition auto.
    left. destruct a; simpl; auto. eapply seen_workset_incl. apply add_workset_incl. auto.
    subst; left; simpl. apply seen_add_workset.
  }
  apply H0; auto.
Qed.

Lemma seen_main_initial_workset:
  forall p, IS.In p.(prog_main) (initial_workset p).
Proof.
  intros. apply seen_add_workset.
Qed.

Lemma seen_public_initial_workset:
  forall p id, In id p.(prog_public) -> IS.In id (initial_workset p).
Proof.
  intros. unfold initial_workset. eapply seen_workset_incl. apply add_workset_incl.
  assert (forall l (w: workset),
          IS.In id w \/ In id l -> IS.In id (fold_left (fun w id => add_workset id w) l w)).
  {
    induction l; simpl; intros.
    tauto.
    apply IHl. intuition auto; left.
    eapply seen_workset_incl. apply add_workset_incl. auto.
    subst a. apply seen_add_workset.
  }
  apply H0. auto.
Qed.

(** * Correctness of the transformation with respect to the relational specification *)

(** Correctness of the dependency graph traversal. *)

Section ANALYSIS.

Variable p: program.
Let pm := prog_defmap p.

Definition workset_invariant (w: workset) : Prop :=
  forall id gd id',
  IS.In id w -> ~List.In id (w_todo w) -> pm!id = Some gd -> ref_def gd id' ->
  IS.In id' w.

Definition used_set_closed (u: IS.t) : Prop :=
  forall id gd id',
  IS.In id u -> pm!id = Some gd -> ref_def gd id' -> IS.In id' u.

Lemma iter_step_invariant:
  forall w,
  workset_invariant w ->
  match iter_step pm w with
  | inl u => used_set_closed u
  | inr w' => workset_invariant w'
  end.
Proof.
  unfold iter_step, workset_invariant, used_set_closed; intros.
  destruct (w_todo w) as [ | id rem ]; intros.
- eapply H; eauto.
- set (w' := {| w_seen := w.(w_seen); w_todo := rem |}) in *.
  destruct (add_ref_definition_incl pm id w').
  destruct (ident_eq id id0).
  + subst id0. eapply seen_add_ref_definition; eauto.
  + exploit TRACK; eauto. intros [A|A].
    * apply SEEN. eapply H; eauto. simpl.
      assert (~ In id0 rem).
      { change rem with (w_todo w'). red; intros. elim H1; auto. }
      tauto.
    * contradiction.
Qed.

Theorem used_globals_sound:
  forall u, used_globals p pm = Some u -> used_set_closed u.
Proof.
  unfold used_globals; intros. eapply PrimIter.iterate_prop with (A := workset) (P := workset_invariant); eauto.
- intros. apply iter_step_invariant; auto.
- destruct (initial_workset_incl p).
  red; intros. edestruct TRACK; eauto.
  simpl in H4. eelim IS.empty_1; eauto.
  contradiction.
Qed.

Theorem used_globals_incl:
  forall u, used_globals p pm = Some u -> IS.Subset (initial_workset p) u.
Proof.
  unfold used_globals; intros.
  eapply PrimIter.iterate_prop with (P := fun (w: workset) => IS.Subset (initial_workset p) w); eauto.
- fold pm; unfold iter_step; intros. destruct (w_todo a) as [ | id rem ].
  auto.
  destruct (add_ref_definition_incl pm id {| w_seen := a; w_todo := rem |}).
  red; auto.
- red; auto.
Qed.

Corollary used_globals_valid:
  forall u,
  used_globals p pm = Some u ->
  IS.for_all (global_defined p pm) u = true ->
  valid_used_set p u.
Proof.
  intros. constructor.
- intros. apply ISF.mem_iff. eapply used_globals_sound; eauto. apply ISF.mem_iff. eauto.
- apply ISF.mem_iff. eapply used_globals_incl; eauto. apply seen_main_initial_workset.
- intros. apply ISF.mem_iff. eapply used_globals_incl; eauto. apply seen_public_initial_workset; auto.
- intros. apply ISF.for_all_iff in H0.
+ red in H0. apply ISF.mem_iff in H1. apply H0 in H1. unfold global_defined in H1.
  destruct pm!id as [g|] eqn:E.
* left. change id with (fst (id,g)). apply in_map. apply in_prog_defmap; auto.
* InvBooleans; auto.
+ hnf. simpl; intros; congruence.
Qed.

End ANALYSIS.

(** Properties of the elimination of unused global definitions. *)

Section TRANSFORMATION.

Variable p: program.
Variable used: IS.t.

Let add_def (m: prog_map) idg := PTree.set (fst idg) (snd idg) m.

Remark filter_globdefs_accu:
  forall defs accu1 accu2 u,
  filter_globdefs u (accu1 ++ accu2) defs = filter_globdefs u accu1 defs ++ accu2.
Proof.
  induction defs; simpl; intros.
  auto.
  destruct a as [id gd]. destruct (IS.mem id u); auto.
  rewrite <- IHdefs. auto.
Qed.

Remark filter_globdefs_nil:
  forall u accu defs,
  filter_globdefs u accu defs = filter_globdefs u nil defs ++ accu.
Proof.
  intros. rewrite <- filter_globdefs_accu. auto.
Qed.

Lemma filter_globdefs_map_1:
  forall id l u m1,
  IS.mem id u = false ->
  m1!id = None ->
  (fold_left add_def (filter_globdefs u nil l) m1)!id = None.
Proof.
  induction l as [ | [id1 gd1] l]; simpl; intros.
- auto.
- destruct (IS.mem id1 u) eqn:MEM.
+ rewrite filter_globdefs_nil. rewrite fold_left_app. simpl.
  unfold add_def at 1. simpl. rewrite PTree.gso by congruence. eapply IHl; eauto.
  rewrite ISF.remove_b. rewrite H; auto.
+ eapply IHl; eauto.
Qed.

Lemma filter_globdefs_map_2:
  forall id l u m1 m2,
  IS.mem id u = true ->
  m1!id = m2!id ->
  (fold_left add_def (filter_globdefs u nil l) m1)!id = (fold_left add_def (List.rev l) m2)!id.
Proof.
  induction l as [ | [id1 gd1] l]; simpl; intros.
- auto.
- rewrite fold_left_app. simpl.
  destruct (IS.mem id1 u) eqn:MEM.
+ rewrite filter_globdefs_nil. rewrite fold_left_app. simpl.
  unfold add_def at 1 3. simpl.
  rewrite ! PTree.gsspec. destruct (peq id id1). auto.
  apply IHl; auto.
  apply IS.mem_1. apply IS.remove_2; auto. apply IS.mem_2; auto.
+ unfold add_def at 2. simpl. rewrite PTree.gso by congruence. apply IHl; auto.
Qed.

Lemma filter_globdefs_map:
  forall id u defs,
  (PTree_Properties.of_list (filter_globdefs u nil (List.rev defs)))! id =
  if IS.mem id u then (PTree_Properties.of_list defs)!id else None.
Proof.
  intros. unfold PTree_Properties.of_list. fold prog_map. unfold PTree.elt. fold add_def.
  destruct (IS.mem id u) eqn:MEM.
- erewrite filter_globdefs_map_2. rewrite List.rev_involutive. reflexivity.
  auto. auto.
- apply filter_globdefs_map_1. auto. apply PTree.gempty.
Qed.

Lemma filter_globdefs_domain:
  forall id l u,
  In id (map fst (filter_globdefs u nil l)) -> IS.In id u /\ In id (map fst l).
Proof.
  induction l as [ | [id1 gd1] l]; simpl; intros.
- tauto.
- destruct (IS.mem id1 u) eqn:MEM.
+ rewrite filter_globdefs_nil, map_app, in_app_iff in H. destruct H.
  apply IHl in H. rewrite ISF.remove_iff in H. tauto.
  simpl in H. destruct H; try tauto. subst id1. split; auto. apply IS.mem_2; auto.
+ apply IHl in H. tauto.
Qed.

Lemma filter_globdefs_image:
  forall id l u kept,
  IS.In id u /\ In id (map fst l) -> In id (map fst (filter_globdefs u nil (map_globdefs kept l))).
Proof.
  induction l as [ | [id1 gd1] l]; simpl; intros.
- tauto.
- destruct (IS.mem id1 u) eqn:MEM.
+ rewrite filter_globdefs_nil, map_app, in_app_iff. destruct H.
  ss.
  destruct (Pos.eq_dec id1 id).
  * clarify. tauto.
  * des; clarify. left. eapply IHl; eauto. esplits; eauto. rewrite ISF.remove_iff. esplits; eauto.
+ apply ISF.not_mem_iff in MEM. des; clarify. eapply IHl; eauto.
Qed.

Lemma filter_globdefs_unique_names:
  forall l u, list_norepet (map fst (filter_globdefs u nil l)).
Proof.
  induction l as [ | [id1 gd1] l]; simpl; intros.
- constructor.
- destruct (IS.mem id1 u) eqn:MEM; auto.
  rewrite filter_globdefs_nil, map_app. simpl.
  apply list_norepet_append; auto.
  constructor. simpl; tauto. constructor.
  red; simpl; intros. destruct H0; try tauto. subst y.
  apply filter_globdefs_domain in H. rewrite ISF.remove_iff in H. intuition.
Qed.

End TRANSFORMATION.

Lemma PTree_Properties_of_list_map
      X Y (f: X -> Y)
      (xs: list (PTree.elt * X))
  :
    forall id,
    (PTree_Properties.of_list (map (fun idx => (idx.(fst), (f idx.(snd)))) xs)) ! id
    =
    (PTree.map (fun _ x => f x) (PTree_Properties.of_list xs)) ! id
.
Proof.
  i. unfold PTree_Properties.of_list. rewrite PTree.gmap. unfold option_map.
  rewrite <- ! fold_left_rev_right.
  rewrite <- map_rev.
  (* unfold PTree.elt, ident. *)
  abstr (rev xs) ixs. clear_tac.
  induction ixs; ii; ss.
  { rewrite ! PTree.gempty. ss. }
  rewrite ! PTree.gsspec in *.
  des_ifs; ss.
Qed.

Theorem transf_program_match:
  forall p tp, transform_program p = OK tp -> match_prog p tp.
Proof.
  unfold transform_program; intros p tp TR. set (pm := prog_defmap p) in *.
  destruct (check_program p) eqn:CHK; ss.
  destruct (used_globals p pm) as [u|] eqn:U; try discriminate.
  destruct (IS.for_all (global_defined p pm) u) eqn:DEF; inv TR.
  exists u; split.
  apply used_globals_valid; auto.
  assert(MATCH: match_prog_1 u p (mkprogram (filter_globdefs u [] (map_globdefs u (rev (prog_defs p))))
                                            (prog_public p) (prog_main p))).
  {
  constructor; simpl; auto.
  intros. unfold prog_defmap; simpl.
  { unfold map_globdefs. rewrite map_rev. rewrite filter_globdefs_map.
    unfold IS_to_idset. des_ifs. unfold option_map. rewrite PTree_Properties_of_list_map. rewrite PTree.gmap. des_ifs.
  }
  apply filter_globdefs_unique_names.
  }
  split; auto.
  split; auto.
  {
    unfold used_set in *.
    exploit used_globals_valid; eauto. intro VAL.
    r. unfold prog_defs_names. ss.
    apply Axioms.functional_extensionality. i.
    inv MATCH. ss. unfold prog_defmap in *. ss.
    specialize (match_prog_def0 x).
    symmetry.
    unfold prog_defs_names in *. ss.
    set (filter_globdefs u [] (rev (prog_defs p))) as tdefs in *.
    rename u into kept.
    apply ISF.for_all_iff in DEF; cycle 1.
    { ii; ss; clarify. }
    r in DEF. unfold global_defined in *.
    subst pm. clear_tac.
    destruct (kept x) eqn:T; des_sumbool; unfold IS_to_idset in *; cycle 1.
    - ii. des; clarify.
      + inv VAL. clarify.
      + exploit filter_globdefs_domain; eauto. i; des.
        erewrite <- ISF.not_mem_iff in *; eauto.
    - destruct (Pos.eq_dec x p.(prog_main)).
      { clarify. tauto. }
      right.
      eapply filter_globdefs_image. esplits; eauto.
      + rewrite ISF.mem_iff; ss.
      + exploit DEF; eauto.
        { eapply ISF.mem_iff; eauto. }
        intro DEFX. des_ifs.
        * exploit PTree_Properties.in_of_list; try apply Heq. i.
          rewrite in_map_iff. eexists (_, _). ss.
          esplits; eauto.
          rewrite <- in_rev; eauto.
        * des_sumbool. clarify.
  }
Qed.

(** * Semantic preservation *)

Section SOUNDNESS.

Variable p: program.
Variable tp: program.
Variable kept: ident -> bool.
Hypothesis USED_VALID: valid_used_set p kept.
Hypothesis TRANSF: match_prog_1 kept p tp.
Let pm := prog_defmap p.

Section CORELEMMA.

Variable (se tse: Senv.t).
Variable ge : genv.
Variable tge : genv.
Hypothesis SECOMPATSRC: senv_genv_compat se ge.
Hypothesis SECOMPATTGT: senv_genv_compat tse tge.

Lemma kept_closed:
  forall id gd id',
  kept id -> pm!id = Some gd -> ref_def gd id' -> kept id'.
Proof.
  intros. eapply used_closed; eauto.
Qed.

Lemma kept_main:
  kept p.(prog_main).
Proof.
  eapply used_main; eauto.
Qed.

Lemma kept_public:
  forall id, In id p.(prog_public) -> kept id.
Proof.
  intros. eapply used_public; eauto.
Qed.

(** Injections that preserve used globals. *)

Record meminj_preserves_globals (invar: block -> Prop) (f: meminj): Prop := {
  symbols_inject_1: forall id b b' delta,
    f b = Some(b', delta) -> Genv.find_symbol ge id = Some b ->
    delta = 0 /\ Genv.find_symbol tge id = Some b' /\ kept id;
  symbols_inject_2: forall id b,
    kept id -> Genv.find_symbol ge id = Some b ->
    exists b', Genv.find_symbol tge id = Some b' /\ f b = Some(b', 0);
  symbols_inject_3: forall id b',
    Genv.find_symbol tge id = Some b' ->
    exists b, Genv.find_symbol ge id = Some b /\ f b = Some(b', 0);
  symbols_inject_4: forall id b,
    ~ kept id -> Genv.find_symbol ge id = Some b -> invar b;
  defs_inject: forall b b' delta gd,
    f b = Some(b', delta) -> Genv.find_def ge b = Some gd ->
    Genv.find_def tge b' = Some (map_globdef kept gd) /\ delta = 0 /\
    (forall id, ref_def gd id -> kept id);
  defs_rev_inject: forall b b' delta gd_tgt,
    f b = Some(b', delta) -> Genv.find_def tge b' = Some gd_tgt ->
    exists gd_src, Genv.find_def ge b = Some gd_src /\ delta = 0 /\ gd_tgt = map_globdef kept gd_src;
  public_eq: Genv.genv_public ge = prog_public p /\ Genv.genv_public tge = prog_public tp;
}.

Lemma globals_symbols_inject invar:
  forall j, meminj_preserves_globals invar j -> symbols_inject j ge tge.
Proof.
  intros.
  assert (E1: Genv.genv_public ge = p.(prog_public)).
  { exploit public_eq; eauto. i; des; eauto. }
  assert (E2: Genv.genv_public tge = p.(prog_public)).
  { exploit public_eq; eauto. i; des. rewrite H1. eapply match_prog_public; eauto. }
  split; [|split;[|split]]; intros.
  + simpl; unfold Genv.public_symbol; rewrite E1, E2.
    destruct (Genv.find_symbol tge id) as [b'|] eqn:TFS.
    exploit symbols_inject_3; eauto. intros (b & FS & INJ). rewrite FS. auto.
    destruct (Genv.find_symbol ge id) as [b|] eqn:FS; auto.
    destruct (in_dec ident_eq id (prog_public p)); simpl; auto.
    exploit symbols_inject_2; eauto.
    eapply kept_public; eauto.
    intros (b' & TFS' & INJ). congruence.
  + ss. exploit symbols_inject_1; eauto. i; des. esplits; eauto.
  + simpl in *; unfold Genv.public_symbol in H0.
    destruct (Genv.find_symbol ge id) as [b|] eqn:FS; try discriminate.
    rewrite E1 in H0.
    destruct (in_dec ident_eq id (prog_public p)); try discriminate. inv H1.
    exploit symbols_inject_2; eauto.
    eapply kept_public; eauto.
    intros (b' & A & B); exists b'; auto.
  + simpl. unfold Genv.block_is_volatile.
    destruct (Genv.find_var_info ge b1) as [gv|] eqn:V1.
    rewrite Genv.find_var_info_iff in V1.
    exploit defs_inject; eauto. intros (A & B & C).
    ss.
    rewrite <- Genv.find_var_info_iff in A. rewrite A; auto.
    destruct (Genv.find_var_info tge b2) as [gv|] eqn:V2; auto.
    rewrite Genv.find_var_info_iff in V2.
    exploit defs_rev_inject; eauto. intros (gd_src & A & B & C).
    unfold map_globdef in *. des_ifs.
    rewrite <- Genv.find_var_info_iff in A. congruence.
Qed.

Lemma symbol_address_inject invar:
  forall j id ofs,
  meminj_preserves_globals invar j -> kept id ->
  Val.inject j (Genv.symbol_address ge id ofs) (Genv.symbol_address tge id ofs).
Proof.
  intros. unfold Genv.symbol_address. destruct (Genv.find_symbol ge id) as [b|] eqn:FS; auto.
  exploit symbols_inject_2; eauto. intros (b' & TFS & INJ). rewrite TFS.
  econstructor; eauto. rewrite Ptrofs.add_zero; auto.
Qed.

(** Semantic preservation *)

Definition regset_inject (f: meminj) (rs rs': regset): Prop :=
  forall r, Val.inject f rs#r rs'#r.

Lemma regs_inject:
  forall f rs rs', regset_inject f rs rs' -> forall l, Val.inject_list f rs##l rs'##l.
Proof.
  induction l; simpl. constructor. constructor; auto.
Qed.

Lemma set_reg_inject:
  forall f rs rs' r v v',
  regset_inject f rs rs' -> Val.inject f v v' ->
  regset_inject f (rs#r <- v) (rs'#r <- v').
Proof.
  intros; red; intros. rewrite ! Regmap.gsspec. destruct (peq r0 r); auto.
Qed.

Lemma set_res_inject:
  forall f rs rs' res v v',
  regset_inject f rs rs' -> Val.inject f v v' ->
  regset_inject f (regmap_setres res v rs) (regmap_setres res v' rs').
Proof.
  intros. destruct res; auto. apply set_reg_inject; auto.
Qed.

Lemma regset_inject_incr:
  forall f f' rs rs', regset_inject f rs rs' -> inject_incr f f' -> regset_inject f' rs rs'.
Proof.
  intros; red; intros. apply val_inject_incr with f; auto.
Qed.

Lemma regset_undef_inject:
  forall f, regset_inject f (Regmap.init Vundef) (Regmap.init Vundef).
Proof.
  intros; red; intros. rewrite Regmap.gi. auto.
Qed.

Lemma init_regs_inject:
  forall f args args', Val.inject_list f args args' ->
  forall params,
  regset_inject f (init_regs args params) (init_regs args' params).
Proof.
  induction 1; intros; destruct params; simpl; try (apply regset_undef_inject).
  apply set_reg_inject; auto.
Qed.

Inductive match_stacks (invar: block -> Prop) (j: meminj):
        list stackframe -> list stackframe -> block -> block -> Prop :=
  | match_stacks_nil: forall bound tbound,
      forall (SYMBINJ: symbols_inject j se tse),
      meminj_preserves_globals invar j ->
      Ple (Genv.genv_next ge) bound -> Ple (Genv.genv_next tge) tbound ->
      match_stacks invar j nil nil bound tbound
  | match_stacks_cons: forall res f sp pc rs s tsp trs ts bound tbound
         tf (TRANF: tf = (transf_function (fun _ i => filter_instr kept i) f))
         (STACKS: match_stacks invar j s ts sp tsp)
         (KEPT: forall id, ref_function f id -> kept id)
         (SPINJ: j sp = Some(tsp, 0))
         (REGINJ: regset_inject j rs trs)
         (BELOW: Plt sp bound)
         (TBELOW: Plt tsp tbound),
      match_stacks invar j (Stackframe res f (Vptr sp Ptrofs.zero) pc rs :: s)
                     (Stackframe res tf (Vptr tsp Ptrofs.zero) pc trs :: ts)
                     bound tbound.

Lemma match_stacks_symbols_inject invar:
  forall j s ts bound tbound,
  match_stacks invar j s ts bound tbound ->
  symbols_inject j se tse.
Proof.
  induction 1; auto.
Qed.

Lemma match_stacks_preserves_globals invar:
  forall j s ts bound tbound,
  match_stacks invar j s ts bound tbound ->
  meminj_preserves_globals invar j.
Proof.
  induction 1; auto.
Qed.

Lemma match_stacks_incr invar:
  forall j j', inject_incr j j' ->
  forall s ts bound tbound, match_stacks invar j s ts bound tbound ->
  (forall b1 b2 delta,
      j b1 = None -> j' b1 = Some(b2, delta) -> Ple bound b1 /\ Ple tbound b2) ->
  match_stacks invar j' s ts bound tbound.
Proof.
  induction 2; intros.
- assert (SAME: forall b b' delta, Plt b (Genv.genv_next ge) ->
                                   j' b = Some(b', delta) -> j b = Some(b', delta)).
  { intros. destruct (j b) as [[b1 delta1] | ] eqn: J.
    exploit H; eauto. congruence.
    exploit H3; eauto. intros [A B]. elim (Plt_strict b).
    eapply Plt_Ple_trans. eauto. eapply Ple_trans; eauto. }
  assert (SAME': forall b b' delta, Plt b' (Genv.genv_next tge) ->
                                   j' b = Some(b', delta) -> j b = Some (b', delta)).
  { intros. destruct (j b) as [[b1 delta1] | ] eqn: J.
    exploit H; eauto. congruence.
    exploit H3; eauto. intros [A B]. elim (Plt_strict b').
    eapply Plt_Ple_trans. eauto. eapply Ple_trans; eauto. }
  constructor; auto.
  { eapply symbols_inject_incr; eauto.
    - i. inv SECOMPATSRC. rewrite NB in *. apply SAME; ss.
    - i. inv SECOMPATTGT. rewrite NB in *. apply SAME'; ss.
  }
  constructor; intros.
  + exploit symbols_inject_1; eauto. apply SAME; auto.
    eapply Genv.genv_symb_range; eauto.
  + exploit symbols_inject_2; eauto. intros (b' & A & B).
    exists b'; auto.
  + exploit symbols_inject_3; eauto. intros (b & A & B).
    exists b; auto.
  + exploit symbols_inject_4; eauto.
  + eapply defs_inject; eauto. apply SAME; auto.
    eapply Genv.genv_defs_range; eauto.
  + eapply defs_rev_inject; eauto. apply SAME'; auto.
    eapply Genv.genv_defs_range; eauto.
  + apply H0.
- econstructor; eauto.
  apply IHmatch_stacks.
  intros. exploit H1; eauto. intros [A B]. split; eapply Ple_trans; eauto.
  apply Plt_Ple; auto. apply Plt_Ple; auto.
  apply regset_inject_incr with j; auto.
Qed.

Lemma match_stacks_bound invar:
  forall j s ts bound tbound bound' tbound',
  match_stacks invar j s ts bound tbound ->
  Ple bound bound' -> Ple tbound tbound' ->
  match_stacks invar j s ts bound' tbound'.
Proof.
  induction 1; intros.
- constructor; auto. eapply Ple_trans; eauto. eapply Ple_trans; eauto.
- econstructor; eauto. eapply Plt_Ple_trans; eauto. eapply Plt_Ple_trans; eauto.
Qed.

Inductive match_states: state -> state -> SimMemInjInv.t' -> Prop :=
  | match_states_regular: forall s f sp pc rs m ts tsp trs tm j
         tf (TRANF: tf = (transf_function (fun _ i => filter_instr kept i) f))
         sm0 (MCOMPAT: SimMemInjInv.mcompat sm0 m tm j)
         invar (INV: sm0.(SimMemInjInv.mem_inv_src) = invar)
         (MWF: SimMemInjInv.wf' SimMemInjInv.top_inv SimMemInjInv.top_inv sm0)
         (STACKS: match_stacks invar j s ts sp tsp)
         (KEPT: forall id, ref_function f id -> kept id)
         (SPINJ: j sp = Some(tsp, 0))
         (REGINJ: regset_inject j rs trs)
         (MEMINJ: Mem.inject j m tm),
      match_states (State s f (Vptr sp Ptrofs.zero) pc rs m)
                   (State ts tf (Vptr tsp Ptrofs.zero) pc trs tm) sm0
  | match_states_call: forall s fptr sg args m ts tfptr targs tm j
         sm0 (MCOMPAT: SimMemInjInv.mcompat sm0 m tm j)
         invar (INV: sm0.(SimMemInjInv.mem_inv_src) = invar)
         (MWF: SimMemInjInv.wf' SimMemInjInv.top_inv SimMemInjInv.top_inv sm0)
         (STACKS: match_stacks invar j s ts (Mem.nextblock m) (Mem.nextblock tm))
         (FPTR: Val.inject j fptr tfptr)
         (ARGINJ: Val.inject_list j args targs)
         (MEMINJ: Mem.inject j m tm),
      match_states (Callstate s fptr sg args m)
                   (Callstate ts tfptr sg targs tm) sm0
  | match_states_return: forall s res m ts tres tm j
         sm0 (MCOMPAT: SimMemInjInv.mcompat sm0 m tm j)
         invar (INV: sm0.(SimMemInjInv.mem_inv_src) = invar)
         (MWF: SimMemInjInv.wf' SimMemInjInv.top_inv SimMemInjInv.top_inv sm0)
         (STACKS: match_stacks invar j s ts (Mem.nextblock m) (Mem.nextblock tm))
         (RESINJ: Val.inject j res tres)
         (MEMINJ: Mem.inject j m tm),
      match_states (Returnstate s res m)
                   (Returnstate ts tres tm) sm0.

Lemma external_call_inject:
  forall ef vargs m1 t vres m2 f m1' vargs' (SYMBINJ: symbols_inject f se tse),
  external_call ef se vargs m1 t vres m2 ->
  Mem.inject f m1 m1' ->
  Val.inject_list f vargs vargs' ->
  exists f', exists vres', exists m2',
    external_call ef tse vargs' m1' t vres' m2'
    /\ Val.inject f' vres vres'
    /\ Mem.inject f' m2 m2'
    /\ Mem.unchanged_on (loc_unmapped f) m1 m2
    /\ Mem.unchanged_on (loc_out_of_reach f m1) m1' m2'
    /\ inject_incr f f'
    /\ inject_separated f f' m1 m1'.
Proof.
  intros. eapply external_call_mem_inject_gen; eauto.
Qed.

Lemma find_function_inject invar:
  forall j ros rs fptr trs,
  meminj_preserves_globals invar j ->
  find_function_ptr ge ros rs = fptr ->
  match ros with inl r => regset_inject j rs trs | inr id => kept id end ->
  exists tfptr, find_function_ptr tge ros trs = tfptr /\ Val.inject j fptr tfptr.
Proof.
  intros. inv H0. destruct ros as [r|id]; simpl in *.
- esplit; eauto.
- destruct (Genv.find_symbol ge id) as [b|] eqn:FS.
  + exploit symbols_inject_2; eauto. intros (tb & P & Q). rewrite P. eauto.
  + destruct (Genv.find_symbol tge id); eauto.
Qed.

Lemma eval_builtin_arg_inject invar:
  forall rs sp m j rs' sp' m' a v,
  eval_builtin_arg ge (fun r => rs#r) (Vptr sp Ptrofs.zero) m a v ->
  j sp = Some(sp', 0) ->
  meminj_preserves_globals invar j ->
  regset_inject j rs rs' ->
  Mem.inject j m m' ->
  (forall id, In id (globals_of_builtin_arg a) -> kept id) ->
  exists v',
     eval_builtin_arg tge (fun r => rs'#r) (Vptr sp' Ptrofs.zero) m' a v'
  /\ Val.inject j v v'.
Proof.
  induction 1; intros SP GL RS MI K; simpl in K.
- exists rs'#x; split; auto. constructor.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- simpl in H. exploit Mem.load_inject; eauto. rewrite Z.add_0_r.
  intros (v' & A & B). exists v'; auto with barg.
- econstructor; split; eauto with barg. simpl. econstructor; eauto. rewrite Ptrofs.add_zero; auto.
- assert (Val.inject j (Senv.symbol_address ge id ofs) (Senv.symbol_address tge id ofs)).
  { unfold Senv.symbol_address; simpl; unfold Genv.symbol_address.
    destruct (Genv.find_symbol ge id) as [b|] eqn:FS; auto.
    exploit symbols_inject_2; eauto. intros (b' & A & B). rewrite A.
    econstructor; eauto. rewrite Ptrofs.add_zero; auto. }
  exploit Mem.loadv_inject; eauto. intros (v' & A & B). exists v'; auto with barg.
- econstructor; split; eauto with barg.
  unfold Senv.symbol_address; simpl; unfold Genv.symbol_address.
  destruct (Genv.find_symbol ge id) as [b|] eqn:FS; auto.
  exploit symbols_inject_2; eauto. intros (b' & A & B). rewrite A.
  econstructor; eauto. rewrite Ptrofs.add_zero; auto.
- destruct IHeval_builtin_arg1 as (v1' & A1 & B1); eauto using in_or_app.
  destruct IHeval_builtin_arg2 as (v2' & A2 & B2); eauto using in_or_app.
  exists (Val.longofwords v1' v2'); split; auto with barg.
  apply Val.longofwords_inject; auto.
- destruct IHeval_builtin_arg1 as (v1' & A1 & B1); eauto using in_or_app.
  destruct IHeval_builtin_arg2 as (v2' & A2 & B2); eauto using in_or_app.
  econstructor; split; eauto with barg.
  destruct Archi.ptr64; auto using Val.add_inject, Val.addl_inject.
Qed.

Lemma eval_builtin_args_inject invar:
  forall rs sp m j rs' sp' m' al vl,
  eval_builtin_args ge (fun r => rs#r) (Vptr sp Ptrofs.zero) m al vl ->
  j sp = Some(sp', 0) ->
  meminj_preserves_globals invar j ->
  regset_inject j rs rs' ->
  Mem.inject j m m' ->
  (forall id, In id (globals_of_builtin_args al) -> kept id) ->
  exists vl',
     eval_builtin_args tge (fun r => rs'#r) (Vptr sp' Ptrofs.zero) m' al vl'
  /\ Val.inject_list j vl vl'.
Proof.
  induction 1; intros.
- exists (@nil val); split; constructor.
- simpl in H5.
  exploit eval_builtin_arg_inject; eauto using in_or_app. intros (v1' & A & B).
  destruct IHlist_forall2 as (vl' & C & D); eauto using in_or_app.
  exists (v1' :: vl'); split; constructor; auto.
Qed.

Lemma transf_function_at:
  forall f pc i,
  f.(fn_code)!pc = Some i ->
  (transf_function (fun _ i => filter_instr kept i) f).(fn_code)!pc = Some (filter_instr kept i).
Proof.
  intros.
  unfold transf_function. ss. rewrite PTree.gmap. unfold option_map. des_ifs.
Qed.

Theorem step_simulation:
  forall S1 t S2, step se ge S1 t S2 ->
  forall S1' sm0 (MS: match_states S1 S1' sm0),
  exists S2', step tse tge S1' t S2' /\ (exists sm1, match_states S2 S2' sm1 /\ <<MLE: SimMemInjInv.le' sm0 sm1>>).
Proof.
  induction 1; intros; inv MS;
    try (exploit transf_function_at; eauto; []; intro CODETGT).

- (* nop *)
  econstructor; split.
  eapply exec_Inop; eauto.
  SimMemInjInv.spl.
  econstructor; eauto.

- (* op *)
  assert (A: exists tv,
               eval_operation tge (Vptr tsp Ptrofs.zero) op trs##args tm = Some tv
            /\ Val.inject j v tv).
  { apply eval_operation_inj with (ge1 := ge) (m1 := m) (sp1 := Vptr sp0 Ptrofs.zero) (vl1 := rs##args).
    intros; eapply Mem.valid_pointer_inject_val; eauto.
    intros; eapply Mem.weak_valid_pointer_inject_val; eauto.
    intros; eapply Mem.weak_valid_pointer_inject_no_overflow; eauto.
    intros; eapply Mem.different_pointers_inject; eauto.
    intros. eapply symbol_address_inject. eapply match_stacks_preserves_globals; eauto.
    apply KEPT. red. exists pc, (Iop op args res pc'); auto.
    econstructor; eauto.
    apply regs_inject; auto.
    assumption. }
  destruct A as (tv & B & C).
  econstructor; split. eapply exec_Iop; eauto.
  SimMemInjInv.spl.
  econstructor; eauto. apply set_reg_inject; auto.

- (* load *)
  assert (A: exists ta,
               eval_addressing tge (Vptr tsp Ptrofs.zero) addr trs##args = Some ta
            /\ Val.inject j a ta).
  { apply eval_addressing_inj with (ge1 := ge) (sp1 := Vptr sp0 Ptrofs.zero) (vl1 := rs##args).
    intros. eapply symbol_address_inject. eapply match_stacks_preserves_globals; eauto.
    apply KEPT. red. exists pc, (Iload chunk addr args dst pc'); auto.
    econstructor; eauto.
    apply regs_inject; auto.
    assumption. }
  destruct A as (ta & B & C).
  exploit Mem.loadv_inject; eauto. intros (tv & D & E).
  econstructor; split. eapply exec_Iload; eauto.
  SimMemInjInv.spl.
  econstructor; eauto. apply set_reg_inject; auto.

- (* store *)
  (* destruct (Classical_Prop.classic (forall id (IN: In id (globals_addressing addr)), kept id)); *)
  (*   rename H2 into T; cycle 1. *)
  set a as AAA.
  dup H1. rename H2 into W.
  unfold Mem.storev in W. des_ifs.
  destruct (j b) eqn:V; cycle 1.
  {
    set addr as BBB.
    assert(exists gid ofs, addr = Aglobal gid ofs /\ ~ kept gid).
    { unfold eval_addressing, eval_addressing64 in *. des_ifs.
      - unfold Val.addl in *. des_ifs. destruct args; ss. clarify. clear_tac.
        hexploit (REGINJ r); eauto. intro INJ. inv INJ; ss; try congruence.
      - unfold Val.addl in *. des_ifs.
        + destruct args; ss. destruct args; ss. clarify. clear_tac.
          hexploit (REGINJ r); eauto. intro INJ. inv INJ; ss; try congruence.
          hexploit (REGINJ r0); eauto. intro INJ. inv INJ; ss; try congruence.
        + destruct args; ss. destruct args; ss. clarify. clear_tac.
          hexploit (REGINJ r); eauto. intro INJ. inv INJ; ss; try congruence.
      - unfold Val.addl, Val.mull in *. des_ifs.
      - unfold Val.addl, Val.mull in *. des_ifs.
        destruct args; ss. clarify. clear_tac.
        destruct args; ss. clarify. clear_tac.
        hexploit (REGINJ r); eauto. intro INJ. inv INJ; ss; try congruence.
      - unfold Genv.symbol_address in *. des_ifs. esplits; eauto.
        ii.
        exploit match_stacks_preserves_globals; eauto. intro GEINJ. inv GEINJ.
        exploit symbols_inject_6; eauto. i; des. clarify.
    }
    replace (filter_instr kept (Istore chunk addr args src pc')) with (Inop pc') in CODETGT; cycle 1.
    { ss. des_ifs. rewrite forallb_forall in *. des. clarify. ss. specialize (Heq gid). tauto. }
  econstructor; split.
  eapply exec_Inop; eauto.

  des.
  assert (INVAR: SimMemInjInv.mem_inv_src sm0 b).
  { unfold eval_addressing in *. des_ifs. ss. des_ifs.
    unfold Genv.symbol_address in *. des_ifs.
    exploit match_stacks_preserves_globals; eauto. intros GEINJ. inv GEINJ.
    exploit symbols_inject_8; eauto. }
  set (sm1 := (SimMemInj.mk
                 m' tm j
                 (SimMemInj.src_external sm0.(SimMemInjInv.minj))
                 (SimMemInj.tgt_external sm0.(SimMemInjInv.minj))
                 (SimMemInj.src_parent_nb sm0.(SimMemInjInv.minj))
                 (SimMemInj.tgt_parent_nb sm0.(SimMemInjInv.minj)))).
  assert (MWF1: SimMemInj.wf' sm1).
  { inv MWF. inv WF. inv MCOMPAT. econs; ss; eauto.
    - eapply Mem.store_unmapped_inject; eauto.
    - etransitivity; eauto. unfold sm1, SimMemInj.src_private.
      ss. ii. des. split; eauto. eapply Mem.store_valid_block_1; eauto.
    - etransitivity; eauto. unfold sm1, SimMemInj.tgt_private, loc_out_of_reach.
      ss. ii. des. split; eauto. ii. eapply PR; eauto.
      eapply Mem.perm_store_2; eauto.
    - eapply Mem.nextblock_store in H1. erewrite H1 in *. eauto. }
  assert (MLE1: SimMemInj.le' sm0.(SimMemInjInv.minj) sm1).
  { inv MCOMPAT. unfold sm1. econs; ss; eauto.
    - eapply Mem.store_unchanged_on; eauto.
      ii. inv MWF. exploit INVRANGESRC; eauto. i. des. eauto.
    - eapply Mem.unchanged_on_refl.
    - eapply SimMemInj.frozen_refl.
    - ii. eapply Mem.perm_store_2; eauto. }
  SimMemInjInv.spl_exact2 sm1.
  econs; ss; eauto.
  { instantiate (1:=SimMemInjInv.mem_inv_tgt sm0). destruct sm0.
    eapply SimMemInjInv.le_inj_wf_wf; eauto; ss. }
  { ss. inv MWF1. auto. }
  { econs; ss; eauto. }
  }
  assert(T: (forall id (IN: In id (globals_addressing addr)), kept id)).
  { i. destruct addr; ss. des; ss. clarify.
    unfold eval_addressing, eval_addressing64 in *. des_ifs_safe.
    destruct (kept id) eqn:U; ss.
    exploit match_stacks_preserves_globals; eauto. intro GEINJ. inv GEINJ.
    unfold Genv.symbol_address in *. des_ifs.
    destruct p0; ss.
    exploit (symbols_inject_5 id b); eauto. i; des. clarify.
  }
  replace (filter_instr kept (Istore chunk addr args src pc')) with (Istore chunk addr args src pc') in CODETGT; cycle 1.
  { ss. des_ifs. destruct addr; ss. rewrite andb_false_iff in Heq. des; ss. specialize (T i0). exploit T; eauto.
    i; des. congruence.
  }
  assert (A: exists ta,
               eval_addressing tge (Vptr tsp Ptrofs.zero) addr trs##args = Some ta
            /\ Val.inject j (Vptr b i) ta).
  { apply eval_addressing_inj with (ge1 := ge) (sp1 := Vptr sp0 Ptrofs.zero) (vl1 := rs##args).
    intros. eapply symbol_address_inject. eapply match_stacks_preserves_globals; eauto.
    eapply T; eauto.
    econstructor; eauto.
    apply regs_inject; auto.
    assumption. }
  destruct A as (ta & B & C).
  exploit Mem.storev_mapped_inject; eauto. intros (tm' & D & E).
  econstructor; split. eapply exec_Istore; eauto.
  inv MCOMPAT.
  exploit SimMemInj.storev_mapped; eauto.
  { inv MWF. eauto. } i; des.
  SimMemInjInv.spl_exact2 sm1.
  econstructor; eauto.
  { SimMemInj.compat_tac. ss. clarify. }
  { instantiate (1:=SimMemInjInv.mem_inv_tgt sm0). destruct sm0.
    eapply SimMemInjInv.le_inj_wf_wf; eauto; ss. }
  { econs; eauto. }

- (* call *)
  inversion FPTR.
  exploit find_function_inject.
  eapply match_stacks_preserves_globals; eauto. eauto.
  destruct ros as [r|id]. eauto. apply KEPT. red. econstructor; econstructor; split; eauto. simpl; auto.
  intros (tfptr & A & B).
  econstructor; split. eapply exec_Icall; eauto. constructor.
  SimMemInjInv.spl.
  econstructor; eauto.
  econstructor; eauto.
  change (Mem.valid_block m sp0). eapply Mem.valid_block_inject_1; eauto.
  change (Mem.valid_block tm tsp). eapply Mem.valid_block_inject_2; eauto.
  { rewrite H2. rewrite A. apply B. }
  apply regs_inject; auto.

- (* tailcall *)
  inversion FPTR.
  exploit find_function_inject.
  eapply match_stacks_preserves_globals; eauto. eauto.
  destruct ros as [r|id]. eauto. apply KEPT. red. econstructor; econstructor; split; eauto. simpl; auto.
  intros (tfptr & A & B).
  exploit Mem.free_parallel_inject; eauto. rewrite ! Z.add_0_r. intros (tm' & C & D).
  econstructor; split.
  eapply exec_Itailcall; eauto. constructor.
  inv MCOMPAT. dup MWF. inv MWF.
  exploit SimMemInj.free_parallel; eauto. i; des.
  eexists (SimMemInjInv.mk sm1 _ _). split.
  econstructor; ss; eauto.
  { SimMemInj.compat_tac. rewrite Z.add_0_r in FREETGT. rewrite C in FREETGT. clarify. }
  { instantiate (1:=SimMemInjInv.mem_inv_tgt sm0).
    instantiate (1:=SimMemInjInv.mem_inv_src sm0).
    destruct sm0.
    eapply SimMemInjInv.le_inj_wf_wf; eauto; ss. }
  apply match_stacks_bound with stk tsp; auto.
  apply Plt_Ple.
  change (Mem.valid_block m' stk). eapply Mem.valid_block_inject_1; eauto.
  apply Plt_Ple.
  change (Mem.valid_block tm' tsp). eapply Mem.valid_block_inject_2; eauto.
  apply regs_inject; auto.
  econs; eauto.

- (* builtin *)
  exploit eval_builtin_args_inject; eauto.
  eapply match_stacks_preserves_globals; eauto.
  intros. apply KEPT. red. econstructor; econstructor; eauto.
  intros (vargs' & P & Q).
  exploit external_call_inject; eauto.
  eapply match_stacks_symbols_inject; eauto.
  intros (j' & tv & tm' & A & B & C & D & E & F & G).
  econstructor; split.
  eapply exec_Ibuiltin; eauto.

  dup MWF. inv MWF.
  exploit SimMemInj.external_call; try by (inv MCOMPAT; eauto). i; des.
  SimMemInjInv.spl_exact2 sm1.
  eapply match_states_regular with (j := j'); eauto.
  { SimMemInj.compat_tac. }
  { instantiate (1:=SimMemInjInv.mem_inv_tgt sm0).
    instantiate (1:=SimMemInjInv.mem_inv_src sm0). destruct sm0.
    eapply SimMemInjInv.le_inj_wf_wf; ss; eauto. }
  apply match_stacks_incr with j; auto.
  intros. exploit G; eauto. intros [U V].
  assert (Mem.valid_block m sp0) by (eapply Mem.valid_block_inject_1; eauto).
  assert (Mem.valid_block tm tsp) by (eapply Mem.valid_block_inject_2; eauto).
  unfold Mem.valid_block in *; xomega.
  apply set_res_inject; auto. apply regset_inject_incr with j; auto.
  econs; ss; eauto.

- (* cond *)
  assert (C: eval_condition cond trs##args tm = Some b).
  { eapply eval_condition_inject; eauto. apply regs_inject; auto. }
  econstructor; split.
  eapply exec_Icond with (pc' := if b then ifso else ifnot); eauto.
  SimMemInjInv.spl.
  econstructor; eauto.

- (* jumptbl *)
  generalize (REGINJ arg); rewrite H0; intros INJ; inv INJ.
  econstructor; split.
  eapply exec_Ijumptable; eauto.
  SimMemInjInv.spl.
  econstructor; eauto.

- (* return *)
  exploit Mem.free_parallel_inject; eauto. rewrite ! Z.add_0_r. intros (tm' & C & D).
  econstructor; split.
  eapply exec_Ireturn; eauto.
  inv MCOMPAT. dup MWF. inv MWF.
  exploit SimMemInj.free_parallel; eauto. i; des.
  SimMemInjInv.spl_exact2 sm1.
  econstructor; eauto.
  { SimMemInjInv.compat_tac. rewrite Z.add_0_r in FREETGT. ss. congruence. }
  { instantiate (1:=SimMemInjInv.mem_inv_tgt sm0).
    instantiate (1:=SimMemInjInv.mem_inv_src sm0). destruct sm0.
    eapply SimMemInjInv.le_inj_wf_wf; eauto; ss. }
  apply match_stacks_bound with stk tsp; auto.
  apply Plt_Ple.
  change (Mem.valid_block m' stk). eapply Mem.valid_block_inject_1; eauto.
  apply Plt_Ple.
  change (Mem.valid_block tm' tsp). eapply Mem.valid_block_inject_2; eauto.
  destruct or; simpl; auto.
  econs; ss; eauto.

- (* internal function *)
  exploit Mem.alloc_parallel_inject. eauto. eauto. apply Z.le_refl. apply Z.le_refl.
  intros (j' & tm' & tstk & C & D & E & F & G).
  assert (STK: stk = Mem.nextblock m) by (eapply Mem.alloc_result; eauto).
  assert (TSTK: tstk = Mem.nextblock tm) by (eapply Mem.alloc_result; eauto).
  assert (STACKS': match_stacks (SimMemInjInv.mem_inv_src sm0) j' s ts stk tstk).
  { rewrite STK, TSTK.
    apply match_stacks_incr with j; auto.
    intros. destruct (eq_block b1 stk).
    subst b1. rewrite F in H1; inv H1. split; apply Ple_refl.
    rewrite G in H1 by auto. congruence. }
  exploit Genv.find_funct_inv; eauto. i; des. clarify. ss. des_ifs. clear_tac.
  inv FPTR0. exploit defs_inject; swap 2 3.
  { eapply match_stacks_preserves_globals. apply STACKS. }
  { apply Genv.find_funct_ptr_iff. eauto. } { eauto. }
  intros (I & J & K). clarify.
  assert (L: Ptrofs.add Ptrofs.zero (Ptrofs.repr 0) = Ptrofs.zero) by eauto.
  econstructor; split.
  eapply exec_function_internal.
  { rewrite L. rewrite Genv.find_funct_find_funct_ptr. rewrite Genv.find_funct_ptr_iff. eauto. }
  { eauto. }
  { eauto. }
  ss. dup MWF. inv MWF.
  exploit SimMemInj.alloc_parallel; eauto; try apply Z.le_refl. { inv MCOMPAT; eauto. }
  intro SM. desH SM. SimMemInjInv.spl_exact2 sm1.
  eapply match_states_regular with (j := j'); eauto.
  { inv MCOMPAT. SimMemInj.compat_tac; ss. congruence. apply Axioms.functional_extensionality. i.
    destruct (eq_block x (Mem.nextblock (SimMemInj.src sm0.(SimMemInjInv.minj)))); ss; try congruence. rewrite INJ0; ss. rewrite G; ss. }
  { eapply SimMemInjInv.le_inj_wf_wf; eauto; ss. econs; eauto. }
  apply init_regs_inject; auto. apply val_inject_list_incr with j; auto.
  econs; ss; eauto.

- (* external function *)
  exploit external_call_inject; eauto.
  eapply match_stacks_symbols_inject; eauto.
  intros (j' & tres & tm' & A & B & C & D & E & F & G).
  exploit Genv.find_funct_inv; eauto. i; des. clarify. ss. des_ifs. clear_tac.
  inv FPTR0. exploit defs_inject; swap 2 3.
  { eapply match_stacks_preserves_globals. apply STACKS. }
  { apply Genv.find_funct_ptr_iff. eauto. } { eauto. }
  intros (I & J & K). clarify.
  assert (L: Ptrofs.add Ptrofs.zero (Ptrofs.repr 0) = Ptrofs.zero) by eauto.
  econstructor; split.
  eapply exec_function_external; eauto.
  { rewrite L. rewrite Genv.find_funct_find_funct_ptr. rewrite Genv.find_funct_ptr_iff. eauto. }
  { eauto. }
  dup MWF. inv MWF.
  exploit SimMemInj.external_call; try by (inv MCOMPAT; eauto). i; des.
  SimMemInjInv.spl_exact2 sm1.
  eapply match_states_return with (j := j'); eauto.
  { SimMemInj.compat_tac. }
  { instantiate (1:=SimMemInjInv.mem_inv_tgt sm0).
    instantiate (1:=SimMemInjInv.mem_inv_src sm0). destruct sm0.
    eapply SimMemInjInv.le_inj_wf_wf; eauto; ss. }
  apply match_stacks_bound with (Mem.nextblock m) (Mem.nextblock tm).
  apply match_stacks_incr with j; auto.
  intros. exploit G; eauto. intros [P Q].
  unfold Mem.valid_block in *; xomega.
  eapply external_call_nextblock; eauto.
  eapply external_call_nextblock; eauto.
  econs; ss; eauto.

- (* return *)
  inv STACKS. econstructor; split.
  eapply exec_return.
  esplits; eauto.
  econstructor; eauto. apply set_reg_inject; auto. reflexivity.
Qed.

End CORELEMMA.

Section WHOLE.

Let ge := Genv.globalenv p.
Let tge := Genv.globalenv tp.

(** Relating [Genv.find_symbol] operations in the original and transformed program *)

Lemma transform_find_symbol_1:
  forall id b,
  Genv.find_symbol ge id = Some b -> kept id -> exists b', Genv.find_symbol tge id = Some b'.
Proof.
  intros.
  assert (A: exists g, (prog_defmap p)!id = Some g).
  { apply prog_defmap_dom. eapply Genv.find_symbol_inversion; eauto. }
  destruct A as (g & P).
  apply Genv.find_symbol_exists with (map_globdef kept g).
  apply in_prog_defmap.
  erewrite match_prog_def by eauto. r in H0. des_ifs.
  unfold option_map. des_ifs.
Qed.

Lemma transform_find_symbol_2:
  forall id b,
  Genv.find_symbol tge id = Some b -> kept id /\ exists b', Genv.find_symbol ge id = Some b'.
Proof.
  intros.
  assert (A: exists g, (prog_defmap tp)!id = Some g).
  { apply prog_defmap_dom. eapply Genv.find_symbol_inversion; eauto. }
  destruct A as (g & P).
  erewrite match_prog_def in P by eauto. des_ifs.
  split. ss.
  unfold option_map in *. des_ifs.
  apply Genv.find_symbol_exists with g0.
  apply in_prog_defmap. auto.
Qed.

Definition init_meminj : meminj :=
  fun b =>
    match Genv.invert_symbol ge b with
    | Some id =>
        match Genv.find_symbol tge id with
        | Some b' => Some (b', 0)
        | None => None
        end
    | None => None
    end.

Remark init_meminj_eq:
  forall id b b',
  Genv.find_symbol ge id = Some b -> Genv.find_symbol tge id = Some b' ->
  init_meminj b = Some(b', 0).
Proof.
  intros. unfold init_meminj. erewrite Genv.find_invert_symbol by eauto. rewrite H0. auto.
Qed.

Remark init_meminj_invert:
  forall b b' delta,
  init_meminj b = Some(b', delta) ->
  delta = 0 /\ exists id, Genv.find_symbol ge id = Some b /\ Genv.find_symbol tge id = Some b'.
Proof.
  unfold init_meminj; intros.
  destruct (Genv.invert_symbol ge b) as [id|] eqn:S; try discriminate.
  destruct (Genv.find_symbol tge id) as [b''|] eqn:F; inv H.
  split. auto. exists id. split. apply Genv.invert_find_symbol; auto. auto.
Qed.

Definition invar (b: block): Prop :=
  match Genv.invert_symbol ge b with
  | Some id =>
    match Genv.find_symbol tge id with
    | Some b' => False
    | None => True
    end
  | None => False
  end.

Lemma init_meminj_preserves_globals:
  meminj_preserves_globals ge tge invar init_meminj.
Proof.
  constructor; intros.
- exploit init_meminj_invert; eauto. intros (A & id1 & B & C).
  assert (id1 = id) by (eapply (Genv.genv_vars_inj ge); eauto). subst id1.
  esplits; auto.
  assert(GD0: exists gd_src, (prog_defmap p) ! id = Some gd_src).
  { unfold ge in *. exploit Genv.find_symbol_inversion; eauto. intro T. eapply prog_defmap_dom; eauto. }
  assert(GD1: exists gd_tgt, (prog_defmap tp) ! id = Some gd_tgt).
  { unfold tge in *. exploit Genv.find_symbol_inversion; eauto. intro T. eapply prog_defmap_dom; eauto. }
  des.
  inv TRANSF. specialize (match_prog_def0 id). rewrite GD0, GD1 in *. des_ifs.
- exploit transform_find_symbol_1; eauto. intros (b' & F). exists b'; split; auto.
  eapply init_meminj_eq; eauto.
- exploit transform_find_symbol_2; eauto. intros (K & b & F).
  exists b; split; auto. eapply init_meminj_eq; eauto.
- destruct (Genv.find_symbol tge id) eqn:FIND.
  + eapply transform_find_symbol_2 in FIND. des. clarify.
  + unfold invar. eapply Genv.find_invert_symbol in H0.
    rewrite H0. rewrite FIND. auto.
- exploit init_meminj_invert; eauto. intros (A & id & B & C).
  assert (kept id) by (eapply transform_find_symbol_2; eauto).
  assert (pm!id = Some gd).
  { unfold pm; rewrite Genv.find_def_symbol. exists b; auto. }
  assert ((prog_defmap tp)!id = Some (map_globdef kept gd)).
  { erewrite match_prog_def by eauto. des_ifs. unfold option_map, map_globdef, pm in *. des_ifs. }
  rewrite Genv.find_def_symbol in H3. destruct H3 as (b1 & P & Q).
  fold tge in P. replace b' with b1 by congruence. split; auto. split; auto.
  intros. eapply kept_closed; eauto.
- exploit init_meminj_invert; eauto. intros (A & id & B & C).
  assert ((prog_defmap tp)!id = Some gd_tgt).
  { rewrite Genv.find_def_symbol. exists b'; auto. }
  erewrite match_prog_def in H1 by eauto.
  des_ifs.
  unfold option_map in *. des_ifs. rename Heq0 into H1.
  rewrite Genv.find_def_symbol in H1. destruct H1 as (b1 & P & Q).
  fold ge in P. replace b with b1 by congruence. eauto.
- esplit; apply Genv.globalenv_public.
Unshelve.
  all: repeat (econs; eauto).
Qed.

(** Relating initial memory states *)

(*
Remark genv_find_def_exists:
  forall (F V: Type) (p: AST.program F V) b,
  Plt b (Genv.genv_next (Genv.globalenv p)) ->
  exists gd, Genv.find_def (Genv.globalenv p) b = Some gd.
Proof.
  intros until b.
  set (P := fun (g: Genv.t F V) =>
        Plt b (Genv.genv_next g) -> exists gd, (Genv.genv_defs g)!b = Some gd).
  assert (forall l g, P g -> P (Genv.add_globals g l)).
  { induction l as [ | [id1 g1] l]; simpl; intros.
  - auto.
  - apply IHl. unfold Genv.add_global, P; simpl. intros LT. apply Plt_succ_inv in LT. destruct LT.
  + rewrite PTree.gso. apply H; auto. apply Plt_ne; auto.
  + rewrite H0. rewrite PTree.gss. exists g1; auto. }
  apply H. red; simpl; intros. exfalso; xomega.
Qed.
*)

Lemma init_meminj_invert_strong:
  forall b b' delta,
  init_meminj b = Some(b', delta) ->
  delta = 0 /\
  exists id gd,
     Genv.find_symbol ge id = Some b
  /\ Genv.find_symbol tge id = Some b'
  /\ Genv.find_def ge b = Some gd
  /\ Genv.find_def tge b' = Some (map_globdef kept gd)
  /\ (forall i, ref_def gd i -> kept i).
Proof.
  intros. exploit init_meminj_invert; eauto. intros (A & id & B & C).
  assert (exists gd, (prog_defmap p)!id = Some gd).
  { apply prog_defmap_dom. eapply Genv.find_symbol_inversion; eauto. }
  destruct H0 as [gd DM]. rewrite Genv.find_def_symbol in DM.
  destruct DM as (b'' & P & Q). fold ge in P. rewrite P in B; inv B.
  fold ge in Q. exploit defs_inject. apply init_meminj_preserves_globals.
  eauto. eauto. intros (X & _ & Y).
  split. auto. exists id, gd; auto.
Qed.

Section INIT_MEM.

Variables m tm: mem.
Hypothesis IM: Genv.init_mem p = Some m.
Hypothesis TIM: Genv.init_mem tp = Some tm.

Lemma bytes_of_init_inject:
  forall il,
  (forall id, ref_init il id -> kept id) ->
  list_forall2 (memval_inject init_meminj) (Genv.bytes_of_init_data_list ge il) (Genv.bytes_of_init_data_list tge il).
Proof.
  induction il as [ | i1 il]; simpl; intros.
- constructor.
- apply list_forall2_app.
+ destruct i1; simpl; try (apply inj_bytes_inject).
  induction (Z.to_nat z); simpl; constructor. constructor. auto.
  destruct (Genv.find_symbol ge i) as [b|] eqn:FS.
  assert (kept i). { apply H. red. exists i0; auto with coqlib. }
  exploit symbols_inject_2. apply init_meminj_preserves_globals. eauto. eauto.
  intros (b' & A & B). rewrite A. apply inj_value_inject.
  econstructor; eauto. symmetry; apply Ptrofs.add_zero.
  destruct (Genv.find_symbol tge i) as [b'|] eqn:FS'.
  exploit symbols_inject_3. apply init_meminj_preserves_globals. eauto.
  intros (b & A & B). congruence.
  apply repeat_Undef_inject_self.
+ apply IHil. intros id [ofs IN]. apply H. exists ofs; auto with coqlib.
Qed.

Lemma Mem_getN_forall2:
  forall (P: memval -> memval -> Prop) c1 c2 i n p,
  list_forall2 P (Mem.getN n p c1) (Mem.getN n p c2) ->
  p <= i -> i < p + Z.of_nat n ->
  P (ZMap.get i c1) (ZMap.get i c2).
Proof.
  induction n; simpl Mem.getN; intros.
- simpl in H1. omegaContradiction.
- inv H. rewrite Nat2Z.inj_succ in H1. destruct (zeq i p0).
+ congruence.
+ apply IHn with (p0 + 1); auto. omega. omega.
Qed.

Lemma init_mem_inj_1:
  Mem.mem_inj init_meminj m tm.
Proof.
  intros; constructor; intros.
- exploit init_meminj_invert_strong; eauto. intros (A & id & gd & B & C & D & E & F).
  exploit (Genv.init_mem_characterization_gen p); eauto.
  exploit (Genv.init_mem_characterization_gen tp); eauto.
  destruct gd as [f|v]; ss.
+ destruct f; ss.
  intros (P2 & Q2) (P1 & Q1).
  apply Q1 in H0. destruct H0. subst.
  apply Mem.perm_cur. auto.
  intros (P2 & Q2) (P1 & Q1).
  apply Q1 in H0. destruct H0. subst.
  apply Mem.perm_cur. auto.
+ intros (P2 & Q2 & R2 & S2) (P1 & Q1 & R1 & S1).
  apply Q1 in H0. destruct H0. subst.
  apply Mem.perm_cur. eapply Mem.perm_implies; eauto.
  apply P2. omega.
- exploit init_meminj_invert; eauto. intros (A & id & B & C).
  subst delta. apply Z.divide_0_r.
- exploit init_meminj_invert_strong; eauto. intros (A & id & gd & B & C & D & E & F).
  exploit (Genv.init_mem_characterization_gen p); eauto.
  exploit (Genv.init_mem_characterization_gen tp); eauto.
  destruct gd as [f|v].
+ destruct f; ss.
  intros (P2 & Q2) (P1 & Q1).
  apply Q1 in H0. destruct H0; discriminate.
  intros (P2 & Q2) (P1 & Q1).
  apply Q1 in H0. destruct H0; discriminate.
+ intros (P2 & Q2 & R2 & S2) (P1 & Q1 & R1 & S1).
  apply Q1 in H0. destruct H0.
  assert (NO: gvar_volatile v = false).
  { unfold Genv.perm_globvar in H1. destruct (gvar_volatile v); auto. inv H1. }
Local Transparent Mem.loadbytes.
  generalize (S1 NO). unfold Mem.loadbytes. destruct Mem.range_perm_dec; intros E1; inv E1.
  generalize (S2 NO). unfold Mem.loadbytes. destruct Mem.range_perm_dec; intros E2; inv E2.
  rewrite Z.add_0_r.
  apply Mem_getN_forall2 with (p := 0) (n := nat_of_Z (init_data_list_size (gvar_init v))).
  rewrite H3, H4. apply bytes_of_init_inject. auto.
  omega.
  rewrite nat_of_Z_eq by (apply init_data_list_size_pos). omega.
Qed.

Lemma init_mem_inj_2:
  Mem.inject init_meminj m tm.
Proof.
  constructor; intros.
- apply init_mem_inj_1.
- destruct (init_meminj b) as [[b' delta]|] eqn:INJ; auto.
  elim H. exploit init_meminj_invert; eauto. intros (A & id & B & C).
  eapply Genv.find_symbol_not_fresh; eauto.
- exploit init_meminj_invert; eauto. intros (A & id & B & C).
  eapply Genv.find_symbol_not_fresh; eauto.
- red; intros.
  exploit init_meminj_invert. eexact H0. intros (A1 & id1 & B1 & C1).
  exploit init_meminj_invert. eexact H1. intros (A2 & id2 & B2 & C2).
  destruct (ident_eq id1 id2). congruence. left; eapply Genv.global_addresses_distinct; eauto.
- exploit init_meminj_invert; eauto. intros (A & id & B & C). subst delta.
  split. omega. generalize (Ptrofs.unsigned_range_2 ofs). omega.
- exploit init_meminj_invert_strong; eauto. intros (A & id & gd & B & C & D & E & F).
  exploit (Genv.init_mem_characterization_gen p); eauto.
  exploit (Genv.init_mem_characterization_gen tp); eauto.
  destruct gd as [f|v].
+ destruct f; ss.
  intros (P2 & Q2) (P1 & Q1).
  apply Q2 in H0. destruct H0. subst. replace ofs with 0 by omega.
  left; apply Mem.perm_cur; auto.
  intros (P2 & Q2) (P1 & Q1).
  apply Q2 in H0. destruct H0. subst. replace ofs with 0 by omega.
  left; apply Mem.perm_cur; auto.
+ intros (P2 & Q2 & R2 & S2) (P1 & Q1 & R1 & S1).
  apply Q2 in H0. destruct H0. subst.
  left. apply Mem.perm_cur. eapply Mem.perm_implies; eauto.
  apply P1. omega.
Qed.

End INIT_MEM.

Lemma init_mem_exists:
  forall m, Genv.init_mem p = Some m ->
  exists tm, Genv.init_mem tp = Some tm.
Proof.
  intros. apply Genv.init_mem_exists.
  intros.
  assert (P: (prog_defmap tp)!id = Some (Gvar v)).
  { eapply prog_defmap_norepet; eauto. eapply match_prog_unique; eauto. }
  rewrite (match_prog_def _ _ _ TRANSF) in P. des_ifs.
  unfold option_map, map_globdef in *. des_ifs.
  exploit Genv.init_mem_inversion; eauto. apply in_prog_defmap; eauto. intros [AL FV].
  split. auto.
  intros. exploit FV; eauto. intros (b & FS).
  apply transform_find_symbol_1 with b; auto.
  apply kept_closed with id (Gvar v).
  auto. auto. red. red. exists o; auto.
Qed.

Theorem init_mem_inject:
  forall m,
  Genv.init_mem p = Some m ->
  exists f tm, Genv.init_mem tp = Some tm /\ Mem.inject f m tm /\ meminj_preserves_globals ge tge invar f.
Proof.
  intros.
  exploit init_mem_exists; eauto. intros [tm INIT].
  exists init_meminj, tm.
  split. auto.
  split. eapply init_mem_inj_2; eauto.
  apply init_meminj_preserves_globals.
Qed.

Lemma transf_initial_states:
  forall S1, initial_state p S1 -> exists S2, initial_state tp S2 /\ exists sm, match_states ge tge ge tge S1 S2 sm.
Proof.
  intros. inv H. exploit init_mem_inject; eauto. intros (j & tm & A & B & C).
  exploit symbols_inject_2. eauto. eapply kept_main. eexact H1. intros (tb & P & Q).
  exists (Callstate nil (Vptr tb Ptrofs.zero) signature_main nil tm); split.
  econstructor; eauto.
  fold tge. erewrite match_prog_main by eauto. auto.
  exists (SimMemInjInv.mk (SimMemInj.mk m0 tm j bot2 bot2 (Mem.nextblock m0) (Mem.nextblock tm)) invar (fun _ => False)).
  econstructor; eauto.
  { SimMemInjInv.compat_tac. }
  { econs; ss.
    - econs; ss; eauto; try xomega.
    - ii. unfold invar in *. des_ifs. splits; ss.
      + eapply Genv.invert_find_symbol in Heq.
        destruct (j blk) eqn:BLK; auto. destruct p0.
        inv C. exploit symbols_inject_5; eauto. i. des. clarify.
      + eapply Genv.invert_find_symbol in Heq.
        eapply Genv.genv_symb_range in Heq.
        erewrite <- Genv.init_mem_genv_next; eauto. ss. }
  exploit globals_symbols_inject; eauto. intro T.
  constructor. auto.
  auto.
  erewrite <- Genv.init_mem_genv_next by eauto. apply Ple_refl.
  erewrite <- Genv.init_mem_genv_next by eauto. apply Ple_refl.
Qed.

Lemma transf_final_states:
  forall S1 S2 r,
  (exists sm, match_states ge tge ge tge S1 S2 sm) -> final_state S1 r -> final_state S2 r.
Proof.
  intros. des. inv H0. inv H. inv STACKS. inv RESINJ. constructor.
Qed.

Lemma transf_program_correct_1:
  forward_simulation (semantics p) (semantics tp).
Proof.
  intros.
  eapply forward_simulation_step with (match_states := fun s1 s2 => exists sm, match_states ge tge ge tge s1 s2 sm).
  exploit globals_symbols_inject. apply init_meminj_preserves_globals. intros [A B]. exact A.
  eexact transf_initial_states.
  eexact transf_final_states.
  { i. des. ss. exploit step_simulation; eauto. i; des; eauto. }
Qed.

End WHOLE.

End SOUNDNESS.

Theorem transf_program_correct:
  forall p tp, match_prog_weak p tp -> forward_simulation (semantics p) (semantics tp).
Proof.
  intros p tp (used & A & B & C).  apply transf_program_correct_1 with used; auto.
Qed.

(** * Commutation with linking *)

Remark link_def_either:
  forall (gd1 gd2 gd: globdef fundef unit),
  link_def gd1 gd2 = Some gd -> gd = gd1 \/ gd = gd2.
Proof with (try discriminate).
  intros until gd.
Local Transparent Linker_def Linker_fundef Linker_varinit Linker_vardef Linker_unit.
  destruct gd1 as [f1|v1], gd2 as [f2|v2]...
(* Two fundefs *)
  destruct f1 as [f1|ef1], f2 as [f2|ef2]; simpl...
  destruct ef2; intuition congruence.
  destruct ef1; intuition congruence.
  destruct (external_function_eq ef1 ef2); intuition congruence.
(* Two vardefs *)
  simpl. unfold link_vardef. destruct v1 as [info1 init1 ro1 vo1], v2 as [info2 init2 ro2 vo2]; simpl.
  destruct (link_varinit init1 init2) as [init|] eqn:LI...
  destruct (eqb ro1 ro2) eqn:RO...
  destruct (eqb vo1 vo2) eqn:VO...
  simpl.
  destruct info1, info2.
  assert (EITHER: init = init1 \/ init = init2).
  { revert LI. unfold link_varinit.
    destruct (classify_init init1), (classify_init init2); intro EQ; inv EQ; auto.
    destruct (zeq sz (Z.max sz0 0 + 0)); inv H0; auto.
    destruct (zeq sz (init_data_list_size il)); inv H0; auto.
    destruct (zeq sz (init_data_list_size il)); inv H0; auto. }
  apply eqb_prop in RO. apply eqb_prop in VO.
  intro EQ; inv EQ. destruct EITHER; subst init; auto.
Qed.

Remark used_not_defined:
  forall p used id,
  valid_used_set p used ->
  (prog_defmap p)!id = None ->
  used id = false \/ id = prog_main p.
Proof.
  intros. destruct (used id) eqn:M; auto.
  exploit used_defined; eauto using IS.mem_2. intros [A|A]; auto.
  apply prog_defmap_dom in A. destruct A as [g E]; congruence.
Qed.

Remark used_not_defined_2:
  forall p used id,
  valid_used_set p used ->
  id <> prog_main p ->
  (prog_defmap p)!id = None ->
  ~used id.
Proof.
  intros. exploit used_not_defined; eauto. intros [A|A].
  congruence.
  congruence.
Qed.

Lemma link_valid_used_set:
  forall p1 p2 p used1 used2,
  link p1 p2 = Some p ->
  valid_used_set p1 used1 ->
  valid_used_set p2 used2 ->
  valid_used_set p (fun id => used1 id || used2 id).
Proof.
  intros until used2; intros L V1 V2.
  destruct (link_prog_inv _ _ _ L) as (X & Y & Z).
  rewrite Z; clear Z; constructor; unfold is_true in *.
- intros. rewrite orb_true_iff in H. rewrite orb_true_iff.
  rewrite prog_defmap_elements, PTree.gcombine in H0.
  destruct (prog_defmap p1)!id as [gd1|] eqn:GD1;
  destruct (prog_defmap p2)!id as [gd2|] eqn:GD2;
  simpl in H0; try discriminate.
+ (* common definition *)
  exploit Y; eauto. intros (PUB1 & PUB2 & _).
  exploit link_def_either; eauto. intros [EQ|EQ]; subst gd.
* left. eapply used_closed. eexact V1. eapply used_public. eexact V1. eauto. eauto. auto.
* right. eapply used_closed. eexact V2. eapply used_public. eexact V2. eauto. eauto. auto.
+ (* left definition *)
  inv H0. destruct (used1 id) eqn:T.
* left; eapply used_closed; eauto.
* des; ss.
  exploit used_defined. eexact V2. eauto. intros [A|A].
  exploit prog_defmap_dom; eauto. intros [g E]; congruence.
  contradict T. rewrite A, <- X. intro. assert(used1 p1.(prog_main) = true) by (eapply used_main; eauto). congruence.
+ (* right definition *)
  inv H0. destruct (used2 id) eqn:T.
* right; eapply used_closed; eauto.
* des; ss.
  exploit used_defined. eexact V1. eauto. intros [A|A].
  exploit prog_defmap_dom; eauto. intros [g E]; congruence.
  contradict T. rewrite A, X. intro. assert(used2 p2.(prog_main) = true) by (eapply used_main; eauto). congruence.
+ (* no definition *)
  auto.
- simpl. rewrite orb_true_iff; left; eapply used_main; eauto.
- simpl. intros id. rewrite in_app_iff, orb_true_iff.
  intros [A|A]; [left|right]; eapply used_public; eauto.
- intros. rewrite orb_true_iff in H.
  destruct (ident_eq id (prog_main p1)).
+ right; assumption.
+ assert (E: exists g, link_prog_merge (prog_defmap p1)!id (prog_defmap p2)!id = Some g).
  { destruct (prog_defmap p1)!id as [gd1|] eqn:GD1;
    destruct (prog_defmap p2)!id as [gd2|] eqn:GD2; simpl.
  * apply Y with id; auto.
  * exists gd1; auto.
  * exists gd2; auto.
  * eapply used_not_defined_2 in GD1; eauto. eapply used_not_defined_2 in GD2; eauto.
    tauto.
    congruence.
  }
  destruct E as [g LD].
  left. unfold prog_defs_names; simpl.
  change id with (fst (id, g)). apply in_map. apply PTree.elements_correct.
  rewrite PTree.gcombine; auto.
Qed.

Lemma PTree_map_extensionality
      X Y
      (f0 f1: positive -> X -> Y)
      px
      (EQ: forall id x (IN: px ! id = Some x), f0 id x = f1 id x)
  :
    PTree.map f0 px = PTree.map f1 px
.
Proof.
  (* unfold PTree.map. *)
  (* generalize (1%positive) at 1 2 as id. *)
  (* ginduction px; intros; ss. des_ifs; ss; eauto. *)
  (* - rename x into xxx. f_equal. *)
  (*   + eapply IHpx1; eauto. i. *)
  (*     specialize (EQ (id0~0)%positive x). exploit EQ; eauto. i. *)
      (* { rewrite <- PTree.gnode'. unfold PTree.Node'. ss. des_ifs; ss. *)
      (* eapply EQ; eauto. rewrite <- PTree.gnode'. unfold PTree.Node'. des_ifs; ss. *)
      (* erewrite IHpx1. eauto. *)
Abort. (* TODO: Do this *)


Lemma PTree_map_extensionality
      X Y
      (f0 f1: X -> Y)
      px
      (EQ: forall id x (IN: px ! id = Some x), f0 x = f1 x)
  :
    PTree.map (fun _ => f0) px = PTree.map (fun _ => f1) px
.
Proof.
  unfold PTree.map.
  generalize (1%positive) at 1 2 as id.
  ginduction px; intros; ss. des_ifs; ss; eauto.
  - rename x into xxx. f_equal.
    + eapply IHpx1; eauto. i. specialize (EQ (id0~0)%positive x). eapply EQ; eauto.
    + specialize (EQ 1%positive xxx). erewrite EQ; eauto.
    + eapply IHpx2; eauto. i. specialize (EQ (id0~1)%positive x). eapply EQ; eauto.
  - f_equal.
    + erewrite IHpx1; eauto. i. specialize (EQ (id0~0)%positive x). eapply EQ; eauto.
    + erewrite IHpx2; eauto. i. specialize (EQ (id0~1)%positive x). eapply EQ; eauto.
Qed.

Ltac align_bool :=
  (repeat match goal with
          | [ H: true <> true |- _ ] => tauto
          | [ H: false <> false |- _ ] => tauto
          | [ H: true <> _ |- _ ] => symmetry in H
          | [ H: false <> _ |- _ ] => symmetry in H
          | [ H: _ <> true |- _ ] => apply not_true_is_false in H
          | [ H: _ <> false |- _ ] => apply not_false_is_true in H
          end)
.
Ltac simpl_bool := unfold Datatypes.is_true in *; unfold is_true in *; autorewrite with simpl_bool in *.
Ltac bsimpl := simpl_bool.

Lemma PTree_forallb_spec
      X (px: PTree.t X) f
  :
    (<<FORALL: PTree_forallb f px = true>>)
    <->
    (<<FORALL: forall id x (IN: px ! id = Some x), f id x = true>>)
.
Proof.
  unfold NW.
  split; ii; des.
  - rename H into FORALL.
    unfold PTree_forallb in *. rewrite PTree.fold_spec in *.
    i. exploit PTree.elements_correct; eauto. intro IN0.
    clear - FORALL IN0. rewrite <- fold_left_rev_right in FORALL. rewrite in_rev in IN0.
    abstr (rev (PTree.elements px)) xs. clear_tac.
    ginduction xs; ii; ss.
    bsimpl.
    des; ss; clarify.
    destruct a; ss. exploit IHxs; eauto.
  - rename H into FORALL.
    unfold PTree_forallb in *. rewrite PTree.fold_spec in *.
    rewrite <- fold_left_rev_right.
    assert(FORALL0: forall idx, In idx (rev (PTree.elements px)) -> f idx.(fst) idx.(snd) = true).
    { i. exploit PTree.elements_complete; eauto. destruct idx; ss.
      rewrite in_rev. ss.
    }
    clear FORALL.
    abstr (rev (PTree.elements px)) xs. clear_tac.
    ginduction xs; ii; ss.
    destruct a; ss. bsimpl. exploit FORALL0; eauto.
Qed.

Lemma addressing_zero_one
      a
  :
    ((globals_addressing a) = [] \/ exists id, (globals_addressing a) = [id])
.
Proof. destruct a; ss; eauto. Qed.

Lemma filter_instr_same
      p1 p2
      used1 used2
      (A1: valid_used_set p1 used1)
      (A2: valid_used_set p2 used2)
      (C2: check_program p2)
      (U: prog_main p1 = prog_main p2)
      (V: forall id gd1 gd2,
          (prog_defmap p1) ! id = Some gd1 ->
          (prog_defmap p2) ! id = Some gd2 ->
          In id (prog_public p1) /\
          In id (prog_public p2))
      id f2
      (GD2: (prog_defmap p2) ! id = Some (Gfun (Internal f2)))
  :
    forall id0 x (IN: (fn_code f2) ! id0 = Some x),
      filter_instr used2 x = filter_instr (fun id1 : ident => used1 id1 || used2 id1) x
.
Proof.
  i. unfold filter_instr. des_ifs.
  { hexploit (addressing_zero_one a); eauto. intro T. des; rewrite T in *; ss.
    repeat (bsimpl; des); try congruence. }
  { hexploit (addressing_zero_one a); eauto. intro T. des; rewrite T in *; ss.
    repeat (bsimpl; des); try congruence.
    assert(PRIV2: ~ In id1 p2.(prog_public)).
    { ii. inv A2. exploit used_public0; eauto. i; congruence. }
    assert(IN2: In id1 (p2.(prog_main) :: p2.(prog_defs_names))).
    { unfold check_program in C2. rewrite forallb_forall in *.
      specialize (C2 (id, (Gfun (Internal f2)))). exploit C2; eauto.
      { eapply in_prog_defmap; eauto. }
      intro TT. ss.
      eapply PTree_forallb_spec in TT; eauto.
      exploit TT; eauto. intro SPEC.
      Local Opaque in_dec.
      ss. rewrite forallb_forall in *. specialize (SPEC id1). rewrite T in *.
      exploit SPEC; eauto.
      { left; ss. }
      intro UU. des_sumbool. ss.
    }
    inv A1. exploit (used_defined0 id1); eauto. intro UU.
    ss. rewrite <- U in *.
    destruct (peq p2.(prog_main) id1).
    { inv A2. congruence. }
    des; try congruence.
    exploit prog_defmap_dom; try apply IN2; eauto. i; des.
    exploit prog_defmap_dom; try apply UU; eauto. i; des.
    exploit (V id1); eauto. i; des. ss.
  }
Qed.

Lemma check_globdef_easier
      defs0 defs1 gd
      (INCL: incl defs0 defs1)
      (CHECK: check_globdef defs0 gd = true)
  :
    <<CHECK: check_globdef defs1 gd = true>>
.
Proof.
  unfold check_globdef in *. des_ifs.
  eapply PTree_forallb_spec in CHECK.
  eapply PTree_forallb_spec.
  ii. exploit CHECK; eauto. i.
  unfold check_instr in *. des_ifs. rewrite forallb_forall in *.
  i. exploit H; eauto. i. des_sumbool. eauto.
Qed.

Lemma in_prog_defmap_exists
      (p: program) id g
      (IN: In (id, g) (prog_defs p))
  :
    exists g, (prog_defmap p) ! id = Some g
.
Proof.
  unfold prog_defmap. abstr (prog_defs p) idgs. clear_tac.
  eapply PTree_Properties.of_list_dom; eauto.
  rewrite in_map_iff. esplits; eauto. ss.
Qed.

Theorem link_match_program:
  forall p1 p2 tp1 tp2 p,
  link p1 p2 = Some p ->
  match_prog_weak p1 tp1 -> match_prog_weak p2 tp2 ->
  exists tp, link tp1 tp2 = Some tp /\ match_prog_weak p tp.
Proof.
  intros. destruct H0 as (used1 & A1 & B1 & C1). destruct H1 as (used2 & A2 & B2 & C2).
  destruct (link_prog_inv _ _ _ H) as (U & V & W).
  econstructor; split.
- apply link_prog_succeeds.
+ rewrite (match_prog_main _ _ _ B1), (match_prog_main _ _ _ B2). auto.
+ intros.
  rewrite (match_prog_def _ _ _ B1) in H0.
  rewrite (match_prog_def _ _ _ B2) in H1.
  destruct (used1 id) eqn:U1; try discriminate.
  destruct (used2 id) eqn:U2; try discriminate.
  unfold option_map, map_globdef in *. des_ifs_safe.
  edestruct V as (X & Y & gd & Z); eauto.
  split. rewrite (match_prog_public _ _ _ B1); auto.
  split. rewrite (match_prog_public _ _ _ B2); auto.
  des_ifs; ss; des_ifs; try congruence.
- exists (fun id => used1 id || used2 id); split; [|split].
+ eapply link_valid_used_set; eauto.
+ rewrite W. constructor; simpl; intros.
* eapply match_prog_main; eauto.
* rewrite (match_prog_public _ _ _ B1), (match_prog_public _ _ _ B2). auto.
* rewrite ! prog_defmap_elements, !PTree.gcombine by auto.
  rewrite (match_prog_def _ _ _ B1 id), (match_prog_def _ _ _ B2 id).
{
  destruct (prog_defmap p1)!id as [gd1|] eqn:GD1;
  destruct (prog_defmap p2)!id as [gd2|] eqn:GD2.
- (* both defined *)
  exploit V; eauto. intros (PUB1 & PUB2 & _).
  assert (EQ1: used1 id = true) by (eapply used_public; eauto).
  assert (EQ2: used2 id = true) by (eapply used_public; eauto).
  rewrite EQ1, EQ2; auto.
  ss. unfold option_map, map_globdef.
  destruct gd1, gd2; ss; try (by des_ifs).
  destruct f, f0; ss; try (by des_ifs).
  + des_ifs. do 3 f_equal. unfold transf_function. f_equal.
    rename f2 into f1.
    eapply PTree_map_extensionality; eauto.
    i.
    exploit filter_instr_same; try apply GD1; try apply PUB2; eauto.
    { i. exploit V; eauto. i; des. esplits; eauto. }
    i. rewrite H0. f_equal. apply Axioms.functional_extensionality. i. apply orb_comm.
  + des_ifs. do 3 f_equal. unfold transf_function. f_equal.
    rename f2 into f2.
    eapply PTree_map_extensionality; eauto.
    clear - V A1 A2 C2 GD2 U.
    i.
    exploit (filter_instr_same p1 p2 used1 used2 A1 A2); try apply GD2; eauto.
    { i. exploit V; eauto. i; des. esplits; eauto. }
- (* left defined *)
  exploit used_not_defined; try apply GD2; eauto. intros [A|A].
  + rewrite A, orb_false_r. destruct (used1 id); auto.
    unfold option_map, map_globdef. ss.
    des_ifs. do 3 f_equal. unfold transf_function. f_equal.
    rename f0 into f1.
    eapply PTree_map_extensionality; eauto.
    i.
    exploit filter_instr_same; try apply GD1; eauto.
    { i. exploit V; eauto. i; des. esplits; eauto. }
    i. rewrite H0. f_equal. apply Axioms.functional_extensionality. i. apply orb_comm.
  + replace (used1 id) with true; cycle 1.
    { symmetry. rewrite A, <- U. eapply used_main; eauto. }
    ss. unfold map_globdef, transf_function. des_ifs; ss; try (do 4 f_equal).
    * rename f0 into f1.
      eapply PTree_map_extensionality; eauto.
      i.
      exploit filter_instr_same; try apply GD1; eauto.
      { i. exploit V; eauto. i; des. esplits; eauto. }
      i. rewrite H0. f_equal. apply Axioms.functional_extensionality. i. apply orb_comm.
    * rename f0 into f1.
      eapply PTree_map_extensionality; eauto.
      i.
      exploit filter_instr_same; try apply GD1; eauto.
      { i. exploit V; eauto. i; des. esplits; eauto. }
      i. rewrite H0. f_equal. apply Axioms.functional_extensionality. i. apply orb_comm.
- (* right defined *)
  exploit used_not_defined. eexact A1. eauto. intros [A|A].
  + rewrite A, orb_false_l. destruct (used2 id); auto.
    unfold option_map, map_globdef. ss.
    des_ifs. do 3 f_equal. unfold transf_function. f_equal.
    rename f0 into f1.
    eapply PTree_map_extensionality; eauto.
    i.
    exploit (filter_instr_same p1 p2 used1 used2 A1 A2); try apply GD2; eauto.
    { i. exploit V; eauto. i; des. esplits; eauto. }
  + replace (used2 id) with true; cycle 1.
    { symmetry. rewrite A, U. eapply used_main; eauto. }
    ss. unfold map_globdef, transf_function. des_ifs; ss; try (do 4 f_equal).
    * rename f0 into f2.
      eapply PTree_map_extensionality; eauto.
      i.
      exploit (filter_instr_same p1 p2 used1 used2 A1 A2); try apply GD2; eauto.
      { i. exploit V; eauto. i; des. esplits; eauto. }
    * rename f0 into f2.
      eapply PTree_map_extensionality; eauto.
      i.
      exploit (filter_instr_same p1 p2 used1 used2 A1 A2); try apply GD2; eauto.
      { i. exploit V; eauto. i; des. esplits; eauto. }
- (* none defined *)
  destruct (used1 id), (used2 id); auto.
}
* intros. apply PTree.elements_keys_norepet.
+ unfold check_program in *. unfold is_true in *. rewrite forallb_forall in *.
  i. rewrite W in H0. ss. destruct x. apply PTree.elements_complete in H0.
  rewrite PTree.gcombine in *; ss. unfold link_prog_merge in H0.
  destruct ((prog_defmap p1) ! i) eqn:IN1.
  * exploit C1; eauto. { eapply in_prog_defmap; eauto. } intro DEF1. ss.
    destruct g; try (by ss).
    destruct ((prog_defmap p2) ! i) eqn:IN2.
    { Local Opaque check_globdef.
      destruct g0; ss; des_ifs; ss.
      destruct f0, f1; ss; des_ifs; ss.
      - eapply check_globdef_easier; eauto. s. ii. ss. des; eauto. right.


        clear - H0 V.
        unfold prog_defs_names in *. ss. rewrite in_map_iff in *. des. clarify. destruct x; ss.
        exploit in_prog_defmap_exists; eauto. i; des.
        assert(exists gg, link_prog_merge (prog_defmap p1) ! i (prog_defmap p2) ! i = Some gg).
        { rewrite H. ss. des_ifs; eauto. exploit V; eauto. i; des. esplits; eauto. }
        des.
        eexists (_, gg). ss. esplits; eauto.
        eapply PTree.elements_correct; eauto.
        rewrite PTree.gcombine; ss.


      - exploit C2; eauto. { eapply in_prog_defmap; eauto. } intro DEF2. ss.
        eapply check_globdef_easier; eauto. s. ii. ss. rewrite U in *. des; eauto. right.


        clear - H0 V.
        unfold prog_defs_names in *. ss. rewrite in_map_iff in *. des. clarify. destruct x; ss.
        exploit in_prog_defmap_exists; eauto. i; des.
        assert(exists gg, link_prog_merge (prog_defmap p1) ! i (prog_defmap p2) ! i = Some gg).
        { rewrite H. destruct ((prog_defmap p1) ! i) eqn:T.
          - ss. exploit V; eauto. i; des. esplits; eauto.
          - ss. esplits; eauto. }
        des.
        eexists (_, gg). ss. esplits; eauto.
        eapply PTree.elements_correct; eauto.
        rewrite PTree.gcombine; ss.

    }
    clarify.
    eapply check_globdef_easier; eauto. s. ii. ss. des; eauto. right.


    clear - H0 V.
    unfold prog_defs_names in *. ss. rewrite in_map_iff in *. des. clarify. destruct x; ss.
    exploit in_prog_defmap_exists; eauto. i; des.
    assert(exists gg, link_prog_merge (prog_defmap p1) ! i (prog_defmap p2) ! i = Some gg).
    { rewrite H. ss. des_ifs; eauto. exploit V; eauto. i; des. esplits; eauto. }
    des.
    eexists (_, gg). ss. esplits; eauto.
    eapply PTree.elements_correct; eauto.
    rewrite PTree.gcombine; ss.


  * exploit C2; eauto. { eapply in_prog_defmap; eauto. } intro DEF2. ss.
    destruct g; try (by ss).
    clarify. ss.
    eapply check_globdef_easier; eauto. s. ii. ss. rewrite U in *. des; eauto. right.


    clear - H1 V.
    unfold prog_defs_names in *. ss. rewrite in_map_iff in *. des. clarify. destruct x; ss.
    exploit in_prog_defmap_exists; eauto. i; des.
    assert(exists gg, link_prog_merge (prog_defmap p1) ! i (prog_defmap p2) ! i = Some gg).
    { rewrite H. destruct ((prog_defmap p1) ! i) eqn:T.
      - ss. exploit V; eauto. i; des. esplits; eauto.
      - ss. esplits; eauto. }
    des.
    eexists (_, gg). ss. esplits; eauto.
    eapply PTree.elements_correct; eauto.
    rewrite PTree.gcombine; ss.
Qed.

Instance TransfSelectionLink : TransfLink match_prog_weak := link_match_program.