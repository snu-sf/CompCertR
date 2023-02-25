Require Import Axioms.
Require Import Classical.
Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import AST.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Ctypes.
Require Import Cop.
Require Import Csyntax.
Require Import Csem.
Require Import sflib.
Require Import Cstrategy.

(** Simulation for expressions. *)

Section STRATEGY.

Hint Resolve leftcontext_context.
Hint Constructors context contextlist.
Hint Resolve context_compose contextlist_compose.

Variable se: Senv.t.
Let rred := rred se.
Let imm_safe := imm_safe se.
Let assign_loc := assign_loc se.
Variable ge: genv.
Variable PROP: Csem.state -> Prop.
Hypothesis NOSTUCK: ~ PROP Stuckstate.

Hint Constructors context contextlist.
Hint Resolve context_compose contextlist_compose.

(** Painful inversion lemmas on particular states that are safe. *)

Section INVERSION_LEMMAS.

Variable e: env.

Fixpoint exprlist_all_values (rl: exprlist) : Prop :=
  match rl with
  | Enil => True
  | Econs (Eval v ty) rl' => exprlist_all_values rl'
  | Econs _ _ => False
  end.

Definition invert_expr_prop (a: expr) (m: mem) : Prop :=
  match a with
  | Eloc b ofs bf ty => False
  | Evar x ty =>
      exists b,
      e!x = Some(b, ty)
      \/ (e!x = None /\ Genv.find_symbol ge x = Some b)
  | Ederef (Eval v ty1) ty =>
      exists b, exists ofs, v = Vptr b ofs
  | Eaddrof (Eloc b ofs bf ty) ty' =>
      bf = Full
  | Efield (Eval v ty1) f ty =>
      exists b, exists ofs, v = Vptr b ofs /\
      match ty1 with
      | Tstruct id _ => exists co delta bf, ge.(genv_cenv)!id = Some co /\ field_offset ge f (co_members co) = Errors.OK (delta, bf)
      | Tunion id _ => exists co delta bf, ge.(genv_cenv)!id = Some co /\ union_field_offset ge f (co_members co) = Errors.OK (delta, bf)
      | _ => False
      end
  | Eval v ty => False
  | Evalof (Eloc b ofs bf ty') ty =>
      ty' = ty /\ exists t, exists v, deref_loc se ty m b ofs bf t v
  | Eunop op (Eval v1 ty1) ty =>
      exists v, sem_unary_operation op v1 ty1 m = Some v
  | Ebinop op (Eval v1 ty1) (Eval v2 ty2) ty =>
      exists v, sem_binary_operation ge op v1 ty1 v2 ty2 m = Some v
  | Ecast (Eval v1 ty1) ty =>
      exists v, sem_cast v1 ty1 ty m = Some v
  | Eseqand (Eval v1 ty1) r2 ty =>
      exists b, bool_val v1 ty1 m = Some b
  | Eseqor (Eval v1 ty1) r2 ty =>
      exists b, bool_val v1 ty1 m = Some b
  | Econdition (Eval v1 ty1) r1 r2 ty =>
      exists b, bool_val v1 ty1 m = Some b
  | Eassign (Eloc b ofs bf ty1) (Eval v2 ty2) ty =>
      exists v, exists m', exists v', exists t,
      ty = ty1 /\ sem_cast v2 ty2 ty1 m = Some v /\ assign_loc ge ty1 m b ofs bf v t m' v'
  | Eassignop op (Eloc b ofs bf ty1) (Eval v2 ty2) tyres ty =>
      exists t, exists v1,
      ty = ty1
      /\ deref_loc se ty1 m b ofs bf t v1
  | Epostincr id (Eloc b ofs bf ty1) ty =>
      exists t, exists v1,
      ty = ty1
      /\ deref_loc se ty m b ofs bf t v1
  | Ecomma (Eval v ty1) r2 ty =>
      typeof r2 = ty
  | Eparen (Eval v1 ty1) ty2 ty =>
      exists v, sem_cast v1 ty1 ty2 m = Some v
  | Ecall (Eval vf tyf) rargs ty =>
      exprlist_all_values rargs ->
      exists tyargs tyres cconv vl,
         classify_fun tyf = fun_case_f tyargs tyres cconv
      /\ DUMMY_PROP
      /\ cast_arguments m rargs tyargs vl
      /\ DUMMY_PROP
  | Ebuiltin ef tyargs rargs ty =>
      exprlist_all_values rargs ->
      exists vargs, exists t, exists vres, exists m',
         cast_arguments m rargs tyargs vargs
      /\ external_call ef se vargs m t vres m'
  | _ => True
  end.

Lemma lred_invert:
  forall l m l' m', lred ge e l m l' m' -> invert_expr_prop l m.
Proof.
  induction 1; red; auto.
  exists b; auto.
  exists b; auto.
  exists b; exists ofs; auto.
  exists b; exists ofs; split; auto. exists co, delta, bf; auto.
  exists b; exists ofs; split; auto. exists co, delta, bf; auto.
Qed.

Lemma rred_invert:
  forall r m t r' m', rred ge r m t r' m' -> invert_expr_prop r m.
Proof.
  induction 1; red; auto.
  split; auto; exists t; exists v; auto.
  exists v; auto.
  exists v; auto.
  exists v; auto.
  exists true; auto. exists false; auto.
  exists true; auto. exists false; auto.
  exists b; auto.
  exists v; exists m'; exists v'; exists t; auto.
  exists t; exists v1; auto.
  exists t; exists v1; auto.
  exists v; auto.
  intros. exists vargs; exists t; exists vres; exists m'; auto.
Qed.

Lemma callred_invert:
  forall r fptr tyf args tyret m,
  callred r m fptr tyf args tyret ->
  invert_expr_prop r m.
Proof.
  intros. inv H. simpl.
  intros. exists tyargs, tyres, cconv, args; auto.
Qed.

Scheme context_ind2 := Minimality for context Sort Prop
  with contextlist_ind2 := Minimality for contextlist Sort Prop.
Combined Scheme context_contextlist_ind from context_ind2, contextlist_ind2.

Lemma invert_expr_context:
  (forall from to C, context from to C ->
   forall a m,
   invert_expr_prop a m ->
   invert_expr_prop (C a) m)
/\(forall from C, contextlist from C ->
  forall a m,
  invert_expr_prop a m ->
  ~exprlist_all_values (C a)).
Proof.
  apply context_contextlist_ind; intros; try (exploit H0; [eauto|intros]); simpl.
  auto.
  destruct (C a); auto; contradiction.
  destruct (C a); auto; contradiction.
  destruct (C a); auto; contradiction.
  auto.
  destruct (C a); auto; contradiction.
  destruct (C a); auto; contradiction.
  destruct (C a); auto; contradiction.
  destruct e1; auto; destruct (C a); auto; contradiction.
  destruct (C a); auto; contradiction.
  destruct (C a); auto; contradiction.
  destruct (C a); auto; contradiction.
  destruct (C a); auto; contradiction.
  destruct (C a); auto; contradiction.
  destruct e1; auto; destruct (C a); auto; contradiction.
  destruct (C a); auto; contradiction.
  destruct e1; auto; destruct (C a); auto; contradiction.
  destruct (C a); auto; contradiction.
  destruct (C a); auto; contradiction.
  destruct e1; auto. intros. elim (H0 a m); auto.
  intros. elim (H0 a m); auto.
  destruct (C a); auto; contradiction.
  destruct (C a); auto; contradiction.
  red; intros. destruct (C a); auto.
  red; intros. destruct e1; auto. elim (H0 a m); auto.
Qed.

Lemma imm_safe_inv:
  forall k a m,
  imm_safe ge e k a m ->
  match a with
  | Eloc _ _ _ _ => True
  | Eval _ _ => True
  | _ => invert_expr_prop a m
  end.
Proof.
  destruct invert_expr_context as [A B].
  intros. inv H.
  auto.
  auto.
  assert (invert_expr_prop (C e0) m).
    eapply A; eauto. eapply lred_invert; eauto.
  red in H. destruct (C e0); auto; contradiction.
  assert (invert_expr_prop (C e0) m).
    eapply A; eauto. eapply rred_invert; eauto.
  red in H. destruct (C e0); auto; contradiction.
  assert (invert_expr_prop (C e0) m).
    eapply A; eauto. eapply callred_invert; eauto.
  red in H. destruct (C e0); auto; contradiction.
Qed.

Lemma safe_inv:
  forall k C f a K m,
  safe se ge PROP (ExprState f (C a) K e m) ->
  context k RV C ->
  match a with
  | Eloc _ _ _ _ => True
  | Eval _ _ => True
  | _ => invert_expr_prop a m
  end.
Proof.
  intros. eapply imm_safe_inv; eauto. eapply safe_imm_safe; eauto.
Qed.

End INVERSION_LEMMAS.

(** * Correctness of the strategy. *)

Section SIMPLE_EVAL.

Variable f: function.
Variable k: cont.
Variable e: env.
Variable m: mem.

Lemma eval_simple_steps:
   (forall a v, eval_simple_rvalue se ge e m a v ->
    forall C, context RV RV C ->
    star Csem.step se ge (ExprState f (C a) k e m)
                   E0 (ExprState f (C (Eval v (typeof a))) k e m))
/\ (forall a b ofs bf, eval_simple_lvalue se ge e m a b ofs bf ->
    forall C, context LV RV C ->
    star Csem.step se ge (ExprState f (C a) k e m)
                   E0 (ExprState f (C (Eloc b ofs bf (typeof a))) k e m)).
Proof.

Ltac Steps REC C' := eapply star_trans; [apply (REC C'); eauto | idtac | simpl; reflexivity].
Ltac FinishR := apply star_one; left; apply step_rred; eauto; simpl; try (econstructor; eauto; fail).
Ltac FinishL := apply star_one; left; apply step_lred; eauto; simpl; try (econstructor; eauto; fail).

  apply eval_simple_rvalue_lvalue_ind; intros.
(* val *)
  apply star_refl.
(* valof *)
  Steps H0 (fun x => C(Evalof x ty)). rewrite <- H1 in *. FinishR.
(* addrof *)
  Steps H0 (fun x => C(Eaddrof x ty)). FinishR.
(* unop *)
  Steps H0 (fun x => C(Eunop op x ty)). FinishR.
(* binop *)
  Steps H0 (fun x => C(Ebinop op x r2 ty)).
  Steps H2 (fun x => C(Ebinop op (Eval v1 (typeof r1)) x ty)).
  FinishR.
(* cast *)
  Steps H0 (fun x => C(Ecast x ty)). FinishR.
(* sizeof *)
  FinishR.
(* alignof *)
  FinishR.
(* loc *)
  apply star_refl.
(* var local *)
  FinishL.
(* var global *)
  FinishL.
(* deref *)
  Steps H0 (fun x => C(Ederef x ty)). FinishL.
(* field struct *)
  Steps H0 (fun x => C(Efield x f0 ty)). rewrite H1 in *. FinishL.
(* field union *)
  Steps H0 (fun x => C(Efield x f0 ty)). rewrite H1 in *. FinishL.
Qed.


Lemma eval_simple_rvalue_steps:
  forall a v, eval_simple_rvalue se ge e m a v ->
  forall C, context RV RV C ->
  star Csem.step se ge (ExprState f (C a) k e m)
                E0 (ExprState f (C (Eval v (typeof a))) k e m).
Proof (proj1 eval_simple_steps).

Lemma eval_simple_lvalue_steps:
  forall a b ofs bf, eval_simple_lvalue se ge e m a b ofs bf ->
  forall C, context LV RV C ->
  star Csem.step se ge (ExprState f (C a) k e m)
                E0 (ExprState f (C (Eloc b ofs bf (typeof a))) k e m).
Proof (proj2 eval_simple_steps).

Corollary eval_simple_rvalue_safe:
  forall C a v,
  eval_simple_rvalue se ge e m a v ->
  context RV RV C -> safe se ge PROP (ExprState f (C a) k e m) ->
  safe se ge PROP (ExprState f (C (Eval v (typeof a))) k e m).
Proof.
  intros. eapply safe_steps; eauto. eapply eval_simple_rvalue_steps; eauto.
Qed.

Corollary eval_simple_lvalue_safe:
  forall C a b ofs bf,
  eval_simple_lvalue se ge e m a b ofs bf ->
  context LV RV C -> safe se ge PROP (ExprState f (C a) k e m) ->
  safe se ge PROP (ExprState f (C (Eloc b ofs bf (typeof a))) k e m).
Proof.
  intros. eapply safe_steps; eauto. eapply eval_simple_lvalue_steps; eauto.
Qed.

Lemma simple_can_eval:
  forall a from C,
  simple a = true -> context from RV C -> safe se ge PROP (ExprState f (C a) k e m) ->
  match from with
  | LV => exists b, exists ofs, exists bf, eval_simple_lvalue se ge e m a b ofs bf
  | RV => exists v, eval_simple_rvalue se ge e m a v
  end.
Proof.
Ltac StepL REC C' a :=
  let b := fresh "b" in let ofs := fresh "ofs" in
  let E := fresh "E" in let S := fresh "SAFE" in
  exploit (REC LV C'); eauto; intros [b [ofs [bf E]]];
  assert (S: safe se ge PROP (ExprState f (C' (Eloc b ofs  bf(typeof a))) k e m)) by
    (eapply (eval_simple_lvalue_safe C'); eauto);
  simpl in S.
Ltac StepR REC C' a :=
  let v := fresh "v" in let E := fresh "E" in let S := fresh "SAFE" in
  exploit (REC RV C'); eauto; intros [v E];
  assert (S: safe se ge PROP (ExprState f (C' (Eval v (typeof a))) k e m)) by
    (eapply (eval_simple_rvalue_safe C'); eauto);
  simpl in S.

  induction a; intros from C S CTX SAFE;
  generalize (safe_expr_kind _ _ _ NOSTUCK _ _ _ _ _ _ _ CTX SAFE); intro K; subst;
  simpl in S; try discriminate; simpl.
- (* val *)
  exists v; constructor.
- (* var *)
  exploit safe_inv; eauto; simpl. intros [b A].
  exists b, Ptrofs.zero, Full.
  intuition. apply esl_var_local; auto. apply esl_var_global; auto.
- (* field *)
  StepR IHa (fun x => C(Efield x f0 ty)) a.
  exploit safe_inv. eexact SAFE0. eauto. simpl.
  intros [b [ofs [EQ TY]]]. subst v. destruct (typeof a) eqn:?; try contradiction.
  destruct TY as (co & delta & bf & CE & OFS). exists b, (Ptrofs.add ofs (Ptrofs.repr delta)), bf; eapply esl_field_struct; eauto.
  destruct TY as (co & delta & bf & CE & OFS). exists b, (Ptrofs.add ofs (Ptrofs.repr delta)), bf; eapply esl_field_union; eauto.
- (* valof *)
  destruct (andb_prop _ _ S) as [S1 S2]. clear S. rewrite negb_true_iff in S2.
  StepL IHa (fun x => C(Evalof x ty)) a.
  exploit safe_inv. eexact SAFE0. eauto. simpl. intros [TY [t [v LOAD]]].
  assert (t = E0). inv LOAD; auto. congruence. subst t.
  exists v; econstructor; eauto. congruence.
- (* deref *)
  StepR IHa (fun x => C(Ederef x ty)) a.
  exploit safe_inv. eexact SAFE0. eauto. simpl. intros [b [ofs EQ]].
  subst v. exists b, ofs, Full; econstructor; eauto.
- (* addrof *)
  StepL IHa (fun x => C(Eaddrof x ty)) a.
  exploit safe_inv. eexact SAFE0. eauto. simpl. intros EQ; subst bf.
  exists (Vptr b ofs); econstructor; eauto.
- (* unop *)
  StepR IHa (fun x => C(Eunop op x ty)) a.
  exploit safe_inv. eexact SAFE0. eauto. simpl. intros [v' EQ].
  exists v'; econstructor; eauto.
- (* binop *)
  destruct (andb_prop _ _ S) as [S1 S2]; clear S.
  StepR IHa1 (fun x => C(Ebinop op x a2 ty)) a1.
  StepR IHa2 (fun x => C(Ebinop op (Eval v (typeof a1)) x ty)) a2.
  exploit safe_inv. eexact SAFE1. eauto. simpl. intros [v' EQ].
  exists v'; econstructor; eauto.
- (* cast *)
  StepR IHa (fun x => C(Ecast x ty)) a.
  exploit safe_inv. eexact SAFE0. eauto. simpl. intros [v' CAST].
  exists v'; econstructor; eauto.
- (* sizeof *)
  econstructor; econstructor.
- (* alignof *)
  econstructor; econstructor.
- (* loc *)
  exists b, ofs, bf; constructor.
Qed.

Lemma simple_can_eval_rval:
  forall r C,
  simple r = true -> context RV RV C -> safe se ge PROP (ExprState f (C r) k e m) ->
  exists v, eval_simple_rvalue se ge e m r v
        /\ safe se ge PROP (ExprState f (C (Eval v (typeof r))) k e m).
Proof.
  intros. exploit (simple_can_eval r RV); eauto. intros [v A].
  exists v; split; auto. eapply eval_simple_rvalue_safe; eauto.
Qed.

Lemma simple_can_eval_lval:
  forall l C,
  simple l = true -> context LV RV C -> safe se ge PROP (ExprState f (C l) k e m) ->
  exists b, exists ofs, exists bf, eval_simple_lvalue se ge e m l b ofs bf
         /\ safe se ge PROP (ExprState f (C (Eloc b ofs bf (typeof l))) k e m).
Proof.
  intros. exploit (simple_can_eval l LV); eauto. intros [b [ofs [bf A]]].
  exists b; exists ofs; exists bf; split; auto. eapply eval_simple_lvalue_safe; eauto.
Qed.

Fixpoint rval_list (vl: list val) (rl: exprlist) : exprlist :=
  match vl, rl with
  | v1 :: vl', Econs r1 rl' => Econs (Eval v1 (typeof r1)) (rval_list vl' rl')
  | _, _ => Enil
  end.

Inductive eval_simple_list': exprlist -> list val -> Prop :=
  | esrl'_nil:
      eval_simple_list' Enil nil
  | esrl'_cons: forall r rl v vl,
      eval_simple_rvalue se ge e m r v ->
      eval_simple_list' rl vl ->
      eval_simple_list' (Econs r rl) (v :: vl).

Lemma eval_simple_list_implies:
  forall rl tyl vl,
  eval_simple_list se ge e m rl tyl vl ->
  exists vl', cast_arguments m (rval_list vl' rl) tyl vl /\ eval_simple_list' rl vl'.
Proof.
  induction 1.
  exists (@nil val); split. constructor. constructor.
  destruct IHeval_simple_list as [vl' [A B]].
  exists (v' :: vl'); split. constructor; auto. constructor; auto.
Qed.

Lemma can_eval_simple_list:
  forall rl vl,
  eval_simple_list' rl vl ->
  forall tyl vl',
  cast_arguments m (rval_list vl rl) tyl vl' ->
  eval_simple_list se ge e m rl tyl vl'.
Proof.
  induction 1; simpl; intros.
  inv H. constructor.
  inv H1. econstructor; eauto.
Qed.

Hint Resolve contextlist'_head contextlist'_tail.

Lemma eval_simple_list_steps:
  forall rl vl, eval_simple_list' rl vl ->
  forall C, contextlist' C ->
  star Csem.step se ge (ExprState f (C rl) k e m)
                E0 (ExprState f (C (rval_list vl rl)) k e m).
Proof.
  induction 1; intros.
(* nil *)
  apply star_refl.
(* cons *)
  eapply star_trans.
  eapply eval_simple_rvalue_steps with (C := fun x => C(Econs x rl)); eauto.
  apply IHeval_simple_list' with (C := fun x => C(Econs (Eval v (typeof r)) x)); auto.
  auto.
Qed.

Lemma simple_list_can_eval:
  forall rl C,
  simplelist rl = true ->
  contextlist' C ->
  safe se ge PROP (ExprState f (C rl) k e m) ->
  exists vl, eval_simple_list' rl vl.
Proof.
  induction rl; intros.
  econstructor; constructor.
  simpl in H. destruct (andb_prop _ _ H).
  exploit (simple_can_eval r1 RV (fun x => C(Econs x rl))); eauto.
  intros [v1 EV1].
  exploit (IHrl (fun x => C(Econs (Eval v1 (typeof r1)) x))); eauto.
  apply (eval_simple_rvalue_safe (fun x => C(Econs x rl))); eauto.
  intros [vl EVl].
  exists (v1 :: vl); constructor; auto.
Qed.

Lemma rval_list_all_values:
  forall vl rl, exprlist_all_values (rval_list vl rl).
Proof.
  induction vl; simpl; intros. auto.
  destruct rl; simpl; auto.
Qed.

End SIMPLE_EVAL.

(** Decomposition *)

Section DECOMPOSITION.

Variable f: function.
Variable k: cont.
Variable e: env.
Variable m: mem.

Definition simple_side_effect (r: expr) : Prop :=
  match r with
  | Evalof l _ => simple l = true /\ type_is_volatile (typeof l) = true
  | Eseqand r1 r2 _ => simple r1 = true
  | Eseqor r1 r2 _ => simple r1 = true
  | Econdition r1 r2 r3 _ => simple r1 = true
  | Eassign l1 r2 _ => simple l1 = true /\ simple r2 = true
  | Eassignop _ l1 r2 _ _ => simple l1 = true /\ simple r2 = true
  | Epostincr _ l1 _ => simple l1 = true
  | Ecomma r1 r2 _ => simple r1 = true
  | Ecall r1 rl _ => simple r1 = true /\ simplelist rl = true
  | Ebuiltin ef tyargs rl _ => simplelist rl = true
  | Eparen r1 _ _ => simple r1 = true
  | _ => False
  end.

Scheme expr_ind2 := Induction for expr Sort Prop
  with exprlist_ind2 := Induction for exprlist Sort Prop.
Combined Scheme expr_expr_list_ind from expr_ind2, exprlist_ind2.

Hint Constructors leftcontext leftcontextlist.

Lemma decompose_expr:
  (forall a from C,
   context from RV C -> safe se ge PROP (ExprState f (C a) k e m) ->
       simple a = true
    \/ exists C', exists a', a = C' a' /\ simple_side_effect a' /\ leftcontext RV from C')
/\(forall rl C,
   contextlist' C -> safe se ge PROP (ExprState f (C rl) k e m) ->
       simplelist rl = true
    \/ exists C', exists a', rl = C' a' /\ simple_side_effect a' /\ leftcontextlist RV C').
Proof.
  apply expr_expr_list_ind; intros; simpl; auto.

Ltac Kind :=
  exploit safe_expr_kind; eauto; simpl; intros X; rewrite <- X in *; clear X.
Ltac Rec HR kind C C' :=
  destruct (HR kind (fun x => C(C' x))) as [? | [C'' [a' [D [A B]]]]];
  [eauto | eauto | auto |
   right; exists (fun x => C'(C'' x)); exists a'; rewrite D; auto].
Ltac Base :=
  right; exists (fun x => x); econstructor; split; [eauto | simpl; auto].

(* field *)
  Kind. Rec H RV C (fun x => Efield x f0 ty).
(* rvalof *)
  Kind. Rec H LV C (fun x => Evalof x ty).
  destruct (type_is_volatile (typeof l)) eqn:?.
  Base. rewrite H2; auto.
(* deref *)
  Kind. Rec H RV C (fun x => Ederef x ty).
(* addrof *)
  Kind. Rec H LV C (fun x => Eaddrof x ty).
(* unop *)
  Kind. Rec H RV C (fun x => Eunop op x ty).
(* binop *)
  Kind. Rec H RV C (fun x => Ebinop op x r2 ty). rewrite H3.
  Rec H0 RV C (fun x => Ebinop op r1 x ty).
(* cast *)
  Kind. Rec H RV C (fun x => Ecast x ty).
(* seqand *)
  Kind. Rec H RV C (fun x => Eseqand x r2 ty). Base.
(* seqor *)
  Kind. Rec H RV C (fun x => Eseqor x r2 ty). Base.
(* condition *)
  Kind. Rec H RV C (fun x => Econdition x r2 r3 ty). Base.
(* assign *)
  Kind. Rec H LV C (fun x => Eassign x r ty). Rec H0 RV C (fun x => Eassign l x ty). Base.
(* assignop *)
  Kind. Rec H LV C (fun x => Eassignop op x r tyres ty). Rec H0 RV C (fun x => Eassignop op l x tyres ty). Base.
(* postincr *)
  Kind. Rec H LV C (fun x => Epostincr id x ty). Base.
(* comma *)
  Kind. Rec H RV C (fun x => Ecomma x r2 ty). Base.
(* call *)
  Kind. Rec H RV C (fun x => Ecall x rargs ty).
  destruct (H0 (fun x => C (Ecall r1 x ty))) as [A | [C' [a' [D [A B]]]]].
    eapply contextlist'_call with (C := C) (rl0 := Enil). auto. auto.
  Base.
  right; exists (fun x => Ecall r1 (C' x) ty); exists a'. rewrite D; simpl; auto.
(* builtin *)
  Kind.
  destruct (H (fun x => C (Ebuiltin ef tyargs x ty))) as [A | [C' [a' [D [A B]]]]].
    eapply contextlist'_builtin with (C := C) (rl0 := Enil). auto. auto.
  Base.
  right; exists (fun x => Ebuiltin ef tyargs (C' x) ty); exists a'. rewrite D; simpl; auto.
(* rparen *)
  Kind. Rec H RV C (fun x => (Eparen x tycast ty)). Base.
(* cons *)
  destruct (H RV (fun x => C (Econs x rl))) as [A | [C' [a' [A [B D]]]]].
    eapply contextlist'_head; eauto. auto.
  destruct (H0 (fun x => C (Econs r1 x))) as [A' | [C' [a' [A' [B D]]]]].
    eapply contextlist'_tail; eauto. auto.
  rewrite A; rewrite A'; auto.
  right; exists (fun x => Econs r1 (C' x)); exists a'. rewrite A'; eauto.
  right; exists (fun x => Econs (C' x) rl); exists a'. rewrite A; eauto.
Qed.

Lemma decompose_topexpr:
  forall a,
  safe se ge PROP (ExprState f a k e m) ->
       simple a = true
    \/ exists C, exists a', a = C a' /\ simple_side_effect a' /\ leftcontext RV RV C.
Proof.
  intros. eapply (proj1 decompose_expr). apply ctx_top. auto.
Qed.

End DECOMPOSITION.

(** Simulation for expressions. *)

Lemma estep_simulation:
  forall S t S',
  estep se ge S t S' -> plus Csem.step se ge S t S'.
Proof.
  intros. inv H.
(* simple *)
  exploit eval_simple_rvalue_steps; eauto. simpl; intros STEPS.
  exploit star_inv; eauto. intros [[EQ1 EQ2] | A]; eauto.
  inversion EQ1. rewrite <- H2 in H1; contradiction.
(* valof volatile *)
  eapply plus_right.
  eapply eval_simple_lvalue_steps with (C := fun x => C(Evalof x (typeof l))); eauto.
  left. apply step_rred; eauto. econstructor; eauto. auto.
(* seqand true *)
  eapply plus_right.
  eapply eval_simple_rvalue_steps with (C := fun x => C(Eseqand x r2 ty)); eauto.
  left. apply step_rred; eauto. apply red_seqand_true; auto. traceEq.
(* seqand false *)
  eapply plus_right.
  eapply eval_simple_rvalue_steps with (C := fun x => C(Eseqand x r2 ty)); eauto.
  left. apply step_rred; eauto. apply red_seqand_false; auto. traceEq.
(* seqor true *)
  eapply plus_right.
  eapply eval_simple_rvalue_steps with (C := fun x => C(Eseqor x r2 ty)); eauto.
  left. apply step_rred; eauto. apply red_seqor_true; auto. traceEq.
(* seqor false *)
  eapply plus_right.
  eapply eval_simple_rvalue_steps with (C := fun x => C(Eseqor x r2 ty)); eauto.
  left. apply step_rred; eauto. apply red_seqor_false; auto. traceEq.
(* condition *)
  eapply plus_right.
  eapply eval_simple_rvalue_steps with (C := fun x => C(Econdition x r2 r3 ty)); eauto.
  left; apply step_rred; eauto. constructor; auto. auto.
(* assign *)
  eapply star_plus_trans.
  eapply eval_simple_lvalue_steps with (C := fun x => C(Eassign x r (typeof l))); eauto.
  eapply plus_right.
  eapply eval_simple_rvalue_steps with (C := fun x => C(Eassign (Eloc b ofs bf (typeof l)) x (typeof l))); eauto.
  left; apply step_rred; eauto. econstructor; eauto.
  reflexivity. auto.
(* assignop *)
  eapply star_plus_trans.
  eapply eval_simple_lvalue_steps with (C := fun x => C(Eassignop op x r tyres (typeof l))); eauto.
  eapply star_plus_trans.
  eapply eval_simple_rvalue_steps with (C := fun x => C(Eassignop op (Eloc b ofs bf (typeof l)) x tyres (typeof l))); eauto.
  eapply plus_left.
  left; apply step_rred; auto. econstructor; eauto.
  eapply star_left.
  left; apply step_rred with (C := fun x => C(Eassign (Eloc b ofs bf (typeof l)) x (typeof l))); eauto. econstructor; eauto.
  apply star_one.
  left; apply step_rred; auto. econstructor; eauto.
  reflexivity. reflexivity. reflexivity. traceEq.
(* assignop stuck *)
  eapply star_plus_trans.
  eapply eval_simple_lvalue_steps with (C := fun x => C(Eassignop op x r tyres (typeof l))); eauto.
  eapply star_plus_trans.
  eapply eval_simple_rvalue_steps with (C := fun x => C(Eassignop op (Eloc b ofs bf (typeof l)) x tyres (typeof l))); eauto.
  eapply plus_left.
  left; apply step_rred; auto. econstructor; eauto.
  destruct (sem_binary_operation ge op v1 (typeof l) v2 (typeof r) m) as [v3|] eqn:?.
  eapply star_left.
  left; apply step_rred with (C := fun x => C(Eassign (Eloc b ofs bf (typeof l)) x (typeof l))); eauto. econstructor; eauto.
  apply star_one.
  left; eapply step_stuck; eauto.
  red; intros. exploit imm_safe_inv; eauto. simpl. intros [v4' [m' [v' [t' [A [B D]]]]]].
  rewrite B in H4. eelim H4; eauto.
  reflexivity.
  apply star_one.
  left; eapply step_stuck with (C := fun x => C(Eassign (Eloc b ofs bf (typeof l)) x (typeof l))); eauto.
  red; intros. exploit imm_safe_inv; eauto. simpl. intros [v3 A]. congruence.
  reflexivity.
  reflexivity. traceEq.
(* postincr *)
  eapply star_plus_trans.
  eapply eval_simple_lvalue_steps with (C := fun x => C(Epostincr id x (typeof l))); eauto.
  eapply plus_left.
  left; apply step_rred; auto. econstructor; eauto.
  eapply star_left.
  left; apply step_rred with (C := fun x => C (Ecomma (Eassign (Eloc b ofs bf (typeof l)) x (typeof l)) (Eval v1 (typeof l)) (typeof l))); eauto.
  econstructor. instantiate (1 := v2). destruct id; assumption.
  eapply star_left.
  left; apply step_rred with (C := fun x => C (Ecomma x (Eval v1 (typeof l)) (typeof l))); eauto.
  econstructor; eauto.
  apply star_one.
  left; apply step_rred; auto. econstructor; eauto.
  reflexivity. reflexivity. reflexivity. traceEq.
(* postincr stuck *)
  eapply star_plus_trans.
  eapply eval_simple_lvalue_steps with (C := fun x => C(Epostincr id x (typeof l))); eauto.
  eapply plus_left.
  left; apply step_rred; auto. econstructor; eauto.
  set (op := match id with Incr => Oadd | Decr => Osub end).
  assert (SEM: sem_binary_operation ge op v1 (typeof l) (Vint Int.one) type_int32s m =
              sem_incrdecr ge id v1 (typeof l) m).
    destruct id; auto.
  destruct (sem_incrdecr ge id v1 (typeof l) m) as [v2|].
  eapply star_left.
  left; apply step_rred with (C := fun x => C (Ecomma (Eassign (Eloc b ofs bf (typeof l)) x (typeof l)) (Eval v1 (typeof l)) (typeof l))); eauto.
  econstructor; eauto.
  apply star_one.
  left; eapply step_stuck with (C := fun x => C (Ecomma x (Eval v1 (typeof l)) (typeof l))); eauto.
  red; intros. exploit imm_safe_inv; eauto. simpl. intros [v3 [m' [v' [t' [A [B D]]]]]].
  rewrite B in H3. eelim H3; eauto.
  reflexivity.
  apply star_one.
  left; eapply step_stuck with (C := fun x => C (Ecomma (Eassign (Eloc b ofs bf (typeof l)) x (typeof l)) (Eval v1 (typeof l)) (typeof l))); eauto.
  red; intros. exploit imm_safe_inv; eauto. simpl. intros [v2 A]. congruence.
  reflexivity.
  traceEq.
(* comma *)
  eapply plus_right.
  eapply eval_simple_rvalue_steps with (C := fun x => C(Ecomma x r2 (typeof r2))); eauto.
  left; apply step_rred; eauto. econstructor; eauto. auto.
(* paren *)
  eapply plus_right; eauto.
  eapply eval_simple_rvalue_steps with (C := fun x => C(Eparen x tycast ty)); eauto.
  left; apply step_rred; eauto. econstructor; eauto. auto.
(* call *)
  exploit eval_simple_list_implies; eauto. intros [vl' [A B]].
  eapply star_plus_trans.
  eapply eval_simple_rvalue_steps with (C := fun x => C(Ecall x rargs ty)); eauto.
  eapply plus_right.
  eapply eval_simple_list_steps with (C := fun x => C(Ecall (Eval vf (typeof rf)) x ty)); eauto.
  eapply contextlist'_call with (rl0 := Enil); auto.
  left; apply Csem.step_call; eauto. econstructor; eauto.
  traceEq. auto.
(* builtin *)
  exploit eval_simple_list_implies; eauto. intros [vl' [A B]].
  eapply plus_right.
  eapply eval_simple_list_steps with (C := fun x => C(Ebuiltin ef tyargs x ty)); eauto.
  eapply contextlist'_builtin with (rl0 := Enil); auto.
  left; apply Csem.step_rred; eauto. econstructor; eauto.
  traceEq.
Qed.

Lemma can_estep:
  forall f a k e m,
  safe se ge PROP (ExprState f a k e m) ->
  match a with Eval _ _ => False | _ => True end ->
  exists t, exists S, estep se ge (ExprState f a k e m) t S.
Proof.
  intros. destruct (decompose_topexpr f k e m a H) as [A | [C [b [P [Q R]]]]].
(* simple expr *)
  exploit (simple_can_eval f k e m a RV (fun x => x)); auto. intros [v P].
  econstructor; econstructor; eapply step_expr; eauto.
(* side effect *)
  clear H0. subst a. red in Q. destruct b; try contradiction.
(* valof volatile *)
  destruct Q.
  exploit (simple_can_eval_lval f k e m b (fun x => C(Evalof x ty))); eauto.
  intros [b1 [ofs [bf [E1 S1]]]].
  exploit safe_inv. eexact S1. eauto. simpl. intros [A [t [v B]]].
  econstructor; econstructor; eapply step_rvalof_volatile; eauto. congruence.
(* seqand *)
  exploit (simple_can_eval_rval f k e m b1 (fun x => C(Eseqand x b2 ty))); eauto.
  intros [v1 [E1 S1]].
  exploit safe_inv. eexact S1. eauto. simpl. intros [b BV].
  destruct b.
  econstructor; econstructor; eapply step_seqand_true; eauto.
  econstructor; econstructor; eapply step_seqand_false; eauto.
(* seqor *)
  exploit (simple_can_eval_rval f k e m b1 (fun x => C(Eseqor x b2 ty))); eauto.
  intros [v1 [E1 S1]].
  exploit safe_inv. eexact S1. eauto. simpl. intros [b BV].
  destruct b.
  econstructor; econstructor; eapply step_seqor_true; eauto.
  econstructor; econstructor; eapply step_seqor_false; eauto.
(* condition *)
  exploit (simple_can_eval_rval f k e m b1 (fun x => C(Econdition x b2 b3 ty))); eauto.
  intros [v1 [E1 S1]].
  exploit safe_inv. eexact S1. eauto. simpl. intros [b BV].
  econstructor; econstructor. eapply step_condition; eauto.
(* assign *)
  destruct Q.
  exploit (simple_can_eval_lval f k e m b1 (fun x => C(Eassign x b2 ty))); eauto.
  intros [b [ofs [bf [E1 S1]]]].
  exploit (simple_can_eval_rval f k e m b2 (fun x => C(Eassign (Eloc b ofs bf (typeof b1)) x ty))); eauto.
  intros [v [E2 S2]].
  exploit safe_inv. eexact S2. eauto. simpl. intros [v' [m' [v'' [t [A [B D]]]]]].
  econstructor; econstructor; eapply step_assign; eauto.
(* assignop *)
  destruct Q.
  exploit (simple_can_eval_lval f k e m b1 (fun x => C(Eassignop op x b2 tyres ty))); eauto.
  intros [b [ofs [bf [E1 S1]]]].
  exploit (simple_can_eval_rval f k e m b2 (fun x => C(Eassignop op (Eloc b ofs bf (typeof b1)) x tyres ty))); eauto.
  intros [v [E2 S2]].
  exploit safe_inv. eexact S2. eauto. simpl. intros [t1 [v1 [A B]]].
  destruct (sem_binary_operation ge op v1 (typeof b1) v (typeof b2) m) as [v3|] eqn:?.
  destruct (sem_cast v3 tyres (typeof b1) m) as [v4|] eqn:?.
  destruct (classic (exists t2, exists m', exists v', assign_loc ge (typeof b1) m b ofs bf v4 t2 m' v')).
  destruct H2 as [t2 [m' [v' D]]].
  econstructor; econstructor; eapply step_assignop; eauto.
  econstructor; econstructor; eapply step_assignop_stuck; eauto.
  rewrite Heqo. rewrite Heqo0. intros; red; intros. elim H2. exists t2; exists m'; exists v'; auto.
  econstructor; econstructor; eapply step_assignop_stuck; eauto.
  rewrite Heqo. rewrite Heqo0. auto.
  econstructor; econstructor; eapply step_assignop_stuck; eauto.
  rewrite Heqo. auto.
(* postincr *)
  exploit (simple_can_eval_lval f k e m b (fun x => C(Epostincr id x ty))); eauto.
  intros [b1 [ofs [bf [E1 S1]]]].
  exploit safe_inv. eexact S1. eauto. simpl. intros [t [v1 [A B]]].
  destruct (sem_incrdecr ge id v1 ty m) as [v2|] eqn:?.
  destruct (sem_cast v2 (incrdecr_type ty) ty m) as [v3|] eqn:?.
  destruct (classic (exists t2, exists m', exists v', assign_loc ge ty m b1 ofs bf v3 t2 m' v')).
  destruct H0 as [t2 [m' [v' D]]].
  econstructor; econstructor; eapply step_postincr; eauto.
  econstructor; econstructor; eapply step_postincr_stuck; eauto.
  rewrite Heqo. rewrite Heqo0. intros; red; intros. elim H0. unfold assign_loc. exists t2; exists m'; exists v'; congruence.
  econstructor; econstructor; eapply step_postincr_stuck; eauto.
  rewrite Heqo. rewrite Heqo0. auto.
  econstructor; econstructor; eapply step_postincr_stuck; eauto.
  rewrite Heqo. auto.
(* comma *)
  exploit (simple_can_eval_rval f k e m b1 (fun x => C(Ecomma x b2 ty))); eauto.
  intros [v1 [E1 S1]].
  exploit safe_inv. eexact S1. eauto. simpl. intros EQ.
  econstructor; econstructor; eapply step_comma; eauto.
(* call *)
  destruct Q.
  exploit (simple_can_eval_rval f k e m b (fun x => C(Ecall x rargs ty))); eauto.
  intros [vf [E1 S1]].
  pose (C' := fun x => C(Ecall (Eval vf (typeof b)) x ty)).
  assert (contextlist' C'). unfold C'; eapply contextlist'_call with (rl0 := Enil); auto.
  exploit (simple_list_can_eval f k e m rargs C'); eauto.
  intros [vl E2].
  exploit safe_inv. 2: eapply leftcontext_context; eexact R.
  eapply safe_steps. eexact S1.
  apply (eval_simple_list_steps f k e m rargs vl E2 C'); auto.
  simpl. intros X. exploit X. eapply rval_list_all_values.
  intros [tyargs [tyres [cconv [vargs [P [Q [U V]]]]]]].
  econstructor; econstructor; eapply step_call; eauto. eapply can_eval_simple_list; eauto.
(* builtin *)
  pose (C' := fun x => C(Ebuiltin ef tyargs x ty)).
  assert (contextlist' C'). unfold C'; eapply contextlist'_builtin with (rl0 := Enil); auto.
  exploit (simple_list_can_eval f k e m rargs C'); eauto.
  intros [vl E].
  exploit safe_inv. 2: eapply leftcontext_context; eexact R.
  eapply safe_steps. eexact H.
  apply (eval_simple_list_steps f k e m rargs vl E C'); auto.
  simpl. intros X. exploit X. eapply rval_list_all_values.
  intros [vargs [t [vres [m' [U V]]]]].
  econstructor; econstructor; eapply step_builtin; eauto.
  eapply can_eval_simple_list; eauto.
(* paren *)
  exploit (simple_can_eval_rval f k e m b (fun x => C(Eparen x tycast ty))); eauto.
  intros [v1 [E1 S1]].
  exploit safe_inv. eexact S1. eauto. simpl. intros [v CAST].
  econstructor; econstructor; eapply step_paren; eauto.
Qed.

(** Simulation for all states *)

Theorem step_simulation:
  forall S1 t S2,
  step se ge S1 t S2 -> plus Csem.step se ge S1 t S2.
Proof.
  intros. inv H.
  apply estep_simulation; auto.
  apply plus_one. right. auto.
Qed.

Theorem progress:
  forall S,
  safe se ge PROP S -> (exists r, final_state S r) \/ (exists t, exists S', step se ge S t S') \/ PROP S.
Proof.
  intros. exploit H. apply star_refl. intros [FIN | [[t [S' STEP]]|PP]]; [| |eauto].
  (* 1. Finished. *)
  auto.
  right. destruct STEP.
  (* 2. Expression step. *)
  assert (exists t, exists S', estep se ge S t S').
    inv H0.
    (* lred *)
    eapply can_estep; eauto. inv H2; auto.
    (* rred *)
    eapply can_estep; eauto. inv H2; auto. inv H1; auto.
    (* callred *)
    eapply can_estep; eauto. inv H2; auto. inv H1; auto.
    (* stuck *)
    exploit (H Stuckstate). apply star_one. left. econstructor; eauto.
    intros [[r F] | [[t [S' R]]|PP]]; ss. inv F. inv R. inv H0. inv H0.
  destruct H1 as [t' [S'' ESTEP]].
  left. exists t'; exists S''; left; auto.
  (* 3. Other step. *)
  left. exists t; exists S'; right; auto.
Qed.

End STRATEGY.

(** The main simulation result. *)

Theorem strategy_simulation:
  forall p, backward_simulation (Csem.semantics p) (semantics p).
Proof.
  intros.
  apply backward_simulation_plus with (match_states := fun (S1 S2: state) => S1 = S2); simpl.
(* symbols *)
  auto.
(* initial states exist *)
  intros. exists s1; auto.
(* initial states match *)
  intros. exists s2; auto.
(* final states match *)
  intros. subst s2. auto.
(* progress *)
  intros. subst s2. hexploit progress; eauto.
  { instantiate (1:= bot1). ss. }
  { ii. exploit H0; eauto. i; des; eauto. }
  { i. des; ss; eauto. }
(* simulation *)
  intros. subst s1. exists s2'; split; auto. apply step_simulation; auto.
Qed.
