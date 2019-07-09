(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** A deterministic evaluation strategy for C. *)

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

Section STRATEGY.

Variable se: Senv.t.
Let rred := rred se.
Let imm_safe := imm_safe se.
Let assign_loc := assign_loc se.
Variable ge: genv.

(** * Definition of the strategy *)

(** We now formalize a particular strategy for reducing expressions which
  is the one implemented by the CompCert compiler.  It evaluates effectful
  subexpressions first, in leftmost-innermost order, then finishes
  with the evaluation of the remaining simple expression. *)

(** Simple expressions are defined as follows. *)

Fixpoint simple (a: expr) : bool :=
  match a with
  | Eloc _ _ _ => true
  | Evar _ _ => true
  | Ederef r _ => simple r
  | Efield r _ _ => simple r
  | Eval _ _ => true
  | Evalof l _ => simple l && negb(type_is_volatile (typeof l))
  | Eaddrof l _ => simple l
  | Eunop _ r1 _ => simple r1
  | Ebinop _ r1 r2 _ => simple r1 && simple r2
  | Ecast r1 _ => simple r1
  | Eseqand _ _ _ => false
  | Eseqor _ _ _ => false
  | Econdition _ _ _ _ => false
  | Esizeof _ _ => true
  | Ealignof _ _ => true
  | Eassign _ _ _ => false
  | Eassignop _ _ _ _ _ => false
  | Epostincr _ _ _ => false
  | Ecomma _ _ _ => false
  | Ecall _ _ _ => false
  | Ebuiltin _ _ _ _ => false
  | Eparen _ _ _ => false
  end.

Fixpoint simplelist (rl: exprlist) : bool :=
  match rl with Enil => true | Econs r rl' => simple r && simplelist rl' end.

(** Simple expressions have interesting properties: their evaluations always
  terminate, are deterministic, and preserve the memory state.
  We seize this opportunity to define a big-step semantics for simple
  expressions. *)

Section SIMPLE_EXPRS.

Variable e: env.
Variable m: mem.

Inductive eval_simple_lvalue: expr -> block -> ptrofs -> Prop :=
  | esl_loc: forall b ofs ty,
      eval_simple_lvalue (Eloc b ofs ty) b ofs
  | esl_var_local: forall x ty b,
      e!x = Some(b, ty) ->
      eval_simple_lvalue (Evar x ty) b Ptrofs.zero
  | esl_var_global: forall x ty b,
      e!x = None ->
      Genv.find_symbol ge x = Some b ->
      eval_simple_lvalue (Evar x ty) b Ptrofs.zero
  | esl_deref: forall r ty b ofs,
      eval_simple_rvalue r (Vptr b ofs) ->
      eval_simple_lvalue (Ederef r ty) b ofs
  | esl_field_struct: forall r f ty b ofs id co a delta,
      eval_simple_rvalue r (Vptr b ofs) ->
      typeof r = Tstruct id a ->
      ge.(genv_cenv)!id = Some co ->
      field_offset ge f (co_members co) = OK delta ->
      eval_simple_lvalue (Efield r f ty) b (Ptrofs.add ofs (Ptrofs.repr delta))
  | esl_field_union: forall r f ty b ofs id co a,
      eval_simple_rvalue r (Vptr b ofs) ->
      typeof r = Tunion id a ->
      ge.(genv_cenv)!id = Some co ->
      eval_simple_lvalue (Efield r f ty) b ofs

with eval_simple_rvalue: expr -> val -> Prop :=
  | esr_val: forall v ty,
      eval_simple_rvalue (Eval v ty) v
  | esr_rvalof: forall b ofs l ty v,
      eval_simple_lvalue l b ofs ->
      ty = typeof l -> type_is_volatile ty = false ->
      deref_loc se ty m b ofs E0 v ->
      eval_simple_rvalue (Evalof l ty) v
  | esr_addrof: forall b ofs l ty,
      eval_simple_lvalue l b ofs ->
      eval_simple_rvalue (Eaddrof l ty) (Vptr b ofs)
  | esr_unop: forall op r1 ty v1 v,
      eval_simple_rvalue r1 v1 ->
      sem_unary_operation op v1 (typeof r1) m = Some v ->
      eval_simple_rvalue (Eunop op r1 ty) v
  | esr_binop: forall op r1 r2 ty v1 v2 v,
      eval_simple_rvalue r1 v1 -> eval_simple_rvalue r2 v2 ->
      sem_binary_operation ge op v1 (typeof r1) v2 (typeof r2) m = Some v ->
      eval_simple_rvalue (Ebinop op r1 r2 ty) v
  | esr_cast: forall ty r1 v1 v,
      eval_simple_rvalue r1 v1 ->
      sem_cast v1 (typeof r1) ty m = Some v ->
      eval_simple_rvalue (Ecast r1 ty) v
  | esr_sizeof: forall ty1 ty,
      eval_simple_rvalue (Esizeof ty1 ty) (Vptrofs (Ptrofs.repr (sizeof ge ty1)))
  | esr_alignof: forall ty1 ty,
      eval_simple_rvalue (Ealignof ty1 ty) (Vptrofs (Ptrofs.repr (alignof ge ty1))).

Inductive eval_simple_list: exprlist -> typelist -> list val -> Prop :=
  | esrl_nil:
      eval_simple_list Enil Tnil nil
  | esrl_cons: forall r rl ty tyl v vl v',
      eval_simple_rvalue r v' -> sem_cast v' (typeof r) ty m = Some v ->
      eval_simple_list rl tyl vl ->
      eval_simple_list (Econs r rl) (Tcons ty tyl) (v :: vl).

Scheme eval_simple_rvalue_ind2 := Minimality for eval_simple_rvalue Sort Prop
  with eval_simple_lvalue_ind2 := Minimality for eval_simple_lvalue Sort Prop.
Combined Scheme eval_simple_rvalue_lvalue_ind from eval_simple_rvalue_ind2, eval_simple_lvalue_ind2.

End SIMPLE_EXPRS.

(** Left reduction contexts. These contexts allow reducing to the right
  of a binary operator only if the left subexpression is simple. *)

Inductive leftcontext: kind -> kind -> (expr -> expr) -> Prop :=
  | lctx_top: forall k,
      leftcontext k k (fun x => x)
  | lctx_deref: forall k C ty,
      leftcontext k RV C -> leftcontext k LV (fun x => Ederef (C x) ty)
  | lctx_field: forall k C f ty,
      leftcontext k RV C -> leftcontext k LV (fun x => Efield (C x) f ty)
  | lctx_rvalof: forall k C ty,
      leftcontext k LV C -> leftcontext k RV (fun x => Evalof (C x) ty)
  | lctx_addrof: forall k C ty,
      leftcontext k LV C -> leftcontext k RV (fun x => Eaddrof (C x) ty)
  | lctx_unop: forall k C op ty,
      leftcontext k RV C -> leftcontext k RV (fun x => Eunop op (C x) ty)
  | lctx_binop_left: forall k C op e2 ty,
      leftcontext k RV C -> leftcontext k RV (fun x => Ebinop op (C x) e2 ty)
  | lctx_binop_right: forall k C op e1 ty,
      simple e1 = true -> leftcontext k RV C ->
      leftcontext k RV (fun x => Ebinop op e1 (C x) ty)
  | lctx_cast: forall k C ty,
      leftcontext k RV C -> leftcontext k RV (fun x => Ecast (C x) ty)
  | lctx_seqand: forall k C r2 ty,
      leftcontext k RV C -> leftcontext k RV (fun x => Eseqand (C x) r2 ty)
  | lctx_seqor: forall k C r2 ty,
      leftcontext k RV C -> leftcontext k RV (fun x => Eseqor (C x) r2 ty)
  | lctx_condition: forall k C r2 r3 ty,
      leftcontext k RV C -> leftcontext k RV (fun x => Econdition (C x) r2 r3 ty)
  | lctx_assign_left: forall k C e2 ty,
      leftcontext k LV C -> leftcontext k RV (fun x => Eassign (C x) e2 ty)
  | lctx_assign_right: forall k C e1 ty,
      simple e1 = true -> leftcontext k RV C ->
      leftcontext k RV (fun x => Eassign e1 (C x) ty)
  | lctx_assignop_left: forall k C op e2 tyres ty,
      leftcontext k LV C -> leftcontext k RV (fun x => Eassignop op (C x) e2 tyres ty)
  | lctx_assignop_right: forall k C op e1 tyres ty,
      simple e1 = true -> leftcontext k RV C ->
      leftcontext k RV (fun x => Eassignop op e1 (C x) tyres ty)
  | lctx_postincr: forall k C id ty,
      leftcontext k LV C -> leftcontext k RV (fun x => Epostincr id (C x) ty)
  | lctx_call_left: forall k C el ty,
      leftcontext k RV C -> leftcontext k RV (fun x => Ecall (C x) el ty)
  | lctx_call_right: forall k C e1 ty,
      simple e1 = true -> leftcontextlist k C ->
      leftcontext k RV (fun x => Ecall e1 (C x) ty)
  | lctx_builtin: forall k C ef tyargs ty,
      leftcontextlist k C ->
      leftcontext k RV (fun x => Ebuiltin ef tyargs (C x) ty)
  | lctx_comma: forall k C e2 ty,
      leftcontext k RV C -> leftcontext k RV (fun x => Ecomma (C x) e2 ty)
  | lctx_paren: forall k C tycast ty,
      leftcontext k RV C -> leftcontext k RV (fun x => Eparen (C x) tycast ty)

with leftcontextlist: kind -> (expr -> exprlist) -> Prop :=
  | lctx_list_head: forall k C el,
      leftcontext k RV C -> leftcontextlist k (fun x => Econs (C x) el)
  | lctx_list_tail: forall k C e1,
      simple e1 = true -> leftcontextlist k C ->
      leftcontextlist k (fun x => Econs e1 (C x)).

Lemma leftcontext_context:
  forall k1 k2 C, leftcontext k1 k2 C -> context k1 k2 C
with leftcontextlist_contextlist:
  forall k C, leftcontextlist k C -> contextlist k C.
Proof.
  induction 1; constructor; auto.
  induction 1; constructor; auto.
Qed.

Hint Resolve leftcontext_context.

(** Strategy for reducing expressions. We reduce the leftmost innermost
  non-simple subexpression, evaluating its arguments (which are necessarily
  simple expressions) with the big-step semantics.
  If there are none, the whole expression is simple and is evaluated in
  one big step. *)

Inductive estep: state -> trace -> state -> Prop :=

  | step_expr: forall f r k e m v ty,
      eval_simple_rvalue e m r v ->
      match r with Eval _ _ => False | _ => True end ->
      ty = typeof r ->
      estep (ExprState f r k e m)
         E0 (ExprState f (Eval v ty) k e m)

  | step_rvalof_volatile: forall f C l ty k e m b ofs t v,
      leftcontext RV RV C ->
      eval_simple_lvalue e m l b ofs ->
      deref_loc se ty m b ofs t v ->
      ty = typeof l -> type_is_volatile ty = true ->
      estep (ExprState f (C (Evalof l ty)) k e m)
          t (ExprState f (C (Eval v ty)) k e m)

  | step_seqand_true: forall f C r1 r2 ty k e m v,
      leftcontext RV RV C ->
      eval_simple_rvalue e m r1 v ->
      bool_val v (typeof r1) m = Some true ->
      estep (ExprState f (C (Eseqand r1 r2 ty)) k e m)
         E0 (ExprState f (C (Eparen r2 type_bool ty)) k e m)
  | step_seqand_false: forall f C r1 r2 ty k e m v,
      leftcontext RV RV C ->
      eval_simple_rvalue e m r1 v ->
      bool_val v (typeof r1) m = Some false ->
      estep (ExprState f (C (Eseqand r1 r2 ty)) k e m)
         E0 (ExprState f (C (Eval (Vint Int.zero) ty)) k e m)

  | step_seqor_true: forall f C r1 r2 ty k e m v,
      leftcontext RV RV C ->
      eval_simple_rvalue e m r1 v ->
      bool_val v (typeof r1) m = Some true ->
      estep (ExprState f (C (Eseqor r1 r2 ty)) k e m)
         E0 (ExprState f (C (Eval (Vint Int.one) ty)) k e m)
  | step_seqor_false: forall f C r1 r2 ty k e m v,
      leftcontext RV RV C ->
      eval_simple_rvalue e m r1 v ->
      bool_val v (typeof r1) m = Some false ->
      estep (ExprState f (C (Eseqor r1 r2 ty)) k e m)
         E0 (ExprState f (C (Eparen r2 type_bool ty)) k e m)

  | step_condition: forall f C r1 r2 r3 ty k e m v b,
      leftcontext RV RV C ->
      eval_simple_rvalue e m r1 v ->
      bool_val v (typeof r1) m = Some b ->
      estep (ExprState f (C (Econdition r1 r2 r3 ty)) k e m)
         E0 (ExprState f (C (Eparen (if b then r2 else r3) ty ty)) k e m)

  | step_assign: forall f C l r ty k e m b ofs v v' t m',
      leftcontext RV RV C ->
      eval_simple_lvalue e m l b ofs ->
      eval_simple_rvalue e m r v ->
      sem_cast v (typeof r) (typeof l) m = Some v' ->
      assign_loc ge (typeof l) m b ofs v' t m' ->
      ty = typeof l ->
      estep (ExprState f (C (Eassign l r ty)) k e m)
          t (ExprState f (C (Eval v' ty)) k e m')

  | step_assignop: forall f C op l r tyres ty k e m b ofs v1 v2 v3 v4 t1 t2 m' t,
      leftcontext RV RV C ->
      eval_simple_lvalue e m l b ofs ->
      deref_loc se (typeof l) m b ofs t1 v1 ->
      eval_simple_rvalue e m r v2 ->
      sem_binary_operation ge op v1 (typeof l) v2 (typeof r) m = Some v3 ->
      sem_cast v3 tyres (typeof l) m = Some v4 ->
      assign_loc ge (typeof l) m b ofs v4 t2 m' ->
      ty = typeof l ->
      t = t1 ** t2 ->
      estep (ExprState f (C (Eassignop op l r tyres ty)) k e m)
          t (ExprState f (C (Eval v4 ty)) k e m')

  | step_assignop_stuck: forall f C op l r tyres ty k e m b ofs v1 v2 t,
      leftcontext RV RV C ->
      eval_simple_lvalue e m l b ofs ->
      deref_loc se (typeof l) m b ofs t v1 ->
      eval_simple_rvalue e m r v2 ->
      match sem_binary_operation ge op v1 (typeof l) v2 (typeof r) m with
      | None => True
      | Some v3 =>
          match sem_cast v3 tyres (typeof l) m with
          | None => True
          | Some v4 => forall t2 m', ~(assign_loc ge (typeof l) m b ofs v4 t2 m')
          end
      end ->
      ty = typeof l ->
      estep (ExprState f (C (Eassignop op l r tyres ty)) k e m)
          t Stuckstate

  | step_postincr: forall f C id l ty k e m b ofs v1 v2 v3 t1 t2 m' t,
      leftcontext RV RV C ->
      eval_simple_lvalue e m l b ofs ->
      deref_loc se ty m b ofs t1 v1 ->
      sem_incrdecr ge id v1 ty m = Some v2 ->
      sem_cast v2 (incrdecr_type ty) ty m = Some v3 ->
      assign_loc ge ty m b ofs v3 t2 m' ->
      ty = typeof l ->
      t = t1 ** t2 ->
      estep (ExprState f (C (Epostincr id l ty)) k e m)
          t (ExprState f (C (Eval v1 ty)) k e m')

  | step_postincr_stuck: forall f C id l ty k e m b ofs v1 t,
      leftcontext RV RV C ->
      eval_simple_lvalue e m l b ofs ->
      deref_loc se ty m b ofs t v1 ->
      match sem_incrdecr ge id v1 ty m with
      | None => True
      | Some v2 =>
          match sem_cast v2 (incrdecr_type ty) ty m with
          | None => True
          | Some v3 => forall t2 m', ~(assign_loc ge (typeof l) m b ofs v3 t2 m')
          end
      end ->
      ty = typeof l ->
      estep (ExprState f (C (Epostincr id l ty)) k e m)
          t Stuckstate

  | step_comma: forall f C r1 r2 ty k e m v,
      leftcontext RV RV C ->
      eval_simple_rvalue e m r1 v ->
      ty = typeof r2 ->
      estep (ExprState f (C (Ecomma r1 r2 ty)) k e m)
         E0 (ExprState f (C r2) k e m)

  | step_paren: forall f C r tycast ty k e m v1 v,
      leftcontext RV RV C ->
      eval_simple_rvalue e m r v1 ->
      sem_cast v1 (typeof r) tycast m = Some v ->
      estep (ExprState f (C (Eparen r tycast ty)) k e m)
         E0 (ExprState f (C (Eval v ty)) k e m)

  | step_call: forall f C rf rargs ty k e m targs tres cconv vf vargs,
      leftcontext RV RV C ->
      classify_fun (typeof rf) = fun_case_f targs tres cconv ->
      eval_simple_rvalue e m rf vf ->
      eval_simple_list e m rargs targs vargs ->
      DUMMY_PROP ->
      DUMMY_PROP ->
      estep (ExprState f (C (Ecall rf rargs ty)) k e m)
         E0 (Callstate vf (Tfunction targs tres cconv) vargs (Kcall f e C ty k) m)

  | step_builtin: forall f C ef tyargs rargs ty k e m vargs t vres m',
      leftcontext RV RV C ->
      eval_simple_list e m rargs tyargs vargs ->
      external_call ef se vargs m t vres m' ->
      estep (ExprState f (C (Ebuiltin ef tyargs rargs ty)) k e m)
          t (ExprState f (C (Eval vres ty)) k e m').

Definition step (S: state) (t: trace) (S': state) : Prop :=
  estep S t S' \/ sstep se ge S t S'.

(** Properties of contexts *)

Lemma context_compose:
  forall k2 k3 C2, context k2 k3 C2 ->
  forall k1 C1, context k1 k2 C1 ->
  context k1 k3 (fun x => C2(C1 x))
with contextlist_compose:
  forall k2 C2, contextlist k2 C2 ->
  forall k1 C1, context k1 k2 C1 ->
  contextlist k1 (fun x => C2(C1 x)).
Proof.
  induction 1; intros; try (constructor; eauto).
  replace (fun x => C1 x) with C1. auto. apply extensionality; auto.
  induction 1; intros; constructor; eauto.
Qed.

Hint Constructors context contextlist.
Hint Resolve context_compose contextlist_compose.

(** * Safe executions. *)

(** A state is safe according to the nondeterministic semantics
  if it cannot get stuck by doing silent transitions only. *)

Variable PROP: Csem.state -> Prop.
Hypothesis NOSTUCK: ~ PROP Stuckstate.

Definition safe (s: Csem.state) : Prop :=
  forall s', star (Csem.step) se ge s E0 s' ->
  (exists r, final_state s' r) \/ (exists t, exists s'', Csem.step se ge s' t s'') \/ PROP s'.

Lemma safe_steps:
  forall s s',
  safe s -> star (Csem.step) se ge s E0 s' -> safe s'.
Proof.
  intros; red; intros.
  eapply H. eapply star_trans; eauto.
Qed.

Lemma star_safe:
  forall s1 s2 t s3,
  safe s1 -> star Csem.step se ge s1 E0 s2 -> (safe s2 -> star Csem.step se ge s2 t s3) ->
  star Csem.step se ge s1 t s3.
Proof.
  intros. eapply star_trans; eauto. apply H1. eapply safe_steps; eauto. auto.
Qed.

Lemma plus_safe:
  forall s1 s2 t s3,
  safe s1 -> star Csem.step se ge s1 E0 s2 -> (safe s2 -> plus Csem.step se ge s2 t s3) ->
  plus Csem.step se ge s1 t s3.
Proof.
  intros. eapply star_plus_trans; eauto. apply H1. eapply safe_steps; eauto. auto.
Qed.

Lemma safe_imm_safe:
  forall f C a k e m K,
  safe (ExprState f (C a) k e m) ->
  context K RV C ->
  imm_safe ge e K a m.
Proof.
  intros. destruct (classic (imm_safe ge e K a m)); auto.
  destruct (H Stuckstate).
  apply star_one. left. econstructor; eauto.
  destruct H2 as [r F]. inv F.
  destruct H2 as [[t [s' S]]|PP]; ss. inv S. inv H2. inv H2.
Qed.

(** Safe expressions are well-formed with respect to l-values and r-values. *)

Definition expr_kind (a: expr) : kind :=
  match a with
  | Eloc _ _ _ => LV
  | Evar _ _ => LV
  | Ederef _ _ => LV
  | Efield _ _ _ => LV
  | _ => RV
  end.

Lemma lred_kind:
  forall e a m a' m', lred ge e a m a' m' -> expr_kind a = LV.
Proof.
  induction 1; auto.
Qed.

Lemma rred_kind:
  forall a m t a' m', rred ge a m t a' m' -> expr_kind a = RV.
Proof.
  induction 1; auto.
Qed.

Lemma callred_kind:
  forall a m fptr tyf args tyret, callred a m fptr tyf args tyret -> expr_kind a = RV.
Proof.
  induction 1; auto.
Qed.

Lemma context_kind:
  forall a from to C, context from to C -> expr_kind a = from -> expr_kind (C a) = to.
Proof.
  induction 1; intros; simpl; auto.
Qed.

Lemma imm_safe_kind:
  forall e k a m, imm_safe ge e k a m -> expr_kind a = k.
Proof.
  induction 1.
  auto.
  auto.
  eapply context_kind; eauto. eapply lred_kind; eauto.
  eapply context_kind; eauto. eapply rred_kind; eauto.
  eapply context_kind; eauto. eapply callred_kind; eauto.
Qed.

Lemma safe_expr_kind:
  forall from C f a k e m,
  context from RV C ->
  safe (ExprState f (C a) k e m) ->
  expr_kind a = from.
Proof.
  intros. eapply imm_safe_kind. eapply safe_imm_safe; eauto.
Qed.

Fixpoint exprlist_app (rl1 rl2: exprlist) : exprlist :=
  match rl1 with
  | Enil => rl2
  | Econs r1 rl1' => Econs r1 (exprlist_app rl1' rl2)
  end.

Lemma exprlist_app_assoc:
  forall rl2 rl3 rl1,
  exprlist_app (exprlist_app rl1 rl2) rl3 =
  exprlist_app rl1 (exprlist_app rl2 rl3).
Proof.
  induction rl1; auto. simpl. congruence.
Qed.

Inductive contextlist' : (exprlist -> expr) -> Prop :=
  | contextlist'_call: forall r1 rl0 ty C,
      context RV RV C ->
      contextlist' (fun rl => C (Ecall r1 (exprlist_app rl0 rl) ty))
  | contextlist'_builtin: forall ef tyargs rl0 ty C,
      context RV RV C ->
      contextlist' (fun rl => C (Ebuiltin ef tyargs (exprlist_app rl0 rl) ty)).

Lemma exprlist_app_context:
  forall rl1 rl2,
  contextlist RV (fun x => exprlist_app rl1 (Econs x rl2)).
Proof.
  induction rl1; simpl; intros.
  apply ctx_list_head. constructor.
  apply ctx_list_tail. auto.
Qed.

Lemma contextlist'_head:
  forall rl C,
  contextlist' C ->
  context RV RV (fun x => C (Econs x rl)).
Proof.
  intros. inv H.
  set (C' := fun x => Ecall r1 (exprlist_app rl0 (Econs x rl)) ty).
  assert (context RV RV C'). constructor. apply exprlist_app_context.
  change (context RV RV (fun x => C0 (C' x))).
  eapply context_compose; eauto.
  set (C' := fun x => Ebuiltin ef tyargs (exprlist_app rl0 (Econs x rl)) ty).
  assert (context RV RV C'). constructor. apply exprlist_app_context.
  change (context RV RV (fun x => C0 (C' x))).
  eapply context_compose; eauto.
Qed.

Lemma contextlist'_tail:
  forall r1 C,
  contextlist' C ->
  contextlist' (fun x => C (Econs r1 x)).
Proof.
  intros. inv H.
  replace (fun x => C0 (Ecall r0 (exprlist_app rl0 (Econs r1 x)) ty))
     with (fun x => C0 (Ecall r0 (exprlist_app (exprlist_app rl0 (Econs r1 Enil)) x) ty)).
  constructor. auto.
  apply extensionality; intros. f_equal. f_equal. apply exprlist_app_assoc.
  replace (fun x => C0 (Ebuiltin ef tyargs (exprlist_app rl0 (Econs r1 x)) ty))
     with (fun x => C0 (Ebuiltin ef tyargs (exprlist_app (exprlist_app rl0 (Econs r1 Enil)) x) ty)).
  constructor. auto.
  apply extensionality; intros. f_equal. f_equal. apply exprlist_app_assoc.
Qed.

Hint Resolve contextlist'_head contextlist'_tail.

End STRATEGY.

(** The semantics that follows the strategy. *)

Definition semantics (p: program) :=
  let ge := globalenv p in
  Semantics_gen step (initial_state p) final_state ge ge.

(** This semantics is receptive to changes in events. *)

Remark deref_loc_trace:
  forall ge ty m b ofs t v,
  deref_loc ge ty m b ofs t v ->
  match t with nil => True | ev :: nil => True | _ => False end.
Proof.
  intros. inv H; simpl; auto. inv H2; simpl; auto.
Qed.

Remark deref_loc_receptive:
  forall ge ty m b ofs ev1 t1 v ev2,
  deref_loc ge ty m b ofs (ev1 :: t1) v ->
  match_traces ge (ev1 :: nil) (ev2 :: nil) ->
  t1 = nil /\ exists v', deref_loc ge ty m b ofs (ev2 :: nil) v'.
Proof.
  intros.
  assert (t1 = nil). exploit deref_loc_trace; eauto. destruct t1; simpl; tauto.
  inv H. exploit volatile_load_receptive; eauto. intros [v' A].
  split; auto; exists v'; econstructor; eauto.
Qed.

Remark assign_loc_trace:
  forall se ge ty m b ofs t v m',
  assign_loc se ge ty m b ofs v t m' ->
  match t with nil => True | ev :: nil => output_event ev | _ => False end.
Proof.
  intros. inv H; simpl; auto. inv H2; simpl; auto.
Qed.

Remark assign_loc_receptive:
  forall se ge ty m b ofs ev1 t1 v m' ev2,
  assign_loc se ge ty m b ofs v (ev1 :: t1) m' ->
  match_traces se (ev1 :: nil) (ev2 :: nil) ->
  ev1 :: t1 = ev2 :: nil.
Proof.
  intros.
  assert (t1 = nil). exploit assign_loc_trace; eauto. destruct t1; simpl; tauto.
  inv H. eapply volatile_store_receptive; eauto.
Qed.

Lemma semantics_strongly_receptive:
  forall p, strongly_receptive (semantics p).
Proof.
  intros. constructor; simpl; intros.
(* receptiveness *)
  set (ge := globalenv p) in *.
  inversion H; subst.
  inv H1.
  (* valof volatile *)
  exploit deref_loc_receptive; eauto. intros [A [v' B]].
  econstructor; econstructor. left; eapply step_rvalof_volatile; eauto.
  (* assign *)
  exploit assign_loc_receptive; eauto. intro EQ; rewrite EQ in H.
  econstructor; econstructor; eauto.
  (* assignop *)
  destruct t0 as [ | ev0 t0]; simpl in H10.
  subst t2. exploit assign_loc_receptive; eauto. intros EQ; rewrite EQ in H.
  econstructor; econstructor; eauto.
  inv H10. exploit deref_loc_receptive; eauto. intros [EQ [v1' A]]. subst t0.
  destruct (sem_binary_operation ge op v1' (typeof l) v2 (typeof r) m) as [v3'|] eqn:?.
  destruct (sem_cast v3' tyres (typeof l) m) as [v4'|] eqn:?.
  destruct (classic (exists t2', exists m'', assign_loc ge ge (typeof l) m b ofs v4' t2' m'')).
  destruct H1 as [t2' [m'' P]].
  econstructor; econstructor. left; eapply step_assignop with (v1 := v1'); eauto. simpl; reflexivity.
  econstructor; econstructor. left; eapply step_assignop_stuck with (v1 := v1'); eauto.
  rewrite Heqo; rewrite Heqo0. intros; red; intros; elim H1. exists t0; exists m'0; auto.
  econstructor; econstructor. left; eapply step_assignop_stuck with (v1 := v1'); eauto.
  rewrite Heqo; rewrite Heqo0; auto.
  econstructor; econstructor. left; eapply step_assignop_stuck with (v1 := v1'); eauto.
  rewrite Heqo; auto.
  (* assignop stuck *)
  exploit deref_loc_receptive; eauto. intros [EQ [v1' A]]. subst t1.
  destruct (sem_binary_operation ge op v1' (typeof l) v2 (typeof r) m) as [v3'|] eqn:?.
  destruct (sem_cast v3' tyres (typeof l) m) as [v4'|] eqn:?.
  destruct (classic (exists t2', exists m'', assign_loc ge ge (typeof l) m b ofs v4' t2' m'')).
  destruct H1 as [t2' [m'' P]].
  econstructor; econstructor. left; eapply step_assignop with (v1 := v1'); eauto. simpl; reflexivity.
  econstructor; econstructor. left; eapply step_assignop_stuck with (v1 := v1'); eauto.
  rewrite Heqo; rewrite Heqo0. intros; red; intros; elim H1. exists t2; exists m'; auto.
  econstructor; econstructor. left; eapply step_assignop_stuck with (v1 := v1'); eauto.
  rewrite Heqo; rewrite Heqo0; auto.
  econstructor; econstructor. left; eapply step_assignop_stuck with (v1 := v1'); eauto.
  rewrite Heqo; auto.
  (* postincr *)
  destruct t0 as [ | ev0 t0]; simpl in H9.
  subst t2. exploit assign_loc_receptive; eauto. intros EQ; rewrite EQ in H.
  econstructor; econstructor; eauto.
  inv H9. exploit deref_loc_receptive; eauto. intros [EQ [v1' A]]. subst t0.
  destruct (sem_incrdecr ge id v1' (typeof l) m) as [v2'|] eqn:?.
  destruct (sem_cast v2' (incrdecr_type (typeof l)) (typeof l) m) as [v3'|] eqn:?.
  destruct (classic (exists t2', exists m'', assign_loc ge ge (typeof l) m b ofs v3' t2' m'')).
  destruct H1 as [t2' [m'' P]].
  econstructor; econstructor. left; eapply step_postincr with (v1 := v1'); eauto. simpl; reflexivity.
  econstructor; econstructor. left; eapply step_postincr_stuck with (v1 := v1'); eauto.
  rewrite Heqo; rewrite Heqo0. intros; red; intros; elim H1. exists t0; exists m'0; auto.
  econstructor; econstructor. left; eapply step_postincr_stuck with (v1 := v1'); eauto.
  rewrite Heqo; rewrite Heqo0; auto.
  econstructor; econstructor. left; eapply step_postincr_stuck with (v1 := v1'); eauto.
  rewrite Heqo; auto.
  (* postincr stuck *)
  exploit deref_loc_receptive; eauto. intros [EQ [v1' A]]. subst t1.
  destruct (sem_incrdecr ge id v1' (typeof l) m) as [v2'|] eqn:?.
  destruct (sem_cast v2' (incrdecr_type (typeof l)) (typeof l) m) as [v3'|] eqn:?.
  destruct (classic (exists t2', exists m'', assign_loc ge ge (typeof l) m b ofs v3' t2' m'')).
  destruct H1 as [t2' [m'' P]].
  econstructor; econstructor. left; eapply step_postincr with (v1 := v1'); eauto. simpl; reflexivity.
  econstructor; econstructor. left; eapply step_postincr_stuck with (v1 := v1'); eauto.
  rewrite Heqo; rewrite Heqo0. intros; red; intros; elim H1. exists t2; exists m'; auto.
  econstructor; econstructor. left; eapply step_postincr_stuck with (v1 := v1'); eauto.
  rewrite Heqo; rewrite Heqo0; auto.
  econstructor; econstructor. left; eapply step_postincr_stuck with (v1 := v1'); eauto.
  rewrite Heqo; auto.
  (* builtin *)
  exploit external_call_trace_length; eauto. destruct t1; simpl; intros.
  exploit external_call_receptive; eauto. intros [vres2 [m2 EC2]].
  econstructor; econstructor. left; eapply step_builtin; eauto.
  omegaContradiction.
  (* external calls *)
  inv H1.
  exploit external_call_trace_length; eauto. destruct t1; simpl; intros.
  exploit external_call_receptive; eauto. intros [vres2 [m2 EC2]].
  exists (Returnstate vres2 k m2); exists E0; right; econstructor; eauto.
  omegaContradiction.
(* well-behaved traces *)
  red; intros. inv H; inv H0; simpl; auto.
  (* valof volatile *)
  exploit deref_loc_trace; eauto. destruct t; auto. destruct t; tauto.
  (* assign *)
  exploit assign_loc_trace; eauto. destruct t; auto. destruct t; simpl; tauto.
  (* assignop *)
  exploit deref_loc_trace; eauto. exploit assign_loc_trace; eauto.
  destruct t1. destruct t2. simpl; auto. destruct t2; simpl; tauto.
  destruct t1. destruct t2. simpl; auto. destruct t2; simpl; tauto.
  tauto.
  (* assignop stuck *)
  exploit deref_loc_trace; eauto. destruct t; auto. destruct t; tauto.
  (* postincr *)
  exploit deref_loc_trace; eauto. exploit assign_loc_trace; eauto.
  destruct t1. destruct t2. simpl; auto. destruct t2; simpl; tauto.
  destruct t1. destruct t2. simpl; auto. destruct t2; simpl; tauto.
  tauto.
  (* postincr stuck *)
  exploit deref_loc_trace; eauto. destruct t; auto. destruct t; tauto.
  (* builtins *)
  exploit external_call_trace_length; eauto.
  destruct t; simpl; auto. destruct t; simpl; auto. intros; omegaContradiction.
  (* external calls *)
  exploit external_call_trace_length; eauto.
  destruct t; simpl; auto. destruct t; simpl; auto. intros; omegaContradiction.
Qed.

(** * A big-step semantics for CompCert C implementing the reduction strategy. *)

Section BIGSTEP.

Variable se: Senv.t.
Variable ge: genv.

(** The execution of a statement produces an ``outcome'', indicating
  how the execution terminated: either normally or prematurely
  through the execution of a [break], [continue] or [return] statement. *)

Inductive outcome: Type :=
   | Out_break: outcome                 (**r terminated by [break] *)
   | Out_continue: outcome              (**r terminated by [continue] *)
   | Out_normal: outcome                (**r terminated normally *)
   | Out_return: option (val * type) -> outcome. (**r terminated by [return] *)

Inductive out_normal_or_continue : outcome -> Prop :=
  | Out_normal_or_continue_N: out_normal_or_continue Out_normal
  | Out_normal_or_continue_C: out_normal_or_continue Out_continue.

Inductive out_break_or_return : outcome -> outcome -> Prop :=
  | Out_break_or_return_B: out_break_or_return Out_break Out_normal
  | Out_break_or_return_R: forall ov,
      out_break_or_return (Out_return ov) (Out_return ov).

Definition outcome_switch (out: outcome) : outcome :=
  match out with
  | Out_break => Out_normal
  | o => o
  end.

Definition outcome_result_value (out: outcome) (t: type) (v: val) (m: mem) : Prop :=
  match out, t with
  | Out_normal, Tvoid => v = Vundef
  | Out_return None, Tvoid => v = Vundef
  | Out_return (Some (v', ty')), ty => ty <> Tvoid /\ sem_cast v' ty' ty m = Some v
  | _, _ => False
  end.

(** [eval_expression ge e m1 a t m2 a'] describes the evaluation of the
  complex expression e.  [v] is the resulting value, [m2] the final
  memory state, and [t] the trace of input/output events performed
  during this evaluation.  *)

Let eval_simple_lvalue := eval_simple_lvalue se.
Let eval_simple_rvalue := eval_simple_rvalue se.
Let eval_simple_list := eval_simple_list se.
Let assign_loc := assign_loc se.

Inductive eval_expression: env -> mem -> expr -> trace -> mem -> val -> Prop :=
  | eval_expression_intro: forall e m a t m' a' v,
      eval_expr e m RV a t m' a' -> eval_simple_rvalue ge e m' a' v ->
      eval_expression e m a t m' v

with eval_expr: env -> mem -> kind -> expr -> trace -> mem -> expr -> Prop :=
  | eval_val: forall e m v ty,
      eval_expr e m RV (Eval v ty) E0 m (Eval v ty)
  | eval_var: forall e m x ty,
      eval_expr e m LV (Evar x ty) E0 m (Evar x ty)
  | eval_field: forall e m a t m' a' f ty,
      eval_expr e m RV a t m' a' ->
      eval_expr e m LV (Efield a f ty) t m' (Efield a' f ty)
  | eval_valof: forall e m a t m' a' ty,
      type_is_volatile (typeof a) = false ->
      eval_expr e m LV a t m' a' ->
      eval_expr e m RV (Evalof a ty) t m' (Evalof a' ty)
  | eval_valof_volatile: forall e m a t1 m' a' ty b ofs t2 v,
      type_is_volatile (typeof a) = true ->
      eval_expr e m LV a t1 m' a' ->
      eval_simple_lvalue ge e m' a' b ofs ->
      deref_loc se (typeof a) m' b ofs t2 v ->
      ty = typeof a ->
      eval_expr e m RV (Evalof a ty) (t1 ** t2) m' (Eval v ty)
  | eval_deref: forall e m a t m' a' ty,
      eval_expr e m RV a t m' a' ->
      eval_expr e m LV (Ederef a ty) t m' (Ederef a' ty)
  | eval_addrof: forall e m a t m' a' ty,
      eval_expr e m LV a t m' a' ->
      eval_expr e m RV (Eaddrof a ty) t m' (Eaddrof a' ty)
  | eval_unop: forall e m a t m' a' op ty,
      eval_expr e m RV a t m' a' ->
      eval_expr e m RV (Eunop op a ty) t m' (Eunop op a' ty)
  | eval_binop: forall e m a1 t1 m' a1' a2 t2 m'' a2' op ty,
      eval_expr e m RV a1 t1 m' a1' -> eval_expr e m' RV a2 t2 m'' a2' ->
      eval_expr e m RV (Ebinop op a1 a2 ty) (t1 ** t2) m'' (Ebinop op a1' a2' ty)
  | eval_cast: forall e m a t m' a' ty,
      eval_expr e m RV a t m' a' ->
      eval_expr e m RV (Ecast a ty) t m' (Ecast a' ty)
  | eval_seqand_true: forall e m a1 a2 ty t1 m' a1' v1 t2 m'' a2' v2 v,
      eval_expr e m RV a1 t1 m' a1' -> eval_simple_rvalue ge e m' a1' v1 ->
      bool_val v1 (typeof a1) m' = Some true ->
      eval_expr e m' RV a2 t2 m'' a2' -> eval_simple_rvalue ge e m'' a2' v2 ->
      sem_cast v2 (typeof a2) type_bool m'' = Some v ->
      eval_expr e m RV (Eseqand a1 a2 ty) (t1**t2) m'' (Eval v ty)
  | eval_seqand_false: forall e m a1 a2 ty t1 m' a1' v1,
      eval_expr e m RV a1 t1 m' a1' -> eval_simple_rvalue ge e m' a1' v1 ->
      bool_val v1 (typeof a1) m' = Some false ->
      eval_expr e m RV (Eseqand a1 a2 ty) t1 m' (Eval (Vint Int.zero) ty)
  | eval_seqor_false: forall e m a1 a2 ty t1 m' a1' v1 t2 m'' a2' v2 v,
      eval_expr e m RV a1 t1 m' a1' -> eval_simple_rvalue ge e m' a1' v1 ->
      bool_val v1 (typeof a1) m' = Some false ->
      eval_expr e m' RV a2 t2 m'' a2' -> eval_simple_rvalue ge e m'' a2' v2 ->
      sem_cast v2 (typeof a2) type_bool m'' = Some v ->
      eval_expr e m RV (Eseqor a1 a2 ty) (t1**t2) m'' (Eval v ty)
  | eval_seqor_true: forall e m a1 a2 ty t1 m' a1' v1,
      eval_expr e m RV a1 t1 m' a1' -> eval_simple_rvalue ge e m' a1' v1 ->
      bool_val v1 (typeof a1) m' = Some true ->
      eval_expr e m RV (Eseqor a1 a2 ty) t1 m' (Eval (Vint Int.one) ty)
  | eval_condition: forall e m a1 a2 a3 ty t1 m' a1' v1 t2 m'' a' v' b v,
      eval_expr e m RV a1 t1 m' a1' -> eval_simple_rvalue ge e m' a1' v1 ->
      bool_val v1 (typeof a1) m' = Some b ->
      eval_expr e m' RV (if b then a2 else a3) t2 m'' a' -> eval_simple_rvalue ge e m'' a' v' ->
      sem_cast v' (typeof (if b then a2 else a3)) ty m'' = Some v ->
      eval_expr e m RV (Econdition a1 a2 a3 ty) (t1**t2) m'' (Eval v ty)
  | eval_sizeof: forall e m ty' ty,
      eval_expr e m RV (Esizeof ty' ty) E0 m (Esizeof ty' ty)
  | eval_alignof: forall e m ty' ty,
      eval_expr e m RV (Ealignof ty' ty) E0 m (Ealignof ty' ty)
  | eval_assign: forall e m l r ty t1 m1 l' t2 m2 r' b ofs v v' t3 m3,
      eval_expr e m LV l t1 m1 l' -> eval_expr e m1 RV r t2 m2 r' ->
      eval_simple_lvalue ge e m2 l' b ofs ->
      eval_simple_rvalue ge e m2 r' v ->
      sem_cast v (typeof r) (typeof l) m2 = Some v' ->
      assign_loc ge (typeof l) m2 b ofs v' t3 m3 ->
      ty = typeof l ->
      eval_expr e m RV (Eassign l r ty) (t1**t2**t3) m3 (Eval v' ty)
  | eval_assignop: forall e m op l r tyres ty t1 m1 l' t2 m2 r' b ofs
                          v1 v2 v3 v4 t3 t4 m3,
      eval_expr e m LV l t1 m1 l' -> eval_expr e m1 RV r t2 m2 r' ->
      eval_simple_lvalue ge e m2 l' b ofs ->
      deref_loc se (typeof l) m2 b ofs t3 v1 ->
      eval_simple_rvalue ge e m2 r' v2 ->
      sem_binary_operation ge op v1 (typeof l) v2 (typeof r) m2 = Some v3 ->
      sem_cast v3 tyres (typeof l) m2 = Some v4 ->
      assign_loc ge (typeof l) m2 b ofs v4 t4 m3 ->
      ty = typeof l ->
      eval_expr e m RV (Eassignop op l r tyres ty) (t1**t2**t3**t4) m3 (Eval v4 ty)
  | eval_postincr: forall e m id l ty t1 m1 l' b ofs v1 v2 v3 m2 t2 t3,
      eval_expr e m LV l t1 m1 l' ->
      eval_simple_lvalue ge e m1 l' b ofs ->
      deref_loc se ty m1 b ofs t2 v1 ->
      sem_incrdecr ge id v1 ty m1 = Some v2 ->
      sem_cast v2 (incrdecr_type ty) ty m1 = Some v3 ->
      assign_loc ge ty m1 b ofs v3 t3 m2 ->
      ty = typeof l ->
      eval_expr e m RV (Epostincr id l ty) (t1**t2**t3) m2 (Eval v1 ty)
  | eval_comma: forall e m r1 r2 ty t1 m1 r1' v1 t2 m2 r2',
      eval_expr e m RV r1 t1 m1 r1' ->
      eval_simple_rvalue ge e m1 r1' v1 ->
      eval_expr e m1 RV r2 t2 m2 r2' ->
      ty = typeof r2 ->
      eval_expr e m RV (Ecomma r1 r2 ty) (t1**t2) m2 r2'
  | eval_call: forall e m rf rargs ty t1 m1 rf' t2 m2 rargs' vf vargs
                      targs tres cconv fd t3 m3 vres,
      eval_expr e m RV rf t1 m1 rf' -> eval_exprlist e m1 rargs t2 m2 rargs' ->
      eval_simple_rvalue ge e m2 rf' vf ->
      eval_simple_list ge e m2 rargs' targs vargs ->
      classify_fun (typeof rf) = fun_case_f targs tres cconv ->
      Genv.find_funct ge vf = Some fd ->
      type_of_fundef fd = Tfunction targs tres cconv ->
      eval_funcall m2 fd vargs t3 m3 vres ->
      eval_expr e m RV (Ecall rf rargs ty) (t1**t2**t3) m3 (Eval vres ty)

with eval_exprlist: env -> mem -> exprlist -> trace -> mem -> exprlist -> Prop :=
  | eval_nil: forall e m,
      eval_exprlist e m Enil E0 m Enil
  | eval_cons: forall e m a1 al t1 m1 a1' t2 m2 al',
      eval_expr e m RV a1 t1 m1 a1' -> eval_exprlist e m1 al t2 m2 al' ->
      eval_exprlist e m (Econs a1 al) (t1**t2) m2 (Econs a1' al')

(** [exec_stmt ge e m1 s t m2 out] describes the execution of
  the statement [s].  [out] is the outcome for this execution.
  [m1] is the initial memory state, [m2] the final memory state.
  [t] is the trace of input/output events performed during this
  evaluation. *)

with exec_stmt: env -> mem -> statement -> trace -> mem -> outcome -> Prop :=
  | exec_Sskip:   forall e m,
      exec_stmt e m Sskip
               E0 m Out_normal
  | exec_Sdo:     forall e m a t m' v,
      eval_expression e m a t m' v ->
      exec_stmt e m (Sdo a)
                t m' Out_normal
  | exec_Sseq_1:   forall e m s1 s2 t1 m1 t2 m2 out,
      exec_stmt e m s1 t1 m1 Out_normal ->
      exec_stmt e m1 s2 t2 m2 out ->
      exec_stmt e m (Ssequence s1 s2)
                (t1 ** t2) m2 out
  | exec_Sseq_2:   forall e m s1 s2 t1 m1 out,
      exec_stmt e m s1 t1 m1 out ->
      out <> Out_normal ->
      exec_stmt e m (Ssequence s1 s2)
                t1 m1 out
  | exec_Sifthenelse: forall e m a s1 s2 t1 m1 v1 t2 m2 b out,
      eval_expression e m a t1 m1 v1 ->
      bool_val v1 (typeof a) m1 = Some b ->
      exec_stmt e m1 (if b then s1 else s2) t2 m2 out ->
      exec_stmt e m (Sifthenelse a s1 s2)
                (t1**t2) m2 out
  | exec_Sreturn_none:   forall e m,
      exec_stmt e m (Sreturn None)
               E0 m (Out_return None)
  | exec_Sreturn_some: forall e m a t m' v,
      eval_expression e m a t m' v ->
      exec_stmt e m (Sreturn (Some a))
                t m' (Out_return (Some(v, typeof a)))
  | exec_Sbreak:   forall e m,
      exec_stmt e m Sbreak
               E0 m Out_break
  | exec_Scontinue:   forall e m,
      exec_stmt e m Scontinue
               E0 m Out_continue
  | exec_Swhile_false: forall e m a s t m' v,
      eval_expression e m a t m' v ->
      bool_val v (typeof a) m' = Some false ->
      exec_stmt e m (Swhile a s)
                t m' Out_normal
  | exec_Swhile_stop: forall e m a s t1 m1 v t2 m2 out' out,
      eval_expression e m a t1 m1 v ->
      bool_val v (typeof a) m1 = Some true ->
      exec_stmt e m1 s t2 m2 out' ->
      out_break_or_return out' out ->
      exec_stmt e m (Swhile a s)
                (t1**t2) m2 out
  | exec_Swhile_loop: forall e m a s t1 m1 v t2 m2 out1 t3 m3 out,
      eval_expression e m a t1 m1 v ->
      bool_val v (typeof a) m1 = Some true ->
      exec_stmt e m1 s t2 m2 out1 ->
      out_normal_or_continue out1 ->
      exec_stmt e m2 (Swhile a s) t3 m3 out ->
      exec_stmt e m (Swhile a s)
                (t1 ** t2 ** t3) m3 out
  | exec_Sdowhile_false: forall e m s a t1 m1 out1 t2 m2 v,
      exec_stmt e m s t1 m1 out1 ->
      out_normal_or_continue out1 ->
      eval_expression e m1 a t2 m2 v ->
      bool_val v (typeof a) m2 = Some false ->
      exec_stmt e m (Sdowhile a s)
                (t1 ** t2) m2 Out_normal
  | exec_Sdowhile_stop: forall e m s a t m1 out1 out,
      exec_stmt e m s t m1 out1 ->
      out_break_or_return out1 out ->
      exec_stmt e m (Sdowhile a s)
                t m1 out
  | exec_Sdowhile_loop: forall e m s a t1 m1 out1 t2 m2 v t3 m3 out,
      exec_stmt e m s t1 m1 out1 ->
      out_normal_or_continue out1 ->
      eval_expression e m1 a t2 m2 v ->
      bool_val v (typeof a) m2 = Some true ->
      exec_stmt e m2 (Sdowhile a s) t3 m3 out ->
      exec_stmt e m (Sdowhile a s)
                (t1 ** t2 ** t3) m3 out
  | exec_Sfor_start: forall e m s a1 a2 a3 out m1 m2 t1 t2,
      exec_stmt e m a1 t1 m1 Out_normal ->
      exec_stmt e m1 (Sfor Sskip a2 a3 s) t2 m2 out ->
      exec_stmt e m (Sfor a1 a2 a3 s)
                (t1 ** t2) m2 out
  | exec_Sfor_false: forall e m s a2 a3 t m' v,
      eval_expression e m a2 t m' v ->
      bool_val v (typeof a2) m' = Some false ->
      exec_stmt e m (Sfor Sskip a2 a3 s)
                t m' Out_normal
  | exec_Sfor_stop: forall e m s a2 a3 t1 m1 v t2 m2 out1 out,
      eval_expression e m a2 t1 m1 v ->
      bool_val v (typeof a2) m1 = Some true ->
      exec_stmt e m1 s t2 m2 out1 ->
      out_break_or_return out1 out ->
      exec_stmt e m (Sfor Sskip a2 a3 s)
                (t1 ** t2) m2 out
  | exec_Sfor_loop: forall e m s a2 a3 t1 m1 v t2 m2 out1 t3 m3 t4 m4 out,
      eval_expression e m a2 t1 m1 v ->
      bool_val v (typeof a2) m1 = Some true ->
      exec_stmt e m1 s t2 m2 out1 ->
      out_normal_or_continue out1 ->
      exec_stmt e m2 a3 t3 m3 Out_normal ->
      exec_stmt e m3 (Sfor Sskip a2 a3 s) t4 m4 out ->
      exec_stmt e m (Sfor Sskip a2 a3 s)
                (t1 ** t2 ** t3 ** t4) m4 out
  | exec_Sswitch:   forall e m a sl t1 m1 v n t2 m2 out,
      eval_expression e m a t1 m1 v ->
      sem_switch_arg v (typeof a) = Some n ->
      exec_stmt e m1 (seq_of_labeled_statement (select_switch n sl)) t2 m2 out ->
      exec_stmt e m (Sswitch a sl)
                (t1 ** t2) m2 (outcome_switch out)

(** [eval_funcall m1 fd args t m2 res] describes the invocation of
  function [fd] with arguments [args].  [res] is the value returned
  by the call.  *)

with eval_funcall: mem -> fundef -> list val -> trace -> mem -> val -> Prop :=
  | eval_funcall_internal: forall m f vargs t e m1 m2 m3 out vres m4,
      list_norepet (var_names f.(fn_params) ++ var_names f.(fn_vars)) ->
      alloc_variables ge empty_env m (f.(fn_params) ++ f.(fn_vars)) e m1 ->
      bind_parameters se ge e m1 f.(fn_params) vargs m2 ->
      exec_stmt e m2 f.(fn_body) t m3 out ->
      outcome_result_value out f.(fn_return) vres m3 ->
      Mem.free_list m3 (blocks_of_env ge e) = Some m4 ->
      eval_funcall m (Internal f) vargs t m4 vres
  | eval_funcall_external: forall m ef targs tres cconv vargs t vres m',
      external_call ef se vargs m t vres m' ->
      eval_funcall m (External ef targs tres cconv) vargs t m' vres.

Scheme eval_expression_ind5 := Minimality for eval_expression Sort Prop
  with eval_expr_ind5 := Minimality for eval_expr Sort Prop
  with eval_exprlist_ind5 := Minimality for eval_exprlist Sort Prop
  with exec_stmt_ind5 := Minimality for exec_stmt Sort Prop
  with eval_funcall_ind5 := Minimality for eval_funcall Sort Prop.

Combined Scheme bigstep_induction from
        eval_expression_ind5,  eval_expr_ind5,  eval_exprlist_ind5,
        exec_stmt_ind5, eval_funcall_ind5.

(** [evalinf_expr ge e m1 K a T] denotes the fact that expression [a]
  diverges in initial state [m1].  [T] is the trace of input/output
  events performed during this evaluation.  *)

CoInductive evalinf_expr: env -> mem -> kind -> expr -> traceinf -> Prop :=
  | evalinf_field: forall e m a t f ty,
      evalinf_expr e m RV a t ->
      evalinf_expr e m LV (Efield a f ty) t
  | evalinf_valof: forall e m a t ty,
      evalinf_expr e m LV a t ->
      evalinf_expr e m RV (Evalof a ty) t
  | evalinf_deref: forall e m a t ty,
      evalinf_expr e m RV a t ->
      evalinf_expr e m LV (Ederef a ty) t
  | evalinf_addrof: forall e m a t ty,
      evalinf_expr e m LV a t ->
      evalinf_expr e m RV (Eaddrof a ty) t
  | evalinf_unop: forall e m a t op ty,
      evalinf_expr e m RV a t ->
      evalinf_expr e m RV (Eunop op a ty) t
  | evalinf_binop_left: forall e m a1 t1 a2 op ty,
      evalinf_expr e m RV a1 t1 ->
      evalinf_expr e m RV (Ebinop op a1 a2 ty) t1
  | evalinf_binop_right: forall e m a1 t1 m' a1' a2 t2 op ty,
      eval_expr e m RV a1 t1 m' a1' -> evalinf_expr e m' RV a2 t2 ->
      evalinf_expr e m RV (Ebinop op a1 a2 ty) (t1 *** t2)
  | evalinf_cast: forall e m a t ty,
      evalinf_expr e m RV a t ->
      evalinf_expr e m RV (Ecast a ty) t
  | evalinf_seqand: forall e m a1 a2 ty t1,
      evalinf_expr e m RV a1 t1 ->
      evalinf_expr e m RV (Eseqand a1 a2 ty) t1
  | evalinf_seqand_2: forall e m a1 a2 ty t1 m' a1' v1 t2,
      eval_expr e m RV a1 t1 m' a1' -> eval_simple_rvalue ge e m' a1' v1 ->
      bool_val v1 (typeof a1) m' = Some true ->
      evalinf_expr e m' RV a2 t2 ->
      evalinf_expr e m RV (Eseqand a1 a2 ty) (t1***t2)
  | evalinf_seqor: forall e m a1 a2 ty t1,
      evalinf_expr e m RV a1 t1 ->
      evalinf_expr e m RV (Eseqor a1 a2 ty) t1
  | evalinf_seqor_2: forall e m a1 a2 ty t1 m' a1' v1 t2,
      eval_expr e m RV a1 t1 m' a1' -> eval_simple_rvalue ge e m' a1' v1 ->
      bool_val v1 (typeof a1) m' = Some false ->
      evalinf_expr e m' RV a2 t2 ->
      evalinf_expr e m RV (Eseqor a1 a2 ty) (t1***t2)
  | evalinf_condition: forall e m a1 a2 a3 ty t1,
      evalinf_expr e m RV a1 t1 ->
      evalinf_expr e m RV (Econdition a1 a2 a3 ty) t1
  | evalinf_condition_2: forall e m a1 a2 a3 ty t1 m' a1' v1 t2 b,
      eval_expr e m RV a1 t1 m' a1' -> eval_simple_rvalue ge e m' a1' v1 ->
      bool_val v1 (typeof a1) m' = Some b ->
      evalinf_expr e m' RV (if b then a2 else a3) t2 ->
      evalinf_expr e m RV (Econdition a1 a2 a3 ty) (t1***t2)
  | evalinf_assign_left: forall e m a1 t1 a2 ty,
      evalinf_expr e m LV a1 t1 ->
      evalinf_expr e m RV (Eassign a1 a2 ty) t1
  | evalinf_assign_right: forall e m a1 t1 m' a1' a2 t2 ty,
      eval_expr e m LV a1 t1 m' a1' -> evalinf_expr e m' RV a2 t2 ->
      evalinf_expr e m RV (Eassign a1 a2 ty) (t1 *** t2)
  | evalinf_assignop_left: forall e m a1 t1 a2 op tyres ty,
      evalinf_expr e m LV a1 t1 ->
      evalinf_expr e m RV (Eassignop op a1 a2 tyres ty) t1
  | evalinf_assignop_right: forall e m a1 t1 m' a1' a2 t2 op tyres ty,
      eval_expr e m LV a1 t1 m' a1' -> evalinf_expr e m' RV a2 t2 ->
      evalinf_expr e m RV (Eassignop op a1 a2 tyres ty) (t1 *** t2)
  | evalinf_postincr: forall e m a t id ty,
      evalinf_expr e m LV a t ->
      evalinf_expr e m RV (Epostincr id a ty) t
  | evalinf_comma_left: forall e m a1 t1 a2 ty,
      evalinf_expr e m RV a1 t1 ->
      evalinf_expr e m RV (Ecomma a1 a2 ty) t1
  | evalinf_comma_right: forall e m a1 t1 m1 a1' v1 a2 t2 ty,
      eval_expr e m RV a1 t1 m1 a1' -> eval_simple_rvalue ge e m1 a1' v1 ->
      ty = typeof a2 ->
      evalinf_expr e m1 RV a2 t2 ->
      evalinf_expr e m RV (Ecomma a1 a2 ty) (t1 *** t2)
  | evalinf_call_left: forall e m a1 t1 a2 ty,
      evalinf_expr e m RV a1 t1 ->
      evalinf_expr e m RV (Ecall a1 a2 ty) t1
  | evalinf_call_right: forall e m a1 t1 m1 a1' a2 t2 ty,
      eval_expr e m RV a1 t1 m1 a1' ->
      evalinf_exprlist e m1 a2 t2 ->
      evalinf_expr e m RV (Ecall a1 a2 ty) (t1 *** t2)
  | evalinf_call: forall e m rf rargs ty t1 m1 rf' t2 m2 rargs' vf vargs
                      targs tres cconv fd t3,
      eval_expr e m RV rf t1 m1 rf' -> eval_exprlist e m1 rargs t2 m2 rargs' ->
      eval_simple_rvalue ge e m2 rf' vf ->
      eval_simple_list ge e m2 rargs' targs vargs ->
      classify_fun (typeof rf) = fun_case_f targs tres cconv ->
      Genv.find_funct ge vf = Some fd ->
      type_of_fundef fd = Tfunction targs tres cconv ->
      evalinf_funcall m2 fd vargs t3 ->
      evalinf_expr e m RV (Ecall rf rargs ty) (t1***t2***t3)

with evalinf_exprlist: env -> mem -> exprlist -> traceinf -> Prop :=
  | evalinf_cons_left: forall e m a1 al t1,
      evalinf_expr e m RV a1 t1 ->
      evalinf_exprlist e m (Econs a1 al) t1
  | evalinf_cons_right: forall e m a1 al t1 m1 a1' t2,
      eval_expr e m RV a1 t1 m1 a1' -> evalinf_exprlist e m1 al t2 ->
      evalinf_exprlist e m (Econs a1 al) (t1***t2)

(** [execinf_stmt ge e m1 s t] describes the diverging execution of
  the statement [s].  *)

with execinf_stmt: env -> mem -> statement -> traceinf -> Prop :=
  | execinf_Sdo:     forall e m a t,
      evalinf_expr e m RV a t ->
      execinf_stmt e m (Sdo a) t
  | execinf_Sseq_1:   forall e m s1 s2 t1,
      execinf_stmt e m s1 t1 ->
      execinf_stmt e m (Ssequence s1 s2) t1
  | execinf_Sseq_2:   forall e m s1 s2 t1 m1 t2,
      exec_stmt e m s1 t1 m1 Out_normal ->
      execinf_stmt e m1 s2 t2 ->
      execinf_stmt e m (Ssequence s1 s2) (t1***t2)
  | execinf_Sifthenelse_test: forall e m a s1 s2 t1,
      evalinf_expr e m RV a t1 ->
      execinf_stmt e m (Sifthenelse a s1 s2) t1
  | execinf_Sifthenelse: forall e m a s1 s2 t1 m1 v1 t2 b,
      eval_expression e m a t1 m1 v1 ->
      bool_val v1 (typeof a) m1 = Some b ->
      execinf_stmt e m1 (if b then s1 else s2) t2 ->
      execinf_stmt e m (Sifthenelse a s1 s2) (t1***t2)
  | execinf_Sreturn_some: forall e m a t,
      evalinf_expr e m RV a t ->
      execinf_stmt e m (Sreturn (Some a)) t
  | execinf_Swhile_test: forall e m a s t1,
      evalinf_expr e m RV a t1 ->
      execinf_stmt e m (Swhile a s) t1
  | execinf_Swhile_body: forall e m a s t1 m1 v t2,
      eval_expression e m a t1 m1 v ->
      bool_val v (typeof a) m1 = Some true ->
      execinf_stmt e m1 s t2 ->
      execinf_stmt e m (Swhile a s) (t1***t2)
  | execinf_Swhile_loop: forall e m a s t1 m1 v t2 m2 out1 t3,
      eval_expression e m a t1 m1 v ->
      bool_val v (typeof a) m1 = Some true ->
      exec_stmt e m1 s t2 m2 out1 ->
      out_normal_or_continue out1 ->
      execinf_stmt e m2 (Swhile a s) t3 ->
      execinf_stmt e m (Swhile a s) (t1***t2***t3)
  | execinf_Sdowhile_body: forall e m s a t1,
      execinf_stmt e m s t1 ->
      execinf_stmt e m (Sdowhile a s) t1
  | execinf_Sdowhile_test: forall e m s a t1 m1 out1 t2,
      exec_stmt e m s t1 m1 out1 ->
      out_normal_or_continue out1 ->
      evalinf_expr e m1 RV a t2 ->
      execinf_stmt e m (Sdowhile a s) (t1***t2)
  | execinf_Sdowhile_loop: forall e m s a t1 m1 out1 t2 m2 v t3,
      exec_stmt e m s t1 m1 out1 ->
      out_normal_or_continue out1 ->
      eval_expression e m1 a t2 m2 v ->
      bool_val v (typeof a) m2 = Some true ->
      execinf_stmt e m2 (Sdowhile a s) t3 ->
      execinf_stmt e m (Sdowhile a s) (t1***t2***t3)
  | execinf_Sfor_start_1: forall e m s a1 a2 a3 t1,
      execinf_stmt e m a1 t1 ->
      execinf_stmt e m (Sfor a1 a2 a3 s) t1
  | execinf_Sfor_start_2: forall e m s a1 a2 a3 m1 t1 t2,
      exec_stmt e m a1 t1 m1 Out_normal -> a1 <> Sskip ->
      execinf_stmt e m1 (Sfor Sskip a2 a3 s) t2 ->
      execinf_stmt e m (Sfor a1 a2 a3 s) (t1***t2)
  | execinf_Sfor_test: forall e m s a2 a3 t,
      evalinf_expr e m RV a2 t ->
      execinf_stmt e m (Sfor Sskip a2 a3 s) t
  | execinf_Sfor_body: forall e m s a2 a3 t1 m1 v t2,
      eval_expression e m a2 t1 m1 v ->
      bool_val v (typeof a2) m1 = Some true ->
      execinf_stmt e m1 s t2 ->
      execinf_stmt e m (Sfor Sskip a2 a3 s) (t1***t2)
  | execinf_Sfor_next: forall e m s a2 a3 t1 m1 v t2 m2 out1 t3,
      eval_expression e m a2 t1 m1 v ->
      bool_val v (typeof a2) m1 = Some true ->
      exec_stmt e m1 s t2 m2 out1 ->
      out_normal_or_continue out1 ->
      execinf_stmt e m2 a3 t3 ->
      execinf_stmt e m (Sfor Sskip a2 a3 s) (t1***t2***t3)
  | execinf_Sfor_loop: forall e m s a2 a3 t1 m1 v t2 m2 out1 t3 m3 t4,
      eval_expression e m a2 t1 m1 v ->
      bool_val v (typeof a2) m1 = Some true ->
      exec_stmt e m1 s t2 m2 out1 ->
      out_normal_or_continue out1 ->
      exec_stmt e m2 a3 t3 m3 Out_normal ->
      execinf_stmt e m3 (Sfor Sskip a2 a3 s) t4 ->
      execinf_stmt e m (Sfor Sskip a2 a3 s) (t1***t2***t3***t4)
  | execinf_Sswitch_expr:   forall e m a sl t1,
      evalinf_expr e m RV a t1 ->
      execinf_stmt e m (Sswitch a sl) t1
  | execinf_Sswitch_body:   forall e m a sl t1 m1 v n t2,
      eval_expression e m a t1 m1 v ->
      sem_switch_arg v (typeof a) = Some n ->
      execinf_stmt e m1 (seq_of_labeled_statement (select_switch n sl)) t2 ->
      execinf_stmt e m (Sswitch a sl) (t1***t2)

(** [evalinf_funcall m1 fd args t m2 res] describes a diverging
  invocation of function [fd] with arguments [args].  *)

with evalinf_funcall: mem -> fundef -> list val -> traceinf -> Prop :=
  | evalinf_funcall_internal: forall m f vargs t e m1 m2,
      list_norepet (var_names f.(fn_params) ++ var_names f.(fn_vars)) ->
      alloc_variables ge empty_env m (f.(fn_params) ++ f.(fn_vars)) e m1 ->
      bind_parameters se ge e m1 f.(fn_params) vargs m2 ->
      execinf_stmt e m2 f.(fn_body) t ->
      evalinf_funcall m (Internal f) vargs t.

(** ** Implication from big-step semantics to transition semantics *)

Inductive outcome_state_match
       (e: env) (m: mem) (f: function) (k: cont): outcome -> state -> Prop :=
  | osm_normal:
      outcome_state_match e m f k Out_normal (State f Sskip k e m)
  | osm_break:
      outcome_state_match e m f k Out_break (State f Sbreak k e m)
  | osm_continue:
      outcome_state_match e m f k Out_continue (State f Scontinue k e m)
  | osm_return_none: forall k',
      call_cont k' = call_cont k ->
      outcome_state_match e m f k
        (Out_return None) (State f (Sreturn None) k' e m)
  | osm_return_some: forall v ty k',
      call_cont k' = call_cont k ->
      outcome_state_match e m f k
        (Out_return (Some (v, ty))) (ExprState f (Eval v ty) (Kreturn k') e m).

Lemma is_call_cont_call_cont:
  forall k, is_call_cont k -> call_cont k = k.
Proof.
  destruct k; simpl; intros; contradiction || auto.
Qed.

Lemma leftcontext_compose:
  forall k2 k3 C2, leftcontext k2 k3 C2 ->
  forall k1 C1, leftcontext k1 k2 C1 ->
  leftcontext k1 k3 (fun x => C2(C1 x))
with leftcontextlist_compose:
  forall k2 C2, leftcontextlist k2 C2 ->
  forall k1 C1, leftcontext k1 k2 C1 ->
  leftcontextlist k1 (fun x => C2(C1 x)).
Proof.
  induction 1; intros; try (constructor; eauto).
  replace (fun x => C1 x) with C1. auto. apply extensionality; auto.
  induction 1; intros; constructor; eauto.
Qed.

Lemma exprlist_app_leftcontext:
  forall rl1 rl2,
  simplelist rl1 = true -> leftcontextlist RV (fun x => exprlist_app rl1 (Econs x rl2)).
Proof.
  induction rl1; simpl; intros.
  apply lctx_list_head. constructor.
  destruct (andb_prop _ _ H). apply lctx_list_tail. auto. auto.
Qed.

Lemma exprlist_app_simple:
  forall rl1 rl2,
  simplelist (exprlist_app rl1 rl2) = simplelist rl1 && simplelist rl2.
Proof.
  induction rl1; intros; simpl. auto. rewrite IHrl1. apply andb_assoc.
Qed.

Lemma bigstep_to_steps:
  (forall e m a t m' v,
   eval_expression e m a t m' v ->
   forall f k,
   star step se ge (ExprState f a k e m) t (ExprState f (Eval v (typeof a)) k e m'))
/\(forall e m K a t m' a',
   eval_expr e m K a t m' a' ->
   forall C f k, leftcontext K RV C ->
   simple a' = true /\ typeof a' = typeof a /\
   star step se ge (ExprState f (C a) k e m) t (ExprState f (C a') k e m'))
/\(forall e m al t m' al',
   eval_exprlist e m al t m' al' ->
   forall a1 al2 ty C f k, leftcontext RV RV C -> simple a1 = true -> simplelist al2 = true ->
   simplelist al' = true /\
   star step se ge (ExprState f (C (Ecall a1 (exprlist_app al2 al) ty)) k e m)
              t (ExprState f (C (Ecall a1 (exprlist_app al2 al') ty)) k e m'))
/\(forall e m s t m' out,
   exec_stmt e m s t m' out ->
   forall f k,
   exists S,
   star step se ge (State f s k e m) t S /\ outcome_state_match e m' f k out S)
/\(forall m fd args t m' res,
   eval_funcall m fd args t m' res ->
   forall vf k
   (FPTR: Genv.find_funct ge vf = Some fd),
   is_call_cont k ->
   star step se ge (Callstate vf (type_of_fundef fd) args k m) t (Returnstate res k m')).
Proof.
  apply bigstep_induction; intros.
(* expression, general *)
  exploit (H0 (fun x => x) f k). constructor. intros [A [B C]].
  assert (match a' with Eval _ _ => False | _ => True end ->
          star step se ge (ExprState f a k e m) t (ExprState f (Eval v (typeof a)) k e m')).
   intro. eapply star_right. eauto. left. eapply step_expr; eauto. traceEq.
  destruct a'; auto.
  simpl in B. rewrite B in C. inv H1. auto.

(* val *)
  simpl; intuition. apply star_refl.
(* var *)
  simpl; intuition. apply star_refl.
(* field *)
  exploit (H0 (fun x => C(Efield x f ty))).
    eapply leftcontext_compose; eauto. repeat constructor. intros [A [B D]].
  simpl; intuition; eauto.
(* valof *)
  exploit (H1 (fun x => C(Evalof x ty))).
    eapply leftcontext_compose; eauto. repeat constructor. intros [A [B D]].
  simpl; intuition; eauto. rewrite A; rewrite B; rewrite H; auto.
(* valof volatile *)
  exploit (H1 (fun x => C(Evalof x ty))).
    eapply leftcontext_compose; eauto. repeat constructor. intros [A [B D]].
  simpl; intuition.
  eapply star_right. eexact D.
  left. eapply step_rvalof_volatile; eauto. rewrite H4; eauto. congruence. congruence.
  traceEq.
(* deref *)
  exploit (H0 (fun x => C(Ederef x ty))).
    eapply leftcontext_compose; eauto. repeat constructor. intros [A [B D]].
  simpl; intuition; eauto.
(* addrof *)
  exploit (H0 (fun x => C(Eaddrof x ty))).
    eapply leftcontext_compose; eauto. repeat constructor. intros [A [B D]].
  simpl; intuition; eauto.
(* unop *)
  exploit (H0 (fun x => C(Eunop op x ty))).
    eapply leftcontext_compose; eauto. repeat constructor. intros [A [B D]].
  simpl; intuition; eauto.
(* binop *)
  exploit (H0 (fun x => C(Ebinop op x a2 ty))).
    eapply leftcontext_compose; eauto. repeat constructor. intros [A [B D]].
  exploit (H2 (fun x => C(Ebinop op a1' x ty))).
    eapply leftcontext_compose; eauto. repeat constructor. auto. intros [E [F G]].
  simpl; intuition. eapply star_trans; eauto.
(* cast *)
  exploit (H0 (fun x => C(Ecast x ty))).
    eapply leftcontext_compose; eauto. repeat constructor. intros [A [B D]].
  simpl; intuition; eauto.
(* seqand true *)
  exploit (H0 (fun x => C(Eseqand x a2 ty))).
    eapply leftcontext_compose; eauto. repeat constructor. intros [A [B D]].
  exploit (H4 (fun x => C(Eparen x type_bool ty))).
    eapply leftcontext_compose; eauto. repeat constructor. intros [E [F G]].
  simpl; intuition. eapply star_trans. eexact D.
  eapply star_left. left; eapply step_seqand_true; eauto. rewrite B; auto.
  eapply star_right. eexact G.
  left; eapply step_paren; eauto. rewrite F; eauto.
  eauto. eauto. traceEq.
(* seqand false *)
  exploit (H0 (fun x => C(Eseqand x a2 ty))).
    eapply leftcontext_compose; eauto. repeat constructor. intros [A [B D]].
  simpl; intuition. eapply star_right. eexact D.
  left; eapply step_seqand_false; eauto. rewrite B; auto.
  traceEq.
(* seqor false *)
  exploit (H0 (fun x => C(Eseqor x a2 ty))).
    eapply leftcontext_compose; eauto. repeat constructor. intros [A [B D]].
  exploit (H4 (fun x => C(Eparen x type_bool ty))).
    eapply leftcontext_compose; eauto. repeat constructor. intros [E [F G]].
  simpl; intuition. eapply star_trans. eexact D.
  eapply star_left. left; eapply step_seqor_false; eauto. rewrite B; auto.
  eapply star_right. eexact G.
  left; eapply step_paren; eauto. rewrite F; eauto.
  eauto. eauto. traceEq.
(* seqor true *)
  exploit (H0 (fun x => C(Eseqor x a2 ty))).
    eapply leftcontext_compose; eauto. repeat constructor. intros [A [B D]].
  simpl; intuition. eapply star_right. eexact D.
  left; eapply step_seqor_true; eauto. rewrite B; auto.
  traceEq.
(* condition *)
  exploit (H0 (fun x => C(Econdition x a2 a3 ty))).
    eapply leftcontext_compose; eauto. repeat constructor. intros [A [B D]].
  exploit (H4 (fun x => C(Eparen x ty ty))).
    eapply leftcontext_compose; eauto. repeat constructor. intros [E [F G]].
  simpl. split; auto. split; auto.
  eapply star_trans. eexact D.
  eapply star_left. left; eapply step_condition; eauto. rewrite B; eauto.
  eapply star_right. eexact G. left; eapply step_paren; eauto. congruence.
  reflexivity. reflexivity. traceEq.
(* sizeof *)
  simpl; intuition. apply star_refl.
(* alignof *)
  simpl; intuition. apply star_refl.
(* assign *)
  exploit (H0 (fun x => C(Eassign x r ty))).
    eapply leftcontext_compose; eauto. repeat constructor. intros [A [B D]].
  exploit (H2 (fun x => C(Eassign l' x ty))).
    eapply leftcontext_compose; eauto. repeat constructor. auto. intros [E [F G]].
  simpl; intuition.
  eapply star_trans. eexact D.
  eapply star_right. eexact G.
  left. eapply step_assign; eauto. congruence. rewrite B; eauto. congruence.
  reflexivity. traceEq.
(* assignop *)
  exploit (H0 (fun x => C(Eassignop op x r tyres ty))).
    eapply leftcontext_compose; eauto. repeat constructor. intros [A [B D]].
  exploit (H2 (fun x => C(Eassignop op l' x tyres ty))).
    eapply leftcontext_compose; eauto. repeat constructor. auto. intros [E [F G]].
  simpl; intuition.
  eapply star_trans. eexact D.
  eapply star_right. eexact G.
  left. eapply step_assignop; eauto.
  rewrite B; eauto. rewrite B; rewrite F; eauto. congruence. rewrite B; eauto. congruence.
  reflexivity. traceEq.
(* postincr *)
  exploit (H0 (fun x => C(Epostincr id x ty))).
    eapply leftcontext_compose; eauto. repeat constructor. intros [A [B D]].
  simpl; intuition.
  eapply star_right. eexact D.
  left. eapply step_postincr; eauto. congruence.
  traceEq.
(* comma *)
  exploit (H0 (fun x => C(Ecomma x r2 ty))).
    eapply leftcontext_compose; eauto. repeat constructor. intros [A [B D]].
  exploit (H3 C). auto. intros [E [F G]].
  simpl; intuition. congruence.
  eapply star_trans. eexact D.
  eapply star_left. left; eapply step_comma; eauto.
  eexact G.
  reflexivity. traceEq.
(* call *)
  unfold Genv.find_funct in *. des_ifs.
  exploit (H0 (fun x => C(Ecall x rargs ty))).
    eapply leftcontext_compose; eauto. repeat constructor. intros [A [B D]].
  exploit (H2 rf' Enil ty C); eauto. intros [E F].
  simpl; intuition.
  eapply star_trans. eexact D.
  eapply star_trans. eexact F.
  eapply star_left. left; eapply step_call; eauto. rewrite B. eauto.
  eapply star_right. rewrite <- H7. eapply H9. eauto. red; auto.
  right; constructor.
  reflexivity. reflexivity. reflexivity. traceEq.
(* nil *)
  simpl; intuition. apply star_refl.
(* cons *)
  exploit (H0 (fun x => C(Ecall a0 (exprlist_app al2 (Econs x al)) ty))).
    eapply leftcontext_compose; eauto. repeat constructor. auto.
    apply exprlist_app_leftcontext; auto. intros [A [B D]].
  exploit (H2 a0 (exprlist_app al2 (Econs a1' Enil))); eauto.
  rewrite exprlist_app_simple. simpl. rewrite H5; rewrite A; auto.
  repeat rewrite exprlist_app_assoc. simpl.
  intros [E F].
  simpl; intuition.
  eapply star_trans; eauto.

(* skip *)
  econstructor; split. apply star_refl. constructor.

(* do *)
  econstructor; split.
  eapply star_left. right; constructor.
  eapply star_right. apply H0. right; constructor.
  reflexivity. traceEq.
  constructor.

(* sequence 2 *)
  destruct (H0 f (Kseq s2 k)) as [S1 [A1 B1]]; auto. inv B1.
  destruct (H2 f k) as [S2 [A2 B2]]; auto.
  econstructor; split.
  eapply star_left. right; econstructor.
  eapply star_trans. eexact A1.
  eapply star_left. right; constructor. eexact A2.
  reflexivity. reflexivity. traceEq.
  auto.

(* sequence 1 *)
  destruct (H0 f (Kseq s2 k)) as [S1 [A1 B1]]; auto.
  set (S2 :=
    match out with
    | Out_break => State f Sbreak k e m1
    | Out_continue => State f Scontinue k e m1
    | _ => S1
    end).
  exists S2; split.
  eapply star_left. right; econstructor.
  eapply star_trans. eexact A1.
  unfold S2; inv B1.
    congruence.
    apply star_one. right; apply step_break_seq.
    apply star_one. right; apply step_continue_seq.
    apply star_refl.
    apply star_refl.
  reflexivity. traceEq.
  unfold S2; inv B1; congruence || econstructor; eauto.

(* ifthenelse *)
  destruct (H3 f k) as [S1 [A1 B1]]; auto.
  exists S1; split.
  eapply star_left. right; apply step_ifthenelse_1.
  eapply star_trans. eapply H0.
  eapply star_left. 2: eexact A1. right; eapply step_ifthenelse_2; eauto.
  reflexivity. reflexivity. traceEq.
  auto.

(* return none *)
  econstructor; split. apply star_refl. constructor. auto.

(* return some *)
  econstructor; split.
  eapply star_left. right; apply step_return_1.
  eapply H0. traceEq.
  econstructor; eauto.

(* break *)
  econstructor; split. apply star_refl. constructor.

(* continue *)
  econstructor; split. apply star_refl. constructor.

(* while false *)
  econstructor; split.
  eapply star_left. right; apply step_while.
  eapply star_right. apply H0. right; eapply step_while_false; eauto.
  reflexivity. traceEq.
  constructor.

(* while stop *)
  destruct (H3 f (Kwhile2 a s k)) as [S1 [A1 B1]].
  set (S2 :=
    match out' with
    | Out_break => State f Sskip k e m2
    | _ => S1
    end).
  exists S2; split.
  eapply star_left. right; apply step_while.
  eapply star_trans. apply H0.
  eapply star_left. right; eapply step_while_true; eauto.
  eapply star_trans. eexact A1.
  unfold S2. inversion H4; subst.
  inv B1. apply star_one. right; constructor.
  apply star_refl.
  reflexivity. reflexivity. reflexivity. traceEq.
  unfold S2. inversion H4; subst. constructor. inv B1; econstructor; eauto.

(* while loop *)
  destruct (H3 f (Kwhile2 a s k)) as [S1 [A1 B1]].
  destruct (H6 f k) as [S2 [A2 B2]]; auto.
  exists S2; split.
  eapply star_left. right; apply step_while.
  eapply star_trans. apply H0.
  eapply star_left. right; eapply step_while_true; eauto.
  eapply star_trans. eexact A1.
  eapply star_left.
  inv H4; inv B1; right; apply step_skip_or_continue_while; auto.
  eexact A2.
  reflexivity. reflexivity. reflexivity. reflexivity. traceEq.
  auto.

(* dowhile false *)
  destruct (H0 f (Kdowhile1 a s k)) as [S1 [A1 B1]].
  exists (State f Sskip k e m2); split.
  eapply star_left. right; constructor.
  eapply star_trans. eexact A1.
  eapply star_left.
  inv H1; inv B1; right; eapply step_skip_or_continue_dowhile; eauto.
  eapply star_right. apply H3.
  right; eapply step_dowhile_false; eauto.
  reflexivity. reflexivity. reflexivity. traceEq.
  constructor.

(* dowhile stop *)
  destruct (H0 f (Kdowhile1 a s k)) as [S1 [A1 B1]].
  set (S2 :=
    match out1 with
    | Out_break => State f Sskip k e m1
    | _ => S1
    end).
  exists S2; split.
  eapply star_left. right; apply step_dowhile.
  eapply star_trans. eexact A1.
  unfold S2. inversion H1; subst.
  inv B1. apply star_one. right; constructor.
  apply star_refl.
  reflexivity. traceEq.
  unfold S2. inversion H1; subst. constructor. inv B1; econstructor; eauto.

(* dowhile loop *)
  destruct (H0 f (Kdowhile1 a s k)) as [S1 [A1 B1]].
  destruct (H6 f k) as [S2 [A2 B2]]; auto.
  exists S2; split.
  eapply star_left. right; constructor.
  eapply star_trans. eexact A1.
  eapply star_left.
  inv H1; inv B1; right; eapply step_skip_or_continue_dowhile; eauto.
  eapply star_trans. apply H3.
  eapply star_left. right; eapply step_dowhile_true; eauto.
  eexact A2.
  reflexivity. reflexivity. reflexivity. reflexivity. traceEq.
  auto.

(* for start *)
  assert (a1 = Sskip \/ a1 <> Sskip). destruct a1; auto; right; congruence.
  destruct H3.
  subst a1. inv H. apply H2; auto.
  destruct (H0 f (Kseq (Sfor Sskip a2 a3 s) k)) as [S1 [A1 B1]]; auto. inv B1.
  destruct (H2 f k) as [S2 [A2 B2]]; auto.
  exists S2; split.
  eapply star_left. right; apply step_for_start; auto.
  eapply star_trans. eexact A1.
  eapply star_left. right; constructor. eexact A2.
  reflexivity. reflexivity. traceEq.
  auto.

(* for false *)
  econstructor; split.
  eapply star_left. right; apply step_for.
  eapply star_right. apply H0. right; eapply step_for_false; eauto.
  reflexivity. traceEq.
  constructor.

(* for stop *)
  destruct (H3 f (Kfor3 a2 a3 s k)) as [S1 [A1 B1]].
  set (S2 :=
    match out1 with
    | Out_break => State f Sskip k e m2
    | _ => S1
    end).
  exists S2; split.
  eapply star_left. right; apply step_for.
  eapply star_trans. apply H0.
  eapply star_left. right; eapply step_for_true; eauto.
  eapply star_trans. eexact A1.
  unfold S2. inversion H4; subst.
  inv B1. apply star_one. right; constructor.
  apply star_refl.
  reflexivity. reflexivity. reflexivity. traceEq.
  unfold S2. inversion H4; subst. constructor. inv B1; econstructor; eauto.

(* for loop *)
  destruct (H3 f (Kfor3 a2 a3 s k)) as [S1 [A1 B1]].
  destruct (H6 f (Kfor4 a2 a3 s k)) as [S2 [A2 B2]]; auto. inv B2.
  destruct (H8 f k) as [S3 [A3 B3]]; auto.
  exists S3; split.
  eapply star_left. right; apply step_for.
  eapply star_trans. apply H0.
  eapply star_left. right; eapply step_for_true; eauto.
  eapply star_trans. eexact A1.
  eapply star_trans with (s2 := State f a3 (Kfor4 a2 a3 s k) e m2).
  inv H4; inv B1.
  apply star_one. right; constructor; auto.
  apply star_one. right; constructor; auto.
  eapply star_trans. eexact A2.
  eapply star_left. right; constructor.
  eexact A3.
  reflexivity. reflexivity. reflexivity. reflexivity.
  reflexivity. reflexivity. traceEq.
  auto.

(* switch *)
  destruct (H3 f (Kswitch2 k)) as [S1 [A1 B1]].
  set (S2 :=
    match out with
    | Out_normal => State f Sskip k e m2
    | Out_break => State f Sskip k e m2
    | Out_continue => State f Scontinue k e m2
    | _ => S1
    end).
  exists S2; split.
  eapply star_left. right; eapply step_switch.
  eapply star_trans. apply H0.
  eapply star_left. right; eapply step_expr_switch. eauto.
  eapply star_trans. eexact A1.
  unfold S2; inv B1.
    apply star_one. right; constructor. auto.
    apply star_one. right; constructor. auto.
    apply star_one. right; constructor.
    apply star_refl.
    apply star_refl.
  reflexivity. reflexivity. reflexivity. traceEq.
  unfold S2. inv B1; simpl; econstructor; eauto.

(* call internal *)
  destruct (H3 f k) as [S1 [A1 B1]].
  eapply star_left. right; eapply step_internal_function; eauto.
  eapply star_right. eexact A1.
  inv B1; simpl in H4; try contradiction.
  (* Out_normal *)
  assert (fn_return f = Tvoid /\ vres = Vundef).
    destruct (fn_return f); auto || contradiction.
  destruct H7 as [P Q]. subst vres. right; eapply step_skip_call; eauto.
  (* Out_return None *)
  assert (fn_return f = Tvoid /\ vres = Vundef).
    destruct (fn_return f); auto || contradiction.
  destruct H8 as [P Q]. subst vres.
  rewrite <- (is_call_cont_call_cont k H6). rewrite <- H7.
  right; apply step_return_0; auto.
  (* Out_return Some *)
  destruct H4. rewrite <- (is_call_cont_call_cont k H6). rewrite <- H7.
  right; eapply step_return_2; eauto.
  reflexivity. traceEq.

(* call external *)
  apply star_one. simpl in *. subst. right; eapply step_external_function; eauto.
Qed.

Lemma eval_expression_to_steps:
   forall e m a t m' v,
   eval_expression e m a t m' v ->
   forall f k,
   star step se ge (ExprState f a k e m) t (ExprState f (Eval v (typeof a)) k e m').
Proof (proj1 bigstep_to_steps).

Lemma eval_expr_to_steps:
   forall e m K a t m' a',
   eval_expr e m K a t m' a' ->
   forall C f k, leftcontext K RV C ->
   simple a' = true /\ typeof a' = typeof a /\
   star step se ge (ExprState f (C a) k e m) t (ExprState f (C a') k e m').
Proof (proj1 (proj2 bigstep_to_steps)).

Lemma eval_exprlist_to_steps:
   forall e m al t m' al',
   eval_exprlist e m al t m' al' ->
   forall a1 al2 ty C f k, leftcontext RV RV C -> simple a1 = true -> simplelist al2 = true ->
   simplelist al' = true /\
   star step se ge (ExprState f (C (Ecall a1 (exprlist_app al2 al) ty)) k e m)
              t (ExprState f (C (Ecall a1 (exprlist_app al2 al') ty)) k e m').
Proof (proj1 (proj2 (proj2 bigstep_to_steps))).

Lemma exec_stmt_to_steps:
   forall e m s t m' out,
   exec_stmt e m s t m' out ->
   forall f k,
   exists S,
   star step se ge (State f s k e m) t S /\ outcome_state_match e m' f k out S.
Proof (proj1 (proj2 (proj2 (proj2 bigstep_to_steps)))).

Lemma eval_funcall_to_steps:
  forall m fd args t m' res,
  eval_funcall m fd args t m' res ->
  forall vf k
  (FPTR: Genv.find_funct ge vf = Some fd),
  is_call_cont k ->
  star step se ge (Callstate vf (type_of_fundef fd) args k m) t (Returnstate res k m').
Proof (proj2 (proj2 (proj2 (proj2 bigstep_to_steps)))).

Fixpoint esize (a: expr) : nat :=
  match a with
  | Eloc _ _ _ => 1%nat
  | Evar _ _ => 1%nat
  | Ederef r1 _ => S(esize r1)
  | Efield l1 _ _ => S(esize l1)
  | Eval _ _ => O
  | Evalof l1 _ => S(esize l1)
  | Eaddrof l1 _ => S(esize l1)
  | Eunop _ r1 _ => S(esize r1)
  | Ebinop _ r1 r2 _ => S(esize r1 + esize r2)%nat
  | Ecast r1 _ => S(esize r1)
  | Eseqand r1 r2 _ => S(esize r1)
  | Eseqor r1 r2 _ => S(esize r1)
  | Econdition r1 _ _ _ => S(esize r1)
  | Esizeof _ _ => 1%nat
  | Ealignof _ _ => 1%nat
  | Eassign l1 r2 _ => S(esize l1 + esize r2)%nat
  | Eassignop _ l1 r2 _ _ => S(esize l1 + esize r2)%nat
  | Epostincr _ l1 _ => S(esize l1)
  | Ecomma r1 r2 _ => S(esize r1 + esize r2)%nat
  | Ecall r1 rl2 _ => S(esize r1 + esizelist rl2)%nat
  | Ebuiltin ef tyargs rl _ => S(esizelist rl)
  | Eparen r1 _ _ => S(esize r1)
  end

with esizelist (el: exprlist) : nat :=
  match el with
  | Enil => O
  | Econs r1 rl2 => S(esize r1 + esizelist rl2)%nat
  end.

Lemma leftcontext_size:
  forall from to C,
  leftcontext from to C ->
  forall e1 e2,
  (esize e1 < esize e2)%nat ->
  (esize (C e1) < esize (C e2))%nat
with leftcontextlist_size:
  forall from C,
  leftcontextlist from C ->
  forall e1 e2,
  (esize e1 < esize e2)%nat ->
  (esizelist (C e1) < esizelist (C e2))%nat.
Proof.
  induction 1; intros; simpl; auto with arith.
  exploit leftcontextlist_size; eauto. auto with arith.
  exploit leftcontextlist_size; eauto. auto with arith.
  induction 1; intros; simpl; auto with arith.
  exploit leftcontext_size; eauto. auto with arith.
Qed.

Lemma evalinf_funcall_steps:
  forall m fd args t k,
  evalinf_funcall m fd args t ->
  forall vf
  (FPTR: Genv.find_funct ge vf = Some fd),
  forever_N step se lt ge O (Callstate vf (type_of_fundef fd) args k m) t.
Proof.
  cofix COF.

  assert (COS:
    forall e m s t f k,
    execinf_stmt e m s t ->
    forever_N step se lt ge O (State f s k e m) t).
  cofix COS.

  assert (COE:
    forall e m K a t C f k,
    evalinf_expr e m K a t ->
    leftcontext K RV C ->
    forever_N step se lt ge (esize a) (ExprState f (C a) k e m) t).
  cofix COE.

  assert (COEL:
    forall e m a t C f k a1 al ty,
    evalinf_exprlist e m a t ->
    leftcontext RV RV C -> simple a1 = true -> simplelist al = true ->
    forever_N step se lt ge (esizelist a)
                   (ExprState f (C (Ecall a1 (exprlist_app al a) ty)) k e m) t).
  cofix COEL.
  intros. inv H.
(* cons left *)
  eapply forever_N_star with (a2 := (esize a0)). apply star_refl. simpl; omega.
  eapply COE with (C := fun x => C(Ecall a1 (exprlist_app al (Econs x al0)) ty)).
  eauto. eapply leftcontext_compose; eauto. constructor. auto.
  apply exprlist_app_leftcontext; auto. traceEq.
(* cons right *)
  destruct (eval_expr_to_steps _ _ _ _ _ _ _ H3
             (fun x => C(Ecall a1 (exprlist_app al (Econs x al0)) ty)) f k)
  as [P [Q R]].
  eapply leftcontext_compose; eauto. repeat constructor. auto.
  apply exprlist_app_leftcontext; auto.
  eapply forever_N_star with (a2 := (esizelist al0)).
  eexact R. simpl; omega.
  change (Econs a1' al0) with (exprlist_app (Econs a1' Enil) al0).
  rewrite <- exprlist_app_assoc.
  eapply COEL. eauto. auto. auto.
  rewrite exprlist_app_simple. simpl. rewrite H2; rewrite P; auto.
  auto.

  intros. inv H.
(* field *)
  eapply forever_N_star with (a2 := (esize a0)). apply star_refl. simpl; omega.
  eapply COE with (C := fun x => C(Efield x f0 ty)). eauto.
  eapply leftcontext_compose; eauto. repeat constructor. traceEq.
(* valof *)
  eapply forever_N_star with (a2 := (esize a0)). apply star_refl. simpl; omega.
  eapply COE with (C := fun x => C(Evalof x ty)). eauto.
  eapply leftcontext_compose; eauto. repeat constructor. traceEq.
(* deref *)
  eapply forever_N_star with (a2 := (esize a0)). apply star_refl. simpl; omega.
  eapply COE with (C := fun x => C(Ederef x ty)). eauto.
  eapply leftcontext_compose; eauto. repeat constructor. traceEq.
(* addrof *)
  eapply forever_N_star with (a2 := (esize a0)). apply star_refl. simpl; omega.
  eapply COE with (C := fun x => C(Eaddrof x ty)). eauto.
  eapply leftcontext_compose; eauto. repeat constructor. traceEq.
(* unop *)
  eapply forever_N_star with (a2 := (esize a0)). apply star_refl. simpl; omega.
  eapply COE with (C := fun x => C(Eunop op x ty)). eauto.
  eapply leftcontext_compose; eauto. repeat constructor. traceEq.
(* binop left *)
  eapply forever_N_star with (a2 := (esize a1)). apply star_refl. simpl; omega.
  eapply COE with (C := fun x => C(Ebinop op x a2 ty)). eauto.
  eapply leftcontext_compose; eauto. repeat constructor. traceEq.
(* binop right *)
  destruct (eval_expr_to_steps _ _ _ _ _ _ _ H1 (fun x => C(Ebinop op x a2 ty)) f k)
  as [P [Q R]].
  eapply leftcontext_compose; eauto. repeat constructor.
  eapply forever_N_star with (a2 := (esize a2)). eexact R. simpl; omega.
  eapply COE with (C := fun x => C(Ebinop op a1' x ty)). eauto.
  eapply leftcontext_compose; eauto. repeat constructor. auto. traceEq.
(* cast *)
  eapply forever_N_star with (a2 := (esize a0)). apply star_refl. simpl; omega.
  eapply COE with (C := fun x => C(Ecast x ty)). eauto.
  eapply leftcontext_compose; eauto. repeat constructor. traceEq.
(* seqand left *)
  eapply forever_N_star with (a2 := (esize a1)). apply star_refl. simpl; omega.
  eapply COE with (C := fun x => C(Eseqand x a2 ty)). eauto.
  eapply leftcontext_compose; eauto. repeat constructor. traceEq.
(* seqand 2 *)
  destruct (eval_expr_to_steps _ _ _ _ _ _ _ H1 (fun x => C(Eseqand x a2 ty)) f k)
  as [P [Q R]].
  eapply leftcontext_compose; eauto. repeat constructor.
  eapply forever_N_plus. eapply plus_right. eexact R.
  left; eapply step_seqand_true; eauto. rewrite Q; eauto.
  reflexivity.
  eapply COE with (C := fun x => (C (Eparen x type_bool ty))). eauto.
  eapply leftcontext_compose; eauto. repeat constructor. traceEq.
(* seqor left *)
  eapply forever_N_star with (a2 := (esize a1)). apply star_refl. simpl; omega.
  eapply COE with (C := fun x => C(Eseqor x a2 ty)). eauto.
  eapply leftcontext_compose; eauto. repeat constructor. traceEq.
(* seqor 2 *)
  destruct (eval_expr_to_steps _ _ _ _ _ _ _ H1 (fun x => C(Eseqor x a2 ty)) f k)
  as [P [Q R]].
  eapply leftcontext_compose; eauto. repeat constructor.
  eapply forever_N_plus. eapply plus_right. eexact R.
  left; eapply step_seqor_false; eauto. rewrite Q; eauto.
  reflexivity.
  eapply COE with (C := fun x => (C (Eparen x type_bool ty))). eauto.
  eapply leftcontext_compose; eauto. repeat constructor. traceEq.
(* condition top *)
  eapply forever_N_star with (a2 := (esize a1)). apply star_refl. simpl; omega.
  eapply COE with (C := fun x => C(Econdition x a2 a3 ty)). eauto.
  eapply leftcontext_compose; eauto. repeat constructor. traceEq.
(* condition *)
  destruct (eval_expr_to_steps _ _ _ _ _ _ _ H1 (fun x => C(Econdition x a2 a3 ty)) f k)
  as [P [Q R]].
  eapply leftcontext_compose; eauto. repeat constructor.
  eapply forever_N_plus. eapply plus_right. eexact R.
  left; eapply step_condition; eauto. rewrite Q; eauto.
  reflexivity.
  eapply COE with (C := fun x => (C (Eparen x ty ty))). eauto.
  eapply leftcontext_compose; eauto. repeat constructor. traceEq.
(* assign left *)
  eapply forever_N_star with (a2 := (esize a1)). apply star_refl. simpl; omega.
  eapply COE with (C := fun x => C(Eassign x a2 ty)). eauto.
  eapply leftcontext_compose; eauto. repeat constructor. traceEq.
(* assign right *)
  destruct (eval_expr_to_steps _ _ _ _ _ _ _ H1 (fun x => C(Eassign x a2 ty)) f k)
  as [P [Q R]].
  eapply leftcontext_compose; eauto. repeat constructor.
  eapply forever_N_star with (a2 := (esize a2)). eexact R. simpl; omega.
  eapply COE with (C := fun x => C(Eassign a1' x ty)). eauto.
  eapply leftcontext_compose; eauto. repeat constructor. auto. traceEq.
(* assignop left *)
  eapply forever_N_star with (a2 := (esize a1)). apply star_refl. simpl; omega.
  eapply COE with (C := fun x => C(Eassignop op x a2 tyres ty)). eauto.
  eapply leftcontext_compose; eauto. repeat constructor. traceEq.
(* assignop right *)
  destruct (eval_expr_to_steps _ _ _ _ _ _ _ H1 (fun x => C(Eassignop op x a2 tyres ty)) f k)
  as [P [Q R]].
  eapply leftcontext_compose; eauto. repeat constructor.
  eapply forever_N_star with (a2 := (esize a2)). eexact R. simpl; omega.
  eapply COE with (C := fun x => C(Eassignop op a1' x tyres ty)). eauto.
  eapply leftcontext_compose; eauto. repeat constructor. auto. traceEq.
(* postincr *)
  eapply forever_N_star with (a2 := (esize a0)). apply star_refl. simpl; omega.
  eapply COE with (C := fun x => C(Epostincr id x ty)). eauto.
  eapply leftcontext_compose; eauto. repeat constructor. traceEq.
(* comma left *)
  eapply forever_N_star with (a2 := (esize a1)). apply star_refl. simpl; omega.
  eapply COE with (C := fun x => C(Ecomma x a2 ty)). eauto.
  eapply leftcontext_compose; eauto. repeat constructor. traceEq.
(* comma right *)
  destruct (eval_expr_to_steps _ _ _ _ _ _ _ H1 (fun x => C(Ecomma x a2 (typeof a2))) f k)
  as [P [Q R]].
  eapply leftcontext_compose; eauto. repeat constructor.
  eapply forever_N_plus. eapply plus_right. eexact R.
  left; eapply step_comma; eauto. reflexivity.
  eapply COE with (C := C); eauto. traceEq.
(* call left *)
  eapply forever_N_star with (a2 := (esize a1)). apply star_refl. simpl; omega.
  eapply COE with (C := fun x => C(Ecall x a2 ty)). eauto.
  eapply leftcontext_compose; eauto. repeat constructor. traceEq.
(* call right *)
  destruct (eval_expr_to_steps _ _ _ _ _ _ _ H1 (fun x => C(Ecall x a2 ty)) f k)
  as [P [Q R]].
  eapply leftcontext_compose; eauto. repeat constructor.
  eapply forever_N_star with (a2 := (esizelist a2)). eexact R. simpl; omega.
  eapply COEL with (al := Enil). eauto. auto. auto. auto. traceEq.
(* call *)
  destruct (eval_expr_to_steps _ _ _ _ _ _ _ H1 (fun x => C(Ecall x rargs ty)) f k)
  as [P [Q R]].
  eapply leftcontext_compose; eauto. repeat constructor.
  destruct (eval_exprlist_to_steps _ _ _ _ _ _ H2 rf' Enil ty C f k)
  as [S T]. auto. auto. simpl; auto.
  unfold Genv.find_funct in *. des_ifs.
  eapply forever_N_plus. eapply plus_right.
  eapply star_trans. eexact R. eexact T. reflexivity.
  simpl. left; eapply step_call; eauto. rewrite Q. eauto. reflexivity. rewrite <- H7.
  apply COF; eauto. traceEq.

(* statements *)
  intros. inv H.
(* do *)
  eapply forever_N_plus. apply plus_one; right; constructor.
  eapply COE with (C := fun x => x); eauto. constructor. traceEq.
(* seq 1 *)
  eapply forever_N_plus. apply plus_one; right; constructor.
  eapply COS; eauto. traceEq.
(* seq 2 *)
  destruct (exec_stmt_to_steps _ _ _ _ _ _ H0 f (Kseq s2 k)) as [S1 [A1 B1]]; auto. inv B1.
  eapply forever_N_plus.
  eapply plus_left. right; constructor.
  eapply star_right. eauto. right; constructor.
  reflexivity. reflexivity.
  eapply COS; eauto. traceEq.
(* if test *)
  eapply forever_N_plus. apply plus_one; right; constructor.
  eapply COE with (C := fun x => x); eauto. constructor. traceEq.
(* if true/false *)
  eapply forever_N_plus.
  eapply plus_left. right; constructor.
  eapply star_right. eapply eval_expression_to_steps; eauto.
  right. eapply step_ifthenelse_2 with (b := b). auto.
  reflexivity. reflexivity.
  eapply COS; eauto. traceEq.
(* return some *)
  eapply forever_N_plus. apply plus_one; right; constructor.
  eapply COE with (C := fun x => x); eauto. constructor. traceEq.
(* while test *)
  eapply forever_N_plus. apply plus_one; right; constructor.
  eapply COE with (C := fun x => x); eauto. constructor. traceEq.
(* while body *)
  eapply forever_N_plus.
  eapply plus_left. right; constructor.
  eapply star_right. eapply eval_expression_to_steps; eauto.
  right; apply step_while_true; auto.
  reflexivity. reflexivity.
  eapply COS; eauto. traceEq.
(* while loop *)
  destruct (exec_stmt_to_steps _ _ _ _ _ _ H2 f (Kwhile2 a s0 k)) as [S1 [A1 B1]]; auto.
  eapply forever_N_plus.
  eapply plus_left. right; constructor.
  eapply star_trans. eapply eval_expression_to_steps; eauto.
  eapply star_left. right; apply step_while_true; auto.
  eapply star_trans. eexact A1.
  inv H3; inv B1; apply star_one; right; apply step_skip_or_continue_while; auto.
  reflexivity. reflexivity. reflexivity. reflexivity.
  eapply COS; eauto. traceEq.
(* dowhile body *)
  eapply forever_N_plus. apply plus_one; right; constructor.
  eapply COS; eauto. traceEq.
(* dowhile test *)
  destruct (exec_stmt_to_steps _ _ _ _ _ _ H0 f (Kdowhile1 a s0 k)) as [S1 [A1 B1]]; auto.
  eapply forever_N_plus.
  eapply plus_left. right; constructor.
  eapply star_trans. eexact A1.
  eapply star_one. right. inv H1; inv B1; apply step_skip_or_continue_dowhile; auto.
  reflexivity. reflexivity.
  eapply COE with (C := fun x => x); eauto. constructor. traceEq.
(* dowhile loop *)
  destruct (exec_stmt_to_steps _ _ _ _ _ _ H0 f (Kdowhile1 a s0 k)) as [S1 [A1 B1]]; auto.
  eapply forever_N_plus.
  eapply plus_left. right; constructor.
  eapply star_trans. eexact A1.
  eapply star_left. right. inv H1; inv B1; apply step_skip_or_continue_dowhile; auto.
  eapply star_right. eapply eval_expression_to_steps; eauto.
  right; apply step_dowhile_true; auto.
  reflexivity. reflexivity. reflexivity. reflexivity.
  eapply COS; eauto. traceEq.
(* for start 1 *)
  assert (a1 <> Sskip). red; intros; subst a1; inv H0.
  eapply forever_N_plus. apply plus_one. right. constructor. auto.
  eapply COS; eauto. traceEq.
(* for start 2 *)
  destruct (exec_stmt_to_steps _ _ _ _ _ _ H0 f (Kseq (Sfor Sskip a2 a3 s0) k)) as [S1 [A1 B1]]; auto. inv B1.
  eapply forever_N_plus.
  eapply plus_left. right; constructor. auto.
  eapply star_trans. eexact A1.
  apply star_one. right; constructor.
  reflexivity. reflexivity.
  eapply COS; eauto. traceEq.
(* for test *)
  eapply forever_N_plus. apply plus_one; right; apply step_for.
  eapply COE with (C := fun x => x); eauto. constructor. traceEq.
(* for body *)
  eapply forever_N_plus.
  eapply plus_left. right; apply step_for.
  eapply star_right. eapply eval_expression_to_steps; eauto.
  right; apply step_for_true; auto.
  reflexivity. reflexivity.
  eapply COS; eauto. traceEq.
(* for next *)
  destruct (exec_stmt_to_steps _ _ _ _ _ _ H2 f (Kfor3 a2 a3 s0 k)) as [S1 [A1 B1]]; auto.
  eapply forever_N_plus.
  eapply plus_left. right; apply step_for.
  eapply star_trans. eapply eval_expression_to_steps; eauto.
  eapply star_left. right; apply step_for_true; auto.
  eapply star_trans. eexact A1.
  inv H3; inv B1; apply star_one; right; apply step_skip_or_continue_for3; auto.
  reflexivity. reflexivity. reflexivity. reflexivity.
  eapply COS; eauto. traceEq.
(* for loop *)
  destruct (exec_stmt_to_steps _ _ _ _ _ _ H2 f (Kfor3 a2 a3 s0 k)) as [S1 [A1 B1]]; auto.
  destruct (exec_stmt_to_steps _ _ _ _ _ _ H4 f (Kfor4 a2 a3 s0 k)) as [S2 [A2 B2]]; auto. inv B2.
  eapply forever_N_plus.
  eapply plus_left. right; apply step_for.
  eapply star_trans. eapply eval_expression_to_steps; eauto.
  eapply star_left. right; apply step_for_true; auto.
  eapply star_trans. eexact A1.
  eapply star_left.
  inv H3; inv B1; right; apply step_skip_or_continue_for3; auto.
  eapply star_right. eexact A2.
  right; constructor.
  reflexivity. reflexivity. reflexivity. reflexivity. reflexivity. reflexivity.
  eapply COS; eauto. traceEq.
(* switch expr *)
  eapply forever_N_plus. apply plus_one; right; constructor.
  eapply COE with (C := fun x => x); eauto. constructor. traceEq.
(* switch body *)
  eapply forever_N_plus.
  eapply plus_left. right; constructor.
  eapply star_right. eapply eval_expression_to_steps; eauto.
  right; constructor. eauto.
  reflexivity. reflexivity.
  eapply COS; eauto. traceEq.

(* funcalls *)
  intros. inv H.
  eapply forever_N_plus. apply plus_one. right; econstructor; eauto.
  eapply COS; eauto. traceEq.
Qed.

End BIGSTEP.

(** ** Whole-program behaviors, big-step style. *)

Inductive bigstep_program_terminates (p: program): trace -> int -> Prop :=
  | bigstep_program_terminates_intro: forall b f m0 m1 t r,
      let ge := globalenv p in
      Genv.init_mem p = Some m0 ->
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      type_of_fundef f = Tfunction Tnil type_int32s cc_default ->
      eval_funcall ge ge m0 f nil t m1 (Vint r) ->
      bigstep_program_terminates p t r.

Inductive bigstep_program_diverges (p: program): traceinf -> Prop :=
  | bigstep_program_diverges_intro: forall b f m0 t,
      let ge := globalenv p in
      Genv.init_mem p = Some m0 ->
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      type_of_fundef f = Tfunction Tnil type_int32s cc_default ->
      evalinf_funcall ge ge m0 f nil t ->
      bigstep_program_diverges p t.

Definition bigstep_semantics (p: program) :=
  Bigstep_semantics (bigstep_program_terminates p) (bigstep_program_diverges p).

Theorem bigstep_semantics_sound:
  forall p, bigstep_sound (bigstep_semantics p) (semantics p).
Proof.
  intros; constructor; intros.
(* termination *)
  inv H. econstructor; econstructor.
  split. econstructor; eauto.
  split. rewrite <- H3. apply eval_funcall_to_steps; eauto. red; auto.
  econstructor.
(* divergence *)
  inv H. econstructor.
  split. econstructor; eauto.
  eapply forever_N_forever with (order := lt).
  apply lt_wf.
  rewrite <- H3. eapply evalinf_funcall_steps; eauto.
Qed.
