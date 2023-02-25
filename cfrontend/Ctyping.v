(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU Lesser General Public License as        *)
(*  published by the Free Software Foundation, either version 2.1 of   *)
(*  the License, or  (at your option) any later version.               *)
(*  This file is also distributed under the terms of the               *)
(*  INRIA Non-Commercial License Agreement.                            *)
(*                                                                     *)
(* *********************************************************************)

(** Typing rules and type-checking for the Compcert C language *)

Require Import SetoidList.
Require Import String.
Require Import Coqlib Maps Integers Floats Errors.
Require Import AST Linking.
Require Import Values Memory Globalenvs Builtins Events.
Require Import Ctypes Cop Csyntax Csem.
Require Import Classical.
Require Import sflib.

Local Open Scope error_monad_scope.



Lemma InA_In_iff: forall X x xs, @InA X eq x xs <-> @In X x xs.
Proof.
  induction xs; split; ii; ss; try inv H; eauto.
  all: right; eapply IHxs; eauto.
Qed.

Section WTTY.

  Variable ce: composite_env.

  Fixpoint wt_type (t: type) : bool :=
    match t with
    | Tarray t' _ _ => wt_type t'
    | Tpointer t' _ => wt_type t'
    | Tstruct id _ | Tunion id _ =>
                     match ce!id with Some co => true | None => false end
    | _ => true
    end.

  Lemma wt_type_sizeof_stable:
    forall t ce'
       (extends: forall id co, ce!id = Some co -> ce'!id = Some co), wt_type t = true -> sizeof ce t = sizeof ce' t.
  Proof.
    induction t; simpl; intros; auto.
    - erewrite IHt; eauto.
    - destruct (ce!i) as [co|] eqn:E; try discriminate.
      erewrite extends by eauto. auto.
    - destruct (ce!i) as [co|] eqn:E; try discriminate.
      erewrite extends by eauto. auto.
  Qed.

  Lemma wt_type_alignof_stable:
    forall t ce'
       (extends: forall id co, ce!id = Some co -> ce'!id = Some co), wt_type t = true -> alignof ce t = alignof ce' t.
  Proof.
    induction t; simpl; intros; auto.
    - erewrite IHt; eauto.
    - destruct (ce!i) as [co|] eqn:E; try discriminate.
      erewrite extends by eauto. auto.
    - destruct (ce!i) as [co|] eqn:E; try discriminate.
      erewrite extends by eauto. auto.
  Qed.

  Fixpoint types_of_expr (e: expr): list type :=
    match e with
    | Eval _ ty => [ty]
    | Evar _ ty => [ty]
    | Efield e0 _ ty => types_of_expr e0 ++ [ty]
    | Evalof e0 ty => types_of_expr e0 ++ [ty]
    | Ederef e0 ty => types_of_expr e0 ++ [ty]
    | Eaddrof e0 ty => types_of_expr e0 ++ [ty]
    | Eunop _ e0 ty => types_of_expr e0 ++ [ty]
    | Ebinop _ e0 e1 ty => types_of_expr e0 ++ types_of_expr e1 ++ [ty]
    | Ecast e0 ty => types_of_expr e0 ++ [ty]
    | Eseqand e0 e1 ty => types_of_expr e0 ++ types_of_expr e1 ++ [ty]
    | Eseqor e0 e1 ty => types_of_expr e0 ++ types_of_expr e1 ++ [ty]
    | Econdition e0 e1 e2 ty => types_of_expr e0 ++ types_of_expr e1 ++ types_of_expr e2 ++ [ty]
    | Esizeof ty0 ty1 => [ty0 ; ty1]
    | Ealignof ty0 ty1 => [ty0 ; ty1]
    | Eassign e0 e1 ty => types_of_expr e0 ++ types_of_expr e1 ++ [ty]
    | Eassignop _ e0 e1 ty0 ty1 => types_of_expr e0 ++ types_of_expr e1 ++ [ty0 ; ty1]
    | Epostincr _ e0 ty => types_of_expr e0 ++ [ty]
    | Ecomma e0 e1 ty => types_of_expr e0 ++ types_of_expr e1 ++ [ty]
    | Ecall e0 es ty => types_of_expr e0 ++ types_of_exprlist es ++ [ty]
    | Ebuiltin _ tys es ty => typelist_to_listtype tys ++ types_of_exprlist es ++ [ty]
    | Eloc _ _ _ ty => [ty]
    | Eparen e0 ty0 ty1 => types_of_expr e0 ++ [ty0 ; ty1]
    end
  with
  types_of_exprlist (es: exprlist): list type :=
    match es with
    | Enil => []
    | Econs e es => types_of_expr e ++ types_of_exprlist es
    end.

  Fixpoint types_of_statement (stmt: statement): list type :=
    match stmt with
    | Sdo e0 => types_of_expr e0
    | Ssequence stmt0 stmt1 => types_of_statement stmt0 ++ types_of_statement stmt1
    | Sifthenelse e0 stmt0 stmt1 => types_of_expr e0 ++ types_of_statement stmt0 ++ types_of_statement stmt1
    | Swhile e0 stmt0 => types_of_expr e0 ++ types_of_statement stmt0
    | Sdowhile e0 stmt0 => types_of_expr e0 ++ types_of_statement stmt0
    | Sfor stmt0 e0 stmt1 stmt2 => types_of_expr e0 ++ types_of_statement stmt0 ++ types_of_statement stmt1
                                                 ++ types_of_statement stmt2
    | Sreturn e0_ => match e0_ with
                     | Some e0 => types_of_expr e0
                     | _ => []
                     end
    | Sswitch e0 lstmt0 => types_of_expr e0 ++ types_of_labeled_statements lstmt0
    | Slabel _ stmt0 => types_of_statement stmt0
    | _ => []
    end
  with
  types_of_labeled_statements (lstmt: labeled_statements): list type :=
    match lstmt with
    | LSnil => []
    | LScons _ stmt lstmt => types_of_statement stmt ++ types_of_labeled_statements lstmt
    end.

  Fixpoint types_of_cont (k: cont): list type :=
    match k with
    | Kstop => []
    | Kdo k0 => types_of_cont k0
    | Kseq stmt0 k0 => types_of_statement stmt0 ++ types_of_cont k0
    | Kifthenelse stmt0 stmt1 k0 => types_of_statement stmt0 ++ types_of_statement stmt1 ++ types_of_cont k0
    | Kwhile1 e0 stmt0 k0 => types_of_expr e0 ++ types_of_statement stmt0 ++ types_of_cont k0
    | Kwhile2 e0 stmt0 k0 => types_of_expr e0 ++ types_of_statement stmt0 ++ types_of_cont k0
    | Kdowhile1 e0 stmt0 k0 => types_of_expr e0 ++ types_of_statement stmt0 ++ types_of_cont k0
    | Kdowhile2 e0 stmt0 k0 => types_of_expr e0 ++ types_of_statement stmt0 ++ types_of_cont k0
    | Kfor2 e0 stmt0 stmt1 k0 => types_of_expr e0 ++ types_of_statement stmt0 ++ types_of_statement stmt1 ++ types_of_cont k0
    | Kfor3 e0 stmt0 stmt1 k0 => types_of_expr e0 ++ types_of_statement stmt0 ++ types_of_statement stmt1 ++ types_of_cont k0
    | Kfor4 e0 stmt0 stmt1 k0 => types_of_expr e0 ++ types_of_statement stmt0 ++ types_of_statement stmt1 ++ types_of_cont k0
    | Kswitch1 lstmt0 k0 => types_of_labeled_statements lstmt0 ++ types_of_cont k0
    | Kswitch2 k0 => types_of_cont k0
    | Kreturn k0 => types_of_cont k0
    | Kcall f e C ty k0  => types_of_statement f.(fn_body) ++ [ty] ++ types_of_cont k0
    end.

  Fixpoint wtype_cont (k: cont): Prop :=
    match k with
    | Kstop => True
    | Kdo k0 => wtype_cont k0
    | Kseq stmt0 k0 => wtype_cont k0 /\ forall ty (IN: In ty (types_of_statement stmt0)), wt_type ty
    | Kifthenelse stmt0 stmt1 k0 =>
      wtype_cont k0 /\ forall ty (IN: In ty (types_of_statement stmt0 ++ types_of_statement stmt1)), wt_type ty
    | Kwhile1 e0 stmt0 k0 =>
      wtype_cont k0 /\ forall ty (IN: In ty (types_of_expr e0 ++ types_of_statement stmt0)), wt_type ty
    | Kwhile2 e0 stmt0 k0 =>
      wtype_cont k0 /\ forall ty (IN: In ty (types_of_expr e0 ++ types_of_statement stmt0)), wt_type ty
    | Kdowhile1 e0 stmt0 k0 =>
      wtype_cont k0 /\ forall ty (IN: In ty (types_of_expr e0 ++ types_of_statement stmt0)), wt_type ty
    | Kdowhile2 e0 stmt0 k0 =>
      wtype_cont k0 /\ forall ty (IN: In ty (types_of_expr e0 ++ types_of_statement stmt0)), wt_type ty
    | Kfor2 e0 stmt0 stmt1 k0 =>
      wtype_cont k0 /\ forall ty (IN: In ty (types_of_expr e0 ++ types_of_statement stmt0 ++ types_of_statement stmt1)), wt_type ty
    | Kfor3 e0 stmt0 stmt1 k0 =>
      wtype_cont k0 /\ forall ty (IN: In ty (types_of_expr e0 ++ types_of_statement stmt0 ++ types_of_statement stmt1)), wt_type ty
    | Kfor4 e0 stmt0 stmt1 k0 =>
      wtype_cont k0 /\ forall ty (IN: In ty (types_of_expr e0 ++ types_of_statement stmt0 ++ types_of_statement stmt1)), wt_type ty
    | Kswitch1 lstmt0 k0 =>
      wtype_cont k0 /\ forall ty (IN: In ty (types_of_labeled_statements lstmt0)), wt_type ty
    | Kswitch2 k0 => wtype_cont k0
    | Kreturn k0 => wtype_cont k0
    | Kcall f e C ty k0  =>
      wtype_cont k0 /\
      (forall e0, (forall ty (IN: In ty (types_of_expr e0)), wt_type ty) ->
                 (forall ty (IN: In ty (types_of_expr (C e0))), wt_type ty)) /\
      (forall ty (IN: In ty (types_of_statement f.(fn_body))), wt_type ty) /\
      wt_type ty /\
      (forall i blk ty, e ! i = Some (blk, ty) -> wt_type ty) /\
      context RV RV C
    end
  .

  (* Copied from Cstrategy *)
  Scheme context_ind2 := Minimality for context Sort Prop
    with contextlist_ind2 := Minimality for contextlist Sort Prop.
  Combined Scheme context_contextlist_ind from context_ind2, contextlist_ind2.

  Notation "a t= b" := (@equivlistA type eq a b) (at level 100).

  Lemma types_of_context:
      (forall k k0 C, context k k0 C -> exists tys, forall a, types_of_expr (C a) t= types_of_expr a ++ tys) /\
      (forall k C, contextlist k C -> exists tys, forall a, types_of_exprlist (C a) t= types_of_expr a ++ tys).
  Proof.
    eapply context_contextlist_ind; i; des; ss;
      try (by esplits; eauto; ii; erewrite H0; eauto; repeat (rewrite <-app_assoc; f_equal; eauto)).
    - eexists nil. ii. rewrite app_nil_r. ss.
    - exists (types_of_expr e1 ++ tys ++ [ty]). esplits; eauto. ii.
      erewrite H0; eauto. repeat rewrite InA_app_iff. split; i; des; eauto.
    - exists (types_of_expr e1 ++ tys ++ [ty]). esplits; eauto. ii.
      erewrite H0; eauto. repeat rewrite InA_app_iff. split; i; des; eauto.
    - exists (types_of_expr e1 ++ tys ++ [tyres ; ty]). esplits; eauto. ii.
      erewrite H0; eauto. repeat rewrite InA_app_iff. split; i; des; eauto.
    - exists (types_of_expr e1 ++ tys ++ [ty]). esplits; eauto. ii.
      erewrite H0; eauto. repeat rewrite InA_app_iff. split; i; des; eauto.
    - exists (typelist_to_listtype tyargs ++ tys ++ [ty]). esplits; eauto. ii.
      erewrite H0; eauto. repeat rewrite InA_app_iff. split; i; des; eauto.
    - exists (types_of_expr e1 ++ tys). esplits; eauto. ii.
      erewrite H0; eauto. repeat rewrite InA_app_iff. split; i; des; eauto.
  Qed.

  Lemma types_of_context1
        C k k0
        (CTX: context k k0 C):
      exists tys,
        (forall a ty (IN: In ty (types_of_expr (C a))), In ty (types_of_expr a ++ tys)) /\
        (forall a ty (IN: In ty (types_of_expr a ++ tys)), In ty (types_of_expr (C a))).
  Proof.
    generalize types_of_context. intro X. des.
    exploit X; eauto. i; des.
    exists tys.
    split; ss; eauto.
    - i. apply InA_In_iff. apply InA_In_iff in IN. erewrite H in IN. eauto.
    - i. apply InA_In_iff. apply InA_In_iff in IN. erewrite H. eauto.
  Qed.

End WTTY.

Definition strict := false.
Opaque strict.

Definition size_t : type :=
  if Archi.ptr64 then Tlong Unsigned noattr else Tint I32 Unsigned noattr.

Definition ptrdiff_t : type :=
  if Archi.ptr64 then Tlong Signed noattr else Tint I32 Signed noattr.

(** * Operations over types *)

(** The type of a member of a composite (struct or union).
  The "volatile" attribute carried by the composite propagates
  to the type of the member, but not the "alignas" attribute. *)

Definition attr_add_volatile (vol: bool) (a: attr) :=
  {| attr_volatile := a.(attr_volatile) || vol;
     attr_alignas  := a.(attr_alignas) |}.

Definition type_of_member (a: attr) (f: ident) (m: members) : res type :=
  do ty <- field_type f m;
  OK (change_attributes (attr_add_volatile a.(attr_volatile)) ty).

(** Type-checking of arithmetic and logical operators *)

Definition type_unop (op: unary_operation) (ty: type) : res type :=
  match op with
  | Onotbool =>
      match classify_bool ty with
      | bool_default => Error (msg "operator !")
      | _ => OK (Tint I32 Signed noattr)
      end
  | Onotint =>
      match classify_notint ty with
      | notint_case_i sg => OK (Tint I32 sg noattr)
      | notint_case_l sg => OK (Tlong sg noattr)
      | notint_default   => Error (msg "operator ~")
      end
  | Oneg =>
      match classify_neg ty with
      | neg_case_i sg => OK (Tint I32 sg noattr)
      | neg_case_f => OK (Tfloat F64 noattr)
      | neg_case_s => OK (Tfloat F32 noattr)
      | neg_case_l sg => OK (Tlong sg noattr)
      | neg_default   => Error (msg "operator prefix -")
      end
  | Oabsfloat =>
      match classify_neg ty with
      | neg_default   => Error (msg "operator __builtin_fabs")
      | _             => OK (Tfloat F64 noattr)
      end
  end.

Definition binarith_type (ty1 ty2: type) (m: string): res type :=
  match classify_binarith ty1 ty2 with
  | bin_case_i sg => OK (Tint I32 sg noattr)
  | bin_case_l sg => OK (Tlong sg noattr)
  | bin_case_f => OK (Tfloat F64 noattr)
  | bin_case_s => OK (Tfloat F32 noattr)
  | bin_default   => Error (msg m)
  end.

Definition binarith_int_type (ty1 ty2: type) (m: string): res type :=
  match classify_binarith ty1 ty2 with
  | bin_case_i sg => OK (Tint I32 sg noattr)
  | bin_case_l sg => OK (Tlong sg noattr)
  | _ => Error (msg m)
  end.

Definition shift_op_type (ty1 ty2: type) (m: string): res type :=
  match classify_shift ty1 ty2 with
  | shift_case_ii sg | shift_case_il sg => OK (Tint I32 sg noattr)
  | shift_case_li sg | shift_case_ll sg => OK (Tlong sg noattr)
  | shift_default => Error (msg m)
  end.

Definition comparison_type (ty1 ty2: type) (m: string): res type :=
  match classify_cmp ty1 ty2 with
  | cmp_default =>
      match classify_binarith ty1 ty2 with
      | bin_default => Error (msg m)
      | _ => OK (Tint I32 Signed noattr)
      end
  | _ => OK (Tint I32 Signed noattr)
  end.

Definition type_binop (op: binary_operation) (ty1 ty2: type) : res type :=
  match op with
  | Oadd =>
      match classify_add ty1 ty2 with
      | add_case_pi ty _ | add_case_ip _ ty
      | add_case_pl ty   | add_case_lp ty => OK (Tpointer ty noattr)
      | add_default => binarith_type ty1 ty2 "operator +"
      end
  | Osub =>
      match classify_sub ty1 ty2 with
      | sub_case_pi ty _ | sub_case_pl ty => OK (Tpointer ty noattr)
      | sub_case_pp ty => OK ptrdiff_t
      | sub_default => binarith_type ty1 ty2 "operator infix -"
      end
  | Omul => binarith_type ty1 ty2 "operator infix *"
  | Odiv => binarith_type ty1 ty2 "operator /"
  | Omod => binarith_int_type ty1 ty2 "operator %"
  | Oand => binarith_int_type ty1 ty2 "operator &"
  | Oor => binarith_int_type ty1 ty2 "operator |"
  | Oxor => binarith_int_type ty1 ty2 "operator ^"
  | Oshl => shift_op_type ty1 ty2 "operator <<"
  | Oshr => shift_op_type ty1 ty2 "operator >>"
  | Oeq => comparison_type ty1 ty2 "operator =="
  | One => comparison_type ty1 ty2 "operator !="
  | Olt => comparison_type ty1 ty2 "operator <"
  | Ogt => comparison_type ty1 ty2 "operator >"
  | Ole => comparison_type ty1 ty2 "operator <="
  | Oge => comparison_type ty1 ty2 "operator >="
  end.

Definition type_deref (ty: type) : res type :=
  match ty with
  | Tpointer tyelt _ => OK tyelt
  | Tarray tyelt _ _ => OK tyelt
  | Tfunction _ _ _ => OK ty
  | _ => Error (msg "operator prefix *")
  end.

(** Inferring the type of a conditional expression: the merge of the types
  of the two arms. *)

Definition attr_combine (a1 a2: attr) : attr :=
  {| attr_volatile := a1.(attr_volatile) || a2.(attr_volatile);
     attr_alignas :=
       match a1.(attr_alignas), a2.(attr_alignas) with
       | None, al2 => al2
       | al1, None => al1
       | Some n1, Some n2 => Some (N.max n1 n2)
       end
  |}.

Definition intsize_eq: forall (x y: intsize), {x=y} + {x<>y}.
Proof. decide equality. Defined.

Definition signedness_eq: forall (x y: signedness), {x=y} + {x<>y}.
Proof. decide equality. Defined.

Definition floatsize_eq: forall (x y: floatsize), {x=y} + {x<>y}.
Proof. decide equality. Defined.

Definition callconv_combine (cc1 cc2: calling_convention) : res calling_convention :=
  if option_eq Z.eq_dec cc1.(cc_vararg) cc2.(cc_vararg) then
    OK {| cc_vararg := cc1.(cc_vararg);
          cc_unproto := cc1.(cc_unproto) && cc2.(cc_unproto);
          cc_structret := cc1.(cc_structret) |}
  else
    Error (msg "incompatible calling conventions").

Fixpoint type_combine (ty1 ty2: type) : res type :=
  match ty1, ty2 with
  | Tvoid, Tvoid => OK Tvoid
  | Tint sz1 sg1 a1, Tint sz2 sg2 a2 =>
      if intsize_eq sz1 sz2 && signedness_eq sg1 sg2
      then OK (Tint sz1 sg1 (attr_combine a1 a2))
      else Error (msg "incompatible int types")
  | Tlong sg1 a1, Tlong sg2 a2 =>
      if signedness_eq sg1 sg2
      then OK (Tlong sg1 (attr_combine a1 a2))
      else Error (msg "incompatible long types")
  | Tfloat sz1 a1, Tfloat sz2 a2 =>
      if floatsize_eq sz1 sz2
      then OK (Tfloat sz1 (attr_combine a1 a2))
      else Error (msg "incompatible float types")
  | Tpointer t1 a1, Tpointer t2 a2 =>
      do t <- type_combine t1 t2; OK (Tpointer t (attr_combine a1 a2))
  | Tarray t1 sz1 a1, Tarray t2 sz2 a2 =>
      do t <- type_combine t1 t2;
      if zeq sz1 sz2
      then OK (Tarray t sz1 (attr_combine a1 a2))
      else Error (msg "incompatible array types")
  | Tfunction args1 res1 cc1, Tfunction args2 res2 cc2 =>
      do res <- type_combine res1 res2;
      do args <-
        (if cc1.(cc_unproto) then OK args2 else
         if cc2.(cc_unproto) then OK args1 else
         typelist_combine args1 args2);
      do cc <- callconv_combine cc1 cc2;
      OK (Tfunction args res cc)
  | Tstruct id1 a1, Tstruct id2 a2 =>
      if ident_eq id1 id2
      then OK (Tstruct id1 (attr_combine a1 a2))
      else Error (msg "incompatible struct types")
  | Tunion id1 a1, Tunion id2 a2 =>
      if ident_eq id1 id2
      then OK (Tunion id1 (attr_combine a1 a2))
      else Error (msg "incompatible union types")
  | _, _ =>
      Error (msg "incompatible types")
  end

with typelist_combine (tl1 tl2: typelist) : res typelist :=
  match tl1, tl2 with
  | Tnil, Tnil => OK Tnil
  | Tcons t1 tl1, Tcons t2 tl2 =>
      do t <- type_combine t1 t2;
      do tl <- typelist_combine tl1 tl2;
      OK (Tcons t tl)
  | _, _ =>
      Error (msg "incompatible function types")
  end.

Definition is_void (ty: type) : bool :=
  match ty with Tvoid => true | _ => false end.

Definition type_conditional (ty1 ty2: type) : res type :=
  match typeconv ty1, typeconv ty2 with
  | (Tint _ _ _ | Tlong _ _ | Tfloat _ _),
    (Tint _ _ _ | Tlong _ _ | Tfloat _ _) =>
      binarith_type ty1 ty2 "conditional expression"
  | Tpointer t1 a1, Tpointer t2 a2 =>
      let t :=
        if is_void t1 || is_void t2 then Tvoid else
          match type_combine t1 t2 with
          | OK t => t
          | Error _ => Tvoid   (* tolerance *)
          end
       in OK (Tpointer t noattr)
  | Tpointer t1 a1, Tint _ _ _ =>
      OK (Tpointer t1 noattr)
  | Tint _ _ _, Tpointer t2 a2 =>
      OK (Tpointer t2 noattr)
  | t1, t2 =>
      type_combine t1 t2
  end.

(** * Specification of the type system *)

(** Type environments map identifiers to their types. *)

Definition typenv := PTree.t type.

Definition wt_cast (from to: type) : Prop :=
  classify_cast from to <> cast_case_default.

Definition wt_bool (ty: type) : Prop :=
  classify_bool ty <> bool_default.

Definition wt_int (n: int) (sz: intsize) (sg: signedness) : Prop :=
  match sz, sg with
  | IBool, _ => Int.zero_ext 8 n = n
  | I8, Unsigned => Int.zero_ext 8 n = n
  | I8, Signed => Int.sign_ext 8 n = n
  | I16, Unsigned => Int.zero_ext 16 n = n
  | I16, Signed => Int.sign_ext 16 n = n
  | I32, _ => True
  end.

Inductive wt_val : val -> type -> Prop :=
  | wt_val_int: forall n sz sg a,
      wt_int n sz sg ->
      wt_val (Vint n) (Tint sz sg a)
  | wt_val_ptr_int: forall b ofs sg a,
      Archi.ptr64 = false ->
      wt_val (Vptr b ofs) (Tint I32 sg a)
  | wt_val_long: forall n sg a,
      wt_val (Vlong n) (Tlong sg a)
  | wt_val_ptr_long: forall b ofs sg a,
      Archi.ptr64 = true ->
      wt_val (Vptr b ofs) (Tlong sg a)
  | wt_val_float: forall f a,
      wt_val (Vfloat f) (Tfloat F64 a)
  | wt_val_single: forall f a,
      wt_val (Vsingle f) (Tfloat F32 a)
  | wt_val_pointer: forall b ofs ty a,
      wt_val (Vptr b ofs) (Tpointer ty a)
  | wt_val_int_pointer: forall n ty a,
      Archi.ptr64 = false ->
      wt_val (Vint n) (Tpointer ty a)
  | wt_val_long_pointer: forall n ty a,
      Archi.ptr64 = true ->
      wt_val (Vlong n) (Tpointer ty a)
  | wt_val_array: forall b ofs ty sz a,
      wt_val (Vptr b ofs) (Tarray ty sz a)
  | wt_val_function: forall b ofs tyargs tyres cc,
      wt_val (Vptr b ofs) (Tfunction tyargs tyres cc)
  | wt_val_struct: forall b ofs id a,
      wt_val (Vptr b ofs) (Tstruct id a)
  | wt_val_union: forall b ofs id a,
      wt_val (Vptr b ofs) (Tunion id a)
  | wt_val_undef: forall ty,
      wt_val Vundef ty
  | wt_val_void: forall v,
      wt_val v Tvoid.

Inductive wt_retval (v: val) (ty: type): Prop :=
| wt_retval_intro
    (WTV: wt_val v ty)
    (NVOID: match ty with
            | Tvoid | Tarray _ _ _ | Tfunction _ _ _ | Tstruct _ _ | Tunion _ _ => v = Vundef
            | _ => True
            end
    ).

Inductive wt_arguments: exprlist -> typelist -> Prop :=
  | wt_arg_nil:
      wt_arguments Enil Tnil
  | wt_arg_cons: forall a al ty tyl
      (NVOID: ty <> Tvoid),
      wt_cast (typeof a) ty ->
      wt_arguments al tyl ->
      wt_arguments (Econs a al) (Tcons ty tyl)
  | wt_arg_extra: forall a al,  (**r tolerance for varargs *)
      strict = false ->
      wt_arguments (Econs a al) Tnil.

Definition subtype (t1 t2: type) : Prop :=
  forall v, wt_val v t1 -> wt_val v t2.

Section WT_EXPR_STMT.

Variable ce: composite_env.
Variable  e: typenv.

Inductive wt_rvalue : expr -> Prop :=
  | wt_Eval: forall v ty,
      wt_val v ty ->
      wt_rvalue (Eval v ty)
  | wt_Evalof: forall l,
      wt_lvalue l ->
      wt_rvalue (Evalof l (typeof l))
  | wt_Eaddrof: forall l,
      wt_lvalue l ->
      wt_rvalue (Eaddrof l (Tpointer (typeof l) noattr))
  | wt_Eunop: forall op r ty,
      wt_rvalue r ->
      type_unop op (typeof r) = OK ty ->
      wt_rvalue (Eunop op r ty)
  | wt_Ebinop: forall op r1 r2 ty,
      wt_rvalue r1 -> wt_rvalue r2 ->
      type_binop op (typeof r1) (typeof r2) = OK ty ->
      wt_rvalue (Ebinop op r1 r2 ty)
  | wt_Ecast: forall r ty,
      wt_rvalue r -> wt_cast (typeof r) ty ->
      wt_rvalue (Ecast r ty)
  | wt_Eseqand: forall r1 r2,
      wt_rvalue r1 -> wt_rvalue r2 ->
      wt_bool (typeof r1) -> wt_bool (typeof r2) ->
      wt_rvalue (Eseqand r1 r2 (Tint I32 Signed noattr))
  | wt_Eseqor: forall r1 r2,
      wt_rvalue r1 -> wt_rvalue r2 ->
      wt_bool (typeof r1) -> wt_bool (typeof r2) ->
      wt_rvalue (Eseqor r1 r2 (Tint I32 Signed noattr))
  | wt_Econdition: forall r1 r2 r3 ty,
      wt_rvalue r1 -> wt_rvalue r2 -> wt_rvalue r3 ->
      wt_bool (typeof r1) ->
      wt_cast (typeof r2) ty -> wt_cast (typeof r3) ty ->
      wt_rvalue (Econdition r1 r2 r3 ty)
  | wt_Esizeof: forall ty,
      wt_rvalue (Esizeof ty size_t)
  | wt_Ealignof: forall ty,
      wt_rvalue (Ealignof ty size_t)
  | wt_Eassign: forall l r,
      wt_lvalue l -> wt_rvalue r -> wt_cast (typeof r) (typeof l) ->
      wt_rvalue (Eassign l r (typeof l))
  | wt_Eassignop: forall op l r ty,
      wt_lvalue l -> wt_rvalue r ->
      type_binop op (typeof l) (typeof r) = OK ty ->
      wt_cast ty (typeof l) ->
      wt_rvalue (Eassignop op l r ty (typeof l))
  | wt_Epostincr: forall id l ty,
      wt_lvalue l ->
      type_binop (match id with Incr => Oadd | Decr => Osub end)
                 (typeof l) (Tint I32 Signed noattr) = OK ty ->
      wt_cast (incrdecr_type (typeof l)) (typeof l) ->
      wt_rvalue (Epostincr id l (typeof l))
  | wt_Ecomma: forall r1 r2,
      wt_rvalue r1 -> wt_rvalue r2 ->
      wt_rvalue (Ecomma r1 r2 (typeof r2))
  | wt_Ecall: forall r1 rargs tyargs tyres cconv,
      wt_rvalue r1 -> wt_exprlist rargs ->
      classify_fun (typeof r1) = fun_case_f tyargs tyres cconv ->
      wt_arguments rargs tyargs ->
      wt_rvalue (Ecall r1 rargs tyres)
  | wt_Ebuiltin: forall ef tyargs rargs ty,
      wt_exprlist rargs ->
      wt_arguments rargs tyargs ->
      (* This typing rule is specialized to the builtin invocations generated
         by C2C, which are either __builtin_sel or builtins returning void. *)
         (ty = Tvoid /\ sig_res (ef_sig ef) = AST.Tvoid)
      \/ (tyargs = Tcons type_bool (Tcons ty (Tcons ty Tnil))
          /\ let t := typ_of_type ty in
             let sg := mksignature (AST.Tint :: t :: t :: nil) t cc_default in
             ef = EF_builtin "__builtin_sel"%string sg) ->
      wt_rvalue (Ebuiltin ef tyargs rargs ty)
  | wt_Eparen: forall r tycast ty,
      wt_rvalue r ->
      wt_cast (typeof r) tycast -> subtype tycast ty ->
      wt_rvalue (Eparen r tycast ty)

with wt_lvalue : expr -> Prop :=
  | wt_Eloc: forall b ofs bf ty,
      wt_lvalue (Eloc b ofs bf ty)
  | wt_Evar: forall x ty,
      e!x = Some ty ->
      wt_lvalue (Evar x ty)
  | wt_Ederef: forall r ty,
      wt_rvalue r ->
      type_deref (typeof r) = OK ty ->
      wt_lvalue (Ederef r ty)
  | wt_Efield: forall r f id a co ty,
      wt_rvalue r ->
      typeof r = Tstruct id a \/ typeof r = Tunion id a ->
      ce!id = Some co ->
      type_of_member a f co.(co_members) = OK ty ->
      wt_lvalue (Efield r f ty)

with wt_exprlist : exprlist -> Prop :=
  | wt_Enil:
      wt_exprlist Enil
  | wt_Econs: forall r1 rl,
      wt_rvalue r1 -> wt_exprlist rl -> wt_exprlist (Econs r1 rl).

Definition wt_expr_kind (k: kind) (a: expr) :=
  match k with
  | RV => wt_rvalue a
  | LV => wt_lvalue a
  end.

Definition expr_kind (a: expr) : kind :=
  match a with
  | Eloc _ _ _ _ => LV
  | Evar _ _ => LV
  | Ederef _ _ => LV
  | Efield _ _ _ => LV
  | _ => RV
  end.

Definition wt_expr (a: expr) :=
  match expr_kind a with
  | RV => wt_rvalue a
  | LV => wt_lvalue a
  end.

Variable rt: type.

Inductive wt_stmt: statement -> Prop :=
  | wt_Sskip:
      wt_stmt Sskip
  | wt_Sdo: forall r,
      wt_rvalue r -> wt_stmt (Sdo r)
  | wt_Ssequence: forall s1 s2,
      wt_stmt s1 -> wt_stmt s2 -> wt_stmt (Ssequence s1 s2)
  | wt_Sifthenelse: forall r s1 s2,
      wt_rvalue r -> wt_stmt s1 -> wt_stmt s2 -> wt_bool (typeof r) ->
      wt_stmt (Sifthenelse r s1 s2)
  | wt_Swhile: forall r s,
      wt_rvalue r -> wt_stmt s -> wt_bool (typeof r) ->
      wt_stmt (Swhile r s)
  | wt_Sdowhile: forall r s,
      wt_rvalue r -> wt_stmt s -> wt_bool (typeof r) ->
      wt_stmt (Sdowhile r s)
  | wt_Sfor: forall s1 r s2 s3,
      wt_rvalue r -> wt_stmt s1 -> wt_stmt s2 -> wt_stmt s3 ->
      wt_bool (typeof r) ->
      wt_stmt (Sfor s1 r s2 s3)
  | wt_Sbreak:
      wt_stmt Sbreak
  | wt_Scontinue:
      wt_stmt Scontinue
  | wt_Sreturn_none
      (VOID: rt = Tvoid):
      wt_stmt (Sreturn None)
  | wt_Sreturn_some: forall r (NVOID: match rt with
                                 | Tvoid | Tarray _ _ _ | Tfunction _ _ _
                                 | Tstruct _ _ | Tunion _ _ => False
                                 | _ => True
                                 end),
      wt_rvalue r ->
      wt_cast (typeof r) rt ->
      wt_stmt (Sreturn (Some r))
  | wt_Sswitch: forall r ls sg sz a,
      wt_rvalue r ->
      typeof r = Tint sz sg a \/ typeof r = Tlong sg a ->
      wt_lblstmts ls ->
      wt_stmt (Sswitch r ls)
  | wt_Slabel: forall lbl s,
      wt_stmt s -> wt_stmt (Slabel lbl s)
  | wt_Sgoto: forall lbl,
      wt_stmt (Sgoto lbl)

with wt_lblstmts : labeled_statements -> Prop :=
  | wt_LSnil:
      wt_lblstmts LSnil
  | wt_LScons: forall case s ls,
      wt_stmt s -> wt_lblstmts ls ->
      wt_lblstmts (LScons case s ls).

End WT_EXPR_STMT.

Fixpoint bind_vars (e: typenv) (l: list (ident * type)) : typenv :=
  match l with
  | nil => e
  | (id, ty) :: l => bind_vars (PTree.set id ty e) l
  end.

Inductive wt_function (ce: composite_env) (e: typenv) : function -> Prop :=
  | wt_function_intro: forall f,
      forall (WT: Forall (wt_type ce) (map snd ((f.(fn_params)) ++ f.(fn_vars)))),
      forall (WTYF: forall ty (IN: In ty (types_of_statement f.(fn_body))), wt_type ce ty),
      wt_stmt ce (bind_vars (bind_vars e f.(fn_params)) f.(fn_vars)) f.(fn_return) f.(fn_body) ->
      wt_function ce e f.

Fixpoint bind_globdef (e: typenv) (l: list (ident * globdef fundef type)) : typenv :=
  match l with
  | nil => e
  | (id, Gfun fd) :: l => bind_globdef (PTree.set id (type_of_fundef fd) e) l
  | (id, Gvar v) :: l => bind_globdef (PTree.set id v.(gvar_info) e) l
  end.

Inductive wt_fundef (ce: composite_env) (e: typenv) : fundef -> Prop :=
  | wt_fundef_internal: forall f,
      wt_function ce e f ->
      wt_fundef ce e (Internal f)
  | wt_fundef_external: forall ef targs tres cc,
      (ef_sig ef).(sig_res) = rettype_of_type tres ->
      wt_fundef ce e (External ef targs tres cc).

Inductive wt_program : program -> Prop :=
  | wt_program_intro: forall p,
      let e := bind_globdef (PTree.empty _) p.(prog_defs) in
      (forall id fd,
         In (id, Gfun fd) p.(prog_defs) ->
         wt_fundef p.(prog_comp_env) e fd) ->
      (forall id ef targs tres cc, In (id, Gfun (External ef targs tres cc)) p.(prog_defs) ->
         signature_of_type targs tres cc = ef_sig ef) ->
      wt_program p.

Global Hint Constructors wt_val wt_rvalue wt_lvalue wt_stmt wt_lblstmts: ty.
Global Hint Extern 1 (wt_int _ _ _) => exact I: ty.
Global Hint Extern 1 (wt_int _ _ _) => reflexivity: ty.

Ltac DestructCases :=
  match goal with
  | [H: match match ?x with _ => _ end with _ => _ end = Some _ |- _ ] => destruct x eqn:?; DestructCases
  | [H: match match ?x with _ => _ end with _ => _ end = OK _ |- _ ] => destruct x eqn:?; DestructCases
  | [H: match ?x with _ => _ end = OK _ |- _ ] => destruct x eqn:?; DestructCases
  | [H: match ?x with _ => _ end = Some _ |- _ ] => destruct x eqn:?; DestructCases
  | [H: Some _ = Some _ |- _ ] => inv H; DestructCases
  | [H: None = Some _ |- _ ] => discriminate
  | [H: OK _ = OK _ |- _ ] => inv H; DestructCases
  | [H: Error _ = OK _ |- _ ] => discriminate
  | _ => idtac
  end.

Ltac DestructMatch :=
  match goal with
  | [ |- match match ?x with _ => _ end with _ => _ end ] => destruct x; DestructMatch
  | [ |- match ?x with _ => _ end ] => destruct x; DestructMatch
  | _ => idtac
  end.

(** * Type checking *)

Definition check_cast (t1 t2: type) : res unit :=
  match classify_cast t1 t2 with
  | cast_case_default => Error (msg "illegal cast")
  | _ => OK tt
  end.

Definition check_bool (t: type) : res unit :=
  match classify_bool t with
  | bool_default => Error (msg "not a boolean")
  | _ => OK tt
  end.

Definition check_literal (v: val) (t: type) : res unit :=
  match v, t  with
  | Vint n, Tint I32 sg a => OK tt
  | Vint n, Tpointer t' a => OK tt
  | Vlong n, Tlong sg a => OK tt
  | Vsingle f, Tfloat F32 a => OK tt
  | Vfloat f, Tfloat F64 a => OK tt
  | _, _ => Error (msg "wrong literal")
  end.

Fixpoint check_arguments (el: exprlist) (tyl: typelist) : res unit :=
  match el, tyl with
  | Enil, Tnil => OK tt
  | Enil, _ => Error (msg "not enough arguments")
  | _, Tnil => if strict then Error (msg "too many arguments") else OK tt
  | Econs e1 el, Tcons ty1 tyl => do x <- check_cast (typeof e1) ty1; assertion(negb (type_eq ty1 Tvoid)); check_arguments el tyl
  end.

Definition check_rval (e: expr) : res unit :=
  match e with
  | Eloc _ _ _ _ | Evar _ _ | Ederef _ _ | Efield _ _ _ =>
      Error (msg "not a r-value")
  | _ =>
      OK tt
  end.

Definition check_lval (e: expr) : res unit :=
  match e with
  | Eloc _ _ _ _ | Evar _ _ | Ederef _ _ | Efield _ _ _ =>
      OK tt
  | _ =>
      Error (msg "not a l-value")
  end.

Fixpoint check_rvals (el: exprlist) : res unit :=
  match el with
  | Enil => OK tt
  | Econs e1 el => do x <- check_rval e1; check_rvals el
  end.

(** Type-checking of expressions is presented as smart constructors
  that check type constraints and build the expression with the correct
  type annotation. *)

Definition evar (e: typenv) (x: ident) : res expr :=
  match e!x with
  | Some ty => OK (Evar x ty)
  | None => Error (MSG "unbound variable " :: CTX x :: nil)
  end.

Definition ederef (r: expr) : res expr :=
  do x1 <- check_rval r;
  do ty <- type_deref (typeof r);
  OK (Ederef r ty).

Definition efield (ce: composite_env) (r: expr) (f: ident) : res expr :=
  do x1 <- check_rval r;
  match typeof r with
  | Tstruct id a | Tunion id a =>
      match ce!id with
      | None => Error (MSG "unbound composite " :: CTX id :: nil)
      | Some co =>
          do ty <- type_of_member a f co.(co_members);
          OK (Efield r f ty)
      end
  | _ =>
      Error (MSG "argument of ." :: CTX f :: MSG " is not a struct or union" :: nil)
  end.

Definition econst_int (n: int) (sg: signedness) : expr :=
  (Eval (Vint n) (Tint I32 sg noattr)).

Definition econst_ptr_int (n: int) (ty: type) : expr :=
  (Eval (if Archi.ptr64 then Vlong (Int64.repr (Int.unsigned n)) else Vint n) (Tpointer ty noattr)).

Definition econst_long (n: int64) (sg: signedness) : expr :=
  (Eval (Vlong n) (Tlong sg noattr)).

Definition econst_ptr_long (n: int64) (ty: type) : expr :=
  (Eval (if Archi.ptr64 then Vlong n else Vint (Int64.loword n)) (Tpointer ty noattr)).

Definition econst_float (n: float) : expr :=
  (Eval (Vfloat n) (Tfloat F64 noattr)).

Definition econst_single (n: float32) : expr :=
  (Eval (Vsingle n) (Tfloat F32 noattr)).

Definition evalof (l: expr) : res expr :=
  do x <- check_lval l; OK (Evalof l (typeof l)).

Definition eaddrof (l: expr) : res expr :=
  do x <- check_lval l; OK (Eaddrof l (Tpointer (typeof l) noattr)).

Definition eunop (op: unary_operation) (r: expr) : res expr :=
  do x <- check_rval r;
  do ty <- type_unop op (typeof r);
  OK (Eunop op r ty).

Definition ebinop (op: binary_operation) (r1 r2: expr) : res expr :=
  do x1 <- check_rval r1; do x2 <- check_rval r2;
  do ty <- type_binop op (typeof r1) (typeof r2);
  OK (Ebinop op r1 r2 ty).

Definition ecast (ty: type) (r: expr) : res expr :=
  do x1 <- check_rval r;
  do x2 <- check_cast (typeof r) ty;
  OK (Ecast r ty).

Definition eseqand (r1 r2: expr) : res expr :=
  do x1 <- check_rval r1; do x2 <- check_rval r2;
  do y1 <- check_bool (typeof r1); do y2 <- check_bool (typeof r2);
  OK (Eseqand r1 r2 type_int32s).

Definition eseqor (r1 r2: expr) : res expr :=
  do x1 <- check_rval r1; do x2 <- check_rval r2;
  do y1 <- check_bool (typeof r1); do y2 <- check_bool (typeof r2);
  OK (Eseqor r1 r2 type_int32s).

Definition econdition (r1 r2 r3: expr) : res expr :=
  do x1 <- check_rval r1; do x2 <- check_rval r2; do x3 <- check_rval r3;
  do y1 <- check_bool (typeof r1);
  do ty <- type_conditional (typeof r2) (typeof r3);
  OK (Econdition r1 r2 r3 ty).

Definition econdition' (r1 r2 r3: expr) (ty: type) : res expr :=
  do x1 <- check_rval r1; do x2 <- check_rval r2; do x3 <- check_rval r3;
  do y1 <- check_bool (typeof r1);
  do y2 <- check_cast (typeof r2) ty;
  do y3 <- check_cast (typeof r3) ty;
  OK (Econdition r1 r2 r3 ty).

Definition esizeof (ty: type) : expr :=
  Esizeof ty size_t.

Definition ealignof (ty: type) : expr :=
  Ealignof ty size_t.

Definition eassign (l r: expr) : res expr :=
  do x1 <- check_lval l; do x2 <- check_rval r;
  do y1 <- check_cast (typeof r) (typeof l);
  OK (Eassign l r (typeof l)).

Definition eassignop (op: binary_operation) (l r: expr) : res expr :=
  do x1 <- check_lval l; do x2 <- check_rval r;
  do ty <- type_binop op (typeof l) (typeof r);
  do y1 <- check_cast ty (typeof l);
  OK (Eassignop op l r ty (typeof l)).

Definition epostincrdecr (id: incr_or_decr) (l: expr) : res expr :=
  do x1 <- check_lval l;
  do ty <- type_binop (match id with Incr => Oadd | Decr => Osub end)
                      (typeof l) type_int32s;
  do y1 <- check_cast (incrdecr_type (typeof l)) (typeof l);
  OK (Epostincr id l (typeof l)).

Definition epostincr (l: expr) := epostincrdecr Incr l.
Definition epostdecr (l: expr) := epostincrdecr Decr l.

Definition epreincr (l: expr) := eassignop Oadd l (Eval (Vint Int.one) type_int32s).
Definition epredecr (l: expr) := eassignop Osub l (Eval (Vint Int.one) type_int32s).

Definition ecomma (r1 r2: expr) : res expr :=
  do x1 <- check_rval r1; do x2 <- check_rval r2;
  OK (Ecomma r1 r2 (typeof r2)).

Definition ecall (fn: expr) (args: exprlist) : res expr :=
  do x1 <- check_rval fn; do x2 <- check_rvals args;
  match classify_fun (typeof fn) with
  | fun_case_f tyargs tyres cconv =>
      do y1 <- check_arguments args tyargs;
      OK (Ecall fn args tyres)
  | _ =>
      Error (msg "call: not a function")
  end.

Definition ebuiltin (ef: external_function) (tyargs: typelist) (args: exprlist) (tyres: type) : res expr :=
  do x1 <- check_rvals args;
  do x2 <- check_arguments args tyargs;
  if type_eq tyres Tvoid
  && AST.rettype_eq (sig_res (ef_sig ef)) AST.Tvoid
  then OK (Ebuiltin ef tyargs args tyres)
  else Error (msg "builtin: wrong type decoration").

Definition eselection (r1 r2 r3: expr) : res expr :=
  do x1 <- check_rval r1; do x2 <- check_rval r2; do x3 <- check_rval r3;
  do y1 <- check_bool (typeof r1);
  do ty <- type_conditional (typeof r2) (typeof r3);
  OK (Eselection r1 r2 r3 ty).

Definition sdo (a: expr) : res statement :=
  do x <- check_rval a; OK (Sdo a).

Definition sifthenelse (a: expr) (s1 s2: statement) : res statement :=
  do x <- check_rval a; do y <- check_bool (typeof a); OK (Sifthenelse a s1 s2).

Definition swhile (a: expr) (s: statement) : res statement :=
  do x <- check_rval a; do y <- check_bool (typeof a); OK (Swhile a s).

Definition sdowhile (a: expr) (s: statement) : res statement :=
  do x <- check_rval a; do y <- check_bool (typeof a); OK (Sdowhile a s).

Definition sfor (s1: statement) (a: expr) (s2 s3: statement) : res statement :=
  do x <- check_rval a; do y <- check_bool (typeof a); OK (Sfor s1 a s2 s3).

Definition sreturn (rt: type) (a: expr) : res statement :=
  do x <- check_rval a; do y <- check_cast (typeof a) rt;
  assertion(match rt with
            | Tvoid | Tarray _ _ _ | Tfunction _ _ _ | Tstruct _ _ | Tunion _ _ => false
            | _ => true
            end);
  OK (Sreturn (Some a)).

Definition sswitch (a: expr) (sl: labeled_statements) : res statement :=
  do x <- check_rval a;
  match typeof a with
  | Tint _ _ _ | Tlong _ _ => OK (Sswitch a sl)
  | _ => Error (msg "wrong type for argument of switch")
  end.

(** Using the smart constructors, we define a type checker that rebuilds
    a correctly-type-annotated program. *)

Fixpoint retype_expr (ce: composite_env) (e: typenv) (a: expr) : res expr :=
  match a with
  | Eval (Vint n) (Tint _ sg _) =>
      OK (econst_int n sg)
  | Eval (Vint n) (Tpointer ty _) =>
      OK (econst_ptr_int n ty)
  | Eval (Vlong n) (Tlong sg _) =>
      OK (econst_long n sg)
  | Eval (Vfloat n) _ =>
      OK (econst_float n)
  | Eval (Vsingle n) _ =>
      OK (econst_single n)
  | Eval _ _ =>
      Error (msg "bad literal")
  | Evar x _ =>
      evar e x
  | Efield r f _ =>
      do r' <- retype_expr ce e r; efield ce r' f
  | Evalof l _ =>
      do l' <- retype_expr ce e l; evalof l'
  | Ederef r _ =>
      do r' <- retype_expr ce e r; ederef r'
  | Eaddrof l _ =>
      do l' <- retype_expr ce e l; eaddrof l'
  | Eunop op r _ =>
      do r' <- retype_expr ce e r; eunop op r'
  | Ebinop op r1 r2 _ =>
      do r1' <- retype_expr ce e r1; do r2' <- retype_expr ce e r2; ebinop op r1' r2'
  | Ecast r ty =>
      do r' <- retype_expr ce e r; ecast ty r'
  | Eseqand r1 r2 _ =>
      do r1' <- retype_expr ce e r1; do r2' <- retype_expr ce e r2; eseqand r1' r2'
  | Eseqor r1 r2 _ =>
      do r1' <- retype_expr ce e r1; do r2' <- retype_expr ce e r2; eseqor r1' r2'
  | Econdition r1 r2 r3 _ =>
      do r1' <- retype_expr ce e r1; do r2' <- retype_expr ce e r2; do r3' <- retype_expr ce e r3; econdition r1' r2' r3'
  | Esizeof ty _ =>
      OK (esizeof ty)
  | Ealignof ty _ =>
      OK (ealignof ty)
  | Eassign l r _ =>
      do l' <- retype_expr ce e l; do r' <- retype_expr ce e r; eassign l' r'
  | Eassignop op l r _ _ =>
      do l' <- retype_expr ce e l; do r' <- retype_expr ce e r; eassignop op l' r'
  | Epostincr id l _ =>
      do l' <- retype_expr ce e l; epostincrdecr id l'
  | Ecomma r1 r2 _ =>
      do r1' <- retype_expr ce e r1; do r2' <- retype_expr ce e r2; ecomma r1' r2'
  | Ecall r1 rl _ =>
      do r1' <- retype_expr ce e r1; do rl' <- retype_exprlist ce e rl; ecall r1' rl'
  | Ebuiltin ef tyargs rl tyres =>
      do rl' <- retype_exprlist ce e rl; ebuiltin ef tyargs rl' tyres
  | Eloc _ _ _ _ =>
      Error (msg "Eloc in source")
  | Eparen _ _ _ =>
      Error (msg "Eparen in source")
  end

with retype_exprlist (ce: composite_env) (e: typenv) (al: exprlist) : res exprlist :=
  match al with
  | Enil => OK Enil
  | Econs a1 al =>
      do a1' <- retype_expr ce e a1;
      do al' <- retype_exprlist ce e al;
      do x1 <- check_rval a1';
      OK (Econs a1' al')
  end.

Fixpoint retype_stmt (ce: composite_env) (e: typenv) (rt: type) (s: statement) : res statement :=
  match s with
  | Sskip =>
      OK Sskip
  | Sdo a =>
      do a' <- retype_expr ce e a; sdo a'
  | Ssequence s1 s2 =>
      do s1' <- retype_stmt ce e rt s1; do s2' <- retype_stmt ce e rt s2; OK (Ssequence s1' s2')
  | Sifthenelse a s1 s2 =>
      do a' <- retype_expr ce e a;
      do s1' <- retype_stmt ce e rt s1; do s2' <- retype_stmt ce e rt s2;
      sifthenelse a' s1' s2'
  | Swhile a s =>
      do a' <- retype_expr ce e a;
      do s' <- retype_stmt ce e rt s;
      swhile a' s'
  | Sdowhile a s =>
      do a' <- retype_expr ce e a;
      do s' <- retype_stmt ce e rt s;
      sdowhile a' s'
  | Sfor s1 a s2 s3 =>
      do a' <- retype_expr ce e a;
      do s1' <- retype_stmt ce e rt s1; do s2' <- retype_stmt ce e rt s2; do s3' <- retype_stmt ce e rt s3;
      sfor s1' a' s2' s3'
  | Sbreak =>
      OK Sbreak
  | Scontinue =>
      OK Scontinue
  | Sreturn None =>
      assertion(type_eq rt Tvoid);
      OK (Sreturn None)
  | Sreturn (Some a) =>
      do a' <- retype_expr ce e a;
      sreturn rt a'
  | Sswitch a sl =>
      do a' <- retype_expr ce e a;
      do sl' <- retype_lblstmts ce e rt sl;
      sswitch a' sl'
  | Slabel lbl s =>
      do s' <- retype_stmt ce e rt s; OK (Slabel lbl s')
  | Sgoto lbl =>
      OK (Sgoto lbl)
  end

with retype_lblstmts (ce: composite_env) (e: typenv) (rt: type) (sl: labeled_statements) : res labeled_statements :=
  match sl with
  | LSnil => OK LSnil
  | LScons case s sl =>
      do s' <- retype_stmt ce e rt s; do sl' <- retype_lblstmts ce e rt sl;
      OK (LScons case s' sl')
  end.

Definition retype_function (ce: composite_env) (e: typenv) (f: function) : res function :=
  let e := bind_vars (bind_vars e f.(fn_params)) f.(fn_vars) in
  do s <- retype_stmt ce e f.(fn_return) f.(fn_body);
    assertion (forallb (wt_type ce) (map snd (fn_params f ++ fn_vars f)));
    assertion (forallb (wt_type ce) (types_of_statement s));
  OK (mkfunction f.(fn_return)
                 f.(fn_callconv)
                 f.(fn_params)
                 f.(fn_vars)
                 s).

Definition retype_fundef (ce: composite_env) (e: typenv) (fd: fundef) : res fundef :=
  match fd with
  | Internal f => do f' <- retype_function ce e f; OK (Internal f')
  | External ef args res cc =>
      assertion (signature_eq (signature_of_type args res cc) (ef_sig ef));
      (* assertion (rettype_eq (ef_sig ef).(sig_res) (rettype_of_type res)); *) OK fd
  end.

Definition typecheck_program (p: program) : res program :=
  let e := bind_globdef (PTree.empty _) p.(prog_defs) in
  let ce := p.(prog_comp_env) in
  do tp <- transform_partial_program (retype_fundef ce e) p;
  OK {| prog_defs := tp.(AST.prog_defs);
        prog_public := p.(prog_public);
        prog_main := p.(prog_main);
        prog_types := p.(prog_types);
        prog_comp_env := ce;
        prog_comp_env_eq := p.(prog_comp_env_eq) |}.

(** Soundness of the smart constructors.  *)

Lemma check_cast_sound:
  forall t1 t2 x, check_cast t1 t2 = OK x -> wt_cast t1 t2.
Proof.
  unfold check_cast, wt_cast; intros.
  destruct (classify_cast t1 t2); congruence.
Qed.

Lemma check_bool_sound:
  forall t x, check_bool t = OK x -> wt_bool t.
Proof.
  unfold check_bool, wt_bool; intros.
  destruct (classify_bool t); congruence.
Qed.

Global Hint Resolve check_cast_sound check_bool_sound: ty.

Lemma check_arguments_sound:
  forall el tl x, check_arguments el tl = OK x -> wt_arguments el tl.
Proof.
  intros el tl; revert tl el.
  induction tl; destruct el; simpl; intros; try discriminate.
  constructor.
  destruct strict eqn:S; try discriminate. constructor; auto.
  destruct (type_eq t Tvoid); ss.
  { des_ifs. }
  monadInv H. constructor; eauto with ty.
Qed.

Lemma check_rval_sound:
  forall a x, check_rval a = OK x -> expr_kind a = RV.
Proof.
  unfold check_rval; intros. destruct a; reflexivity || discriminate.
Qed.

Lemma check_lval_sound:
  forall a x, check_lval a = OK x -> expr_kind a = LV.
Proof.
  unfold check_lval; intros. destruct a; reflexivity || discriminate.
Qed.

Lemma binarith_type_cast:
  forall t1 t2 m t,
  binarith_type t1 t2 m = OK t -> wt_cast t1 t /\ wt_cast t2 t.
Proof.
Local Transparent Ctypes.intsize_eq.
  unfold wt_cast, binarith_type, classify_binarith; intros; DestructCases;
  simpl; split; try congruence;
  try (destruct Archi.ptr64; congruence).
  destruct f0; congruence.
Qed.

Lemma typeconv_cast:
  forall t1 t2, wt_cast (typeconv t1) t2 -> wt_cast t1 t2.
Proof.
  unfold typeconv, wt_cast; intros. destruct t1; auto.
  assert (classify_cast (Tint I32 Signed a) t2 <> cast_case_default ->
          classify_cast (Tint i s a) t2 <> cast_case_default).
  {
    unfold classify_cast. destruct t2; try congruence. destruct f; congruence.
    destruct Archi.ptr64; congruence.
  }
  destruct i; auto.
Qed.

Lemma wt_bool_cast:
  forall ty, wt_bool ty -> wt_cast ty type_bool.
Proof.
  unfold wt_bool, wt_cast; unfold classify_bool; intros.
  destruct ty; simpl in *; try congruence;
  try (destruct Archi.ptr64; congruence).
  destruct f; congruence.
Qed.

Lemma wt_cast_int:
  forall i1 s1 a1 i2 s2 a2, wt_cast (Tint i1 s1 a1) (Tint i2 s2 a2).
Proof.
  intros; red; simpl.
  destruct Archi.ptr64; [ | destruct (Ctypes.intsize_eq i2 I32)].
- destruct i2; congruence.
- subst i2; congruence.
- destruct i2; congruence.
Qed.

Lemma type_combine_cast:
  forall t1 t2 t,
  type_combine t1 t2 = OK t ->
  match t1 with Tarray _ _ _ => False | Tfunction _ _ _ => False | _ => True end ->
  match t2 with Tarray _ _ _ => False | Tfunction _ _ _ => False | _ => True end ->
  wt_cast t1 t /\ wt_cast t2 t.
Proof.
  intros.
  unfold wt_cast; destruct t1; try discriminate; destruct t2; simpl in H; inv H.
- simpl; split; congruence.
- destruct (intsize_eq i i0 && signedness_eq s s0); inv H3.
  split; apply wt_cast_int.
- destruct (signedness_eq s s0); inv H3.
  simpl; split; try congruence; destruct Archi.ptr64; congruence.
- destruct (floatsize_eq f f0); inv H3.
  simpl; destruct f0; split; congruence.
- monadInv H3. simpl; split; congruence.
- contradiction.
- contradiction.
- destruct (ident_eq i i0); inv H3. simpl; split; congruence.
- destruct (ident_eq i i0); inv H3. simpl; split; congruence.
Qed.

Lemma type_conditional_cast:
  forall t1 t2 t,
  type_conditional t1 t2 = OK t -> wt_cast t1 t /\ wt_cast t2 t.
Proof.
  intros.
  assert (A: forall x, match typeconv x with Tarray _ _ _ => False | Tfunction _ _ _ => False | _ => True end).
  { destruct x; simpl; auto. destruct i; auto. }
  assert (D: type_combine (typeconv t1) (typeconv t2) = OK t -> wt_cast t1 t /\ wt_cast t2 t).
  { intros. apply type_combine_cast in H0. destruct H0; split; apply typeconv_cast; auto.
    apply A. apply A. }
  clear A. unfold type_conditional in H.
  destruct (typeconv t1) eqn:T1; try discriminate;
  destruct (typeconv t2) eqn:T2; inv H; eauto using D, binarith_type_cast.
- split; apply typeconv_cast; unfold wt_cast.
  rewrite T1; simpl; try congruence; destruct Archi.ptr64; congruence.
  rewrite T2; simpl; try congruence; destruct Archi.ptr64; congruence.
- split; apply typeconv_cast; unfold wt_cast.
  rewrite T1; simpl; try congruence; destruct Archi.ptr64; congruence.
  rewrite T2; simpl; try congruence; destruct Archi.ptr64; congruence.
- split; apply typeconv_cast; unfold wt_cast.
  rewrite T1; simpl; try congruence; destruct Archi.ptr64; congruence.
  rewrite T2; simpl; try congruence; destruct Archi.ptr64; congruence.
Qed.

Section SOUNDNESS_CONSTRUCTORS.

Variable ce: composite_env.
Variable e: typenv.
Variable rt: type.

Corollary check_rval_wt:
  forall a x, wt_expr ce e a -> check_rval a = OK x -> wt_rvalue ce e a.
Proof.
  unfold wt_expr; intros. erewrite check_rval_sound in H by eauto. auto.
Qed.

Corollary check_lval_wt:
  forall a x, wt_expr ce e a -> check_lval a = OK x -> wt_lvalue ce e a.
Proof.
  unfold wt_expr; intros. erewrite check_lval_sound in H by eauto. auto.
Qed.

Hint Resolve check_rval_wt check_lval_wt: ty.
Hint Extern 1 (wt_expr _ _ _) => (unfold wt_expr; simpl): ty.

Lemma evar_sound:
  forall x a, evar e x = OK a -> wt_expr ce e a.
Proof.
  unfold evar; intros. destruct (e!x) as [ty|] eqn:E; inv H. eauto with ty.
Qed.

Lemma ederef_sound:
  forall r a, ederef r = OK a -> wt_expr ce e r -> wt_expr ce e a.
Proof.
  intros. monadInv H. eauto with ty.
Qed.

Lemma efield_sound:
  forall r f a, efield ce r f = OK a -> wt_expr ce e r -> wt_expr ce e a.
Proof.
  intros. monadInv H.
  destruct (typeof r) eqn:TR; try discriminate;
  destruct (ce!i) as [co|] eqn:CE; monadInv EQ0; eauto with ty.
Qed.

Lemma econst_int_sound:
  forall n sg, wt_expr ce e (econst_int n sg).
Proof.
  unfold econst_int; auto with ty.
Qed.

Lemma econst_ptr_int_sound:
  forall n ty, wt_expr ce e (econst_ptr_int n ty).
Proof.
  unfold econst_ptr_int; intros. destruct Archi.ptr64 eqn:SF; auto with ty.
Qed.

Lemma econst_long_sound:
  forall n sg, wt_expr ce e (econst_long n sg).
Proof.
  unfold econst_long; auto with ty.
Qed.

Lemma econst_ptr_long_sound:
  forall n ty, wt_expr ce e (econst_ptr_long n ty).
Proof.
  unfold econst_ptr_long; intros. destruct Archi.ptr64 eqn:SF; auto with ty.
Qed.

Lemma econst_float_sound:
  forall n, wt_expr ce e (econst_float n).
Proof.
  unfold econst_float; auto with ty.
Qed.

Lemma econst_single_sound:
  forall n, wt_expr ce e (econst_single n).
Proof.
  unfold econst_single; auto with ty.
Qed.

Lemma evalof_sound:
  forall l a, evalof l = OK a -> wt_expr ce e l -> wt_expr ce e a.
Proof.
  intros. monadInv H. eauto with ty.
Qed.

Lemma eaddrof_sound:
  forall l a, eaddrof l = OK a -> wt_expr ce e l -> wt_expr ce e a.
Proof.
  intros. monadInv H. eauto with ty.
Qed.

Lemma eunop_sound:
  forall op r a, eunop op r = OK a -> wt_expr ce e r -> wt_expr ce e a.
Proof.
  intros. monadInv H. eauto with ty.
Qed.

Lemma ebinop_sound:
  forall op r1 r2 a, ebinop op r1 r2 = OK a -> wt_expr ce e r1 -> wt_expr ce e r2 -> wt_expr ce e a.
Proof.
  intros. monadInv H. eauto with ty.
Qed.

Lemma ecast_sound:
  forall ty r a, ecast ty r = OK a -> wt_expr ce e r -> wt_expr ce e a.
Proof.
  intros. monadInv H. eauto with ty.
Qed.

Lemma eseqand_sound:
  forall r1 r2 a, eseqand r1 r2 = OK a -> wt_expr ce e r1 -> wt_expr ce e r2 -> wt_expr ce e a.
Proof.
  intros. monadInv H. eauto 10 with ty.
Qed.

Lemma eseqor_sound:
  forall r1 r2 a, eseqor r1 r2 = OK a -> wt_expr ce e r1 -> wt_expr ce e r2 -> wt_expr ce e a.
Proof.
  intros. monadInv H. eauto 10 with ty.
Qed.

Lemma econdition_sound:
  forall r1 r2 r3 a, econdition r1 r2 r3 = OK a ->
  wt_expr ce e r1 -> wt_expr ce e r2 -> wt_expr ce e r3 -> wt_expr ce e a.
Proof.
  intros. monadInv H. apply type_conditional_cast in EQ3. destruct EQ3. eauto 10 with ty.
Qed.

Lemma econdition'_sound:
  forall r1 r2 r3 ty a, econdition' r1 r2 r3 ty = OK a ->
  wt_expr ce e r1 -> wt_expr ce e r2 -> wt_expr ce e r3 -> wt_expr ce e a.
Proof.
  intros. monadInv H. eauto 10 with ty.
Qed.

Lemma esizeof_sound:
  forall ty, wt_expr ce e (esizeof ty).
Proof.
  unfold esizeof; auto with ty.
Qed.

Lemma ealignof_sound:
  forall ty, wt_expr ce e (ealignof ty).
Proof.
  unfold ealignof; auto with ty.
Qed.

Lemma eassign_sound:
  forall l r a, eassign l r = OK a -> wt_expr ce e l -> wt_expr ce e r -> wt_expr ce e a.
Proof.
  intros. monadInv H. eauto 10 with ty.
Qed.

Lemma eassignop_sound:
  forall op l r a, eassignop op l r = OK a -> wt_expr ce e l -> wt_expr ce e r -> wt_expr ce e a.
Proof.
  intros. monadInv H. eauto 10 with ty.
Qed.

Lemma epostincrdecr_sound:
  forall id l a, epostincrdecr id l = OK a -> wt_expr ce e l -> wt_expr ce e a.
Proof.
  intros. monadInv H. eauto 10 with ty.
Qed.

Lemma ecomma_sound:
  forall r1 r2 a, ecomma r1 r2 = OK a -> wt_expr ce e r1 -> wt_expr ce e r2 -> wt_expr ce e a.
Proof.
  intros. monadInv H. eauto with ty.
Qed.

Lemma ecall_sound:
  forall fn args a, ecall fn args = OK a -> wt_expr ce e fn -> wt_exprlist ce e args -> wt_expr ce e a.
Proof.
  intros. monadInv H.
  destruct (classify_fun (typeof fn)) eqn:CF; monadInv EQ2.
  econstructor; eauto with ty. eapply check_arguments_sound; eauto.
Qed.

Lemma ebuiltin_sound:
  forall ef tyargs args tyres a,
  ebuiltin ef tyargs args tyres = OK a -> wt_exprlist ce e args -> wt_expr ce e a.
Proof.
  intros. monadInv H.
  destruct (type_eq tyres Tvoid); simpl in EQ2; try discriminate.
  destruct (rettype_eq (sig_res (ef_sig ef)) AST.Tvoid); inv EQ2.
  econstructor; eauto. eapply check_arguments_sound; eauto.
Qed.

(* Lemma eselection_sound: *)
(*   forall r1 r2 r3 a, eselection r1 r2 r3 = OK a -> *)
(*   wt_expr ce e r1 -> wt_expr ce e r2 -> wt_expr ce e r3 -> wt_expr ce e a. *)
(* Proof. *)
(*   intros. monadInv H. apply type_conditional_cast in EQ3. destruct EQ3. *)
(*   eapply wt_Ebuiltin. *)
(*   repeat (constructor; eauto with ty). *)
(*   repeat (constructor; eauto with ty). ss. apply wt_bool_cast; eauto with ty. *)
(*   right; auto. *)
(* Qed. *)

Lemma sdo_sound:
  forall a s, sdo a = OK s -> wt_expr ce e a -> wt_stmt ce e rt s.
Proof.
  intros. monadInv H. eauto with ty.
Qed.

Lemma sifthenelse_sound:
  forall a s1 s2 s, sifthenelse a s1 s2 = OK s ->
  wt_expr ce e a -> wt_stmt ce e rt s1 -> wt_stmt ce e rt s2 -> wt_stmt ce e rt s.
Proof.
  intros. monadInv H. eauto with ty.
Qed.

Lemma swhile_sound:
  forall a s1 s, swhile a s1 = OK s ->
  wt_expr ce e a -> wt_stmt ce e rt s1 -> wt_stmt ce e rt s.
Proof.
  intros. monadInv H. eauto with ty.
Qed.

Lemma sdowhile_sound:
  forall a s1 s, sdowhile a s1 = OK s ->
  wt_expr ce e a -> wt_stmt ce e rt s1 -> wt_stmt ce e rt s.
Proof.
  intros. monadInv H. eauto with ty.
Qed.

Lemma sfor_sound:
  forall s1 a s2 s3 s, sfor s1 a s2 s3 = OK s ->
  wt_stmt ce e rt s1 -> wt_expr ce e a -> wt_stmt ce e rt s2 -> wt_stmt ce e rt s3 ->
  wt_stmt ce e rt s.
Proof.
  intros. monadInv H. eauto 10 with ty.
Qed.

Lemma sreturn_sound:
  forall a s, sreturn rt a = OK s -> wt_expr ce e a -> wt_stmt ce e rt s.
Proof.
  intros. unfold sreturn in H. unfold bind in *. des_ifs; eauto with ty.
Qed.

Lemma sswitch_sound:
  forall a sl s, sswitch a sl = OK s ->
  wt_expr ce e a -> wt_lblstmts ce e rt sl -> wt_stmt ce e rt s.
Proof.
  intros. monadInv H. destruct (typeof a) eqn:TA; inv EQ0.
  eauto with ty.
  eapply wt_Sswitch with (sz := I32); eauto with ty.
Qed.

Lemma retype_expr_sound:
  forall a a', retype_expr ce e a = OK a' -> wt_expr ce e a'
with retype_exprlist_sound:
  forall al al', retype_exprlist ce e al = OK al' -> wt_exprlist ce e al'.
Proof.
- destruct a; simpl; intros a' RT; try (monadInv RT).
+ destruct v; try discriminate.
  destruct ty; inv RT. apply econst_int_sound. apply econst_ptr_int_sound.
  destruct ty; inv RT. apply econst_long_sound.
  inv RT. apply econst_float_sound.
  inv RT. apply econst_single_sound.
+ eapply evar_sound; eauto.
+ eapply efield_sound; eauto.
+ eapply evalof_sound; eauto.
+ eapply ederef_sound; eauto.
+ eapply eaddrof_sound; eauto.
+ eapply eunop_sound; eauto.
+ eapply ebinop_sound; eauto.
+ eapply ecast_sound; eauto.
+ eapply eseqand_sound; eauto.
+ eapply eseqor_sound; eauto.
+ eapply econdition_sound; eauto.
+ apply esizeof_sound.
+ apply ealignof_sound.
+ eapply eassign_sound; eauto.
+ eapply eassignop_sound; eauto.
+ eapply epostincrdecr_sound; eauto.
+ eapply ecomma_sound; eauto.
+ eapply ecall_sound; eauto.
+ eapply ebuiltin_sound; eauto.
- destruct al; simpl; intros al' RT; monadInv RT.
+ constructor.
+ constructor; eauto with ty.
Qed.

Lemma retype_stmt_sound:
  forall s s', retype_stmt ce e rt s = OK s' -> wt_stmt ce e rt s'
with retype_lblstmts_sound:
  forall sl sl', retype_lblstmts ce e rt sl = OK sl' -> wt_lblstmts ce e rt sl'.
Proof.
- destruct s; simpl; intros s' RT; try (monadInv RT).
+ constructor.
+ eapply sdo_sound; eauto using retype_expr_sound.
+ constructor; eauto.
+ eapply sifthenelse_sound; eauto using retype_expr_sound.
+ eapply swhile_sound; eauto using retype_expr_sound.
+ eapply sdowhile_sound; eauto using retype_expr_sound.
+ eapply sfor_sound; eauto using retype_expr_sound.
+ constructor.
+ constructor.
+ destruct o. monadInv RT. eapply sreturn_sound; eauto using retype_expr_sound.
  clear - RT. des_ifs. constructor. reflexivity.
+ eapply sswitch_sound; eauto using retype_expr_sound.
+ constructor; eauto.
+ constructor.
- destruct sl; simpl; intros sl' RT; monadInv RT.
+ constructor.
+ constructor; eauto.
Qed.

End SOUNDNESS_CONSTRUCTORS.

Lemma retype_function_sound:
  forall ce e f f', retype_function ce e f = OK f' -> wt_function ce e f'.
Proof.
  intros. monadInv H. constructor; simpl.
  { rewrite Forall_forall. rewrite forallb_forall in *. ss. }
  { ii. rewrite forallb_forall in Heqb0. eapply Heqb0. eauto. }
  eapply retype_stmt_sound; eauto.
Qed.

Lemma retype_fundef_sound:
  forall ce e fd fd', retype_fundef ce e fd = OK fd' -> wt_fundef ce e fd'.
Proof.
  intros. destruct fd; monadInv H.
- constructor; eapply retype_function_sound; eauto.
- constructor; auto.
  destruct (ef_sig e0) eqn:T; ss. unfold signature_of_type, mksignature in *. clarify.
Qed.

Theorem typecheck_program_sound:
  forall p p', typecheck_program p = OK p' -> wt_program p'.
Proof.
  unfold typecheck_program; intros. monadInv H.
  rename x into tp.
  constructor; simpl.
  set (ce := prog_comp_env p) in *.
  set (e := bind_globdef (PTree.empty type) (prog_defs p)) in *.
  set (e' := bind_globdef (PTree.empty type) (AST.prog_defs tp)) in *.
  assert (M: match_program (fun ctx f tf => retype_fundef ce e f = OK tf) eq p tp)
  by (eapply match_transform_partial_program; eauto).
  destruct M as (MATCH & _). simpl in MATCH.
  assert (ENVS: e' = e).
  { unfold e, e'. revert MATCH; generalize (prog_defs p) (AST.prog_defs tp) (PTree.empty type).
    induction l as [ | [id gd] l ]; intros l' t M; inv M.
    auto.
    destruct b1 as [id' gd']; destruct H1; simpl in *. inv H0; simpl.
    replace (type_of_fundef f2) with (type_of_fundef f1); auto.
    unfold retype_fundef in H2. destruct f1; monadInv H2; auto. monadInv EQ0; auto.
    inv H1. simpl. auto.
  }
  rewrite ENVS.
  intros id fd. revert MATCH; generalize (prog_defs p) (AST.prog_defs tp).
  induction 1; simpl; intros.
  contradiction.
  destruct H0; auto. subst b1; inv H. simpl in H1. inv H1.
  eapply retype_fundef_sound; eauto.
  { hexploit (match_transform_partial_program _ _ _ EQ); eauto. intro M.
    rr in M. des.  i. exploit list_forall2_in_right; eauto. intro MATCH; des. ss.
    inv MATCH0. ss. clarify. inv H1. destruct x1; ss. clarify. unfold retype_fundef in H4. des_ifs.
    monadInv H4.
  }
Qed.

(** * Subject reduction *)

(** We show that reductions preserve well-typedness *)

Lemma pres_cast_int_int:
  forall sz sg n, wt_int (cast_int_int sz sg n) sz sg.
Proof.
  intros. unfold cast_int_int. destruct sz; simpl.
- destruct sg. apply Int.sign_ext_idem; lia. apply Int.zero_ext_idem; lia.
- destruct sg. apply Int.sign_ext_idem; lia. apply Int.zero_ext_idem; lia.
- auto.
- destruct (Int.eq n Int.zero); auto.
Qed.

Lemma wt_val_casted:
  forall v ty, val_casted v ty -> wt_val v ty.
Proof.
  induction 1; constructor; auto.
- rewrite <- H; apply pres_cast_int_int.
Qed.

Lemma pres_sem_cast:
  forall m v2 ty2 v1 ty1, wt_val v1 ty1 -> sem_cast v1 ty1 ty2 m = Some v2 -> wt_val v2 ty2.
Proof.
  intros. apply wt_val_casted. eapply cast_val_is_casted; eauto.
Qed.

Lemma pres_sem_binarith:
  forall
    (sem_int: signedness -> int -> int -> option val)
    (sem_long: signedness -> int64 -> int64 -> option val)
    (sem_float: float -> float -> option val)
    (sem_single: float32 -> float32 -> option val)
    v1 ty1 v2 ty2 m v ty msg,
    (forall sg n1 n2,
     match sem_int sg n1 n2 with None | Some (Vint _) | Some Vundef => True | _ => False end) ->
    (forall sg n1 n2,
     match sem_long sg n1 n2 with None | Some (Vlong _) | Some Vundef => True | _ => False end) ->
    (forall n1 n2,
     match sem_float n1 n2 with None | Some (Vfloat _) | Some Vundef => True | _ => False end) ->
    (forall n1 n2,
     match sem_single n1 n2 with None | Some (Vsingle _) | Some Vundef => True | _ => False end) ->
    sem_binarith sem_int sem_long sem_float sem_single v1 ty1 v2 ty2 m = Some v ->
    binarith_type ty1 ty2 msg = OK ty ->
    wt_val v ty.
Proof with (try discriminate).
  intros. unfold sem_binarith, binarith_type in *.
  set (ty' := Cop.binarith_type (classify_binarith ty1 ty2)) in *.
  destruct (sem_cast v1 ty1 ty' m) as [v1'|] eqn:CAST1...
  destruct (sem_cast v2 ty2 ty' m) as [v2'|] eqn:CAST2...
  DestructCases.
- specialize (H s i i0). rewrite H3 in H.
  destruct v; auto with ty; contradiction.
- specialize (H0 s i i0). rewrite H3 in H0.
  destruct v; auto with ty; contradiction.
- specialize (H1 f f0). rewrite H3 in H1.
  destruct v; auto with ty; contradiction.
- specialize (H2 f f0). rewrite H3 in H2.
  destruct v; auto with ty; contradiction.
Qed.

Lemma pres_sem_binarith_int:
  forall
    (sem_int: signedness -> int -> int -> option val)
    (sem_long: signedness -> int64 -> int64 -> option val)
    v1 ty1 v2 ty2 m v ty msg,
    (forall sg n1 n2,
     match sem_int sg n1 n2 with None | Some (Vint _) | Some Vundef => True | _ => False end) ->
    (forall sg n1 n2,
     match sem_long sg n1 n2 with None | Some (Vlong _) | Some Vundef => True | _ => False end) ->
    sem_binarith sem_int sem_long (fun n1 n2 => None) (fun n1 n2 => None) v1 ty1 v2 ty2 m = Some v ->
    binarith_int_type ty1 ty2 msg = OK ty ->
    wt_val v ty.
Proof.
  intros. eapply pres_sem_binarith with (msg := msg); eauto.
  simpl; auto. simpl; auto.
  unfold binarith_int_type, binarith_type in *.
  destruct (classify_binarith ty1 ty2); congruence.
Qed.

Lemma pres_sem_shift:
  forall sem_int sem_long ty1 ty2 m ty v1 v2 v,
  shift_op_type ty1 ty2 m = OK ty ->
  sem_shift sem_int sem_long v1 ty1 v2 ty2 = Some v ->
  wt_val v ty.
Proof.
  intros. unfold shift_op_type, sem_shift in *. DestructCases; auto with ty.
Qed.

Lemma pres_sem_cmp:
  forall ty1 ty2 msg ty c v1 v2 m v,
  comparison_type ty1 ty2 msg = OK ty ->
  sem_cmp c v1 ty1 v2 ty2 m = Some v ->
  wt_val v ty.
Proof with (try discriminate).
  unfold comparison_type, sem_cmp; intros.
  assert (X: forall b, wt_val (Val.of_bool b) (Tint I32 Signed noattr)).
  {
    intros b; destruct b; constructor; exact I.
  }
  assert (Y: forall ob, option_map Val.of_bool ob = Some v -> wt_val v (Tint I32 Signed noattr)).
  {
    intros ob EQ. destruct ob as [b|]; inv EQ. eauto.
  }
  destruct (classify_cmp ty1 ty2).
- inv H; eauto.
- DestructCases; eauto.
- DestructCases; eauto.
- DestructCases; eauto.
- DestructCases; eauto.
- unfold sem_binarith in H0.
  set (ty' := Cop.binarith_type (classify_binarith ty1 ty2)) in *.
  destruct (sem_cast v1 ty1 ty') as [v1'|]...
  destruct (sem_cast v2 ty2 ty') as [v2'|]...
  DestructCases; auto.
Qed.

Lemma pres_sem_binop:
  forall ce op ty1 ty2 ty v1 v2 v m,
  type_binop op ty1 ty2 = OK ty ->
  sem_binary_operation ce op v1 ty1 v2 ty2 m = Some v ->
  wt_val v1 ty1 -> wt_val v2 ty2 ->
  wt_val v ty.
Proof.
  intros until m; intros TY SEM WT1 WT2.
  destruct op; simpl in TY; simpl in SEM.
- (* add *)
  unfold sem_add, sem_add_ptr_int, sem_add_ptr_long in SEM; DestructCases; auto with ty.
  eapply pres_sem_binarith; eauto; intros; exact I.
- (* sub *)
  unfold sem_sub in SEM; DestructCases; auto with ty.
  unfold ptrdiff_t, Vptrofs. destruct Archi.ptr64; auto with ty.
  eapply pres_sem_binarith; eauto; intros; exact I.
- (* mul *)
  unfold sem_mul in SEM. eapply pres_sem_binarith; eauto; intros; exact I.
- (* div *)
  unfold sem_div in SEM. eapply pres_sem_binarith; eauto; intros.
  simpl; DestructMatch; auto.
  simpl; DestructMatch; auto.
  simpl; DestructMatch; auto.
  simpl; DestructMatch; auto.
- (* mod *)
  unfold sem_mod in SEM. eapply pres_sem_binarith_int; eauto; intros.
  simpl; DestructMatch; auto.
  simpl; DestructMatch; auto.
- (* and *)
  unfold sem_and in SEM. eapply pres_sem_binarith_int; eauto; intros; exact I.
- (* or *)
  unfold sem_or in SEM. eapply pres_sem_binarith_int; eauto; intros; exact I.
- (* xor *)
  unfold sem_xor in SEM. eapply pres_sem_binarith_int; eauto; intros; exact I.
- (* shl *)
  unfold sem_shl in SEM. eapply pres_sem_shift; eauto.
- (* shr *)
  unfold sem_shr in SEM. eapply pres_sem_shift; eauto.
- (* comparisons *)
  eapply pres_sem_cmp; eauto.
- eapply pres_sem_cmp; eauto.
- eapply pres_sem_cmp; eauto.
- eapply pres_sem_cmp; eauto.
- eapply pres_sem_cmp; eauto.
- eapply pres_sem_cmp; eauto.
Qed.

Lemma pres_sem_unop:
  forall op ty1 ty v1 m v,
  type_unop op ty1 = OK ty ->
  sem_unary_operation op v1 ty1 m = Some v ->
  wt_val v1 ty1 ->
  wt_val v ty.
Proof.
  intros until v; intros TY SEM WT1.
  destruct op; simpl in TY; simpl in SEM.
- (* notbool *)
  unfold sem_notbool in SEM.
  assert (A: ty = Tint I32 Signed noattr) by (destruct (classify_bool ty1); inv TY; auto).
  assert (B: exists b, v = Val.of_bool b).
  { destruct (bool_val v1 ty1 m); inv SEM. exists (negb b); auto. }
  destruct B as [b B].
  rewrite A, B. destruct b; constructor; auto with ty.
- (* notint *)
  unfold sem_notint in SEM; DestructCases; auto with ty.
- (* neg *)
  unfold sem_neg in SEM; DestructCases; auto with ty.
- (* absfloat *)
  unfold sem_absfloat in SEM; DestructCases; auto with ty.
Qed.

Lemma wt_load_result:
  forall ty chunk v,
  access_mode ty = By_value chunk ->
  wt_val (Val.load_result chunk v) ty.
Proof.
  unfold access_mode, Val.load_result. remember Archi.ptr64 as ptr64.
  intros until v; intros AC. destruct ty; simpl in AC; try discriminate AC.
- destruct i; [destruct s|destruct s|idtac|idtac]; inv AC; simpl.
  destruct v; auto with ty. constructor; red. apply Int.sign_ext_idem; lia.
  destruct v; auto with ty. constructor; red. apply Int.zero_ext_idem; lia.
  destruct v; auto with ty. constructor; red. apply Int.sign_ext_idem; lia.
  destruct v; auto with ty. constructor; red. apply Int.zero_ext_idem; lia.
  destruct Archi.ptr64 eqn:SF; destruct v; auto with ty.
  destruct v; auto with ty. constructor; red. apply Int.zero_ext_idem; lia.
- inv AC. destruct Archi.ptr64 eqn:SF; destruct v; auto with ty.
- destruct f; inv AC; destruct v; auto with ty.
- inv AC. unfold Mptr. destruct Archi.ptr64 eqn:SF; destruct v; auto with ty.
Qed.

Lemma wt_decode_val:
  forall ty chunk vl,
  access_mode ty = By_value chunk ->
  wt_val (decode_val chunk vl) ty.
Proof.
  intros until vl; intros ACC.
  assert (LR: forall v, wt_val (Val.load_result chunk v) ty) by (eauto using wt_load_result).
  destruct ty; simpl in ACC; try discriminate.
- destruct i; [destruct s|destruct s|idtac|idtac]; inv ACC; unfold decode_val.
  destruct (proj_bytes vl); auto with ty.
  constructor; red. apply Int.sign_ext_idem; lia.
  destruct (proj_bytes vl); auto with ty.
  constructor; red. apply Int.zero_ext_idem; lia.
  destruct (proj_bytes vl); auto with ty.
  constructor; red. apply Int.sign_ext_idem; lia.
  destruct (proj_bytes vl); auto with ty.
  constructor; red. apply Int.zero_ext_idem; lia.
  destruct (proj_bytes vl). auto with ty. destruct Archi.ptr64 eqn:SF; auto with ty.
  destruct (proj_bytes vl); auto with ty.
  constructor; red. apply Int.zero_ext_idem; lia.
- inv ACC. unfold decode_val. destruct (proj_bytes vl). auto with ty.
  destruct Archi.ptr64 eqn:SF; auto with ty.
- destruct f; inv ACC; unfold decode_val; destruct (proj_bytes vl); auto with ty.
- inv ACC. unfold decode_val. destruct (proj_bytes vl).
  unfold Mptr in *. destruct Archi.ptr64 eqn:SF; auto with ty.
  unfold Mptr in *. destruct Archi.ptr64 eqn:SF; auto with ty.
Qed.

Remark wt_bitfield_normalize: forall sz sg width sg1 n,
  0 < width <= bitsize_intsize sz ->
  sg1 = (if zlt width (bitsize_intsize sz) then Signed else sg) ->
  wt_int (bitfield_normalize sz sg width n) sz sg1.
Proof.
  intros. destruct sz; cbn in *.
  + destruct sg.
    * replace sg1 with Signed by (destruct zlt; auto).
      apply Int.sign_ext_widen; lia.
    * subst sg1; destruct zlt.
      ** apply Int.sign_zero_ext_widen; lia.
      ** apply Int.zero_ext_widen; lia.
  + destruct sg.
    * replace sg1 with Signed by (destruct zlt; auto).
      apply Int.sign_ext_widen; lia.
    * subst sg1; destruct zlt.
      ** apply Int.sign_zero_ext_widen; lia.
      ** apply Int.zero_ext_widen; lia.
  + auto.
  + apply Int.zero_ext_widen; lia.
Qed.

Lemma wt_deref_loc:
  forall ge ty m b ofs bf t v,
  deref_loc ge ty m b ofs bf t v ->
  wt_val v ty.
Proof.
  induction 1.
- (* by value, non volatile *)
  simpl in H1. exploit Mem.load_result; eauto. intros EQ; rewrite EQ.
  apply wt_decode_val; auto.
- (* by value, volatile *)
  inv H1.
  + (* truly volatile *)
    eapply wt_load_result; eauto.
  + (* not really volatile *)
    exploit Mem.load_result; eauto. intros EQ; rewrite EQ.
    apply wt_decode_val; auto.
- (* by reference *)
  destruct ty; simpl in H; try discriminate; auto with ty.
  destruct i; destruct s; discriminate.
  destruct f; discriminate.
- (* by copy *)
  destruct ty; simpl in H; try discriminate; auto with ty.
  destruct i; destruct s; discriminate.
  destruct f; discriminate.
- (* bitfield *)
  inv H. constructor.
  apply wt_bitfield_normalize. lia. auto.
Qed.

Lemma wt_assign_loc:
  forall se ge ty m b ofs bf v t m' v',
  assign_loc se ge ty m b ofs bf v t m' v' ->
  wt_val v ty -> wt_val v' ty.
Proof.
  induction 1; intros; auto.
- inv H. constructor.
  apply wt_bitfield_normalize. lia. auto.
Qed.

Lemma wt_cast_self:
  forall t1 t2, wt_cast t1 t2 -> wt_cast t2 t2.
Proof.
  unfold wt_cast; intros. destruct t2; simpl in *; try congruence.
- apply (wt_cast_int i s a i s a).
- destruct Archi.ptr64; congruence.
- destruct f; congruence.
Qed.

Lemma binarith_type_int32s:
  forall ty1 msg ty2,
  binarith_type ty1 type_int32s msg = OK ty2 ->
  ty2 = incrdecr_type ty1.
Proof.
  intros. unfold incrdecr_type.
  unfold binarith_type, classify_binarith in H; simpl in H.
  destruct ty1; simpl; try congruence.
  destruct i; destruct s; try congruence.
  destruct s; congruence.
  destruct f; congruence.
Qed.

Lemma type_add_int32s:
  forall ty1 ty2,
  type_binop Oadd ty1 type_int32s = OK ty2 ->
  ty2 = incrdecr_type ty1.
Proof.
  simpl; intros. unfold classify_add in H; destruct ty1; simpl in H;
  try (eapply binarith_type_int32s; eauto; fail).
  destruct i; eapply binarith_type_int32s; eauto.
  inv H; auto.
  inv H; auto.
  inv H; auto.
Qed.

Lemma type_sub_int32s:
  forall ty1 ty2,
  type_binop Osub ty1 type_int32s = OK ty2 ->
  ty2 = incrdecr_type ty1.
Proof.
  simpl; intros. unfold classify_sub in H; destruct ty1; simpl in H;
  try (eapply binarith_type_int32s; eauto; fail).
  destruct i; eapply binarith_type_int32s; eauto.
  inv H; auto.
  inv H; auto.
  inv H; auto.
Qed.

Lemma has_rettype_wt_val:
  forall v ty,
  Val.has_rettype v (rettype_of_type ty) -> wt_val v ty.
Proof.
  unfold rettype_of_type, Val.has_rettype, Val.has_type; destruct ty; intros.
- destruct v; contradiction || constructor.
- destruct i.
  + destruct s; destruct v; try contradiction; constructor; red; auto.
  + destruct s; destruct v; try contradiction; constructor; red; auto.
  + destruct v; try contradiction; constructor; auto.
  + destruct v; try contradiction; constructor; red; auto.
- destruct v; try contradiction; constructor; auto.
- destruct f; destruct v; try contradiction; constructor.
- unfold Tptr in *; destruct v; destruct Archi.ptr64 eqn:P64; try contradiction; constructor; auto.
- destruct v; contradiction || constructor.
- destruct v; contradiction || constructor.
- destruct v; contradiction || constructor.
- destruct v; contradiction || constructor.
Qed.

Lemma wt_rred:
  forall se ge tenv a m t a' m',
  rred se ge a m t a' m' -> wt_rvalue ge tenv a -> wt_rvalue ge tenv a'.
Proof.
  induction 1; intros WT; inversion WT.
- (* valof *) simpl in *. constructor. eapply wt_deref_loc; eauto.
- (* addrof *) constructor; auto with ty.
- (* unop *) simpl in H4. inv H2. constructor. eapply pres_sem_unop; eauto.
- (* binop *)
  simpl in H6. inv H3. inv H5. constructor. eapply pres_sem_binop; eauto.
- (* cast *) inv H2. constructor. eapply pres_sem_cast; eauto.
- (* sequand true *) subst. constructor. auto. apply wt_bool_cast; auto.
  red; intros. inv H0; auto with ty.
- (* sequand false *) constructor. auto with ty.
- (* seqor true *) constructor. auto with ty.
- (* seqor false *) subst. constructor. auto. apply wt_bool_cast; auto.
  red; intros. inv H0; auto with ty.
- (* condition *) constructor. destruct b; auto. destruct b; auto. red; auto.
- (* sizeof *)  unfold size_t, Vptrofs; destruct Archi.ptr64; constructor; auto with ty.
- (* alignof *)  unfold size_t, Vptrofs; destruct Archi.ptr64; constructor; auto with ty.
- (* assign *) inversion H5. constructor. eapply wt_assign_loc; eauto. eapply pres_sem_cast; eauto.
- (* assignop *) subst tyres l r. constructor. auto.
  constructor. constructor. eapply wt_deref_loc; eauto.
  auto. auto. auto.
- (* postincr *) simpl in *. subst id0 l.
  exploit wt_deref_loc; eauto. intros WTV1.
  constructor.
  constructor. auto. rewrite <- H0 in H5. constructor.
  constructor; auto. constructor. constructor. auto with ty.
  subst op. destruct id.
  erewrite <- type_add_int32s by eauto. auto.
  erewrite <- type_sub_int32s by eauto. auto.
  simpl; auto.
  constructor; auto.
- (* comma *) auto.
- (* paren *) inv H3. constructor. apply H5. eapply pres_sem_cast; eauto.
- (* builtin *) subst. destruct H7 as [(A & B) | (A & B)].
+ subst ty. auto with ty.
+ simpl in B. set (T := typ_of_type ty) in *.
  set (sg := mksignature (AST.Tint :: T :: T :: nil) T cc_default) in *.
  assert (LK: lookup_builtin_function "__builtin_sel"%string sg = Some (BI_standard (BI_select T))).
  { unfold sg, T; destruct ty as   [ | ? ? ? | ? | [] ? | ? ? | ? ? ? | ? ? ? | ? ? | ? ? ];
    simpl; unfold Tptr; destruct Archi.ptr64; reflexivity. }
  subst ef. red in H0. red in H0. rewrite LK in H0. inv H0.
  inv H. inv H8. inv H9. inv H10. simpl in H1.
  assert (A: val_casted v1 type_bool) by (eapply cast_val_is_casted; eauto).
  inv A.
  set (v' := if Int.eq n Int.zero then v4 else v2) in *.
  constructor.
  destruct (type_eq ty Tvoid).
  subst. constructor.
  inv H1.
  assert (C: val_casted v' ty).
  { unfold v'; destruct (Int.eq n Int.zero); eapply cast_val_is_casted; eauto. }
  assert (EQ: Val.normalize v' T = v').
  { apply Val.normalize_idem. apply val_casted_has_type; auto. }
  rewrite EQ. apply wt_val_casted; auto.
Qed.

Lemma wt_lred:
  forall tenv ge e a m a' m',
  lred ge e a m a' m' -> wt_lvalue ge tenv a -> wt_lvalue ge tenv a'.
Proof.
  induction 1; intros WT; constructor.
Qed.

Lemma rred_same_type:
  forall se ge a m t a' m',
  rred se ge a m t a' m' -> typeof a' = typeof a.
Proof.
  induction 1; auto.
Qed.

Lemma lred_same_type:
  forall ge e a m a' m',
  lred ge e a m a' m' -> typeof a' = typeof a.
Proof.
  induction 1; auto.
Qed.

Section WT_CONTEXT.

Variable cenv: composite_env.
Variable tenv: typenv.
Variable a a': expr.
Hypothesis SAMETY: typeof a' = typeof a.

Lemma wt_subexpr:
  forall from to C,
  context from to C ->
  wt_expr_kind cenv tenv to (C a) ->
  wt_expr_kind cenv tenv from a
with wt_subexprlist:
  forall from C,
  contextlist from C ->
  wt_exprlist cenv tenv (C a) ->
  wt_expr_kind cenv tenv from a.
Proof.
- destruct 1; intros WT; auto; inv WT; eauto.
- destruct 1; intros WT; inv WT; eauto.
Qed.

Lemma typeof_context:
  forall from to C, context from to C -> typeof (C a') = typeof (C a).
Proof.
  induction 1; simpl; auto.
Qed.

Lemma wt_arguments_context:
  forall k C, contextlist k C ->
  forall tyl, wt_arguments (C a) tyl -> wt_arguments (C a') tyl.
Proof.
  induction 1; intros.
- inv H0. constructor; auto. rewrite (typeof_context _ _ _ H); auto.
  constructor; auto.
- inv H0. constructor; auto. constructor; auto.
Qed.

Lemma wt_context:
  forall from to C,
  context from to C ->
  wt_expr_kind cenv tenv to (C a) ->
  wt_expr_kind cenv tenv from a' ->
  wt_expr_kind cenv tenv to (C a')
with wt_contextlist:
  forall from C,
  contextlist from C ->
  wt_exprlist cenv tenv (C a) ->
  wt_expr_kind cenv tenv from a' ->
  wt_exprlist cenv tenv (C a').
Proof.
- induction 1; intros WT BASE;
  auto;
  inv WT;
  try (pose (EQTY := typeof_context _ _ _ H); rewrite <- ? EQTY; econstructor;
       try (apply IHcontext; assumption); rewrite ? EQTY; eauto).
* red. econstructor; eauto. eapply wt_arguments_context; eauto.
* red. econstructor; eauto. eapply wt_arguments_context; eauto.
- induction 1; intros WT BASE.
* inv WT. constructor. apply (wt_context _ _ _ H); auto. auto.
* inv WT. constructor; auto.
Qed.

End WT_CONTEXT.

Section WT_SWITCH.

Lemma wt_select_switch:
  forall n ce e rt sl,
  wt_lblstmts ce e rt sl -> wt_lblstmts ce e rt (select_switch n sl).
Proof.
  unfold select_switch; intros.
  assert (A: wt_lblstmts ce e rt (select_switch_default sl)).
  {
     revert sl H. induction 1; simpl; intros.
     constructor.
     destruct case. auto. constructor; auto.
  }
  assert (B: forall sl', select_switch_case n sl = Some sl' -> wt_lblstmts ce e rt sl').
  {
    revert H. generalize sl. induction 1; simpl; intros.
    discriminate.
    destruct case; eauto. destruct (zeq z n); eauto. inv H1. econstructor; eauto.
  }
  destruct (select_switch_case n sl); auto.
Qed.

Lemma wt_seq_of_ls:
  forall ce e rt sl,
  wt_lblstmts ce e rt sl -> wt_stmt ce e rt (seq_of_labeled_statement sl).
Proof.
  induction 1; simpl.
  constructor.
  constructor; auto.
Qed.

End WT_SWITCH.

Section PRESERVATION.

Variable prog: program.
Hypothesis WTPROG: wt_program prog.
Variable se: Senv.t.
Variable ge: genv.
Hypothesis CECMPT: prog.(prog_comp_env) = ge.(genv_cenv).
Hypothesis GECMPT: forall id blk gd
    (SYMB: Genv.find_symbol ge id = Some blk)
    (DEF: Genv.find_def ge blk = Some gd),
    <<MAP: (prog_defmap prog) ! id = Some gd>>.

Hypothesis GECMPTREV: forall id gd
    (MAP: (prog_defmap prog) ! id = Some gd),
    exists blk, (<<SYMB: Genv.find_symbol ge id = Some blk>>).

Hypothesis GEWF: forall blk gd
    (DEF: Genv.find_def ge blk = Some gd),
    exists id, <<SYMB: Genv.find_symbol ge id = Some blk>>.

Let gtenv := bind_globdef (PTree.empty _) prog.(prog_defs).

Hypothesis WT_EXTERNAL:
  forall id ef args res cc vargs m t vres m',
  In (id, Gfun (External ef args res cc)) prog.(prog_defs) ->
  external_call ef se vargs m t vres m' ->
  wt_retval vres res.

Inductive wt_expr_cont: typenv -> function -> cont -> Prop :=
  | wt_Kdo: forall te f k,
      wt_stmt_cont te f k ->
      wt_expr_cont te f (Kdo k)
  | wt_Kifthenelse: forall te f s1 s2 k,
      wt_stmt_cont te f k ->
      wt_stmt ge te f.(fn_return) s1 -> wt_stmt ge te f.(fn_return) s2 ->
      wt_expr_cont te f (Kifthenelse s1 s2 k)
  | wt_Kwhile1: forall te f r s k,
      wt_stmt_cont te f k ->
      wt_rvalue ge te r -> wt_stmt ge te f.(fn_return) s -> wt_bool (typeof r) ->
      wt_expr_cont te f (Kwhile1 r s k)
  | wt_Kdowhile2: forall te f r s k,
      wt_stmt_cont te f k ->
      wt_rvalue ge te r -> wt_stmt ge te f.(fn_return) s -> wt_bool (typeof r) ->
      wt_expr_cont te f (Kdowhile2 r s k)
  | wt_Kfor2: forall te f r s2 s3 k,
      wt_stmt_cont te f k ->
      wt_rvalue ge te r -> wt_stmt ge te f.(fn_return) s2 -> wt_stmt ge te f.(fn_return) s3 ->
      classify_bool (typeof r) <> bool_default ->
      wt_expr_cont te f (Kfor2 r s2 s3 k)
  | wt_Kswitch1: forall te f ls k,
      wt_stmt_cont te f k ->
      wt_lblstmts ge te f.(fn_return) ls ->
      wt_expr_cont te f (Kswitch1 ls k)
  | wt_Kreturn: forall te f k
      (NVOID: match f.(fn_return) with
              | Tvoid | Tarray _ _ _ | Tfunction _ _ _ | Tstruct _ _ | Tunion _ _ => False
              | _ => True
              end),
      wt_stmt_cont te f k ->
      wt_expr_cont te f (Kreturn k)

with wt_stmt_cont: typenv -> function -> cont -> Prop :=
  | wt_Kseq: forall te f s k,
      wt_stmt_cont te f k ->
      wt_stmt ge te f.(fn_return) s ->
      wt_stmt_cont te f (Kseq s k)
  | wt_Kwhile2: forall te f r s k,
      wt_stmt_cont te f k ->
      wt_rvalue ge te r -> wt_stmt ge te f.(fn_return) s -> wt_bool (typeof r) ->
      wt_stmt_cont te f (Kwhile2 r s k)
  | wt_Kdowhile1: forall te f r s k,
      wt_stmt_cont te f k ->
      wt_rvalue ge te r -> wt_stmt ge te f.(fn_return) s -> wt_bool (typeof r) ->
      wt_stmt_cont te f (Kdowhile1 r s k)
  | wt_Kfor3: forall te f r s2 s3 k,
      wt_stmt_cont te f k ->
      wt_rvalue ge te r -> wt_stmt ge te f.(fn_return) s2 -> wt_stmt ge te f.(fn_return) s3 ->
      wt_bool (typeof r) ->
      wt_stmt_cont te f (Kfor3 r s2 s3 k)
  | wt_Kfor4: forall te f r s2 s3 k,
      wt_stmt_cont te f k ->
      wt_rvalue ge te r -> wt_stmt ge te f.(fn_return) s2 -> wt_stmt ge te f.(fn_return) s3 ->
      wt_bool (typeof r) ->
      wt_stmt_cont te f (Kfor4 r s2 s3 k)
  | wt_Kswitch2: forall te f k,
      wt_stmt_cont te f k ->
      wt_stmt_cont te f (Kswitch2 k)
  | wt_Kstop': forall te f,
      wt_stmt_cont te f Kstop
  | wt_Kcall': forall te f f' e C ty k,
      wt_call_cont (Kcall f' e C ty k) ty ->
      ty = f.(fn_return) ->
      wt_stmt_cont te f (Kcall f' e C ty k)

with wt_call_cont: cont -> type -> Prop :=
  | wt_Kstop: forall ty,
      wt_call_cont Kstop ty
  | wt_Kcall: forall te f e C ty k,
      te = (bind_vars (bind_vars gtenv (fn_params f)) (fn_vars f)) ->
      wt_expr_cont te f k ->
      wt_stmt ge te f.(fn_return) f.(fn_body) ->
      (forall i, In i (map fst (fn_params f ++ fn_vars f)) -> exists b t, e ! i = Some (b, t)) ->
      (forall v, wt_val v ty -> wt_rvalue ge te (C (Eval v ty))) ->
      wt_call_cont (Kcall f e C ty k) ty.

Lemma is_wt_call_cont:
  forall te f k,
  is_call_cont k -> wt_stmt_cont te f k -> wt_call_cont k f.(fn_return).
Proof.
  intros. inv H0; simpl in H; try contradiction. constructor. auto.
Qed.

Lemma wt_call_cont_stmt_cont:
  forall te f k, wt_call_cont k f.(fn_return) -> wt_stmt_cont te f k.
Proof.
  intros. inversion H; subst. constructor. constructor; auto.
Qed.

Lemma call_cont_wt:
  forall e f k, wt_stmt_cont e f k -> wt_call_cont (call_cont k) f.(fn_return).
Proof.
  induction 1; simpl; auto.
  constructor.
  congruence.
Qed.

Lemma call_cont_wt':
  forall e f k, wt_stmt_cont e f k -> wt_stmt_cont e f (call_cont k).
Proof.
  induction 1; simpl; auto; econstructor; eauto.
Qed.

Definition fundef_return (fd: fundef) : type :=
  match fd with
  | Internal f => f.(fn_return)
  | External ef targs tres cc => tres
  end.

Definition fundef_args (fd: fundef) : typelist :=
  match fd with
  | Internal f => type_of_params f.(fn_params)
  | External ef targs tres cc => targs
  end.

Lemma wt_find_funct:
  forall v fd, Genv.find_funct ge v = Some fd -> wt_fundef ge gtenv fd.
Proof.
  i. inv WTPROG. rewrite <- CECMPT. unfold Genv.find_funct, Genv.find_funct_ptr in *. des_ifs.
  exploit GEWF; eauto. i; des.
  exploit GECMPT; eauto. i; des.
  eapply H0; eauto.
  eapply PTree_Properties.in_of_list; eauto.
Qed.

Scheme wt_rvalue_ind2 := Minimality for wt_rvalue Sort Prop
  with wt_lvalue_ind2 := Minimality for wt_lvalue Sort Prop
  with wt_exprlist_ind2 := Minimality for wt_exprlist Sort Prop.
Combined Scheme wt_expression_ind from wt_rvalue_ind2, wt_lvalue_ind2, wt_exprlist_ind2.

Lemma wt_expr_wt_expr
      co te k1 k2 C e
      (CTX: context k1 k2 C)
      (WT: wt_expr co te (C e)):
    wt_expr co te e.
Proof.
  generalize dependent e.
  revert co te.
  revert CTX. revert k1 k2 C.
  eapply (context_ind2
            (fun k k' C => forall co te e,
                 wt_expr co te (C e) -> wt_expr co te e)
            (fun k C => forall co te e,
                 wt_exprlist co te (C e) -> wt_expr co te e)); ss; i;
    try (inv H1; eapply H0; eauto); remember (C e) as e'; destruct e'; clarify;
      try (by inv H4); try (by inv H3); try (by inv H5); try (by inv H6); try inv H7; inv H8.
  Qed.

Lemma wt_rvalue_wt_expr
      co te C e
      (CTX: context LV RV C)
      (WT: wt_rvalue co te (C e)):
    wt_expr co te e.
Proof.
  eapply wt_expr_wt_expr; eauto.
  unfold wt_expr in *. des_ifs.
  destruct (C e); clarify; inv WT.
Qed.

Inductive wt_state: state -> Prop :=
  | wt_stmt_state: forall f s k e m te
        (WTYK: wtype_cont ge k)
        (WTYB: forall ty (IN: In ty (types_of_statement f.(fn_body))), wt_type ge ty)
        (WTYS: forall ty (IN: In ty (types_of_statement s)), wt_type ge ty)
        (WTENV: forall i blk ty, e ! i = Some (blk, ty) -> wt_type ge ty)
        (WFENV: forall i, In i (map fst (fn_params f ++ fn_vars f)) -> exists b t, e ! i = Some (b, t))
        (TENV: te = (bind_vars (bind_vars gtenv (fn_params f)) (fn_vars f)))
        (WTTENV: forall i ty, te ! i = Some ty -> (exists blk ty, e ! i = Some (blk, ty)) \/ exists blk, Genv.find_symbol ge i = Some blk)
        (WTK: wt_stmt_cont te f k)
        (WTB: wt_stmt ge te f.(fn_return) f.(fn_body))
        (WTS: wt_stmt ge te f.(fn_return) s),
      wt_state (State f s k e m)
  | wt_expr_state: forall f r k e m te
        (WTYK: wtype_cont ge k)
        (WTYB: forall ty (IN: In ty (types_of_statement f.(fn_body))), wt_type ge ty)
        (WTYE: forall ty (IN: In ty (types_of_expr r)), wt_type ge ty)
        (WTENV: forall i blk ty, e ! i = Some (blk, ty) -> wt_type ge ty)
        (WFENV: forall i, In i (map fst (fn_params f ++ fn_vars f)) -> exists b t, e ! i = Some (b, t))
        (TENV: te = (bind_vars (bind_vars gtenv (fn_params f)) (fn_vars f)))
        (WTTENV: forall i ty, te ! i = Some ty -> (exists blk ty, e ! i = Some (blk, ty)) \/ exists blk, Genv.find_symbol ge i = Some blk)
        (WTK: wt_expr_cont te f k)
        (WTB: wt_stmt ge te f.(fn_return) f.(fn_body))
        (WTE: wt_rvalue ge te r),
      wt_state (ExprState f r k e m)
  | wt_call_state: forall vf tyf tyargs tyres cc vargs k m
        (WTY: wt_type ge tyf)
        (WTYK: wtype_cont ge k)
        (WTK: wt_call_cont k tyres)
        (CLASSIFY: classify_fun_strong tyf = fun_case_f tyargs tyres cc)
        (WTLOCAL: forall f
            (INTERNAL: Genv.find_funct ge vf = Some (Internal f)),
            Forall (fun t : type => wt_type ge t) (map snd (fn_params f ++ fn_vars f)))
        (WTKS: forall
            (EXT: forall f, Genv.find_funct ge vf <> Some (Internal f)),
            exists _f _e _C _k, k = Kcall _f _e _C tyres _k)
        (WTARGS: Forall2 val_casted vargs (typelist_to_listtype tyargs))
        (NVOID: Forall (fun ty => ty <> Tvoid) (typelist_to_listtype tyargs)),
      wt_state (Callstate vf tyf vargs k m)
  | wt_return_state: forall v k m ty
        (WTYK: wtype_cont ge k)
        (WTK: wt_call_cont k ty)
        (VAL: wt_retval v ty),
      wt_state (Returnstate v k m)
  | wt_stuck_state:
      wt_state Stuckstate.

Hint Constructors wt_expr_cont wt_stmt_cont wt_stmt wt_state: ty.

Section WT_FIND_LABEL.

Scheme wt_stmt_ind2 := Minimality for wt_stmt Sort Prop
  with wt_lblstmts2_ind2 := Minimality for wt_lblstmts Sort Prop.

Lemma wt_find_label:
  forall lbl e f s, wt_stmt ge e f.(fn_return) s ->
  forall k s' k',
  find_label lbl s k = Some (s', k') ->
  wt_stmt_cont e f k ->
  wt_stmt ge e f.(fn_return) s' /\ wt_stmt_cont e f k'.
Proof.
  intros lbl e f s0 WTS0. pattern s0.
  apply (wt_stmt_ind2 ge e f.(fn_return) _
    (fun ls => wt_lblstmts ge e f.(fn_return) ls ->
           forall k s' k',
           find_label_ls lbl ls k = Some (s', k') ->
           wt_stmt_cont e f k ->
           wt_stmt ge e f.(fn_return) s' /\ wt_stmt_cont e f k'));
  simpl; intros; try discriminate.
  + destruct (find_label lbl s1 (Kseq s2 k)) as [[sx kx] | ] eqn:F.
    inv H3. eauto with ty.
    eauto with ty.
  + destruct (find_label lbl s1 k) as [[sx kx] | ] eqn:F.
    inv H5. eauto with ty.
    eauto with ty.
  + eauto with ty.
  + eauto with ty.
  + destruct (find_label lbl s1 (Kseq (Sfor Sskip r s2 s3) k)) as [[sx kx] | ] eqn:F.
    inv H7. eauto with ty.
    destruct (find_label lbl s3 (Kfor3 r s2 s3 k)) as [[sx kx] | ] eqn:F2.
    inv H7. eauto with ty.
    eauto with ty.
  + eauto with ty.
  + destruct (ident_eq lbl lbl0).
    inv H1. auto.
    eauto.
  + destruct (find_label lbl s (Kseq (seq_of_labeled_statement ls) k)) as [[sx kx] | ] eqn:F.
    inv H4. eapply H0; eauto. constructor. auto. apply wt_seq_of_ls; auto.
    eauto.
  + assumption.
Qed.

End WT_FIND_LABEL.

Ltac wtype_tac :=
  ss; try (esplits; eauto);
  i; ss; repeat rewrite in_app_iff in *; des; eauto;
  repeat multimatch goal with
  | [H: context[wt_type _ _] |- _ ] => eapply H; repeat rewrite in_app_iff in *; eauto; fail
  end
.

Lemma preservation_estep:
  forall S t S', estep se ge S t S' -> wt_state S -> wt_state S'.
Proof.
  induction 1; intros WT; inv WT.
- (* lred *)
  econstructor; eauto.
  { ii. eapply WTYE; eauto.
    exploit types_of_context1; eauto. intro X; des. specialize (X a' ty). specialize (X0 a ty).
    inv H; ss; eauto.
  }
  change (wt_expr_kind ge (bind_vars (bind_vars gtenv (fn_params f)) (fn_vars f)) RV (C a')).
  eapply wt_context with (a := a); eauto.
  eapply lred_same_type; eauto.
  eapply wt_lred; eauto. change (wt_expr_kind ge (bind_vars (bind_vars gtenv (fn_params f)) (fn_vars f)) LV a). eapply wt_subexpr; eauto.
- (* rred *)
  econstructor; eauto.
  { ii. clear - H H0 IN WTYE.
    pose a' as TT.
    exploit types_of_context1; eauto. intro X; des. specialize (X a' ty). specialize (X0 a ty).
    apply X in IN.
    exploit types_of_context1; eauto. intros [tys0 [A B]].
    inv H; ss; try rewrite ! in_app_iff in *; ss; des; des_ifs; clarify; eauto; try (by eapply WTYE; eauto; eapply X0; eauto 10).
    - inv H1; ss; unfold access_mode in *; des_ifs; ss.
      { exploit (WTYE (Tpointer t a)); ss. eapply B; ss; auto. }
      { exploit (WTYE (Tpointer t0 a)); ss. eapply B; ss; auto. }
      { exploit (WTYE (Tarray t z a)); ss. eapply B; ss; auto. }
      { inv H. desf; unfold incrdecr_type; cbn; desf. }
    - inv H1; ss; unfold access_mode in *; des_ifs; ss.
      { exploit (WTYE (Tpointer t a)); ss. eapply B; ss; auto. }
      { exploit (WTYE (Tpointer t0 a)); ss. eapply B; ss; auto. }
      { exploit (WTYE (Tarray t z a)); ss. eapply B; ss; auto. }
      { inv H. desf; unfold incrdecr_type; cbn; desf. }
  }
  change (wt_expr_kind ge (bind_vars (bind_vars gtenv (fn_params f)) (fn_vars f)) RV (C a')).
  eapply wt_context with (a := a); eauto.
  eapply rred_same_type; eauto.
  eapply wt_rred; eauto. change (wt_expr_kind ge (bind_vars (bind_vars gtenv (fn_params f)) (fn_vars f)) RV a). eapply wt_subexpr; eauto.
- (* call *)
  assert (A: wt_expr_kind ge (bind_vars (bind_vars gtenv (fn_params f)) (fn_vars f)) RV a) by (eapply wt_subexpr; eauto).
  simpl in A. inv H. inv A. simpl in H9; rewrite H4 in H9; inv H9.
  econstructor.
  { ss. }
  { ii. ss. esplits; eauto.
    - wtype_tac.
      exploit types_of_context1; eauto. intro X; des. eapply X in IN. wtype_tac.
      exploit X0; eauto. wtype_tac.
    - eapply WTYE; eauto.
      exploit types_of_context1; eauto. intro X; des. eapply X0. ss. wtype_tac. right. left. right. ss. eauto.
  }
  {
  econstructor; eauto.
  intros. change (wt_expr_kind ge (bind_vars (bind_vars gtenv (fn_params f)) (fn_vars f)) RV (C (Eval v ty))).
  eapply wt_context with (a := (Ecall (Eval fptr tyf0) el ty)); eauto.
  red; constructor; auto.
  }
  { rr. ss. }
  { inv WTPROG. i. unfold Genv.find_funct in *. des_ifs. rewrite Genv.find_funct_ptr_iff in *.
    exploit GEWF; eauto. i. des. exploit GECMPT; eauto. i. rr in H6. exploit in_prog_defmap; eauto. i.
    exploit H; eauto. i. inv H11. rewrite CECMPT in *. inv H13. ss. }
  { ii. esplits; eauto. }
  { simpl. eauto. clear - H2 H10. ginduction vargs; ii; ss; inv H2; inv H10; ss. econs; eauto. eapply cast_val_is_casted; eauto. }
  clear - H10. ginduction tyargs0; ii; ss. inv H10. econs; eauto.

- (* stuck *)
  constructor.
Qed.

Lemma wtype_cont_call_cont k
      (WTY: wtype_cont ge k)
  : <<WTY: wtype_cont ge (call_cont k)>>.
Proof. clear - k WTY. unfold NW. induction k; ii; ss; wtype_tac. Qed.

Lemma types_of_call_cont k
  : <<INCL: incl (types_of_cont (call_cont k)) (types_of_cont k)>>.
Proof. clear - k. ii. ginduction k; ii; ss; wtype_tac. Qed.

Lemma types_of_labeled_statements_seq ty0 sl (IN: In ty0 (types_of_statement (seq_of_labeled_statement sl)))
  : <<IN: In ty0 (types_of_labeled_statements sl)>>.
Proof. clear - IN. r. ginduction sl; ii; ss. rewrite in_app_iff in *; eauto. des; eauto. Qed.

Lemma types_of_labeled_statements_switch ty0 n sl (IN: In ty0 (types_of_labeled_statements (select_switch n sl)))
  : <<IN: In ty0 (types_of_labeled_statements sl)>>.
Proof.
  clear - IN. r. ginduction sl; ii; ss. rewrite in_app_iff in *; eauto.
  unfold select_switch in IN. ss. des_ifs; ss; try rewrite in_app_iff in *; des; eauto.
  - exploit IHsl; eauto. unfold select_switch. rewrite Heq. ss.
  - exploit IHsl; eauto. unfold select_switch. rewrite Heq. ss.
  - exploit IHsl; eauto. unfold select_switch. rewrite Heq. ss.
Qed.

Scheme statement_ind2 := Induction for statement Sort Prop
  with labeled_statements_ind2 := Induction for labeled_statements Sort Prop.
Combined Scheme statement_labeled_statements_ind from statement_ind2, labeled_statements_ind2.

Let find_label_prop0 (stmt: statement) :=
  (forall lbl k s' k' (FIND: find_label lbl stmt k = Some (s', k')),
    <<INCL: wtype_cont ge k -> (forall ty (IN: In ty (types_of_statement stmt)), wt_type ge ty) -> wtype_cont ge k'>>).
Let find_label_ls_prop0 (lstmts: labeled_statements) :=
  (forall lbl k s' k' (FIND: find_label_ls lbl lstmts k = Some (s', k')),
    <<INCL: wtype_cont ge k -> (forall ty (IN: In ty (types_of_labeled_statements lstmts)), wt_type ge ty) -> wtype_cont ge k'>>).

Let find_label_prop1 (stmt: statement) :=
  (forall lbl k s' k' (FIND: find_label lbl stmt k = Some (s', k')),
    <<INCL: incl (types_of_statement s') ((types_of_statement stmt))>>).

Let find_label_ls_prop1 (lstmts: labeled_statements) :=
  (forall lbl k s' k' (FIND: find_label_ls lbl lstmts k = Some (s', k')),
    <<INCL: incl (types_of_statement s') ((types_of_labeled_statements lstmts))>>).

Lemma types_of_find_label0:
  (forall stmt, find_label_prop0 stmt)
  /\ (forall lstmts, find_label_ls_prop0 lstmts).
Proof.
  clear - prog. clear prog.
  eapply statement_labeled_statements_ind; eauto;
    unfold find_label_prop0, find_label_ls_prop0 in *; ii; ss; des_ifs;
      try rewrite ! in_app_iff in *; eauto;
      try (by (exploit H; eauto; i; des; wtype_tac));
      try (by (exploit H0; eauto; i; des; wtype_tac));
      try (by (exploit H1; eauto; i; des; wtype_tac));
      try (by (exploit H2; eauto; i; des; wtype_tac)).
  - exploit H; eauto. { ss. wtype_tac. exploit types_of_labeled_statements_seq; eauto. wtype_tac. } wtype_tac.
Qed.

Lemma types_of_find_label1:
  (forall stmt, find_label_prop1 stmt)
  /\ (forall lstmts, find_label_ls_prop1 lstmts).
Proof.
  clear - prog. clear prog.
  eapply statement_labeled_statements_ind; eauto;
    unfold find_label_prop1, find_label_ls_prop1 in *; ii; ss; des_ifs;
      try rewrite ! in_app_iff in *; eauto;
      try (by (exploit H; eauto; i; des; wtype_tac));
      try (by (exploit H0; eauto; i; des; wtype_tac));
      try (by (exploit H1; eauto; i; des; wtype_tac));
      try (by (exploit H2; eauto; i; des; wtype_tac)).
Qed.

Lemma alloc_variables_environment
      e m l e' m' i
      (ALLOC: alloc_variables ge e m l e' m')
      (IN: In i (map fst l)):
    exists blk ty, e' ! i = Some (blk, ty).
Proof.
  clear - IN ALLOC. ginduction l; ss. i. destruct a; ss; des; subst.
  - inv ALLOC. ss.
    assert (exists a, (PTree.set i (b1, t) e) ! i = Some a).
    { erewrite PTree.gss. eauto. }
    remember (PTree.set i (b1, t) e) as e1. clear -H7 H.
    { ginduction l; ss.
      - i. inv H7. des. rewrite H. destruct a. eauto.
      - i. inv H7. des. destruct a. destruct (classic (i = id)).
        + subst. exploit IHl; eauto. erewrite PTree.gss; eauto.
        + exploit IHl; eauto. erewrite PTree.gso; eauto.
    }
  - inv ALLOC. ss. exploit IHl; eauto.
Qed.

Lemma bind_vars_none
      te l i ty
      (TENV: (bind_vars te l) ! i = Some ty)
      (NOTIN: ~ In i (map fst l)):
    te ! i = Some ty.
Proof.
  clear -TENV NOTIN. ginduction l; ss. i. destruct a. ss.
  eapply not_or_and in NOTIN. des.
  exploit IHl; eauto. i.
  erewrite PTree.gso in H; eauto.
Qed.

Lemma preservation_sstep:
  forall S t S', sstep se ge S t S' -> wt_state S -> wt_state S'.
Proof.
  induction 1; intros WT; inversion WT; subst;
    try (by inv WTK; econs; eauto with ty; wtype_tac);
    try (by inv WTS; econs; eauto with ty; wtype_tac).
- inv WTK; destruct b; econs; eauto with ty; wtype_tac.
- econstructor. { eapply wtype_cont_call_cont; eauto. } eapply call_cont_wt; eauto. split. constructor. destruct (fn_return f); eauto.
- inv WTK. econstructor. { eapply wtype_cont_call_cont; eauto. } eapply call_cont_wt; eauto.
  inv WTE. split. eapply pres_sem_cast; eauto.
  { destruct (fn_return f); inv H; ss. }
- econstructor. { wtype_tac. } eapply is_wt_call_cont; eauto. split. constructor.
  destruct (fn_return f); eauto.
- inv WTK. econs; eauto with ty; wtype_tac.
  { eapply WTYK0. clear - IN.
    eapply types_of_labeled_statements_seq in IN; eauto. ss. eapply types_of_labeled_statements_switch; eauto.
  }
  apply wt_seq_of_ls. apply wt_select_switch; auto.
- exploit wt_find_label. eexact WTB. eauto. eapply call_cont_wt'; eauto.
  intros [A B]. econs; eauto with ty; wtype_tac.
  { eapply types_of_find_label0 in H. eapply H; eauto. eapply wtype_cont_call_cont; eauto. }
  { eapply types_of_find_label1 in H. eapply H in IN. wtype_tac. }
- assert(WTFD: wt_fundef ge gtenv (Internal f)).
  { eapply wt_find_funct; eauto. }
  inv WTFD. inv H3. econstructor; eauto.
  { clear - H0 WT0.
    assert (EMPTY:forall (i : positive) (blk : block) (ty : type), empty_env ! i = Some (blk, ty) -> wt_type ge ty).
    { ii. erewrite PTree.gempty in H. clarify. }
    remember (fn_params f ++ fn_vars f) as l. remember empty_env as ev.
    clear Heqev Heql. ginduction l; i; ss; inv H0.
    - eapply EMPTY; eauto.
    - exploit IHl; eauto.
      { inv WT0; eauto. }
      i. rewrite PTree.gsspec in *. des_ifs.
      + inv WT0. eauto.
      + eapply EMPTY; eauto. }
  { i. clear -H0 H3.
    exploit alloc_variables_environment; eauto. }
  { i. unfold gtenv in *. ss.
    destruct (classic (In i (map fst (fn_params f)) \/ In i (map fst (fn_vars f)))) as [A | A].
    { clear -H0 A. left.
      assert (In i (map fst (fn_params f ++ fn_vars f))).
      { rewrite map_app. eapply in_or_app; eauto. }
      exploit alloc_variables_environment; eauto. }
    eapply not_or_and in A.
    assert (In i (prog_defs_names prog)).
    { remember (fn_params f) as l1. remember (fn_vars f) as l2. clear - H3 A. des.
      do 2 (eapply bind_vars_none in H3; eauto).
      unfold prog_defs_names. ss. remember (prog_defs prog) as l.
      assert ((PTree.empty type) ! i = None).
      { rewrite PTree.gempty in *. clarify. }
      remember (PTree.empty type) as pe. clear - H3 H. ginduction l; ss.
      - i. clarify.
      - i. destruct a. ss. destruct (classic (i0 = i)); eauto. right. des_ifs.
        + eapply IHl in H3; eauto. erewrite PTree.gso; eauto.
        + eapply IHl in H3; eauto. erewrite PTree.gso; eauto. }
    exploit prog_defmap_dom; eauto. i. des.
    exploit GECMPTREV; eauto. }
  apply wt_call_cont_stmt_cont; auto.
  inv CLASSIFY. eauto.
- assert(WTFD: wt_fundef ge gtenv (External ef targs tres cc)).
  { eapply wt_find_funct; eauto. }
  unfold Genv.find_funct, Genv.find_funct_ptr in *. des_ifs. exploit GEWF; eauto. i; des. exploit GECMPT; eauto. i; des.
  exploit WT_EXTERNAL; eauto.
  { eapply PTree_Properties.in_of_list; eauto. }
  inv CLASSIFY.
  econstructor; eauto.
- inv WTK. inv VAL. econs; eauto with ty; wtype_tac.
  { exploit types_of_context1; eauto. intro Y; des. eapply Y in IN. rewrite in_app_iff in *. des.
    - exploit Y0; eauto. { rewrite in_app_iff. left; eauto. } intro Z.
      exploit (WTYK0 (Eval v ty0)); eauto. i. ss. des; ss. clarify.
    - rename ty into tyy.
      hexploit (Y0 (Eval v ty0) tyy); eauto. { wtype_tac. } intro Z.
      exploit WTYK0; eauto. i. ss. des; ss. clarify.
  }
  { i. unfold gtenv in *. ss.
    destruct (classic (In i (map fst (fn_params f)) \/ In i (map fst (fn_vars f)))) as [A | A].
    { left.
      assert (In i (map fst (fn_params f ++ fn_vars f))).
      { rewrite map_app. eapply in_or_app; eauto. }
      inv WT. inv WTK. ss. eapply H14; eauto. }
    eapply not_or_and in A.
    assert (In i (prog_defs_names prog)).
    { remember (fn_params f) as l1. remember (fn_vars f) as l2. clear -H A. des.
      do 2 (eapply bind_vars_none in H; eauto).
      unfold prog_defs_names. ss. remember (prog_defs prog) as l.
      assert ((PTree.empty type) ! i = None).
      { rewrite PTree.gempty in *. clarify. }
      remember (PTree.empty type) as pe. clear - H0 H. ginduction l; ss.
      - i. clarify.
      - i. destruct a. ss. destruct (classic (i0 = i)); eauto. right. des_ifs; eapply IHl in H; eauto; erewrite PTree.gso; eauto.
    }
    exploit prog_defmap_dom; eauto. i. des.
    exploit GECMPTREV; eauto. }
  Unshelve. all: auto.
Qed.

Theorem preservation:
  forall S t S', step se ge S t S' -> wt_state S -> wt_state S'.
Proof.
  intros. destruct H. eapply preservation_estep; eauto. eapply preservation_sstep; eauto.
Qed.

Theorem wt_initial_state:
  forall vf tyf vargs k m,
    initial_state prog (Callstate vf tyf vargs k m) ->
    (exists fd, Genv.find_funct ge vf = Some (Internal fd)) ->
    wt_state (Callstate vf tyf vargs k m).
Proof.
  intros. inv H. econstructor; ss; try by (econstructor; eauto).
  { inv WTPROG. i. unfold Genv.find_funct in *. des_ifs. rewrite Genv.find_funct_ptr_iff in *.
    exploit GEWF; eauto. i. des. exploit GECMPT; eauto. i. rr in H2. exploit in_prog_defmap; eauto. i.
    exploit H; eauto. i. inv H4. rewrite CECMPT in *. inv H10. ss. }
  { ii. exfalso. des. eapply EXT; eauto. }
Qed.

End PRESERVATION.
