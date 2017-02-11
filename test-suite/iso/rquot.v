Require Import ReflParam.common.
Require Import ReflParam.templateCoqMisc.
Require Import String.
Require Import List.
Require Import Template.Ast.
Require Import SquiggleEq.terms.
Require Import ReflParam.paramDirect.
Require Import SquiggleEq.substitution.
Require Import ReflParam.PiTypeR.
Import ListNotations.
Open Scope string_scope.

Require Import ReflParam.Trecord.


Set Imlicit Arguments.

Inductive list (A : Set) : Set :=  nil : list A | cons : A -> list A -> list A.

Arguments nil {A}.
Arguments cons {A} _ _.

Notation "[ x ]" := (cons x nil) : list_scope.
Notation "[ x , y , .. , z ]" := (cons x (cons y .. (cons z nil) ..)) : list_scope.


(*
Definition beq (b1 b2 : bool) := eqs bool b1 b2.
Infix "≡" := beq (at level 80).
 *)

Section Reals.
  (* Variable V:Set. This interface is too abstract for exposing V *)
  Variable R:Set.
  Variable (Rone Rzero : R).
  Variable (Radd : R -> R -> R).
  Variable (Rle : R -> R -> Prop).

  Definition isLub (f : nat -> R) (lub:R) : Prop.
  Admitted.

  (* show that this is iff *)
  Fixpoint isLubL (fl : list (nat -> R)) (lub:R) {struct fl}: Prop.
  Admitted.

    (* in HoTT, to get informity,  one would have to form the quotient type
      and maintain it. So, the Radd will have teh quotiented type. Thus one cannot
      use the real for practical purposes.  *)

End Reals.