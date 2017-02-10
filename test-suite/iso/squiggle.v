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

(*

Inductive sigs (A : Set) (P : A -> Prop) : Set :=
 existss : forall x : A, P x -> sigs A P.
 *)

Set Imlicit Arguments.

Inductive eqs (A : Set) (x : A) : forall (a:A), Prop :=  
eq_refls : eqs A x x.

(*
Definition beq (b1 b2 : bool) := eqs bool b1 b2.
Infix "≡" := beq (at level 80).
 *)
Section Squiggle.
  Variable V:Set.
  Variable Tm:Set.
  Variable BTm:Set.
  Variable app: Tm -> Tm -> Tm.
  Variable lam: BTm -> Tm.
  Variable num: nat -> Tm.
  (*
  Variable primRec: Tm (* num*) ->Tm (* base case*) ->Tm (* rec case *) -> Tm.
  *)
  Variable applyBtm: BTm -> Tm -> Tm.
End Squiggle.
