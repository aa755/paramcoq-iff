Require Import Coq.Classes.DecidableClass.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import SquiggleEq.export.
Require Import SquiggleEq.UsefulTypes.
Require Import SquiggleEq.list.
Require Import SquiggleEq.LibTactics.
Require Import SquiggleEq.tactics.
Require Import SquiggleEq.AssociationList.
Require Import ReflParam.common.
Require Import ReflParam.templateCoqMisc.
Require Import ReflParam.paramDirect ReflParam.indType.
Require Import Arith.

(* see erasure.v for original motivations *)

Definition polyF (A B :Type) (f: A->B) (a:A) :=  f a.

Definition trueId := (fun x:True => x).
Definition polyFApT := polyF True True trueId.

Declare ML Module "paramcoq".

Parametricity Recursive polyF.

Print Top_o_erasurreF_o_v_o_polyF_R.

Definition polyF_R :=
fun  (A₁ A₂ : Type) (A_R : A₁ -> A₂ -> Type) (B₁ B₂ : Type) (B_R : B₁ -> B₂ -> Type)
  (f₁ : A₁ -> B₁) (f₂ : A₂ -> B₂)
  (f_R : forall (H : A₁) (H0 : A₂), A_R H H0 -> B_R (f₁ H) (f₂ H0)) 
  (a₁ : A₁) (a₂ : A₂) (a_R : A_R a₁ a₂) => f_R a₁ a₂ a_R.

Parametricity Recursive polyFApT.

Print Top_o_erasurreF_o_v_o_polyFApT_R.

Print Top_o_erasurreF_o_v_o_trueId_R.

Definition trueId_R :=
  fun (x₁ x₂ : True) (x_R : True_R x₁ x₂) => x_R.

Definition polyFApT_R := 
polyF_R True True True_R True True True_R trueId trueId
  trueId_R.

Definition True_RR := fun (a b : True) => True.
Definition trueId_RR := I.

Definition polyFApT_RR :=
polyF_R True True True_RR True True True_RR trueId trueId
  trueId_RR.
(*
Error:
The term "trueId_RR" has type "True" while it is expected to have type
 "forall H H0 : True, True_RR H H0 -> True_RR (trueId H) (trueId H0)".
*)

