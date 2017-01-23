Require Import Coq.Classes.DecidableClass.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import SquiggleEq.export.
Require Import SquiggleEq.UsefulTypes.
Require Import SquiggleEq.list.
Require Import SquiggleEq.LibTactics.
Require Import SquiggleEq.tactics.
Require Import SquiggleEq.AssociationList.

(* creating a Prop without using inductives *)
Definition constTrue (T:Type) : Prop := (forall P:Prop, P->P).

Definition constFalse (T:Type) : Prop := (forall P:Prop, P->P).

Definition nonConst (T:Type) : Prop := (exists (t:T), True).

(*
Declare ML Module "paramcoq".
Parametricity Recursive constTrue.
Print constTrue_R.
*)

Definition constTrue_R : forall T₁ T₂ : Type, (T₁ -> T₂ -> Type) -> constTrue T₁ -> constTrue T₂ -> Prop
:= 
fun (T₁ T₂ : Type) (_ : T₁ -> T₂ -> Type) (H H0 : forall P : Prop, P -> P) =>
forall (P₁ P₂ : Prop) (P_R : P₁ -> P₂ -> Prop) (H1 : P₁) (H2 : P₂),
P_R H1 H2 -> P_R (H P₁ H1) (H0 P₂ H2).

(* this is hardly a generic proof *)
Lemma constTrue_RP : forall T₁ T₂ : Type, (T₁ -> T₂ -> Type) -> constTrue T₁ <-> constTrue T₂.
Proof using.
  intros ? ? _. unfold constTrue. reflexivity.
Qed.

Print and.

SearchAbout (nat->Prop).
Print Between.between.



