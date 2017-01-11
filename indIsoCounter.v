Require Import Coq.Classes.DecidableClass.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import SquiggleEq.export.
Require Import SquiggleEq.UsefulTypes.
Require Import SquiggleEq.list.
Require Import SquiggleEq.LibTactics.
Require Import SquiggleEq.tactics.
Require Import SquiggleEq.AssociationList.
Require Import ExtLib.Structures.Monads.
Require Import common.
Require Import Trecord.

(* remove the Cons case. remove C, the payload type. generalize nat and O *)
Inductive Vec (nat:Set) (O:nat) : nat -> Set :=
| vnil : Vec nat O O.

(*
Parametricity Recursive Vec.
Print Vec_R.
For one constructor, Coq Picks Prop
*)


Inductive Vec_R (nat₁ nat₂ : Set) (nat_R : nat₁ -> nat₂ -> Set) (O₁ : nat₁)
(O₂ : nat₂) (O_R : nat_R O₁ O₂)
  : forall (H : nat₁) (H0 : nat₂), nat_R H H0 -> Vec nat₁ O₁ H -> Vec nat₂ O₂ H0 -> Prop :=
Vec_R_vnil_R : Vec_R nat₁ nat₂ nat_R O₁ O₂ O_R O₁ O₂ O_R (vnil nat₁ O₁) (vnil nat₂ O₂).

Require Import paramDirect.

Import ListNotations.
Open Scope string_scope.

Run TemplateProgram (genParamInd false true "Top.Vec").

Definition Vec_RR :=
(fix
 Top_Vec_RR0 (nat nat₂ : Set) (nat_R : nat -> nat₂ -> Set) (O : nat) 
             (O₂ : nat₂) (O_R : nat_R O O₂) (H : nat) (H0 : nat₂) 
             (H1 : nat_R H H0) (H2 : Vec nat O H) (H3 : Vec nat₂ O₂ H0) {struct H2} :
   Prop := match H2 with
           | vnil _ _ => match H3 with
                         | vnil _ _ => True
                         end
           end).


Let nat₁:= nat.
Let nat₂:= nat.
Let nat_R : nat -> nat -> Set := fun _ _ => nat.
Let O₁ := O.
Let O₂ := O.
Let O_R := 17.
Let v₁ : Vec nat₁ O₁ O₁:= vnil nat₁ O₁.
Let v₂ : Vec nat₂ O₂ O₂:= vnil nat₂ O₂.



Definition VecRInd : Set := Vec_R  nat₁ nat₂ nat_R O₁ O₂ O_R O₁ O₂ 19 v₁ v₂.
Definition VecRDed : Set := Vec_RR nat₁ nat₂ nat_R O₁ O₂ O_R O₁ O₂ 19 v₁ v₂.

Definition VecRDedInhabited : VecRDed.
  unfold VecRDed. simpl. exact I.
Defined.

Require Import SquiggleEq.UsefulTypes.


Require Import Coq.Logic.Eqdep_dec.
Require Import Omega.

Definition VecRDedUnInhabited : VecRInd -> False.
  unfold VecRInd. intro H.
  remember 19 as nn.
  change nat with (nat_R O₁ O₂) in nn.
  inversion H.
  apply Eqdep_dec.inj_pair2_eq_dec in H2;[| exact NPeano.Nat.eq_dec].
  apply Eqdep_dec.inj_pair2_eq_dec in H2;[| exact NPeano.Nat.eq_dec].
  unfold O_R in *. subst.
  omega.
Defined.

Print Assumptions VecRDedUnInhabited.
(*Closed under the global context *)

Print Assumptions VecRDedInhabited.
(*Closed under the global context *)





