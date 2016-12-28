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

Print list.


Inductive list (A : Set (* Type fails *)) 
  : Set :=  nil : list A | cons : A -> list A -> list A.

Fixpoint listElim (A:Set )(l  : list A) : Type:=
match l with
| nil _ => unit
| cons _ _ tl => A + (listElim _ tl)
end.


Parametricity Recursive unit.
Parametricity Recursive sum.
(*Parametricity Recursive list.
 Parametricity Recursive listElim. 

Print listElim_R.
(* copied below *)
*)

Inductive list_R (A₁ A₂ : Set) (A_R : A₁ -> A₂ -> Set) : list A₁ -> list A₂ -> Prop :=
    list_R_nil_R : list_R A₁ A₂ A_R (nil A₁) (nil A₂)
  | list_R_cons_R : forall (H : A₁) (H0 : A₂),
                    A_R H H0 ->
                    forall (H1 : list A₁) (H2 : list A₂),
                    list_R A₁ A₂ A_R H1 H2 ->
                    list_R A₁ A₂ A_R (cons A₁ H H1) (cons A₂ H0 H2).

(* Fails because list_R is now in Prop
Definition listElim_R := 
let fix_listElim_1 :=
  fix listElim (A : Set) (l : list A) {struct l} : Type :=
    match l with
    | nil _ => unit
    | cons _ _ tl => (A + listElim A tl)%type
    end in
let fix_listElim_2 :=
  fix listElim (A : Set) (l : list A) {struct l} : Type :=
    match l with
    | nil _ => unit
    | cons _ _ tl => (A + listElim A tl)%type
    end in
fix
listElim_R (A₁ A₂ : Set) (A_R : A₁ -> A₂ -> Set) (l₁ : list A₁) 
           (l₂ : list A₂) (l_R : list_R A₁ A₂ A_R l₁ l₂) {struct l_R} :
  fix_listElim_1 A₁ l₁ -> fix_listElim_2 A₂ l₂ -> Type :=
  match
    l_R in (list_R _ _ _ l₁0 l₂0)
    return (fix_listElim_1 A₁ l₁0 -> fix_listElim_2 A₂ l₂0 -> Type)
  with
  | list_R_nil_R _ _ _ => unit_R
  | list_R_cons_R _ _ _ _ _ _ tl₁ tl₂ tl_R =>
      sum_R A₁ A₂ A_R (fix_listElim_1 A₁ tl₁) (fix_listElim_2 A₂ tl₂)
        (listElim_R A₁ A₂ A_R tl₁ tl₂ tl_R)
  end.
*)
