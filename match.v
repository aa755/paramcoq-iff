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
| cons _ _ tl => @sum A (listElim A tl)
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

Fixpoint list_RR (A₁ A₂ : Set) (A_R : A₁ -> A₂ -> Prop) (l1 : list A₁) (l2 : list A₂)
  {struct l1} : Prop :=
match (l1, l2) with
| (nil _, nil _) => True
| (cons _ h1 tl1, cons _ h2 tl2) => (A_R h1 h2) /\ (list_RR _ _ A_R tl1 tl2)
| ( _, _) => False
end.

(* because of template polymorphism, * for /\ works *)

Fixpoint listElim_RR  (A₁ A₂ : Set) (A_R : A₁ -> A₂ -> Prop) (l1 : list A₁) (l2 : list A₂)
  (l_R : list_RR A₁ A₂ A_R l1 l2) {struct l1} (* not l_R *)
 : (listElim A₁ l1) -> (listElim A₂ l2) -> Type :=
let reT := fun l1 l2 => list_RR A₁ A₂ A_R l1 l2 -> (listElim A₁ l1) -> (listElim A₂ l2) -> Type in
(match l1 return reT l1 l2 with
| nil _ => 
  match l2 return reT (nil _) l2 with
  | nil _ => fun l_R => unit_R
  | cons _ _ _ => fun l_R => False_rect _ l_R
  end
| cons _ h1 tl1 =>
  match l2 return reT (cons _ h1 tl1) l2 with
  | nil _ => fun l_R => False_rect _ l_R
  | cons _ h2 tl2 => fun l_R => 
      let tl_R := proj2 l_R in
      @sum_R _ _ A_R
      _ _ (listElim_RR _ _ A_R _ _ tl_R)
  end
end) l_R.

Print eq_R.
(* Should we have a set version as well? *)
(* The return type of eq is a Prop... So we can hust return fun _ _ .. => True *)

Definition eq_RR (A₁ A₂ : Type) (A_R : A₁ -> A₂ -> Type) (x₁ : A₁) (x₂ : A₂) 
(x_R : A_R x₁ x₂) : forall (y₁ : A₁) (y₂ : A₂), A_R y₁ y₂ -> x₁ = y₁ -> x₂ = y₂ -> Prop.
intros ? ?.
(*
rename H into y₁.
rename H0 into y₂. *)
intros ary H1eq H2eq.
destruct H1eq.
destruct H2eq.
exact True.
Defined.


Inductive Vec  (C:Set) : nat -> Type :=
| vnil : Vec C 0
| vcons : forall (n: nat), C -> Vec C n -> Vec C (S n).



(*
Definition transportRev {T : Type} {a b : T} {P : T -> Type}
   (p : a = b) (pb : P b) : P a
:= transport (eq_sym p) pb.
*)


Fixpoint vAppend  {C:Set} {n m : nat} 
  (vl : Vec C n) (vr : Vec C m): Vec C (n+m) :=
match vl in Vec _ n return Vec C (n + m) with
| vnil _ =>  vr
| vcons _ n' hl tl => 
    (vcons _ _ hl (vAppend tl vr))
end.

(* Also try the eq type *)

 
