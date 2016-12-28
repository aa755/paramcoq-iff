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


Fixpoint natElim (n  : nat) : Type:=
match n with
| 0 => bool
| S n => unit + (natElim n)
end.


Parametricity Recursive unit.
Parametricity Recursive sum.

Print nat_R.

(* Print nat_R
Changed Set to Prop
*)
Inductive nat_R : nat -> nat -> (* Set *) Prop :=
nat_R_O_R : nat_R 0 0 | nat_R_S_R : forall H H0 : nat, nat_R H H0 -> nat_R (S H) (S H0).

(*
Parametricity Recursive natElim.
Print natElim_R.
(* copied below *)
*)

(* Fails because nat_R is now in Prop
Definition natElim_R := 
let fix_natElim_1 :=
  fix natElim (n : nat) : Type :=
    match n with
    | 0 => bool
    | S n0 => (unit + natElim n0)%type
    end in
let fix_natElim_2 :=
  fix natElim (n : nat) : Type :=
    match n with
    | 0 => bool
    | S n0 => (unit + natElim n0)%type
    end in
fix natElim_R (n₁ n₂ : nat) (n_R : nat_R n₁ n₂) {struct n_R} :
  fix_natElim_1 n₁ -> fix_natElim_2 n₂ -> Type :=
  match n_R in (nat_R n₁0 n₂0) return (fix_natElim_1 n₁0 -> fix_natElim_2 n₂0 -> Type) with
  | nat_R_O_R => bool_R
  | nat_R_S_R n₁0 n₂0 n_R0 =>
      sum_R unit unit unit_R (fix_natElim_1 n₁0) (fix_natElim_2 n₂0)
        (natElim_R n₁0 n₂0 n_R0)
  end.
*)
