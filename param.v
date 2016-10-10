Require Import Coq.Classes.DecidableClass.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import SquiggleEq.export.
Require Import SquiggleEq.UsefulTypes.
Require Import SquiggleEq.list.
Require Import SquiggleEq.LibTactics.
Require Import SquiggleEq.tactics.
Require Import SquiggleEq.lmap.

Section VarSort.

Variable V:Set.

(* this type contains terms denoting Coq's sorts,
which are Prop, Set, Type_i *)
Variable S : Set.
Variable translateS : S -> S.

Inductive Opid : Set :=
(* x, which is var, we get for free *)
 | pSort : S -> Opid
 | pLam
 | pPi
(* | pSig *)
 | pApp
(* pNat *)
(* p0 *)
(* pS *)
(* pPrimRec *).

Definition OpBindings (c : Opid) 
    : list nat :=
  match c with
  | pSort _ => [0] (* continuation lambda  *)
  | pLam => [1] (* continuation lambda  *)
  | pPi => [1] (* continuation lambda  *)
  | pApp => [0;0]
  end.

Let Term : Set := (@NTerm V Opid).

End VarSort.

