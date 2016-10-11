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

Section MaxUniv.

(* max universe. 0 denotes [Set] *)
Variable n : nat.

Inductive Opid : Set :=
(* x, which is var, we get for free *)
 | pSort : forall m, (PeanoNat.Nat.leb m n = true) -> Opid
 | pLam
 | pPi
 | pSig
 | pApp
 | projSig : bool (* true := fst, false := snd *) -> Opid
(* pNat *)
(* p0 *)
(* pS *)
(* pPrimRec *).

Definition OpBindings (c : Opid) 
    : list nat :=
  match c with
  | pSort _ _ => [0]
  | pLam => [0,1] (* contains type as well  *)
  | pPi => [0,1]
  | pSig => [0,1]
  | projSig _ => [0]
  | pApp => [0;0]
  end.


End MaxUniv.
Let Term : nat -> Set := (fun n => (@NTerm V (Opid n))).



(* We can define the semantics of Term 1, by going as TermplateCoq.Term.
Then, one would have to manually reflect it using the "Make Definition" command.
Else, we can also just pretty print as a string, and dump the contents to a .v file. *)

(*
There is no way to give semantics where t:Term i is mapped to {T:Type | T}.
Think about (oterm (pLam) (bterm [x] (vterm x))). We want it to map it to
fun x => x. Suppose V:=string. There is no way to convert the string "x" to the binder x in fun x => x.
There is not even a way to get a fresh binders. the "fresh" function is only available in Ltac.
If there were such a function in Coq, we could cook up well-typed open terms, which is impossible.

Perhaps thats why the "Make Definition" command of template-Coq is external
*)

(*
Because there is no internal semantics function, we cannot use it to reduce the typehood of codes
to the typehood of the semantics. It may be best to formalize the typehood.
*)

Fixpoint translate (n:nat) (t:Term n) : Term (S n).
Abort.


End VarSort.

