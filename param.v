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

Set Implicit Arguments.


Section MaxUniv.

(* max universe. 0 denotes [Set] *)
Variable n : nat.

Set Implicit Arguments.

Inductive Opid : Set :=
(* x, which is var, we get for free *)
 | pSort : forall m, (PeanoNat.Nat.leb m n = true) -> Opid
 | pLam
 | pPi
 | pSig
 | pApp
 | pProjSig : bool (* true := fst, false := snd *) -> Opid
 | pPair : bool (* true := fst, false := snd *) -> Opid
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
  | pProjSig _ => [0]
  | pPair _ => [0;0]
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

(* v' in the translation on paper *)
Variable vprime : V -> V.
(* v_R in the translation on paper *)
Variable vrel : V -> V.
(* later, axiomatize that the output of vprime and the outputs of vrel and the inputs to these functions
are in (3) disctinct classes *)

Definition mkLam {n:nat} (x: V) (A b: Term n) : Term n :=
  oterm (pLam _) [bterm [] A; bterm [x] b].

Definition mkPi {n:nat} (x: V) (A b: Term n) : Term n :=
  oterm (pLam _) [bterm [] A; bterm [x] b].

Definition mkSig {n:nat} (x: V) (A b: Term n) : Term n :=
  oterm (pSig _) [bterm [] A; bterm [x] b].

Definition mkApp {n:nat}  (A B: Term n) : Term n :=
  oterm (pApp _) [bterm [] A; bterm [] B].

(* use fold_left. *)
Fixpoint mkAppL {n:nat}  (f : Term n) (args : list (Term n)) : Term n :=
match args with
| nil => f
| a::tl => mkAppL (mkApp f a) tl
end.

Inductive VClass := vOrig | vPrim | vRel.

Context `{VarType V VClass}.

(* Move to Squiggle *)


Definition mkFun {n:nat} (A B: Term n) : Term n :=
  mkPi (freshVar vOrig (free_vars B)) A B.

Definition mkProd {n:nat} (A B: Term n) : Term n :=
  mkSig (freshVar vOrig (free_vars B)) A B.

Fixpoint mkLamL {n:nat} (lb: list (V*Term n)) (b: Term n) 
  : Term n :=
match lb with
| nil => b
| a::tl =>  mkLam (fst a) (snd a )(mkLamL tl b)
end.

Fixpoint mkPiL {n:nat} (lb: list (V*Term n)) (b: Term n) 
  : Term n :=
match lb with
| nil => b
| a::tl =>  mkPi (fst a) (snd a )(mkPiL tl b)
end.


Notation "x → y" := (mkFun x y)
  (at level 99, y at level 200, right associativity).

Let dvar := (freshVar vOrig []).

Definition mkTR {n:nat} (A B s: Term n): Term n :=
  let lv := (freshVars 3 (Some vOrig) (free_vars B ++ free_vars A) []) in
  let R := nth 0 lv dvar in
  let a := nth 1 lv dvar in
  let b := nth 2 lv dvar in
 mkSig R (A → B → s) 
    (mkProd 
      (mkPi a A (mkSig b B (mkAppL (vterm R) [vterm a; vterm b]))) 
      (mkPi b B (mkSig a A (mkAppL (vterm R) [vterm a; vterm b]))) 
      ).

Definition pfst {n:nat} (T: Term n): Term n :=
oterm (pProjSig _ true) [bterm [] T].

Fixpoint translate {n:nat} (t:Term n) : Term n :=
match t with
| vterm v => vterm (vrel v)
| oterm (pSort _ _ n) [] => 
  let x:= dvar in
  mkLamL [(x,t);(vprime x, t)] (mkTR (vterm x) (vterm (vprime x)) t)
| oterm (pPi _) [bterm [] A; bterm [x] B] =>
  let f:= (freshVar vOrig (free_vars A ++ free_vars B)) in
  let A':= tvmap vprime A in
  let B':= tvmap vprime B in
  let t' := oterm (pPi _) [bterm [] A'; bterm [x] B'] in 
  let tA := translate A in 
  let tB := translate B in 
(* fix : make a sigma type, with proof of totality of the relation below *)
 mkLamL 
  [(f,t);(vprime f,t')]
  (mkPiL 
   [(x,A);(vprime x, A');(vrel x, mkAppL (pfst tA) [vterm x; vterm (vprime x)])]
    (mkAppL (pfst tB) [mkApp (vterm f) (vterm x); 
                    mkApp (vterm (vprime f)) (vterm (vprime x))]))
| _ => oterm (pApp _) nil
end.

(*
because any type can be provided for instantiating an existential, as in RProp rforall,all type constructors must preserve 
  the property required by such instantiations.
E.g., because we have (nat->nat) : Type,
we have [[nat->nat]]: [[Type]] (nat -> nat) (nat -> nat),
which computes to saying that [[nat->nat]] is a total relation.
*)

Print VarType.
End VarSort.

