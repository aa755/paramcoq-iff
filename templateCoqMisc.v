Require Import Template.Template.
Require Import Template.Ast.
Require Import Coq.Lists.List.

Fixpoint mkLamL (lt: list (name *term)) (b: term) 
  : term :=
match lt with
| nil => b
| a::tl =>  tLambda (fst a) (snd a )(mkLamL tl b)
end.


Definition mkFun  (A B: term) : term :=
  tProd nAnon A B.

(* copied from
https://coq.inria.fr/library/Coq.Unicode.Utf8_core.html#
*)
Notation "x ↪ y" := (mkFun x y)
  (at level 99, y at level 200, right associativity).

Definition nameMap (f: ident -> ident) (n:name): name :=
match n with
| nNamed s => nNamed (f s)
| nAnon => nAnon
end.


Fixpoint mapDbIndices (f:nat -> nat) (t:term) : term :=
match t with
| tRel n => tRel (f n)

| _ => (* mapDbIndices f t *) t
end.

Require Import ExtLib.Structures.Monads.

Global Instance tmMonad : Monad TemplateMonad :=
  Build_Monad _ (@tmReturn) (@tmBind).

Ltac cexact ids := 
  (let T := eval compute in ids in exact T).

Definition printTerm (name  : ident): TemplateMonad unit :=
  (tmBind (tmQuote name true) tmPrint).


Inductive CoqOpid : Set :=
 | CLambda
 | CProd
 | CSort (s: sort)
 | CCast
 | CConst
(* | TFix (nMut index: nat) *)
(* | NDCon (dc : inductive*nat) (nargs : nat) *)
 | CApply (nargs:nat)
(* | NLet *)
(* | NMatch (dconAndNumArgs : list (dcon * nat)). *)
 | CUnknown.

Require Import SquiggleEq.termsDB.
Require Import SquiggleEq.list.
Import ListNotations.
Require Import NArith.
Require Import Program.

Fixpoint toSquiggle (t: term) : (@DTerm Ast.name CoqOpid):=
match t with
| tRel n => vterm (N.of_nat n)
| tSort s => oterm (CSort s) []
| tLambda n T b => oterm CLambda [bterm [] (toSquiggle T); bterm [n] (toSquiggle b)]
| tProd n T b => oterm CProd [bterm [] (toSquiggle T);  bterm [n] (toSquiggle b)]
| tApp f args => oterm (CApply (length args)) (map ((bterm [])∘toSquiggle) (f::args))
| _ => oterm CUnknown []
end.


Fixpoint fromSquiggle (t:@DTerm Ast.name CoqOpid) : term :=
(* switch the side, remove toSquiggle from LHS, but fromSquiggle in RHS at the corresponding
place *)
match t with
| vterm n => tRel (N.to_nat n)
| oterm (CSort s) [] => tSort s
| oterm CLambda [bterm [] T; bterm [n] b] =>  
    tLambda n (fromSquiggle T) (fromSquiggle b)
| oterm CProd [bterm [] T; bterm [n] b] =>  
    tProd n (fromSquiggle T) (fromSquiggle b)
| oterm (CApply _) ((bterm [] f)::args) =>
    tApp (fromSquiggle f) (map (fromSquiggle ∘ get_nt) args)
| _ => tUnknown ""
end.

Require Import SquiggleEq.tactics.
Require Import SquiggleEq.LibTactics.
Require Import Psatz.

Lemma fromSquiggleFromSquiggleInv t:
  getOpid (toSquiggle t) <> Some CUnknown
  -> fromSquiggle (toSquiggle t) = t.
Proof using.
  induction t; unfold getOpid; simpl; intros Hneq; sp.
- f_equal. lia.
- f_equal; try rewrite IHt1; try rewrite IHt2; try reflexivity. admit. admit.
- f_equal; try rewrite IHt1; try rewrite IHt2; try reflexivity. admit. admit.
- repeat rewrite map_map. unfold compose. simpl. 
  f_equal;[ apply IHt| setoid_rewrite <- (map_id l) at 2; apply eq_maps;
      intros].
  (* term_ind is weak *) admit.  admit.
Abort.

Require Import SquiggleEq.varImplN.
Require Import SquiggleEq.varImplDummyPair.
Require Import SquiggleEq.terms.
Require Import ExtLib.Data.Map.FMapPositive.

Section Temp.

Definition toSqNamed (t:term) : @NTerm (N*name) CoqOpid:=
  fromDB nAnon id 0%N Maps.empty (toSquiggle t).
  
Require Import SquiggleEq.UsefulTypes.

Global Instance deqName : Deq name.
apply @deqAsSumbool.
intros ? ?. unfold DecidableSumbool.
repeat decide equality.
Defined.


Definition fromSqNamed (t:@NTerm (N*name) CoqOpid) : term :=
  fromSquiggle (toDB snd [] t).


 
