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
 | CCast (ck:cast_kind)
 | CConst (id: ident)
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
| tConst s => oterm (CConst s) []
| tSort s => oterm (CSort s) []
| tLambda n T b => oterm CLambda [bterm [] (toSquiggle T); bterm [n] (toSquiggle b)]
| tProd n T b => oterm CProd [bterm [] (toSquiggle T);  bterm [n] (toSquiggle b)]
| tApp f args => oterm (CApply (length args)) (map ((bterm [])∘toSquiggle) (f::args))
| tCast t ck typ => oterm (CCast ck) (map ((bterm [])∘toSquiggle) [t;typ])
| _ => oterm CUnknown []
end.


Fixpoint fromSquiggle (t:@DTerm Ast.name CoqOpid) : term :=
(* switch the side, remove toSquiggle from LHS, but fromSquiggle in RHS at the corresponding
place *)
match t with
| vterm n => tRel (N.to_nat n)
| oterm (CSort s) [] => tSort s
| oterm (CConst s) [] => tConst s
| oterm CLambda [bterm [] T; bterm [n] b] =>  
    tLambda n (fromSquiggle T) (fromSquiggle b)
| oterm CProd [bterm [] T; bterm [n] b] =>  
    tProd n (fromSquiggle T) (fromSquiggle b)
| oterm (CApply _) ((bterm [] f)::args) =>
    tApp (fromSquiggle f) (map (fromSquiggle ∘ get_nt) args)
| oterm (CCast ck)  [bterm [] t; bterm [] typ] =>
    tCast (fromSquiggle t) ck (fromSquiggle typ)
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


Definition toSqNamed (t:term) : @NTerm (N*name) CoqOpid:=
  fromDB nAnon (fun n => (3*(fst n), snd n))%N 0%N Maps.empty (toSquiggle t).
  
Require Import SquiggleEq.UsefulTypes.

Global Instance deqName : Deq name.
apply @deqAsSumbool.
intros ? ?. unfold DecidableSumbool.
repeat decide equality.
Defined.

Definition fromSqNamed (t:@NTerm (N*name) CoqOpid) : term :=
  fromSquiggle (toDB snd [] t).

Import MonadNotation.
Open Scope monad_scope.

Require Import ExtLib.Structures.Monads.

Quote Definition ds := (eq_refl: (false = false)).
Print ds.

Definition mkEq (t1 t2 typ:term) :=
tCast
  (tApp (tConstruct (mkInd "Coq.Init.Logic.eq" 0) 0)
     [typ,t1]) Cast
  (tApp (tInd (mkInd "Coq.Init.Logic.eq" 0))
     [typ,t1,t2]).

Definition mkEqTerm (t1 t2:term) :=
mkEq t1 t2 (tInd (mkInd "Template.Ast.term" 0)).


Definition printTermSq (name  : ident): TemplateMonad unit :=
  x <- tmQuote name true ;;
  match x with
  Some (inl t) => 
    tr <- @tmReduce Ast.all _ (toSqNamed t) ;;
    tmPrint tr 
  | _ => ret tt
  end.

Definition checkTermSq (name  : ident): TemplateMonad unit :=
  x <- tmQuote name true ;;
  match x with
  Some (inl t) => 
    tr <- @tmReduce Ast.all _ (toSqNamed t) ;;
    tmPrint tr ;;
    trb <- @tmReduce Ast.all _ (fromSqNamed tr) ;;
    tmPrint trb ;;
    tmMkDefinition true (String.append name "__Req") (mkEqTerm t trb)
  | _ => ret tt
  end.

Notation STerm :=  (@NTerm (N*name) CoqOpid).

(* generalize mutual_inductive_entry to be use STerm *)
Definition tmQuoteSq id b : TemplateMonad (option (STerm + mutual_inductive_entry)) :=
  t <- tmQuote id b;;
  ret
  (match t with
  | Some (inl t) => Some (inl (toSqNamed t))
  | Some (inr t) => Some (inr t)
  | None => None
  end).

Definition tmMkDefinitionSq id st : TemplateMonad () :=
  tmMkDefinition true id (fromSqNamed st).

(*
Global Instance deqTerm : Deq term.
apply @deqAsSumbool.
intros ? ?. unfold DecidableSumbool.
repeat decide equality.
Defined.

Definition ids : forall A : Set, A -> A := fun (A : Set) (x : A) => x.
Definition idsT  := forall A : Set, A -> A.

Run TemplateProgram (printTermSq "ids").
Run TemplateProgram (checkTermSq "ids").
Run TemplateProgram (checkTermSq "idsT").
Print ids__Req.
Print idsT__Req.
*)

 
