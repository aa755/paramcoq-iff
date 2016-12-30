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
 | CConstruct (id: inductive) (n:nat)
 | CInd (id: inductive)
 | CFix (nMut index: nat) (rindex: list nat) (* recursive index in each body*)
 | CApply (nargs:nat)
(* | NLet *)
 | CCase (i : inductive * nat) (lb: list nat) (* num pats in each branch *)
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
| tConstruct i n => oterm (CConstruct i n) []
| tInd i => oterm (CInd i) []
| tSort s => oterm (CSort s) []
| tLambda n T b => oterm CLambda [bterm [] (toSquiggle T); bterm [n] (toSquiggle b)]
| tCase i typ disc brs => 
    let brs := map (fun p => (fst p, toSquiggle (snd p))) brs in
    oterm (CCase i (map fst brs)) 
        (map ((bterm [])) ((toSquiggle typ)::(toSquiggle disc)::(map snd brs)))
| tProd n T b => oterm CProd [bterm [] (toSquiggle T);  bterm [n] (toSquiggle b)]
| tApp f args => oterm (CApply (length args)) (map ((bterm [])∘toSquiggle) (f::args))
| tFix defs index =>
    let names := map (dname _) defs in
    let bodies := map (toSquiggle∘(dbody _)) defs in
    let types := map (toSquiggle∘(dtype _)) defs in
    let rargs := map (rarg _) defs in
    oterm (CFix (length defs) index rargs) 
        ((map (bterm names) bodies)++map (bterm []) types)
| tCast t ck typ => oterm (CCast ck) (map ((bterm [])∘toSquiggle) [t;typ])
| _ => oterm CUnknown []
end.

Print Ast.one_inductive_entry.
Print Ast.mutual_inductive_entry.

SearchAbout ( nat -> list _  -> list _).
SearchAbout firstn skipn.
Print skipn.

Fixpoint fromSquiggle (t:@DTerm Ast.name CoqOpid) : term :=
(* switch the side, remove toSquiggle from LHS, but fromSquiggle in RHS at the corresponding
place *)
match t with
| vterm n => tRel (N.to_nat n)
| oterm (CSort s) [] => tSort s
| oterm (CConstruct i n) [] => tConstruct i n
| oterm (CInd i) [] => tInd i
| oterm (CConst s) [] => tConst s
| oterm CLambda [bterm [] T; bterm [n] b] =>  
    tLambda n (fromSquiggle T) (fromSquiggle b)
| oterm CProd [bterm [] T; bterm [n] b] =>  
    tProd n (fromSquiggle T) (fromSquiggle b)
| oterm (CApply _) ((bterm [] f)::args) =>
    tApp (fromSquiggle f) (map (fromSquiggle ∘ get_nt) args)
| oterm (CCast ck)  [bterm [] t; bterm [] typ] =>
    tCast (fromSquiggle t) ck (fromSquiggle typ)
| oterm (CFix len index rargs) lbs =>
    tFix
    (match lbs with
    | [] => []
    | (bterm names _)::_ => 
      let lbs := map (fromSquiggle ∘ get_nt) lbs in
      let bodies := firstn len lbs in
      let types := skipn len lbs in
      let f (pp: (name*nat)*(term*term)) :=
        let (name, rarg) := fst pp in
        let (body, type) := snd pp in mkdef _ name type body rarg in
        map f (combine (combine names rargs) (combine bodies types))
     end) index
| oterm (CCase i ln) ((bterm [] bt):: (bterm [] disc)::lb) => 
    let lb := (map (fromSquiggle ∘ get_nt) lb) in
    tCase i (fromSquiggle bt) (fromSquiggle disc) (combine ln lb)

| _ => tUnknown ""
end.

Definition isLocalEntryAssum (l:local_entry) : bool :=
match l with
| LocalAssum _ => true
| LocalDef _ => false
end.

Definition getLocalEntryType (l:local_entry) : term :=
match l with
| LocalAssum t => t
| LocalDef t => t
end.


(* ask the user to reduce away the local lets, or do it automatically before
reification *)
Definition hasNoLocalAssums (t: mutual_inductive_entry) :bool :=
ball (map (isLocalEntryAssum ∘ snd) (mind_entry_params t)).

Definition simple_one_ind (term:Set) : Set := (ident*term).

(* ignore coinductives for now *)
Definition simple_mutual_ind (term:Set) : Set := nat(* params*) *list (simple_one_ind term).

Definition prependProd (lp : list (name*term)) (t:term) : term :=
List.fold_right (fun p t => tProd (fst p) (snd p) t) t lp.

Definition mkSimpleInd pars (t: one_inductive_entry ) : simple_one_ind  term
  := ((mind_entry_typename t), prependProd pars (mind_entry_arity t)).

(* because we would never need to create new inductives, the opposite direction
  wont be necessary *)
Definition parseMutuals (t: mutual_inductive_entry) : simple_mutual_ind term :=
let pars := 
  map
    (fun p => (nNamed (fst p), getLocalEntryType (snd p))) 
    (mind_entry_params t) 
  in (length (pars), (map (mkSimpleInd pars) (mind_entry_inds t))).

Definition mapTermSimpleMutind {A B:Set} (f:A->B) (s: simple_mutual_ind A):
simple_mutual_ind B :=
(fst s, map (fun p => (fst p, f (snd p))) (snd s)).




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

Notation STerm :=  (@NTerm (N*name) CoqOpid).

Definition toSqNamed (t:term) : @NTerm (N*name) CoqOpid:=
  fromDB nAnon (fun n => (3*(fst n), snd n))%N 0%N Maps.empty (toSquiggle t).
  
  
  (* because we would never need to create new inductives, the opposite direction
  wont be necessary *)
Definition parseMutualsSq (t: mutual_inductive_entry) : simple_mutual_ind STerm :=
mapTermSimpleMutind (toSqNamed)  (parseMutuals t).

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
  | Some (inr t) =>
    tr <- @tmReduce Ast.all _ (parseMutualsSq t) ;;
    tmPrint tr 
  | _ => ret tt
  end.

Definition checkTermSq (name  : ident) (b:bool): TemplateMonad unit :=
  x <- tmQuote name true ;;
  match x with
  Some (inl t) => 
    tr <- @tmReduce Ast.all _ (toSqNamed t) ;;
    tmPrint tr ;;
    trb <- @tmReduce Ast.all _ (fromSqNamed tr) ;;
    tmPrint trb ;;
    if b then (tmMkDefinition true (String.append name "__Req") (mkEqTerm t trb))
      else (ret tt) 
  | _ => ret tt
  end.



(* generalize mutual_inductive_entry to be use STerm *)
Definition tmQuoteSq id b : TemplateMonad (option (STerm + simple_mutual_ind STerm)) :=
  t <- tmQuote id b;;
  ret
  (match t with
  | Some (inl t) => Some (inl (toSqNamed t))
  | Some (inr t) => Some (inr (parseMutualsSq t))
  | None => None
  end).

Definition tmMkDefinitionSq id st : TemplateMonad () :=
  tmMkDefinition true id (fromSqNamed st).

Definition ids : forall A : Set, A -> A := fun (A : Set) (x : A) => x.
Definition idsT  := forall A : Set, A -> A.

Run TemplateProgram (printTermSq "ids").
Run TemplateProgram (printTerm "Nat.add").
Run TemplateProgram (printTermSq "Nat.add").
Run TemplateProgram (checkTermSq "ids" true).


Run TemplateProgram (checkTermSq "Nat.add" true).
Run TemplateProgram (checkTermSq "idsT" true).

Definition duplicateDefn (name newName : ident): TemplateMonad unit :=
  (tmBind (tmQuote name false) (fun body => 
    match body with
    | Some (inl bd) => 
        (tmBind (tmPrint body) (fun _ => tmMkDefinition true newName bd))
    | _ => tmReturn tt
    end))
    .
    
Require Import SquiggleEq.varInterface.


Module STermVarInstances.
  Let fvN3 : FreshVars (N*name) _ := 
    @varImplDummyPair.freshVarsNVar  _ _ _ (freshVarsN 3) Ast.nAnon.
  Let vnN3 : VarClass (N*name) _ :=
     @varImplDummyPair.varClassNVar _ _ _ (varClassN 3 eq_refl).
  Existing Instance fvN3.
  Existing Instance vnN3.
  Let vTypeN3 : VarType (N * name) _
    := @varImplDummyPair.vartypePos _ _ _ _ _ _ (vartypeN 3 eq_refl) _ nAnon.
  Existing Instance vTypeN3.
End STermVarInstances.

Require Import String.
Require Import Ascii.

Fixpoint stringMap (f: ascii-> ascii) s : string :=
match s with
| EmptyString => EmptyString
| String a s => String (f a) (stringMap f s)
end.

Definition mapDots (repl : ascii) (s:string) : string:= 
  stringMap (fun a => if (ascii_dec a ".") then repl else a) s.
   
(*
Global Instance deqTerm : Deq term.
apply @deqAsSumbool.
intros ? ?. unfold DecidableSumbool.
repeat decide equality.
Defined.

Print ids__Req.
Print idsT__Req.
*)

 
