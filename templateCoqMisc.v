(* This file should eventually be moved to SquiggleEq *)

Require Import Template.Template.
Require Import Template.Ast.
Require Import Coq.Lists.List.

(*
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
*)


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
(*
Inductives are always referred to as the first one in the mutual block, index.
The names of the second inductive never apear?
*)
 | CInd (id: inductive)
 | CFix (nMut index: nat) (rindex: list nat) (* recursive index in each body*)
 | CApply (nargs:nat)
 | CLet
 | CCase (i : inductive * nat) (lb: list nat) (* num pats in each branch *)
 | CUnknown.

Require Import SquiggleEq.termsDB.
Require Import SquiggleEq.list.
Import ListNotations.
Require Import NArith.
Require Import Program.

(*
Definition xx :nat := let x := 0 in x+x.
Open Scope string_scope.
Run TemplateProgram (printTerm "xx").
*)
Fixpoint toSquiggle (t: term) : (@DTerm Ast.name CoqOpid):=
match t with
| tRel n => vterm (N.of_nat n)
| tConst s => oterm (CConst s) []
| tConstruct i n => oterm (CConstruct i n) []
| tInd i => oterm (CInd i) []
| tSort s => oterm (CSort s) []
| tLambda n T b => oterm CLambda [bterm [] (toSquiggle T); bterm [n] (toSquiggle b)]
| tLetIn n bd typ t => oterm CLet 
    [bterm [n] (toSquiggle t); bterm [] (toSquiggle bd); bterm [] (toSquiggle typ)]
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
| oterm CLet [bterm [n] t; bterm [] bd; bterm [] typ] =>
  tLetIn n (fromSquiggle bd) (fromSquiggle typ) (fromSquiggle t)
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
| oterm (CCase i ln) ((bterm [] typ):: (bterm [] disc)::lb) =>
  (* in lb, all the the lv is always []. the constructor vars are explicit lambdas *)
    let lb := (map (fromSquiggle ∘ get_nt) lb) in
    tCase i (fromSquiggle typ) (fromSquiggle disc) (combine ln lb)

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

Definition simple_one_ind (term bterm:Set) : Set := 
  ((ident*term)* list (ident*bterm)).

(* ignore coinductives for now *)
Definition simple_mutual_ind (term bterm:Set) 
  : Set := (list (name)) *list (simple_one_ind term bterm).

Definition prependProd (lp : list (name*term)) (t:term) : term :=
List.fold_right (fun p t => tProd (fst p) (snd p) t) t lp.

Definition mkSimpleInd pars (t: one_inductive_entry) : simple_one_ind term term
  := ((mind_entry_typename t), prependProd pars (mind_entry_arity t),
        combine (mind_entry_consnames t) ((mind_entry_lc t))).

(* because we would never need to create new inductives, the opposite direction
  wont be necessary *)
Definition parseMutuals (t: mutual_inductive_entry) : simple_mutual_ind term term :=
let pars := 
  map
    (fun p => (nNamed (fst p), getLocalEntryType (snd p))) 
    (mind_entry_params t) 
  in ((map fst pars), (map (mkSimpleInd pars) (mind_entry_inds t))).

Definition mapTermSimpleOneInd {A A2 B B2:Set} (f:A->B) (g:A2->B2) (t: simple_one_ind A A2):
simple_one_ind B B2 :=
let (nty, cs) := t in
let (n,ty):= nty in
(n, f ty, map (fun p => (fst p, (g (snd p)))) cs).

Definition mapTermSimpleMutInd {A A2 B B2:Set} (f:A->B) (g:A2->B2) (t: simple_mutual_ind A A2):
simple_mutual_ind B B2 :=
let (n, cs) := t in (n, map (mapTermSimpleOneInd f g) cs).


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
- f_equal; try rewrite IHt1; try rewrite IHt2; try rewrite IHt3;
     try reflexivity. admit. admit. admit.
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
Notation SBTerm :=  (@BTerm (N*name) CoqOpid).

Let mkNVar3 (n:(N*name)) := (3*(fst n), snd n)%N.
Let dbToNamed : DTerm -> (@NTerm (N*name) CoqOpid):=
fromDB nAnon mkNVar3 0%N Maps.empty.
Let dbToNamed_bt : DBTerm -> (@BTerm (N*name) CoqOpid):=
fromDB_bt nAnon mkNVar3 0%N Maps.empty.

Definition toSqNamed (t:term) : @NTerm (N*name) CoqOpid:=
  dbToNamed (toSquiggle t).
  
  
  (* because we would never need to create new inductives, the opposite direction
  wont be necessary *)

Definition toOneIndSq names : (simple_one_ind term term) -> simple_one_ind DTerm DBTerm:=
mapTermSimpleOneInd toSquiggle ((termsDB.bterm names)∘ toSquiggle).

Definition toMutualIndSq  (t: simple_mutual_ind term term) : simple_mutual_ind DTerm DBTerm:=
let (n,ones) := t in
let names := map (nNamed∘fst∘fst) ones in
(n, map (toOneIndSq (names++n)) ones).


Definition parseMutualsSq : mutual_inductive_entry -> simple_mutual_ind STerm 
  (@BTerm (N*name) CoqOpid):=
(mapTermSimpleMutInd dbToNamed dbToNamed_bt) ∘ toMutualIndSq ∘ parseMutuals.


Require Import SquiggleEq.UsefulTypes.
Require Import SquiggleEq.list.
Require Import String.
Require Import DecidableClass.

Global Instance deqName : Deq name.
intros x y.
exists (
match (x,y) with
|(nNamed x,nNamed y) => decide (x=y)
| (nAnon, nAnon) => true
| _ => false
end
).
destruct x, y; split; intros Hyp; try (inverts Hyp; fail); try auto.
- setoid_rewrite Decidable_spec in Hyp.
  f_equal. assumption.
- setoid_rewrite Decidable_spec. inverts Hyp.
  refl.
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
Definition tmQuoteSq id b : TemplateMonad (option (STerm + simple_mutual_ind STerm SBTerm)) :=
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

Definition mapDefn (f:term->term)
  (name newName : ident): TemplateMonad unit :=
  (tmBind (tmQuote name false) (fun body => 
    match body with
    | Some (inl bd) => 
        (tmBind (tmPrint body) (fun _ => tmMkDefinition true newName (f bd)))
    | _ => tmReturn tt
    end))
    .

Definition duplicateDefn := (mapDefn id).

Require Import SquiggleEq.varInterface.

(* TODO : Move : this is specific to parametricity *)
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

Set Implicit Arguments.
Record fixDef (term : Set) : Set := mkdef
  { ftype : term;  fbody : term;  structArg : nat }.

Definition V:Set := (N*name).

Open Scope N_scope.

Definition vprime (v:V) : V := (1+(fst v), nameMap (fun x => String.append x "₂") (snd v)).
Definition vrel (v:V) : V := (2+(fst v), nameMap (fun x => String.append x "_R") (snd v)).

Notation mkLam x A b :=
  (oterm CLambda [bterm [] A; bterm [x] b]).

Notation mkLetIn x bd typ t :=
  (oterm CLet [bterm [x] t; bterm [] bd; bterm [] typ]).

Notation mkPi x A b :=
  (oterm CProd [bterm [] A; bterm [x] b]).

Require Import List.

(* because of length, this cannot be used as a pattern *)
Definition mkApp (f: STerm) (args: list STerm) : STerm :=
  oterm (CApply (length args)) ((bterm [] f)::(map (bterm []) args)).

Notation mkConst s:=
  (oterm (CConst s) []).

Notation mkConstInd s:=
  (oterm (CInd s) []).

Notation mkSort s  :=
  (oterm (CSort s) []).

Notation mkCast t ck typ :=
  (oterm (CCast ck) [bterm [] t; bterm [] typ]).

Definition mkConstApp s l : STerm :=
mkApp  (mkConst s) l.

Require Import SquiggleEq.UsefulTypes.

Definition mkIndApp (i:inductive) l : STerm :=
if (decide (length l=0))%nat then (mkConstInd i) else
mkApp (mkConstInd i) l.

Definition removeHeadCast (t:STerm) : STerm :=
match t with
| mkCast t  _ (mkSort _) => t
| _ => t
end.

Definition mkLamL (lb: list (V*STerm)) (b: STerm) 
  : STerm :=
fold_right (fun p t  => mkLam (fst p) (snd p) t) b lb.



Definition mkPiL (lb: list (V*STerm)) (b: STerm) 
  : STerm :=
fold_right (fun p t  => mkPi (fst p) (snd p) t) b lb.

Definition mkSig  (a : N * name) (A B : STerm) := 
 mkApp (mkConstInd (mkInd "Coq.Init.Specif.sigT" 0)) [A, mkLam a A B].

Definition mkSigL (lb: list (V*STerm)) (b: STerm) 
  : STerm :=
fold_right (fun p t  => mkSig (fst p) (snd p) t) b lb.

Definition changeVarName (v:V) (name:String.string): V := (fst v, nNamed name).

Require Import SquiggleEq.substitution.

Definition boolToProp (b:bool) : STerm := 
  if b then mkConstInd (mkInd "Coq.Init.Logic.True" 0)
            else mkConstInd (mkInd "Coq.Init.Logic.False" 0).


Fixpoint mkAppBeta (f: STerm) (args: list STerm) : STerm :=
  match (f, args) with
  | (mkLam x _ b, a::[]) => 
      (apply_bterm (bterm [x] b) [a])
  | (mkLam x _ b, a::tl) => 
      mkAppBeta (apply_bterm (bterm [x] b) [a]) tl
  | _ => mkApp f args
  end.


Fixpoint headLamsToPi (tail tlams :STerm) : STerm := 
match tlams with
| mkLam n A b => mkPi n A (headLamsToPi tail b)
| _ => tail
end.

Fixpoint getHeadPIs (s: STerm) : STerm * list (V*STerm) :=
match s with
| mkPi nm A B => let (t,l):=(getHeadPIs B) in (t,(nm,A)::l)
| mkCast t _ _ => getHeadPIs t
| _ => (s,[])
end.

Fixpoint flattenApp (s: STerm) (args: list STerm): STerm * list (STerm) :=
match s with
| oterm (CApply _) (s :: argsi) => 
  flattenApp (get_nt s) ((map get_nt argsi)++args)
| mkCast s _ _ => flattenApp s args
| _ => (s,args)
end.


Fixpoint reduce (n:nat) (s: STerm) {struct n}: STerm :=
match n with
| 0%nat => s
| S m => 
  match s with
  | oterm o lbt =>
    match (o,lbt) with
    | (CApply _, (bterm [] (mkLam x _ b))::(bterm [] a)::(h::tl))
      => reduce m (mkApp (apply_bterm (bterm [x] b) [a]) (map get_nt (h::tl)))
    | (CApply _, (bterm [] (mkLam x _ b))::(bterm [] a)::[])
      => reduce m (apply_bterm (bterm [x] b) [a])
    | (CApply 0, [bterm [] f])
      => reduce m f
    | _ => let lbt := map (btMapNt (reduce m)) lbt in oterm o lbt
    end
  | vterm v => vterm v
  end
end.



Definition appsBad :=
         (oterm (CApply 1)
            [bterm []
               (mkLam (3, nNamed "y")
                  (mkSort sSet)
                  (mkLam (0, nNamed "x")
                     (mkSort sSet)
                     (oterm (CApply 2)
                        [bterm [] (mkConst "add");
                        bterm [] (vterm (0, nNamed "x"));
                        bterm [] (vterm (3, nNamed "y"))])));
            bterm [] (vterm (0, nNamed "x"))]).

Example noCapture : (reduce 100 appsBad) = 
mkLam (12, nNamed "x") (mkSort sSet)
  (oterm (CApply 2)
     [bterm [] (mkConst "add"); bterm [] (vterm (12, nNamed "x"));
     bterm [] (vterm (0, nNamed "x"))]).
Proof using.
  unfold appsBad.
  compute. refl.
Qed.

Eval compute in (reduce 10 appsBad).


Definition getIndName (i:inductive) : String.string :=
match i with
| mkInd s _ => s
end.


Definition isRecursive (tind: inductive) (typ: STerm) : (bool):=
let n : String.string := getIndName tind in
match typ with
| mkConstInd s => (decide (getIndName s=n))
| _ => (false)
end.

Definition isConstrArgRecursive (tind: inductive) (typ: STerm) : (bool):=
    let (ret, _) := getHeadPIs typ in
    let (ret, _) := flattenApp ret [] in
    (isRecursive tind ret).



 
