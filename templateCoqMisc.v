(* This file should eventually be moved to SquiggleEq *)

Require Import Template.Template.
Require Import Template.Ast.
Require Import Coq.Lists.List.

(*
Make Definition ddd := (tRel 2).
 reference _UNBOUND_REL_3 was not found *)

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

Definition nAppend (s:ident) (n : name) := 
 match n with
 | nAnon => nNamed s
 | nNamed ss => nNamed (String.append ss s)
 end.


Require Import ExtLib.Structures.Monads.

Global Instance tmMonad : Monad TemplateMonad :=
  Build_Monad _ (@tmReturn) (@tmBind).

Ltac cexact ids := 
  (let T := eval compute in ids in exact T).

Definition printTerm (name  : ident): TemplateMonad unit :=
  (tmBind (tmQuote name true) tmPrint).

Set Boolean Equality Schemes.

Inductive CoqOpid (*b:bool*): Set :=
 | CLambda (argSort : option sort)
 | CProd (argsort bodySort : option sort)
(* | CProd : if b then (option sort -> option sort-> CoqOpid b) else (CoqOpid b) *)
 | CSort (s: sort)
 | CCast (ck:cast_kind)
 | CConst (id: ident)
 | CConstruct (id: inductive) (n:nat)
(*
Inductives are always referred to as the first one in the mutual block, index.
The names of the second inductive never apear?
*)
 | CInd (id: inductive)
 | CFix (nMut: nat) (rindex: list nat) (* recursive index in each body*) (retSort : list (option sort))
        (index: nat) (* which one in the mutual block does this fix represent *)
 | CApply (nargs:nat)
 | CLet
 | CCase (i : inductive * nat) (lb: list nat) (* num pats in each branch *)
         (retSort : option sort)
 | CUnknown (s:String.string).

Unset Boolean Equality Schemes.

Require Import SquiggleEq.list.
Require Import SquiggleEq.UsefulTypes.

Lemma CoqOpid_beq_correct a b : CoqOpid_beq a b = true <-> a = b.
Admitted.


Global Instance deqCoqOpid : Deq CoqOpid.
Proof.
  intros ? ?. exists (CoqOpid_beq a b).
  apply CoqOpid_beq_correct.
Defined.  

Require Import SquiggleEq.termsDB.
Import ListNotations.
Require Import NArith.
Require Import Program.
Require Import String.
Require Import List.

Arguments dname {term} d.
Arguments dtype {term} d.
Arguments dbody {term} d.
Arguments rarg {term} d.

(* use this in Template.Ast?, where var is hardcoded as name *)
Record fixDef (var term : Set) : Set := mkfdef
  { fname: var ; ftype : (term*option sort);  fbody : term;  structArg : nat }.

Arguments fname {var }{term} f.
Arguments ftype {var }{term} f.
Arguments fbody {var }{term} f.
Arguments structArg {var }{term} f.

Definition  toFixDef {V T : Set} (fv: name -> V) (ft: term -> T) (d:def term): fixDef V T :=
  {| fname := fv (dname d); ftype := (ft (dtype d), None); fbody := ft (dbody d)
     ; structArg := rarg d |}.

Definition  fromFixDef {V T : Set} (fv: V  -> name) (ft: T -> term) (d: fixDef V T): def term :=
  (* assuming that Pis have been put back by this time. ignores sort info *)
  {| dname := fv (fname d); dtype := ft (fst (ftype d)); dbody := ft (fbody d)
     ; rarg := structArg d |}.


Definition  fixDefSq {Var BTerm NTerm: Set} 
            (bterm: list Var -> NTerm -> BTerm) (defs : list (fixDef Var NTerm)) :
  (nat -> CoqOpid) * list BTerm :=
  let names := map fname defs in
    let bodies := map fbody defs in
    let types := map (fst ∘ ftype) defs in
    let rargs := map structArg defs in
    (* having bodies and types be side by side in the list, instead of having all bodies first,
then all types, may be friendlier w.r.t the typechecker *)
    (CFix (length defs) rargs [],
        (map (bterm names) bodies)++map (bterm []) types).

  
Open Scope string_scope.

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
| tLambda n T b => oterm (CLambda None)
   [bterm [] (toSquiggle T); bterm [n] (toSquiggle b)]
| tLetIn n bd typ t => oterm CLet 
    [bterm [n] (toSquiggle t); bterm [] (toSquiggle bd); bterm [] (toSquiggle typ)]
| tCase i typ disc brs => 
    let brs := map (fun p => (fst p, toSquiggle (snd p))) brs in
    oterm (CCase i (map fst brs) None) 
        (map ((bterm [])) ((toSquiggle typ)::(toSquiggle disc)::(map snd brs)))
| tProd n T b => oterm (CProd None None) 
    [bterm [] (toSquiggle T);  bterm [n] (toSquiggle b)]
| tApp f args => oterm (CApply (length args)) (map ((bterm [])∘toSquiggle) (f::args))
| tFix defs index =>
  let fd : list (fixDef name (@DTerm Ast.name CoqOpid)) := map (toFixDef id toSquiggle) defs in
  let olb : (nat -> CoqOpid) * list (@DBTerm Ast.name CoqOpid) :=
      fixDefSq bterm fd in
  let (o,lb) := olb in
  oterm (o index) lb
  (*
    let names := map (dname _) defs in
    let bodies := map (toSquiggle∘(dbody _)) defs in
    let types := map (toSquiggle∘(dtype _)) defs in
    let rargs := map (rarg _) defs in
    oterm (CFix (length defs) rargs index) 
        ((map (bterm names) bodies)++map (bterm []) types) *)
| tCast t ck typ => oterm (CCast ck) (map ((bterm [])∘toSquiggle) [t;typ])
| tUnknown s => oterm (CUnknown s) []
| _ => oterm (CUnknown "bad case in toSquiggle") []
end.

Print Ast.one_inductive_entry.
Print Ast.mutual_inductive_entry.

SearchAbout ( nat -> list _  -> list _).
SearchAbout firstn skipn.
Print skipn.
Require Import DecidableClass.

(* this is easier for the termination checker *)
Definition  tofixDefSqAux {V BTerm term: Set}
            (names : list V)
            (fbt (*get nt and fromSquiggle *) : BTerm -> term)
            (len : nat) (rargs : list nat) (sorts : list (option sort))
            (lbs: list BTerm)
  : list (fixDef V term) :=
      let lbs := map fbt lbs in
      let bodies := firstn len lbs in
      let types := skipn len lbs in
      let f (pp: (V*nat)*(term*(term * (option sort)))) :=
        let (name, rarg) := fst pp in
        let (body, type) := snd pp in mkfdef _ _ name type body rarg in
      map f (combine (combine names rargs) (combine bodies (combineDef2 types sorts None))).



(*
Definition  tofixDefSq {V BTerm NTerm term: Set}
            (get_vars : BTerm -> list V)
            (fbt (*get nt and fromSquiggle *) : BTerm -> term)
            (len : nat) (rargs : list nat)
            (lbs: list BTerm)
  : list (fixDef V term) :=
    (match lbs with
    | [] => []
    | b::_ =>
      tofixDefSqAux (get_vars b) fbt len rargs lbs
     end).
*)

Definition prependProd (lp : list (name*term)) (t:term) : term :=
List.fold_right (fun p t => tProd (fst p) (snd p) t) t lp.

(* these are not for STerm *)
Fixpoint extractNHeadProds (n:nat) (t:term) : list (name*term) :=
match (n,t) with
| (S n,tProd nm A B) => (nm,A)::(extractNHeadProds n B)
| _ => []
end.

(* these are not for STerm *)
Fixpoint extractNHeadLams (n:nat) (t:term) : list (name*term) :=
match (n,t) with
| (S n,tLambda nm A B) => (nm,A)::(extractNHeadLams n B)
| _ => []
end.

(* 
see deb2fed4662026b671c68db631c8f606b3c9ffdc. DB is to late to do this. need to do it
before DB conversion

Definition putPisOnType (p:nat*def term) : def term:=
  let (numPis, d) := p in
  let bodyLamArgs := extractNHeadLams numPis (dbody d) in
  {| dname := dname d;
     dtype := prependProd bodyLamArgs (dtype d);
     dbody := (dbody d)
     ; rarg := rarg d |}.
*)

Fixpoint fromSquiggle (t:@DTerm Ast.name CoqOpid) : term :=
(* switch the side, remove toSquiggle from LHS, but fromSquiggle in RHS at the corresponding
place *)
match t with
| vterm n => tRel (N.to_nat n)
| oterm (CSort s) [] => tSort s
| oterm (CConstruct i n) [] => tConstruct i n
| oterm (CInd i) [] => tInd i
| oterm (CConst s) [] => tConst s
| oterm (CLambda _) [bterm [] T; bterm [n] b] =>  
    tLambda n (fromSquiggle T) (fromSquiggle b)
| oterm CLet [bterm [n] t; bterm [] bd; bterm [] typ] =>
  tLetIn n (fromSquiggle bd) (fromSquiggle typ) (fromSquiggle t)
| oterm (CProd _ _) [bterm [] T; bterm [n] b] =>  
    tProd n (fromSquiggle T) (fromSquiggle b)
| oterm (CApply _) ((bterm [] f)::args) =>
    tApp (fromSquiggle f) (map (fromSquiggle ∘ get_nt) args)
| oterm (CCast ck)  [bterm [] t; bterm [] typ] =>
    tCast (fromSquiggle t) ck (fromSquiggle typ)
| oterm (CFix len rargs _ index) lbs =>
  let names := getFirstBTermNames lbs in
  let fds := @tofixDefSqAux _ _ _ names (fromSquiggle ∘ get_nt)
                            len rargs [] lbs in
  let fds : list (def term) := (map (fromFixDef id id) fds) in
(* 
see deb2fed4662026b671c68db631c8f606b3c9ffdc. DB is to late to do this. need to do it
before DB conversion
 let typNumBvars : list nat := map ((@length _) ∘ termsDB.get_bvars) (skipn len lbs) in
  let fds := map putPisOnType (combine typNumBvars fds) in

It is now the user's responsibility to do:
undoProcessFixBodyType before reflecting
if they did ProcessFixBodyType after reification
 *)
  tFix fds index
| oterm (CCase i ln _) ((bterm [] typ):: (bterm [] disc)::lb) =>
  (* in lb, all the the lv is always []. the constructor vars are explicit lambdas *)
    let lb := (map (fromSquiggle ∘ get_nt) lb) in
    let lb := if (decide (length ln = length lb)) 
          then lb 
          else skipn 1 lb (*skip the discriminant type*) in
    tCase i (fromSquiggle typ) (fromSquiggle disc) (combine ln lb)
| oterm (CUnknown s) [] => tUnknown s
| _ => tUnknown "bad case in fromSquiggle"
end.
(* (@DTerm Ast.name CoqOpid) _ get_bvars *)
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
  ((ident (* name of the indictive *) *term (* type of the inductive*) ) *
   list (ident*bterm) (*names and types of constructors. 
             vars denoting params and mutual inds may be bound in some choices of [bterm].
             If so, the vars for the mutual inds come first, and then come the params. *)).


(* ignore coinductives for now *)
Definition simple_mutual_ind (term bterm:Set) 
  : Set := (list (name) (* names of param*) ) *list (simple_one_ind term bterm).

(*
Inductive sigs (A : Set) (P : A -> Prop) : Prop :=
 existss : forall x : A, P x -> sigs A P.
Run TemplateProgram (printTermSq "Top.exists.sigs").

([nNamed "A"; nNamed "P"],
[("sigs",
 mkPiS (0, nNamed "A") (mkSort sSet) None
   (mkPiS (3, nNamed "P")
      (mkPiS (3, nAnon) (vterm (0, nNamed "A")) (Some sSet) (mkSort sProp) None) None
      (mkSort sProp) None) None,
 [("existss",
  bterm [(0, nNamed "sigs"); (3, nNamed "A"); (6, nNamed "P")]
    (mkPiS (9, nNamed "x") (vterm (3, nNamed "A")) (Some sSet)
       (mkPiS (12, nAnon)
          (oterm (CApply 1)
             [bterm [] (vterm (6, nNamed "P")); bterm [] (vterm (9, nNamed "x"))])
          (Some sProp)
          (oterm (CApply 2)
             [bterm [] (vterm (0, nNamed "sigs")); bterm [] (vterm (3, nNamed "A"));
             bterm [] (vterm (6, nNamed "P"))]) (Some sProp)) (Some sProp)))])])
*)


Fixpoint removeNHeadProds (n:nat) (t:term) : term :=
match (n,t) with
| (S n,tProd nm A B) => (removeNHeadProds n B)
| _ => t
end.

Definition parseInd pars (t: one_inductive_entry) : simple_one_ind term term
  := ((mind_entry_typename t), prependProd pars (mind_entry_arity t),
        combine (mind_entry_consnames t) ((mind_entry_lc t))). 
        (* why no prepending to types of constructors? *)

(* Assuming that there are no local assumptions? *)
Definition parseMutuals (t: mutual_inductive_entry) : simple_mutual_ind term term :=
let pars := 
  map
    (fun p => (nNamed (fst p), getLocalEntryType (snd p))) 
    (mind_entry_params t) 
  in ((map fst pars), (map (parseInd pars) (mind_entry_inds t))).


Definition unparseInd (numParams :nat) (t: simple_one_ind term term) : one_inductive_entry :=
{|
  mind_entry_typename := fst (fst t);
  mind_entry_arity := removeNHeadProds  numParams (snd (fst t));
  mind_entry_template := true; (* how to figure it out *)
  mind_entry_consnames := map fst (snd t);
  mind_entry_lc := map snd (snd t);
|}.


Definition extractNameStr (n:name) : ident :=
match n with
| nAnon => ""
| nNamed id => id
end.

Definition unParseMutuals (t: simple_mutual_ind term term) : mutual_inductive_entry :=
let (paramsNames, ones) := t in
let numParams := length paramsNames in (* only used here *)
let params : list (name*term) :=
  match ones with
  | h::_=> 
    let typ := (snd (fst h)) in
    extractNHeadProds numParams typ
  | _ => []
  end in
{|
  mind_entry_record := None;
  mind_entry_finite := Finite; (* Fix? *)
  mind_entry_params := map (fun p => (extractNameStr (fst p), LocalAssum (snd p))) params;
  mind_entry_inds := map (unparseInd numParams) ones;
  mind_entry_polymorphic := false; (* Fix? *)
  mind_entry_private := None;
|}.


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

(*
Lemma fromSquiggleFromSquiggleInv t s:
  getOpid (toSquiggle t) <> Some (CUnknown s)
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
*)

Require Import SquiggleEq.varImplN.
Require Import SquiggleEq.varImplDummyPair.
Require Import SquiggleEq.terms.
Require Import ExtLib.Data.Map.FMapPositive.
Require Import SquiggleEq.list.
Require Import DecidableClass.

Global Instance deqName : Deq name.
Proof using.
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


Notation STerm :=  (@NTerm (N*name) CoqOpid).
Notation SBTerm :=  (@BTerm (N*name) CoqOpid).

Let mkNVar3 (n:(N*name)) := (3*(fst n), snd n)%N.
Let dbToNamed : DTerm -> (@NTerm (N*name) CoqOpid):=
fromDB nAnon mkNVar3 0%N Maps.empty.
Let dbToNamed_bt : DBTerm -> (@BTerm (N*name) CoqOpid):=
fromDB_bt nAnon mkNVar3 0%N Maps.empty.

Let namedToDb :  (@NTerm (N*name) CoqOpid) -> DTerm :=
  toDB snd [].
Let namedToDb_bt : (@BTerm (N*name) CoqOpid)  -> DBTerm :=
  toDB_bt snd [].


Definition toSqNamed (t:term) : @NTerm (N*name) CoqOpid:=
  dbToNamed (toSquiggle t).

Definition fromSqNamed (t:@NTerm (N*name) CoqOpid) : term :=
  fromSquiggle (toDB snd [] t).
  
  
  (* because we would never need to create new inductives, the opposite direction
  wont be necessary *)

Definition toOneIndSq indAndParamNames : (simple_one_ind term term) -> simple_one_ind DTerm DBTerm:=
mapTermSimpleOneInd toSquiggle ((termsDB.bterm indAndParamNames)∘ toSquiggle).

Definition toMutualIndSq  (t: simple_mutual_ind term term) : simple_mutual_ind DTerm DBTerm:=
let (paramNames,ones) := t in
let indNames := map (nNamed∘fst∘fst) ones in
(paramNames, map (toOneIndSq (indNames++paramNames)) ones).

Definition fromOneIndSq : simple_one_ind DTerm DBTerm -> (simple_one_ind term term):=
mapTermSimpleOneInd fromSquiggle (fromSquiggle ∘ (termsDB.get_nt)).

Definition fromMutualIndSq  (t: simple_mutual_ind DTerm DBTerm) 
  : simple_mutual_ind term term:=
let (paramNames,ones) := t in
(paramNames, map fromOneIndSq ones).


Definition parseMutualsSq : mutual_inductive_entry -> simple_mutual_ind STerm 
  (@BTerm (N*name) CoqOpid):=
(mapTermSimpleMutInd dbToNamed dbToNamed_bt) ∘ toMutualIndSq ∘ parseMutuals.

Definition unparseMutualsSq : 
simple_mutual_ind STerm 
  (@BTerm (N*name) CoqOpid)  -> mutual_inductive_entry :=
unParseMutuals ∘ fromMutualIndSq ∘ (mapTermSimpleMutInd namedToDb namedToDb_bt).



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


Definition V:Set := (N*name).

Open Scope N_scope.

Definition vprime (v:V) : V := (1+(fst v), nameMap (fun x => String.append x "₂") (snd v)).
Definition vrel (v:V) : V := (2+(fst v), nameMap (fun x => String.append x "_R") (snd v)).

Notation mkLam x A b :=
  (oterm (CLambda None) [bterm [] A; bterm [x] b]).

Notation mkLamS x A S b :=
  (oterm (CLambda S) [bterm [] A; bterm [x] b]).

Notation mkLetIn x bd typ t :=
  (oterm CLet [bterm [x] t; bterm [] bd; bterm [] typ]).

Notation mkPi x A b :=
  (oterm (CProd None None) [bterm [] A; bterm [x] b]).

Notation mkPiS x A Sa b Sb :=
  (oterm (CProd Sa Sb) [bterm [] A; bterm [x] b]).

Require Import List.

(* because of length, this cannot be used as a pattern *)
Definition mkApp (f: STerm) (args: list STerm) : STerm :=
  match args with
  | [] => f
  | _ =>oterm (CApply (length args)) ((bterm [] f)::(map (bterm []) args))
  end.


Notation mkConst s:=
  (oterm (CConst s) []).

Notation mkConstr i n:=
  (oterm (CConstruct i n) []).

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

Definition mkLamL (lb: list (V*STerm)) (b: STerm) 
  : STerm :=
fold_right (fun p t  => mkLam (fst p) (snd p) t) b lb.


Definition Arg : Set := V*(STerm*(option sort)).

Definition mkLamLS (lb: list Arg) (b: STerm) 
  : STerm :=
fold_right (fun p t  => mkLamS (fst p) (fst (snd p)) (snd (snd p)) t) b lb.

Definition removeSortInfo (a: Arg) : (V*STerm) :=
(fst a, fst (snd a)).

(*
Definition mkLamSL (lb: list Arg) (b: STerm) 
  : STerm :=
fold_right (fun (p:Arg) t  => let (v,Typ) :=p in mkLam v (fst Typ) t) b lb.
*)

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
         
Fixpoint mkAppBetaUnsafe (f: STerm) (args: list STerm) : STerm :=
  match (f, args) with
  | (mkLam x _ b, a::[]) => 
      (apply_bterm_unsafe (bterm [x] b) [a])
  | (mkLam x _ b, a::tl) => 
      mkAppBetaUnsafe (apply_bterm_unsafe (bterm [x] b) [a]) tl
  | _ => mkApp f args
  end.

Fixpoint mkAppBetaSafe (f: STerm) (args: list STerm) : STerm :=
  match (f, args) with
  | (mkLam x _ b, a::[]) => 
      (apply_bterm (bterm [x] b) [a])
  | (mkLam x _ b, a::tl) => 
      mkAppBetaSafe (apply_bterm (bterm [x] b) [a]) tl
  | _ => mkApp f args
  end.

Definition mkAppBeta := mkAppBetaSafe.

(*
Definition mkAppBeta := mkApp.
*)

Definition tprime : STerm -> STerm :=  tvmap vprime.
Definition btprime : SBTerm -> SBTerm :=  tvmap_bterm vprime.



Fixpoint headLamsToPi (tail tlams :STerm) : STerm := 
match tlams with
| mkLamS n A _ b => mkPi n A (headLamsToPi tail b)
| _ => tail
end.

Fixpoint headLamsToPi2 (tlams :STerm) : STerm := 
match tlams with
| mkLamS n A _ b => mkPi n A (headLamsToPi2 b)
| _ => tlams
end.

Fixpoint headPisToLams (tlams :STerm) : STerm := 
match tlams with
| mkPiS n A As B _ => mkLamS n A As (headPisToLams B)
| _ => tlams
end.


Fixpoint getNHeadPis (n:nat)(s: STerm) : STerm * list Arg :=
match (n,s) with
| (S n,  mkPiS nm A Sa B _) => let (t,l):=(getNHeadPis n B) in (t,(nm,(A,Sa))::l)
| _ => (s,[])
end.

Fixpoint getNHeadPisS (n:nat)(s: STerm) :
  (option sort (* the sort of the innermost B *) * STerm) * list Arg :=
match (n,s) with
| (S n,  mkPiS nm A Sa B Sb) =>
  let '(SbInner,t,l):=(getNHeadPisS n B) in
  let retBS :=
      match SbInner with
      | None => Sb
      | Some _ => SbInner
      end in                   
  (retBS, t,(nm,(A,Sa))::l)
| _ => (None,s,[])
end.

Fixpoint getHeadPIs (s: STerm) : STerm * list Arg :=
match s with
| mkPiS nm A Sa B Sb => let (t,l):=(getHeadPIs B) in (t,(nm,(A,Sa))::l)
| _ => (s,[])
end.

Fixpoint getHeadLams (s: STerm) : STerm * list Arg :=
match s with
| mkLamS nm A Sa b => let (t,l):=(getHeadLams b) in (t,(nm,(A,Sa))::l)
| _ => (s,[])
end.

Fixpoint getNHeadLams (n:nat)(s: STerm) : STerm * list Arg :=
match (n,s) with
| (S n, mkLamS nm A Sa b) => let (t,l):=(getNHeadLams n b) in (t,(nm,(A,Sa))::l)
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

(* used to check if a constructor argument is recursive. Because
of strict positiviity, this is solely determined by the tail of the Pi.
So it recurses under Pis. It also returns the arguments of of Pis it recursed
under. This information is useful and returing it duplicate computation in some
callees*)
  
Definition isConstrArgRecursive (tind: inductive) (typ: STerm) : (bool):=
    let (ret, _) := getHeadPIs typ in
    let (ret, _) := flattenApp ret [] in
    (isRecursive tind ret).

Definition numPiArgs (typ: STerm) : nat:=
  let (_, pargs) := getHeadPIs typ in
  length pargs.

Unset Implicit Arguments.

Definition userVar : varClassTypeOf V := exist (fun t : N => decide (t < 3) = true) 0 eq_refl.
Definition primeVar : varClassTypeOf V := exist (fun t : N => decide (t < 3) = true) 1 eq_refl.
Definition relVar : varClassTypeOf V := exist (fun t : N => decide (t < 3) = true) 2 eq_refl.

Require Import Psatz.



Definition extractSort (t:STerm) : (option sort)* STerm :=
match t with
| mkCast t _ (mkSort s) => (Some s, t)
| _ => (None, t)
end.

Fixpoint processFixBodyType (bodies types: list SBTerm)  {struct bodies} :
  (* new types and sort infos. bodies dont change *)
  (list (option sort) *list SBTerm) :=
  match (bodies, types) with
  |(b::bodies, t::types) => 
   let (_, bargs) := getHeadLams (get_nt b) in
   let nargs := length bargs in
   let (fretType, targs) := getNHeadPisS nargs (get_nt t) in
   let (srt, fretType) := fretType in
   (* because unlike the type, the body binds even the function names, the numbers
for corresponding vars in the body would be typically higher *)
   let fretType : STerm  := ssubst_aux fretType
                                       (combine (map fst targs) (map (vterm ∘ fst) bargs)) in
   let fretType : SBTerm := bterm (map fst bargs) fretType in
   let rec := processFixBodyType bodies types in
   (srt::(fst rec), fretType::(snd rec))
  | _ => ([],[])
  end.


Definition  mrs := (map removeSortInfo).
Definition argType (p:Arg) :STerm := fst (snd p).
Definition argVar (p:Arg) :V := fst p.


Fixpoint undoProcessFixBodyTypeAux (bodies types: list SBTerm)  {struct bodies} :
  (* new types and sort infos. bodies dont change *)
  (list SBTerm) :=
  match (bodies, types) with
  |(b::bodies, t::types) => 
   let nargs := num_bvars t in
   let (_,lambArgs) := getNHeadLams nargs (get_nt b) in
   (bterm [] (mkPiL (map removeSortInfo lambArgs) (get_nt t)))
     ::(undoProcessFixBodyTypeAux bodies types)
  | _ => []
  end.
   
Definition undoProcessFixBodyType (len:nat) (lb: list SBTerm) : list SBTerm :=
  let bodies := firstn len lb in
  let types := skipn len lb in
  bodies++(undoProcessFixBodyTypeAux bodies types).

(* processTypeInfo removes Pis from fix's type. this puts it back *)
Definition getProcessedFixFullType (p:fixDef V STerm) :STerm :=
  let (_, lamArgs) := getHeadLams (fbody p) in
  mkPiL (mrs lamArgs) (fst (ftype p)).

Fixpoint processTypeInfo (t:STerm) : STerm :=
match t with
| mkLam x A b => 
  let (Sa,A) := extractSort (processTypeInfo A) in
    mkLamS x A Sa (processTypeInfo b)
| mkPi x A B => 
  let (Sa,A) := extractSort (processTypeInfo A) in
  let (Sb,B) := extractSort (processTypeInfo B) in
    mkPiS x A Sa B Sb
| oterm (CCase i ln _ (* this would be None *)) ((bterm [] retTyp):: (bterm [] disc)::lb) =>
  let lb := map (btMapNt processTypeInfo) lb in
  let disc := processTypeInfo disc in
  let retTyp := processTypeInfo retTyp in
  let (retTypLeaf, retTypArgs) := getHeadLams retTyp in
  let (rsort, retTypLeaf) := extractSort retTypLeaf in
  let retTyp := mkLamLS retTypArgs retTypLeaf in
  let o := (CCase i ln rsort) in
  match disc with
  | mkCast disc _ discType =>
    (* TODO : replace None by examining the caset set by template coq *)
    oterm o ((bterm [] retTyp):: (bterm [] disc):: (bterm [] discType)::lb)
          
  | _ => oterm o ((bterm [] retTyp):: (bterm [] disc)::lb)
  end
(* If it is a fix, get all the types, and put all the vars in PIs as a BTerm.
This is important because while doing structural recursion, as in translateFix,
we can directly get the translation of the return type.
Earlier, this was extracted from the translation from the Pi Type, which can be complex,
especially if the goodness combinators where used.
Translating after extracting head Pis can confuse the typechecker.

Also do the substitution so that the bvars are the same as that in the lambda.
What happens on the way back?


case 1) processTypeinfo was done and no further processing was done: 
fromSquiggle could notice those BTerms on types on the way back. 
If there are, it would extract that many lam args from the body and put them in front of
the type as Pis. Because the names are consistent, no changing of DB indices in the type should
be needed.

case 0) processTypeinfo not done: the above process would be id.

case 2) further processing was done after processTypeinfo: need to enforce the invariant that
the type mentions only the vars in the body's lambda, in a consistent way.
If not, one can make the Pis themselves and set bterm as [].
Remember to put back either bterms or Pis if bterm is removed after processing
 *)

| oterm (CFix len rargs _ index) lbs =>
  let lbs :=  (map (btMapNt processTypeInfo) lbs) in
  let bodies := firstn len lbs in
  let types := skipn len lbs in
  let (sorts, types) := processFixBodyType bodies types in
  oterm (CFix len rargs sorts index) (bodies++types)
| oterm o lbt => oterm o (map (btMapNt processTypeInfo) lbt)
| vterm v => vterm v
end.



Definition  toSqNamedProc := processTypeInfo ∘ toSqNamed.

Definition parseMutualsSqProc := 
(mapTermSimpleMutInd processTypeInfo (btMapNt processTypeInfo)) ∘ parseMutualsSq.
     
Definition printTermSq (name  : ident): TemplateMonad unit :=
  x <- tmQuote name true ;;
  match x with
  Some (inl t) => 
    tr <- @tmReduce Ast.all _ (toSqNamedProc t) ;;
    tmPrint tr 
  | Some (inr t) =>
    tr <- @tmReduce Ast.all _ (parseMutualsSqProc t) ;;
    tmPrint tr 
  | _ => ret tt
  end.

Definition checkTermSq (name  : ident) (b:bool): TemplateMonad unit :=
  x <- tmQuote name true ;;
  match x with
  Some (inl t) => 
    tr <- @tmReduce Ast.all _ (toSqNamedProc t) ;;
    tmPrint tr ;;
    trb <- @tmReduce Ast.all _ (fromSqNamed tr) ;;
    trEqb <- @tmReduce Ast.all _ (mkEqTerm t trb) ;;
    tmPrint trEqb ;;
    if b then (tmMkDefinition true (String.append name "__Req") trEqb)
      else (ret tt) 
  | _ => ret tt
  end.



(* generalize mutual_inductive_entry to be use STerm *)
Definition tmQuoteSq id b : TemplateMonad (option (STerm + simple_mutual_ind STerm SBTerm)) :=
  t <- tmQuote id b;;
  ret
  (match t with
  | Some (inl t) => Some (inl (toSqNamedProc t))
  | Some (inr t) => Some (inr (parseMutualsSqProc t))
  | None => None
  end).

Definition tmReducePrint {T:Set} (t: T) : TemplateMonad () :=
  (trr <- tmReduce Ast.all t;; tmPrint trr).



Definition tmMkDefinitionSq id (st : STerm) : TemplateMonad () :=
  tmMkDefinition true id (fromSqNamed st).

Definition tmMkIndSq (st : simple_mutual_ind STerm SBTerm) : TemplateMonad () :=
  tmMkInductive (unparseMutualsSq st). 
(*  tr <- tmReduce Ast.all ((unparseMutualsSq st));;
  tmPrint tr.*)

Definition mapNames (f:ident -> ident) (st : simple_mutual_ind STerm SBTerm) :
  simple_mutual_ind STerm SBTerm
  :=
    let (np, ones) := st in
    (np, map (fun p => (f (fst (fst p)) , snd (fst p) ,
                     map (fun c => (f (fst c), snd c))(snd p))) ones).

Definition tmDuplicateSq (id:ident) (b:bool) : TemplateMonad () :=
  t <- tmQuote id b;;
  (match t with
  | Some (inl t) => tmMkDefinitionSq (append id "_dupDefn") (toSqNamedProc t)
  | Some (inr t) => 
    let parse := (parseMutualsSqProc t) in
    let unparse := (unparseMutualsSq (mapNames (fun s => append s "_dupInd") parse)) in
    _ <- tmPrint unparse;;
    tmMkInductive unparse
  | None => ret tt
  end).

(*
Run TemplateProgram (tmDuplicateSq "Coq.Init.Datatypes.nat" true).
Inductive nat_dupInd : Set :=  O_dupInd : nat_dupInd | S_dupInd : nat_dupInd -> nat_dupInd
Print nat_dupInd.
*)

Require Import SquiggleEq.ExtLibMisc.


Definition ids : forall A : Set, A -> A := fun (A : Set) (x : A) => x.
Definition idsT  := forall A : Set, A -> A.

Run TemplateProgram (printTermSq "ids").
(*
(mkLamS (0, nNamed "A") (mkSort sSet) None
   (mkLamS (3, nNamed "x") (vterm (0, nNamed "A")) (Some sSet) (vterm (3, nNamed "x"))))
*)

Run TemplateProgram (printTerm "Nat.add").
Run TemplateProgram (printTermSq "Nat.add").

(*
because of cast mismatches, this wont work if template-coq puts casts
Run TemplateProgram (checkTermSq "ids" false).
Run TemplateProgram (checkTermSq "Nat.add" true).
Run TemplateProgram (checkTermSq "idsT" true).
*)

Definition isPropOrSet (s:sort) : bool :=
match s with
| sSet => true
| sProp => true
| sType _ => false
end.

Definition freshUserVars avoid sugg : list V := 
  let cl :(decSubtype (fun n : N => (n < 3)%N)) := userVar in
    (@freshVars V (decSubtype (fun n : N => (n < 3)%N)) _ 
      (length sugg) (Some cl) avoid (map (fun s => (0,nNamed s)) sugg)).


Definition freshUserVar avoid sugg : V := 
nth 0 (freshUserVars avoid [sugg]) (0,nNamed sugg).

Definition primeArgsOld  (p : (V * STerm)) : (V * STerm) :=
(vprime (fst p), tvmap vprime (snd p)).

Definition primeArg  (p : Arg) : (V * STerm) :=
let (v, Typ) := p in
(vprime v, tvmap vprime (fst Typ)).

(* vars are names along with numbers. *)
Definition getParamAsVars (numParams:nat)
  (l:list (simple_one_ind STerm SBTerm)) : list Arg:=
match l with
| smi::_ =>
  let (nmT, cs) := smi in
  let (nm, t) := nmT in
  let (srt, bs) := getHeadPIs t in
  firstn numParams bs
| _ => []
end.

Require Import SquiggleEq.AssociationList.
Fixpoint substConstants (ids: AssocList ident STerm) (t :STerm) : STerm := 
match t  with
| mkConst s =>
    match ALFind ids s with
    | Some v => v
    | None => t
    end
| vterm v => vterm v
| oterm o lbt => oterm o (map (btMapNt (substConstants ids)) lbt)
end.

Definition dummyInd : simple_one_ind STerm SBTerm :=
  ("", oterm (CUnknown "dummyInd") [], []).

Definition sigt_rec_ref := "sigtPolyRect".
Definition sigt_ref := "Coq.Init.Specif.sigT".

Definition and_ref := "Coq.Init.Logic.and".
Definition mkAndSq := (mkInd and_ref 0).
Definition conjSq : STerm :=  mkConstr (mkInd and_ref 0) 0.
Definition proj1_ref := "Coq.Init.Logic.proj1".
Definition proj2_ref := "Coq.Init.Logic.proj2".


Definition projT1_ref := "Coq.Init.Specif.projT1".
Definition projT2_ref := "Coq.Init.Specif.projT2".

Definition sigtInd : inductive := (mkInd sigt_ref 0).
Definition sigtMatchOpid : CoqOpid :=
  (CCase (sigtInd, 2) [0])%nat None.

Definition falseInd : inductive := mkInd "Coq.Init.Logic.False" 0.
Definition FalseMatchOpid : CoqOpid :=
  (CCase (falseInd, 0) [])%nat None.

Run TemplateProgram (printTermSq "eq_rect").

Definition eqMatchOpid : CoqOpid := (CCase (mkInd "Coq.Init.Logic.eq" 0, 2%nat) [0%nat] None).


Definition False_rectt@{i} (P:Type@{i}) (f:False) : P:= 
match f with end.
Eval compute in (fromSqNamed (mkConstApp "False_rect" 
  [mkConstInd (mkInd "Coq.Init.Datatypes.nat" 0); mkConst "F"])).

Fixpoint sigTToExistT2 (witnesses : list STerm) (last t: STerm)
  {struct witnesses} : STerm :=
match (witnesses,t) with
| (hw::tlw, oterm (CApply _)
(* fix : no strings in patterns. use decide equality if really needed.
Probably just _ will work for the current uses *)
 ((bterm [] (mkConstInd (mkInd _ 0)))::
   (bterm [] A)::(bterm [] (mkLamS a _(*A*) _ b))::[]))
   => mkApp (mkConstr sigtInd 0) 
      [A, (mkLam a A b), hw, sigTToExistT2 tlw last (ssubst_aux b [(a,hw)])]
| _ => last
end.

Definition TrueIConstr : STerm := (mkConstr (mkInd "Coq.Init.Logic.True" 0) 0).
Definition fixCache :Set := (nat -> CoqOpid) * (list SBTerm).



Fixpoint sigTToExistT (last t: STerm) : STerm :=
match t with
| oterm (CApply _)
(* fix : no strings in patterns. use decide equality if really needed.
Probably just _ will work for the current uses *)
 ((bterm [] (mkConstInd (mkInd _ 0)))::
   (bterm [] A)::(bterm [] (mkLamS a _(*A*) _ b))::[])
   => mkApp (mkConstr sigtInd 0) 
      [A, (mkLam a A b), vterm a, sigTToExistT last b]
| _ => last
end.

Fixpoint sigTToExistTRect (existt ret sigt: STerm) (vars: list V): STerm :=
match sigt with
| oterm (CApply _)
 ((bterm [] (mkConstInd (mkInd _ 0)))::
   (bterm [] A)::(bterm [] (mkLamS a _(*A*) _ b))::[])
   => 
   let B := (mkLam a A b) in
   let proj1 := (mkConstApp "Coq.Init.Specif.projT1" [A, B, existt]) in
   let proj2 := (mkConstApp "Coq.Init.Specif.projT2" [A, B, existt]) in
   mkLetIn a proj1 A (sigTToExistTRect proj2 ret b (snoc vars a))
| _ => mkApp ret (map vterm vars)
end.

(*
Axiom F: False.

Run TemplateProgram (tmMkDefinitionSq "fff" (mkConstApp "False_rect" 
  [mkConstInd (mkInd "Coq.Init.Datatypes.nat" 0); mkConst "F"])).
*)

Definition filter_mod3 {A:Type }(l: list A)  (rem:N) : (list A) 
:=
filter_mod l 3 rem.


Definition separate_Rs {A:Type }(l: list A) : (list A (* _Rs *) * list A (* the rest *)) 
:=
let ls := combine (list.seq N.succ 0 (length l))%N l in
let (l,r) := partition (fun p => decide ((fst p) mod 3 = 2)) ls in
(map snd l, map snd r).

Definition eqTypeInd :inductive := (mkInd "Coq.Init.Logic.eq" 0).

Definition mkEqSq (typ t1 t2: STerm) :=
  (mkIndApp eqTypeInd [typ,t1,t2]).

Definition mkEqReflSq (typ t: STerm) :=
  mkApp  (mkConstr eqTypeInd 0) [typ,t].


Definition dummyVar : V := (0, nAnon).

Definition packageArgsTypesAsSigt (la: list (V*STerm)) : STerm :=
let defHead := (dummyVar,boolToProp true) in
let (hd, tail) := headTail defHead la in
mkSigL tail (snd hd).

Record defSq : Set := {nameSq : ident; bodySq : STerm}.

Definition defIndSq : Set := defSq + (simple_mutual_ind STerm SBTerm).

Definition tmMkDefinitionLSq (ids: list defSq) : TemplateMonad () :=
  _ <- 
  ExtLibMisc.flatten
    (map (fun (p:defSq) => tmMkDefinitionSq (nameSq p) (bodySq p)) ids);; 
  ret ().

Definition tmMkDefIndSq (t : defIndSq) : TemplateMonad () :=
  match t with
  | inl p => tmMkDefinitionSq (nameSq p) (bodySq p)
  | inr i => tmMkIndSq i
  end.

(*
Definition flatten {m} {A: Type} `{Monad m} (lm:list (m A)) : m (list A) :=
fold_right (fun a l => 
              a <- a;;
                l <- l;; 
                      ret (a :: l))
          (ret []) 
          lm.
Check (eq_refl : @flatten = @ExtLibMisc.flatten).
 *)

Definition tmMkDefIndLSq (ids: list defIndSq) : TemplateMonad () :=
  _ <- 
  ExtLibMisc.flatten (map tmMkDefIndSq ids);;  ret ().


Module TranslatedArg.
Record T (A:Set) : Set :=
  { arg: A; argPrime: A; argRel:A }.

Arguments arg {A} t.
Arguments argPrime {A} t.
Arguments argRel {A} t.
Fixpoint  unMerge3way {A:Set} (la: list A): list (T A) :=
  match la with
  | arg::argp::argr::tl => {|arg:= arg; argPrime:=argp; argRel := argr |}::(unMerge3way tl)
  | _ => []
  end.

Fixpoint  combineLists {A:Set} (la lap lar: list A): list (T A) :=
  match la, lap, lar with
  | arg::la, argp::lap, argr::lar =>
    {|arg:= arg; argPrime:=argp; argRel := argr |}::(combineLists la lap lar)
  | _,_,_ => []
  end.

Definition asList {A:Set} (la: (T A)): list A :=
  [arg la; argPrime la; argRel la].

Definition   merge3way {A:Set} (la: list (T A)): list A :=
  flat_map asList la.


End TranslatedArg.

Definition merge3Lists {A:Set} (la lap lar: list A): list A :=
  TranslatedArg.merge3way (TranslatedArg.combineLists la lap lar).

Definition falseRectSq (rType proofFalse : STerm):=
  let v := freshUserVar (free_vars rType) "pfalse" in
  oterm FalseMatchOpid (map (bterm [])
                            [mkLam v (mkConstInd falseInd) rType; proofFalse]).

(* this caues universe issues *)
Definition falseRectSqold (rType proofFalse : STerm):=
  mkConstApp "False_rectt" [rType;proofFalse] .


Record EqType (S:Set): Set := {
    eqType : S;
    eqLHS : S;
    eqRHS : S  
  }.

Arguments eqType {S} e.
Arguments eqLHS {S} e.
Arguments eqRHS {S} e.

Definition map_EqType {A B:Set} (f: A->B) (eq: EqType A) : EqType B := {|
    eqType := f (eqType eq);
    eqLHS := f (eqLHS eq);
    eqRHS := f (eqRHS eq)
  |}.

Definition getEqTypeSq (eq: EqType STerm) : STerm :=
  (mkEqSq (eqType eq) (eqLHS eq) (eqRHS eq)).

Definition getEqRefl (eq: EqType STerm) : STerm :=
  mkEqReflSq (eqType eq) (eqLHS eq).

Print transport.
(* to avoid universe issues, unfold the definition of transport*)
Definition mkTransportOld (P:STerm) (eq: EqType STerm) (peq: STerm) (pl: STerm) : STerm :=
  mkConstApp "SquiggleEq.UsefulTypes.transport" [
               eqType eq;
                 eqLHS eq;
                 eqRHS eq;
                 P;
                 peq;
                 pl
             ].

Definition mkTransport (P:STerm) (eq: EqType STerm) (peq: STerm) (pl: STerm) : STerm :=
  let freshVars : list V:= freshUserVars (free_vars P) ["trEqr";"trEqp"] in
  let vtrEqr := nth 0 freshVars dummyVar in
  let vtrEqp := nth 1 freshVars dummyVar in
  let retTyp := mkLamL [(vtrEqr, eqType eq);
                          (vtrEqp, (mkEqSq (eqType eq) (eqLHS eq) (vterm vtrEqr)))]
                       (mkApp P [vterm vtrEqr]) in
  oterm eqMatchOpid (map (bterm []) [retTyp; peq; pl]).

Definition mkTransportV (v:V) (P:STerm (* can mention v *))
           (eq: EqType STerm)
           (peq: STerm)
           (pl: STerm) : STerm :=
  let freshVars : list V:= freshUserVars (free_vars P) ["trEqp"] in
  let vtrEqp := nth 0 freshVars dummyVar in
  let retTyp := mkLamL [(v, eqType eq);
                          (vtrEqp,
                           (mkEqSq (eqType eq) (eqLHS eq) (vterm v)))]
                        P in
  oterm eqMatchOpid (map (bterm []) [retTyp; peq; pl]).

Definition mkFiatTransport (P:STerm) (eq: EqType STerm) (pl: STerm) : STerm :=
  mkTransport P eq (mkConstApp "fiat" [getEqTypeSq eq]) pl.

Definition extractInd (s:STerm) : inductive :=
  match s with
  | (oterm (CInd s) []) => s
  | _ => mkInd "NoIndFound" 0
  end.

Definition vAllRelated (v: V) : list V :=
  [v; vprime v; vrel v].


(* this ignores variable binding/capture/alpha equality issues. variables are just
another parts of AST for this function *)
Require Import SquiggleEq.terms2.

Fixpoint replaceOccurrences {NVar Opid: Type} `{Deq NVar} `{Deq Opid}
         (ts td t: @NTerm NVar Opid) {struct t}: @NTerm NVar Opid :=
  if (NTerm_beq t ts) then td else
  match t with
  | vterm v => t
  | oterm op bts => oterm op (map (replaceOccurrences_bt ts td) bts)
  end
with replaceOccurrences_bt {NVar Opid: Type} `{Deq NVar} `{Deq Opid}
                         (ts td : @NTerm NVar Opid) (t : @BTerm NVar Opid) 
  :@BTerm NVar Opid :=
  match t with
  | bterm lv t => bterm lv (replaceOccurrences ts td t)
  end.


Definition flattenHeadApp (f: STerm)  : STerm :=
  let (f, args ) := flattenApp f [] in
  mkApp f args.


  Definition mkUnknown (s:ident) : STerm := oterm (CUnknown s) [].

  Definition totalPiHalfGood_ref : ident  :=  "ReflParam.PiTypeR.totalPiHalfGood".
  Definition totalPiHalfGood21_ref : ident  :=  "ReflParam.PiTypeR.totalPiHalfGood21".
  Definition oneOnePiHalfGood_ref : ident  :=  "ReflParam.PiTypeR.onePiHalfGood".
  Definition oneOnePiHalfGood21_ref : ident  :=  "ReflParam.PiTypeR.onePiHalfGood21".
  Definition RPiS_ref : ident  :=  "ReflParam.common.R_PiS".
  
  Definition mkRPiS (A1 A2 AR B1 B2 BR: STerm) :=
    mkConstApp RPiS_ref [A1;A2;AR;B1;B2;BR].


  Require Import ExtLib.Data.String.

  (* adding a non-numeric
suffix is useful so that we don't confuse these vars with the internal renaming that
 coq does by adding numerical suffices *)
Definition varName (prefix  suffix : ident) (n:nat) :=
  String.append (String.append prefix (nat2string10 n)) suffix.

Definition varNames (prefix  suffix : ident) (len:nat) :=
  map (varName prefix suffix) (List.seq 0 len).

(* this assumes that the vars (map fst l) are NOT free in (map snd l) *)
Definition renameArgs (avoid : list V) (l:list (V*STerm)): list V :=
  let origVars := (map fst l) in
  let vars : list V :=
      freshUserVars (avoid++origVars) (varNames "i" "irr" (length l)) in
  let vars := map vrel vars in vars (* skip when geneeralizing to arbit indices *).
 
Definition proofIrrel_ref :ident := "Coq.Logic.ProofIrrelevance.proof_irrelevance".

Definition proofIrrelEqProofSq (e: EqType STerm) : STerm :=
  mkConstApp proofIrrel_ref [(eqType e); (eqLHS e); (eqRHS e)].


Definition injpair2_ref:=
(*  "EqdepTheory.inj_pair2". *)
 "Coq.Logic.ProofIrrelevance.ProofIrrelevanceTheory.EqdepTheory.inj_pair2".

Definition mkSigTRect  A B  sigRetTyp sigRet:=
mkConstApp sigt_rec_ref [A;B; sigRetTyp; sigRet].

Definition mkSigTRectDirect  A B  sigRetTyp sigRet:=
  (* compute this only once, outside? *)
  let v := freshUserVar (flat_map free_vars [A;B;sigRetTyp;sigRet]) "sigrectv" in
  mkLam v (mkIndApp sigtInd [A;B]) 
        (oterm sigtMatchOpid (map (bterm []) [sigRetTyp; vterm v; sigRet])).


Definition fstVterms : list Arg -> list STerm :=  map (vterm ∘ fst).

