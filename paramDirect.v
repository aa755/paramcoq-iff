

(* coqide -top ReflParam.paramDirect paramDirect.v *)

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
Require Import templateCoqMisc.
Require Import Template.Template.
Require Import Template.Ast.
Require Import NArith.
Require Import Coq.Program.Program.
Open Scope program_scope.
Require Import Coq.Init.Nat.
Require Import SquiggleEq.varInterface.
Require Import SquiggleEq.varImplDummyPair.

Require Import ExtLib.Data.String.
Definition constTransName (n:ident) : ident :=
  String.append (mapDots "_" n) "_pmtcty_RR".

Definition indTransName (n:inductive) : ident :=
match n with
| mkInd s n => String.append (constTransName s) (nat2string10 n)
end.

Definition constrTransName (n:inductive) (nc: nat) : ident :=
String.append (indTransName n) (String.append "_constr_" (nat2string10 nc)).

Definition constrTransTotName (n:inductive) (nc: nat) : ident :=
String.append (constrTransName n nc) "_tot".

Definition constrInvName (cn:ident)  : ident :=
String.append cn "_inv".

(* not iso *)
Definition constrInvFullName (n:inductive) (nc: nat)  : ident :=
constrInvName (constrTransName n nc).


(*
Definition sigtPolyRect@{i j} (A : Type@{i}) (P : A -> Type@{i}) (P0 : {x : A & P x} -> Type@{j})
  (f : forall (x : A) (p : P x), P0 (existT P x p)) (s : {x : A & P x}) :=
             let (x, x0) as s0 return (P0 s0) := s in f x x0.
*)                                                        



Module IndTrans.

Record ConstructorInfo : Set := {
  index : nat; (* index of this constructor *)
  args_R : list (TranslatedArg.T Arg);
(*  argsPrimes : list Arg;
  args_RR : list Arg; *)
  retTyp : STerm; 
(*  retTypIndices : list STerm; *)
  retTypIndices_R : list (TranslatedArg.T STerm);
  (* retTypIndicesPacket : STerm  packaged as a sigma *)
}.

  Record IndInfo :=
  {
    numParams : nat;
    tind : inductive;
    constrInfo_R :  list ConstructorInfo;
    indArgs_R : list (TranslatedArg.T Arg);
    retSort : STerm;
    retSort_R : STerm;
    castedArgs_R : list STerm; (* these include indices as well, althoug only params are casted *)
  }.

  

  Definition indAppR (i: IndInfo) : STerm :=
    mkConstApp (indTransName (tind i)) (castedArgs_R i).

  Definition indApp (i: IndInfo) : STerm :=
    mkIndApp (tind i) (map (vterm ∘ fst ∘ TranslatedArg.arg) (indArgs_R i)).


  Definition argsLen (ci: IndTrans.ConstructorInfo) : nat := 
    (length (args_R ci)).

  Definition matchOpid (i: IndInfo) : CoqOpid :=
      let cargsLens : list nat := (map IndTrans.argsLen  (constrInfo_R i)) in
      (CCase ((tind i), (numParams i)) cargsLens) None.

  Definition indIndices_R (i: IndInfo) : list (TranslatedArg.T Arg) :=
    skipn (numParams i) (indArgs_R i).

  Definition indParams_R (i: IndInfo) : list (TranslatedArg.T Arg) :=
    firstn (numParams i) (indArgs_R i).

    Definition castedParams_R (i: IndInfo) : list STerm :=
    firstn (3*(numParams i)) ( castedArgs_R i).

  (* because these are not translated, it doesn't matter whether we pick this or
    the casted params*)
  Definition indParams (i: IndInfo) : list (Arg) :=
    map TranslatedArg.arg (indParams_R i).


      (* because these are not translated, it doesn't matter whether we pick this or
    the casted params*)
  Definition indIndices (i: IndInfo) : list (Arg) :=
    map TranslatedArg.arg (indIndices_R i).

    Definition sigIndApp (i: IndInfo) : STerm :=
    let indIndices := mrs (indIndices i) in
    mkSigL indIndices (indApp i).

Definition args (ci: IndTrans.ConstructorInfo) : list Arg := 
  map TranslatedArg.arg  (args_R ci).

Definition thisConstructor (i: IndInfo) (ci: ConstructorInfo) : STerm :=
  let params := indParams i in
  let c11 := mkApp (mkConstr (tind i) (index ci)) (map (vterm∘fst) params) in
  mkApp c11 (map (vterm∘fst∘TranslatedArg.arg) (args_R ci)).

Definition constrInvApp (i: IndInfo) (ci: ConstructorInfo) :
  (STerm (*need to append indIndices_RR with cretIndices1/2 substed in. most
     of the constructions of matches already compute this *)
   ):=
  let cInvName := constrInvFullName (tind i) (index ci) in (* not iso *)
  let cargsAndPrimes := flat_map (fun p =>
                                    [TranslatedArg.arg p;
                                       TranslatedArg.argPrime p]) (args_R ci) in
  let cargsRR := map TranslatedArg.argRel (args_R ci) in
  (mkConstApp cInvName ((castedParams_R i)++(map (vterm ∘ fst) cargsAndPrimes))
   ).

Definition argPrimes (ci: IndTrans.ConstructorInfo) : list Arg:= 
map TranslatedArg.argPrime  (args_R ci).

Definition argRR (ci: IndTrans.ConstructorInfo) : list Arg := 
map TranslatedArg.argRel  (args_R ci).

Definition indices (ci: IndTrans.ConstructorInfo) : list STerm := 
map TranslatedArg.arg  (retTypIndices_R ci).

Definition indicesPrimes (ci: IndTrans.ConstructorInfo) : list STerm := 
map TranslatedArg.argPrime (retTypIndices_R ci).

Definition indicesRR (ci: IndTrans.ConstructorInfo) : list STerm := 
map TranslatedArg.argRel  (retTypIndices_R ci).

Definition constrBvars (c: ConstructorInfo) : list V :=
  map fst (args c).

  Definition indBVars (i: IndInfo) : list V :=
    let allConsrVars : list V:= flat_map constrBvars (constrInfo_R i) in
    let indVars := map (fst ∘ TranslatedArg.arg) (indArgs_R i) in
    allConsrVars++indVars.
    

End IndTrans.


(* can be Prop for set *)
Definition translateSort (s:sort) : sort := 
match s with
| sType _ => s
| _ => sProp
end.
(*
Definition mkTyRel (T1 T2 sort: term) : term :=
  T1 ↪ T2 ↪ sort.
Definition projTyRel (T1 T2 T_R: term) : term := T_R.
*)

Require Import Trecord.
Require Import common.



(* inline it? *)
Definition mkTyRel (T1 T2 sort: STerm) : STerm :=
  mkConstApp "ReflParam.Trecord.BestRel" [T1; T2].

(* inline it? *)
Definition projTyRel (T1 T2 T_R: STerm) : STerm := 
mkConstApp "ReflParam.Trecord.BestR" [T1; T2; T_R].


(*
Fixpoint hasSortSetOrProp (t:STerm) : bool :=
match t with
| mkCast t _ (mkSort sSet) => true
| mkCast t _ (mkSort sProp) => true
(* this should not be needed. Fix template-coq cast branch to insert casts
when params are converted to lambdas *)
| mkPi x A B => andb (hasSortSetOrProp A) (hasSortSetOrProp B) (* ignoring impred prop *)
(* TODO: ensure that App and inductives is casted in Coq *)
(* Todo : handle Fix (look at the types in the body*)
| _ => false
end.

*)


Require Import PiTypeR.

(*
Using this can cause universe inconsistencies. Using its quote is like using
a notation and does not add universe constraints
Definition PiABType@{i it j jt}
  (A1 A2 :Type@{i}) (A_R: A1 -> A2 -> Type@{it}) 
  (B1: A1 -> Type@{j}) 
  (B2: A2 -> Type@{j})
  (B_R: forall a1 a2,  A_R a1 a2 ->  (B1 a1) -> (B2 a2) -> Type@{jt})
  := (fun (f1 : forall a : A1, B1 a) (f2 : forall a : A2, B2 a) =>
forall (a1 : A1) (a2 : A2) (p : A_R a1 a2), B_R a1 a2 p (f1 a1) (f2 a2)).
*)



Definition PiABType (Asp Bsp:bool) (a1:V)
  (A1 A2 A_R B1 B2 B_R : STerm) : STerm :=
let allVars := flat_map all_vars ([A1; A2; B1; B2; A_R; B_R]) in
let f1 : V := freshUserVar (a1::allVars) "ff" in
let a2 := vprime a1 in
let ar := vrel a1 in
let f2 := vprime f1 in
let A_R := if Asp then projTyRel A1 A2 A_R else A_R in
let B_R := mkAppBetaUnsafe B_R [vterm a1; vterm a2; vterm ar] in
let B_R := if Bsp then projTyRel (mkAppBeta B1 [vterm a1]) (mkAppBeta B2 [vterm a2])
     B_R else B_R in
mkLamL [(f1, mkPi a1 A1 (mkAppBeta B1 [vterm a1])) ; (f2, mkPi a2 A2 (mkAppBeta B2 [vterm a2]))]
       (mkPiL [(a1,A1); (a2,A2) ; (ar, mkAppBeta A_R [vterm a1; vterm a2])]
(* dont change the app below to mkAppBeta -- that would complicate the function 
remove removePiRHeadArg, which
   is to get B_R from the translation of [forall a, B]. Because of the termination check issues,
   we can often not directly translate B, as the recursive function to extract [B] confuses the termination checker *)
   (mkApp B_R [mkApp (vterm f1) [vterm a1]; mkApp (vterm f2) [vterm a2]])).

(* to be used when flattening must not be done *)
Definition appExtract (t:STerm) : (STerm * list STerm):=
  match t with
  | vterm _ => (t,[])
  | oterm (CApply _) (b::lb) => (get_nt b, map get_nt lb)
  | oterm _ _ => (t,[])
   end.
(* not in use anymore *)
Definition removePiRHeadArg (t:STerm) : STerm :=
  let (t,_) := getNHeadLams 2 t in
  let (t,_) := (getNHeadPis 3 t) in
  fst (appExtract t).

(*
Definition getPiConst (Asp Bsp : bool) := 
match (Asp, Bsp) with
(* true means lower universe (sp stands for Set or Prop) *)
| (false, false) => "PiABType" (* not used *)
| (false, true) => "PiATypeBSet" (* not used *)
| (true, false) => "PiASetBType" (* not used *)
| (true, true) => "ReflParam.PiTypeR.PiGoodSet"
end.
Run TemplateProgram (printTermSq "PiABType").
 *)


Definition getPiConst (Bsort : sort) := 
match Bsort with
| sSet => "ReflParam.PiTypeR.PiGoodSet"
| sProp => "ReflParam.PiTypeR.PiGoodProp"
| _ => "errrorrConst"
end.

Definition getPiGoodnessLevel (Bsort : sort) : ident := 
match Bsort with
| sSet => "ReflParam.Trecord.allProps"
| sProp => "ReflParam.Trecord.onlyTotal"
| _ => "errrorrGoodLvl"
end.

Definition getPiDownCastOp (Bsort : sort) : STerm  -> STerm := 
match Bsort with
| sSet => id
| sProp => fun t => mkConstApp "Trecord.cast_Good_onlyTotal" [t] 
| _ => id
end.

(* TODO: simplify this. just return the final STerm. the first two elems of the pair are
not needed anymore *)
Definition mkPiR (isoMode: bool) (needToProjectRel : option sort -> bool)
           (Asp Bsp : option sort) :
  ((STerm->STerm) * option ident *(forall (a: V) (A1 A2 A_R  B1 B2 B_R: STerm), STerm)) :=
  let PiABType := PiABType (needToProjectRel Asp) (needToProjectRel Bsp) in
  if (negb isoMode) then (id, None, PiABType) else
match (Asp, Bsp) with
(*if RHS is Prop, then the result is in Prop, and the abstraction theorem would
need goodness which this doesn't provide. If A:=Prop, this works. Try
to characterize such cases.

Come up with a concrete couterexample.
(Regardless, because if A is of a higher univ, we don't have goodness for it
and then we have no combinator we can use)
T:Type
A:=T
B:= fun a:T => A

  *)
| (None, _) => (id, None ,PiABType)
| (_, None) => (id, None ,PiABType)
| (Some _, Some Bsort) =>
  (getPiDownCastOp Bsort, Some (getPiGoodnessLevel Bsort)
   ,fun _ (A1 A2 A_R  B1 B2 B_R: STerm) =>mkApp (mkConst (getPiConst Bsort))
                                             [A1; A2; A_R ; B1; B2; B_R])
end.


Definition appArgTranslate translate (b:@BTerm (N*name) CoqOpid) : list STerm :=
  let t := get_nt b in
  let t2 := tvmap vprime t in
  let tR := translate t in
  [t; t2; tR].

Definition mkTyRelOld T1 T2 TS := 
  let v1 := (6, nAnon) in (* safe to use 0,3 ? *)
  let v2 := (9, nAnon) in
  mkPiL [(v1,T1); (v2,T2)] TS. 



(* 
Remove casts around tind.
TODO: additional work needed for nested inductives.
Fixpoint removeCastsAroundInd (tind: inductive) (t:STerm) : (STerm) :=
match t with
| mkPi x A B 
  => mkPi x A (removeCastsAroundInd tind B) (* strict positivity => tind cannot appear in A *)
| mkCast tc _ (mkSort sProp)
| mkCast tc _ (mkSort sSet) => 
    let (f, args) := flattenApp tc [] in
    match f with
    | mkConstInd tin  => if (decide (getIndName tind = getIndName tin)) then tc else t
    | mkPi x A B => tc (* must ensure that this argument is recursive *)
    | _ => t
    end
| t => t
end.
*)


(* while translating an inductive, we don't yet have its goodness. So, we remove the flags
that signal the need for creation and projection of goodness props.
The callee must ensure that this argument is recursive -- the last item in the Pi type is the inductive type
being translated. *)
Fixpoint removeIndRelProps (*_: inductive*) (t:STerm) : (STerm) :=
match t with
| mkPiS x A Sa B Sb 
  => mkPiS x A (* strict positivity => tind cannot appear in A *) Sa (removeIndRelProps B) None
| t => t
end.




Import STermVarInstances.
Definition isoModeId (id:ident) := String.append id "_iso".

Definition indGoodTransName (n:inductive) : ident :=
  String.append (indTransName n) "_good". 

Definition indIndicesTransName (n:inductive) : ident :=
String.append (indTransName n) "_indices".

Definition indIndicesIrrelTransName (n:inductive) : ident :=
String.append (indTransName n) "_indices_irr".

Definition indIndicesConstrTransName (i:ident) : ident := 
String.append i "c".

Definition indIndicesConstrTransNameFull (n:inductive) : ident :=
indIndicesConstrTransName (indIndicesTransName n).

Definition indTransTotName (iff b21: bool)(n:inductive) : ident :=
  let tot := if iff then "iff" else "tot" in
  let s21 := if b21 then "21" else "12" in
  (String.append (indTransName n) (String.append tot s21)).

Definition indTransOneName (b21: bool)(n:inductive) : ident :=
  let tot := "one" in
  let s21 := if b21 then "21" else "12" in
  (String.append (indTransName n) (String.append tot s21)).

Require Import SquiggleEq.AssociationList.

Definition mindNumParams (t:simple_mutual_ind STerm SBTerm) :nat :=
length (fst t).

(* Move to templateCoqMisc?
In the constructor types in t, vars representing the inductive being defined
(now already defined) need to be replaces with the corresponding term (of the form mkInd _)
by which they are referred to after the definition.
 *)
Definition substMutIndMap {T:Set} (f: SBTerm -> list STerm -> list Arg -> T)
           (id:ident) (t: simple_mutual_ind STerm SBTerm)
:list (inductive* simple_one_ind STerm T) :=
    let (params,ones) := t  in
    let numInds := (length ones) in
    let is := List.seq 0 numInds in
    let inds := map (fun n => mkInd id n) is in
    let indsT := map (fun n => mkConstInd n) inds in
    let numParams := (length params) in
    (* Fix: for robustness agains variable implementation, use FreshVars?*)
    let lp := getParamAsVars numParams ones in
    let onesS := map (mapTermSimpleOneInd
       (@Datatypes.id STerm)
       (fun b: SBTerm => f b indsT lp)) ones in
       combine inds onesS.

Definition substMutInd 
           (id:ident) (t: simple_mutual_ind STerm SBTerm)
  :list (inductive* simple_one_ind STerm STerm) :=
  substMutIndMap (fun b is ps => apply_bterm b (is++(map (vterm∘fst)ps))) id t.

Definition ondIndType {ConstrType:Set} (t: simple_one_ind STerm ConstrType) : STerm :=
  let '(_,typ,_) := t in typ.
                
Definition indTypes (id:ident)
           (t: simple_mutual_ind STerm SBTerm) : list (inductive * STerm):=
  let (_,ones) := t  in
  let oneTypes := map ondIndType ones in
  let oneTypesN := numberElems oneTypes in
  map (fun (p:(nat*STerm)) => let (n,typ) := p in (mkInd id n, typ)) oneTypesN.


Definition substMutIndNoParams
           (id:ident) (t: simple_mutual_ind STerm SBTerm)
  :list (inductive* simple_one_ind STerm SBTerm) :=
  substMutIndMap (fun b is _ => apply_bterm_partial b is) id t.

Definition substMutIndParamsAsPi
           (id:ident) (t: simple_mutual_ind STerm SBTerm)
  :list (inductive * simple_one_ind STerm STerm) :=
  substMutIndMap (fun b is ps => 
    mkPiL (map removeSortInfo ps) (apply_bterm b (is++(map (vterm∘fst) ps)))
    ) id t.



Definition mutAllConstructors
           (id:ident) (t: simple_mutual_ind STerm SBTerm) : list (ident * STerm) :=
  flat_map (fun p:(inductive * simple_one_ind STerm STerm) => let (i,one) := p in 
    let numberedConstructors := numberElems (map snd (snd one)) in
    map (fun pc => (constrTransName i (fst pc),snd pc)) numberedConstructors
    ) (substMutIndParamsAsPi id t).


Definition substIndConstsWithVars (id:ident) (numInds : nat)
           
(indTransName : inductive -> ident)
  : list (ident*V) :=
    let is := List.seq 0 numInds in
    let inds := map (fun n => mkInd id n) is in
    let indRNames := map indTransName inds in
    (* Fix: for robustness agains variable implementation, use FreshVars?*)
    let indRVars : list V := combine (seq (N.add 3) 0 numInds) (map nNamed indRNames) in
    combine indRNames (indRVars).


(** to be used when we don't yet know how to produce a subterm *)
Axiom F: False.
Definition fiat (T:Type) : T := @False_rect T F.

(* somehow False_rect doesn't work while unquoting *)

Definition indEnv:  Type := AssocList ident (simple_mutual_ind STerm SBTerm).


(* return numParams as well? may be needed for generating Fix F = F (Fix F)*)
Definition lookUpInd (ienv: indEnv) (ind : inductive) : (simple_one_ind STerm SBTerm)*nat :=
  match ind with
  | mkInd id n =>
    let omind := ALFind ienv id in
    let dummy :=  (ind, dummyInd) in
    (match omind with
      | Some mind => 
        let mindS := substMutIndNoParams id mind in
        (snd (nth n mindS dummy), length (fst mind))
      | None=> (dummyInd, O)
    end) 
  end.
  

Section trans.
Variable piff:bool.
(* already removed
Let removeHeadCast := if piff then removeHeadCast else id. 
*)
Definition needSpecialTyRel := if piff 
then 
  (fun os =>
    match os with
  | Some s => isPropOrSet s
  | None => false
  end
  ) 
else (fun _ => false).

Let isoModeId  := if piff then isoModeId else id.
Let indTransName s := (isoModeId ( indTransName s)).


(* TODO : use fixDefSq *)
Definition mkFixCache
           (p: list (fixDef V STerm)) : fixCache :=
  fixDefSq bterm p.

(* TODO:  use the mkFixcache above.
 indTransName depends on mode*)
Definition mutIndToMutFixAux {TExtra:Type}
(tone : forall (numParams:nat)(tind : inductive*(simple_one_ind STerm STerm)),
  (list Arg) * (fixDef True STerm)* list TExtra)
(id:ident) (t: simple_mutual_ind STerm SBTerm) (i:nat)
  : STerm * list TExtra :=
    let onesS := substMutInd id t in
    let numInds := length onesS in
    let numParams := length (fst t) in
    let trAndDefs := map (tone numParams) onesS in
    let tr: list ((list Arg) *fixDef True STerm) := map fst trAndDefs in
    let lamArgs := match tr with
                   | (la,_)::_ => la
                   | _ => []
                   end in
    let tr := map snd tr in
    let extraDefs := flat_map snd trAndDefs in
    let lamArgs := mrs lamArgs in 
    let constMap := substIndConstsWithVars id numInds indTransName in
    let indRVars := map snd constMap in
    let constMap := map (fun p => (fst p, mkLamL lamArgs ((vterm ∘ snd) p))) constMap in
    (* TODO : use one of the combinators *)
    let o: CoqOpid := (CFix numInds (map (@structArg True STerm) tr) [] i) in
    let bodies := (map ((bterm indRVars)∘(substConstants constMap)∘(@fbody True STerm)) tr) in
    let f := mkLamL (lamArgs) (oterm o (bodies++(map ((bterm [])∘ fst ∘(@ftype True STerm)) tr))) in
    (f , extraDefs).

Definition mutIndToMutFix
(tone : forall (numParams:nat)(tind : inductive*(simple_one_ind STerm STerm)),
    (list Arg) *  (fixDef True STerm))
(id:ident) (t: simple_mutual_ind STerm SBTerm) (i:nat)
  : STerm:=
fst (@mutIndToMutFixAux True (fun np i => (tone np i,[])) id t i).

Let constrTransName ind cnum := (isoModeId (constrTransName ind cnum)).
Let constrInvFullName ind cnum := (isoModeId (constrInvFullName ind cnum)).
Let projTyRel := if piff then projTyRel else (fun _ _ t=> t).
Let mkTyRel := if piff then mkTyRel else mkTyRelOld.

(* Let indTransName := if piff then indGoodTransName else indTransName. *)

(** AR is of type BestRel A1 A2 or A1 -> A2 -> Type. project out the relation
in the former case. 
Definition maybeProjRel (A1 A2 AR : STerm) :=
   if (hasSortSetOrProp A) then 
           (fun t => projTyRel A1 A2 AR)
      else AR.
*)


(* TODO : rename to projectifIneeded *)
Definition castIfNeeded  (A : (STerm * option sort)) (Aprime AR : STerm)
  : STerm :=
  let (A, Sa) := A in
  let f := if (needSpecialTyRel Sa) then 
           (fun t => projTyRel A Aprime t)
      else id in
  f AR.

(*
Definition transLamAux (translate : STerm -> STerm)
           (A : (STerm * option sort)) : ((STerm * STerm)*STerm) :=
  let (A1, Sa) := A in
  let A2 := tvmap vprime A1 in
  (A1, A2, castIfNeeded A A2 (translate A1)).
 *)

Definition transLam (translate : STerm -> STerm) (nma : Arg) b :=
  let (nm,A1s) := nma in
  let A1 := fst A1s in
  let A2 := tprime A1 in
  let AR := castIfNeeded A1s  A2 (translate A1) in
  mkLamL [(nm, A1);
            (vprime nm, A2);
            (vrel nm, mkAppBeta AR [vterm nm; vterm (vprime nm)])]
         b.

Definition getConstrRetIndices 
  (numParams: nat)  
    (fretType : forall (cargs: list Arg) (cretType : STerm), STerm)
    (ctype : STerm)
    : list STerm :=
  let (constrRetTyp, constrArgs) := getHeadPIs ctype in
  let thisConstrRetTyp : STerm := fretType constrArgs constrRetTyp in
  let (_,cRetTypArgs) := flattenApp thisConstrRetTyp [] in
  skipn numParams cRetTypArgs.

(* take the variables denoting constructor arguments in the original match branch
lambda and get the full constructor and the indices in its return type *)
Definition matchProcessConstructors
           (np: nat)
           (tind: inductive)
           (discTParams  : list STerm) (bnc : (list V)*(nat*SBTerm)) :
  (STerm * list STerm) :=
  let (bargs, thisConstrTyp) := bnc in
  let bargs : list STerm := map (vterm) bargs in
  let (thisConstrNum, thisConstrTyp) := thisConstrTyp in
  (* let restArgs := skipn ncargs args in *)
  let thisConstrTyp : STerm := apply_bterm thisConstrTyp discTParams in
  let substCRetType  constrArgs constrRetTyp : STerm := 
    ssubst_aux constrRetTyp
     (combine (map fst constrArgs) bargs) in
  let thisConstr := mkConstr tind thisConstrNum in
  let thisConstrFull := mkApp thisConstr (discTParams++bargs) in
  (thisConstrFull, getConstrRetIndices np substCRetType thisConstrTyp).

(* write a function that gets only the first x headLams *)
Definition transMatchBranchInner (discTypParamsR : list STerm)
           (*translate: STerm -> STerm*) (*np: nat*)
           (*tind: inductive*)
           (retTypLamPartiallyApplied : list STerm -> STerm)
           (bnc : (option ident)*((STerm * list Arg)*(STerm * list STerm))) : STerm :=
  let (constrInv, bnc) := bnc in
  let (brn, thisConstrInfo) := bnc in
  let (thisConstrFull, thisConstrRetTypIndices) := thisConstrInfo in
  let retTyp := retTypLamPartiallyApplied
                  (map tprime (snoc thisConstrRetTypIndices thisConstrFull)) in
  let (ret, args) := brn in (* assuming there are no letins *)
  let cargs := map removeSortInfo args in
  let cargs2 := (filter_mod3 cargs 1) in
  let (cargs_R (*R*), cargsAndPrimes) := separate_Rs cargs in
  let cargsAndPrimes := map (vterm ∘ fst) cargsAndPrimes in
  let (retTypBody,pargs) := getHeadPIs retTyp in
  let ret :=
    match constrInv with (* in the branches where the constructors dont match, this is None *)
    | Some constrInv => 
        let f : STerm := mkLamL cargs_R ret in 
        mkConstApp constrInv (discTypParamsR++cargsAndPrimes
                                            (* indIndices_R with 1s and 2s substituted *)
                                            ++(map (vterm ∘ fst) pargs)
          ++[headPisToLams retTyp;f])
    | None =>
         let sigt : V := last (map fst pargs) dummyVar in
        falseRectSq retTypBody (vterm sigt)
    end
    in
  mkLamL cargs2 (mkLamL (map removeSortInfo pargs) ret).


Definition transMatchBranch (discTypParamsR : list STerm) (o: CoqOpid) (np: nat)
           (tind: inductive)
           (allBnc : list ((STerm * list Arg)*(STerm * list STerm)))
           (retTypLam : STerm) (retArgs1: list (V*STerm))
           (disc2: STerm)
           (bnc: nat* ((STerm * list Arg)*(STerm * list STerm))) : STerm
            :=
  let (thisConstrIndex, bnc) := bnc in
  let (brn, thisConstrInfo) := bnc in
  let (b_R, cargs) := brn in
  let (thisConstrFull, thisConstrRetTypIndices) := thisConstrInfo in
  let retArgs2 := map primeArgsOld retArgs1 in
  let cargs := map removeSortInfo (filter_mod3 cargs 0) in
  (* let restArgs := skipn ncargs args in *)
  let oneRetArgs1 := (snoc thisConstrRetTypIndices thisConstrFull) in
  let goodConstrb := (boolNthTrue (length allBnc) thisConstrIndex) in
  let constrInvName := constrInvFullName tind thisConstrIndex in
  let goodConstrb := 
    map (fun b:bool => if b then Some constrInvName else None) goodConstrb in
  let allBnc := combine goodConstrb allBnc in
  let brs :=
      (* this must be AppBeta because we need to analyse the simplified result *)
      let retTypLamPartial args2 := mkAppBeta retTypLam (merge oneRetArgs1 args2) in
      map (transMatchBranchInner discTypParamsR retTypLamPartial) allBnc in
  let matchRetTyp :=
    mkApp retTypLam (merge oneRetArgs1 (map (vterm∘fst) retArgs2)) in
  let matchRetTyp := mkLamL retArgs2 matchRetTyp in
  mkLamL cargs
    (oterm o ((bterm [] matchRetTyp):: (bterm [] disc2)::(map (bterm []) brs))).
           
Definition transMatch (translate: STerm -> STerm) (ienv: indEnv) (tind: inductive)
           (rsort: option sort)
           (numIndParams: nat) (lNumCArgs : list nat) (retTyp disc discTyp : STerm)
           (branches : list SBTerm) : STerm :=
  let o := (CCase (tind, numIndParams) lNumCArgs None) in
  let (_, retArgs) := getHeadLams retTyp in (* this is a lambda, encoding  as _  in _ return _  with*)
  let vars := map fst retArgs in
  let lastVar := last vars dummyVar in
  let mt := oterm o ((bterm [] retTyp):: (bterm [] (vterm lastVar))
                                      :: (bterm [] discTyp)::(branches)) in
  let discInner := tvmap vprime disc in
  let retTyp_R := translate (* in false mode?*) retTyp in
  let (retTypLeaf, rargs) := getHeadLams retTyp in
  let nrargs := length rargs in
  let (retTyp_R, retArgs_R) := getNHeadLams (3*nrargs) retTyp_R in
  let (arg_Rs, argsAndPrimes) := separate_Rs retArgs_R in
  
  let retTyp_R := mkApp (castIfNeeded (retTypLeaf,rsort) (tprime retTypLeaf) retTyp_R)
                        [mt; tvmap vprime mt] in
  let retTyp_R := mkPiL (map removeSortInfo arg_Rs) retTyp_R in
  (* let binding this monster can reduce bloat, but to letbind, 
      we need to compute its type. *)
  let retTypLam : STerm := mkLamL (map removeSortInfo argsAndPrimes) retTyp_R in
  let (_,discTypArgs) := flattenApp discTyp [] in
  let discTypIndices := skipn numIndParams discTypArgs in
  let discTypParams := firstn numIndParams discTypArgs in
  let (_, discTypArgsR) := flattenApp (translate discTyp) [] in
  let discTypParamsR := (firstn (3*numIndParams) discTypArgsR) in
  let discTypIndicesR :=
      fst (separate_Rs (skipn (3*numIndParams) discTypArgsR)) in
  (* Warning! if this list of constructors has no elements,
     there will be no branches in the produced translation *)
  let constrTyps : list SBTerm := map snd ((snd ∘ fst) (lookUpInd ienv tind)) in
  let branches_R  := map (translate ∘ get_nt) branches in
  let branches_RN := (combine lNumCArgs branches_R) in
  let branches_R := map (fun p => getNHeadLams (3*fst p) (snd p)) branches_RN in
  let branches_RArgs := map (fun p => map fst (filter_mod3 (snd p) 0)) branches_R in
  let branchPackets :=  (combine branches_RArgs (numberElems constrTyps)) in
  let pbranchPackets :=
      map (matchProcessConstructors numIndParams tind discTypParams) branchPackets in
  let branchPackets_R :=(combine branches_R pbranchPackets) in
  let retArgs := map removeSortInfo retArgs in
  let brs := 
      map (transMatchBranch discTypParamsR
             o numIndParams tind branchPackets_R retTypLam
             retArgs (tprime disc)) (numberElems branchPackets_R) in
  let retTypOuter : STerm :=
    mkApp retTypLam 
      (merge (map (vterm∘fst) retArgs) 
             (map (tvmap vprime) (snoc discTypIndices disc))) in
  let retTypOuter : STerm := mkLamL (retArgs) retTypOuter in
  mkApp
    (oterm o ((bterm [] retTypOuter):: (bterm [] disc)::(map (bterm []) brs)))
    (snoc discTypIndicesR (translate disc)).
  

(*  
  let fv : V := freshUserVar (all_vars mt) "retTyp" in
  mkLetIn fv  (headLamsToPi2 retTypLam) 
  ((oterm (CConstruct (mkInd "Coq.Numbers.BinNums.N" 0) 0) [])).
  oterm o
    ((bterm [] retTyp):: (bterm [] disc):: (bterm [] discTyp)::lb) => 

  disc.
*)



(* to get the unfolding lemma for (fix name ... :=), first let bind the fix to name
  and then put the result of this function..
e.f. let name  :=  (fix name ... :=) in [output of this function]. This function
gets the name from fb*)
Definition fixUnfoldingProof (ienv : indEnv) (fb: fixDef V STerm) : STerm
  :=
  let fbmut := vterm (fname fb) in
  let (body, bargs) := getHeadLams (fbody fb) in
  let nargs := length bargs in
  (*TODO : find out whether fretType:Set or Prop. because a cast will then be needed.
assume. A fixpoint may return a Prop, in which case casting should not be done*)
  let fretType := (ftype fb) in
  let sarg : Arg := nth (structArg fb) bargs
                        (dummyVar, (oterm (CUnknown "fixUnfoldingProof:nthFail") [], None))in
  let sargType := fst (snd sarg) in
  let (tind, sargT) := flattenApp sargType [] in
  let tind : inductive := extractInd tind in
  let (tindDefn, numParams) :=  lookUpInd ienv tind in
  let constrTyps : list SBTerm := map snd (snd tindDefn) in
  let sargTIndices : list STerm := skipn numParams sargT in
  let sargTParams : list STerm := firstn numParams sargT in
  let constrTyps : list STerm := map (fun b => apply_bterm_unsafe b sargTParams) constrTyps  in
  let bargs : list (V*STerm):= mrs bargs in
  let eqt : STerm := mkEqSq (fst fretType) body (mkApp fbmut (map (vterm ∘fst) bargs)) in
  (* all indices must be vars *)
  let sargTIndicesVars : list V := flat_map free_vars sargTIndices in
  let caseRetType : STerm :=
      let indicArgs : list (V*STerm):=
          map (fun v => (v,opExtract (oterm (CUnknown "fixUnfoldingProof:ALMap") [])
              (ALFind bargs v))) sargTIndicesVars in
      mkLamL  (snoc indicArgs (removeSortInfo sarg)) eqt in
  let mkBranch (ctype : (nat * STerm)) : nat*STerm :=
      let (constrIndex, ctype) := ctype in 
      let ctype := change_bvars_alpha (free_vars eqt) ctype in 
      let (cretType,cargs) := getHeadPIs ctype in
      let cretIndices :=
          let (_,cRetTypArgs) := flattenApp cretType [] in
          skipn numParams cRetTypArgs in
      let indicesSubst := combine sargTIndicesVars cretIndices in
      let thisConstr : STerm := mkApp (mkConstr tind constrIndex)
                                      (sargTParams++(map (vterm ∘fst) cargs)) in
      (* each branch needs to be translated to match the current constructors *)
      let fretType := ssubst_aux (fst fretType) (snoc indicesSubst (fst sarg, thisConstr)) in
      (* do we also need to substitute the indices in the body ?*)
      let ret := (mkEqReflSq fretType
             (ssubst_aux body [(fst sarg, thisConstr)])) in
      (length cargs, mkLamL (mrs cargs) ret) in
  let branches : list (nat*STerm) := map mkBranch (numberElems constrTyps) in
  let o : CoqOpid:= (CCase (tind, numParams) (map fst branches) None) in
  let unfBody := oterm o (map (bterm []) (caseRetType::(vterm (fst sarg))::(map snd branches))) in
  mkLamL bargs unfBody.

Definition translateFix (ienv : indEnv) (bvars : list V)
           (t:  (fixDef V STerm) * (fixDef V STerm)) : (fixDef V STerm) :=
  let (t, t_R) := t in
  let (bodyOrig, args) := getHeadLams (fbody t) in
  let nargs := length args in
  let (body_R, bargs_R) := getNHeadLams (3*nargs) (fbody t_R) in
  let fretType := ftype t in
  let vargs := (map (vterm ∘ fst) args) in
  let fretType_R := ftype t_R in
  let fretType_R := castIfNeeded fretType (tprime (fst fretType)) (fst fretType_R) in
  let fretType := fst fretType in
  let fixApp : STerm := (mkApp (vterm (fname t)) vargs) in
  (* need thse apps. otherwise function extensionality may be needed *)
  let fixAppPrime : STerm := tprime fixApp in
  let bargs_R := (map removeSortInfo bargs_R) in
  let fretTypeFull :=
      mkPiL bargs_R (mkApp fretType_R [fixApp; fixAppPrime]) in
  let vl : V := freshUserVar (bvars++ allVars (fbody t) ++ allVars fretType) "equ" in
  let transportPL := mkLam vl fretType (mkApp fretType_R [vterm vl; fixAppPrime]) in
  let transportPR := mkLam vl (tprime fretType)
                           (mkApp fretType_R [bodyOrig; vterm vl]) in
  let eqLType : EqType STerm := (Build_EqType _ fretType bodyOrig fixApp) in
  let eqRType : EqType STerm := map_EqType tprime eqLType in
  let peqUnfolding := mkApp (fixUnfoldingProof ienv t) vargs  in
  let body : STerm := mkTransport transportPR eqRType (tprime peqUnfolding) body_R in
  let body : STerm := mkTransport transportPL eqLType peqUnfolding body in
  let body := mkLamL bargs_R body in
  
  (* the tprime below is duplicat computation. it was done in the main fix loop *)
(*  let fretTypeFull :=
      reduce 10 (mkAppBeta (ftype _ _ t_R) [vterm (fname _ _ t); vterm (vprime (fname _ _ t))]) in *)
  (* the name in t_R is not vreled *)
  {|fname := vrel (fname t);
    fbody :=  body;
    ftype := (fretTypeFull, None);
    structArg := 3*(structArg t) (* add 2 if the struct arg inductive was translated in ind style *)|}.


Variable ienv : indEnv.



Fixpoint translate (t:STerm) : STerm :=
match t with
| vterm n => vterm (vrel n)
| mkSort s =>
  let v1 := (0, nAnon) in
  let v2 := (3, nAnon) in
(* because the body of the lambda is closed, no capture possibility*)
      mkLamL
        [(v1 (* Coq picks some name like H *), t);
         (v2, t)]
         (mkTyRel (vterm v1) (vterm v2) (mkSort (translateSort s)))
| mkCast tc _ _ => translate tc
| mkConstr i n => mkConst (constrTransName i n)
| mkConst c => mkConst (constTransName c)
| mkConstInd s => mkConst (indTransName s)
| mkLamS nm A Sa b => transLam translate (nm,(A,Sa)) (translate b)
| oterm (CFix len rargs sorts index) lbs =>
  let o := CFix len rargs [] in
  let mkLetBinding (p:nat*fixDef V STerm) (tb :STerm) : STerm :=
      let lbs := undoProcessFixBodyType len lbs in
      let lbsPrime := map btprime lbs in
      let (n,t) := p in
      let body := mkLetIn (vprime (fname t))
                      (oterm (o n) lbsPrime)
                      (tprime (getProcessedFixFullType t))
                      tb
                       in 
      mkLetIn (fname t)
              (oterm (o n) lbs)
               ((getProcessedFixFullType  t))
              body in
  let bvars := getFirstBTermVars lbs in
  (* delaying the translation will only confuse the termination checker *)
  let fds_R  := tofixDefSqAux bvars (translate ∘ get_nt) len rargs [] lbs in
  let fds  := tofixDefSqAux bvars (get_nt) len rargs sorts lbs in
  let letBindings th := fold_right mkLetBinding th (numberElems fds) in
  let (o,lb) := fixDefSq bterm (map (translateFix ienv bvars) (combine fds fds_R)) in
    (* letBindings (mkConstApp "fiat" []) *)
    letBindings (oterm (o index) lb)
| mkPiS nm A Sa B Sb =>
  let (_, f) := mkPiR piff needSpecialTyRel Sa Sb in
  (*let (downCastOp, goodLvl) := goodLvl in *)
  let A1 := A in
  let A2 := tvmap vprime A1 in
  let B1 := (mkLam nm A1 B) in
  let B2 := tvmap vprime B1 in
  let B_R := transLam translate (nm,(A,Sa)) ((translate B)) in
   f nm A1 A2 (translate A) B1 B2 B_R
(* the translation of a lambda always is a lambda with 3 bindings. So no
projection of LHS should be required *)
| oterm (CApply _) (fb::argsb) =>
  (* if this changes, change extractGoodRelFromApp below *)
    mkAppBeta (translate (get_nt fb)) (flat_map (appArgTranslate translate) argsb)
(* Const C needs to be translated to Const C_R, where C_R is the registered translation
  of C. Until we figure out how to make such databases, we can assuming that C_R =
    f C, where f is a function from strings to strings that also discards all the
    module prefixes *)
| oterm (CCase (tind, numIndParams) lNumCArgs rsort) 
    ((bterm [] retTyp):: (bterm [] disc):: (bterm [] discTyp)::lb) =>
  transMatch translate ienv tind rsort numIndParams lNumCArgs retTyp disc discTyp lb
| _ => oterm (CUnknown "bad case in translate") []
end.

End trans.


(* only used in translateOnePropTotal 
Definition translateArg  (p : Arg) : (V * STerm) :=
  let (v,As) := p in
  let A:= fst As  in
let AR := castIfNeeded As (tprime A) (translate A) in
(vrel v, mkAppBeta AR [vterm v; vterm (vprime v)]).
 *)

(*
Definition transLamAux (translate : STerm -> STerm)
           (A : (STerm * option sort)) : ((STerm * STerm)*STerm) :=
  let (A1, Sa) := A in
  let A2 := tvmap vprime A1 in
  (A1, A2, castIfNeeded A A2 (translate A1)).
*)


Fixpoint removeCastsInConstrType (tind : inductive) (t:STerm) : (STerm) :=
match t with
| mkPiS x A Sa B Sb 
  => let (A,Sa) := if isConstrArgRecursive tind A then (removeIndRelProps A,None) else (A,Sa) in
    mkPiS x A Sa (removeCastsInConstrType tind B) None
| t => t
end.


(*
Definition translateConstrArg tind (p : Arg) : (V * STerm) :=
let (v,t) := p in
let t := if isConstrArgRecursive tind (fst t) then (removeIndRelProps (fst t),None) else t in 
translateArg (v,t).
 *)

(* Move *)
Definition mkConstrInfo numParams (constrLamType_R : nat*STerm) 
(* Pis converted to lams before translating *)
: IndTrans.ConstructorInfo := 
let (index, constrLamType_R) := constrLamType_R  in
let (retType_R, args_R) := getHeadLams constrLamType_R  in
  let (_,cRetTypArgs_R) := flattenApp retType_R [] in
  let cretIndices_R := skipn (3*numParams) cRetTypArgs_R in
{|
    IndTrans.index := index;
    IndTrans.args_R := TranslatedArg.unMerge3way args_R;
    IndTrans.retTyp := retType_R;
    IndTrans.retTypIndices_R := TranslatedArg.unMerge3way cretIndices_R
|}.

(* for a constructor C of type T, it produces C_R : [T] C C.
the input args are already translated.
Both in C_RR and C_RRinv, the corresponding I_RR never directly occurs.
if they occured, there relation would have to be casted. right now,
C_RR and C_RRinv already produce the casted version *)
Definition translateConstructor (tind:inductive)
(*np:nat*) (cindex:nat)
(cargs_R cargsRR indTypeParams_R (* indTypIndices_RR*) : list Arg)
(constrApp sigtFullConstrIndices : STerm)
  : defSq*STerm :=
let cname := constrTransName tind cindex in
let lamArgs := (map removeSortInfo (indTypeParams_R ++ cargs_R)) in
let ext := sigTToExistT2 (map (vterm∘fst) cargsRR) constrApp sigtFullConstrIndices in
({| nameSq := cname; bodySq := mkLamL lamArgs ext |}, ext).

(* the indices_RR need not be cretIndices. 
this one uses the index indices irrel lemma whic uses proof irrelevance *) 
Definition translateConstructorTot (tind:inductive)
(*np:nat*) (cindex:nat) (cretIndices_R : list STerm)
(cargs_R  indTypeParams_R : list Arg) (indTypIndices_RR : list (V*STerm))
(sigtFull : STerm)
  : defSq :=
  let cname := constrTransTotName tind cindex in
  let constArgs := mrs (indTypeParams_R ++ cargs_R) in
  let allArgs := constArgs ++ indTypIndices_RR in
  let tindIArgs : list STerm :=
      (map (vterm ∘ fst) indTypeParams_R)
        ++ cretIndices_R
        ++ (map (vterm ∘ fst) indTypIndices_RR) in
  let body := mkConstApp (constrTransName tind cindex) (map (vterm ∘ fst) constArgs) in
  let v := freshUserVar (map fst allArgs) "eqIrr" in
  let tindi := mkInd (indIndicesTransName tind) 0 in
  let o :=
      (CCase (tindi, length constArgs) [0])%nat None in
  let caseRet :=
      mkLamL (snoc (indTypIndices_RR) (v, mkIndApp tindi tindIArgs))
             sigtFull in
  let peq := mkConstApp (indIndicesIrrelTransName tind) tindIArgs in
  let body := oterm o (map (bterm [])[caseRet; peq; body]) in
({| nameSq := cname; bodySq := mkLamL (allArgs) body |}).

Definition mkSigTRect  A B  sigRetTyp sigRet:=
mkConstApp sigt_rec_ref [A;B; sigRetTyp; sigRet].

Definition mkSigTRectDirect  A B  sigRetTyp sigRet:=
  (* compute this only once, outside? *)
  let v := freshUserVar (flat_map free_vars [A;B;sigRetTyp;sigRet]) "sigrectv" in
  mkLam v (mkIndApp sigtInd [A;B]) 
  (oterm sigtMatchOpid (map (bterm []) [sigRetTyp; vterm v; sigRet])).

(** retTyp is the retTyp applied to all the ind_RRs except the last one.
existT is initially sigtVar, whose type is the big sigma type.
vars : initially null
sigT is the type of sigtVar, the branch of I_RR *)
Fixpoint crInvMapSigT o (indicRR: list (V*STerm))(sigtVar : V) (f retTyp existt sigt: STerm)
         (vars: list V) {struct sigt}: STerm :=
  let sigRetTyp := (mkLam sigtVar sigt (mkApp retTyp [existt])) in
  let finalCase (_: unit) :=
      let mb := mkApp f (map vterm vars) in (* the constructor takes no args *)
      (* Fix. need to have goodness here.. this will be used in matches.
only while generating I_RR and its goodness, we can skip goodness *)
      let caseType := mkLamL(*S*) (indicRR) sigRetTyp in
      let matchBody := oterm o (map (bterm []) [caseType; vterm sigtVar; mb]) in
      mkLam sigtVar sigt matchBody in
                  
match sigt with
| oterm (CApply _)
 ((bterm [] (mkConstInd (mkInd s _)))::
   (bterm [] A)::(bterm [] (mkLamS a _(*A*) _ b))::[])
  =>
  if (decide (s=sigt_ref)) then 
    let B := (mkLam a A b) in
    let newDepPair := mkApp (mkConstr (mkInd sigt_ref 0) 0) [A;B;vterm a;vterm sigtVar] in 
    let newExistt := ssubst_aux existt [(sigtVar,newDepPair)] in 
    let sigRet := mkLam a A (crInvMapSigT o indicRR sigtVar f retTyp newExistt b (snoc vars a)) in
    mkSigTRectDirect A B  sigRetTyp sigRet
  else finalCase ()
| _ => finalCase ()
end.
Check sigT_rect.

Definition translateConstructorInv 
  (tind tindConstr:inductive) (indConstrNumParams : nat)
  (*np:nat*) (cindex:nat)
  (C_RRBody : STerm)
  (cretIndices_RR : list STerm)
  (cargs_R cargsRR indTypeParams_R : list Arg)  
  (indTypIndices_RR : list (V*STerm))
  (sigtFull : STerm) : defSq:=

let cname := constrInvFullName tind cindex in
let freshVars := 
  let fvars :=  dummyVar::((map fst cargs_R)++(map fst indTypeParams_R)) in
  freshUserVars fvars ["sigt", "rett", "retTyp"] in
let sigtVar := vrel (nth 0 freshVars dummyVar) in
let rettVar := vrel (nth 1 freshVars dummyVar) in
let retTypVar := vrel (nth 2 freshVars dummyVar) in
let (cargs_RR,cargsAndPrimes) := separate_Rs cargs_R in
let lamArgs := (map removeSortInfo (indTypeParams_R++ cargsAndPrimes))
                ++indTypIndices_RR in 
let cargs_RR := map removeSortInfo cargs_RR in
let retTypVarType : STerm := 
    let retTypVarSort : STerm
                  (* Fix. make it template/univ poly *)
        := mkConst "Trecord.IndicesInvUniv" in 
  (* dummyVar is fine, because the next item is a sort, thus has no fvars *)
  (mkPiL (snoc indTypIndices_RR (dummyVar, sigtFull)) retTypVarSort) in
let rettVarType := 
  (mkPiL cargs_RR (mkApp (vterm retTypVar) (snoc cretIndices_RR C_RRBody))) in
let crinvBody := 
    let rettTypPartiallyApplied : STerm := 
        (mkApp (vterm retTypVar) (map (vterm∘fst) indTypIndices_RR)) in
    let o := (CCase (tindConstr, indConstrNumParams) [O] None) in
    mkApp (crInvMapSigT o indTypIndices_RR sigtVar (vterm rettVar) rettTypPartiallyApplied
                 (vterm sigtVar) sigtFull []) [vterm sigtVar] in
(*  let T := (mkConstInd (mkInd "Coq.Init.Logic.True" 0)) in
  let sigt := (mkSigL cargs_RR T) in
  let ext := sigTToExistTRect (vterm sigtVar) (vterm rettVar) sigt [] in *)
let lamArgs := lamArgs
  ++ [(sigtVar, sigtFull); (retTypVar, retTypVarType); (rettVar, rettVarType)] in
{| nameSq := cname; bodySq := mkLamL lamArgs crinvBody |}.


Definition translateIndInnerMatchBranch (tind : inductive )
(indTypeParams_R (* indTypIndices_RR *) : list Arg) (indTypIndicVars : list V)
(caseTypRet:  STerm) (argsB: bool * IndTrans.ConstructorInfo) : 
  STerm * (list defSq) :=
  let (b,cinfo) := argsB in
  let cargsRR := map removeSortInfo (IndTrans.argRR cinfo) in
  let cargs_R : list Arg := TranslatedArg.merge3way (IndTrans.args_R cinfo) in
  let cargs := IndTrans.args cinfo in
  let indTypIndicVars := (map vprime indTypIndicVars) in
  let caseTypRet := 
    let cretIndicesPrime := (IndTrans.indicesPrimes cinfo) in
    ssubst_aux caseTypRet (combine indTypIndicVars cretIndicesPrime) in
  let (_,indTypIndices_RR) := getHeadPIs caseTypRet in
  let indTypIndices_RR := map removeSortInfo indTypIndices_RR in
  let cretIndices_R : list STerm := TranslatedArg.merge3way
                                      (IndTrans.retTypIndices_R cinfo) in
  let cretIndices_RR : list STerm := (IndTrans.indicesRR cinfo) in
  let t := boolToProp b in
  let ret (_:True):=
    let tindIndicesName := (indIndicesTransName tind) in 
    let tindIndices := (mkInd tindIndicesName 0) in
    let tindsConstrArgs := map (vterm ∘ fst) indTypeParams_R ++ cretIndices_R in
    let tindsArgs :=  tindsConstrArgs ++ map (vterm ∘ fst) indTypIndices_RR in
    let tindApplied := mkIndApp tindIndices tindsArgs in
    let tindConstrApplied := mkApp (mkConstr tindIndices 0) tindsConstrArgs in
    let sigtFull := mkSigL cargsRR tindApplied in
    let (C_RR,C_RRbody) := 
      let fvars : list V:= flat_map free_vars cretIndices_RR in
      let sigtFullR : STerm := change_bvars_alpha fvars sigtFull in
      let sigtFullConstrIndices : STerm := 
        ssubst_aux sigtFullR (combine (map fst indTypIndices_RR) cretIndices_RR) in
          translateConstructor tind (IndTrans.index cinfo) 
          cargs_R (IndTrans.argRR cinfo) indTypeParams_R tindConstrApplied sigtFullConstrIndices in
    let C_RRInv := 
        translateConstructorInv tind tindIndices (length tindsConstrArgs)
                                (IndTrans.index cinfo) 
                                C_RRbody cretIndices_RR cargs_R (IndTrans.argRR cinfo)
                                indTypeParams_R indTypIndices_RR
                                sigtFull in 
    let C_RRTot := 
        translateConstructorTot tind (IndTrans.index cinfo)
                                (TranslatedArg.merge3way (IndTrans.retTypIndices_R cinfo))
                                cargs_R
                                indTypeParams_R
                                indTypIndices_RR
                                sigtFull in 
    (sigtFull,  [C_RR , C_RRInv , C_RRTot  ]) in
  (* to avoid duplicate work, only make defs if b is true *)
  let retDefs : (STerm* list defSq) := 
    (if b  then (ret I) else (t,[])) in
  (mkLamL (map primeArg cargs) (mkLamL indTypIndices_RR (fst retDefs)),snd retDefs).


(* List.In  (snd lb) lcargs *)
Definition translateIndInnerMatchBody tind o (lcargs: list IndTrans.ConstructorInfo)
   v (caseTypArgs : list (V*STerm))(caseTypRet:  STerm)
   (indTypeParams_R indTypIndices_RR : list Arg) (indTypIndicVars : list V)
    (lb: (list bool)*(IndTrans.ConstructorInfo)) :=
  let (lb,cinfo) := lb in 
  let cretIndices := IndTrans.indices cinfo in
  let args := IndTrans.args cinfo in
  let caseTypRet := 
    ssubst_aux caseTypRet (combine indTypIndicVars cretIndices) in
  let mTyInfo := mkLamL (map primeArgsOld caseTypArgs) caseTypRet in
  let brsAndDefs := (map (translateIndInnerMatchBranch tind 
          indTypeParams_R
          (*indTypIndices_RR  *)
          indTypIndicVars caseTypRet)
         (combine lb lcargs)) in
  let branches := map fst brsAndDefs in
  let defs := flat_map snd brsAndDefs in 
    (* _RRs and _RRinvs for ONLY the constructor where the bool is true in b*)
  let lnt : list STerm := [mTyInfo; vterm (vprime v)] ++branches in
  (mkLamL (map removeSortInfo args) (oterm  o (map (bterm []) lnt)), defs).


(* before goodness has been fully generated, we need too remove the flags that inddicate
that A:Set and thus A's relation must be good, for A:= the mutual ind being processed now.
The index in tind is ignored *)

Definition mkConstrInfoBeforeGoodness (tind:inductive)
           (numParams : nat )(translate: STerm-> STerm) (constrTypes : list STerm) :=
      let constrTypes_R := map (translate ∘ headPisToLams ∘ (removeCastsInConstrType tind))
                               constrTypes in
      map (mkConstrInfo numParams) (numberElems constrTypes_R).

Section IndsFalse.
  Variable ienv: indEnv.
  Let translate := translate false ienv.
  
Definition translateIndMatchBody (numParams:nat) 
  tind v (caseTypArgs : list (V*STerm))(caseTypRet:  STerm) 
  (indTypeParams_R indTypIndices_RR : list Arg) (indTypIndicVars : list V)
  (constrTypes : list STerm): STerm * list defSq :=
  let numConstrs : nat := length constrTypes in
  let lcargs  := mkConstrInfoBeforeGoodness tind numParams translate constrTypes in
  let seq := (List.seq 0 numConstrs) in
  let cargsLens : list nat := map IndTrans.argsLen lcargs in
  let o := (CCase (tind, numParams) cargsLens) None in
  let lb : list (list bool):= map (boolNthTrue numConstrs) seq in
  let brsAndDefs :=
  (map (translateIndInnerMatchBody tind o lcargs v 
          caseTypArgs caseTypRet indTypeParams_R 
            indTypIndices_RR indTypIndicVars) (combine lb lcargs)) in
  let branches := map fst brsAndDefs in
  let defs := flat_map snd brsAndDefs in (* _RRs and _RRinvs for constructors *)
  let lnt : list STerm := [mkLamL caseTypArgs caseTypRet; vterm v]
      ++branches in
  (mkApp (oterm o (map (bterm []) lnt)) (map (vterm∘fst) indTypIndices_RR), defs).

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
(*                                 
                                 
  let typesRenamed := map snd l
      (*let sub := combine origVars (map vterm vars) in
      map (fun t => ssubst_aux (snd t) sub) l *)in
  combine vars typesRenamed.
 *)
                                 
(* generalize this to arbitrary n-ary dependent pairs. Because the indices here
were dependent on some of the params of the inductive type, we had to cast so that
the BestRs compute. 
Also, disable this in the final true mode where the indices may be in Type
 *)

Locate proof_irrelevance.
(* get the proof of this equality using proof irrelevance. The type must be a Prop *)
 
Definition proofIrrel_ref :ident := "Coq.Logic.ProofIrrelevance.proof_irrelevance".

Definition proofIrrelEqProofSq (e: EqType STerm) : STerm :=
  mkConstApp proofIrrel_ref [(eqType e); (eqLHS e); (eqRHS e)].

Definition translateOneInd_indicesInductive_irrel 
           (indTypArgs_R (* including indices *) indTypeIndices_RR: list (V*STerm))
           (tindi: (*indices*) inductive) (constName : ident)
  :  defSq :=
  
  let newIndicesRRVars := renameArgs (map fst indTypArgs_R) indTypeIndices_RR in
(*  let allArgs := indTypArgs_R ++ newIndicesRR in *)
(*  let allArgsOld := indTypArgs_R ++  indTypeIndices_RR in *)
  (* inside the matches, lies a beautiful world where the indices coincide *)
  let retTypCore := mkIndApp tindi (map (vterm ∘ fst) indTypArgs_R) in
(*  let retTypOuter := mkIndApp tindi (map (vterm ∘ fst) allArgs) in *)
  let bodyInner := mkApp (mkConstr tindi 0) (map (vterm ∘ fst) indTypArgs_R) in
  let rwf :=
      (* vars move from (map fst old) to doneVars as we recurs *)
      (fix rewriteIndRRs (old: list (V*STerm)) (newVars doneVars: list V)
          (t : STerm) {struct old}
       : (STerm (* ret *)
          * list (V*STerm) (* indTypeIndices_RR with new vars and accordingly substed types *)) :=
        match old, newVars with
        | (ov,oldT)::old, nv::newVars =>
          let eqt: EqType STerm :=
              {|eqType := oldT; eqLHS := (vterm ov); eqRHS := (vterm nv) |} in
          let peq := proofIrrelEqProofSq eqt in
          let newDoneVars := (snoc doneVars ov) in
          let (recRet, recArgss) :=
              rewriteIndRRs old newVars newDoneVars t in
          let recArgssSub := (ALMapRange
                            (fun t => ssubst_aux t [(ov, vterm nv)])
                            (recArgss)) in
          let newArgs :=  (nv,oldT)::recArgssSub in
          let retType := mkApp retTypCore (map vterm (doneVars++ (map fst newArgs))) in
          let transportP := mkLam nv oldT (mkPiL recArgssSub retType) in
          let ret :STerm :=
              let trRet :=
              match recArgss with
              | (vr,TR)::_ =>  (mkLam vr TR recRet)
(* at the top level, transport, there is no lambda. Inner indices depend on the
outer indices. so, there types have to be rewritten *)                                
              | _ => recRet
              end in
              mkTransport transportP eqt peq trRet in
          (ret, newArgs)
        | _,_ => (t,[])
        end)  indTypeIndices_RR newIndicesRRVars [] bodyInner in
  let '(ret ,newIndicesRR) := rwf in
  {| nameSq := constName;
     bodySq := mkLamL (indTypArgs_R ++ newIndicesRR)
                      (* tail, because the first index doesn't depend on previous indices *)
                      (mkApp ret (map vterm (tail newIndicesRRVars))) |}.
                  
   
(* generalize this to arbitrary n-ary dependent pairs. Because the indices here
were dependent on some of the params of the inductive type, we had to cast so that
the BestRs compute. *)
Definition translateOneInd_indicesInductive 
(indTypArgs_R (* including indices *) indTypeIndices_RR: list Arg)
(srt: STerm) (tind: inductive)
  :  list defIndSq
 :=
let allArgs := mrs (indTypArgs_R ++ indTypeIndices_RR) in
let indType := mkPiL allArgs srt in
let paramVars := map fst indTypArgs_R in 
  (* ensure that all of these have non-empty (unique?) names *)
let thisIndVar: V  := freshUserVar (freevars indType) "thisInd"  in
let ctype := mkApp (vterm thisIndVar) 
  ((map vterm paramVars)++ (map (vterm∘fst) indTypeIndices_RR)) (* no args *) in
let cbterm := bterm (thisIndVar::paramVars) ctype in
let tindiName := (indIndicesTransName tind) in 
let oneInd : simple_one_ind STerm SBTerm := 
    (tindiName, indType,  [(indIndicesConstrTransName tindiName, cbterm)]) in
let indIrrel : defSq :=
    let tindi := mkInd tindiName 0 in
    let indIndicesIrrelName := indIndicesIrrelTransName tind in
    translateOneInd_indicesInductive_irrel
      (mrs indTypArgs_R)
      (mrs indTypeIndices_RR)
      tindi
      indIndicesIrrelName in
                    
[inr (map snd paramVars, [oneInd]); inl indIrrel].

(** tind is a constant denoting the inductive being processed *)
Definition translateOneInd (numParams:nat) 
  (tind : inductive*(simple_one_ind STerm STerm)) : ((list Arg) * fixDef True STerm) * list defIndSq :=
  let (tind,smi) := tind in
  let (nmT, constrs) := smi in
  let (_, indTyp) := nmT in
  let indTyp_R := translate (headPisToLams indTyp) in
  let (srt, indTypArgs) := getHeadPIs indTyp in
  let (_, indTypArgs_R) := getNHeadLams (3*length indTypArgs) indTyp_R in
  let srt_R := 
    match srt with 
    | mkSort s => mkSort (translateSort s) 
    | _ => srt (* should never happen *)
    end in
  let indTypeIndices : list Arg := skipn numParams indTypArgs in
  let numParams_R :nat := (3*numParams)%nat in 
  let indTypeIndices_R : list Arg := skipn numParams_R indTypArgs_R in
  let indTypeParams_R : list Arg := firstn numParams_R indTypArgs_R in
  let (indTypeIndices_RR,_) := separate_Rs indTypeIndices_R in
  let indTypIndicVars : list V := map fst indTypeIndices in
  let srtMatch := mkPiL (map removeSortInfo indTypeIndices_RR) srt_R in
  let vars : list V := map fst indTypArgs in
  let t1 : STerm := (mkIndApp tind (map vterm vars)) in
  let t2 : STerm := (mkIndApp tind (map (vterm∘vprime) vars)) in
  (* local section variables could be a problem. Other constants are not a problem*)
  let v : V := fresh_var vars in
  let caseTypArgs : list (V*STerm) 
    := (snoc (map removeSortInfo indTypeIndices) (v,t1)) in
  let constrTypes := (map snd constrs) in
  let (mb, defs) := translateIndMatchBody numParams tind v caseTypArgs srtMatch 
  indTypeParams_R indTypeIndices_RR
  indTypIndicVars constrTypes in
  let fArgs : list (V*STerm) := ((mrs indTypeIndices_R)++[(v,t1); (vprime v, t2)]) in
  let fbody := mkLamL fArgs mb   in
  let ftyp: STerm := mkPiL fArgs srt_R in
  let rarg : nat := length indTypeIndices_R in
  let indicesInductive :=
  translateOneInd_indicesInductive indTypArgs_R indTypeIndices_RR srt_R tind in 
  (indTypeParams_R,{|fname := I ; ftype := (ftyp,None); fbody := fbody; structArg:= rarg |}, 
    indicesInductive++ map inl defs).


Definition translateMutInd (id:ident) (t: simple_mutual_ind STerm SBTerm) (i:nat)
  : STerm * list defIndSq := 
  mutIndToMutFixAux false (translateOneInd) id t i.

End IndsFalse.




Definition castTerm  (ienv : indEnv) (typ: V*STerm) : STerm  :=
  let (v,typ) := typ in
  let typ := headPisToLams typ in
  let (ret, args) := getHeadLams typ in
  let typ_R := translate true ienv typ in
  let (_, args_R) := getNHeadLams (3*(length args)) typ_R in
  match ret with
  | mkSort s =>
    if (negb (isPropOrSet s)) then vterm (vrel v) else
    let bestrT1 := mkApp (vterm v) (map (vterm ∘ fst) args) in
    let bestrT2 := tprime bestrT1 in
    (* this is a bug? vrel needs to be applied ? *)
    let vrapp := mkApp (vterm (vrel v)) (map (vterm ∘ fst) args_R) in
    mkLamL (mrs args_R) (projTyRel bestrT1 bestrT2 vrapp)
  | _ => vterm (vrel v)
  end.

Definition transArgWithCast (ienv : indEnv) (nma : Arg) : (list (V * STerm * STerm)):=
  let (nm,A1s) := nma in
  let A1 := fst A1s in
  let A2 := tprime A1 in
  let nmp := vprime nm in
  let nmr := vrel nm in
  let AR := castIfNeeded true A1s  A2 (translate true ienv A1) in
  [(nm, A1, vterm nm);
   (nmp, A2, vterm nmp);
   (nmr, mkAppBeta AR [vterm nm; vterm (vprime nm)], castTerm ienv (removeSortInfo nma))].

Definition mkIndTransPacket (iso:bool) (ienv: indEnv)
           (numParams:nat) 
           (tind : inductive*(simple_one_ind STerm STerm)) :
  IndTrans.IndInfo :=
  let (tind,smi) := tind in
  let (nmT, constrs) := smi in
  let constrTypes := map snd constrs in
  let (_, indTyp) := nmT in
  let (retSort, indTypArgs) := getHeadPIs indTyp in
  let indTyp_R := translate iso ienv (headPisToLams indTyp) in
  let (retSort_R, indTypArgs_R) := getNHeadLams (3*length indTypArgs) indTyp_R  in
  let indTypArgs_RM := TranslatedArg.unMerge3way  indTypArgs_R in
  {|
     IndTrans.numParams :=  numParams;
     IndTrans.tind := tind;
     IndTrans.constrInfo_R :=  mkConstrInfoBeforeGoodness
                                 tind
                                 numParams
                                 (translate iso ienv)
                                 constrTypes ;
     IndTrans.indArgs_R := indTypArgs_RM;
     IndTrans.retSort := retSort;
     IndTrans.retSort_R := retSort_R;
     IndTrans.castedArgs_R :=
      let args := flat_map (transArgWithCast ienv) indTypArgs in
      map snd args
  |}.

Definition extractGoodRelFromApp  (t_RApp (* BestR A1 A2 AR a1 a2 *):STerm):=
  (* need to return AR *)
  let (_, args) := flattenApp t_RApp [] in
  nth 2 args (oterm (CUnknown "extractGoodRelFromApp") []).

Definition goodijNonRec (consName : ident)
           (typ : TranslatedArg.T Arg) : STerm:=
  let args := [argType (TranslatedArg.arg typ);
                 argType (TranslatedArg.argPrime typ);
                 ((extractGoodRelFromApp ∘ argType) (TranslatedArg.argRel typ))
              ] in
mkConstApp consName args.

(* TODO: use [goodijNonRec] from above *)
Definition totIJConst (consNames : ident*ident)
           (typ : TranslatedArg.T Arg) (ti : STerm) : (STerm (*t2*)* STerm (*tr*)):=
  let (idij, idijr) := consNames in
  let args := [argType (TranslatedArg.arg typ);
                 argType (TranslatedArg.argPrime typ);
                 ((extractGoodRelFromApp ∘ argType) (TranslatedArg.argRel typ)) ;ti
              ] in
(mkConstApp idij args, 
mkConstApp idijr args).



  Definition totConst  (b21 : bool) :=
    if b21 then
  ("ReflParam.Trecord.BestTot21",  "ReflParam.Trecord.BestTot21R")
      else
        ("ReflParam.Trecord.BestTot12",  "ReflParam.Trecord.BestTot12R").

Section IndTrue.
  Variable (b21 : bool).
(* give [ret: BaseType cIndices],
   It returns a term of type [BaseType (map (vterm ∘ snd) retArgs)]
   DoneIndices is initially [], and items shift from the front of [cIndices] 
   to the back of donIndices.
   The types of RetArgs are OneToOne, which is used to produce the equality proofs.
   The type of later indices may depend on the former indices. Therefore,
   these rewrites have to be carefully threaded
*)
Fixpoint mkOneOneRewrites (oneConst:ident) (retArgs : list (V*STerm*V))
         (doneIndices : list STerm)
         (cIndices : list (STerm (* js *) * STerm (* rels *)))
         (baseType ret: STerm) {struct retArgs} : STerm :=
  match (retArgs, cIndices) with
  | (hi::retArgs, (hcp,hcr)::cIndices) =>
    let (hi, vPrimehi) := hi in
    let (vRhi , Thi) := hi in
    let (_ (* BestR *), ThiArgs (* 5 items *)) := flattenApp Thi [] in
    let peq := mkConstApp oneConst (ThiArgs++[hcp; vterm vRhi; hcr]) in
    let transportType :=
        let tindex : nat := (if b21 then 0 else 1)%nat in 
        nth tindex ThiArgs (oterm (CUnknown "mkOneOneRewrites") []) in
    let eqT := {| eqType := transportType;  eqLHS := hcp;  eqRHS := vterm vPrimehi |} in
    let rep1 := replaceOccurrences hcp (vterm vPrimehi) in
    let rep2 := replaceOccurrences hcr (vterm vRhi) in
    let cIndices := map (fun p => ((rep1 ∘ fst) p, (rep1 ∘ rep2 ∘ snd) p)) cIndices in
    let transportP :=
        let base := mkAppBetaUnsafe baseType (doneIndices++[vterm vPrimehi]++(map fst cIndices)) in
        mkLam vPrimehi transportType base in
    let rw := mkTransport transportP eqT peq ret in
    mkOneOneRewrites oneConst retArgs
                     (snoc doneIndices (vterm vPrimehi))
                     cIndices baseType rw
  | _ => ret
  end.

Let maybeSwap {A:Set} (p:A*A) := (if b21 then (snd p, fst p) else p).
  Let targi {A}  := if b21 then @TranslatedArg.argPrime A else @TranslatedArg.arg A.
  Let targj {A}  := if b21 then @TranslatedArg.arg A else @TranslatedArg.argPrime A.
  Definition oneOneConst := if b21 then "ReflParam.Trecord.BestOne21"
                     else "ReflParam.Trecord.BestOne12".

  Definition oneOneConstijjo := if b21 then "ReflParam.Trecord.BestOneijjo21"
                     else "ReflParam.Trecord.BestOneijjo".

  Definition totalPiConst := if b21 then totalPiHalfGood21_ref else totalPiHalfGood_ref.
  Definition oneOnePiConst := if b21 then oneOnePiHalfGood21_ref else oneOnePiHalfGood_ref.

  Definition mkTotalPiHalfGood (A1 A2 AR B1 B2 BR BtotHalf: STerm) :=
    mkConstApp totalPiConst [A1;A2;AR;B1;B2;BR;BtotHalf].

  Definition mkOneOnePiHalfGood (A1 A2 AR B1 B2 BR BtotHalf: STerm) :=
    mkConstApp oneOnePiConst [A1;A2;AR;B1;B2;BR;BtotHalf].

  Definition totij (typ : TranslatedArg.T Arg) (ti : STerm) : (STerm (*tj*)* STerm (*tr*)):=
    totIJConst (totConst b21) typ ti.

  Definition totji (typ : TranslatedArg.T Arg) (ti : STerm) : (STerm (*tj*)* STerm (*tr*)):=
    totIJConst (totConst (negb b21)) typ ti.

  Variable ienv: indEnv.
  Let translate := translate true ienv.

  
  Definition recursiveArgIff (p:TranslatedArg.T Arg) (numPiArgs:nat) t :=
      let procLamArgOfArg (p:TranslatedArg.T Arg) (t:STerm): STerm:=
        let (T1InAux,T2InAux, TRIn) := p in
        let (TIni, TInj) := maybeSwap (T1InAux,T2InAux) in
        let tji := totji p (vterm (argVar TInj)) in
        mkLetIn (argVar TIni) (fst tji) (argType TIni)
          (mkLetIn (argVar TRIn) (snd tji)  (* typ to t1 *)
              (argType TRIn) t) in
      let (T11,T22,_) := p in
      let (Ti, Tj) := maybeSwap (T11, T22) in
      let T1lR := (translate(*f*) (headPisToLams (argType T11))) in
      let (ret_R, lamArgs_R) := getNHeadLams (3*numPiArgs) T1lR in
      let lamArgs_R := TranslatedArg.unMerge3way lamArgs_R in
      let recCall : STerm := flattenHeadApp ret_R in (* not needed? *)
      let (vi,vj) := (argVar Ti,argVar Tj) in
      let fi : STerm := vterm vi in
      let recArg : STerm := mkApp fi (map (vterm∘fst∘targi) lamArgs_R) in
      let recRet := (mkApp recCall [recArg]) in
      let retIn := List.fold_right procLamArgOfArg recRet lamArgs_R in
      let retIn := mkLamL (map (removeSortInfo ∘ targj) lamArgs_R) retIn in
      mkLetIn vj retIn (argType Tj) t.
(* (vrel v) is not needed. indices of a constr cannot mention rec args.
onenote:https://d.docs.live.net/946e75b47b19a3b5/Documents/Postdoc/parametricity/papers/logic/isorel.one#indices%20of%20a%20constr%20cannot%20mention%20rec%20args&section-id={6FC701EE-23A1-4695-AC21-2E6CBE61463B}&page-id={A96060FB-9EFC-4F21-8C1C-44E1B3385424}&end
*)

  
  (* returns 1) the correct translation relation for the Pi Type. Note that just
  [argType] is not the correct relation, because it uses _iso, which is rebound here to
  something else (iso hasn't been even fully generated yet). Also, params need to be casted
  as this function does in the base case.
  2) the half totality proof. *)
  Fixpoint recursiveArgPiCombinator
           (gPiCombinator : STerm -> STerm -> STerm -> STerm -> STerm -> STerm -> STerm -> STerm)
           (castedParams_R : list STerm) (argType1: STerm)  : (STerm*STerm):=
    match argType1 with
    | mkPiS nm A Sa B _ =>
      let A2 := (tprime A) in
      let AR := (translate A) in 
      let brtot := gPiCombinator A A2 AR in
      let Bl1 := (mkLam nm A B) in
      let Bl2 := (tprime Bl1) in
      let brtot := brtot Bl1 Bl2  in
      let (recbr, recbrtot) := recursiveArgPiCombinator gPiCombinator
                                                  castedParams_R B in
      let lrecbr := transLam true translate (nm,(A,Sa)) recbr in
      let lrecbrtot := transLam true translate (nm,(A,Sa)) recbrtot in 
      let brtot := brtot lrecbr lrecbrtot in
        (mkRPiS A A2 (castIfNeeded true (A,Sa) A2 AR) Bl1 Bl2 lrecbr, brtot)
    | _ =>
      (* cast is removed because this is a recursive arg of the constructor *)
      let argType_Rtot := translate argType1 in (* argType translate the current inductive to the 
_iso name , which will be replaced with the fixpoint var binding this fixpoint. 
We want this for brtothalf but not BR *)
      let argType_R :=
          let tind_RR (* not the iso version *) :=
              let (indt, args) := flattenApp argType1 [] in
              let tind := extractInd indt in
              indTransName tind in (* we will use this name instead of the _iso version *)
          (* Also, we use  castedParams_R, because (indTransName tind) is the core (non-good) version *)
          let (_, args_R) := flattenApp  argType_Rtot [] in
          let args_R := skipn (length castedParams_R) args_R in
          mkConstApp tind_RR (castedParams_R++args_R) in
      ( argType_R, argType_Rtot)
    end.

  Definition recursiveArgTot (castedParams_R : list STerm) (p:TranslatedArg.T Arg)
             (t: STerm) :=
      let (T11,T22,TR) := p in
      let (Ti,Tj) := maybeSwap (T11, T22) in
       let (vi,vj) := (argVar Ti, argVar Tj) in
      let fi: STerm := vterm vi in
      let vr :V := (argVar TR) in
      let (TR,pitot) := (recursiveArgPiCombinator mkTotalPiHalfGood
                                            castedParams_R (argType T11)) in
      let fjr: STerm := (mkApp pitot [fi]) in
      let fjType: STerm := argType Tj in
      let trApp: STerm := (mkApp TR (map (vterm ∘ argVar)[T11;T22])) in
      let fjrType: STerm :=
          mkSig (argVar Tj) (argType Tj) trApp in
      let frType : STerm :=
          mkLam (argVar Tj) (argType Tj) trApp in
      let body: STerm :=
          mkLetIn vr
                  (mkConstApp projT2_ref [fjType; frType; vterm vr])
                  trApp t in
      let body: STerm :=
          mkLetIn (argVar Tj)
                  (mkConstApp projT1_ref [fjType; frType; vterm vr])
                  (argType Tj) body in
      mkLetIn vr fjr fjrType body.

  Definition cretIndicesij  ( cinfo_RR : IndTrans.ConstructorInfo) :=
      maybeSwap (IndTrans.indices cinfo_RR, IndTrans.indicesPrimes cinfo_RR).

  Definition indIndicesij  (indPacket : IndTrans.IndInfo) :=
  let indIndices := IndTrans.indIndices_R indPacket in
      maybeSwap (mrs (map TranslatedArg.arg indIndices),
                 mrs (map TranslatedArg.argPrime indIndices)).

  Definition translateOnePropBranch  (iffOnly:bool (* false => total*))
             (* v : the main (last) input to totality *)
             (ind : inductive) (totalTj: STerm) (vi vj :V) (params: list Arg)
             (castedParams_R : list STerm)
           (indIndicess indPrimeIndicess indRelIndices : list (V*STerm))
           (indAppParamsj: STerm)
  (cinfo_RR : IndTrans.ConstructorInfo): STerm := 
  let constrIndex :=  IndTrans.index cinfo_RR in
  let constrArgs_R := IndTrans.args_R cinfo_RR in
  let procArg  (p: TranslatedArg.T Arg) (t:STerm): STerm:=
    let (T11, T22,TR) := p in
    let (Ti, Tj) := maybeSwap (T11, T22) in  
    let isRec :=  (isConstrArgRecursive ind (argType Ti)) in
    if isRec
    then
      (if iffOnly
       then recursiveArgIff p (numPiArgs (argType Ti)) t
       else recursiveArgTot castedParams_R p t)
    else
      mkLetIn (argVar Tj) (fst (totij p (vterm (argVar Ti)))) (argType Tj)
        (mkLetIn (argVar TR) (snd (totij p (vterm (argVar Ti)))) 
                 (argType TR) t) in
  (* todo : use IndTrans.thisConstr *)
  let c11 := mkApp (mkConstr ind constrIndex) (map (vterm∘fst) params) in
  let c11 := mkApp c11 (map (vterm∘fst∘TranslatedArg.arg) constrArgs_R) in
  let c22 := tprime c11 in
  let (ci, cj) := maybeSwap (c11, c22) in
  let (indicesIndi, indicesIndj) := maybeSwap (indIndicess,indPrimeIndicess) in
  let (cretIndicesi, cretIndicesj) :=
      maybeSwap (IndTrans.indices cinfo_RR, IndTrans.indicesPrimes cinfo_RR) in
  let thisBranchSubi :=
      (* specialize the return type to the indices. later even the constructor is substed*)
      (combine (map fst indicesIndi) cretIndicesi) in
  let indRelIndices : list (V*STerm) :=
      ALMapRange (fun t => ssubst_aux t thisBranchSubi) indRelIndices in
  (* after rewriting with oneOnes, the indicesPrimes become (map tprime cretIndices)*)
  let thisBranchSubj :=  (combine (map fst indicesIndj) cretIndicesj) in
  let indRelArgsAfterRws : list (V*STerm) :=
      ALMapRange (fun t => ssubst_aux t thisBranchSubj) indRelIndices in
  let (c2MaybeTot, c2MaybeTotBaseType) :=
      if iffOnly
      then (cj,indAppParamsj)
      else
        let thisBranchSubFull := snoc thisBranchSubi (vi, ci) in
        let retTRR := ssubst_aux totalTj (thisBranchSubFull) in
        let retTRRLam := mkLamL indicesIndj (mkPiL indRelIndices retTRR)  in
        let crr :=
            mkConstApp (constrTransTotName ind constrIndex)
                       (castedParams_R
                          ++(map (vterm ∘ fst)
                                 (TranslatedArg.merge3way constrArgs_R))
                          ++ (map (vterm ∘ fst) indRelIndices)) in
        (mkLamL
           indRelArgsAfterRws
           (sigTToExistT2 [cj] crr (ssubst_aux retTRR thisBranchSubj))
         ,retTRRLam) in
  (* do the rewriting with OneOne *)
  let c2rw :=
      let cretIndicesJRRs := combine cretIndicesj
                                    (IndTrans.indicesRR cinfo_RR) in
      mkOneOneRewrites oneOneConst
                       (combine indRelIndices (map fst indicesIndj))
                       []
                       cretIndicesJRRs
                       c2MaybeTotBaseType
                       c2MaybeTot in
  let c2rw := if iffOnly then c2rw else mkApp (c2rw) (map (vterm ∘ fst) indRelIndices) in
  let ret := List.fold_right procArg c2rw constrArgs_R in
  mkLamL ((map (removeSortInfo ∘ targi) constrArgs_R)
            ++(indicesIndj++ indRelIndices)) ret.

  
  (* TODO: use mkIndTranspacket to cut down the boilerplate *)
(** tind is a constant denoting the inductive being processed *)
Definition translateOnePropTotal (iffOnly:bool (* false => total*))
           (numParams:nat)
           (tind : inductive*(simple_one_ind STerm STerm)) : (list Arg) * fixDef True STerm :=
  let (tind,smi) := tind in
  let (nmT, constrs) := smi in
  let constrTypes := map snd constrs in
  let (_, indTyp) := nmT in
  let (_, indTypArgs) := getHeadPIs indTyp in
  let indTyp_R := translate(*f*) (headPisToLams indTyp) in
  let (_, indTypArgs_R) := getNHeadLams (3*length indTypArgs) indTyp_R  in
  let indTypArgs_RM := TranslatedArg.unMerge3way  indTypArgs_R in
  let indTypeParams : list Arg := firstn numParams indTypArgs in
  let indTypeIndices : list (V*STerm) := mrs (skipn numParams indTypArgs) in
  let indTypeParams_R : list Arg := firstn (3*numParams) indTypArgs_R in
  let indTypeIndices_R : list Arg := skipn (3*numParams) indTypArgs_R in
  let vars : list V := map fst indTypArgs in
  let indAppParamsj : STerm :=
      let indAppParams : STerm := (mkIndApp tind (map (vterm ∘ fst) indTypeParams)) in
      if b21 then indAppParams else tprime indAppParams in
  let (Ti, Tj) :=
        let T1 : STerm := (mkIndApp tind (map vterm vars)) in
        let T2 : STerm := tprime T1 in maybeSwap (T1,T2) in
  let vv : V := freshUserVar vars "tind" in
  let (vi,vj) := maybeSwap (vv, vprime vv) in
  let (totalTj, castedParams_R)   :=
      let args := flat_map (transArgWithCast ienv) indTypArgs in
      let args := map snd args in
      (mkSig vj Tj (mkConstApp (indTransName tind)
                         (args++[vterm vv; vterm (vprime vv)]))
       , firstn (3*numParams) args)  in
  let retTyp : STerm :=
      if iffOnly then Tj else totalTj in
  let indTypeIndices_RM := skipn  numParams  indTypArgs_RM in
  (* why are we splitting the indicesPrimes and indices_RR? *)
  let indPrimeIndices :=  map (removeSortInfo ∘ TranslatedArg.argPrime) indTypeIndices_RM in
  let indRelIndices :=  map (removeSortInfo ∘ TranslatedArg.argRel) indTypeIndices_RM in
  let (caseArgsi, caseArgsj) := maybeSwap (indTypeIndices, indPrimeIndices) in
  let caseRetAllArgs :=  (caseArgsj++indRelIndices) in
  let caseRetTyp := mkPiL caseRetAllArgs  retTyp in
  let caseTyp := mkLamL (snoc caseArgsi (vi,Ti)) caseRetTyp in
  let cinfo_R := mkConstrInfoBeforeGoodness tind numParams translate constrTypes in 
  let o :=
      let cargsLens : list nat := (map IndTrans.argsLen  cinfo_R) in
      (CCase (tind, numParams) cargsLens) None in
  let matcht :=
      let lnt : list STerm := [caseTyp; vterm vi]
                                ++(map (translateOnePropBranch
                                          iffOnly
                                          tind
                                          totalTj
                                          vi
                                          vj
                                          indTypeParams
                                          castedParams_R
                                          indTypeIndices
                                          indPrimeIndices
                                          indRelIndices
                                          indAppParamsj)
                                   cinfo_R) in
      oterm o (map (bterm []) lnt) in
  let matchBody : STerm :=
      mkApp matcht (map (vterm ∘ fst)  (caseArgsj++indRelIndices)) in
  (* todo, do mkLamL indTypArgs_R just like transOneInd *)
  let fixArgs :=  ((mrs (indTypeIndices_R))) in
  let allFixArgs :=  (snoc fixArgs (vi,Ti)) in
  let fbody : STerm := mkLamL allFixArgs (matchBody) in
  let ftyp: STerm := mkPiL allFixArgs retTyp in
  let rarg : nat := ((length fixArgs))%nat in
  (indTypeParams_R, {|fname := I; ftype := (ftyp, None); fbody := fbody; structArg:= rarg |}).



(* Move *)
Definition nAppend (s:ident) (n : name) := 
 match n with
 | nAnon => nNamed s
 | nNamed ss => nNamed (String.append ss s)
 end.

      
(** OneToOne hood *)

(** We need 2 vars of the J and RR classes. These are obtained
by adding a large enough number, and appending "o".
This operation is done after doing vprime/vrel if neccessary  *)
Definition extraVar (add :N) (v:V):=
  (add+fst v, nAppend "o" (snd v)).


Definition pairMapl {A B A2:Type} (f: A-> A2) (p:A*B) : A2*B :=
  let (a,b) := p in (f a, b).

Definition pairMapr {A B B2:Type} (f: B-> B2) (p:A*B) : A*B2 :=
  let (a,b) := p in (a, f b).

Definition injpair2_ref:=
(*  "EqdepTheory.inj_pair2". *)
 "Coq.Logic.ProofIrrelevance.ProofIrrelevanceTheory.EqdepTheory.inj_pair2".

(* The last item is guaranteed to be a var. So, only the sigt applies will be 
recursed over *)
Fixpoint sigTToInjPair2 (existTL existTR : STerm) (exEq:V)
  {struct existTL} : STerm :=
match existTL, existTR  with
| (oterm (CApply _) lbt1), (oterm (CApply _) lbt2)  =>
  match lbt1, lbt2 with
  (_::A::B::x::p1::[]), (_::_::_::_::p2::[])=>
  let A:= get_nt A in  
  let B:= get_nt B in  
  let x:= get_nt x in  
  let p1:= get_nt p1 in  
  let p2:= get_nt p2 in  
  let eqproj2 :=  mkConstApp injpair2_ref  [A; B; x; p1; p2; (vterm exEq)] in
  let letType :=
      let eqt : EqType STerm :=
          {|
            eqType := mkApp B [x];
            eqLHS := p1;
            eqRHS := p2
          |} in
      getEqTypeSq eqt in
  mkLetIn exEq eqproj2 letType (sigTToInjPair2 p1 p2 exEq)
  | _,_ => vterm exEq
  end
| _,_ => vterm exEq
end.

(* TODO: move to SquiggleEq, and optimize it (if so, prove correct) bu directly opeerating
over the vars and not calling ssubst_aux *)
Definition ssubst_auxv (subv : list (V*V)) (t:STerm):=
  ssubst_aux t (map (fun p:(V*V) => let (vs,vt):=p in (vs, vterm vt)) subv).

Definition argsVarf (f:V->V) (args: list (V*STerm)) :
  (list (V*STerm)) * (list (V*V)) :=
  let argsf := ALMapDom f args in
  let sub := combine (map fst args) (map fst argsf) in
  (ALMapRange (ssubst_auxv sub) argsf , sub).

(*
Fixpoint letBindProj1s (l: list (V*STerm)) (v:V) (t:STerm) {struct l} : STerm :=
*)
Definition oneOneConstrArgCombinator
           (indPacket : IndTrans.IndInfo) (carg : TranslatedArg.T Arg) :
  (V*STerm (*Type_R*) * STerm (*OneOne combinator *)):=
    let (T1, T2,TR) := carg in
    let isRec :=  (isConstrArgRecursive (IndTrans.tind indPacket) (argType T1)) in
    if isRec
    then
      let (TRCorrect, TOneOneComb) :=
          recursiveArgPiCombinator
            mkOneOnePiHalfGood
            (IndTrans.castedParams_R indPacket)
            (argType T1) in
      (fst TR, mkApp TRCorrect [vterm (argVar T1); vterm (argVar T2)] , TOneOneComb)
    else
      (removeSortInfo TR, goodijNonRec oneOneConstijjo carg).
  

Fixpoint oneBranch3Rewrites (oneCombinators : list STerm)
         (cargsRRo cargsjo: list (V*STerm)) (* types keep changing *)
         (revSubj revSubRR : list V)  (* remains constant *)
         (retTypeBase (* keeps changing during recursion *): STerm)
         (lcargvi : list V) (* remains constant *)
         (eqReflBaseCase : STerm) (* remains constant *)
  : STerm  :=
  match oneCombinators, cargsRRo, cargsjo, revSubj, revSubRR, lcargvi with
  | oneComb::oneCombinators, cr::cargsRR, cargjo::cargsjo, vj::revSubj,
    vrr::revSubRR, vi::lcargvi =>
    let vjo := fst cargjo in
    let vrro := fst cr in
    let outerRW (t: STerm) : STerm :=
      let eqT :=
        {|
          eqType := snd cargjo;
          eqLHS := vterm vj;
          eqRHS := vterm vjo
        |} in
      let peq := mkApp oneComb [vterm vi; vterm vj; vterm vjo; vterm vrr; vterm vrro] in
        (* we need to change the type of cr. so we convoy it *)
      let transportP := (mkPiL (cr::(merge cargsjo cargsRR)) retTypeBase) in
      mkLamL [cargjo;cr]
             (mkApp (mkTransportV vjo transportP eqT peq t) [vterm (fst cr)]) in
    let subj := [(vjo,vj)] in
    let cr := pairMapr (ssubst_auxv subj) cr in
    let cargsRR := ALMapRange (ssubst_auxv subj) cargsRR in
    let cargsjo := ALMapRange (ssubst_auxv subj) cargsjo in
    let retTypeBase := ssubst_auxv subj retTypeBase in
    let innerRW (t:STerm): STerm :=
      let eqT :=
        {|
          eqType := snd cr;
          eqLHS := vterm vrr;
          eqRHS := vterm vrro 
        |} in
      let peq := proofIrrelEqProofSq eqT in
      let transportP := (mkPiL (merge cargsjo cargsRR) retTypeBase) in
        (* we need to change the type of cr. so we convoy it *)
      mkLamL [cr] (mkTransportV vrro transportP eqT peq t) in
    let recCall : STerm :=
      let cargsRR := ALMapRange (ssubst_auxv [(vrro,vrr)]) cargsRR in
      oneBranch3Rewrites
        oneCombinators
        cargsRR
        cargsjo
        revSubj
        revSubRR
        retTypeBase
        lcargvi
        eqReflBaseCase in
    outerRW (innerRW recCall)
  | _,_,_,_,_,_ => eqReflBaseCase
  end.
                                            
  
Definition translateOneBranch3 (o : CoqOpid (*to avoid recomputing*))
           (indPacket : IndTrans.IndInfo) (vhexeq : V) (maxbv :N)
           (vtti vttj vttjo tindAppR tindAppRo : (V*STerm))
           ((*retTyp*) retTypFull: STerm)
           (indIndicesi indIndicesj indIndicesRel : list (V*STerm))
           (*cretIndicesi cretIndicesj (* cretIndicesj for outerConstrIndex*) : list STerm *)
           (outerConstrIndex : nat) (* use False_rect for all other constructors*)
           (cargCombinators : list  (V*STerm (*Type_R*) * STerm (*OneOne combinator *)))
           (constrInv eqReflBaseCase: STerm)
           (cinfo_R : IndTrans.ConstructorInfo): STerm := 
  let (_, cretIndicesj) := cretIndicesij cinfo_R in
  let lamcjArgs := (map (removeSortInfo ∘ targj) (IndTrans.args_R cinfo_R)) in
  let (lamcjoArgs,varjosub)  := argsVarf (extraVar maxbv) lamcjArgs in
  let cretIndicesj : list STerm := map (ssubst_auxv varjosub) cretIndicesj in
  let c11 := IndTrans.thisConstructor indPacket cinfo_R in
  let (_,cj) := maybeSwap (c11, tprime c11) in (* make a maybeprime? *)
  let cj := ssubst_auxv varjosub cj in
  let thisBranchSubjFull :=
      snoc (combine (map fst indIndicesj) cretIndicesj) (fst vttjo, cj) in
  let subFullF :=  (fun t => ssubst_aux t thisBranchSubjFull) in
  let (cargsRR, oneCombinators) := split cargCombinators in
  let '(cargsRRo,cargsRRoSub)  := argsVarf (extraVar maxbv) cargsRR in
  let cargsRRo := ALMapRange (ssubst_auxv varjosub) cargsRRo in
  let tindAppRo := pairMapr subFullF tindAppRo in
  let retTypFull := ssubst_aux retTypFull thisBranchSubjFull  in
  let (retTypBody,retTypArgs) := getHeadPIs retTypFull in
  let lamAllArgs :=
      lamcjoArgs++ (mrs retTypArgs) in
  let ret := if (decide (outerConstrIndex = (IndTrans.index cinfo_R)))
    then
      let constrInvf :=
        let indIndicesRelS := ALMapRange subFullF indIndicesRel in
        let lamIArgs :=  (snoc indIndicesRelS tindAppRo) in
        let constrInvRetType :=
            mkLamL lamIArgs (*vacuous bindings*) retTypBody in
        let constrInv := ssubst_auxv varjosub constrInv in
        (* RRs remain the same when switching direction*)
        let body := oneBranch3Rewrites
                      oneCombinators
                      cargsRRo
                      lamcjoArgs
                      (map fst varjosub)
                      (map fst cargsRRoSub)
                      retTypBody
                      (map (fst ∘ targi) (IndTrans.args_R cinfo_R))
                      eqReflBaseCase in
        let body := mkLamL cargsRRo
                           (mkApp body (merge
                                          (map (vterm ∘ fst) lamcjoArgs)
                                          (map (vterm ∘ fst) cargsRRo))) in
        mkApp constrInv
              ((map (vterm ∘ fst) lamIArgs)
                 ++[constrInvRetType;body])
              in constrInvf
    else
      falseRectSq retTypBody (vterm (fst tindAppRo)) in
  mkLamL lamAllArgs ret.
  


Definition translateOneBranch2 (o : CoqOpid (*to avoid recomputing*))
           (indPacket : IndTrans.IndInfo) (vhexeq : V) (maxbv :N)
           (vtti vttj vttjo tindAppR tindAppRo : (V*STerm))
           ((*retTyp*) retTypFull: STerm)
           (indIndicesi indIndicesj indIndicesRel : list (V*STerm))
           (*cretIndicesi cretIndicesj (* cretIndicesj for outerConstrIndex*) : list STerm *)
           (outerConstrIndex : nat) (* use False_rect for all other constructors*)
           (cinfo_R : IndTrans.ConstructorInfo): STerm :=
  let (_, cretIndicesj) := cretIndicesij cinfo_R in
  let c11 := IndTrans.thisConstructor indPacket cinfo_R in
  let (_,cj) := maybeSwap (c11, tprime c11) in (* make a maybeprime? *)
  let thisBranchSubjFull :=
      snoc (combine (map fst indIndicesj) cretIndicesj) (fst vttj, cj) in
  let subFullF :=  (fun t => ssubst_aux t thisBranchSubjFull) in
  let retTypFull := ssubst_aux retTypFull thisBranchSubjFull  in
  let tindAppR := pairMapr subFullF tindAppR in
  let (retTypBody,retTypArgs) := getHeadPIs retTypFull in
  let lamAllArgs :=
      let lamcjArgs := (map (removeSortInfo ∘ targj) (IndTrans.args_R cinfo_R)) in
      lamcjArgs++ (mrs retTypArgs) in
  let ret := if (decide (outerConstrIndex = (IndTrans.index cinfo_R)))
  then
    let sigjType : STerm :=
        let sigType := IndTrans.sigIndApp indPacket in
        if b21 then sigType else tprime sigType in
    let eqT : EqType STerm := {|
          eqType := sigjType;
          eqLHS := sigTToExistT2 cretIndicesj cj sigjType;
          eqRHS := sigTToExistT2 cretIndicesj (vterm (fst vttjo)) sigjType
        |} in
    let eqt :STerm := getEqTypeSq eqT in
    let injPair2:= sigTToInjPair2 (eqLHS eqT) (eqRHS eqT) vhexeq  in
    let caseRetPiArgs :=  (snoc indIndicesRel tindAppRo) in
    let cargCombinators :=
         map (oneOneConstrArgCombinator indPacket) (IndTrans.args_R cinfo_R) in
    let constrInv :=  IndTrans.constrInvApp indPacket cinfo_R in
    let match3 :=
        let eqTG : EqType STerm := {|
              eqType := eqType eqT;
              eqLHS := eqLHS eqT;
              eqRHS := (sigTToExistT (vterm (fst vttjo)) sigjType)
            |} in
        let eqReflBase:= getEqRefl eqTG in
        let lamArgs := snoc indIndicesj vttjo in
        let retTypFull := (mkPiL caseRetPiArgs (getEqTypeSq eqTG)) in
        let caseRetTyp := mkLamL lamArgs retTypFull  in
        let lnt3 := map (translateOneBranch3 o
                         indPacket
                         vhexeq
                         maxbv
                         vtti
                         vttj
                         vttjo
                         tindAppR
                         tindAppRo
                         retTypFull
                         indIndicesi
                         indIndicesj
                         indIndicesRel
                         (IndTrans.index cinfo_R)
                         cargCombinators
                         constrInv
                         eqReflBase
                        )
                 (IndTrans.constrInfo_R indPacket) in
        oterm o (map (bterm []) ([caseRetTyp; vterm (fst vttjo)]++lnt3)) in
    let match3App := (mkApp match3 (map (vterm ∘ fst) caseRetPiArgs)) in
    let constrInvf :=
        let indIndicesRelS := ALMapRange subFullF indIndicesRel in
        let lamIArgs :=  (snoc indIndicesRelS tindAppR) in
        let constrInvRetType :=
            mkLamL lamIArgs (*vacuous bindings*) eqt in
        (* RRs remain the same when switching direction*)
        let cargsRR := (map fst cargCombinators)  in
        mkApp constrInv
              ((map (vterm ∘ fst) lamIArgs)
                 ++[constrInvRetType;mkLamL cargsRR match3App]) in
    mkLetIn vhexeq constrInvf eqt injPair2
  else
    falseRectSq retTypBody (vterm (fst tindAppR)) in
  mkLamL lamAllArgs ret.
                 
                                                    
Definition translateOneBranch1 (o : CoqOpid (*to avoid recomputing*))
           (indPacket : IndTrans.IndInfo) (vhexeq : V) (maxbv :N)
           (vtti vttj vttjo tindAppR tindAppRo : (V*STerm))
           (retTypFull: STerm)
           (indIndicesi indIndicesj indIndicesRel: list (V*STerm))
           (cinfo_R : IndTrans.ConstructorInfo): STerm :=
  let (cretIndicesi, _) := cretIndicesij cinfo_R in
  let c11 := IndTrans.thisConstructor indPacket cinfo_R in
  let (ci,_) := maybeSwap (c11, tprime c11) in
  let thisBranchSubiFull :=
      snoc (combine (map fst indIndicesi) cretIndicesi) (fst vtti, ci) in
  let retTypFull := mkPiL [vttjo] retTypFull  in 
  let retTypFull := ssubst_aux retTypFull thisBranchSubiFull  in 
  let indIndicesRel := ALMapRange (fun t => ssubst_aux t thisBranchSubiFull) indIndicesRel  in 
  let tindAppR := pairMapr (fun t => ssubst_aux t thisBranchSubiFull) tindAppR  in 
  let tindAppRo := pairMapr (fun t => ssubst_aux t thisBranchSubiFull) tindAppRo  in 
  (* TODO : substitute in tindAppR tindAppRo. there, even the constructor needs to be substed*)
  let matcht2 :=
      let lamArgs := snoc indIndicesj vttj in
      let retTypM2 := mkLamL lamArgs retTypFull in 
      let lnt2 := map (translateOneBranch2
                         o
                         indPacket
                         vhexeq
                         maxbv
                         vtti
                         vttj
                         vttjo
                         tindAppR
                         tindAppRo
                         retTypFull
                         indIndicesi
                         indIndicesj
                         indIndicesRel
                         (IndTrans.index cinfo_R))
                 (IndTrans.constrInfo_R indPacket) in
      oterm o (map (bterm []) ([retTypM2; vterm (fst vttj)]++lnt2)) in 
  mkLamL (map (removeSortInfo ∘ targi)
              (IndTrans.args_R cinfo_R)) (mkApp matcht2 [vterm (fst vttjo)]).
  

Definition translateIndOne2One
           (numParams:nat)
           (tind : inductive*(simple_one_ind STerm STerm)) : (list Arg) * fixDef True STerm :=
  let indPacket : IndTrans.IndInfo
      := mkIndTransPacket true ienv numParams tind in
  let lv : list V := freshUserVars (IndTrans.indBVars indPacket) ["tind"; "Hexeq"; "n"] in
  let vt : V := nth 0 lv dummyVar in
  let vhexeq : V := nth 1 lv dummyVar in
  let maxbv :N :=
      let vn : V := nth 2 lv dummyVar in
      (* the larger of these vars dont clash with anything. So adding
        this to anything (0 in the worst case) will give us something that 
        is disjoint from all bvars in the inductive.*)
      Nmax (Nmax (fst vt) (fst vn)) (fst vhexeq) in
  let vtt : (V*STerm):= (vt, IndTrans.indApp indPacket) in
  let vtt2 : (V*STerm) := primeArgsOld vtt in
  let vtr :V := vrel vt in
  let (vtti, vttj) := maybeSwap (vtt, vtt2) in
  let vttjo : (V*STerm) := pairMapl (extraVar maxbv) vttj in
  let tindApp : STerm := IndTrans.indAppR indPacket in
  let tindAppR : (V*STerm) := (vtr, mkApp tindApp (map (vterm ∘ fst) [vtt; vtt2])) in
  let tindAppRo : (V*STerm) :=
      let vars : list (V*STerm) := if b21 then [vttjo; vtt2] else [vtt; vttjo] in
      (extraVar maxbv vtr,
       mkApp tindApp (map (vterm ∘ fst) vars)) in
  let extraArgs : list (V*STerm):= [vtti;vttj;vttjo;tindAppR;tindAppRo] in 
  let fixArgs :=  mrs (TranslatedArg.merge3way (IndTrans.indIndices_R indPacket)) in
  let allFixArgs :=  fixArgs ++ extraArgs  in
  let retTyp :=
      let eqt : EqType STerm :=
          {|eqType := snd vttj; eqLHS := vterm (fst vttj); eqRHS := vterm (fst vttjo) |} in
      getEqTypeSq eqt in
  let o : CoqOpid:= IndTrans.matchOpid indPacket in
  let indIndices := IndTrans.indIndices_R indPacket in
  let (indIndicesi, indIndicesj) := indIndicesij indPacket in
  let indIndicesRel := (map (removeSortInfo ∘ TranslatedArg.argRel) indIndices) in
  let piArgs := indIndicesRel++[tindAppR;tindAppRo]  in
  let retTypFull := mkPiL piArgs retTyp in
  let match1 :=
      let lamArgs := snoc indIndicesi vtti in
      let retTypeM1 := mkLamL lamArgs retTypFull  in
      let lnt := map (translateOneBranch1
                        o
                        indPacket
                        vhexeq
                        maxbv
                        vtti
                        vttj
                        vttjo
                        tindAppR
                        tindAppRo
                        retTypFull
                        indIndicesi
                        indIndicesj
                        indIndicesRel
                     )
                 (IndTrans.constrInfo_R indPacket) in
      oterm o (map (bterm []) ([retTypeM1; vterm (fst vtti)]++lnt) ) in 
  let fbody : STerm := mkLamL allFixArgs (mkApp match1 (map (vterm ∘ fst) piArgs)) in
  let ftyp: STerm := mkPiL allFixArgs retTyp in
  let rarg : nat := (length fixArgs)%nat in
  (TranslatedArg.merge3way (IndTrans.indParams_R indPacket),
   {|fname := I; ftype := (ftyp, None); fbody := fbody; structArg:= rarg |}).
  
  
  
  

End IndTrue.
Import MonadNotation.
Open Scope monad_scope.


Require Import List. 

(*
Fixpoint castTermAux (vtyp: V*STerm) (t:STerm) : STerm  :=
  let (v,typ) := vtyp in
  match typ with
  | mkSort s => projTyRel
  |
  end.
 *)


(*
Definition castParam (a:Arg) : STerm  :=
  castTerm (snd a) (vterm (fst a)).
*)

Definition genIndisoWrappers  (ienv : indEnv) (numParams:nat) 
           (p : (inductive * simple_one_ind STerm STerm))
  (oldNameFs : list (inductive -> nat -> ident)): list defIndSq :=
  let (tind, smi) := p in
  let (nmT, constrs) := smi in
  let seq := List.seq 0 (length constrs) in
  let (_, indTyp) := nmT in
  let (_, indTypParams) := getNHeadPis numParams indTyp in
  let bodyArgs := flat_map (transArgWithCast ienv) indTypParams in
  let defn constrIndex oldNameF :=
      let oldName := (oldNameF tind constrIndex) in
      let body := mkConstApp oldName (map snd bodyArgs) in
      let body := mkLamL (map fst bodyArgs) body in
      inl {|nameSq := isoModeId oldName; bodySq := body  |} in
  let defn constrIndex :=
      map (defn constrIndex) oldNameFs in
  flat_map defn seq.


Definition crrCrrInvWrappers (ienv : indEnv) (numParams:nat) 
           (p : (inductive * simple_one_ind STerm STerm))
  : list defIndSq :=
 genIndisoWrappers ienv numParams p [constrTransName; constrInvFullName].
  
Definition  allCrrCrrInvsWrappers  (env : indEnv)
  : list defIndSq :=
  flat_map
    (fun (p: ident * (simple_mutual_ind STerm SBTerm)) =>
       let (id, mind) := p in
         let numParams := mindNumParams mind in
           let ones := substMutInd id mind in
           flat_map (crrCrrInvWrappers env numParams) ones
           ) env.

Definition mkBestRel_ref := "ReflParam.Trecord.mkBestRel".

Definition  mkOneIndGoodPacket  (ienv: indEnv) (p: inductive * STerm) : defSq :=
  let (tind, typ) := p in
  let (_, indTypArgs) := getHeadPIs typ in
  let indTyp_R := translate true ienv (headPisToLams typ) in
  let (_, indTypArgs_R) := getNHeadLams (3*length indTypArgs) indTyp_R  in
  let appArgs : list STerm := map (vterm ∘ fst) indTypArgs_R in
  let indApp := mkIndApp tind (map (vterm ∘ fst) indTypArgs) in
  let indApp2 := tprime indApp in
  let iRRname := (indTransName tind) in
  let IRR := mkConstApp iRRname appArgs in
  let tot12 := mkConstApp (indTransTotName false false tind) appArgs in
  let tot21 := mkConstApp (indTransTotName false true tind) appArgs in
  let one12 := mkConstApp (indTransOneName false tind) appArgs in
  let one21 := mkConstApp (indTransOneName true tind) appArgs in
  let body := mkConstApp mkBestRel_ref [indApp, indApp2,
                                        IRR, tot12, tot21,
                                        one12, one21] in
  {|
    nameSq := isoModeId iRRname;
     bodySq:= mkLamL (mrs indTypArgs_R) body
  |}.
  
Definition  mkIndGoodPacket  (ienv: indEnv)
            (id:ident) (mind: simple_mutual_ind STerm SBTerm)
  : list defIndSq :=
  let indTyps : list (inductive * STerm) := indTypes id mind in
  map (inl ∘ (mkOneIndGoodPacket ienv)) indTyps.

Definition genWrappers  (ienv : indEnv) : TemplateMonad () :=
  tmMkDefIndLSq (allCrrCrrInvsWrappers ienv).


Definition genParam (ienv : indEnv) (piff: bool) (b:bool) (id: ident) : TemplateMonad unit :=
  id_s <- tmQuoteSq id true;;
(*  _ <- tmPrint id_s;; *)
  match id_s with
  Some (inl t) => 
  let t_R := (translate piff ienv t) in
  if b then (@tmMkDefinitionSq (constTransName id)  t_R)
  else
    trr <- tmReduce Ast.all t_R;;
    tmPrint trr  ;;
    trrt <- tmReduce Ast.all (fromSqNamed t_R);;
    tmPrint trrt
  | _ => ret tt
  end.


(* no crinv. don't produce it at source if not needed *)
Definition genParamInd (ienv : indEnv)  (b cr:bool) (id: ident) : TemplateMonad unit :=
  id_s <- tmQuoteSq id true;;
(*  _ <- tmPrint id_s;; *)
  match id_s with
  Some (inl t) => ret tt
  | Some (inr t) =>
    let (fb, defs) := translateMutInd ienv id t 0 in
    let (defs , inds) := partition (isInl) defs in
      (if b then ret tt else trr <- tmReduce Ast.all (fb,defs);; tmPrint trr);;
      _ <- (if b then tmMkDefIndLSq inds else ret tt);;
      _ <- (if b then  (tmMkDefinitionSq (indTransName (mkInd id 0)) fb) else ret tt);;
        tmMkDefIndLSq (if cr then defs else [])
      (* repeat for other inds in the mutual block *)
  | _ => ret tt
  end.
Print fold_left.

(* indEnv is needed because the types may contain matches
Definition addConstrInvsToIndInv b ienv (ide:ident*(simple_mutual_ind STerm SBTerm))
:
(ident* ((simple_mutual_ind STerm SBTerm)
        * list (simple_one_ind STerm (STerm -> STerm -> SBTerm))))
 :=
 let (id,t) := ide in
 let (_,ones) := substMutIndNoParams id t in
  map (mapTermSimpleOneInd
       (@Datatypes.id STerm)
       (fun b: SBTerm => (b,translateConstructorInv b ienv indsT lp))) ones.
       
        in
       combine inds onesS.
 
substMutIndNoParams
           (id:ident) (t: simple_mutual_ind STerm SBTerm)
  :list (inductive* simple_one_ind STerm SBTerm) :=
  substMutIndMap (fun b is _ => apply_bterm_partial b is) id t.
  let (_)
mapSimpl
 *)
 
Definition mkIndEnv (idEnv : ident) (lid: list ident) : TemplateMonad unit :=
  let addIndToEnv (id: ident) (l: TemplateMonad indEnv) : TemplateMonad indEnv :=
       l <- l;;
       id_s <- tmQuoteSq id true;;
       ret
       (match id_s with
       | Some (inl t) => l
       | Some (inr t) => (id,t)::l
       | _ => l
        end) in
    
  ienv <- fold_right addIndToEnv (ret []) lid;;
  tmMkDefinition false idEnv ienv.


Definition genParamIndTot (iffb21:list (bool * bool))
           (ienv : indEnv) (b:bool) (id: ident) : TemplateMonad unit :=
  id_s <- tmQuoteSq id true;;
(*  _ <- tmPrint id_s;; *)
  match id_s with
  Some (inl t) => ret tt
  | Some (inr t) =>
    let ff (ifb: bool*bool) : TemplateMonad unit :=
        let (iff,b21) := ifb in
        let fb := (mutIndToMutFix true (translateOnePropTotal b21 ienv iff)) id t 0%nat in
        if b then (tmMkDefinitionSq (indTransTotName iff b21 (mkInd id 0)) fb) else
          (trr <- tmReduce Ast.all fb;; tmPrint trr) in
        _ <- ExtLibMisc.flatten (map ff iffb21);; ret tt
  | _ => ret tt
  end.

Definition genParamIndOne (lb21: list bool)
           (ienv : indEnv) (b:bool) (id: ident) : TemplateMonad unit :=
  id_s <- tmQuoteSq id true;;
(*  _ <- tmPrint id_s;; *)
  match id_s with
  Some (inl t) => ret tt
  | Some (inr t) =>
    let ff (b21: bool) : TemplateMonad unit :=
        let fb := (mutIndToMutFix true (translateIndOne2One b21 ienv)) id t 0%nat in
        if b then (tmMkDefinitionSq (indTransOneName b21 (mkInd id 0)) fb) else
          (trr <- tmReduce Ast.all fb;; tmPrint trr) in
        _ <- ExtLibMisc.flatten (map ff lb21);; ret tt
  | _ => ret tt
  end.

Definition genParamIso 
           (ienv : indEnv) (id: ident) : TemplateMonad unit :=
  id_s <- tmQuoteSq id true;;
(*  _ <- tmPrint id_s;; *)
  match id_s with
  Some (inl t) => ret tt
  | Some (inr mind) =>
      tmMkDefIndLSq (mkIndGoodPacket ienv id mind)
  | _ => ret tt
  end.

Definition genParamIndOneAll :=
  genParamIndOne [false;true].

Definition genParamIndTotAllAux :=
  genParamIndTot [(false, false); (false, true); (true, false); (true, true)].

Definition genParamIndTotAll (ienv : indEnv) (b:bool) (id: ident) :=
  ExtLibMisc.flatten [genParamIndTotAllAux ienv b id;  genParamIndOneAll ienv b id].

Definition genParamIndAll (ienv : indEnv) (id: ident) :=
  ExtLibMisc.flatten [
      genParamInd ienv true true id;
        genParamIndTotAllAux ienv true  id;  genParamIndOneAll ienv true id;
    genParamIso ienv id].
