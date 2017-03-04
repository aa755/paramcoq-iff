

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

Notation AnyRel := false (only parsing).
Notation IsoRel := true (only parsing).

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

(* see matchR.vappend2_RR for some concrete intuition on why the translation is the way it is,
e.g., why the type of the discriminee is needed. This function was written after
playing with those examples. *)
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
  let (retTypLeaf, rargs) := getHeadLams retTyp in (* FIX: this was already done above. reuse that *)
  let nrargs := length rargs in
  (* FIX: the word retTyp is used both for the leaf and thw whole term including lambdas *)
  let (retTyp_R, retArgs_R) := getNHeadLams (3*nrargs) retTyp_R in
  let (arg_Rs (*rename to arg_RRs *), argsAndPrimes) := separate_Rs retArgs_R in
  (* contains lastVar *)
  
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
             (map (tvmap vprime) (*FIX: tprime*) (snoc discTypIndices disc))) in
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


Import MonadNotation.
Open Scope monad_scope.


Require Import List. 

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
