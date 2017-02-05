




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

Definition argsLen (ci: IndTrans.ConstructorInfo) : nat := 
(length (args_R ci)).

Definition args (ci: IndTrans.ConstructorInfo) : list Arg := 
map TranslatedArg.arg  (args_R ci).

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

End IndTrans.

Require Import Coq.Program.Program.
Open Scope program_scope.

Require Import Coq.Init.Nat.

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



Require Import SquiggleEq.varInterface.
Import STermVarInstances.
Require Import SquiggleEq.varImplDummyPair.
Definition isoModeId (id:ident) := String.append id "_iso".

Definition constTransName (n:ident) : ident :=
  String.append (mapDots "_" n) "_pmtcty_RR".
Require Import ExtLib.Data.String.

Definition indTransName (n:inductive) : ident :=
match n with
| mkInd s n => String.append (constTransName s) (nat2string10 n)
end.

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

Definition indTransTotName (n:inductive) : ident :=
match n with
| mkInd s n => String.append (String.append (constTransName s) "_tot_") (nat2string10 n)
end.

Require Import SquiggleEq.AssociationList.

Definition mindNumParams (t:simple_mutual_ind STerm SBTerm) :nat :=
length (fst t).

(* Move to templateCoqMisc? *)
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


Definition constrTransName (n:inductive) (nc: nat) : ident :=
String.append (indTransName n) (String.append "_constr_" (nat2string10 nc)).

Definition constrTransTotName (n:inductive) (nc: nat) : ident :=
String.append (constrTransName n nc) "_tot".

Definition constrInvName (cn:ident)  : ident :=
String.append cn "_inv".

Definition constrInvFullName (n:inductive) (nc: nat)  : ident :=
constrInvName (constrTransName n nc).

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
  let (cargs_R, cargsAndPrimes) := separate_Rs cargs in
  let cargsAndPrimes := map (vterm ∘ fst) cargsAndPrimes in
  let (retTypBody,pargs) := getHeadPIs retTyp in
  let ret :=
    match constrInv with
    | Some constrInv => 
        let f : STerm := mkLamL cargs_R ret in 
        mkConstApp constrInv (discTypParamsR++cargsAndPrimes++(map (vterm ∘ fst) pargs)
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
    (sigtFull,  [C_RR , C_RRInv, C_RRTot ]) in
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

Definition extractGoodRelFromApp  (t_RApp (* BestR A1 A2 AR a1 a2 *):STerm):=
  (* need to return AR *)
  let (_, args) := flattenApp t_RApp [] in
  nth 2 args (oterm (CUnknown "extractGoodRelFromApp") []).

Definition totij (consNames : ident*ident)
           (typ : TranslatedArg.T Arg) (ti : STerm) : (STerm (*t2*)* STerm (*tr*)):=
  let (idij, idijr) := consNames in
  let args := [argType (TranslatedArg.arg typ);
                 argType (TranslatedArg.argPrime typ);
                 ((extractGoodRelFromApp ∘ argType) (TranslatedArg.argRel typ)) ;ti
              ] in
(mkConstApp idij args, 
mkConstApp idijr args).

Definition tot12 (typ : TranslatedArg.T Arg) (t1 : STerm) : (STerm (*t2*)* STerm (*tr*)):=
  totij ("ReflParam.Trecord.BestTot12",  "ReflParam.Trecord.BestTot12R")
        typ t1.

Definition tot21 (typ : TranslatedArg.T Arg) (t2 : STerm)  : (STerm (*t2*)* STerm (*tr*)):=
  totij ("ReflParam.Trecord.BestTot21",  "ReflParam.Trecord.BestTot21R")
        typ t2.

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
         (cIndices : list (STerm (* primes *) * STerm (* rels *)))
         (baseType ret: STerm) {struct retArgs} : STerm :=
  match (retArgs, cIndices) with
  | (hi::retArgs, (hcp,hcr)::cIndices) =>
    let (hi, vPrimehi) := hi in
    let (vRhi , Thi) := hi in
    let (_ (* BestR *), ThiArgs (* 5 items *)) := flattenApp Thi [] in
    let peq := mkConstApp oneConst (ThiArgs++[hcp; vterm vRhi; hcr]) in
    let transportType := nth 1 ThiArgs (oterm (CUnknown "mkOneOneRewrites") []) in
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

Section IndTrue.
  Variable ienv: indEnv.
  Let translatef := translate true ienv.
  Let translate := translate true ienv.

  
  Definition recursiveArgIff (p:TranslatedArg.T Arg) (numPiArgs:nat) t :=
      let procLamArgOfArg (p:TranslatedArg.T Arg) (t:STerm): STerm:=
        let (T1In,T2In, TRIn) := p in 
        let t21 := tot21 p (vterm (argVar T2In)) in
        mkLetIn (argVar T1In) (fst t21) (argType T1In)
          (mkLetIn (argVar TRIn) (snd t21)  (* typ to t1 *)
              (argType TRIn) t) in
      let (T1,T2,_) := p in 
      let T1lR := (translatef (headPisToLams (argType T1))) in
      let (ret_R, lamArgs_R) := getNHeadLams (3*numPiArgs) T1lR in
      let lamArgs_R := TranslatedArg.unMerge3way lamArgs_R in
      let recCall : STerm := flattenHeadApp ret_R in (* not needed? *)
      let v := (argVar T1) in
      let f1 : STerm := vterm v in
      let recArg : STerm := mkApp f1 (map (vterm∘fst∘TranslatedArg.arg) lamArgs_R) in
      let recRet := (mkApp recCall [recArg]) in
      let retIn := List.fold_right procLamArgOfArg recRet lamArgs_R in
      let retIn := mkLamL (map (removeSortInfo ∘ TranslatedArg.argPrime) lamArgs_R) retIn in
      mkLetIn (vprime v) retIn (argType T2) t.
(* (vrel v) is not needed. indices of a constr cannot mention rec args.
onenote:https://d.docs.live.net/946e75b47b19a3b5/Documents/Postdoc/parametricity/papers/logic/isorel.one#indices%20of%20a%20constr%20cannot%20mention%20rec%20args&section-id={6FC701EE-23A1-4695-AC21-2E6CBE61463B}&page-id={A96060FB-9EFC-4F21-8C1C-44E1B3385424}&end
*)

  
  (* returns 1) the correct translation relation for the Pi Type. Note that just
  [argType] is not the correct relation, because it uses _iso, which is rebound here to
  something else (iso hasn't been even fully generated yet). Also, params need to be casted
  as this function does in the base case.
  2) the half totality proof. *)
  Fixpoint recursiveArgTotAux (castedParams_R : list STerm) (argType: STerm)  : (STerm*STerm):=
    match argType with
    | mkPiS nm A Sa B _ =>
      let A2 := (tprime A) in
      let AR := (translate A) in 
      let brtot := mkTotalPiHalfGood A A2 AR in
      let Bl1 := (mkLam nm A B) in
      let Bl2 := (tprime Bl1) in
      let brtot := brtot Bl1 Bl2  in
      let (recbr, recbrtot) := recursiveArgTotAux castedParams_R B in
      let lrecbr := transLam true translate (nm,(A,Sa)) recbr in
      let lrecbrtot := transLam true translate (nm,(A,Sa)) recbrtot in 
      let brtot := brtot lrecbr lrecbrtot in
        (mkRPiS A A2 (castIfNeeded true (A,Sa) A2 AR) Bl1 Bl2 lrecbr, brtot)
    | _ =>
      (* cast is removed because this is a recursive arg of the constructor *)
      let argType_Rtot := translate argType in (* argType translate the current inductive to the 
_iso name , which will be replaced with the fixpoint var binding this fixpoint. 
We want this for brtothalf but not brtot *)
      let argType_R :=
          let tind_RR (* not the iso version *) :=
              let (indt, args) := flattenApp argType [] in
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
      let (T1,T2,TR) := p in 
      let v: V:= (argVar T1) in
      let f1: STerm := vterm v in
      let vr :V := (argVar TR) in
      let (TR,pitot) := (recursiveArgTotAux castedParams_R (argType T1)) in
      let f2r: STerm := (mkApp pitot [f1]) in
      let f2Type: STerm := argType T2 in
      let f2rType: STerm :=
          mkSig (argVar T2) (argType T2) (mkApp TR [f1; vterm (argVar T2)]) in
      let frType : STerm :=
          mkLam (argVar T2) (argType T2) (mkApp TR [f1; vterm (argVar T2)]) in
      let body: STerm :=
          mkLetIn vr
                  (mkConstApp projT2_ref [f2Type; frType; vterm vr])
                  (mkApp TR [f1; vterm (argVar T2)]) t in
      let body: STerm :=
          mkLetIn (argVar T2)
                  (mkConstApp projT1_ref [f2Type; frType; vterm vr])
                  (argType T2) body in
      mkLetIn vr f2r f2rType body.

  Definition translateOnePropBranch  (iffOnly:bool (* false => total*))
             (* v : the main (last) input to totality *)
             (ind : inductive) (totalT2: STerm) (v:V) (params: list Arg) (castedParams_R : list STerm)
           (indIndices caseRetPrimeArgs caseRetRelArgs : list (V*STerm))
           (indAppParamsPrime: STerm)
  (cinfo_RR : IndTrans.ConstructorInfo): STerm := 
  let constrIndex :=  IndTrans.index cinfo_RR in
  let constrArgs_R := IndTrans.args_R cinfo_RR in
  let c1 := mkApp (mkConstr ind constrIndex) (map (vterm∘fst) params) in
  let procArg  (p: TranslatedArg.T Arg) (t:STerm): STerm:=
    let (T1,T2,TR) := p in 
    let isRec :=  (isConstrArgRecursive ind (argType T1)) in
    if isRec
    then
      (if iffOnly
       then recursiveArgIff p (numPiArgs (argType T1)) t
       else recursiveArgTot castedParams_R p t)
    else
      mkLetIn (argVar T2) (fst (tot12 p (vterm (argVar T1)))) (argType T2)
        (mkLetIn (argVar TR) (snd (tot12 p (vterm (argVar T1)))) 
            (argType TR) t) in
  let c1 := mkApp c1 (map (vterm∘fst∘TranslatedArg.arg) constrArgs_R) in
  let c2 := tprime c1 in
  let thisBranchSub :=
      (* specialize the return type to the indices. later even the constructor is substed*)
      let cretIndices := IndTrans.indices cinfo_RR in
      (combine (map fst indIndices) cretIndices) in
  let caseRetRelArgs : list (V*STerm) :=
      ALMapRange (fun t => ssubst_aux t thisBranchSub) caseRetRelArgs in
  (* after rewriting with oneOnes, the indicesPrimes become (map tprime cretIndices)*)
  let thisBranchSubPrime := ALMap vprime tprime thisBranchSub in
  let caseRetRelArgsAfterRws : list (V*STerm) :=
      ALMapRange (fun t => ssubst_aux t thisBranchSubPrime) caseRetRelArgs in
  let (c2MaybeTot, c2MaybeTotBaseType) :=
      if iffOnly
      then (c2,indAppParamsPrime)
      else
        let thisBranchSubFull := snoc thisBranchSub (v, c1) in
        let retTRR := ssubst_aux totalT2 (thisBranchSubFull) in
        let retTRRLam := mkLamL caseRetPrimeArgs (mkPiL caseRetRelArgs retTRR)  in
        let crr :=
            mkConstApp (constrTransName ind constrIndex)
                       (castedParams_R
                          ++(map (vterm ∘ fst) (TranslatedArg.merge3way constrArgs_R))) in
        (mkLamL
           caseRetRelArgsAfterRws
           (sigTToExistT2 [c2] crr (ssubst_aux retTRR thisBranchSubPrime))
         ,retTRRLam) in
  (* do the rewriting with OneOne *)
  let c2rw :=
      let cretIndicesPrimesRRs := combine (IndTrans.indicesPrimes cinfo_RR)
                                          (IndTrans.indicesRR cinfo_RR) in
      let cretIndices := IndTrans.indicesRR cinfo_RR in
      mkOneOneRewrites "BestOne12"
                       (combine caseRetRelArgs (map fst caseRetPrimeArgs))
                       []
                       cretIndicesPrimesRRs
                       c2MaybeTotBaseType
                       c2MaybeTot in
  let c2rw := if iffOnly then c2rw else mkApp (c2rw) (map (vterm ∘ fst) caseRetRelArgs) in
  let ret := List.fold_right procArg c2rw constrArgs_R in
  mkLamL ((map (removeSortInfo ∘ TranslatedArg.arg) constrArgs_R)
            ++(caseRetPrimeArgs++ caseRetRelArgs)) ret.

(** tind is a constant denoting the inductive being processed *)
Definition translateOnePropTotal (iffOnly:bool (* false => total*))
           (numParams:nat)
  (tind : inductive*(simple_one_ind STerm STerm)) : (list Arg) * fixDef True STerm :=
  let (tind,smi) := tind in
  let (nmT, constrs) := smi in
  let constrTypes := map snd constrs in
  let (_, indTyp) := nmT in
  let (_, indTypArgs) := getHeadPIs indTyp in
  let indTyp_R := translatef (headPisToLams indTyp) in
  let (_, indTypArgs_R) := getNHeadLams (3*length indTypArgs) indTyp_R  in
  let indTypArgs_RM := TranslatedArg.unMerge3way  indTypArgs_R in
  let indTypeParams : list Arg := firstn numParams indTypArgs in
  let indTypeIndices : list Arg := skipn numParams indTypArgs in
  let indTypeParams_R : list Arg := firstn (3*numParams) indTypArgs_R in
  let indTypeIndices_R : list Arg := skipn (3*numParams) indTypArgs_R in
  let vars : list V := map fst indTypArgs in
  let indAppParamsPrime : STerm := (mkIndApp tind (map (vterm ∘ vprime ∘ fst) indTypeParams)) in
  let T1 : STerm := (mkIndApp tind (map vterm vars)) in
  let T2 : STerm := tprime T1 in
  let v : V := fresh_var vars in
  let (totalT2, castedParams_R)   :=
      let args := flat_map (transArgWithCast ienv) indTypArgs in
      let args := map snd args in
      (mkSig (vprime v) T2 (mkConstApp (indTransName tind)
                         (args++[vterm v; vterm (vprime v)]))
       , firstn (3*numParams) args)  in
  let retTyp : STerm :=
      if iffOnly then T2 else totalT2 in
  let indTypeIndices_RM := skipn  numParams  indTypArgs_RM in
  (* why are we splitting the indicesPrimes and indices_RR? *)
  let caseRetPrimeArgs :=  map (removeSortInfo ∘ TranslatedArg.argPrime) indTypeIndices_RM in
  let caseRetRelArgs :=  map (removeSortInfo ∘ TranslatedArg.argRel) indTypeIndices_RM in
  let caseRetArgs :=  (caseRetPrimeArgs++caseRetRelArgs) in
  let caseRetTyp := mkPiL caseRetArgs  retTyp in
  let caseTyp := mkLamL (snoc (map removeSortInfo indTypeIndices) (v,T1)) caseRetTyp in
  let cinfo_R := mkConstrInfoBeforeGoodness tind numParams translate constrTypes in 
  let o :=
      let cargsLens : list nat := (map IndTrans.argsLen  cinfo_R) in
      (CCase (tind, numParams) cargsLens) None in
  let matcht :=
      let lnt : list STerm := [caseTyp; vterm v]
                                ++(map (translateOnePropBranch
                                          iffOnly
                                          tind
                                          totalT2
                                          v
                                          indTypeParams
                                          castedParams_R
                                          (mrs indTypeIndices)
                                          caseRetPrimeArgs
                                          caseRetRelArgs
                                          indAppParamsPrime)
                                   cinfo_R) in
      oterm o (map (bterm []) lnt) in
  let matchBody : STerm :=
      let indTypeIndexVars := map fst indTypeIndices in
      mkApp matcht (map vterm ((map vprime indTypeIndexVars)++ (map vrel indTypeIndexVars))) in
  (* todo, do mkLamL indTypArgs_R just like transOneInd *)
  let fixArgs :=  ((mrs (indTypeParams_R++indTypeIndices_R)) ) in
  let allFixArgs :=  (snoc fixArgs (v,T1)) in
  let fbody : STerm := mkLamL allFixArgs (matchBody) in
  let ftyp: STerm := mkPiL allFixArgs retTyp in
  let rarg : nat := ((length fixArgs))%nat in
  ([], {|fname := I; ftype := (ftyp, None); fbody := fbody; structArg:= rarg |}).

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
  let (_, indTypParams) := getNHeadPisS numParams indTyp in
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


Definition genParamIndTot (ienv : indEnv) (total: bool) (b:bool) (id: ident) : TemplateMonad unit :=
  id_s <- tmQuoteSq id true;;
(*  _ <- tmPrint id_s;; *)
  match id_s with
  Some (inl t) => ret tt
  | Some (inr t) =>
    let fb := (mutIndToMutFix true (translateOnePropTotal ienv total)) id t 0%nat in
      if b then (tmMkDefinitionSq (indTransTotName (mkInd id 0)) fb) else
        (trr <- tmReduce Ast.all fb;; tmPrint trr)
  | _ => ret tt
  end.
