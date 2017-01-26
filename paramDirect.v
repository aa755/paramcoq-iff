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


Module IndTrans.
Record ConstructorInfo : Set := {
  index : nat; (* index of this constructor *)
  args_R : list Arg;
(*  argsPrimes : list Arg;
  args_RR : list Arg; *)
  retTyp : STerm; 
(*  retTypIndices : list STerm; *)
  retTypIndices_R : list STerm;
  (* retTypIndicesPacket : STerm  packaged as a sigma *)
}.

Definition args (ci: IndTrans.ConstructorInfo) := 
filter_mod3  (args_R ci) 0%N.

Definition argPrimes (ci: IndTrans.ConstructorInfo) := 
filter_mod3  (args_R ci) 1%N.

Definition argRR (ci: IndTrans.ConstructorInfo) := 
filter_mod3  (args_R ci) 2%N.

Definition indices (ci: IndTrans.ConstructorInfo) := 
filter_mod3  (retTypIndices_R ci) 0%N.

Definition indicesPrimes (ci: IndTrans.ConstructorInfo) := 
filter_mod3  (retTypIndices_R ci) 1%N.

Definition indicesRR (ci: IndTrans.ConstructorInfo) := 
filter_mod3  (retTypIndices_R ci) 2%N.

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
let B_R := mkAppBeta B_R [vterm a1; vterm a2; vterm ar] in
let B_R := if Bsp then projTyRel (mkAppBeta B1 [vterm a1]) (mkAppBeta B2 [vterm a2])
     B_R else B_R in
mkLamL [(f1, mkPi a1 A1 (mkAppBeta B1 [vterm a1])) ; (f2, mkPi a2 A2 (mkAppBeta B2 [vterm a2]))]
(mkPiL [(a1,A1); (a2,A2) ; (ar, mkAppBeta A_R [vterm a1; vterm a2])]
   (mkAppBeta B_R [mkApp (vterm f1) [vterm a1]; mkApp (vterm f2) [vterm a2]])).


Definition getPiConst (Asp Bsp : bool) := 
match (Asp, Bsp) with
(* true means lower universe (sp stands for Set or Prop) *)
| (false, false) => "PiABType" (* not used *)
| (false, true) => "PiATypeBSet" (* not used *)
| (true, false) => "PiASetBType" (* not used *)
| (true, true) => "ReflParam.PiTypeR.PiTSummary"
end.

Run TemplateProgram (printTermSq "PiABType").

Definition mkPiR (Asp Bsp : bool) (a: V) 
 (A1 A2 A_R  B1 B2 B_R: STerm) := 
let pir :=
mkApp (mkConst (getPiConst Asp Bsp)) [A1; A2; A_R ; B1; B2; B_R] in 
let pirQ :=
PiABType Asp Bsp a A1 A2 A_R  B1 B2 B_R in 
match (Asp, Bsp) with
(* true means lower universe (sp stands for Set or Prop) *)
| (false, false) => pirQ
| (false, true) => pirQ
| (true, false) => pirQ
| (true, true) => pir
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

Definition constTransName (n:ident) : ident :=
  String.append (mapDots "_" n) "_pmtcty_RR".
Require Import ExtLib.Data.String.

Definition indTransName (n:inductive) : ident :=
match n with
| mkInd s n => String.append (constTransName s) (nat2string10 n)
end.

Definition indIndicesTransName (n:inductive) : ident :=
String.append (indTransName n) "_indices".

Definition indIndicesConstrTransName (i:ident) : ident := 
String.append i "c".

Definition indIndicesConstrTransNameFull (n:inductive) : ident :=
indIndicesConstrTransName (indIndicesTransName n).

Definition indTransTotName (n:inductive) : ident :=
match n with
| mkInd s n => String.append (String.append (constTransName s) "_tot_") (nat2string10 n)
end.

Require Import SquiggleEq.AssociationList.


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


Definition substIndConstsWithVars (id:ident) (numParams numInds : nat)
(indTransName : inductive -> ident)
  : list (ident*V) :=
    let is := List.seq 0 numInds in
    let inds := map (fun n => mkInd id n) is in
    let indRNames := map indTransName inds in
    (* Fix: for robustness agains variable implementation, use FreshVars?*)
    let indRVars : list V := combine (seq (N.add 3) 0 numInds) (map nNamed indRNames) in
    combine indRNames indRVars.

(* TODO : use fixDefSq *)
Definition mkFixCache
           (p: list (V*fixDef V STerm)) : fixCache :=
  let bvars := map fst p in
  let fds := map snd p in
  let o: nat->CoqOpid := (CFix (length bvars) (map ((@structArg V STerm)) fds)) in
  let bodies := (map ((bterm bvars)∘(@fbody V STerm)) fds) in
    (o, (bodies++(map ((bterm [])∘(@ftype V STerm)) fds))).


(* TODO:  use the mkFixcache above *)
Definition mutIndToMutFixAux {TExtra:Type}
(tone : forall (numParams:nat)(tind : inductive*(simple_one_ind STerm STerm)),
  (fixDef True STerm)* list TExtra)
(id:ident) (t: simple_mutual_ind STerm SBTerm) (i:nat)
  : STerm * list TExtra :=
    let onesS := substMutInd id t in
    let numInds := length onesS in
    let numParams := length (fst t) in
    let trAndDefs := map (tone numParams) onesS in
    let tr: list (fixDef True STerm) := map fst trAndDefs in
    let extraDefs := flat_map snd trAndDefs in
    let constMap := substIndConstsWithVars id numParams numInds indTransName in
    let indRVars := map snd constMap  in
    let o: CoqOpid := (CFix numInds (map (@structArg True STerm) tr) i) in
    let bodies := (map ((bterm indRVars)∘(constToVar constMap)∘(@fbody True STerm)) tr) in
    (reduce 100 (oterm o (bodies++(map ((bterm [])∘(@ftype True STerm)) tr))), extraDefs).

Definition mutIndToMutFix
(tone : forall (numParams:nat)(tind : inductive*(simple_one_ind STerm STerm)),
  (fixDef True STerm))
(id:ident) (t: simple_mutual_ind STerm SBTerm) (i:nat)
  : STerm:=
fst (@mutIndToMutFixAux True (fun np i => (tone np i,[])) id t i).

(** to be used when we don't yet know how to produce a subterm *)
Axiom F: False.
Definition fiat (T:Type) : T := @False_rect T F.

(* somehow False_rect doesn't work while unquoting *)

Definition indEnv:  Type := AssocList ident (simple_mutual_ind STerm SBTerm).


Definition lookUpInd (ienv: indEnv) (ind : inductive) : simple_one_ind STerm SBTerm :=
  match ind with
  | mkInd id n =>
    let omind := ALFind ienv id in
    let dummy :=  (ind, dummyInd) in
    snd (match omind with
      | Some mind => 
        let mindS := substMutIndNoParams id mind in
        (nth n mindS dummy)
      | None=> dummy
    end)
  end.
  

Section trans.
Variable piff:bool.
(* already removed
Let removeHeadCast := if piff then removeHeadCast else id. 
*)
Let needSpecialTyRel := if piff 
then 
  (fun os =>
    match os with
  | Some s => isPropOrSet s
  | None => false
  end
  ) 
else (fun _ => false).

Let projTyRel := if piff then projTyRel else (fun _ _ t=> t).
Let mkTyRel := if piff then mkTyRel else mkTyRelOld.

(** AR is of type BestRel A1 A2 or A1 -> A2 -> Type. project out the relation
in the former case. 
Definition maybeProjRel (A1 A2 AR : STerm) :=
   if (hasSortSetOrProp A) then 
           (fun t => projTyRel A1 A2 AR)
      else AR.
*)



Definition transLamAux translate  (nma : Arg) : ((STerm * STerm)*STerm) :=
  let (nm,A) := nma in
  let (A, Sa) := A in
  let A1 := A in
  let A2 := tvmap vprime A1 in
  let f := if (needSpecialTyRel Sa) then 
           (fun t => projTyRel A1 A2 t)
      else id in
  (A1, A2, f (translate A)).

Definition transLam (translate : STerm -> STerm) (nma : Arg) b :=
  let (A12, AR) := transLamAux translate nma in
  let (A1, A2) := A12 in
  let nm := fst nma in
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
        mkConstApp "False_rectt" [retTypBody;vterm sigt] 
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
           (numIndParams: nat) (lNumCArgs : list nat) (retTyp disc discTyp : STerm)
           (branches : list SBTerm) : STerm :=
  let o := (CCase (tind, numIndParams) lNumCArgs) in
  let (_, retArgs) := getHeadLams retTyp in
  let vars := map fst retArgs in
  let lastVar := last vars dummyVar in
  let mt := oterm o ((bterm [] retTyp):: (bterm [] (vterm lastVar))
                                      :: (bterm [] discTyp)::(branches)) in
  let discInner := tvmap vprime disc in
  let retTyp_R := translate (* in false mode?*) retTyp in
  let (retTyp_R, retArgs_R) := getHeadLams retTyp_R in
  let (arg_Rs, argsAndPrimes) := separate_Rs retArgs_R in
  let retTyp_R := mkApp retTyp_R [mt; tvmap vprime mt] in
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
  let constrTyps : list SBTerm := map snd (snd (lookUpInd ienv tind)) in
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
| mkPiS nm A Sa B Sb =>
  let A1 := A in
  let A2 := tvmap vprime A1 in
  let B1 := (mkLam nm A1 B) in
  let B2 := tvmap vprime B1 in
  let B_R := transLam translate (nm,(A,Sa)) (translate B) in
  let Asp := (needSpecialTyRel Sa) in
  let Bsp := (needSpecialTyRel Sb) in
   mkPiR Asp Bsp nm A1 A2 (translate A) B1 B2 B_R
(* the translation of a lambda always is a lambda with 3 bindings. So no
projection of LHS should be required *)
| oterm (CApply _) (fb::argsb) =>
    mkAppBeta (translate (get_nt fb)) (flat_map (appArgTranslate translate) argsb)
(* Const C needs to be translated to Const C_R, where C_R is the registered translation
  of C. Until we figure out how to make such databases, we can assuming that C_R =
    f C, where f is a function from strings to strings that also discards all the
    module prefixes *)
| oterm (CCase (tind, numIndParams) lNumCArgs) 
    ((bterm [] retTyp):: (bterm [] disc):: (bterm [] discTyp)::lb) =>
  transMatch translate ienv tind numIndParams lNumCArgs retTyp disc discTyp lb
| _ => oterm (CUnknown "bad case in translate") []
end.

Definition translateArg  (p : Arg) : (V * STerm) :=
(* todo: take remove Cast from applications of the inductive type being translated.
Or after translation, remove BestR.
Or remove Goodness all over in this part of the definition. In the outer definition,
map it back*)
let (_, AR) := transLamAux translate p in
let (v,_) := p in
(vrel v, mkAppBeta AR [vterm v; vterm (vprime v)]).

Definition translateConstrArg tind (p : Arg) : (V * STerm) :=
(* todo: take remove Cast from applications of the inductive type being translated.
Or after translation, remove BestR.
Or remove Goodness all over in this part of the definition. In the outer definition,
map it back*)
let (v,t) := p in
let t := if isConstrArgRecursive tind (fst t) then (removeIndRelProps (fst t),None) else t in 
translateArg (v,t).

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
    IndTrans.args_R := args_R;
    IndTrans.retTyp := retType_R;
    IndTrans.retTypIndices_R := cretIndices_R
|}.


Definition translateConstructor (tind:inductive)
(*np:nat*) (cindex:nat)
(cargs_R cargsRR indTypeParams_R (* indTypIndices_RR*) : list Arg)
(constrApp sigtFullConstrIndices : STerm)
  : defSq*STerm :=
let cname := constrTransName tind cindex in
let lamArgs := (map removeSortInfo (indTypeParams_R ++ cargs_R)) in
let ext := sigTToExistT2 (map (vterm∘fst) cargsRR) constrApp sigtFullConstrIndices in
({| nameSq := cname; bodySq := mkLamL lamArgs ext |}, ext).

Definition sigt_rec_ref := "Coq.Init.Specif.sigT_rec".
Definition sigt_ref := "Coq.Init.Specif.sigT".

Let mrs := (map removeSortInfo).

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
    mkConstApp sigt_rec_ref [A;B; sigRetTyp; sigRet]
  else finalCase ()
| _ => finalCase ()
end.

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
  let retTypVarSort : STerm := mkSort sSet (* Fix. make it template/univ poky *) in 
  (* dummyVar is fine, because the next item is a sort, thus has no fvars *)
  (mkPiL (snoc indTypIndices_RR (dummyVar, sigtFull)) retTypVarSort) in
let rettVarType := 
  (mkPiL cargs_RR (mkApp (vterm retTypVar) (snoc cretIndices_RR C_RRBody))) in
let crinvBody := 
    let rettTypPartiallyApplied : STerm := 
        (mkApp (vterm retTypVar) (map (vterm∘fst) indTypIndices_RR)) in
    let o := (CCase (tindConstr, indConstrNumParams) [O]) in
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
  let cargs_R := IndTrans.args_R cinfo in
  let cargs := IndTrans.args cinfo in
  let indTypIndicVars := (map vprime indTypIndicVars) in
  let caseTypRet := 
    let cretIndicesPrime := (IndTrans.indicesPrimes cinfo) in
    ssubst_aux caseTypRet (combine indTypIndicVars cretIndicesPrime) in
  let (_,indTypIndices_RR) := getHeadPIs caseTypRet in
  let indTypIndices_RR := map removeSortInfo indTypIndices_RR in
  let cretIndices_R : list STerm := (IndTrans.retTypIndices_R cinfo) in
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
    (sigtFull,  [C_RR , C_RRInv ]) in
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


Definition translateIndMatchBody (numParams:nat) 
  tind v (caseTypArgs : list (V*STerm))(caseTypRet:  STerm) 
  (indTypeParams_R indTypIndices_RR : list Arg) (indTypIndicVars : list V)
  (constrTypes : list STerm): STerm * list defSq :=
  let numConstrs : nat := length constrTypes in
  let seq := (List.seq 0 numConstrs) in
  let lcargs  := 
    let constrTypes_R := map (translate ∘ headPisToLams) constrTypes in
    map (mkConstrInfo numParams) (combine seq constrTypes_R) in
  let cargsLens : list nat := (map ((@length Arg)∘IndTrans.args) lcargs) in
  let o := (CCase (tind, numParams) cargsLens) in
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


Definition translateOneInd_inducesInductive 
(indTypArgs_R (* including indices *) indTypeIndices_RR: list Arg)
(srt: STerm) (tind: inductive)
  : simple_mutual_ind STerm SBTerm
 :=
let allArgs := mrs (indTypArgs_R ++ indTypeIndices_RR) in
let indType := mkPiL allArgs srt in
let paramVars := map fst indTypArgs_R in 
  (* ensure that all of these have non-empty (unique?) names *)
let thisIndVar: V  := freshUserVar (freevars indType) "thisInd"  in
let ctype := mkApp (vterm thisIndVar) 
  ((map vterm paramVars)++ (map (vterm∘fst) indTypeIndices_RR)) (* no args *) in
let cbterm := bterm (thisIndVar::paramVars) ctype in
let tindName := (indIndicesTransName tind) in 
let oneInd : simple_one_ind STerm SBTerm := 
 (tindName, indType,  [(indIndicesConstrTransName tindName, cbterm)]) in
(map snd paramVars, [oneInd]).

(** tind is a constant denoting the inductive being processed *)
Definition translateOneInd (numParams:nat) 
  (tind : inductive*(simple_one_ind STerm STerm)) : fixDef True STerm * list defIndSq :=
  let (tind,smi) := tind in
  let (nmT, constrs) := smi in
  let (_, indTyp) := nmT in
  let indTyp_R := translate (headPisToLams indTyp) in
  let (srt, indTypArgs) := getHeadPIs indTyp in
  let (_, indTypArgs_R) := getHeadLams indTyp_R in
  let indTypArgs_R := firstn (3*length indTypArgs) indTypArgs_R in
  let srt_R := 
    match srt with 
    | mkSort s => mkSort (translateSort s) 
    | _ => srt (* should never happen *)
    end in
  let indTypeIndices : list Arg := skipn numParams indTypArgs in
  let indTypeIndices_R : list Arg := skipn (3*numParams) indTypArgs_R in
  let indTypeParams_R : list Arg := firstn (3*numParams) indTypArgs_R in
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
  let lcargs := (map snd constrs) in
  let (mb, defs) := translateIndMatchBody numParams tind v caseTypArgs srtMatch 
  indTypeParams_R indTypeIndices_RR
    indTypIndicVars lcargs in
  let body : STerm := 
    fold_right (transLam translate) (mkLamL [(v,t1); (vprime v, t2)] mb) indTypArgs in
  let typ: STerm := headLamsToPi srt_R body in
  let rarg : nat := 
      ((fun x=>(x-2)%nat)∘(@length Arg)∘snd∘getHeadPIs) typ in
  let indicesInductive :=
  translateOneInd_inducesInductive indTypArgs_R indTypeIndices_RR srt_R tind in 
  ({|fname := I ; ftype := typ; fbody := body; structArg:= rarg |}, 
    (inr indicesInductive):: map inl defs).


Definition translateMutInd (id:ident) (t: simple_mutual_ind STerm SBTerm) (i:nat)
  : STerm * list defIndSq := 
  mutIndToMutFixAux translateOneInd id t i.

(*
Definition mkExistT  (a : STerm) (A B : STerm) := 
 mkApp (mkConstr (mkInd "Coq.Init.Specif.sigT" 0) 0) [A, a, B].

Definition mkExistTL (lb: list (STerm*STerm)) (b: STerm) 
  : STerm :=
fold_right (fun p t  => mkExistT (fst p) (snd p) t) b lb.
*)


Definition tot12 (typ t1 : STerm) : (STerm (*t2*)* STerm (*tr*)):=
let T1 :=  typ in
let T2 := tvmap vprime T1 in
let T_R := translate typ in
(mkConstApp "BestTot12" [T1; T2; T_R; t1], 
mkConstApp "BestTot12R" [T1; T2; T_R; t1]).


Definition tot21 (typ t2 : STerm) : (STerm (*t2*)* STerm (*tr*)):=
let T1 := typ in
let T2 := tvmap vprime T1 in
let T_R := translate typ in
(mkConstApp "BestTot21" [T1; T2; T_R; t2], 
mkConstApp "BestTot21R" [T1; T2; T_R; t2]).

Definition translateOnePropBranch (ind : inductive) (params: list Arg)
  (ncargs : (nat*list Arg)): STerm := 
  let (constrIndex, constrArgs) :=  ncargs in
  let constr := (oterm (CConstruct ind constrIndex) []) in
  let constr := mkApp constr (map (vterm∘vprime∘fst) params) in
  let procArg  (p:Arg) (t:STerm): STerm:=
    let (v,typ) := p in 
    let T1 :=  fst typ in
    let T2 := tvmap vprime T1 in
    let (ret, lamArgs) := getHeadPIs T1 in
    let (ret, retArgs) := flattenApp ret [] in
    if (isRecursive ind ret)
    then
      let procLamArgOfArg (p:(V * STerm)) (t:STerm): STerm:=
        let (vIn,typIn) := p in 
        let T1In := typIn in
        let T2In := tvmap vprime T1In in
        let t21 := tot21 typIn (vterm (vprime vIn)) in
        mkLetIn vIn (fst t21) T1In
          (mkLetIn (vrel vIn) (snd t21)  (* typ to t1 *)
              (mkApp (translate typIn) [vterm vIn; vterm (vprime vIn)]) t) in
      let recCall : STerm := translate (mkApp ret retArgs) in
      let f1 : STerm := vterm v in
      let recArg : STerm := mkApp f1 (map (vterm∘fst) lamArgs) in
      let recRet := (mkApp recCall [recArg]) in
      let retIn := List.fold_right procLamArgOfArg recRet (map removeSortInfo lamArgs) in
      let retIn := mkLamL (map primeArg lamArgs) retIn in
      mkLetIn (vprime v) retIn T2 t
    else
      mkLetIn (vprime v) (fst (tot12 (fst typ) (vterm v))) T2
        (mkLetIn (vrel v) (snd (tot12 (fst typ) (vterm v))) 
            (mkApp (translate (fst typ)) [vterm v; vterm (vprime v)]) t) in
  let ret := mkApp constr (map (vterm∘vprime∘fst) constrArgs) in
  let ret := List.fold_right procArg ret constrArgs in
  mkLamL (map removeSortInfo constrArgs) ret.


(** tind is a constant denoting the inductive being processed *)
Definition translateOnePropTotal (numParams:nat) 
  (tind : inductive*(simple_one_ind STerm STerm)) : fixDef True STerm :=
  let (tind,smi) := tind in
  let (nmT, constrs) := smi in
  let (_, indTyp) := nmT in
  let (_, indTypArgs) := getHeadPIs indTyp in
  let indTypeIndices : list Arg := skipn numParams indTypArgs in
  let indTypeParams : list Arg := firstn numParams indTypArgs in
  let vars : list V := map fst indTypArgs in
  let t1 : STerm := (mkIndApp tind (map vterm vars)) in
  let t2 : STerm := (mkIndApp tind (map (vterm∘vprime) vars)) in (* return type *)
  let caseRetPrimeArgs := map primeArg indTypeIndices in
  let caseRetRelArgs := map translateArg indTypeIndices in
  let caseRetTyp := mkPiL (caseRetPrimeArgs++caseRetRelArgs) t2 in
  let v : V := fresh_var vars in
  let caseTyp := mkLamL (snoc (map removeSortInfo indTypeIndices) (v,t1)) caseRetTyp in
  (* [l1...ln] . li is the list of arguments (and types of those arguments) 
      of the ith constructor. *)
  let lcargs : list (list Arg) := map (snd∘getHeadPIs∘snd) constrs in
  let cargsLens : list nat := (map (@length Arg) lcargs) in
  let o := (CCase (tind, numParams) cargsLens) in
  let numConstrs : nat := length lcargs in
  let cseq := List.seq 0 numConstrs in
  let lnt : list STerm := [caseTyp; vterm v]
      ++(map (translateOnePropBranch tind indTypeParams) (combine cseq lcargs)) in
  let matcht := oterm o (map (bterm []) lnt) in
  let indTypeIndexVars := map fst indTypeIndices in
  let matchBody : STerm 
    := mkApp matcht (map vterm ((map vprime indTypeIndexVars)++ (map vrel indTypeIndexVars))) in
  let body : STerm :=
    fold_right (transLam translate) (mkLam v t1 matchBody) indTypArgs in
  let typ: STerm := headLamsToPi t2 body in
  let rarg : nat := 
      ((fun x=>(x-1)%nat)∘(@length Arg)∘snd∘getHeadPIs) typ in
  {|fname := I; ftype := typ; fbody := body; structArg:= rarg |}.


End trans.


Import MonadNotation.
Open Scope monad_scope.


Require Import List. 



Definition genParam (ienv : indEnv) (piff: bool) (b:bool) (id: ident) : TemplateMonad unit :=
  id_s <- tmQuoteSq id true;;
(*  _ <- tmPrint id_s;; *)
  match id_s with
  Some (inl t) => 
    let t_R := (translate piff ienv t) in
    trr <- tmReduce Ast.all t_R;;
    tmPrint trr  ;;
    trrt <- tmReduce Ast.all (fromSqNamed t_R);;
    tmPrint trrt  ;;
     if b then (@tmMkDefinitionSq (String.append id "_RR")  t_R) else (tmReturn tt)
  | _ => ret tt
  end.


(* no crinv. don't produce it at source if not needed *)
Definition genParamInd (ienv : indEnv) (piff: bool) (b cr:bool) (id: ident) : TemplateMonad unit :=
  id_s <- tmQuoteSq id true;;
(*  _ <- tmPrint id_s;; *)
  match id_s with
  Some (inl t) => ret tt
  | Some (inr t) =>
    let (fb, defs) := translateMutInd piff ienv id t 0 in
    let (defs , inds) := partition (isInl) defs in
      _ <- tmMkDefIndLSq inds;;
      _ <- (if b then  (tmMkDefinitionSq (indTransName (mkInd id 0)) fb) else 
      (trr <- tmReduce Ast.all (fb,defs);; tmPrint trr));;
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

Definition genParamIndTot (ienv : indEnv) (piff: bool) (b:bool) (id: ident) : TemplateMonad unit :=
  id_s <- tmQuoteSq id true;;
(*  _ <- tmPrint id_s;; *)
  match id_s with
  Some (inl t) => ret tt
  | Some (inr t) =>
    let fb := (mutIndToMutFix (translateOnePropTotal piff ienv)) id t 0%nat in
      if b then (tmMkDefinitionSq (indTransTotName (mkInd id 0)) fb) else
        (trr <- tmReduce Ast.all fb;; tmPrint trr)
  | _ => ret tt
  end.

Search fixDef.

(*
Run TemplateProgram (genParamInd mode true "ReflParam.matchR.IWT").
*)
