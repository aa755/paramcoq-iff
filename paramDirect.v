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

Require Import NArith.
Require Import Trecord.
Require Import common.



(* inline it? *)
Definition mkTyRel (T1 T2 sort: STerm) : STerm :=
  mkConstApp "ReflParam.Trecord.BestRel" [T1; T2].

(* inline it? *)
Definition projTyRel (T1 T2 T_R: STerm) : STerm := 
mkConstApp "ReflParam.Trecord.BestR" [T1; T2; T_R].

Definition isPropOrSet (s:sort) : bool :=
match s with
| sSet => true
| sProp => true
| sType _ => false
end.

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

Definition dummyVar : V := (0, nAnon).

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



Definition freshUserVar avoid sugg : V := 
  let cl :(decSubtype (fun n : N => (n < 3)%N)) := 
    userVar in
    nth 0 
    (@freshVars V (decSubtype (fun n : N => (n < 3)%N)) _ 
      1 (Some cl) avoid [(0,nNamed sugg)]) (0,nNamed sugg).

  
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
| (false, false) => "PiABType"
| (false, true) => "PiATypeBSet"
| (true, false) => "PiASetBType"
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
  String.append (mapDots "_" n) "_RR".
Require Import ExtLib.Data.String.

Definition indTransName (n:inductive) : ident :=
match n with
| mkInd s n => String.append (constTransName s) (nat2string10 n)
end.

(* delete *)
Definition primeArgsOld  (p : (V * STerm)) : (V * STerm) :=
(vprime (fst p), tvmap vprime (snd p)).

Definition primeArg  (p : Arg) : (V * STerm) :=
let (v, Typ) := p in
(vprime v, tvmap vprime (fst Typ)).

Require Import SquiggleEq.AssociationList.

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


Fixpoint constToVar (ids: AssocList ident V) (t :STerm) : STerm := 
match t  with
| mkConst s =>
    match ALFind ids s with
    | Some v => vterm v
    | None => t
    end
| vterm v => vterm v
| oterm o lbt => oterm o (map (btMapNt (constToVar ids)) lbt)
end.

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

Definition mutAllConstructors
           (id:ident) (t: simple_mutual_ind STerm SBTerm) : list (ident * STerm) :=
  flat_map (snd∘snd) (substMutIndParamsAsPi id t).


Definition substIndConstsWithVars (id:ident) (numParams numInds : nat)
(indTransName : inductive -> ident)
  : list (ident*V) :=
    let is := List.seq 0 numInds in
    let inds := map (fun n => mkInd id n) is in
    let indRNames := map indTransName inds in
    (* Fix: for robustness agains variable implementation, use FreshVars?*)
    let indRVars : list V := combine (seq (N.add 3) 0 numInds) (map nNamed indRNames) in
    combine indRNames indRVars.


Definition mutIndToMutFix 
(tone : forall (numParams:nat)(tind : inductive*(simple_one_ind STerm STerm)),fixDef STerm)
(id:ident) (t: simple_mutual_ind STerm SBTerm) (i:nat)
  : STerm :=
    let onesS := substMutInd id t in
    let numInds := length onesS in
    let numParams := length (fst t) in
    let tr: list (fixDef STerm)
      := map (tone numParams) onesS in
    let constMap := substIndConstsWithVars id numParams numInds indTransName in
    let indRVars := map snd constMap  in
    let o: CoqOpid := (CFix numInds i (map (@structArg STerm) tr)) in
    let bodies := (map ((bterm indRVars)∘(constToVar constMap)∘(@fbody STerm)) tr) in
    reduce 100 (oterm o (bodies++(map ((bterm [])∘(@ftype STerm)) tr))).

Definition numberElems {A:Type }(l: list A) : list (nat*A) :=
  combine (List.seq 0 (length l)) l.

Definition separate_Rs {A:Type }(l: list A) : (list A (* _Rs *) * list A (* the rest *)) 
:=
let ls := combine (seq N.succ 0 (length l)) l in
let (l,r) := partition (fun p => decide ((fst p) mod 3 = 2)) ls in
(map snd l, map snd r).

(** to be used when we don't yet know how to produce a subterm *)
Axiom F: False.
Definition fiat (T:Type) : T := @False_rect T F.


Definition indEnv:  Type := AssocList ident (simple_mutual_ind STerm SBTerm).

Definition dummyInd : simple_one_ind STerm SBTerm :=
  ("", oterm CUnknown [], []).

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

(*
Definition matchProcessConstructors
           (np: nat)
           (cargs : list (V*STerm))
           (discTParams : list STerm)
           (ctype : (nat*SBTerm)) : list STerm :=
  let (thisConstrNum, thisConstrTyp) := ctype in
  (* let restArgs := skipn ncargs args in *)
  let thisConstrTyp : STerm := apply_bterm thisConstrTyp discTParams in
  let thisConstrTyp : STerm := headPisToLams thisConstrTyp in
  let cargst := (map (vterm∘fst) cargs) in
  let thisConstrRetTyp : STerm := mkAppBeta thisConstrTyp cargst in
  let (_,cRetTypArgs) := flattenApp thisConstrRetTyp [] in
  let cRetTypIndices := skipn np cRetTypArgs in
  cRetTypIndices.
*)

(* take the variables denoting constructor arguments in the original match branch
lambda and get the full constructor and the indices in its return type *)
Definition matchProcessConstructors
           (np: nat)
           (tind: inductive)
           (discTParams  : list STerm) (bnc : (nat (* remove*) * STerm)*(nat*SBTerm)) :
  (STerm * list STerm) :=
  let (bn, thisConstrTyp) := bnc in
  let (_, b) := bn in
  let (_, bargs) := getHeadLams b in (* assuming there are no letins *)
  let (thisConstrNum, thisConstrTyp) := thisConstrTyp in
  (* let restArgs := skipn ncargs args in *)
  let thisConstrTyp : STerm := apply_bterm thisConstrTyp discTParams in
  let (constrRetTyp, constrArgs) := getHeadPIs thisConstrTyp in
  let bargs := firstn (length constrArgs) bargs in
  let bargs := map (vterm∘fst) bargs in
  let constrArgVars := map fst constrArgs in
  let thisConstrRetTyp : STerm := ssubst_aux constrRetTyp
     (combine constrArgVars bargs) in
  let (_,cRetTypArgs) := flattenApp thisConstrRetTyp [] in
  let cRetTypIndices := skipn np cRetTypArgs in
  let thisConstr := mkConstr tind thisConstrNum in
  let thisConstrFull := mkApp thisConstr (discTParams++bargs) in
  (thisConstrFull, cRetTypIndices).

Definition transMatchBranchInner
           (*translate: STerm -> STerm*) (*np: nat*)
           (*tind: inductive*)
           (retTypLamPartiallyApplied : list STerm -> STerm)
           (bnc : (nat *  STerm)*(STerm * list STerm)) : STerm :=
  let (brn, thisConstrInfo) := bnc in
  let (thisConstrFull, thisConstrRetTypIndices) := thisConstrInfo in
  let retTyp := retTypLamPartiallyApplied
                  (map tprime (snoc thisConstrRetTypIndices thisConstrFull)) in
  let (ncargs, b) := brn in
  let (_, args) := getHeadLams b in (* assuming there are no letins *)
  let cargs2 := map removeSortInfo (firstn ncargs args) in
  let cargs2 := map primeArgsOld cargs2 in
  let (retTypBody,pargs) := getHeadPIs retTyp in
  let ret := mkConstApp "fiat" [retTypBody] in
  mkLamL cargs2 (mkLamL (map removeSortInfo pargs) ret).

  (* let (ret, args) := getHeadLams b in (* assuming there are no letins *)
  let cargs := firstn ncargs args in
  let restArgs := skipn ncargs args in 
  let matchRetTyp := mkLamL retArgs matchRetTyp in retTypLam.
   *)

Definition transMatchBranch (translate: STerm -> STerm) (o: CoqOpid) (np: nat)
           (tind: inductive)
           (allBnc : list ((nat *  STerm)*(STerm * list STerm)))
           (retTypLam : STerm) (retArgs1: list (V*STerm))
           (disc2: STerm)
           (bnc: (nat *  STerm)*(STerm * list STerm)) : STerm :=
  let (brn, thisConstrInfo) := bnc in
  let (ncargs, b) := brn in
  let (thisConstrFull, thisConstrRetTypIndices) := thisConstrInfo in
  let retArgs2 := map primeArgsOld retArgs1 in
  let (ret, args) := getHeadLams b in (* assuming there are no letins *)
  let cargs := map removeSortInfo (firstn ncargs args) in
  let cargs2 := map primeArgsOld cargs in
  (* let restArgs := skipn ncargs args in *)
  let oneRetArgs1 := (snoc thisConstrRetTypIndices thisConstrFull) in
  let brs :=
      (* this must be AppBeta because we need to analyse the simplified result *)
      let retTypLamPartial args2 := mkAppBeta retTypLam (merge oneRetArgs1 args2) in
      map (transMatchBranchInner retTypLamPartial) allBnc in
  let matchRetTyp :=
    mkApp retTypLam (merge oneRetArgs1 (map (vterm∘fst) retArgs2)) in
  let matchRetTyp := mkLamL retArgs2 matchRetTyp in
  mkLamL cargs
    (oterm o ((bterm [] matchRetTyp):: (bterm [] disc2)::(map (bterm []) brs))).


Definition transMatch (translate: STerm -> STerm) (ienv: indEnv) (tind: inductive)
           (numIndParams: nat) (lNumCArgs : list nat) (retTyp disc discTyp : STerm)
           (branches : list STerm) : STerm :=
  let o := (CCase (tind, numIndParams) lNumCArgs) in
  let (_, retArgs) := getHeadLams retTyp in
  let vars := map fst retArgs in
  let lastVar := last vars dummyVar in
  let mt := oterm o ((bterm [] retTyp):: (bterm [] (vterm lastVar))
                                      :: (bterm [] discTyp)::(map (bterm []) branches)) in
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
  let discTypIndicesR :=
      let (_, discTypArgsR) := flattenApp (translate discTyp) [] in
      fst (separate_Rs (skipn (3*numIndParams) discTypArgsR)) in
  let constrTyps := map snd (snd (lookUpInd ienv tind)) in
  let branchPackets := combine (combine lNumCArgs branches) (numberElems constrTyps) in
  let pbranchPackets :=
      map (matchProcessConstructors numIndParams tind discTypParams) branchPackets in
  let branchPackets :=
      combine (combine lNumCArgs branches) pbranchPackets in
  let retArgs := map removeSortInfo retArgs in
  let brs := 
      map (transMatchBranch
             translate
             o numIndParams tind branchPackets retTypLam
             retArgs (tprime disc)) branchPackets in
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
  transMatch translate ienv tind numIndParams lNumCArgs retTyp disc discTyp (map get_nt lb)
| _ => oterm CUnknown []
end.


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


Definition translateIndInnerMatchBranch tind (argsB: bool * list Arg) : STerm :=
  let (b,args) := argsB in
  let t := boolToProp b in
  let ret :=
   (if b  then (mkSigL (map (translateConstrArg tind) args) t) else t)
  in
  mkLamL (map primeArg args) ret.


(* List.In  (snd lb)  cargs
Inline? *)
Definition translateIndInnerMatchBody tind o (lcargs: list (list Arg))
   v mTyInfo (lb: (list bool)*(list Arg)) :=
  let lnt : list STerm := [tvmap vprime mTyInfo; vterm (vprime v)]
      ++(map (translateIndInnerMatchBranch tind) (combine ((fst lb)) lcargs)) in
  mkLamL (map removeSortInfo (snd lb)) (oterm  o (map (bterm []) lnt)).


Definition translateIndMatchBody (numParams:nat) 
  tind v (mTyInfo:  STerm)
  (lcargs : list (list Arg)): STerm :=
  let cargsLens : list nat := (map (@length Arg) lcargs) in
  let o := (CCase (tind, numParams) cargsLens) in
  let numConstrs : nat := length lcargs in
  let lb : list (list bool):= map (boolNthTrue numConstrs) (List.seq 0 numConstrs) in
  let lnt : list STerm := [mTyInfo; vterm v]
      ++(map (translateIndInnerMatchBody tind o lcargs v mTyInfo) (combine lb lcargs)) in
    oterm o (map (bterm []) lnt).


(** tind is a constant denoting the inductive being processed *)
Definition translateOneInd (numParams:nat) 
  (tind : inductive*(simple_one_ind STerm STerm)) : fixDef STerm :=
  let (tind,smi) := tind in
  let (nmT, constrs) := smi in
  let (_, indTyp) := nmT in
  let (srt, indTypArgs) := getHeadPIs indTyp in
  let indTypeIndices := skipn numParams indTypArgs in
  let srt := 
    match srt with 
    | mkSort s => mkSort (translateSort s) 
    | _ => srt (* should never happen *)
    end in
  let vars : list V := map fst indTypArgs in
  let t1 : STerm := (mkIndApp tind (map vterm vars)) in
  let t2 : STerm := (mkIndApp tind (map (vterm∘vprime) vars)) in
  (* local section variables could be a problem. Other constants are not a problem*)
  let v : V := fresh_var vars in
  let caseTyp := mkLamL (snoc (map removeSortInfo indTypeIndices) (v,t1)) srt in
  (* [l1...ln] . li is the list of arguments (and types of those arguments) 
      of the ith constructor. *)
  let lcargs : list (list Arg) := map (snd∘getHeadPIs∘snd) constrs in
  let mb := translateIndMatchBody numParams tind v caseTyp lcargs in
  let body : STerm := 
    fold_right (transLam translate) (mkLamL [(v,t1); (vprime v, t2)] mb) indTypArgs in
  let typ: STerm := headLamsToPi srt body in
  let rarg : nat := 
      ((fun x=>(x-2)%nat)∘(@length Arg)∘snd∘getHeadPIs) typ in
  {|ftype := typ; fbody := body; structArg:= rarg |}.


Definition translateMutInd (id:ident) (t: simple_mutual_ind STerm SBTerm) (i:nat)
  : STerm := (mutIndToMutFix translateOneInd id t i).

Definition translateConstructor (c: ident * STerm)
  : list (ident*STerm).
Abort.

Definition translateConstructors (id: ident )(t: simple_mutual_ind STerm SBTerm) 
: list (ident*STerm) :=
mutAllConstructors id t.

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
  (tind : inductive*(simple_one_ind STerm STerm)) : fixDef STerm :=
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
  {|ftype := typ; fbody := body; structArg:= rarg |}.


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

Definition indTransTotName (n:inductive) : ident :=
match n with
| mkInd s n => String.append (String.append (constTransName s) "_tot_") (nat2string10 n)
end.


Definition genParamInd (ienv : indEnv) (piff: bool) (b:bool) (id: ident) : TemplateMonad unit :=
  id_s <- tmQuoteSq id true;;
(*  _ <- tmPrint id_s;; *)
  match id_s with
  Some (inl t) => ret tt
  | Some (inr t) =>
    let fb := translateMutInd piff ienv id t 0 in
      if b then (tmMkDefinitionSq (indTransName (mkInd id 0)) fb) 
      (* repeat for other inds in the mutual block *)
      else (trr <- tmReduce Ast.all fb;; tmPrint trr)
  | _ => ret tt
  end.

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

Declare ML Module "paramcoq".

Parametricity Recursive ids.

Definition appTest  := fun (A : Set) (B: forall A, Set) (f: (forall a:A, B a)) (a:A)=>
 f a.

Let mode := true.


Definition ids : forall A : Set, A -> A := fun (A : Set) (x : A) => x.
Definition idsT  := forall A : Set, A -> A.

(*
Run TemplateProgram (genParamInd mode true "ReflParam.matchR.IWT").
*)

(* reification of this fails
Inductive NatLike (A B:Set) (C: (A->B) -> Set): Set := 
| SS : forall (f:A->B), C f -> NatLike A B C.
*)

Inductive NatLike (A:Set) (C: A-> Set): Set := 
(* | SS : forall (f:A->B) (c:C f)  (d:forall a:A, NatLike A B C)
     (e:forall (fi:A->B) (ci:C fi), NatLike A B C), NatLike A B C *)
 | SS2 :  forall (d:forall a:A,NatLike A C),
       NatLike A C.
       

Require Import PIWNew.
Run TemplateProgram (genParamInd [] mode true "Coq.Init.Datatypes.nat").

Require Import matchR. (* shadows Coq.Init.Datatypes.list *)
Require Import List.
Run TemplateProgram (printTerm "ReflParam.PIWNew.IWT").

Run TemplateProgram (printTermSq "ReflParam.PIWNew.IWT").

Run TemplateProgram (mkIndEnv "indTransEnv" ["ReflParam.matchR.Vec"]).


(*suceeds: Run TemplateProgram (genParamInd false true "ReflParam.PIWNew.IWT"). *)
Run TemplateProgram (genParamInd [] false true "ReflParam.matchR.Vec").

Notation Vec_RR := ReflParam_matchR_Vec_RR0.


Notation nat_RR :=  Coq_Init_Datatypes_nat_RR0.

Definition S_RR (n1 n2 : nat) 
  (n_R : nat_RR n1 n2) : nat_RR (S n1) (S n2) :=
@existT _ _ n_R I.

Definition O_RR : nat_RR O O := I.


Fixpoint Coq_Init_Nat_add_RR (n1 n2 : nat) (n_R : nat_RR n1 n2) (m1 m2 : nat) (m_R : nat_RR m1 m2):
nat_RR (n1 + m1) (n2 + m2) :=
let reT := fun n1 n2 => nat_RR n1 n2 -> nat_RR (n1 + m1) (n2 + m2) in
(match n1 return reT n1 n2 with
| 0 => 
  match n2 return reT 0 n2 with
  | 0 => fun _ => m_R
  | S _ => fun n_R => False_rect _ n_R
  end
| S p1 =>
  match n2 return reT (S p1) n2 with
  | 0 => fun n_R => False_rect _ n_R
  | S p2 => fun n_R =>
             let n_R := projT1 n_R in
             S_RR _ _ (Coq_Init_Nat_add_RR p1 p2 n_R m1 m2 m_R)
  end
end) n_R.

Notation add_RR := Coq_Init_Nat_add_RR.

Definition vcons_RR {C₁ C₂ : Set} {C_R : C₁ -> C₂ -> Prop}
(n₁ n₂ : nat) (n_R : nat_RR n₁ n₂)
 (H : C₁) (H0 : C₂) (c_R: C_R H H0)
 (H1 : Vec C₁ n₁) (H2 : Vec C₂ n₂)
 (v_R : Vec_RR C₁ C₂ C_R n₁ n₂ n_R H1 H2):
  Vec_RR C₁ C₂ C_R (S n₁) (S n₂) (S_RR n₁ n₂ n_R)
  (vcons C₁ n₁ H H1) (vcons C₂ n₂ H0 H2) :=
  existT
  (fun n_R0 : nat_RR n₁ n₂ =>
   {_ : C_R H H0 & {_ : Vec_RR C₁ C₂ C_R n₁ n₂ n_R0 H1 H2 & True}}) n_R
  (existT (fun _ : C_R H H0 => {_ : Vec_RR C₁ C₂ C_R n₁ n₂ n_R H1 H2 & True}) c_R
     (existT (fun _ : Vec_RR C₁ C₂ C_R n₁ n₂ n_R H1 H2 => True) v_R I)).
(*
Proof.
simpl. eexists; eexists; eauto.
Defined.
*)

Fixpoint ReflParam_matchR_vAppend_RR {C₁ C₂ : Set} {C_R : C₁ -> C₂ -> Prop} (n₁ n₂ : nat) 
   (n_R : nat_RR n₁ n₂) (m₁ m₂ : nat) (m_R : nat_RR m₁ m₂)
   (vl₁ : Vec C₁ n₁) (vl₂ : Vec C₂ n₂)
   (vl_R : Vec_RR C₁ C₂ C_R n₁ n₂ n_R vl₁ vl₂)
   (vr₁ : Vec C₁ m₁) (vr₂ : Vec C₂ m₂)
   (vr_R : Vec_RR C₁ C₂ C_R m₁ m₂ m_R vr₁ vr₂) {struct vl₁ }:
    Vec_RR C₁ C₂ C_R (n₁ + m₁) (n₂ + m₂) (add_RR n₁ n₂ n_R m₁ m₂ m_R)
         (vAppend vl₁ vr₁) (vAppend vl₂ vr₂) :=
let reT := fun n₁ vl₁ n₂ vl₂ => 
forall n_R: nat_RR n₁ n₂,
Vec_RR C₁ C₂ C_R n₁ n₂ n_R vl₁ vl₂
-> 
Vec_RR C₁ C₂ C_R (n₁ + m₁) (n₂ + m₂) (add_RR n₁ n₂ n_R m₁ m₂ m_R)
         (vAppend vl₁ vr₁) (vAppend vl₂ vr₂)  in 
(match vl₁ in Vec _ n₁ return reT n₁ vl₁ n₂ vl₂ with
| vnil _ =>  
  match vl₂ in (Vec _ n₂) return reT 0 (vnil _) n₂ vl₂ with
  | vnil _ => fun _ _ => vr_R
  | vcons _ _ _ _ => fun _ v_R => False_rect _ v_R
  end

| vcons _ n₁ hl₁ tl₁ => 
  match vl₂ in (Vec _ n₂) return reT (S n₁) (vcons _ n₁ hl₁ tl₁) n₂ vl₂ with
  | vnil _ =>  fun _ v_R => False_rect _ v_R
  | vcons _ _ hl₂ tl₂ => fun _ v_R =>
    let v_R := projT2 v_R in
    let hl_R := projT1 v_R in
    let tl_R := projT1 (projT2 v_R) in
    (vcons_RR _ _ _ _ _ hl_R _ _ (ReflParam_matchR_vAppend_RR _ _ _ _ _ _ _ _  tl_R  _ _ vr_R))
  end
end) n_R vl_R.

Notation vAppend_RR := ReflParam_matchR_vAppend_RR.

Print sigT_rect.

Print ReflParam_matchR_Vec_RR0.
Print projT1.
Print projT2.

Definition vAppend2_RR (C₁ C₂ : Set) (C_R : C₁ -> C₂ -> Prop) (m₁ m₂ : nat) 
  (m_R : nat_RR m₁ m₂)
  (cdef₁ : C₁) (cdef₂ : C₂) (cdef_R : C_R cdef₁ cdef₂)
  (vr₁ : Vec C₁ m₁) (vr₂ : Vec C₂ m₂) (vr : Vec_RR C₁ C₂ C_R m₁ m₂ m_R vr₁ vr₂):
  C_R (vAppend2  cdef₁ vr₁) (vAppend2 cdef₂ vr₂) :=
(
let reT n1 n2 v1 v2 (* indices and values. move the _Rs to the body, as Pi args  *) :=
      forall (nr: nat_RR n1 n2)
        (vapr: Vec_RR C₁ C₂ C_R n1 n2 nr v1 v2),
     C_R match v1 with
      | vnil _ => cdef₁
      | vcons _ _ hl _ => hl
      end match v2 with
          | vnil _ => cdef₂
          | vcons _ _ hl _ => hl
          end in

(* the "as vap1" part cannot be inlined.
"vAppend vr₁ vr₁" has type "Vec C₁ (m₁ + m₁)" while vap1 has type "Vec C₁ n1"
*)
match vAppend vr₁ vr₁ as vap1 in Vec _ n1
  return reT n1 (m₂+m₂)(*prime of index of discriminee *) 
      vap1 (vAppend vr₂ vr₂) (* prime of discriminee*)
with
| vnil _ => 
    match vAppend vr₂ vr₂ as vap2 in Vec _ n2
      return reT O (*index of this constr:vnil*) n2 (* from in *)
          (vnil _) vap2
      with  
      | vnil _ => fun (nr : nat_RR 0 0) (_ : Vec_RR C₁ C₂ C_R 0 0 nr (vnil C₁) (vnil C₂))  => cdef_R
      | vcons _ n2 hl2 v2 =>
        fun (nr : nat_RR 0 (S n2))
          (vr0 : Vec_RR C₁ C₂ C_R 0 (S n2) nr (vnil C₁) (vcons C₂ n2 hl2 v2))
        => False_rect
            (*reT 0 (S n2) (vnil C₁) (vcons C₂ n2 hl2 v2) nr vr0 -- then strip the 2 pis*)
            _ vr0 (* always the last lambda *)
      end
| vcons _ n1 hl tl =>
    match vAppend vr₂ vr₂ as vap2 in Vec _ n2
      return reT (S n1) (*index of this constr*) n2 (* from in *)
          (vcons _ _ hl tl) vap2
      with  
      | vnil _ => fun _ vr => False_rect _ vr
      | vcons _ _ hl _ => fun _ v_R =>
    let v_R := projT2 v_R in
    let hl_R := projT1 v_R in
    let tl_R := projT1 (projT2 v_R)
        in hl_R
      end

end (add_RR m₁ m₂ m_R m₁ m₂ m_R) 
  (vAppend_RR _ _ _ _ _ _ _ _ vr _ _ vr)
).
Check indTransEnv.
Eval compute in (map (fun p => translateConstructors (fst p) (snd p)) indTransEnv).
(*
     = [[("vnil",
         mkPiS (0%N, nNamed "C") (mkSort sSet) None
           (oterm (CApply 2)
              [bterm [] (mkConstInd (mkInd "ReflParam.matchR.Vec" 0));
              bterm [] (vterm (0%N, nNamed "C"));
              bterm [] (mkConstr (mkInd "Coq.Init.Datatypes.nat" 0) 0)]) None);
        ("vcons",
        mkPiS (0%N, nNamed "C") (mkSort sSet) None
          (mkPiS (6%N, nNamed "n") (mkConstInd (mkInd "Coq.Init.Datatypes.nat" 0))
             (Some sSet)
             (mkPiS (9%N, nAnon) (vterm (0%N, nNamed "C")) (Some sSet)
                (mkPiS (12%N, nAnon)
                   (oterm (CApply 2)
                      [bterm [] (mkConstInd (mkInd "ReflParam.matchR.Vec" 0));
                      bterm [] (vterm (0%N, nNamed "C"));
                      bterm [] (vterm (6%N, nNamed "n"))]) (Some sSet)
                   (oterm (CApply 2)
                      [bterm [] (mkConstInd (mkInd "ReflParam.matchR.Vec" 0));
                      bterm [] (vterm (0%N, nNamed "C"));
                      bterm []
                        (oterm (CApply 1)
                           [bterm [] (mkConstr (mkInd "Coq.Init.Datatypes.nat" 0) 1);
                           bterm [] (vterm (6%N, nNamed "n"))])]) 
                   (Some sSet)) (Some sSet)) (Some sSet)) None)]]
     : Datatypes.list (Datatypes.list (ident * STerm))
*)
Run TemplateProgram (genParam indTransEnv false true "vAppend2"). (* success!*)
Print vAppend2_RR.

(*
vAppend2_RR = 
fun (C C₂ : Set) (C_R : C -> C₂ -> Prop) (m m₂ : nat) (m_R : nat_RR m m₂) 
  (cdef : C) (cdef₂ : C₂) (_ : C_R cdef cdef₂) (vr : Vec C m) (vr₂ : Vec C₂ m₂)
  (vr_R : Vec_RR C C₂ C_R m m₂ m_R vr vr₂) =>
match
  vAppend vr vr as vapx in (Vec _ n)
  return
    (forall n_R : nat_RR n (m₂ + m₂),
     Vec_RR C C₂ C_R n (m₂ + m₂) n_R vapx (vAppend vr₂ vr₂) ->
     C_R match vapx with
         | vnil _ => cdef
         | vcons _ _ hl _ => hl
         end match vAppend vr₂ vr₂ with
             | vnil _ => cdef₂
             | vcons _ _ hl₂ _ => hl₂
             end)
with
| vnil _ =>
    match
      vAppend vr₂ vr₂ as vapx₂ in (Vec _ n₂)
      return
        (forall n_R : nat_RR 0 n₂,
         Vec_RR C C₂ C_R 0 n₂ n_R (vnil C) vapx₂ ->
         C_R cdef match vapx₂ with
                  | vnil _ => cdef₂
                  | vcons _ _ hl₂ _ => hl₂
                  end)
    with
    | vnil _ =>
        fun (n_R : nat_RR 0 0) (_ : Vec_RR C C₂ C_R 0 0 n_R (vnil C) (vnil C₂)) =>
        fiat
          (C_R match vnil C with
               | vnil _ => cdef
               | vcons _ _ hl _ => hl
               end match vnil C₂ with
                   | vnil _ => cdef₂
                   | vcons _ _ hl₂ _ => hl₂
                   end)
    | vcons _ n'₂ hl₂ tl₂ =>
        fun (n_R : nat_RR 0 (S n'₂))
          (_ : Vec_RR C C₂ C_R 0 (S n'₂) n_R (vnil C) (vcons C₂ n'₂ hl₂ tl₂)) =>
        fiat
          (C_R match vnil C with
               | vnil _ => cdef
               | vcons _ _ hl _ => hl
               end
             match vcons C₂ n'₂ hl₂ tl₂ with
             | vnil _ => cdef₂
             | vcons _ _ hl₂0 _ => hl₂0
             end)
    end
| vcons _ n' hl tl =>
    match
      vAppend vr₂ vr₂ as vapx₂ in (Vec _ n₂)
      return
        (forall n_R : nat_RR (S n') n₂,
         Vec_RR C C₂ C_R (S n') n₂ n_R (vcons C n' hl tl) vapx₂ ->
         C_R hl match vapx₂ with
                | vnil _ => cdef₂
                | vcons _ _ hl₂ _ => hl₂
                end)
    with
    | vnil _ =>
        fun (n_R : nat_RR (S n') 0)
          (_ : Vec_RR C C₂ C_R (S n') 0 n_R (vcons C n' hl tl) (vnil C₂)) =>
        fiat
          (C_R match vcons C n' hl tl with
               | vnil _ => cdef
               | vcons _ _ hl0 _ => hl0
               end match vnil C₂ with
                   | vnil _ => cdef₂
                   | vcons _ _ hl₂ _ => hl₂
                   end)
    | vcons _ n'₂ hl₂ tl₂ =>
        fun (n_R : nat_RR (S n') (S n'₂))
          (_ : Vec_RR C C₂ C_R (S n') (S n'₂) n_R (vcons C n' hl tl) (vcons C₂ n'₂ hl₂ tl₂))
        =>
        fiat
          (C_R match vcons C n' hl tl with
               | vnil _ => cdef
               | vcons _ _ hl0 _ => hl0
               end
             match vcons C₂ n'₂ hl₂ tl₂ with
             | vnil _ => cdef₂
             | vcons _ _ hl₂0 _ => hl₂0
             end)
    end
end (add_RR m m₂ m_R m m₂ m_R)
  (ReflParam_matchR_vAppend_RR m m₂ m_R m m₂ m_R vr vr₂ vr_R vr vr₂ vr_R)
     : forall (C C₂ : Set) (C_R : C -> C₂ -> Prop) (m m₂ : nat) 
         (m_R : nat_RR m m₂) (cdef : C) (cdef₂ : C₂),
       C_R cdef cdef₂ ->
       forall (vr : Vec C m) (vr₂ : Vec C₂ m₂),
       Vec_RR C C₂ C_R m m₂ m_R vr vr₂ ->
       C_R match vAppend vr vr with
           | vnil _ => cdef
           | vcons _ _ hl _ => hl
           end match vAppend vr₂ vr₂ with
               | vnil _ => cdef₂
               | vcons _ _ hl₂ _ => hl₂
               end
*)

Run TemplateProgram (genParamInd [] mode true "ReflParam.PIWNew.IWT"). 


(* nat must  have a BestRel 
Run TemplateProgram (genParamInd true true "ReflParam.matchR.Vec").
*)

Run TemplateProgram (genParamInd [] mode true "ReflParam.paramDirect.NatLike").



Eval compute in  ReflParam.paramDirect.NatLike.


Run TemplateProgram (genParam [] mode true "appTest").
Eval compute in appTest_RR.

Run TemplateProgram (genParam [] mode true "idsT").
Eval compute in idsT_RR.

Print idsT.

Parametricity idsT.

(* Given f: some Pi Type, prove that the new theorem implies the old *)
Eval vm_compute in idsT_RR.


Run TemplateProgram (genParam [] mode true "ids").
Eval compute in ids_RR.

Definition idsTT  := fun A : Set => forall a:A, A.

Parametricity Recursive idsTT.

Run TemplateProgram (genParam [] mode true "idsTT").
Eval compute in idsTT_RR.

Print idsTT_RR.

Definition s := Set.
Run TemplateProgram (genParam [] mode  true "s").

Eval compute in s_RR.

Definition propIff : Type := forall A:Set, Prop.

Run TemplateProgram (genParam [] mode true "propIff").

Eval compute in propIff_RR.

Definition propIff2 : Prop := forall A:Prop, A.

Run TemplateProgram (genParam [] mode  true "propIff2").

Run TemplateProgram (printTerm "propIff2").

Eval compute in propIff2_RR.

Goal propIff2_RR = fun _ _ => True.
unfold propIff2_RR.
Print PiTSummary.
unfold PiATypeBSet. simpl.
Print PiATypeBSet.
Abort.

Definition p := Prop.
Run TemplateProgram (genParam [] mode  true "p").

Eval compute in p_RR.
