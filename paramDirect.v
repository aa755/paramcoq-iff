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


Require Import Program.
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

Definition getSort (t:STerm) : option sort :=
match t with
| mkCast t _ (mkSort s) => Some s
| _ => None
end.

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


Require Import PiTypeR.

(* can be used only find binding an mkPi whose body has NO free variables at all,
e.g. Set *)
(* Definition dummyVar : V := (0, nAnon). *)

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
let f1l : list V := 
  let cl :(decSubtype (fun n : N => (n < 3)%N)) := 
    userVar in
    (@freshVars V (decSubtype (fun n : N => (n < 3)%N)) _ 
      1 (Some cl) (a1::allVars) [changeVarName a1 "ff"]) in
match f1l with
| f1::_ =>
let a2 := vprime a1 in
let ar := vrel a1 in
let f2 := vprime f1 in
let A_R := if Asp then projTyRel A1 A2 A_R else A_R in
let B_R := mkAppBeta B_R [vterm a1; vterm a2; vterm ar] in
let B_R := if Bsp then projTyRel (mkAppBeta B1 [vterm a1]) (mkAppBeta B2 [vterm a2])
     B_R else B_R in
mkLamL [(f1, mkPi a1 A1 (mkAppBeta B1 [vterm a1])) ; (f2, mkPi a2 A2 (mkAppBeta B2 [vterm a2]))]
(mkPiL [(a1,A1); (a2,A2) ; (ar, mkAppBeta A_R [vterm a1; vterm a2])]
   (mkAppBeta B_R [mkApp (vterm f1) [vterm a1]; mkApp (vterm f2) [vterm a2]]))
| _ => A1 (* impossible *)
end.


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


Fixpoint removeCastsAroundInd (tind: inductive) (t:STerm) : (STerm) :=
match t with
| mkPi x A B 
  => mkPi x A (removeCastsAroundInd tind B) (* strict positivity => tind cannot appear in A *)
| mkCast tc _ (mkSort sProp)
| mkCast tc _ (mkSort sSet) => (removeCastsAroundInd tind tc)
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
(** TODO: inline *)
Definition translateIndMatchBranch (argsB: STerm * list (V * STerm)) : STerm :=
  let (ret,args) := argsB in
  mkLamL args ret.

Definition primeArgs  (p : (V * STerm)) : (V * STerm) :=
(vprime (fst p), tvmap vprime (snd p)).

Require Import SquiggleEq.AssociationList.

(* vars are names along with numbers. *)
Definition getParamAsVars (numParams:nat)
  (l:list (simple_one_ind STerm SBTerm)) : list (V*STerm):=
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
Definition substMutInd (id:ident) (t: simple_mutual_ind STerm SBTerm)
:list (inductive* simple_one_ind STerm STerm) :=
    let (params,ones) := t  in
    let numInds := (length ones) in
    let is := List.seq 0 numInds in
    let inds := map (fun n => mkInd id n) is in
    let numParams := (length params) in
    (* Fix: for robustness agains variable implementation, use FreshVars?*)
    let lp := getParamAsVars numParams ones in
    let paramVars := map (vterm∘fst) lp in
    let indsParams : list STerm := (map (fun t => mkConstInd t) inds)++ paramVars in
    let onesS := map (mapTermSimpleOneInd
       (@Datatypes.id STerm)
       (fun b: SBTerm => apply_bterm b indsParams)) ones in
       combine inds onesS.

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
     (oterm o (bodies++(map ((bterm [])∘(@ftype STerm)) tr))).

(** to be used when we don't yet know how to produce a subterm *)
Axiom F: False.
Definition fiat (T:Type) : T := @False_rect T F.

Section trans.
Variable piff:bool.
Let removeHeadCast := if piff then removeHeadCast else id.
Let hasSortSetOrProp := if piff then hasSortSetOrProp else (fun _ => false).
Let projTyRel := if piff then projTyRel else (fun _ _ t=> t).
Let mkTyRel := if piff then mkTyRel else mkTyRelOld.

(** AR is of type BestRel A1 A2 or A1 -> A2 -> Type. project out the relation
in the former case. 
Definition maybeProjRel (A1 A2 AR : STerm) :=
   if (hasSortSetOrProp A) then 
           (fun t => projTyRel A1 A2 AR)
      else AR.
*)

Definition transLamAux translate  (nma : V*STerm) : ((STerm * STerm)*STerm) :=
  let (nm,A) := nma in
  let A1 := (removeHeadCast A) in
  let A2 := tvmap vprime A1 in
  let f := if (hasSortSetOrProp A) then 
           (fun t => projTyRel A1 A2 t)
      else id in
  (A1, A2, f (translate A)).

Definition transLam (translate : STerm -> STerm) (nma : V*STerm) b :=
  let (A12, AR) := transLamAux translate nma in
  let (A1, A2) := A12 in
  let nm := fst nma in
  mkLamL [(nm, A1);
            (vprime nm, A2);
            (vrel nm, mkAppBeta AR [vterm nm; vterm (vprime nm)])]
         b.

Definition transMatch (translate: STerm -> STerm) (tind: inductive)
  (numIndParams: nat) (lNumCArgs : list nat) (retTyp disc : STerm) 
  (branches : list STerm) : STerm :=
  let o := (CCase (tind, numIndParams) lNumCArgs) in
  let discInner := tvmap vprime disc in
  let retTypOuter := disc in 
  disc.

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
| mkLam nm A b => transLam (translate ) (nm,A) (translate b)
| mkPi nm A B =>
  let A1 := (removeHeadCast A) in
  let A2 := tvmap vprime A1 in
  let B1 := (mkLam nm A1 (removeHeadCast B)) in
  let B2 := tvmap vprime B1 in
  let B_R := transLam translate (nm,A) (translate (removeHeadCast B)) in
  let Asp := (hasSortSetOrProp A) in
  let Bsp := (hasSortSetOrProp B) in
   mkPiR Asp Bsp nm A1 A2 (translate A) B1 B2 B_R
(* the translation of a lambda always is a lambda with 3 bindings. So no
projection of LHS should be required *)
| oterm (CApply _) (fb::argsb) =>
    mkAppBeta (translate (get_nt fb)) (flat_map (appArgTranslate translate) argsb)
(* Const C needs to be translated to Const C_R, where C_R is the registered translation
  of C. Until we figure out how to make such databases, we can assuming that C_R =
    f C, where f is a function from strings to strings that also discards all the
    module prefixes *)
| oterm (CCase (tind, numIndParams) lNumCArgs) ((bterm [] retTyp):: (bterm [] disc)::lb) =>
  transMatch translate tind numIndParams lNumCArgs retTyp disc (map get_nt lb)
| _ => oterm CUnknown []
end.


Definition tot12 (typ t1 : STerm) : (STerm (*t2*)* STerm (*tr*)):=
let T1 := (removeHeadCast typ) in
let T2 := tvmap vprime T1 in
let T_R := translate typ in
(mkConstApp "BestTot12" [T1; T2; T_R; t1], 
mkConstApp "BestTot12R" [T1; T2; T_R; t1]).


Definition tot21 (typ t2 : STerm) : (STerm (*t2*)* STerm (*tr*)):=
let T1 := (removeHeadCast typ) in
let T2 := tvmap vprime T1 in
let T_R := translate typ in
(mkConstApp "BestTot21" [T1; T2; T_R; t2], 
mkConstApp "BestTot21R" [T1; T2; T_R; t2]).


    
Definition translateArg  (p : (V * STerm)) : (V * STerm) :=
(* todo: take remove Cast from applications of the inductive type being translated.
Or after translation, remove BestR.
Or remove Goodness all over in this part of the definition. In the outer definition,
map it back*)
let (_, AR) := transLamAux translate p in
let (v,_) := p in
(vrel v, mkAppBeta AR [vterm v; vterm (vprime v)]).

Definition translateConstrArg tind (p : (V * STerm)) : (V * STerm) :=
(* todo: take remove Cast from applications of the inductive type being translated.
Or after translation, remove BestR.
Or remove Goodness all over in this part of the definition. In the outer definition,
map it back*)
let (v,t) := p in
let t := if isConstrArgRecursive tind t then removeCastsAroundInd tind t else t in 
translateArg (v,t).


Definition translateIndInnerMatchBranch tind (argsB: bool * list (V * STerm)) : STerm :=
  let (b,args) := argsB in
  let t := boolToProp b in
  let ret :=
   (if b  then (mkSigL (map (translateConstrArg tind) args) t) else t)
  in
  mkLamL (map primeArgs args) ret.


(* List.In  (snd lb)  cargs
Inline? *)
Definition translateIndInnerMatchBody tind o (lcargs: list (list (V * STerm)))
   v mTyInfo (lb: (list bool)*(list (V * STerm))) :=
  let lnt : list STerm := [tvmap vprime mTyInfo; vterm (vprime v)]
      ++(map (translateIndInnerMatchBranch tind) (combine ((fst lb)) lcargs)) in
    translateIndMatchBranch (oterm  o (map (bterm []) lnt), snd lb).


Definition translateIndMatchBody (numParams:nat) 
  tind v (mTyInfo:  STerm)
  (lcargs : list (list (V * STerm))): STerm :=
  let cargsLens : list nat := (map (@length (V * STerm)) lcargs) in
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
  let caseTyp := mkLamL (snoc indTypeIndices (v,t1)) srt in
  (* [l1...ln] . li is the list of arguments (and types of those arguments) 
      of the ith constructor. *)
  let lcargs : list (list (V * STerm)) := map (snd∘getHeadPIs∘snd) constrs in
  let mb := translateIndMatchBody numParams tind v caseTyp lcargs in
  let body : STerm := 
    fold_right (transLam translate) (mkLamL [(v,t1); (vprime v, t2)] mb) indTypArgs in
  let typ: STerm := headLamsToPi srt body in
  let rarg : nat := 
      ((fun x=>(x-2)%nat)∘(@length (V * STerm))∘snd∘getHeadPIs) typ in
  {|ftype := typ; fbody := body; structArg:= rarg |}.


Definition translateMutInd (id:ident) (t: simple_mutual_ind STerm SBTerm) (i:nat)
  : STerm := (mutIndToMutFix translateOneInd id t i).





Definition translateOnePropBranch (ind : inductive) (params: list (V * STerm))
  (ncargs : (nat*list (V * STerm))): STerm := 
  let (constrIndex, constrArgs) :=  ncargs in
  let constr := (oterm (CConstruct ind constrIndex) []) in
  let constr := mkApp constr (map (vterm∘vprime∘fst) params) in
  let procArg  (p:(V * STerm)) (t:STerm): STerm:=
    let (v,typ) := p in 
    let T1 := (removeHeadCast typ) in
    let T2 := tvmap vprime T1 in
    let (ret, lamArgs) := getHeadPIs T1 in
    let (ret, retArgs) := flattenApp ret [] in
    if (isRecursive ind ret)
    then
      let procLamArgOfArg (p:(V * STerm)) (t:STerm): STerm:=
        let (vIn,typIn) := p in 
        let T1In := (removeHeadCast typIn) in
        let T2In := tvmap vprime T1In in
        let t21 := tot21 typIn (vterm (vprime vIn)) in
        mkLetIn vIn (fst t21) T1In
          (mkLetIn (vrel vIn) (snd t21)  (* typ to t1 *)
              (mkApp (translate typIn) [vterm vIn; vterm (vprime vIn)]) t) in
      let recCall : STerm := translate (mkApp ret retArgs) in
      let f1 : STerm := vterm v in
      let recArg : STerm := mkApp f1 (map (vterm∘fst) lamArgs) in
      let recRet := (mkApp recCall [recArg]) in
      let retIn := List.fold_right procLamArgOfArg recRet lamArgs in
      let retIn := mkLamL (map primeArgs lamArgs) retIn in
      mkLetIn (vprime v) retIn T2 t
    else
      mkLetIn (vprime v) (fst (tot12 typ (vterm v))) T2
        (mkLetIn (vrel v) (snd (tot12 typ (vterm v))) 
            (mkApp (translate typ) [vterm v; vterm (vprime v)]) t) in
  let ret := mkApp constr (map (vterm∘vprime∘fst) constrArgs) in
  let ret := List.fold_right procArg ret constrArgs in
  mkLamL constrArgs ret.


(** tind is a constant denoting the inductive being processed *)
Definition translateOnePropTotal (numParams:nat) 
  (tind : inductive*(simple_one_ind STerm STerm)) : fixDef STerm :=
  let (tind,smi) := tind in
  let (nmT, constrs) := smi in
  let (_, indTyp) := nmT in
  let (_, indTypArgs) := getHeadPIs indTyp in
  let indTypeIndices : list (V * STerm) := skipn numParams indTypArgs in
  let indTypeParams : list (V * STerm) := firstn numParams indTypArgs in
  let vars : list V := map fst indTypArgs in
  let t1 : STerm := (mkIndApp tind (map vterm vars)) in
  let t2 : STerm := (mkIndApp tind (map (vterm∘vprime) vars)) in (* return type *)
  let caseRetPrimeArgs := map primeArgs indTypeIndices in
  let caseRetRelArgs := map translateArg indTypeIndices in
  let caseRetTyp := mkPiL (caseRetPrimeArgs++caseRetRelArgs) t2 in
  let v : V := fresh_var vars in
  let caseTyp := mkLamL (snoc indTypeIndices (v,t1)) caseRetTyp in
  (* [l1...ln] . li is the list of arguments (and types of those arguments) 
      of the ith constructor. *)
  let lcargs : list (list (V * STerm)) := map (snd∘getHeadPIs∘snd) constrs in
  let cargsLens : list nat := (map (@length (V * STerm)) lcargs) in
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
      ((fun x=>(x-1)%nat)∘(@length (V * STerm))∘snd∘getHeadPIs) typ in
  {|ftype := typ; fbody := body; structArg:= rarg |}.


End trans.


Import MonadNotation.
Open Scope monad_scope.


Require Import List. 



Definition genParam (piff: bool) (b:bool) (id: ident) : TemplateMonad unit :=
  id_s <- tmQuoteSq id true;;
(*  _ <- tmPrint id_s;; *)
  match id_s with
  Some (inl t) => 
    let t_R := (translate piff t) in
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


Definition genParamInd (piff: bool) (b:bool) (id: ident) : TemplateMonad unit :=
  id_s <- tmQuoteSq id true;;
(*  _ <- tmPrint id_s;; *)
  match id_s with
  Some (inl t) => ret tt
  | Some (inr t) =>
    let fb := translateMutInd piff id t 0 in
      if b then (tmMkDefinitionSq (indTransName (mkInd id 0)) fb) else
        (trr <- tmReduce Ast.all fb;; tmPrint trr)
  | _ => ret tt
  end.

Definition genParamIndTot (piff: bool) (b:bool) (id: ident) : TemplateMonad unit :=
  id_s <- tmQuoteSq id true;;
(*  _ <- tmPrint id_s;; *)
  match id_s with
  Some (inl t) => ret tt
  | Some (inr t) =>
    let fb := (mutIndToMutFix (translateOnePropTotal piff)) id t 0%nat in
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

(* in the translation, inline this *)
Notation PiABTypeN
  A1 A2 A_R
  B1 B2
  B_R
  := (fun (f1 : forall a : A1, B1 a) (f2 : forall a : A2, B2 a) =>
forall (a1 : A1) (a2 : A2) (p : A_R a1 a2), B_R a1 a2 p (f1 a1) (f2 a2)) (only parsing).

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
Run TemplateProgram (printTerm "ReflParam.PIWNew.IWT").
Run TemplateProgram (genParamInd mode true "ReflParam.PIWNew.IWT"). 
Eval compute in ReflParam_PIWNew_IWT_RR0.


Run TemplateProgram (genParamInd mode true "Coq.Init.Datatypes.nat").

Require Import matchR. (* shadows Coq.Init.Datatypes.list *)
Require Import List.
(* nat must  have a BestRel 
Run TemplateProgram (genParamInd true true "ReflParam.matchR.Vec").
*)

Run TemplateProgram (genParamInd false true "ReflParam.matchR.Vec").
Run TemplateProgram (genParamInd false true "ReflParam.paramDirect.NatLike").



Eval compute in  ReflParam.paramDirect.NatLike.


(*
Require Import matchR. (* shadows Coq.Init.Datatypes.list *)
Require Import Datatypes.List.
Run TemplateProgram (genParamInd false false "ReflParam.matchR.Vec").
*)


(* while compiling *)


(*
(fix
 ReflParam_paramDirect_NatLike_RR0 (A A₂ : Set)
                                   (A_R : (fun H H0 : Set => BestRel H H0) A
                                            A₂) (B B₂ : Set)
                                   (B_R : (fun H H0 : Set => BestRel H H0) B
                                            B₂) (H : NatLike A B) {struct H} :
   NatLike A₂ B₂ :=
   match H with
   | SS _ _ a =>
       SS A₂ B₂
         (BestTot12
            (PiTSummary A A₂ A_R (fun _ : A => B) 
               (fun _ : A₂ => B₂)
               (fun (H0 : A) (H1 : A₂) (_ : BestR A_R H0 H1) => B_R)) a)
   end)
*)


(* Run TemplateProgram (genParamInd mode true "ReflParam.paramDirect.NatLike"). *)




(*
Run TemplateProgram (genParamInd mode true "Top.NatLike").
Run TemplateProgram (printTermSq "NatLike").
Run TemplateProgram (printTermSq "nat").
Eval compute in Top_NatLike_RR0.
*)




(*
Run TemplateProgram (genParamInd mode true "ReflParam.matchR.IWT").
*)

Run TemplateProgram (genParam mode true "appTest").
Eval compute in appTest_RR.
(* how does the type of f_R have BestR? Template-coq quotes the type in a lambda,
even if the type is a mkPi, whose sort can be easily computed from its subterms
that are guaranteed to be tagged. *)
Definition ids_RN : forall (A₁ A₂ : Set) (A_R : BestRel A₁ A₂ ) (x₁ : A₁) (x₂ : A₂),
       R A_R x₁ x₂ -> R A_R x₁ x₂
:= 
fun (A₁ A₂ : Set) (A_R :BestRel A₁ A₂) (x₁ : A₁) (x₂ : A₂) 
  (x_R : BestR A_R x₁ x₂) => x_R.

Run TemplateProgram (printTerm "ids").

Run TemplateProgram (printTerm "ids_RN").



Run TemplateProgram (genParam mode true "idsT").
Eval compute in idsT_RR.

Print idsT.

Parametricity idsT.

(* Given f: some Pi Type, prove that the new theorem implies the old *)
Eval vm_compute in idsT_RR.


Run TemplateProgram (genParam mode true "ids").
Eval compute in ids_RR.

Definition idsTT  := fun A : Set => forall a:A, A.

Parametricity Recursive idsTT.

Run TemplateProgram (genParam mode true "idsTT").
Eval compute in idsTT_RR.

Print idsTT_RR.

Definition s := Set.
Run TemplateProgram (genParam mode  true "s").

Eval compute in s_RR.

Definition propIff : Type := forall A:Set, Prop.

Run TemplateProgram (genParam mode true "propIff").

Eval compute in propIff_RR.

Definition propIff2 : Prop := forall A:Prop, A.

Run TemplateProgram (genParam mode  true "propIff2").

Run TemplateProgram (printTerm "propIff2").

Eval compute in propIff2_RR.

Goal propIff2_RR = fun _ _ => True.
unfold propIff2_RR.
Print PiTSummary.
unfold PiATypeBSet. simpl.
Print PiATypeBSet.
Abort.

Definition p := Prop.
Run TemplateProgram (genParam mode  true "p").

Eval compute in p_RR.
