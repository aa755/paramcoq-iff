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
Require Import ReflParam.paramDirect.


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

(* before goodness has been fully generated, we need too remove the flags that inddicate
that A:Set and thus A's relation must be good, for A:= the mutual ind being processed now.
The index in tind is ignored *)

Definition mkConstrInfoBeforeGoodness (tind:inductive)
           (numParams : nat )(translate: STerm-> STerm) (constrTypes : list STerm) :=
      let constrTypes_R := map (translate ∘ headPisToLams ∘ (removeCastsInConstrType tind))
                               constrTypes in
      map (mkConstrInfo numParams) (numberElems constrTypes_R).

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
             sigtFull in (* sigtFull is only used here *)
  let peq := mkConstApp (indIndicesIrrelTransName tind) tindIArgs in
  let body := oterm o (map (bterm [])[caseRet; peq; body]) in
({| nameSq := cname; bodySq := mkLamL (allArgs) body |}).


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
  let indTypeParams_RP := TranslatedArg.unMerge3way indTypeParams_R in
  let cargs_R : list Arg := TranslatedArg.merge3way (IndTrans.args_R cinfo) in
  let cargs := IndTrans.args cinfo in
  let indTypIndicVarsP := (map vprime indTypIndicVars) in
  let cretIndices843 := (IndTrans.indices cinfo) in
  let cretIndicesPrime843 := (IndTrans.indicesPrimes cinfo) in
  let caseTypRet := 
    ssubst_aux caseTypRet (combine indTypIndicVarsP cretIndicesPrime843) in
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
        let sigtFull :=
            let cretIndices_Rpartial :=
                (* change the indIndices and indIndicesPrimes to cretIndices and cretIndicesPrimes
                   but don't change indIndiceRs *)
                merge3Lists cretIndices843 cretIndicesPrime843 (map (vterm∘vrel) indTypIndicVars) in
            let thisConstrApplied :=
                mkApp
                  (mkConstr tind (IndTrans.index cinfo))
                  (fstVterms ((map (TranslatedArg.arg) indTypeParams_RP) ++ cargs)) in
            mkConstApp
              (indTransName tind)
              ((fstVterms indTypeParams_R)
                 ++ cretIndices_Rpartial
                 ++ [thisConstrApplied; tprime thisConstrApplied]) in
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



Section IndTypeAnyRel.
  Variable ienv: indEnv.
  Let translate := translate AnyRel ienv.
  
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

End IndTypeAnyRel.




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

Section IndTypeIsoRel.
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
  Let translate := translate IsoRel ienv.

  
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


      
(** OneToOne hood *)

(** We need 2 vars of the J and RR classes. These are obtained
by adding a large enough number, and appending "o".
This operation is done after doing vprime/vrel if neccessary  *)
Definition extraVar (add :N) (v:V):=
  (add+fst v, nAppend "o" (snd v)).


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
  
  
  
  

End IndTypeIsoRel.
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

(* useful when we want to make them opaque *)
Definition oldOneIndNames
           (oldNameFs : list (inductive -> nat -> ident))
           (p : (inductive * simple_one_ind STerm STerm))
  : list ident :=
  let (tind, smi) := p in
  let (nmT, constrs) := smi in
  let seq := List.seq 0 (length constrs) in
  let defn constrIndex oldNameF := (oldNameF tind constrIndex) in
  let defn constrIndex :=
      map (defn constrIndex) oldNameFs in
  (indTransName tind)::(flat_map defn seq).

Definition crrCrrInvWrappers (ienv : indEnv) (numParams:nat) 
           (p : (inductive * simple_one_ind STerm STerm))
  : list defIndSq :=
 genIndisoWrappers ienv numParams p [constrTransName; constrInvFullName].
  
Definition  allCrrCrrInvsWrappers  (env : indEnv)
  : list defIndSq  :=
  flat_map
    (fun (p: ident * (simple_mutual_ind STerm SBTerm)) =>
       let (id, mind) := p in
         let numParams := mindNumParams mind in
           let ones := substMutInd id mind in
           flat_map (crrCrrInvWrappers env numParams) ones
           ) env.

Definition  oldIndNamesL  (env : indEnv)
  : list ident :=
  flat_map
    (fun (p: ident * (simple_mutual_ind STerm SBTerm)) =>
       let (id, mind) := p in
           let ones := substMutInd id mind in
           flat_map (oldOneIndNames  [constrTransName; constrInvFullName; constrTransTotName])
                    ones
           ) env.

Definition  oldIndNames  (env : indEnv)
  : ident := 
  flattenDelim newLineString (oldIndNamesL env).

Definition mkBestRel_ref := "ReflParam.Trecord.mkBestRel".
Definition mkBestRelProp_ref := "ReflParam.Trecord.mkBestRelProp".

Definition  mkOneIndGoodPacket  (ienv: indEnv) (numParams:nat)
            (p: inductive * STerm) : defSq :=
  let (tind, typ) := p in
  let (sort, indTypArgs) := getHeadPIs typ in
  let castedParams_R : list STerm :=
      let (_, indTypParams) := getNHeadPis numParams typ in
      map snd (flat_map (transArgWithCast ienv) indTypParams) in
  let indTyp_R := translate true ienv (headPisToLams typ) in
  let (_, indTypArgs_R) := getNHeadLams (3*length indTypArgs) indTyp_R  in
  let appArgs : list STerm := map (vterm ∘ fst) indTypArgs_R in
  let indApp := mkIndApp tind (map (vterm ∘ fst) indTypArgs) in
  let indApp2 := tprime indApp in
  let iRRname := (indTransName tind) in
  let IRR :=
      let indIndices_RR := skipn (3*numParams) appArgs in
      mkConstApp iRRname (castedParams_R++indIndices_RR) in
  let tot12 := mkConstApp (indTransTotName false false tind) appArgs in
  let tot21 := mkConstApp (indTransTotName false true tind) appArgs in
  (* TODO: if the inductive is a Prop, skip these 2 and use a different combinator *)
  let body := 
  match sort with
    | mkSort sSet =>
    
      let one12 := mkConstApp (indTransOneName false tind) appArgs in
      let one21 := mkConstApp (indTransOneName true tind) appArgs in
      mkConstApp mkBestRel_ref [indApp, indApp2,
                                        IRR, tot12, tot21,
                                        one12, one21]
    | mkSort sProp =>
      mkConstApp mkBestRelProp_ref [indApp, indApp2,
                                    IRR, tot12, tot21]
    | _ => mkUnknown "mkOneIndGoodPacket:expected a sort"
  end in
  {|
    nameSq := isoModeId iRRname;
     bodySq:= mkLamL (mrs indTypArgs_R) body
  |}.
  
Definition  mkIndGoodPacket  (ienv: indEnv)
            (id:ident) (mind: simple_mutual_ind STerm SBTerm)
  : list defIndSq :=
  let indTyps : list (inductive * STerm) := indTypes id mind in
  let nump:= (mindNumParams mind) in
  map (inl ∘ (mkOneIndGoodPacket ienv nump)) indTyps.




(* end : translating  inductive props *)

Definition genWrappers  (ienv : indEnv) : TemplateMonad () :=
  tmMkDefIndLSq (allCrrCrrInvsWrappers ienv).

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
