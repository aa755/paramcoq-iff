

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
Require Import ReflParam.paramDirect.




(* This file implements inductive-style translation of inductive props *)

(* The [translate] translate [mkInd i] to a constant, as needed 
  in the deductive style, where the constant is a fixpoint (of the form [mkConst c]), 
and not an in the form [mkInd c].
In the inductive style, which is used for Props,
 the translation of an inductive is an inductive (of the form mkInd ir).
 We instead use mkInd (propAuxname ir).
 Then we make a constant wrapper defining ir:=mkInd (propAuxname ir).
Thus, [translate] does not worry about whether an inductive [i] was Prop 
(whether it was translated in deductive style) 
*)


Definition propAuxName (n: ident) : ident := n.
  (*String.append n "_prop". *)


(* similar to [[T]] t t, but produces a normalized result if T is a Pi type *)
Definition transTermWithPiType (ienv: indEnv) (t T: STerm) :=
      let (retTyp, args) := getHeadPIs T in
      let tlR := translate AnyRel ienv (headPisToLams T) in
      let (retTyp_R,args_R) := getNHeadLams (3* (length args)) tlR in
      let tapp := mkApp t (map (vterm ∘ fst) args) in
      mkPiL (mrs args_R) (mkAppBeta (retTyp_R) [tapp; tprime tapp]).

Definition  translateIndConstr (ienv: indEnv) (tind: inductive)
            (indRefs: list inductive)
            (numInds (*# inds in this mutual block *) : nat)
            (c: (nat*(ident * SBTerm))) : (*c_R*)  (ident * SBTerm)  :=
  let '(cindex, (cname, cbtype)) := c in
  let (bvars, ctype) := cbtype in
  let mutBVars := firstn numInds bvars in
  let paramBVars := skipn numInds bvars in
  (* for each I in the mutual block, we are defining I_R in the new mutual block *)
  let mutBVarsR := map vrel mutBVars  in 
  (* I_R has 3 times the old params *)
  let paramBVarsR := flat_map vAllRelated paramBVars in
  let ctypeR :=
      let thisConstr := mkApp (mkConstr tind cindex) (map vterm paramBVars) in
      let ctypeRAux := transTermWithPiType ienv thisConstr ctype in
      let sub :=
          let terms := map (fun i => mkConstInd i) indRefs in
          combine mutBVars terms in
      let subPrime :=
          let terms := map (fun i => mkConstInd i) indRefs in
          combine (map vprime mutBVars) terms in
      ssubst_aux ctypeRAux (sub++subPrime) in
  (constrTransName tind cindex, bterm (mutBVarsR++paramBVarsR) (reduce 1000 ctypeR)).


Definition  translateIndProp (ienv: indEnv) (indRefs: list inductive)
            (numInds (*# inds in this mutual block *) : nat)
            (ioind:  inductive * (simple_one_ind STerm SBTerm)) : simple_one_ind STerm SBTerm :=
  let (ind, oind) := ioind in
  let '(indName, typ, constrs) := oind in
  let indRName := (propAuxName (indTransName ind)) in
  let typR :=
      (* the simple approach of [[typ]] I I needs beta normalizing the application so
         that the reflection mechanism can extract the parameters.  *)
      (* mkAppBeta (translate AnyRel ienv typ) [mkConstInd ind; mkConstInd ind] in *)
      (* So, we directly produce the result of sufficiently beta normalizing the above. *)
      transTermWithPiType ienv (mkConstInd ind) typ in
  let constrsR := map (translateIndConstr ienv ind indRefs numInds) (numberElems constrs) in
  (indRName, typR, constrsR).


Definition  translateMutIndProp  (ienv: indEnv)
            (id:ident) (mind: simple_mutual_ind STerm SBTerm)
  : simple_mutual_ind STerm SBTerm :=
  let (paramNames, oneInds) := mind in
  let indRefs : list inductive := map fst (indTypes id mind) in
  let packets := combine indRefs oneInds in
  let numInds := length oneInds in
  let onesR := map (translateIndProp ienv indRefs numInds) packets in
  let paramsR := flat_map (fun n => [n;n;n]) paramNames in
                 (* contents are gargabe: only the length matters while reflecting*) 
  (paramsR, onesR).

Import MonadNotation.
Open Scope monad_scope.

(* Move *)
Definition tmReducePrint {T:Set} (t: T) : TemplateMonad () :=
  (trr <- tmReduce Ast.all t;; tmPrint trr).

Definition genParamIndProp (ienv : indEnv)  (cr:bool) (id: ident) : TemplateMonad unit :=
  id_s <- tmQuoteSq id true;;
(*  _ <- tmPrint id_s;; *)
  match id_s with
  Some (inl t) => ret tt
  | Some (inr t) =>
    let mindR := translateMutIndProp ienv id t in
    if cr then (tmMkIndSq mindR)  else  (tmReducePrint mindR)
      (* repeat for other inds in the mutual block *)
  | _ => ret tt
  end.


