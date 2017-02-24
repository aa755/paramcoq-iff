

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

Definition propAuxName (n: ident) : ident :=
  String.append n "_prop".

Definition  translateIndProp (ienv: indEnv)
            (ioind:  inductive * (simple_one_ind STerm SBTerm)) : simple_one_ind STerm SBTerm :=
  let (ind, oind) := ioind in
  let '(indName, typ, constrs) := oind in
  let indRName := (propAuxName (indTransName ind)) in
  let typR :=
      (* the simple approach of [[typ]] I I needs beta normalizing the application so
         that the reflection mechanism can extract the parameters.  *)
      (* mkAppBeta (translate AnyRel ienv typ) [mkConstInd ind; mkConstInd ind] in *)
      (* So, we directly produce the result of sufficiently beta normalizing the above. *)
      let (retTyp, args) := getHeadPIs typ in
      let tlR := translate AnyRel ienv (headPisToLams typ) in
      let (retTyp_R,args_R) := getNHeadLams (3* (length args)) tlR in
      let tapp := mkIndApp ind (map (vterm ∘ fst) args) in
      mkPiL (mrs args_R) (mkAppBeta (retTyp_R) [tapp; tprime tapp]) in
  (indRName, typR,[] (* fix *)).


Definition  translateMutIndProp  (ienv: indEnv)
            (id:ident) (mind: simple_mutual_ind STerm SBTerm)
  : simple_mutual_ind STerm SBTerm :=
  let (paramNames, oneInds) := mind in
  let indRefs : list inductive := map fst (indTypes id mind) in
  let packets := combine indRefs oneInds in
  let onesR := map (translateIndProp ienv) packets in
  let paramsR := flat_map (fun n => [n;n;n]) paramNames in
                 (* contents are gargabe: only the length matters while reflecting*) 
  (paramsR, onesR).

Import MonadNotation.
Open Scope monad_scope.

Definition genParamIndProp (ienv : indEnv)  (cr:bool) (id: ident) : TemplateMonad unit :=
  id_s <- tmQuoteSq id true;;
(*  _ <- tmPrint id_s;; *)
  match id_s with
  Some (inl t) => ret tt
  | Some (inr t) =>
    let mindR := translateMutIndProp ienv id t in
    tmMkIndSq mindR
      (* repeat for other inds in the mutual block *)
  | _ => ret tt
  end.


