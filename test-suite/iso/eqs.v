Require Import ReflParam.common.
Require Import ReflParam.templateCoqMisc.
Require Import String.
Require Import List.
Require Import Template.Ast.
Require Import SquiggleEq.terms.
Require Import ReflParam.paramDirect.
Require Import SquiggleEq.substitution.
Require Import ReflParam.PiTypeR.
Import ListNotations.
Open Scope string_scope.

Inductive eqs (A : Set) (x : A) : forall a:A, Prop :=  eq_refls : eqs A x x.

Run TemplateProgram (genParamInd [] true true "Top.eqs.eqs").



Run TemplateProgram (mkIndEnv "indTransEnv" ["Top.eqs.eqs"]).

Print indTransEnv.

Definition  allCrrCrrInvsWrappers  (env : indEnv)
  : list nat :=
  map
    (fun (p: ident * (simple_mutual_ind STerm SBTerm)) =>
       let (id, mind) := p in
         let numParams := mindNumParams mind in numParams
           ) env.

Eval compute in (allCrrCrrInvsWrappers indTransEnv).
(* 
= [2%nat]
     : list nat
     *)
Run TemplateProgram (genWrappers indTransEnv).
