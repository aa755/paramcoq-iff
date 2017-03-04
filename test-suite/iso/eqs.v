Require Import ReflParam.common.
Require Import ReflParam.templateCoqMisc.
Require Import String.
Require Import List.
Require Import Template.Ast.
Require Import SquiggleEq.terms.
Require Import ReflParam.paramDirect ReflParam.indType.
Require Import SquiggleEq.substitution.
Require Import ReflParam.PiTypeR.
Import ListNotations.
Open Scope string_scope.

Inductive eqs (A : Set) (x : A) : forall a:A, Prop :=  eq_refls : eqs A x x.

Run TemplateProgram (genParamIndAll [] "Top.eqs.eqs").



Run TemplateProgram (mkIndEnv "indTransEnv" ["Top.eqs.eqs"]).

Run TemplateProgram (genWrappers indTransEnv).
