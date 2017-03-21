Require Import ReflParam.common.
Require Import ReflParam.templateCoqMisc.
Require Import String.
Require Import List.
Require Import Template.Ast.
Require Import SquiggleEq.terms.
Require Import ReflParam.paramDirect ReflParam.indType ReflParam.indProp.
Require Import SquiggleEq.substitution.
Require Import ReflParam.PiTypeR.
Import ListNotations.
Open Scope string_scope.

Inductive eqs (A : Set) (x : A) : forall a:A, Prop :=  eq_refls : eqs A x x.

Run TemplateProgram (genParamIndPropAll [] "Top.eqs.eqs").



Run TemplateProgram (mkIndEnv "indTransEnv" ["Top.eqs.eqs"]).

(* Run TemplateProgram (genWrappers indTransEnv). *)


Definition eqs_recs := 
fun (A : Set) (x : A) (P : A -> Set) (f : P x) (a : A) (e : eqs A x a) =>
match e in (eqs _ _ a0) return (P a0) with
| eq_refls _ _ => f
end.

Run TemplateProgram (genParam indTransEnv true true "Top.eqs.eqs_recs").
Module AnyRel.
Run TemplateProgram (genParam indTransEnv false true "Top.eqs.eqs_recs").
End AnyRel.

