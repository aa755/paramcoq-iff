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

Print sig.

Inductive sigs (A : Set) (P : A -> Prop) : Prop :=
 existss : forall x : A, P x -> sigs A P.

Run TemplateProgram (genParamIndAll [] "Top.exists.sigs").
