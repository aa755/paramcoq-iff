Require Import ReflParam.common.
Require Import ReflParam.templateCoqMisc.
Require Import String.
Require Import List.
Require Import Template.Ast.
Require Import SquiggleEq.terms.
Require Import ReflParam.paramDirect ReflParam.indType.
Require Import ReflParam.indProp.
Require Import SquiggleEq.substitution.
Require Import ReflParam.PiTypeR.
Import ListNotations.
Open Scope string_scope.

Require Import ReflParam.Trecord.



Definition piProp:= True -> True.

Run TemplateProgram (genParamIndPropAll [] "Coq.Init.Logic.True").
Run TemplateProgram (genParam [] true true "Top.propSetSubtypeProblem.piProp").
Run TemplateProgram (genParamIndAll [] "Coq.Init.Datatypes.nat").

Definition subProblem1 := (fun (X:Set) => nat -> X) True.
Definition subProblem2 := (fun (X:Set) => nat -> X) nat.
Definition subProblem3 := (fun (X:Prop) => nat -> X) True.
Definition subProblem4 := (fun (X:Set) => X -> nat) True.

Definition subProblem1C := Eval compute in subProblem1.
Definition subProblem2C := Eval compute in subProblem2.
Definition subProblem3C := Eval compute in subProblem3.
Definition subProblem4C := Eval compute in subProblem4.

Run TemplateProgram (genParam [] true true "Top.propSetSubtypeProblem.subProblem1").
Run TemplateProgram (genParam [] true true "Top.propSetSubtypeProblem.subProblem1C").
Run TemplateProgram (genParam [] true true "Top.propSetSubtypeProblem.subProblem2").
Run TemplateProgram (genParam [] true true "Top.propSetSubtypeProblem.subProblem2C").
Run TemplateProgram (genParam [] true true "Top.propSetSubtypeProblem.subProblem3").
Run TemplateProgram (genParam [] true true "Top.propSetSubtypeProblem.subProblem3C").
Run TemplateProgram (genParam [] true true "Top.propSetSubtypeProblem.subProblem4").
Run TemplateProgram (genParam [] true true "Top.propSetSubtypeProblem.subProblem4C").

Fail Check (eq_refl : Top_propSetSubtypeProblem_subProblem1_pmtcty_RR = Top_propSetSubtypeProblem_subProblem1C_pmtcty_RR).
Check (eq_refl : Top_propSetSubtypeProblem_subProblem2_pmtcty_RR = Top_propSetSubtypeProblem_subProblem2C_pmtcty_RR).
Check (eq_refl : Top_propSetSubtypeProblem_subProblem3_pmtcty_RR = Top_propSetSubtypeProblem_subProblem3C_pmtcty_RR).
Check (eq_refl : Top_propSetSubtypeProblem_subProblem4_pmtcty_RR = Top_propSetSubtypeProblem_subProblem4C_pmtcty_RR).
