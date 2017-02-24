Require Import ReflParam.common.
Require Import ReflParam.templateCoqMisc.
Require Import String.
Require Import List.
Require Import Template.Ast.
Require Import SquiggleEq.terms.
Require Import ReflParam.paramDirect.
Require Import SquiggleEq.substitution.
Require Import ReflParam.PiTypeR.
Require Import ReflParam.anyRelIndProp.
Import ListNotations.
Open Scope string_scope.

Print sig.

Inductive sigs (A : Set) (P : A -> Prop) : Prop :=
 existss : forall x : A, P x -> sigs A P.

Require Import ReflParam.anyRelIndProp.
Run TemplateProgram (genParamIndProp [] true "Top.exists.sigs").
Print Top_exists_sigs_pmtcty_RR0_prop.

Run TemplateProgram (printTermSq "Top.exists.sigs").

(*
Inductive
Top_exists_sigs_pmtcty_RR0_prop (A A₂ : Set) (A_R : A -> A₂ -> Prop) 
(P : A -> Prop) (P₂ : A₂ -> Prop)
(P_R : forall (H : A) (H0 : A₂),
       A_R H H0 -> (fun H1 H2 : Prop => H1 -> H2 -> Prop) (P H) (P₂ H0))
  : sigs A P -> sigs A₂ P₂ -> Prop 
*)