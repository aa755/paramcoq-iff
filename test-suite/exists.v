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

Print sig.

Inductive sigs (A : Set) (P : A -> Prop) : Prop :=
 existss : forall x : A, P x -> sigs A P.

Run TemplateProgram (genParamIndProp [] true "Top.exists.sigs").
Print Top_exists_sigs_pmtcty_RR0_prop.
(*
Need to reduce more before extracting params
Inductive
Top_exists_sigs_pmtcty_RR0_prop (A A₂ : Set) (A_R : A -> A₂ -> Prop)
  : (fun (ff : (A -> Prop) -> Prop) (ff₂ : (A₂ -> Prop) -> Prop) =>
     forall (P : A -> Prop) (P₂ : A₂ -> Prop),
     (forall (H : A) (H0 : A₂),
      A_R H H0 -> (fun H1 H2 : Prop => H1 -> H2 -> Prop) (P H) (P₂ H0)) ->
     (fun H H0 : Prop => H -> H0 -> Prop) (ff P) (ff₂ P₂)) (sigs A) 
      (sigs A₂) := 
*)