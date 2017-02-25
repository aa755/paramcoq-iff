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
 existss : forall (x : A) (p:P x), sigs A P.

Require Import ReflParam.anyRelIndProp.
Run TemplateProgram (genParamIndProp [] true "Top.exists.sigs").

Print Top_exists_sigs_pmtcty_RR0.


(*
Inductive
Top_exists_sigs_pmtcty_RR0 (A A₂ : Set) (A_R : A -> A₂ -> Prop) (P : A -> Prop) 
(P₂ : A₂ -> Prop)
(P_R : forall (H : A) (H0 : A₂), A_R H H0 -> (fun H1 H2 : Prop => H1 -> H2 -> Prop) (P H) (P₂ H0))
  : sigs A P -> sigs A₂ P₂ -> Prop :=
    Top_exists_sigs_pmtcty_RR0_constr_0 : forall (x : A) (x₂ : A₂) (x_R : A_R x x₂) 
                                            (p : P x) (p₂ : P₂ x₂),
                                          P_R x x₂ x_R p p₂ ->
                                          Top_exists_sigs_pmtcty_RR0 A A₂ A_R P P₂ P_R
                                            (existss A P x p) (existss A₂ P₂ x₂ p₂)
*)
