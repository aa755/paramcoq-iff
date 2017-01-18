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

Print eq.

Inductive eqs (A : Set) (x : A) : forall a:A, Set :=  eq_refls : eqs A x x.


Definition eqsRMatch
(A A₂ : Set) (A_R : A -> A₂ -> Set) (x : A) (x₂ : A₂) 
                 (x_R : A_R x x₂) (a1 : A) (a2 : A₂) (ar : A_R a1 a2) 
                 (eqs1 : eqs A x a1) (eqs2 : eqs A₂ x₂ a2) : Set :=

   let reT a1 a2 := forall (ar : A_R a1 a2), Set in
   (match eqs1 in eqs _ _ a1 return reT a1 a2 with
   | eq_refls _ _ => match eqs2 with
                     | eq_refls _ _ => fun ar => x_R = ar
                     end
   end) ar.


Definition eqs_recs := 
fun (A : Set) (x : A) (P : forall a:A, Set) (f : P x) (y : A) (e : eqs A x y) =>
match e as esss in (eqs _ _ yy)  return (P yy) with
| eq_refls _ _ => f
end.

Arguments sigT : clear implicits.

Check eqs.

Definition eqrecs_RR :
forall (A₁ A₂ : Set) (A_R : A₁ -> A₂ -> Prop) (x₁ : A₁) (x₂ : A₂) 
         (x_R : A_R x₁ x₂) (P₁ : A₁ -> Set) (P₂ : A₂ -> Set)
         (P_R : forall (a₁ : A₁) (a₂ : A₂), A_R a₁ a₂ -> P₁ a₁ -> P₂ a₂ -> Set) 
         (f₁ : P₁ x₁) (f₂ : P₂ x₂),
       P_R x₁ x₂ x_R f₁ f₂ ->
       forall (y₁ : A₁) (y₂ : A₂) (y_R : A_R y₁ y₂) (e₁ : eqs A₁ x₁ y₁) (e₂ : eqs A₂ x₂ y₂),
       eqsRMatch A₁ A₂ A_R x₁ x₂ x_R y₁ y₂ y_R e₁ e₂ ->
       P_R y₁ y₂ y_R (eqs_recs A₁ x₁ P₁ f₁ y₁ e₁) (eqs_recs A₂ x₂ P₂ f₂ y₂ e₂).
Proof.
intros.
unfold eqs_recs.
rename H0 into eqsr.
revert eqsr.
revert e₂.
destruct e₁.
simpl.
intro.
destruct e₂.
intros Heq. subst. assumption.
Qed.

(*
Declare ML Module "paramcoq".
Parametricity Recursive eqs_recs.
Print eqs_R.
*)

Inductive eqs_RInd (A₁ A₂ : Set) (A_R : A₁ -> A₂ -> Set) (x₁ : A₁) (x₂ : A₂) 
(x_R : A_R x₁ x₂)
  : forall (a₁ : A₁) (a₂ : A₂), A_R a₁ a₂ -> eqs A₁ x₁ a₁ -> eqs A₂ x₂ a₂ -> Set :=
eq_refls_Rind : eqs_RInd A₁ A₂ A_R x₁ x₂ x_R x₁ x₂ x_R (eq_refls A₁ x₁) (eq_refls A₂ x₂).

Locate UIP_on.
Require Import Coq.Logic.EqdepFacts.

Section usp.
Require Import ReflParam.common.
Require Import ReflParam.Contractible.
Context (A₁ A₂ : Set) (A_R : A₁ -> A₂ -> Set) (x₁ : A₁) (x₂ : A₂) (x_R : A_R x₁ x₂)
  (peq : UIP_ (A_R x₁ x₂)).
  
Lemma cc_rr: forall  
  y₁ y₂ y_R (e₁ : eqs A₁ x₁ y₁) (e₂ : eqs A₂ x₂ y₂),
       Contractible (eqsRMatch A₁ A₂ A_R x₁ x₂ x_R y₁ y₂ y_R e₁ e₂).
Proof using peq.
  intros ? ? ? ?.
  induction e₁.
  destruct e₂.
  simpl.
  intros ? ?. apply peq.
Qed.

Require Import Coq.Logic.JMeq.
Require Import Coq.Program.Equality.

Lemma cc_r: forall  
  y₁ y₂ y_R (e₁ : eqs A₁ x₁ y₁) (e₂ : eqs A₂ x₂ y₂),
       Contractible (eqs_RInd A₁ A₂ A_R x₁ x₂ x_R y₁ y₂ y_R e₁ e₂).
Proof using peq.
  intros ? ? ? ? ? ?.
  induction a.
  intros b.
  dependent destruction b.
  reflexivity.
Qed.

End usp.

Section tofrom.
Context (A₁ A₂ : Set) (A_R : A₁ -> A₂ -> Set) (x₁ : A₁) (x₂ : A₂) (x_R : A_R x₁ x₂)
  (y₁: A₁) (y₂: A₂) (y_R : A_R y₁ y₂)
  (e₁ : eqs A₁ x₁ y₁) (e₂ : eqs A₂ x₂ y₂).


