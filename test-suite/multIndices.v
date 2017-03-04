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


Inductive multInd (A : Set) (B: A-> Set)
 (a : A) (b : B a) : forall a:A, B a -> Set  :=  
eq_refls : multInd A B a b a b.

Require Import SquiggleEq.UsefulTypes.

Run TemplateProgram (genParamInd [] false true true "Top.multIndices.multInd").
(*
(fix
 Top_multIndices_multInd_RR0 (A A₂ : Set) (A_R : A -> A₂ -> Prop) 
                             (B : A -> Set) (B₂ : A₂ -> Set)
                             (B_R : forall (H : A) (H0 : A₂),
                                    A_R H H0 -> B H -> B₂ H0 -> Prop) 
                             (a : A) (a₂ : A₂) (a_R : A_R a a₂) 
                             (b : B a) (b₂ : B₂ a₂) (b_R : B_R a a₂ a_R b b₂) 
                             (a0 : A) (a₂0 : A₂) (a_R0 : A_R a0 a₂0) 
                             (H : B a0) (H0 : B₂ a₂0) (H1 : B_R a0 a₂0 a_R0 H H0)
                             (H2 : multInd A B a b a0 H) (H3 : multInd A₂ B₂ a₂ b₂ a₂0 H0)
                             {struct H2} : Prop :=
   match H2 with
   | eq_refls _ _ _ _ => match H3 with
                         | eq_refls _ _ _ _ => True
                         end
   end)
Top_multIndices_multInd_RR0 is defined
(fun (A A₂ : Set) (A_R : A -> A₂ -> Prop) (B : A -> Set) (B₂ : A₂ -> Set)
   (B_R : forall (H : A) (H0 : A₂), A_R H H0 -> B H -> B₂ H0 -> Prop) 
   (a : A) (a₂ : A₂) (a_R : A_R a a₂) (b : B a) (b₂ : B₂ a₂) (_ : B_R a a₂ a_R b b₂)
   (_ : True) (retTyp : Set) (rett : retTyp) => rett)
Top_multIndices_multInd_RR0_paramConstr_0_paramInv is defined
(fun (A A₂ : Set) (A_R : A -> A₂ -> Prop) (B : A -> Set) (B₂ : A₂ -> Set)
   (B_R : forall (H : A) (H0 : A₂), A_R H H0 -> B H -> B₂ H0 -> Prop) 
   (a : A) (a₂ : A₂) (a_R : A_R a a₂) (b : B a) (b₂ : B₂ a₂) (_ : B_R a a₂ a_R b b₂) => I)
Top_multIndices_multInd_RR0_paramConstr_0 is defined
*)

Print Top_multIndices_multInd_RR0_paramConstr_0_paramInv.

Print Top_multIndices_multInd_RR0_paramConstr_0.

Definition multInd_RR :
 forall (A A₂ : Set) (A_R : A -> A₂ -> Prop) (B : A -> Set) 
         (B₂ : A₂ -> Set) (B_R : forall (H : A) (H0 : A₂), A_R H H0 -> B H -> B₂ H0 -> Prop)
         (a : A) (a₂ : A₂) (a_R : A_R a a₂) (b : B a) (b₂ : B₂ a₂),
       B_R a a₂ a_R b b₂ ->
       forall (a0 : A) (a₂0 : A₂) (a_R0 : A_R a0 a₂0) (H : B a0) (H0 : B₂ a₂0),
       B_R a0 a₂0 a_R0 H H0 -> multInd A B a b a0 H -> multInd A₂ B₂ a₂ b₂ a₂0 H0 -> Prop.
refine (fix
 Top_multIndices_multInd_RR0 (A A₂ : Set) (A_R : A -> A₂ -> Prop) 
                             (B : A -> Set) (B₂ : A₂ -> Set)
                             (B_R : forall (H : A) (H0 : A₂),
                                    A_R H H0 -> B H -> B₂ H0 -> Prop) 
                             (a : A) (a₂ : A₂) (a_R : A_R a a₂) 
                             (b : B a) (b₂ : B₂ a₂) (b_R : B_R a a₂ a_R b b₂) 
                             (a0 : A) (a₂0 : A₂) (a_R0 : A_R a0 a₂0) 
                             (H : B a0) (H0 : B₂ a₂0) (H1 : B_R a0 a₂0 a_R0 H H0)
                             (H2 : multInd A B a b a0 H) (H3 : multInd A₂ B₂ a₂ b₂ a₂0 H0)
                             {struct H2} : Prop :=
   let reT a1 a2 b1 b2 := forall (ar : A_R a1 a2) (br : B_R a1 a2 ar b1 b2), Prop in
   (match H2 in multInd _ _ _ _ a1 b1 return reT a1 a₂0 b1 H0 with
   | eq_refls _ _ _ _ => match H3 
    in multInd _ _ _ _ a2 b2 return reT a a2 b b2 with
    
                         | eq_refls _ _ _ _ => fun  ar0 br => 
                            @existT _ (fun ar => B_R a a₂ ar b b₂) a_R b_R = @existT _ _ ar0 br
                         end
  end)  a_R0 H1).
Defined.


Definition multInd_recs := 
fun (A : Set) (B : A -> Set) (a : A) (b : B a)
  (P : forall (a0 : A) (b0 : B a0), multInd A B a b a0 b0 -> Set)
  (f : P a b (eq_refls A B a b)) (a0 : A) (y : B a0) (m : multInd A B a b a0 y) =>
match m as m0 in (multInd _ _ _ _ a1 y0) return (P a1 y0 m0) with
| eq_refls _ _ _ _ => f
end.