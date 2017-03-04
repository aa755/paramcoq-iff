(*
abhishek@brixpro:~/parametricity/reflective-paramcoq/test-suite$ ./coqid.sh indFunArg
*)

Require Import SquiggleEq.terms.


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

Require Import ReflParam.PIWNew.

Require Import Template.Template.

Inductive IWT (I A : Set) (B : A -> Set) (AI : A -> I) 
(BI : forall (a : A), B a -> I) : forall (i:I), Set :=
    iwt : forall (a : A) (lim: forall b : B a, IWT I A B AI BI (BI a b)),
     IWT I A B AI BI (AI a).
    
Run TemplateProgram (genParamInd [] true true "Top.IWTS.IWT").

Print Top_IWTS_IWT_pmtcty_RR0_indices.

Module Temp.

Inductive Top_IWTS_IWT_pmtcty_RR0_indices (I I₂ : Set) (I_R : I -> I₂ -> Prop) 
(A A₂ : Set) (A_R : A -> A₂ -> Prop) (B : A -> Set) (B₂ : A₂ -> Set)
(B_R : forall (H : A) (H0 : A₂),
       A_R H H0 -> (fun H1 H2 : Set => H1 -> H2 -> Prop) (B H) (B₂ H0)) 
(AI : A -> I) (AI₂ : A₂ -> I₂)
(AI_R : forall (H : A) (H0 : A₂), A_R H H0 -> I_R (AI H) (AI₂ H0))
(BI : forall a : A, B a -> I) (BI₂ : forall a₂ : A₂, B₂ a₂ -> I₂)
(BI_R : forall (a : A) (a₂ : A₂) (a_R : A_R a a₂),
        (fun (ff : B a -> I) (ff₂ : B₂ a₂ -> I₂) =>
         forall (H : B a) (H0 : B₂ a₂), B_R a a₂ a_R H H0 -> I_R (ff H) (ff₂ H0)) 
          (BI a) (BI₂ a₂)) (i : I) (i₂ : I₂) (i_R : I_R i i₂) : 
I_R i i₂ -> Prop :=
    Top_IWTS_IWT_pmtcty_RR0_indicesc : Top_IWTS_IWT_pmtcty_RR0_indices I I₂ I_R A A₂ A_R B
                                         B₂ B_R AI AI₂ AI_R BI BI₂ BI_R i i₂ i_R i_R.

Print Top_IWTS_IWT_pmtcty_RR0.
Definition IWT_R :=
fun (I I₂ : Set) (I_R : I -> I₂ -> Prop) (A A₂ : Set) (A_R : A -> A₂ -> Prop) 
  (B : A -> Set) (B₂ : A₂ -> Set)
  (B_R : forall (H : A) (H0 : A₂),
         A_R H H0 -> (fun H1 H2 : Set => H1 -> H2 -> Prop) (B H) (B₂ H0)) 
  (AI : A -> I) (AI₂ : A₂ -> I₂)
  (AI_R : forall (H : A) (H0 : A₂), A_R H H0 -> I_R (AI H) (AI₂ H0))
  (BI : forall a : A, B a -> I) (BI₂ : forall a₂ : A₂, B₂ a₂ -> I₂)
  (BI_R : forall (a : A) (a₂ : A₂) (a_R : A_R a a₂),
          (fun (ff : B a -> I) (ff₂ : B₂ a₂ -> I₂) =>
           forall (H : B a) (H0 : B₂ a₂), B_R a a₂ a_R H H0 -> I_R (ff H) (ff₂ H0)) 
            (BI a) (BI₂ a₂)) =>
fix
Top_IWTS_IWT_pmtcty_RR0 (i : I) (i₂ : I₂) (i_R : I_R i i₂) (H : IWT I A B AI BI i)
                        (H0 : IWT I₂ A₂ B₂ AI₂ BI₂ i₂) {struct H} : Prop :=
  match H in (IWT _ _ _ _ _ i0) return (I_R i0 i₂ -> Prop) with
  | iwt _ _ _ _ _ a lim =>
      match H0 in (IWT _ _ _ _ _ i₂0) return (I_R (AI a) i₂0 -> Prop) with
      | iwt _ _ _ _ _ a₂ lim₂ =>
          fun i_R0 : I_R (AI a) (AI₂ a₂) =>
          {a_R : A_R a a₂ &
          {_
          : forall (b : B a) (b₂ : B₂ a₂) (b_R : B_R a a₂ a_R b b₂),
            (fun (I0 I₂0 : Set) (I_R0 : I0 -> I₂0 -> Prop) (A0 A₂0 : Set)
               (A_R0 : A0 -> A₂0 -> Prop) (B0 : A0 -> Set) (B₂0 : A₂0 -> Set)
               (B_R0 : forall (H1 : A0) (H2 : A₂0),
                       A_R0 H1 H2 -> (fun H3 H4 : Set => H3 -> H4 -> Prop) (B0 H1) (B₂0 H2))
               (AI0 : A0 -> I0) (AI₂0 : A₂0 -> I₂0)
               (_ : forall (H1 : A0) (H2 : A₂0), A_R0 H1 H2 -> I_R0 (AI0 H1) (AI₂0 H2))
               (BI0 : forall a0 : A0, B0 a0 -> I0) (BI₂0 : forall a₂0 : A₂0, B₂0 a₂0 -> I₂0)
               (_ : forall (a0 : A0) (a₂0 : A₂0) (a_R0 : A_R0 a0 a₂0),
                    (fun (ff : B0 a0 -> I0) (ff₂ : B₂0 a₂0 -> I₂0) =>
                     forall (H1 : B0 a0) (H2 : B₂0 a₂0),
                     B_R0 a0 a₂0 a_R0 H1 H2 -> I_R0 (ff H1) (ff₂ H2)) 
                      (BI0 a0) (BI₂0 a₂0)) => Top_IWTS_IWT_pmtcty_RR0) I I₂ I_R A A₂ A_R B
              B₂ B_R AI AI₂ AI_R BI BI₂ BI_R (BI a b) (BI₂ a₂ b₂) 
              (BI_R a a₂ a_R b b₂ b_R) (lim b) (lim₂ b₂) &
          IWTS.Top_IWTS_IWT_pmtcty_RR0_indices I I₂ I_R A A₂ A_R B B₂ B_R AI AI₂ AI_R BI BI₂
            BI_R (AI a) (AI₂ a₂) (AI_R a a₂ a_R) i_R0}}
      end
  end i_R.
  
End Temp.
