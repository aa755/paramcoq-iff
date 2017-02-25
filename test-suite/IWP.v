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
Require Import ReflParam.paramDirect.
Require Import SquiggleEq.substitution.
Require Import ReflParam.PiTypeR.
Import ListNotations.
Open Scope string_scope.

Require Import ReflParam.PIWNew.

Require Import Template.Template.

Inductive IWT (I A : Set) (B : A -> Set) (AI : A -> I) 
(BI : forall (a : A), B a -> I) : forall (i:I), Prop :=
iwt : forall (a : A) (lim: forall b : B a, IWT I A B AI BI (BI a b)),
     IWT I A B AI BI (AI a).

Inductive WT (A : Set) :  Prop :=
wt : forall (lim: WT A),
     WT A.

Require Import ReflParam.anyRelIndProp.
Run TemplateProgram (genParamIndProp [] true "Top.IWP.WT").
Run TemplateProgram (genParamIndProp [] true "Top.IWP.IWT").

Print Top_IWP_IWT_pmtcty_RR0.

(*
Query commands should not be
inserted in scripts
Inductive
Top_IWP_IWT_pmtcty_RR0 (I I₂ : Set) (I_R : I -> I₂ -> Prop) 
(A A₂ : Set) (A_R : A -> A₂ -> Prop) (B : A -> Set) (B₂ : A₂ -> Set)
(B_R : forall (H : A) (H0 : A₂),
       A_R H H0 -> (fun H1 H2 : Set => H1 -> H2 -> Prop) (B H) (B₂ H0)) 
(AI : A -> I) (AI₂ : A₂ -> I₂)
(AI_R : forall (H : A) (H0 : A₂), A_R H H0 -> I_R (AI H) (AI₂ H0))
(BI : forall a : A, B a -> I) (BI₂ : forall a₂ : A₂, B₂ a₂ -> I₂)
(BI_R : forall (a : A) (a₂ : A₂) (a_R : A_R a a₂),
        (fun (ff : B a -> I) (ff₂ : B₂ a₂ -> I₂) =>
         forall (H : B a) (H0 : B₂ a₂), B_R a a₂ a_R H H0 -> I_R (ff H) (ff₂ H0)) 
          (BI a) (BI₂ a₂))
  : forall (i : I) (i₂ : I₂),
    I_R i i₂ -> IWT I A B AI BI i -> IWT I₂ A₂ B₂ AI₂ BI₂ i₂ -> Prop :=
    Top_IWP_IWT_pmtcty_RR0_constr_0 : forall (a : A) (a₂ : A₂) 
                                        (a_R : A_R a a₂)
                                        (lim : forall b : B a, IWT I A B AI BI (BI a b))
                                        (lim₂ : forall b₂ : B₂ a₂,
                                                IWT I₂ A₂ B₂ AI₂ BI₂ (BI₂ a₂ b₂)),
                                      (forall (b : B a) (b₂ : B₂ a₂)
                                         (b_R : B_R a a₂ a_R b b₂),
                                       Top_IWP_IWT_pmtcty_RR0 I I₂ I_R A A₂ A_R B B₂ B_R
                                         AI AI₂ AI_R BI BI₂ BI_R 
                                         (BI a b) (BI₂ a₂ b₂) 
                                         (BI_R a a₂ a_R b b₂ b_R) 
                                         (lim b) (lim₂ b₂)) ->
                                      Top_IWP_IWT_pmtcty_RR0 I I₂ I_R A A₂ A_R B B₂ B_R
                                        AI AI₂ AI_R BI BI₂ BI_R 
                                        (AI a) (AI₂ a₂) (AI_R a a₂ a_R)
                                        (iwt I A B AI BI a lim)
                                        (iwt I₂ A₂ B₂ AI₂ BI₂ a₂ lim₂)
*)