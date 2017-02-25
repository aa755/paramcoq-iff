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
Module Temp.
Run TemplateProgram (genParamIndProp [] true "Top.IWP.IWT").
End Temp.

Definition Top_IWP_IWT_pmtcty_RR0 :=
Temp.Top_IWP_IWT_pmtcty_RR0.

Definition Top_IWP_IWT_pmtcty_RR0_constr_0 :=
Temp.Top_IWP_IWT_pmtcty_RR0_constr_0.

Check Top_IWP_IWT_pmtcty_RR0_constr_0.
(*return type is I_R (params_R++cretIndices_R++[cApplied; tprime cApplied]) 
Temp.Top_IWP_IWT_pmtcty_RR0 I I₂ I_R A A₂ A_R B B₂ B_R AI AI₂ AI_R BI BI₂ BI_R 
         (AI a) (AI₂ a₂) (AI_R a a₂ a_R) 
         (iwt I A B AI BI a lim) (iwt I₂ A₂ B₂ AI₂ BI₂ a₂ lim₂)
*)
Run TemplateProgram (genParamIndPropCRTots [] true "Top.IWP.IWT").

(* 
Error: In pattern-matching on term
 "Top_IWP_IWT_pmtcty_RR0_indices_irr I I₂ I_R A A₂ A_R B B₂ B_R AI AI₂ AI_R BI BI₂ BI_R
    (AI a) (AI₂ a₂) (AI_R a a₂ a_R) i_R" the branch for constructor
"Top_IWP_IWT_pmtcty_RR0_indicesc" has type
 "Temp.Top_IWP_IWT_pmtcty_RR0 I I₂ I_R A A₂ A_R B B₂ B_R AI AI₂ AI_R BI BI₂ BI_R 
    (AI a) (AI₂ a₂) (AI_R a a₂ a_R) (iwt I A B AI BI a lim) (iwt I₂ A₂ B₂ AI₂ BI₂ a₂ lim₂)"
which should be
 "{a_R0 : A_R a a₂ &
  {_
  : forall (b : B a) (b₂ : B₂ a₂) (b_R : B_R a a₂ a_R0 b b₂),
    Top_IWP_IWT_pmtcty_RR0 I I₂ I_R A A₂ A_R B B₂ B_R AI AI₂ AI_R BI BI₂ BI_R 
      (BI a b) (BI₂ a₂ b₂) (BI_R a a₂ a_R0 b b₂ b_R) (lim b) (lim₂ b₂) &
  Top_IWP_IWT_pmtcty_RR0_indices I I₂ I_R A A₂ A_R B B₂ B_R AI AI₂ AI_R BI BI₂ BI_R 
    (AI a) (AI₂ a₂) (AI_R a a₂ a_R0) (AI_R a a₂ a_R)}}".
    *)

Axiom 
Top_IWP_IWT_pmtcty_RR0_constr_0_tot
     : forall (I I₂ : Set) (I_R : I -> I₂ -> Prop) (A A₂ : Set) 
         (A_R : A -> A₂ -> Prop) (B : A -> Set) (B₂ : A₂ -> Set)
         (B_R : forall (H : A) (H0 : A₂), A_R H H0 -> B H -> B₂ H0 -> Prop) 
         (AI : A -> I) (AI₂ : A₂ -> I₂)
         (AI_R : forall (H : A) (H0 : A₂), A_R H H0 -> I_R (AI H) (AI₂ H0))
         (BI : forall a : A, B a -> I) (BI₂ : forall a₂ : A₂, B₂ a₂ -> I₂)
         (BI_R : forall (a : A) (a₂ : A₂) (a_R : A_R a a₂) (H : B a) (H0 : B₂ a₂),
                 B_R a a₂ a_R H H0 -> I_R (BI a H) (BI₂ a₂ H0)) 
         (a : A) (a₂ : A₂) (a_R : A_R a a₂) (lim : forall b : B a, IWT I A B AI BI (BI a b))
         (lim₂ : forall b₂ : B₂ a₂, IWT I₂ A₂ B₂ AI₂ BI₂ (BI₂ a₂ b₂)),
       (forall (b : B a) (b₂ : B₂ a₂) (b_R : B_R a a₂ a_R b b₂),
        Top_IWP_IWT_pmtcty_RR0 I I₂ I_R A A₂ A_R B B₂ B_R AI AI₂ AI_R BI BI₂ BI_R 
          (BI a b) (BI₂ a₂ b₂) (BI_R a a₂ a_R b b₂ b_R) (lim b) 
          (lim₂ b₂)) ->
       forall i_R : I_R (AI a) (AI₂ a₂),
       Top_IWP_IWT_pmtcty_RR0 I I₂ I_R A A₂ A_R B B₂ B_R AI AI₂ AI_R BI BI₂ BI_R
       (AI a) (AI₂ a₂) i_R (iwt _ _ _ _ _ a lim) (iwt _ _ _ _ _ a₂ lim₂).

Run TemplateProgram (genParamIndPropIffComplete [false] [] true "Top.IWP.IWT").




Inductive multInd2 (A I : Set) (B: I-> Set) (f: A-> I) (g: forall i, B i) 
  : forall (i:I) (b:B i), Prop  :=  
mlind2 : forall a
(dd:forall (aa:A), multInd2 A I B f g (f aa) (g (f aa))),
multInd2 A I B f g (f a) (g (f a))

|mlind2d : forall aaaa
(ddd:forall (aaa:A), multInd2 A I B f g (f aaa) (g (f aaa))),
multInd2 A I B f g (f aaaa) (g (f aaaa)).


Run TemplateProgram (genParamIndProp [] true "Top.IWP.multInd2").
Print Top_IWP_multInd2_pmtcty_RR0.
