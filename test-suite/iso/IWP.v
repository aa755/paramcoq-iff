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

Definition Top_IWP_IWT_pmtcty_RR0 :=
Top_IWP_IWT_pmtcty_RR0_prop.

Definition Top_IWP_IWT_pmtcty_RR0_constr_0 :=
Top_IWP_IWT_pmtcty_RR0_constr_0_prop.

Check Top_IWP_IWT_pmtcty_RR0_constr_0.
(*return type is I_R (params_R++cretIndices_R++[cApplied; tprime cApplied]) 
Temp.Top_IWP_IWT_pmtcty_RR0 I I₂ I_R A A₂ A_R B B₂ B_R AI AI₂ AI_R BI BI₂ BI_R 
         (AI a) (AI₂ a₂) (AI_R a a₂ a_R) 
         (iwt I A B AI BI a lim) (iwt I₂ A₂ B₂ AI₂ BI₂ a₂ lim₂)
*)
Run TemplateProgram (genParamIndPropCRTots [] true "Top.IWP.IWT").
Run TemplateProgram (genParamIndPropIffComplete [false] [] true "Top.IWP.IWT").
Run TemplateProgram (genParamIndPropIffComplete [true] [] true "Top.IWP.IWT").

Run TemplateProgram (genParamIso [] "Top.IWP.IWT").




Inductive multInd2 (A I : Set) (B: I-> Set) (f: A-> I) (g: forall i, B i) 
  : forall (i:I) (b:B i), Prop  :=  
mlind2 : forall a
(dd:forall (aa:A), multInd2 A I B f g (f aa) (g (f aa))),
multInd2 A I B f g (f a) (g (f a))

|mlind2d : forall aaaa
(ddd:forall (aaa:A), multInd2 A I B f g (f aaa) (g (f aaa))),
multInd2 A I B f g (f aaaa) (g (f aaaa)).


Run TemplateProgram (genParamIndProp [] true "Top.IWP.multInd2").
Print Top_IWP_multInd2_pmtcty_RR0_prop.
