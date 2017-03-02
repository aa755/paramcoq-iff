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
Run TemplateProgram (genParamIndPropAll [] "Top.IWP.WT").
Run TemplateProgram (genParamIndPropAll [] "Top.IWP.IWT").

Print Top_IWP_WT_pmtcty_RR0_iso.



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
