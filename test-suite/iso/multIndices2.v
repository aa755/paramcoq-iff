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


Inductive multInd (A I : Set) (B: I-> Set) (f: A-> I) (g: forall i, B i) 
  : forall (i:I) (b:B i), Set  :=  
mlin1d : forall a, multInd A I B f g (f a) (g (f a)).
(* | mlin2d : forall a2a, multInd A I B f g (f a2a) (g (f a2a)). *)


Require Import SquiggleEq.UsefulTypes.

Run TemplateProgram (genParamInd [] true true "Top.multIndices2.multInd").
Check Top_multIndices2_multInd_pmtcty_RR0_indices_irr. (* correct! *)
Print Top_multIndices2_multInd_pmtcty_RR0_constr_0_tot. (* correct! *)


Require Import ReflParam.Trecord.
Locate BestOne12.
Locate BestOne21.

Run TemplateProgram (genParamIndTotAll [] true "Top.multIndices2.multInd").
