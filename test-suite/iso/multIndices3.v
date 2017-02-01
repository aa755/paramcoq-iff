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


Inductive multInd (A I : Set) (B: I-> Set) (C : forall (ic:I) (bc: B ic), Set )
(f: A-> I) (g: forall i, B i) (gb : forall (igb:I) (gb:B igb), C igb gb) 
  : forall (i:I) (b:B i) (c: C i b), Set  :=  
mlind : forall a, multInd A I B C f g gb (f a) (g (f a)) (gb (f a) (g (f a))).


Require Import SquiggleEq.UsefulTypes.

Run TemplateProgram (genParamInd [] true true true "Top.multIndices3.multInd").


Require Import ReflParam.Trecord.

Set Printing All.

Run TemplateProgram (genParamIndTot [] true true "Top.multIndices3.multInd").
(* Success :)! this runs fast. the above runs slow.*)
