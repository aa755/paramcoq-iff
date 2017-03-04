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

(* translation of this fails because of clashes due to unnabed binders
Inductive NatLike (A B:Set) (C: (A->B) -> Set): Set := 
| SS : forall (f:A->B), C f -> NatLike A B C.
*)

Print totalPiHalfGood (* has a universe: bad. use totalPiHalfGood2 instead*).



Inductive NatLike (A:Set) (C: forall aa:A, Set): Set := 
 | SS : forall  (d:forall a:A, NatLike A C), NatLike A C
 | SS2 :  forall (ao:A) (cao: C ao) 
 (d:forall (a:A) (ca da: C a), NatLike A C),
       NatLike A C.

Run TemplateProgram (genParamInd [] true true "Top.indFunArg.NatLike").
Require Import ReflParam.Trecord.



Arguments projT1 : clear implicits.
Arguments projT2 : clear implicits.

Run TemplateProgram (mkIndEnv "indTransEnv" [
"Top.indFunArg.NatLike" ]).


Set Printing Depth 10000.
Run TemplateProgram (genParamIndTot [(true, false)] [] true "Top.indFunArg.NatLike").

Goal False.
set (f:=Top_indFunArg_NatLike_pmtcty_RR0iff12).
unfold Top_indFunArg_NatLike_pmtcty_RR0iff12 in f.
cbv beta in f.
Abort.

(*
Run TemplateProgram (genWrappers indTransEnv). (* enable when CRRInvs are generated *)
*)