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




Inductive NatLike (A:Set) (C: forall aa:A, Set): Prop := 
 | SS : forall  (d:forall a:A, NatLike A C), NatLike A C
 | SS2 :  forall (ao:A) (cao: C ao) 
    (d:forall (a:A) (ca da: C a), NatLike A C),
       NatLike A C.

(*
Run TemplateProgram (genParamInd [] true true "Top.indFunArgP.NatLike").
*)

Require Import ReflParam.Trecord.
Require Import ReflParam.anyRelIndProp.
Open Scope string_scope.
Open Scope N_scope.
Module Temp.
Run TemplateProgram (genParamIndProp [] true "Top.indFunArgP.NatLike").


Arguments projT1 : clear implicits.
Arguments projT2 : clear implicits.

(*
Run TemplateProgram (mkIndEnv "indTransEnv" [
"Top.indFunArgP.NatLike" ]).
*)

Set Printing Depth 10000.

End Temp.


Definition Top_indFunArgP_NatLike_pmtcty_RR0 :=
Temp.Top_indFunArgP_NatLike_pmtcty_RR0.

Definition Top_indFunArgP_NatLike_pmtcty_RR0_constr_0_tot :=
Temp.Top_indFunArgP_NatLike_pmtcty_RR0_constr_0.

Definition Top_indFunArgP_NatLike_pmtcty_RR0_constr_1_tot :=
Temp.Top_indFunArgP_NatLike_pmtcty_RR0_constr_1.


Run TemplateProgram (genParamIndPropIffComplete [false] [] true "Top.indFunArgP.NatLike").



(*
Run TemplateProgram (genWrappers indTransEnv). (* enable when CRRInvs are generated *)
*)