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

Definition and (A B:Prop):=
  forall (b:bool), if b then A else B.

Module Temp.
Run TemplateProgram (genParamInd [] false true true "Coq.Init.Datatypes.bool").
End Temp.

Run TemplateProgram (mkIndEnv "indTransEnv" ["Coq.Init.Datatypes.bool"]).

Print Temp.Coq_Init_Datatypes_bool_pmtcty_RR0_constr_1_inv.

Import Temp.
(*
Definition InvType := Type.

Definition Coq_Init_Datatypes_bool_pmtcty_RR0_constr_0_inv := 
fun (sigt_R : Temp.Coq_Init_Datatypes_bool_pmtcty_RR0_indices)
  (retTyp_R : Temp.Coq_Init_Datatypes_bool_pmtcty_RR0_indices -> InvType)
  (rett_R : retTyp_R Temp.Coq_Init_Datatypes_bool_pmtcty_RR0_indicesc) =>
(fun sigt_R0 : Temp.Coq_Init_Datatypes_bool_pmtcty_RR0_indices =>
 match sigt_R0 as sigt_R1 return (retTyp_R sigt_R1) with
 | Temp.Coq_Init_Datatypes_bool_pmtcty_RR0_indicesc => rett_R
 end) sigt_R.

Definition Coq_Init_Datatypes_bool_pmtcty_RR0_constr_1_inv := 
fun (sigt_R : Temp.Coq_Init_Datatypes_bool_pmtcty_RR0_indices)
  (retTyp_R : Temp.Coq_Init_Datatypes_bool_pmtcty_RR0_indices -> InvType)
  (rett_R : retTyp_R Temp.Coq_Init_Datatypes_bool_pmtcty_RR0_indicesc) =>
(fun sigt_R0 : Temp.Coq_Init_Datatypes_bool_pmtcty_RR0_indices =>
 match sigt_R0 as sigt_R1 return (retTyp_R sigt_R1) with
 | Temp.Coq_Init_Datatypes_bool_pmtcty_RR0_indicesc => rett_R
 end) sigt_R.
*)
Definition and2 (b:bool) (A B:Prop) : Prop:=
   if b then A else B.

Definition and3 (b:bool) (A B:bool) : bool:=
   if b then A else B.

Run TemplateProgram (genParam indTransEnv false true "and3").

Definition pp := Prop.
Run TemplateProgram (genParam indTransEnv false true "pp").

Eval compute in Coq_Init_Datatypes_bool_pmtcty_RR0 true true.

Run TemplateProgram (genParam indTransEnv false true "and2").

Run TemplateProgram (genParam indTransEnv false true "and").
