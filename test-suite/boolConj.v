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


Run TemplateProgram (genParamInd [] false true true "Coq.Init.Datatypes.bool").

Run TemplateProgram (mkIndEnv "indTransEnv" ["Coq.Init.Datatypes.bool"]).


Definition and2 (b:bool) (A B:Prop) : Prop:=
   if b then A else B.

Definition and3 (b:bool) (A B:bool) : bool:=
   if b then A else B.

Run TemplateProgram (genParam indTransEnv false true "and3").

Definition pp := Prop.
Run TemplateProgram (genParam indTransEnv false true "pp").

Eval compute in Coq_Init_Datatypes_bool_pmtcty_RR0 true true.

Run TemplateProgram (genParam indTransEnv false true "and2").

(*
The 2nd term has type "Coq_Init_Datatypes_bool_pmtcty_RR0 true true -> Type"
which should be coercible to "Coq_Init_Datatypes_bool_pmtcty_RR0_indices -> Set".
*)
Run TemplateProgram (genParam indTransEnv false true "and2").

Run TemplateProgram (genParam indTransEnv false true "and").

