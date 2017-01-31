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

Set Printing All.
Run TemplateProgram (genParam indTransEnv false true "and").

