
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


(* Inductive nat : Set :=  O : nat | S : forall ns:nat, nat. *)

Run TemplateProgram (genParamInd [] true true "Coq.Init.Datatypes.nat").
Run TemplateProgram (mkIndEnv "indTransEnv" ["Coq.Init.Datatypes.nat"]).


Set Printing All.

Run TemplateProgram (genParamIndTotAll [] true "Coq.Init.Datatypes.nat").


(* functions wont work until we fully produce the goodness of inductives *)