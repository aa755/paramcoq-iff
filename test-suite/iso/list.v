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


Require Import Template.Template.

Inductive list (A : Set) : Set :=  
nil : list A | cons : forall (l:list A) (a:A) , list A.


(* Inductive nat : Set :=  O : nat | S : forall ns:nat, nat. *)

Run TemplateProgram (genParamInd [] true true "Top.list.list").

Require Import ReflParam.Trecord.

Require Import String.
Require Import Ascii.
Require Import Template.Ast.

Open Scope string_scope.
Print Top_list_list_pmtcty_RR0_constr_1.

   


Run TemplateProgram (genParamIndTotAll [] true "Top.list.list").

Require Import Nat.

(* functions wont work until we fully produce the goodness of inductives *)