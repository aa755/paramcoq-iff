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

Require Import List.

(* Run TemplateProgram (genParamInd [] false true true "ReflParam.matchR.list"). *)

Fixpoint list_RF (A A₂ : Type) (A_R : A -> A₂ -> Type) 
                                  (l : list A) (l₂ : list A₂) {struct l} :
   Type :=
   match l with
   | nil =>
       match l₂ with
       | nil => True
       | cons _ _ => False
       end
   | cons h tl =>
       match l₂ with
       | nil  => False
       | cons h₂ tl₂ =>
           A_R h h₂ * list_RF A A₂ A_R tl tl₂
       end
   end.

Inductive list_R (A₁ A₂ : Type) (A_R : A₁ -> A₂ -> Type) : list A₁ -> list A₂ -> Type :=
| nil_R : list_R A₁ A₂ A_R [] []
| cons_R : forall (h : A₁) (h₂ : A₂),
    A_R h h₂ ->
    forall (tl : list A₁) (tl₂ : list A₂),
    list_R A₁ A₂ A_R tl tl₂ -> list_R A₁ A₂ A_R (h :: tl) (h₂ :: tl₂).

About list_R. 

Check  ((list_R nat nat (fun _ _ => True) [] []):Set).
Fail Check  ((list_RF nat nat (fun _ _ => True) [] []):Set).
About list.

Fail Check  ((list_R nat nat (fun _ _ => True) [] []):Prop).

(* Parametricity Recursive Datatypes.list. 

    Definition LT:= forall A:Type, list A->nat.
    Parametricity Recursive LT.
*)

