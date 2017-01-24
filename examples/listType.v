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



Set Universe Polymorphism.

Inductive list@{i} (A : Type@{i}) : Type@{i} 
:=  nil : list A | cons : A -> list A -> list A.

Arguments nil {A}.
Arguments cons {A} h tl.

Inductive list_R@{i} (A₁ A₂ : Type@{i}) 
  (A_R : A₁ -> A₂ -> Type@{i}) : list A₁ -> list A₂ -> Type@{i} :=
| nil_R : list_R A₁ A₂ A_R nil nil
| cons_R : forall (h : A₁) (h₂ : A₂),
    A_R h h₂ ->
    forall (tl : list A₁) (tl₂ : list A₂),
    list_R A₁ A₂ A_R tl tl₂ -> list_R A₁ A₂ A_R (cons h tl) (cons h₂ tl₂). 

   
Fixpoint list_RF@{i} (A: Type@{i}) (A₂ : Type@{i}) (A_R : A -> A₂ -> Type@{i}) 
                                  (l : list@{i} A) (l₂ : list@{i} A₂) {struct l}
                                  : Type@{i} :=
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
           (A_R h h₂ * list_RF A A₂ A_R tl tl₂)%type
       end
   end.


Check  ((list_R nat nat (fun _ _ => True) nil nil):Set).
Check  ((list_RF nat nat (fun _ _ => True) nil nil):Set).
Check  ((list_R Set Set (fun _ _ => True) nil nil):Type).
Check  ((list_RF Set Set (fun _ _ => True) nil nil):Type).
Fail Check  ((list_R Set Set (fun _ _ => True) nil nil):Set).
Fail Check  ((list_RF Set Set (fun _ _ => True) nil nil):Set).

About list.

Fail Check  ((list_R nat nat (fun _ _ => True) [] []):Prop).

