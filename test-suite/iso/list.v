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

Definition listTot :=
(fix
 Top_list_list_pmtcty_RR0_iso (A A₂ : Set) (A_R : BestRel A A₂) 
                              (H : list A) {struct H} :
   {H0 : list A₂ & Top_list_list_pmtcty_RR0 A A₂ (BestR A_R) H H0} :=
   match
     H as H0
     return {H1 : list A₂ & Top_list_list_pmtcty_RR0 A A₂ (BestR A_R) H0 H1}
   with
   | nil _ => existT _ (nil A₂) (Top_list_list_pmtcty_RR0_constr_0 _ _ (BestR A_R))
   | cons _ l a =>
       let l₂ := Top_list_list_pmtcty_RR0_iso A A₂ A_R l in
       let l_R := projT2 l₂ in
       let l₂ := projT1 l₂ in
       let a₂ := BestTot12 A_R a in
       let a_R := BestTot12R A_R a in
       existT _ (cons A₂ l₂ a₂)
        (Top_list_list_pmtcty_RR0_constr_1 _ _ (BestR A_R) l l₂ l_R a a₂ a_R)
   end).


Run TemplateProgram (genParamIndTot [] false true "Top.list.list").

Require Import Nat.

(* functions wont work until we fully produce the goodness of inductives *)