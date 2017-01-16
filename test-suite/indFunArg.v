(*
abhishek@brixpro:~/parametricity/reflective-paramcoq/test-suite$ ./coqid.sh indFunArg
*)

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

(* reification of this fails
Inductive NatLike (A B:Set) (C: (A->B) -> Set): Set := 
| SS : forall (f:A->B), C f -> NatLike A B C.
*)

Inductive NatLike (A:Set) (C: A-> Set): Set := 
(* | SS : forall (f:A->B) (c:C f)  (d:forall a:A, NatLike A B C)
     (e:forall (fi:A->B) (ci:C fi), NatLike A B C), NatLike A B C *)
 | SS2 :  forall (d:forall a:A,NatLike A C),
       NatLike A C.

Let mode := false.
Run TemplateProgram (genParamInd [] mode true true true "Top.indFunArg.NatLike").

(*
(fix
 Top_NatLike_RR0 (A A₂ : Set) (A_R : A -> A₂ -> Prop) (C : A -> Set) 
                 (C₂ : A₂ -> Set)
                 (C_R : forall (H : A) (H0 : A₂), A_R H H0 -> C H -> C₂ H0 -> Prop)
                 (H : NatLike A C) (H0 : NatLike A₂ C₂) {struct H} : Prop :=
   match H with
   | SS2 _ _ d =>
       match H0 with
       | SS2 _ _ d₂ =>
           {_
           : forall (a : A) (a₂ : A₂),
             A_R a a₂ -> Top_NatLike_RR0 A A₂ A_R C C₂ C_R (d a) (d₂ a₂) & True}
       end
   end)
Top_NatLike_RR0 is defined
(fun (A A₂ : Set) (A_R : A -> A₂ -> Prop) (C : A -> Set) (C₂ : A₂ -> Set)
   (C_R : forall (H : A) (H0 : A₂), A_R H H0 -> C H -> C₂ H0 -> Prop) 
   (d : A -> NatLike A C) (d₂ : A₂ -> NatLike A₂ C₂)
   (sigt : {_
           : forall (a : A) (a₂ : A₂),
             A_R a a₂ -> Top_NatLike_RR0 A A₂ A_R C C₂ C_R (d a) (d₂ a₂) & True})
   (retTyp : Set)
   (rett : (forall (a : A) (a₂ : A₂),
            A_R a a₂ -> Top_NatLike_RR0 A A₂ A_R C C₂ C_R (d a) (d₂ a₂)) -> retTyp) =>
 let d_R := projT1 sigt in rett d_R)
Top_NatLike_RR0_paramConstr_0_paramInv is defined
(fun (A A₂ : Set) (A_R : A -> A₂ -> Prop) (C : A -> Set) (C₂ : A₂ -> Set)
   (C_R : forall (H : A) (H0 : A₂), A_R H H0 -> C H -> C₂ H0 -> Prop) 
   (d : A -> NatLike A C) (d₂ : A₂ -> NatLike A₂ C₂)
   (d_R : forall (a : A) (a₂ : A₂),
          A_R a a₂ -> Top_NatLike_RR0 A A₂ A_R C C₂ C_R (d a) (d₂ a₂)) => 
 existT d_R I)
Top_NatLike_RR0_paramConstr_0 is defined
*)