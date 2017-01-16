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

Require Import ReflParam.PIWNew.


Let mode := false.
Arguments existT : clear implicits.
Run TemplateProgram (genParamInd [] mode true true true "ReflParam.PIWNew.IWT").

(*
(fix
 ReflParam_PIWNew_IWT_RR0 (I I₂ : Set) (I_R : I -> I₂ -> Prop) (A A₂ : Set)
                          (A_R : A -> A₂ -> Prop) (B : A -> Set) 
                          (B₂ : A₂ -> Set)
                          (B_R : forall (H : A) (H0 : A₂), A_R H H0 -> B H -> B₂ H0 -> Prop)
                          (AI : A -> I) (AI₂ : A₂ -> I₂)
                          (AI_R : forall (H : A) (H0 : A₂), A_R H H0 -> I_R (AI H) (AI₂ H0))
                          (BI : forall a : A, B a -> I) (BI₂ : forall a₂ : A₂, B₂ a₂ -> I₂)
                          (BI_R : forall (a : A) (a₂ : A₂) (a_R : A_R a a₂) 
                                    (H : B a) (H0 : B₂ a₂),
                                  B_R a a₂ a_R H H0 -> I_R (BI a H) (BI₂ a₂ H0)) 
                          (H : I) (H0 : I₂) (H1 : I_R H H0) (H2 : IWT I A B AI BI H)
                          (H3 : IWT I₂ A₂ B₂ AI₂ BI₂ H0) {struct H2} : Prop :=
   match H2 with
   | iwt _ _ _ _ _ a x =>
       match H3 with
       | iwt _ _ _ _ _ a₂ x0 =>
           {a_R : A_R a a₂ &
           {_
           : forall (b : B a) (b₂ : B₂ a₂) (b_R : B_R a a₂ a_R b b₂),
             ReflParam_PIWNew_IWT_RR0 I I₂ I_R A A₂ A_R B B₂ B_R AI AI₂ AI_R BI BI₂ BI_R
               (BI a b) (BI₂ a₂ b₂) (BI_R a a₂ a_R b b₂ b_R) (x b) 
               (x0 b₂) & True}}
       end
   end)
ReflParam_PIWNew_IWT_RR0 is defined
(fun (I I₂ : Set) (I_R : I -> I₂ -> Prop) (A A₂ : Set) (A_R : A -> A₂ -> Prop)
   (B : A -> Set) (B₂ : A₂ -> Set)
   (B_R : forall (H : A) (H0 : A₂), A_R H H0 -> B H -> B₂ H0 -> Prop) 
   (AI : A -> I) (AI₂ : A₂ -> I₂)
   (AI_R : forall (H : A) (H0 : A₂), A_R H H0 -> I_R (AI H) (AI₂ H0))
   (BI : forall a : A, B a -> I) (BI₂ : forall a₂ : A₂, B₂ a₂ -> I₂)
   (BI_R : forall (a : A) (a₂ : A₂) (a_R : A_R a a₂) (H : B a) (H0 : B₂ a₂),
           B_R a a₂ a_R H H0 -> I_R (BI a H) (BI₂ a₂ H0)) (a : A) 
   (a₂ : A₂) (H : forall b : B a, IWT I A B AI BI (BI a b))
   (H0 : forall b₂ : B₂ a₂, IWT I₂ A₂ B₂ AI₂ BI₂ (BI₂ a₂ b₂))
   (sigt : {a_R : A_R a a₂ &
           {_
           : forall (b : B a) (b₂ : B₂ a₂) (b_R : B_R a a₂ a_R b b₂),
             ReflParam_PIWNew_IWT_RR0 I I₂ I_R A A₂ A_R B B₂ B_R AI AI₂ AI_R BI BI₂ BI_R
               (BI a b) (BI₂ a₂ b₂) (BI_R a a₂ a_R b b₂ b_R) (H b) 
               (H0 b₂) & True}}) (retTyp : Set)
   (rett : forall a_R : A_R a a₂,
           (forall (b : B a) (b₂ : B₂ a₂) (b_R : B_R a a₂ a_R b b₂),
            ReflParam_PIWNew_IWT_RR0 I I₂ I_R A A₂ A_R B B₂ B_R AI AI₂ AI_R BI BI₂ BI_R
              (BI a b) (BI₂ a₂ b₂) (BI_R a a₂ a_R b b₂ b_R) (H b) 
              (H0 b₂)) -> retTyp) =>
 let a_R := projT1 sigt in let H1 := projT1 (projT2 sigt) in rett a_R H1)
ReflParam_PIWNew_IWT_RR0_paramConstr_0_paramInv is defined
(fun (I0 I₂ : Set) (I_R : I0 -> I₂ -> Prop) (A A₂ : Set) (A_R : A -> A₂ -> Prop)
   (B : A -> Set) (B₂ : A₂ -> Set)
   (B_R : forall (H : A) (H0 : A₂), A_R H H0 -> B H -> B₂ H0 -> Prop) 
   (AI : A -> I0) (AI₂ : A₂ -> I₂)
   (AI_R : forall (H : A) (H0 : A₂), A_R H H0 -> I_R (AI H) (AI₂ H0))
   (BI : forall a : A, B a -> I0) (BI₂ : forall a₂ : A₂, B₂ a₂ -> I₂)
   (BI_R : forall (a : A) (a₂ : A₂) (a_R : A_R a a₂) (H : B a) (H0 : B₂ a₂),
           B_R a a₂ a_R H H0 -> I_R (BI a H) (BI₂ a₂ H0)) (a : A) 
   (a₂ : A₂) (a_R : A_R a a₂) (H : forall b : B a, IWT I0 A B AI BI (BI a b))
   (H0 : forall b₂ : B₂ a₂, IWT I₂ A₂ B₂ AI₂ BI₂ (BI₂ a₂ b₂))
   (H1 : forall (b : B a) (b₂ : B₂ a₂) (b_R : B_R a a₂ a_R b b₂),
         ReflParam_PIWNew_IWT_RR0 I0 I₂ I_R A A₂ A_R B B₂ B_R AI AI₂ AI_R BI BI₂ BI_R
           (BI a b) (BI₂ a₂ b₂) (BI_R a a₂ a_R b b₂ b_R) (H b) (H0 b₂)) =>
 existT (A_R a a₂)
   (fun a_R0 : A_R a a₂ =>
    {_
    : forall (b : B a) (b₂ : B₂ a₂) (b_R : B_R a a₂ a_R0 b b₂),
      ReflParam_PIWNew_IWT_RR0 I0 I₂ I_R A A₂ A_R B B₂ B_R AI AI₂ AI_R BI BI₂ BI_R 
        (BI a b) (BI₂ a₂ b₂) (BI_R a a₂ a_R0 b b₂ b_R) (H b) (H0 b₂) & True}) a_R
   (existT
      (forall (b : B a) (b₂ : B₂ a₂) (b_R : B_R a a₂ a_R b b₂),
       ReflParam_PIWNew_IWT_RR0 I0 I₂ I_R A A₂ A_R B B₂ B_R AI AI₂ AI_R BI BI₂ BI_R 
         (BI a b) (BI₂ a₂ b₂) (BI_R a a₂ a_R b b₂ b_R) (H b) (H0 b₂))
      (fun
         _ : forall (b : B a) (b₂ : B₂ a₂) (b_R : B_R a a₂ a_R b b₂),
             ReflParam_PIWNew_IWT_RR0 I0 I₂ I_R A A₂ A_R B B₂ B_R AI AI₂ AI_R BI BI₂ BI_R
               (BI a b) (BI₂ a₂ b₂) (BI_R a a₂ a_R b b₂ b_R) (H b) 
               (H0 b₂) => True) H1 I))
ReflParam_PIWNew_IWT_RR0_paramConstr_0 is defined
*)

(*
(fix
 ReflParam_PIWNew_IWT_RR0 (I I₂ : Set) (I_R : I -> I₂ -> Prop) 
                          (A A₂ : Set) (A_R : A -> A₂ -> Prop) 
                          (B : A -> Set) (B₂ : A₂ -> Set)
                          (B_R : forall (H : A) (H0 : A₂),
                                 A_R H H0 -> B H -> B₂ H0 -> Prop)
                          (AI : A -> I) (AI₂ : A₂ -> I₂)
                          (AI_R : forall (H : A) (H0 : A₂),
                                  A_R H H0 -> I_R (AI H) (AI₂ H0))
                          (BI : forall a : A, B a -> I)
                          (BI₂ : forall a₂ : A₂, B₂ a₂ -> I₂)
                          (BI_R : forall (a : A) (a₂ : A₂) 
                                    (a_R : A_R a a₂) 
                                    (H : B a) (H0 : B₂ a₂),
                                  B_R a a₂ a_R H H0 ->
                                  I_R (BI a H) (BI₂ a₂ H0)) 
                          (H : I) (H0 : I₂) (H1 : I_R H H0)
                          (H2 : IWT I A B AI BI H)
                          (H3 : IWT I₂ A₂ B₂ AI₂ BI₂ H0) {struct H2} :
   Prop :=
   match H2 with
   | iwt _ _ _ _ _ a x =>
       match H3 with
       | iwt _ _ _ _ _ a₂ x0 =>
           {a_R : A_R a a₂ &
           {_
           : forall (b : B a) (b₂ : B₂ a₂) (b_R : B_R a a₂ a_R b b₂),
             ReflParam_PIWNew_IWT_RR0 I I₂ I_R A A₂ A_R B B₂ B_R AI AI₂ AI_R
               BI BI₂ BI_R (BI a b) (BI₂ a₂ b₂) (BI_R a a₂ a_R b b₂ b_R)
               (x b) (x0 b₂) & True}}
       end
   end)
Debug:
(fun (I0 I₂ : Set) (I_R : I0 -> I₂ -> Prop) (A A₂ : Set)
   (A_R : A -> A₂ -> Prop) (B : A -> Set) (B₂ : A₂ -> Set)
   (B_R : forall (H : A) (H0 : A₂), A_R H H0 -> B H -> B₂ H0 -> Prop)
   (AI : A -> I0) (AI₂ : A₂ -> I₂)
   (AI_R : forall (H : A) (H0 : A₂), A_R H H0 -> I_R (AI H) (AI₂ H0))
   (BI : forall a : A, B a -> I0) (BI₂ : forall a₂ : A₂, B₂ a₂ -> I₂)
   (BI_R : forall (a : A) (a₂ : A₂) (a_R : A_R a a₂) (H : B a) (H0 : B₂ a₂),
           B_R a a₂ a_R H H0 -> I_R (BI a H) (BI₂ a₂ H0)) 
   (a : A) (a₂ : A₂) (a_R : A_R a a₂)
   (H : forall b : B a, IWT I0 A B AI BI (BI a b))
   (H0 : forall b₂ : B₂ a₂, IWT I₂ A₂ B₂ AI₂ BI₂ (BI₂ a₂ b₂))
   (H1 : forall (b : B a) (b₂ : B₂ a₂) (b_R : B_R a a₂ a_R b b₂),
         ReflParam_PIWNew_IWT_RR0 I0 I₂ I_R A A₂ A_R B B₂ B_R AI AI₂ AI_R BI
           BI₂ BI_R (BI a b) (BI₂ a₂ b₂) (BI_R a a₂ a_R b b₂ b_R) 
           (H b) (H0 b₂)) => existT a_R (existT H1 I))
File "./IWTS.v", line 21, characters 0-81:
Error:
In environment
I : Set
I₂ : Set
I_R : I -> I₂ -> Prop
A : Set
A₂ : Set
A_R : A -> A₂ -> Prop
B : A -> Set
B₂ : A₂ -> Set
B_R : forall (H : A) (H0 : A₂), A_R H H0 -> B H -> B₂ H0 -> Prop
AI : A -> I
AI₂ : A₂ -> I₂
AI_R : forall (H : A) (H0 : A₂), A_R H H0 -> I_R (AI H) (AI₂ H0)
BI : forall a : A, B a -> I
BI₂ : forall a₂ : A₂, B₂ a₂ -> I₂
BI_R :
forall (a : A) (a₂ : A₂) (a_R : A_R a a₂) (H : B a) (H0 : B₂ a₂),
B_R a a₂ a_R H H0 -> I_R (BI a H) (BI₂ a₂ H0)
a : A
a₂ : A₂
a_R : A_R a a₂
H : forall b : B a, IWT I A B AI BI (BI a b)
H0 : forall b₂ : B₂ a₂, IWT I₂ A₂ B₂ AI₂ BI₂ (BI₂ a₂ b₂)
H1 :
forall (b : B a) (b₂ : B₂ a₂) (b_R : B_R a a₂ a_R b b₂),
ReflParam_PIWNew_IWT_RR0 I I₂ I_R A A₂ A_R B B₂ B_R AI AI₂ AI_R BI BI₂ BI_R
  (BI a b) (BI₂ a₂ b₂) (BI_R a a₂ a_R b b₂ b_R) (H b) 
  (H0 b₂)
Unable to unify
 "{_
  : forall (b : B a) (b₂ : B₂ a₂) (b_R : B_R a a₂ a_R b b₂),
    ReflParam_PIWNew_IWT_RR0 I I₂ I_R A A₂ A_R B B₂ B_R AI AI₂ AI_R BI BI₂
      BI_R (BI a b) (BI₂ a₂ b₂) (BI_R a a₂ a_R b b₂ b_R) 
      (H b) (H0 b₂) & True}" with "?P a_R".
Makefile.coq:270: recipe for target 'IWTS.vo' failed

*)