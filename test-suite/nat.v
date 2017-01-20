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

Arguments existT : clear implicits.

Arguments eq_refl : clear implicits.

Run TemplateProgram (genParamInd [] false true true "Coq.Init.Datatypes.nat").
(*
found Inductive
(fix Coq_Init_Datatypes_nat_RR0 (H H0 : nat) {struct H} : Prop :=
   match H with
   | 0%nat => match H0 with
              | 0%nat => I = I
              | S _ => False
              end
   | S x =>
       match H0 with
       | 0%nat => False
       | S x0 => {_ : Coq_Init_Datatypes_nat_RR0 x x0 & I = I}
       end
   end)
Coq_Init_Datatypes_nat_RR0 is defined
(fun (H H0 : nat) (_ : Coq_Init_Datatypes_nat_RR0 H H0) => eq_refl True I)
Coq_Init_Datatypes_nat_RR0_paramConstr_1 is defined
(eq_refl True I)
Coq_Init_Datatypes_nat_RR0_paramConstr_0 is defined
*)

Notation S_RR := Coq_Init_Datatypes_nat_RR0_paramConstr_1.
Notation O_RR := Coq_Init_Datatypes_nat_RR0_paramConstr_0.



Notation nat_RR :=  Coq_Init_Datatypes_nat_RR0.

Open Scope nat_scope.
(*
Fixpoint Coq_Init_Nat_add_RR (n1 n2 : nat) (n_R : nat_RR n1 n2) (m1 m2 : nat) (m_R : nat_RR m1 m2):
nat_RR (n1 + m1) (n2 + m2) :=
let reT := fun n1 n2 => nat_RR n1 n2 -> nat_RR (n1 + m1) (n2 + m2) in
(match n1 return reT n1 n2 with
| 0 => 
  match n2 return reT 0 n2 with
  | 0 => fun _ => m_R
  | S _ => fun n_R => False_rect _ n_R
  end
| S p1 =>
  match n2 return reT (S p1) n2 with
  | 0 => fun n_R => False_rect _ n_R
  | S p2 => fun n_R =>
             let n_R := projT1 n_R in
             S_RR _ _ (Coq_Init_Nat_add_RR p1 p2 n_R m1 m2 m_R)
  end
end) n_R.
Notation add_RR := Coq_Init_Nat_add_RR.
*)

