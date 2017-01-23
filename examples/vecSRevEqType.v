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

Require Import ReflParam.matchR. (* shadows Coq.Init.Datatypes.list *)
Require Import List.
(* Run TemplateProgram (mkIndEnv "indTransEnv" ["ReflParam.matchR.Vec"]). *)

Inductive Vec (C : Type) : nat -> Type :=
    vnil : Vec C 0 | vcons : forall n : nat, C -> Vec C n -> Vec C (n+1).
About Vec.
(*
Vec is template universe polymorphic
*)

Definition Coq_Init_Datatypes_nat_RR0 :=
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
   end).

Notation nat_RR := Coq_Init_Datatypes_nat_RR0.

Arguments existT : clear implicits.
Arguments eq_refl : clear implicits.

Definition S_RRInv:=
(fun (H H0 : nat) (sigt_R : {_ : Coq_Init_Datatypes_nat_RR0 H H0 & I = I})
   (retTyp_R : {_ : Coq_Init_Datatypes_nat_RR0 H H0 & I = I} -> Set)
   (_ : forall H1 : Coq_Init_Datatypes_nat_RR0 H H0,
        retTyp_R
          (existT (Coq_Init_Datatypes_nat_RR0 H H0)
             (fun _ : Coq_Init_Datatypes_nat_RR0 H H0 => I = I) H1 
             (eq_refl True I))) => fiat (retTyp_R sigt_R)).


Definition S_RR :=
(fun (H H0 : nat) (H1 : Coq_Init_Datatypes_nat_RR0 H H0) =>
 existT (Coq_Init_Datatypes_nat_RR0 H H0) (fun _ : Coq_Init_Datatypes_nat_RR0 H H0 => I = I)
   H1 (eq_refl True I))
.

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
Definition O_RR := (eq_refl True I).
(*   
Coq_Init_Datatypes_nat_RR0_paramConstr_1 is defined
(fun (sigt_R : I = I) (retTyp_R : I = I -> Set) (_ : retTyp_R (eq_refl True I)) =>
 fiat (retTyp_R sigt_R))
Coq_Init_Datatypes_nat_RR0_paramConstr_0_paramInv is defined
*)
    
(*
Require Import Top.nat.
Run TemplateProgram (genParamInd [] false true true true "ReflParam.matchR.Vec").
*)

Definition one_RR : nat_RR 1 1.
simpl. eexists; eauto.
Defined.

Definition Vec_RR :=
(fix
 ReflParam_matchR_Vec_RR0 (C C₂ : Type) (C_R : C -> C₂ -> Type) (H H0 : nat)
                          (H1 : nat_RR H H0) (H2 : Vec C H) (H3 : Vec C₂ H0) {struct H2} :
   Type :=
   let reT n1 n2 := forall (nr : nat_RR n1 n2), Type in
   (match H2 in Vec _ n1 return reT n1 H0 with
   | vnil _ => match H3 in Vec _ n2 return reT 0 n2  with
               | vnil _ => fun nr => nr = O_RR
               | vcons _ _ _ _ => fun _ => False
               end
   | vcons _ n x x0 =>
       match H3 with
       | vnil _ => fun _ => False
       | vcons _ n₂ x1 x2 =>
       fun nr =>
           {n_R : nat_RR n n₂ &
           {_ : C_R x x1 & {_ : ReflParam_matchR_Vec_RR0 C C₂ C_R n n₂ n_R x0 x2 
           & nr = add_RR _ _ n_R 1 1 one_RR}}}
       end
   end) H1
    ).

 (*success!*)
(*
(fun (C C₂ : Set) (C_R : C -> C₂ -> Prop) (n n₂ : nat) (H : C) (H0 : C₂) 
   (H1 : Vec C n) (H2 : Vec C₂ n₂)
   (sigt : {n_R : Coq_Init_Datatypes_nat_RR0 n n₂ &
           {_ : C_R H H0 & {_ : ReflParam_matchR_Vec_RR0 C C₂ C_R n n₂ n_R H1 H2 & True}}})
   (retTyp : Set)
   (rett : forall n_R : Coq_Init_Datatypes_nat_RR0 n n₂,
           C_R H H0 -> ReflParam_matchR_Vec_RR0 C C₂ C_R n n₂ n_R H1 H2 -> retTyp) =>
 let n_R := projT1 sigt in
 let H3 := projT1 (projT2 sigt) in let H4 := projT1 (projT2 (projT2 sigt)) in rett n_R H3 H4)
*)

Print vcons_RR.

Check (Vec nat).
(*
Vec nat : nat -> Set
*)

Check Vec.
(*
Type -> nat -> Type
*)

Check Vec: Set -> nat -> Set.
(*
(fun C : Set => Vec C) : Set
What?
*)

Fail Check ((Vec_RR nat nat nat_RR 0 0 O_RR (vnil _) (vnil _)): Prop).
(*
Error:
The term "Vec_RR nat nat nat_RR 0 0 O_RR (vnil nat) (vnil nat)" has type 
"Type" while it is expected to have type "Prop" (universe inconsistency).
*)

Fail Check ((Vec_RR nat nat nat_RR 0 0 O_RR (vnil _) (vnil _)): Set).

Check ((Vec_RR nat nat nat_RR 0 0 O_RR (vnil _) (vnil _)): Type).

