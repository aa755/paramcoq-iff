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

Run TemplateProgram (genParamInd [] false true true "Coq.Init.Datatypes.nat").
Run TemplateProgram (mkIndEnv "indTransEnv" ["Coq.Init.Datatypes.nat"]).
Require Import Nat.

Fixpoint nat0 (n:nat) {struct n} : nat := 0.

Run TemplateProgram (genParam indTransEnv false true "add").

(*
this fails because we need Fix F = F (Fix F)

(fix
 nat0_R (n n₂ : nat) (n_R : Coq_Init_Datatypes_nat_pmtcty_RR0 n n₂) {struct
        n} :
   Coq_Init_Datatypes_nat_pmtcty_RR0 ((fix nat0 (n0 : nat) : nat := 0%nat) n)
     ((fix nat0 (n0 : nat) : nat := 0%nat) n₂) :=
   Coq_Init_Datatypes_nat_pmtcty_RR0_constr_0)

It checks after manual unfolding:
*)

Definition nat0_RR_manual_unfold :=
(fix
 nat0_R (n n₂ : nat) (n_R : Coq_Init_Datatypes_nat_pmtcty_RR0 n n₂) {struct
        n} :
   Coq_Init_Datatypes_nat_pmtcty_RR0 0
     0 :=
   Coq_Init_Datatypes_nat_pmtcty_RR0_constr_0).

Open Scope nat_scope.

Declare ML Module "paramcoq".
Parametricity Recursive Nat.pred. (* no error. the error was in sub *)

Parametricity Recursive Nat.add.


Print Coq_o_Init_o_Nat_o_add_R.

Lemma addUnfold (n m:nat ): 
         (match n with
         | 0%nat => m
         | S p => S (add p m)
          end)= add n m.
Proof.
  intros. destruct n; reflexivity.
Qed.

Definition add_RR_manual_fixed:
forall   (n n₂ : nat) (n_R : Coq_Init_Datatypes_nat_pmtcty_RR0 n n₂)
       (m m₂ : nat) (m_R : Coq_Init_Datatypes_nat_pmtcty_RR0 m m₂),
  Coq_Init_Datatypes_nat_pmtcty_RR0 (add n m) (add n₂ m₂).
  refine (
(fix
 add_R (add:=
        fun n m : nat => match n with
                         | 0%nat => m
                         | S p => S (p p m)
                         end)
       (add₂:=
        fun n₂ m₂ : nat =>
        match n₂ with
        | 0%nat => m₂
        | S p₂ => S (p₂ p₂ m₂)
        end) (n n₂ : nat) (n_R : Coq_Init_Datatypes_nat_pmtcty_RR0 n n₂)
       (m m₂ : nat) (m_R : Coq_Init_Datatypes_nat_pmtcty_RR0 m m₂) {struct n} :
   Coq_Init_Datatypes_nat_pmtcty_RR0
     ((fix add0 (n0 m0 : nat) {struct n0} : nat :=
         match n0 with
         | 0%nat => m0
         | S p => S (add0 p m0)
         end) n m)
     ((fix add0 (n0 m0 : nat) {struct n0} : nat :=
         match n0 with
         | 0%nat => m0
         | S p => S (add0 p m0)
         end) n₂ m₂) :=
   match
     n as n0
     return
       ((fun n1 n₂0 : nat : Set =>
         Coq_Init_Datatypes_nat_pmtcty_RR0 n1 n₂0 ->
         Coq_Init_Datatypes_nat_pmtcty_RR0
           match n1 with
           | 0 => m
           | S p => S (add p m)
           end match n₂0 with
               | 0 => m₂
               | S p₂ => S (add₂ p₂ m₂)
               end) n0 n₂)
   with
   | 0%nat =>
       match
         n₂ as n₂0
         return
           ((fun n0 n₂1 : nat : Set =>
             Coq_Init_Datatypes_nat_pmtcty_RR0 n0 n₂1 ->
             Coq_Init_Datatypes_nat_pmtcty_RR0
               match n0 with
               | 0 => m
               | S p => S (add p m)
               end match n₂1 with
                   | 0 => m₂
                   | S p₂ => S (add₂ p₂ m₂)
                   end) 0%nat n₂0)
       with
       | 0%nat =>
           fun n_R0 : Coq_Init_Datatypes_nat_pmtcty_RR0 0 0 =>
           Coq_Init_Datatypes_nat_pmtcty_RR0_constr_0_inv n_R0
             (fun _ : Coq_Init_Datatypes_nat_pmtcty_RR0 0 0 =>
              Coq_Init_Datatypes_nat_pmtcty_RR0
                match 0%nat with
                | 0 => m
                | S p => S (add p m)
                end match 0%nat with
                    | 0 => m₂
                    | S p₂ => S (add₂ p₂ m₂)
                    end) m_R
       | S p₂ =>
           fun n_R0 : Coq_Init_Datatypes_nat_pmtcty_RR0 0 (S p₂) =>
           False_rectt
             (Coq_Init_Datatypes_nat_pmtcty_RR0
                match 0%nat with
                | 0 => m
                | S p => S (add p m)
                end match S p₂ with
                    | 0 => m₂
                    | S p₂0 => S (add₂ p₂0 m₂)
                    end) n_R0
       end
   | S p =>
       match
         n₂ as n₂0
         return
           ((fun n0 n₂1 : nat : Set =>
             Coq_Init_Datatypes_nat_pmtcty_RR0 n0 n₂1 ->
             Coq_Init_Datatypes_nat_pmtcty_RR0
               match n0 with
               | 0 => m
               | S p0 => S (add p0 m)
               end match n₂1 with
                   | 0 => m₂
                   | S p₂ => S (add₂ p₂ m₂)
                   end) (S p) n₂0)
       with
       | 0%nat =>
           fun n_R0 : Coq_Init_Datatypes_nat_pmtcty_RR0 (S p) 0 =>
           False_rectt
             (Coq_Init_Datatypes_nat_pmtcty_RR0
                match S p with
                | 0 => m
                | S p0 => S (add p0 m)
                end match 0%nat with
                    | 0 => m₂
                    | S p₂ => S (add₂ p₂ m₂)
                    end) n_R0
       | S p₂ =>
           fun n_R0 : Coq_Init_Datatypes_nat_pmtcty_RR0 (S p) (S p₂) =>
           Coq_Init_Datatypes_nat_pmtcty_RR0_constr_1_inv p p₂ n_R0
             (fun _ : Coq_Init_Datatypes_nat_pmtcty_RR0 (S p) (S p₂) =>
              Coq_Init_Datatypes_nat_pmtcty_RR0
                match S p with
                | 0 => m
                | S p0 => S (add p0 m)
                end match S p₂ with
                    | 0 => m₂
                    | S p₂0 => S (add₂ p₂0 m₂)
                    end)
             (fun p_R : Coq_Init_Datatypes_nat_pmtcty_RR0 p p₂ =>
              Coq_Init_Datatypes_nat_pmtcty_RR0_constr_1 
                (add p m) (add₂ p₂ m₂) (add_R p p₂ p_R m m₂ m_R))
       end
   end n_R)
      
    )  .
   @UsefulTypes.transport _ _ _ (fun mmm =>  Coq_Init_Datatypes_nat_pmtcty_RR0 mmm (add n₂ m₂) )
                         (addUnfold n m)  
(UsefulTypes.transport (addUnfold n₂ m₂)   
                       (
Defined.


(*
Run TemplateProgram (genParam indTransEnv false true "nat0").
 *)

(*
(fix Coq_Init_Datatypes_natparam_RR0 (H H0 : nat) {struct H} : Prop :=
   match H with
   | 0%nat =>
       match H0 with
       | 0%nat => Coq_Init_Datatypes_natparam_RR0_indices
       | S _ => False
       end
   | S x =>
       match H0 with
       | 0%nat => False
       | S x0 =>
           {_ : Coq_Init_Datatypes_natparam_RR0 x x0 &
           Coq_Init_Datatypes_natparam_RR0_indices}
       end
   end)
(fun (H H0 : nat)
   (sigt_R : {_ : Coq_Init_Datatypes_natparam_RR0 H H0 &
             Coq_Init_Datatypes_natparam_RR0_indices})
   (retTyp_R : {_ : Coq_Init_Datatypes_natparam_RR0 H H0 &
               Coq_Init_Datatypes_natparam_RR0_indices} -> Set)
   (_ : forall H1 : Coq_Init_Datatypes_natparam_RR0 H H0,
        retTyp_R
          (existT (Coq_Init_Datatypes_natparam_RR0 H H0)
             (fun _ : Coq_Init_Datatypes_natparam_RR0 H H0 =>
              Coq_Init_Datatypes_natparam_RR0_indices) H1
             Coq_Init_Datatypes_natparam_RR0_indicesc)) => fiat (retTyp_R sigt_R))
(fun (H H0 : nat) (H1 : Coq_Init_Datatypes_natparam_RR0 H H0) =>
 existT (Coq_Init_Datatypes_natparam_RR0 H H0)
   (fun _ : Coq_Init_Datatypes_natparam_RR0 H H0 => Coq_Init_Datatypes_natparam_RR0_indices)
   H1 Coq_Init_Datatypes_natparam_RR0_indicesc)
(fun (sigt_R : Coq_Init_Datatypes_natparam_RR0_indices)
   (retTyp_R : Coq_Init_Datatypes_natparam_RR0_indices -> Set)
   (_ : retTyp_R Coq_Init_Datatypes_natparam_RR0_indicesc) => fiat (retTyp_R sigt_R))
Coq_Init_Datatypes_natparam_RR0_indicesc


*)
Notation S_RR := Coq_Init_Datatypes_nat_pmtcty_RR0_constr_1.
Notation O_RR := Coq_Init_Datatypes_nat_pmtcty_RR0_constr_1.



Notation nat_RR :=  Coq_Init_Datatypes_nat_pmtcty_RR0.


Open Scope nat_scope.
Fixpoint Coq_Init_Nat_add_pmtcty_RR (n1 n2 : nat)
         (n_R : nat_RR n1 n2) (m1 m2 : nat) (m_R : nat_RR m1 m2):
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
             S_RR _ _ (Coq_Init_Nat_add_pmtcty_RR p1 p2 n_R m1 m2 m_R)
  end
end) n_R.
Notation add_RR := Coq_Init_Nat_add_pmtcty_RR.



Run TemplateProgram (genParam indTransEnv false true "pred").
(*
Print pred_RR.
*)
(*
pred_RR = 
fun (n n₂ : nat) (n_R : nat_RR n n₂) =>
match
  n as n0
  return
    ((fun n1 n₂0 : nat : Set =>
      nat_RR n1 n₂0 ->
      nat_RR match n1 with
             | 0 => n
             | S u => u
             end match n₂0 with
                 | 0 => n₂
                 | S u₂ => u₂
                 end) n0 n₂)
with
| 0 =>
    match
      n₂ as n₂0
      return
        ((fun n0 n₂1 : nat : Set =>
          nat_RR n0 n₂1 ->
          nat_RR match n0 with
                 | 0 => n
                 | S u => u
                 end match n₂1 with
                     | 0 => n₂
                     | S u₂ => u₂
                     end) 0 n₂0)
    with
    | 0 =>
        fun n_R0 : nat_RR 0 0 =>
        Coq_Init_Datatypes_nat_pmtcty_RR0_constr_0_inv n_R0
          (fun _ : nat_RR 0 0 =>
           nat_RR match 0 with
                  | 0 => n
                  | S u => u
                  end match 0 with
                      | 0 => n₂
                      | S u₂ => u₂
                      end) n_R
    | S u₂ =>
        fun n_R0 : nat_RR 0 (S u₂) =>
        False_rectt
          (nat_RR match 0 with
                  | 0 => n
                  | S u => u
                  end match S u₂ with
                      | 0 => n₂
                      | S u₂0 => u₂0
                      end) n_R0
    end
| S u =>
    match
      n₂ as n₂0
      return
        ((fun n0 n₂1 : nat : Set =>
          nat_RR n0 n₂1 ->
          nat_RR match n0 with
                 | 0 => n
                 | S u0 => u0
                 end match n₂1 with
                     | 0 => n₂
                     | S u₂ => u₂
                     end) (S u) n₂0)
    with
    | 0 =>
        fun n_R0 : nat_RR (S u) 0 =>
        False_rectt
          (nat_RR match S u with
                  | 0 => n
                  | S u0 => u0
                  end match 0 with
                      | 0 => n₂
                      | S u₂ => u₂
                      end) n_R0
    | S u₂ =>
        fun n_R0 : nat_RR (S u) (S u₂) =>
        Coq_Init_Datatypes_nat_pmtcty_RR0_constr_1_inv u u₂ n_R0
          (fun _ : nat_RR (S u) (S u₂) =>
           nat_RR match S u with
                  | 0 => n
                  | S u0 => u0
                  end match S u₂ with
                      | 0 => n₂
                      | S u₂0 => u₂0
                      end) (fun u_R : nat_RR u u₂ => u_R)
    end
end n_R
     : forall n n₂ : nat,
       nat_RR n n₂ ->
       nat_RR match n with
              | 0 => n
              | S u => u
              end match n₂ with
                  | 0 => n₂
                  | S u₂ => u₂
                  end

Argument scopes are [nat_scope nat_scope _]
*)

Declare ML Module "paramcoq".
Parametricity Recursive Nat.pred. (* no error. the error was in sub *)

Parametricity Recursive Nat.add.
(*
Print Coq_o_Init_o_Nat_o_pred_R.
Print Coq_o_Init_o_Nat_o_add_R.
*)
Definition Coq_o_Init_o_Nat_o_pred_R2 := 
fun (n₁ n₂ : nat) (n_R : nat_R n₁ n₂) =>
match
  n_R in (nat_R n₁0 n₂0)
  return (nat_R match n₁0 with
                | 0 => n₁
                | S u => u
                end match n₂0 with
                    | 0 => n₂
                    | S u => u
                    end)
with
| nat_R_O_R => n_R (* this accidentally has the right type. not so lucky in sub *)
| nat_R_S_R _ _ u_R => u_R
end.

(*
Fixpoint sub_R (n₁ n₂ : nat) (n_R : nat_R n₁ n₂) (m₁ m₂ : nat) (m_R : nat_R m₁ m₂)
  {struct n_R} : nat_R (sub n₁ m₁) (sub n₂  m₂) :=
match n_R in nat_R n₁ n₂ return nat_R (sub n₁ m₁) (sub n₂ m₂)  with 
| nat_R_O_R => n_R (*type error. expecting nat_R 0 0, found nat_R n₁ n₂. this should be O_R*)
| nat_R_S_R nr₁ nr₂ nr_R => fiat _
end.
*)
Fixpoint sub_R (n₁ n₂ : nat) (n_R : nat_R n₁ n₂) (m₁ m₂ : nat) (m_R : nat_R m₁ m₂)
  {struct n_R} : nat_R (sub n₁ m₁) (sub n₂  m₂) :=
(match n_R in nat_R n₁ n₂ return nat_R n₁ n₂ -> nat_R (sub n₁ m₁) (sub n₂ m₂)  with 
| nat_R_O_R => fun n_R => n_R (*type error. expecting nat_R 0 0, found nat_R n₁ n₂. this should be O_R*)
| nat_R_S_R nr₁ nr₂ nr_R => fun n_R => fiat _
end) n_R.
 *)