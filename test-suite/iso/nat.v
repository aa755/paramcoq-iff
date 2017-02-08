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

Definition xx :=
(fix
 Coq_Init_Datatypes_nat_pmtcty_RR0_iso (tind tind₂ tind₂o : nat)
                                       (tind_R : Coq_Init_Datatypes_nat_pmtcty_RR0
                                                 tind tind₂)
                                       (tind_Ro : 
                                        Coq_Init_Datatypes_nat_pmtcty_RR0
                                          tind tind₂o) {struct tind} :
   tind₂ = tind₂o :=
   match
     tind as tind0
     return
       (Coq_Init_Datatypes_nat_pmtcty_RR0 tind0 tind₂ ->
        Coq_Init_Datatypes_nat_pmtcty_RR0 tind0 tind₂o -> tind₂ = tind₂o)
   with
   | 0%nat =>
       match
         tind₂ as tind₂0
         return
           (forall tind₂o0 : nat,
            Coq_Init_Datatypes_nat_pmtcty_RR0 0 tind₂0 ->
            Coq_Init_Datatypes_nat_pmtcty_RR0 0 tind₂o0 -> tind₂0 = tind₂o0)
       with
       | 0%nat =>
           fun (tind₂o0 : nat)
             (tind_R0 : Coq_Init_Datatypes_nat_pmtcty_RR0 0 0)
             (tind_Ro0 : Coq_Init_Datatypes_nat_pmtcty_RR0 0 tind₂o0) =>
           let Hexeq :=
             Coq_Init_Datatypes_nat_pmtcty_RR0_constr_0_inv tind_R0
               (fun _ : Coq_Init_Datatypes_nat_pmtcty_RR0 0 0 =>
                0%nat = tind₂o0)
               (match
                  tind₂o0 as tind₂o1
                  return
                    (Coq_Init_Datatypes_nat_pmtcty_RR0 0 tind₂o1 ->
                     0%nat = tind₂o1)
                with
                | 0%nat =>
                    fun _ : Coq_Init_Datatypes_nat_pmtcty_RR0 0 0 =>
                    fiat (0%nat = 0%nat)
                | S o =>
                    fun tind_Ro1 : Coq_Init_Datatypes_nat_pmtcty_RR0 0 (S o)
                    => match tind_Ro1 return (0%nat = S o) with
                       end
                end tind_Ro0) in
           Hexeq
       | S x =>
           fun (tind₂o0 : nat)
             (tind_R0 : Coq_Init_Datatypes_nat_pmtcty_RR0 0 (S x))
             (_ : Coq_Init_Datatypes_nat_pmtcty_RR0 0 tind₂o0) =>
           match tind_R0 return (S x = tind₂o0) with
           end
       end tind₂o
   | S x =>
       match
         tind₂ as tind₂0
         return
           (forall tind₂o0 : nat,
            Coq_Init_Datatypes_nat_pmtcty_RR0 (S x) tind₂0 ->
            Coq_Init_Datatypes_nat_pmtcty_RR0 (S x) tind₂o0 ->
            tind₂0 = tind₂o0)
       with
       | 0%nat =>
           fun (tind₂o0 : nat)
             (tind_R0 : Coq_Init_Datatypes_nat_pmtcty_RR0 (S x) 0)
             (_ : Coq_Init_Datatypes_nat_pmtcty_RR0 (S x) tind₂o0) =>
           match tind_R0 return (0%nat = tind₂o0) with
           end
       | S x0 =>
           fun (tind₂o0 : nat)
             (tind_R0 : Coq_Init_Datatypes_nat_pmtcty_RR0 (S x) (S x0))
             (tind_Ro0 : Coq_Init_Datatypes_nat_pmtcty_RR0 (S x) tind₂o0) =>
           let Hexeq :=
             Coq_Init_Datatypes_nat_pmtcty_RR0_constr_1_inv x x0 tind_R0
               (fun _ : Coq_Init_Datatypes_nat_pmtcty_RR0 (S x) (S x0) =>
                S x0 = tind₂o0)
               (fun _ : Coq_Init_Datatypes_nat_pmtcty_RR0_iso x x0 =>
                match
                  tind₂o0 as tind₂o1
                  return
                    (Coq_Init_Datatypes_nat_pmtcty_RR0 (S x) tind₂o1 ->
                     S x0 = tind₂o1)
                with
                | 0%nat =>
                    fun tind_Ro1 : Coq_Init_Datatypes_nat_pmtcty_RR0 (S x) 0
                    => match tind_Ro1 return (S x0 = 0%nat) with
                       end
                | S o =>
                    fun _ : Coq_Init_Datatypes_nat_pmtcty_RR0 (S x) (S o) =>
                    fiat (S x0 = S o)
                end tind_Ro0) in
           Hexeq
       end tind₂o
          end tind_R tind_Ro)
.



Run TemplateProgram (genParamIndTotAll [] true "Coq.Init.Datatypes.nat").



(* functions wont work until we fully produce the goodness of inductives *)