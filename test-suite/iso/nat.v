
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
   @eq nat tind₂ tind₂o :=
   match
     tind as tind0
     return
       (forall (_ : Coq_Init_Datatypes_nat_pmtcty_RR0 tind0 tind₂)
          (_ : Coq_Init_Datatypes_nat_pmtcty_RR0 tind0 tind₂o),
        @eq nat tind₂ tind₂o)
   with
   | O =>
       match
         tind₂ as tind₂0
         return
           (forall (tind₂o0 : nat)
              (_ : Coq_Init_Datatypes_nat_pmtcty_RR0 O tind₂0)
              (_ : Coq_Init_Datatypes_nat_pmtcty_RR0 O tind₂o0),
            @eq nat tind₂0 tind₂o0)
       with
       | O =>
           fun (tind₂o0 : nat)
             (tind_R0 : Coq_Init_Datatypes_nat_pmtcty_RR0 O O)
             (tind_Ro0 : Coq_Init_Datatypes_nat_pmtcty_RR0 O tind₂o0) =>
           let Hexeq :=
             Coq_Init_Datatypes_nat_pmtcty_RR0_constr_0_inv tind_R0
               (fun _ : Coq_Init_Datatypes_nat_pmtcty_RR0 O O =>
                @eq nat O tind₂o0)
               (match
                  tind₂o0 as tind₂o1
                  return
                    (forall _ : Coq_Init_Datatypes_nat_pmtcty_RR0 O tind₂o1,
                     @eq nat O tind₂o1)
                with
                | O =>
                    fun tind_Ro1 : Coq_Init_Datatypes_nat_pmtcty_RR0 O O =>
                    Coq_Init_Datatypes_nat_pmtcty_RR0_constr_0_inv tind_Ro1
                      (fun _ : Coq_Init_Datatypes_nat_pmtcty_RR0 O O =>
                       @eq nat O O) (@eq_refl nat O)
                | S o =>
                    fun tind_Ro1 : Coq_Init_Datatypes_nat_pmtcty_RR0 O (S o)
                    => match tind_Ro1 return (@eq nat O (S o)) with
                       end
                end tind_Ro0) in
           Hexeq
       | S x =>
           fun (tind₂o0 : nat)
             (tind_R0 : Coq_Init_Datatypes_nat_pmtcty_RR0 O (S x))
             (_ : Coq_Init_Datatypes_nat_pmtcty_RR0 O tind₂o0) =>
           match tind_R0 return (@eq nat (S x) tind₂o0) with
           end
       end tind₂o
   | S x =>
       match
         tind₂ as tind₂0
         return
           (forall (tind₂o0 : nat)
              (_ : Coq_Init_Datatypes_nat_pmtcty_RR0 (S x) tind₂0)
              (_ : Coq_Init_Datatypes_nat_pmtcty_RR0 (S x) tind₂o0),
            @eq nat tind₂0 tind₂o0)
       with
       | O =>
           fun (tind₂o0 : nat)
             (tind_R0 : Coq_Init_Datatypes_nat_pmtcty_RR0 (S x) O)
             (_ : Coq_Init_Datatypes_nat_pmtcty_RR0 (S x) tind₂o0) =>
           match tind_R0 return (@eq nat O tind₂o0) with
           end
       | S x0 =>
           fun (tind₂o0 : nat)
             (tind_R0 : Coq_Init_Datatypes_nat_pmtcty_RR0 (S x) (S x0))
             (tind_Ro0 : Coq_Init_Datatypes_nat_pmtcty_RR0 (S x) tind₂o0) =>
           let Hexeq :=
             Coq_Init_Datatypes_nat_pmtcty_RR0_constr_1_inv x x0 tind_R0
               (fun _ : Coq_Init_Datatypes_nat_pmtcty_RR0 (S x) (S x0) =>
                @eq nat (S x0) tind₂o0)
               (fun H : Coq_Init_Datatypes_nat_pmtcty_RR0 x x0 =>
                match
                  tind₂o0 as tind₂o1
                  return
                    (forall
                       _ : Coq_Init_Datatypes_nat_pmtcty_RR0 (S x) tind₂o1,
                     @eq nat (S x0) tind₂o1)
                with
                | O =>
                    fun tind_Ro1 : Coq_Init_Datatypes_nat_pmtcty_RR0 (S x) O
                    => match tind_Ro1 return (@eq nat (S x0) O) with
                       end
                | S o =>
                    fun
                      tind_Ro1 : Coq_Init_Datatypes_nat_pmtcty_RR0 
                                   (S x) (S o) =>
                    Coq_Init_Datatypes_nat_pmtcty_RR0_constr_1_inv x o
                      tind_Ro1
                      (fun _ : Coq_Init_Datatypes_nat_pmtcty_RR0 (S x) (S o)
                       => @eq nat (S x0) (S o))
                      (fun o0 : Coq_Init_Datatypes_nat_pmtcty_RR0 x o =>
                       match
                         Coq_Init_Datatypes_nat_pmtcty_RR0_iso x x0 o H o0 in
                         (eq _ o1)
                         return
                           (forall _ : Coq_Init_Datatypes_nat_pmtcty_RR0 x o1,
                            @eq nat (S x0) (S o1))
                       with
                       | eq_refl =>
                           fun o1 : Coq_Init_Datatypes_nat_pmtcty_RR0 x x0 =>
                           match
                             ProofIrrelevance.proof_irrelevance
                               (Coq_Init_Datatypes_nat_pmtcty_RR0 x x0) H o1
                             in (eq _ o2) return (@eq nat (S x0) (S x0))
                           with
                           | eq_refl => @eq_refl nat (S x0)
                           end
                       end o0)
                end tind_Ro0) in
           Hexeq
       end tind₂o
   end tind_R tind_Ro).


(*

Definition xxr:=
(fix
 Coq_Init_Datatypes_nat_pmtcty_RR0_iso (tind₂ tind tindo : nat)
                                       (tind_R : Coq_Init_Datatypes_nat_pmtcty_RR0
                                                 tind tind₂)
                                       (tind_Ro : 
                                        Coq_Init_Datatypes_nat_pmtcty_RR0
                                          tindo tind₂) {struct tind₂} :
   @eq nat tind tindo :=
   match
     tind₂ as tind₂0
     return
       (forall (_ : Coq_Init_Datatypes_nat_pmtcty_RR0 tind tind₂0)
          (_ : Coq_Init_Datatypes_nat_pmtcty_RR0 tindo tind₂0),
        @eq nat tind tindo)
   with
   | O =>
       match
         tind as tind0
         return
           (forall (tindo0 : nat)
              (_ : Coq_Init_Datatypes_nat_pmtcty_RR0 tind0 O)
              (_ : Coq_Init_Datatypes_nat_pmtcty_RR0 tindo0 O),
            @eq nat tind0 tindo0)
       with
       | O =>
           fun (tindo0 : nat)
             (tind_R0 : Coq_Init_Datatypes_nat_pmtcty_RR0 O O)
             (tind_Ro0 : Coq_Init_Datatypes_nat_pmtcty_RR0 tindo0 O) =>
           let Hexeq :=
             Coq_Init_Datatypes_nat_pmtcty_RR0_constr_0_inv tind_R0
               (fun _ : Coq_Init_Datatypes_nat_pmtcty_RR0 O O =>
                @eq nat O tindo0)
               (match
                  tindo0 as tindo1
                  return
                    (forall _ : Coq_Init_Datatypes_nat_pmtcty_RR0 tindo1 O,
                     @eq nat O tindo1)
                with
                | O =>
                    fun tind_Ro1 : Coq_Init_Datatypes_nat_pmtcty_RR0 O O =>
                    Coq_Init_Datatypes_nat_pmtcty_RR0_constr_0_inv tind_Ro1
                      (fun _ : Coq_Init_Datatypes_nat_pmtcty_RR0 O O =>
                       @eq nat O O) (@eq_refl nat O)
                | S o =>
                    fun tind_Ro1 : Coq_Init_Datatypes_nat_pmtcty_RR0 (S o) O
                    => match tind_Ro1 return (@eq nat O (S o)) with
                       end
                end tind_Ro0) in
           Hexeq
       | S x =>
           fun (tindo0 : nat)
             (tind_R0 : Coq_Init_Datatypes_nat_pmtcty_RR0 (S x) O)
             (_ : Coq_Init_Datatypes_nat_pmtcty_RR0 tindo0 O) =>
           match tind_R0 return (@eq nat (S x) tindo0) with
           end
       end tindo
   | S x =>
       match
         tind as tind0
         return
           (forall (tindo0 : nat)
              (_ : Coq_Init_Datatypes_nat_pmtcty_RR0 tind0 (S x))
              (_ : Coq_Init_Datatypes_nat_pmtcty_RR0 tindo0 (S x)),
            @eq nat tind0 tindo0)
       with
       | O =>
           fun (tindo0 : nat)
             (tind_R0 : Coq_Init_Datatypes_nat_pmtcty_RR0 O (S x))
             (_ : Coq_Init_Datatypes_nat_pmtcty_RR0 tindo0 (S x)) =>
           match tind_R0 return (@eq nat O tindo0) with
           end
       | S x0 =>
           fun (tindo0 : nat)
             (tind_R0 : Coq_Init_Datatypes_nat_pmtcty_RR0 (S x0) (S x))
             (tind_Ro0 : Coq_Init_Datatypes_nat_pmtcty_RR0 tindo0 (S x)) =>
           let Hexeq :=
             Coq_Init_Datatypes_nat_pmtcty_RR0_constr_1_inv x0 x tind_R0
               (fun _ : Coq_Init_Datatypes_nat_pmtcty_RR0 (S x0) (S x) =>
                @eq nat (S x0) tindo0)
               (fun H : Coq_Init_Datatypes_nat_pmtcty_RR0 x0 x =>
                match
                  tindo0 as tindo1
                  return
                    (forall
                       _ : Coq_Init_Datatypes_nat_pmtcty_RR0 tindo1 (S x),
                     @eq nat (S x0) tindo1)
                with
                | O =>
                    fun tind_Ro1 : Coq_Init_Datatypes_nat_pmtcty_RR0 O (S x)
                    => match tind_Ro1 return (@eq nat (S x0) O) with
                       end
                | S o =>
                    fun
                      tind_Ro1 : Coq_Init_Datatypes_nat_pmtcty_RR0 
                                   (S o) (S x) =>
                    Coq_Init_Datatypes_nat_pmtcty_RR0_constr_1_inv o x
                      tind_Ro1
                      (fun _ : Coq_Init_Datatypes_nat_pmtcty_RR0 (S o) (S x)
                       => @eq nat (S x0) (S o))
                      (fun o0 : Coq_Init_Datatypes_nat_pmtcty_RR0 o x =>
                       match
                         Coq_Init_Datatypes_nat_pmtcty_RR0_iso x0 x0 o H o0
                         in (eq _ o1)
                         return
                           (forall _ : Coq_Init_Datatypes_nat_pmtcty_RR0 o1 x,
                            @eq nat (S x0) (S o1))
                       with
                       | eq_refl =>
                           fun o1 : Coq_Init_Datatypes_nat_pmtcty_RR0 x0 x =>
                           match
                             ProofIrrelevance.proof_irrelevance
                               (Coq_Init_Datatypes_nat_pmtcty_RR0 x0 x) H o1
                             in (eq _ o2) return (@eq nat (S x0) (S x0))
                           with
                           | eq_refl => @eq_refl nat (S x0)
                           end
                       end o0)
                end tind_Ro0) in
           Hexeq
       end tindo
   end tind_R tind_Ro).
*)   
Set Printing All.
Run TemplateProgram (genParamIndOne [false] [] true "Coq.Init.Datatypes.nat").
(* success! *)

Run TemplateProgram (genParamIndOne [true] [] true "Coq.Init.Datatypes.nat").

Run TemplateProgram (genParamIndTotAll [] true "Coq.Init.Datatypes.nat").



(* functions wont work until we fully produce the goodness of inductives *)