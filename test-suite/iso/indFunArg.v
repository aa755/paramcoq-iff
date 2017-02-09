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

(* translation of this fails because of clashes due to unnabed binders
Inductive NatLike (A B:Set) (C: (A->B) -> Set): Set := 
| SS : forall (f:A->B), C f -> NatLike A B C.
*)

Print totalPiHalfGood (* has a universe: bad. use totalPiHalfGood2 instead*).



Inductive NatLike (A:Set) (C: forall aa:A, Set): Set := 
(* | SS : forall (f:A->B) (c:C f)  (d:forall a:A, NatLike A B C)
     (e:forall (fi:A->B) (ci:C fi), NatLike A B C), NatLike A B C *) 
 | SS2 :  forall (ao:A) (cao: C ao) 
 (*d:forall (a:A) (ca da: C a), NatLike A C*),
       NatLike A C.

Run TemplateProgram (genParamInd [] true true "Top.indFunArg.NatLike").
Require Import ReflParam.Trecord.



Arguments projT1 : clear implicits.
Arguments projT2 : clear implicits.

Run TemplateProgram (mkIndEnv "indTransEnv" [
"Top.indFunArg.NatLike" ]).


Definition xx :=
(fun (A A₂ : Set) (A_R : BestRel A A₂) (C : A -> Set) 
   (C₂ : A₂ -> Set)
   (C_R : forall (aa : A) (aa₂ : A₂),
          BestR A_R aa aa₂ ->
          (fun H H0 : Set => BestRel H H0) (C aa) (C₂ aa₂)) =>
 fix
 Top_indFunArg_NatLike_pmtcty_RR0_iso (tind : NatLike A C)
                                      (tind₂ tind₂o : NatLike A₂ C₂)
                                      (tind_R : Top_indFunArg_NatLike_pmtcty_RR0
                                                 A A₂ 
                                                 (BestR A_R) C C₂
                                                 (fun 
                                                 (aa : A) 
                                                 (aa₂ : A₂)
                                                 (aa_R : BestR A_R aa aa₂) =>
                                                 BestR (C_R aa aa₂ aa_R))
                                                 tind tind₂)
                                      (tind_Ro : Top_indFunArg_NatLike_pmtcty_RR0
                                                 A A₂ 
                                                 (BestR A_R) C C₂
                                                 (fun 
                                                 (aa : A) 
                                                 (aa₂ : A₂)
                                                 (aa_R : BestR A_R aa aa₂) =>
                                                 BestR (C_R aa aa₂ aa_R))
                                                 tind tind₂o) {struct tind} :
   tind₂ = tind₂o :=
   match
     tind as tind0
     return
       (Top_indFunArg_NatLike_pmtcty_RR0 A A₂ (BestR A_R) C C₂
          (fun (aa : A) (aa₂ : A₂) (aa_R : BestR A_R aa aa₂) =>
           BestR (C_R aa aa₂ aa_R)) tind0 tind₂ ->
        Top_indFunArg_NatLike_pmtcty_RR0 A A₂ (BestR A_R) C C₂
          (fun (aa : A) (aa₂ : A₂) (aa_R : BestR A_R aa aa₂) =>
           BestR (C_R aa aa₂ aa_R)) tind0 tind₂o -> 
        tind₂ = tind₂o)
   with
   | SS2 _ _ ao cao =>
       match
         tind₂ as tind₂0
         return
           (forall tind₂o0 : NatLike A₂ C₂,
            Top_indFunArg_NatLike_pmtcty_RR0 A A₂ 
              (BestR A_R) C C₂
              (fun (aa : A) (aa₂ : A₂) (aa_R : BestR A_R aa aa₂) =>
               BestR (C_R aa aa₂ aa_R)) (SS2 A C ao cao) tind₂0 ->
            Top_indFunArg_NatLike_pmtcty_RR0 A A₂ 
              (BestR A_R) C C₂
              (fun (aa : A) (aa₂ : A₂) (aa_R : BestR A_R aa aa₂) =>
               BestR (C_R aa aa₂ aa_R)) (SS2 A C ao cao) tind₂o0 ->
            tind₂0 = tind₂o0)
       with
       | SS2 _ _ ao₂ cao₂ =>
           fun (tind₂o0 : NatLike A₂ C₂)
             (tind_R0 : Top_indFunArg_NatLike_pmtcty_RR0 A A₂ 
                          (BestR A_R) C C₂
                          (fun (aa : A) (aa₂ : A₂) (aa_R : BestR A_R aa aa₂)
                           => BestR (C_R aa aa₂ aa_R)) 
                          (SS2 A C ao cao) (SS2 A₂ C₂ ao₂ cao₂))
             (tind_Ro0 : Top_indFunArg_NatLike_pmtcty_RR0 A A₂ 
                           (BestR A_R) C C₂
                           (fun (aa : A) (aa₂ : A₂) (aa_R : BestR A_R aa aa₂)
                            => BestR (C_R aa aa₂ aa_R)) 
                           (SS2 A C ao cao) tind₂o0) =>
           let Hexeq :=
             Top_indFunArg_NatLike_pmtcty_RR0_constr_0_inv A A₂ 
               (BestR A_R) C C₂
               (fun (aa : A) (aa₂ : A₂) (aa_R : BestR A_R aa aa₂) =>
                BestR (C_R aa aa₂ aa_R)) ao ao₂ cao cao₂ tind_R0
               (fun
                  _ : Top_indFunArg_NatLike_pmtcty_RR0 A A₂ 
                        (BestR A_R) C C₂
                        (fun (aa : A) (aa₂ : A₂) (aa_R : BestR A_R aa aa₂) =>
                         BestR (C_R aa aa₂ aa_R)) 
                        (SS2 A C ao cao) (SS2 A₂ C₂ ao₂ cao₂) =>
                SS2 A₂ C₂ ao₂ cao₂ = tind₂o0)
               (fun (ao_R : BestR A_R ao ao₂)
                  (cao_R : BestR (C_R ao ao₂ ao_R) cao cao₂) =>
                match
                  tind₂o0 as tind₂o1
                  return
                    (Top_indFunArg_NatLike_pmtcty_RR0 A A₂ 
                       (BestR A_R) C C₂
                       (fun (aa : A) (aa₂ : A₂) (aa_R : BestR A_R aa aa₂) =>
                        BestR (C_R aa aa₂ aa_R)) (SS2 A C ao cao) tind₂o1 ->
                     SS2 A₂ C₂ ao₂ cao₂ = tind₂o1)
                with
                | SS2 _ _ ao₂o cao₂o =>
                    fun
                      tind_Ro1 : Top_indFunArg_NatLike_pmtcty_RR0 A A₂
                                   (BestR A_R) C C₂
                                   (fun (aa : A) (aa₂ : A₂)
                                      (aa_R : BestR A_R aa aa₂) =>
                                    BestR (C_R aa aa₂ aa_R)) 
                                   (SS2 A C ao cao) 
                                   (SS2 A₂ C₂ ao₂o cao₂o) =>
                    Top_indFunArg_NatLike_pmtcty_RR0_constr_0_inv A A₂
                      (BestR A_R) C C₂
                      (fun (aa : A) (aa₂ : A₂) (aa_R : BestR A_R aa aa₂) =>
                       BestR (C_R aa aa₂ aa_R)) ao ao₂o cao cao₂o tind_Ro1
                      (fun
                         _ : Top_indFunArg_NatLike_pmtcty_RR0 A A₂
                               (BestR A_R) C C₂
                               (fun (aa : A) (aa₂ : A₂)
                                  (aa_R : BestR A_R aa aa₂) =>
                                BestR (C_R aa aa₂ aa_R)) 
                               (SS2 A C ao cao) (SS2 A₂ C₂ ao₂o cao₂o) =>
                       SS2 A₂ C₂ ao₂ cao₂ = SS2 A₂ C₂ ao₂o cao₂o)
                      (fun ao_Ro : BestR A_R ao ao₂o =>
                       match
                         BestOneijjo A_R ao ao₂ ao₂o ao_R ao_Ro in
                         (_ = ao₂o0)
                         return
                           (forall ao_Ro0 : BestR A_R ao ao₂o0,
                            BestR (C_R ao ao₂o0 ao_Ro0) cao cao₂o ->
                            SS2 A₂ C₂ ao₂ cao₂ = SS2 A₂ C₂ ao₂o0 cao₂o)
                       with
                       | eq_refl =>
                           fun ao_Ro0 : BestR A_R ao ao₂ =>
                           match
                             ProofIrrelevance.proof_irrelevance
                               (BestR A_R ao ao₂) ao_R ao_Ro0 in 
                             (_ = ao_Ro1)
                             return
                               (BestR (C_R ao ao₂ ao_Ro1) cao cao₂o ->
                                SS2 A₂ C₂ ao₂ cao₂ = SS2 A₂ C₂ ao₂ cao₂o)
                           with
                           | eq_refl =>
                               fun cao_Ro : BestR (C_R ao ao₂ ao_R) cao cao₂o
                               =>
                               match
                                 BestOneijjo (C_R ao ao₂ ao_R) cao cao₂ cao₂o
                                   cao_R cao_Ro in 
                                 (_ = cao₂o0)
                                 return
                                   (BestR (C_R ao ao₂ ao_R) cao cao₂o0 ->
                                    SS2 A₂ C₂ ao₂ cao₂ = SS2 A₂ C₂ ao₂ cao₂o0)
                               with
                               | eq_refl =>
                                   fun
                                     cao_Ro0 : BestR 
                                                 (C_R ao ao₂ ao_R) cao cao₂
                                   =>
                                   match
                                     ProofIrrelevance.proof_irrelevance
                                       (BestR (C_R ao ao₂ ao_R) cao cao₂)
                                       cao_R cao_Ro0
                                   with
                                   | eq_refl => eq_refl
                                   end
                               end cao_Ro
                           end
                       end ao_Ro)
                end tind_Ro0) in
           Hexeq
       end tind₂o
   end tind_R tind_Ro).



Set Printing Depth 10000.
Run TemplateProgram (genParamIndOne [false] [] true "Top.indFunArg.NatLike").

Run TemplateProgram (genParamIndOne [true] [] true "Top.indFunArg.NatLike").
(*
Run TemplateProgram (genParamIndTotAll [] true "Top.indFunArg.NatLike").
*)

Definition xx:=
(fun (A A₂ : Set) (A_R : BestRel A A₂) (C : A -> Set) 
   (C₂ : A₂ -> Set)
   (C_R : forall (aa : A) (aa₂ : A₂),
          BestR A_R aa aa₂ ->
          (fun H H0 : Set => BestRel H H0) (C aa) (C₂ aa₂)) =>
 fix
 Top_indFunArg_NatLike_pmtcty_RR0_iso (tind : NatLike A C)
                                      (tind₂ tind₂o : NatLike A₂ C₂)
                                      (tind_R : Top_indFunArg_NatLike_pmtcty_RR0
                                                 A A₂ 
                                                 (BestR A_R) C C₂
                                                 (fun 
                                                 (aa : A) 
                                                 (aa₂ : A₂)
                                                 (aa_R : BestR A_R aa aa₂) =>
                                                 BestR (C_R aa aa₂ aa_R))
                                                 tind tind₂)
                                      (tind_Ro : Top_indFunArg_NatLike_pmtcty_RR0
                                                 A A₂ 
                                                 (BestR A_R) C C₂
                                                 (fun 
                                                 (aa : A) 
                                                 (aa₂ : A₂)
                                                 (aa_R : BestR A_R aa aa₂) =>
                                                 BestR (C_R aa aa₂ aa_R))
                                                 tind tind₂o) {struct tind} :
   tind₂ = tind₂o :=
   match
     tind as tind0
     return
       (Top_indFunArg_NatLike_pmtcty_RR0 A A₂ (BestR A_R) C C₂
          (fun (aa : A) (aa₂ : A₂) (aa_R : BestR A_R aa aa₂) =>
           BestR (C_R aa aa₂ aa_R)) tind0 tind₂ ->
        Top_indFunArg_NatLike_pmtcty_RR0 A A₂ (BestR A_R) C C₂
          (fun (aa : A) (aa₂ : A₂) (aa_R : BestR A_R aa aa₂) =>
           BestR (C_R aa aa₂ aa_R)) tind0 tind₂o -> 
        tind₂ = tind₂o)
   with
   | SS2 _ _ ao cao d =>
       match
         tind₂ as tind₂0
         return
           (forall tind₂o0 : NatLike A₂ C₂,
            Top_indFunArg_NatLike_pmtcty_RR0 A A₂ 
              (BestR A_R) C C₂
              (fun (aa : A) (aa₂ : A₂) (aa_R : BestR A_R aa aa₂) =>
               BestR (C_R aa aa₂ aa_R)) (SS2 A C ao cao d) tind₂0 ->
            Top_indFunArg_NatLike_pmtcty_RR0 A A₂ 
              (BestR A_R) C C₂
              (fun (aa : A) (aa₂ : A₂) (aa_R : BestR A_R aa aa₂) =>
               BestR (C_R aa aa₂ aa_R)) (SS2 A C ao cao d) tind₂o0 ->
            tind₂0 = tind₂o0)
       with
       | SS2 _ _ ao₂ cao₂ d₂ =>
           fun (tind₂o0 : NatLike A₂ C₂)
             (tind_R0 : Top_indFunArg_NatLike_pmtcty_RR0 A A₂ 
                          (BestR A_R) C C₂
                          (fun (aa : A) (aa₂ : A₂) (aa_R : BestR A_R aa aa₂)
                           => BestR (C_R aa aa₂ aa_R)) 
                          (SS2 A C ao cao d) (SS2 A₂ C₂ ao₂ cao₂ d₂))
             (tind_Ro0 : Top_indFunArg_NatLike_pmtcty_RR0 A A₂ 
                           (BestR A_R) C C₂
                           (fun (aa : A) (aa₂ : A₂) (aa_R : BestR A_R aa aa₂)
                            => BestR (C_R aa aa₂ aa_R)) 
                           (SS2 A C ao cao d) tind₂o0) =>
           let Hexeq :=
             Top_indFunArg_NatLike_pmtcty_RR0_constr_0_inv A A₂ 
               (BestR A_R) C C₂
               (fun (aa : A) (aa₂ : A₂) (aa_R : BestR A_R aa aa₂) =>
                BestR (C_R aa aa₂ aa_R)) ao ao₂ cao cao₂ d d₂ tind_R0
               (fun
                  _ : Top_indFunArg_NatLike_pmtcty_RR0 A A₂ 
                        (BestR A_R) C C₂
                        (fun (aa : A) (aa₂ : A₂) (aa_R : BestR A_R aa aa₂) =>
                         BestR (C_R aa aa₂ aa_R)) 
                        (SS2 A C ao cao d) (SS2 A₂ C₂ ao₂ cao₂ d₂) =>
                SS2 A₂ C₂ ao₂ cao₂ d₂ = tind₂o0)
               (fun (ao_R : BestR A_R ao ao₂)
                  (cao_R : BestR (C_R ao ao₂ ao_R) cao cao₂)
                  (d_R : R_PiS
                           (fun (a : A) (a₂ : A₂) (a_R : BestR A_R a a₂) =>
                            R_PiS
                              (fun (ca : C a) (ca₂ : C₂ a₂)
                                 (_ : BestR (C_R a a₂ a_R) ca ca₂) =>
                               R_PiS
                                 (fun (da : C a) (da₂ : C₂ a₂)
                                    (_ : BestR (C_R a a₂ a_R) da da₂) =>
                                  Top_indFunArg_NatLike_pmtcty_RR0 A A₂
                                    (BestR A_R) C C₂
                                    (fun (aa : A) 
                                       (aa₂ : A₂) 
                                       (aa_R : BestR A_R aa aa₂) =>
                                     BestR (C_R aa aa₂ aa_R))))) d d₂) =>
                match
                  tind₂o0 as tind₂o1
                  return
                    (Top_indFunArg_NatLike_pmtcty_RR0 A A₂ 
                       (BestR A_R) C C₂
                       (fun (aa : A) (aa₂ : A₂) (aa_R : BestR A_R aa aa₂) =>
                        BestR (C_R aa aa₂ aa_R)) (SS2 A C ao cao d) tind₂o1 ->
                     SS2 A₂ C₂ ao₂ cao₂ d₂ = tind₂o1)
                with
                | SS2 _ _ ao₂o cao₂o d₂o =>
                    fun
                      tind_Ro1 : Top_indFunArg_NatLike_pmtcty_RR0 A A₂
                                   (BestR A_R) C C₂
                                   (fun (aa : A) (aa₂ : A₂)
                                      (aa_R : BestR A_R aa aa₂) =>
                                    BestR (C_R aa aa₂ aa_R))
                                   (SS2 A C ao cao d)
                                   (SS2 A₂ C₂ ao₂o cao₂o d₂o) =>
                    Top_indFunArg_NatLike_pmtcty_RR0_constr_0_inv A A₂
                      (BestR A_R) C C₂
                      (fun (aa : A) (aa₂ : A₂) (aa_R : BestR A_R aa aa₂) =>
                       BestR (C_R aa aa₂ aa_R)) ao ao₂o cao cao₂o d d₂o
                      tind_Ro1
                      (fun
                         _ : Top_indFunArg_NatLike_pmtcty_RR0 A A₂
                               (BestR A_R) C C₂
                               (fun (aa : A) (aa₂ : A₂)
                                  (aa_R : BestR A_R aa aa₂) =>
                                BestR (C_R aa aa₂ aa_R)) 
                               (SS2 A C ao cao d) 
                               (SS2 A₂ C₂ ao₂o cao₂o d₂o) =>
                       SS2 A₂ C₂ ao₂ cao₂ d₂ = SS2 A₂ C₂ ao₂o cao₂o d₂o)
                      (fun ao_Ro : BestR A_R ao ao₂o =>
                       match
                         BestOneijjo A_R ao ao₂ ao₂o ao_R ao_Ro in
                         (_ = ao₂o0)
                         return
                           (forall ao_Ro0 : BestR A_R ao ao₂o0,
                            BestR (C_R ao ao₂o0 ao_Ro0) cao cao₂o ->
                            R_PiS
                              (fun (a : A) (a₂ : A₂) (a_R : BestR A_R a a₂)
                               =>
                               R_PiS
                                 (fun (ca : C a) (ca₂ : C₂ a₂)
                                    (_ : BestR (C_R a a₂ a_R) ca ca₂) =>
                                  R_PiS
                                    (fun (da : C a) 
                                       (da₂ : C₂ a₂)
                                       (_ : BestR (C_R a a₂ a_R) da da₂) =>
                                     Top_indFunArg_NatLike_pmtcty_RR0 A A₂
                                       (BestR A_R) C C₂
                                       (fun (aa : A) 
                                          (aa₂ : A₂)
                                          (aa_R : BestR A_R aa aa₂) =>
                                        BestR (C_R aa aa₂ aa_R))))) d d₂o ->
                            SS2 A₂ C₂ ao₂ cao₂ d₂ = SS2 A₂ C₂ ao₂o0 cao₂o d₂o)
                       with
                       | eq_refl =>
                           fun ao_Ro0 : BestR A_R ao ao₂ =>
                           match
                             ProofIrrelevance.proof_irrelevance
                               (BestR A_R ao ao₂) ao_R ao_Ro0 in 
                             (_ = ao_Ro1)
                             return
                               (BestR (C_R ao ao₂ ao_Ro1) cao cao₂o ->
                                R_PiS
                                  (fun (a : A) (a₂ : A₂)
                                     (a_R : BestR A_R a a₂) =>
                                   R_PiS
                                     (fun (ca : C a) 
                                        (ca₂ : C₂ a₂)
                                        (_ : BestR (C_R a a₂ a_R) ca ca₂) =>
                                      R_PiS
                                        (fun (da : C a) 
                                           (da₂ : C₂ a₂)
                                           (_ : BestR (C_R a a₂ a_R) da da₂)
                                         =>
                                         Top_indFunArg_NatLike_pmtcty_RR0 A
                                           A₂ (BestR A_R) C C₂
                                           (fun (aa : A) 
                                              (aa₂ : A₂) 
                                              (aa_R : ...) => 
                                            BestR (...))))) d d₂o ->
                                SS2 A₂ C₂ ao₂ cao₂ d₂ =
                                SS2 A₂ C₂ ao₂ cao₂o d₂o)
                           with
                           | eq_refl =>
                               fun cao_Ro : BestR (C_R ao ao₂ ao_R) cao cao₂o
                               =>
                               match
                                 BestOneijjo (C_R ao ao₂ ao_R) cao cao₂ cao₂o
                                   cao_R cao_Ro in 
                                 (_ = cao₂o0)
                                 return
                                   (BestR (C_R ao ao₂ ao_R) cao cao₂o0 ->
                                    R_PiS
                                      (fun (a : A) 
                                         (a₂ : A₂) 
                                         (a_R : BestR A_R a a₂) =>
                                       R_PiS
                                         (fun (ca : C a) 
                                            (ca₂ : C₂ a₂)
                                            (_ : BestR (...) ca ca₂) =>
                                          R_PiS
                                            (fun ... ... ... =>
                                             Top_indFunArg_NatLike_pmtcty_RR0
                                               A A₂ ... C C₂ ...))) d d₂o ->
                                    SS2 A₂ C₂ ao₂ cao₂ d₂ =
                                    SS2 A₂ C₂ ao₂ cao₂o0 d₂o)
                               with
                               | eq_refl =>
                                   fun
                                     cao_Ro0 : BestR 
                                                 (C_R ao ao₂ ao_R) cao cao₂
                                   =>
                                   match
                                     ProofIrrelevance.proof_irrelevance
                                       (BestR (C_R ao ao₂ ao_R) cao cao₂)
                                       cao_R cao_Ro0
                                   with
                                   | eq_refl =>
                                       fun
                                         d_Ro : R_PiS
                                                 (fun 
                                                 (a : A) 
                                                 (a₂ : A₂)
                                                 (a_R : BestR A_R a a₂) =>
                                                 R_PiS
                                                 (fun 
                                                 (ca : C a) 
                                                 (ca₂ : C₂ a₂)
                                                 (_ : BestR ... ca ca₂) =>
                                                 R_PiS (... => ...))) d d₂o
                                       =>
                                       match
                                         onePiHalfGood A A₂ A_R
                                           (fun a : A =>
                                            C a -> C a -> NatLike A C)
                                           (fun a₂ : A₂ =>
                                            C₂ a₂ -> C₂ a₂ -> NatLike A₂ C₂)
                                           (fun (a : A) 
                                              (a₂ : A₂)
                                              (a_R : BestR A_R a a₂) =>
                                            R_PiS (... => ...))
                                           (fun (a : A) 
                                              (a₂ : A₂)
                                              (a_R : BestR A_R a a₂) =>
                                            onePiHalfGood 
                                              (C a) 
                                              (C₂ a₂) 
                                              (C_R a a₂ a_R) 
                                              (... => ...) 
                                              (... => ...) 
                                              (... => ...) 
                                              (... => ...)) d d₂ d₂o d_R d_Ro
                                         in (_ = d₂o0)
                                         return
                                           (R_PiS
                                              (fun ... ... ... => R_PiS ...)
                                              d d₂o0 ->
                                            SS2 A₂ C₂ ao₂ cao₂ d₂ =
                                            SS2 A₂ C₂ ao₂ cao₂ d₂o0)
                                       with
                                       | eq_refl =>
                                           fun
                                             d_Ro0 : 
                                              R_PiS
                                                (fun 
                                                 (a : A) 
                                                 (a₂ : A₂) 
                                                 (a_R : ...) => 
                                                 R_PiS (...)) d d₂ =>
                                           match
                                             ProofIrrelevance.proof_irrelevance
                                               (R_PiS ... d d₂) d_R d_Ro0
                                           with
                                           | eq_refl => eq_refl
                                           end
                                       end d_Ro
                                   end
                               end cao_Ro
                           end
                       end ao_Ro)
                end tind_Ro0) in
           Hexeq
       end tind₂o
   end tind_R tind_Ro)



(*
Run TemplateProgram (genWrappers indTransEnv). (* enable when CRRInvs are generated *)
*)