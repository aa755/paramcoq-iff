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
 (d:forall (a:A) (ca da: C a), NatLike A C),
       NatLike A C.

Run TemplateProgram (genParamInd [] true true "Top.indFunArg.NatLike").
Require Import ReflParam.Trecord.



Arguments projT1 : clear implicits.
Arguments projT2 : clear implicits.

Run TemplateProgram (mkIndEnv "indTransEnv" [
"Top.indFunArg.NatLike" ]).

Run TemplateProgram (genWrappers indTransEnv). (* success *)

Definition xx :=
(fix
 Top_indFunArg_NatLike_pmtcty_RR0_iso (A A₂ : Set) 
                                      (A_R : BestRel A A₂) 
                                      (C : A -> Set) 
                                      (C₂ : A₂ -> Set)
                                      (C_R : forall (aa : A) (aa₂ : A₂),
                                             BestR A_R aa aa₂ ->
                                             (fun H H0 : Set => BestRel H H0)
                                               (C aa) 
                                               (C₂ aa₂))
                                      (tind₂ : NatLike A₂ C₂) {struct tind₂} :
   {tind : NatLike A C &
   Top_indFunArg_NatLike_pmtcty_RR0 A A₂ (BestR A_R) C C₂
     (fun (aa : A) (aa₂ : A₂) (aa_R : BestR A_R aa aa₂) =>
      BestR (C_R aa aa₂ aa_R)) tind tind₂} :=
   match
     tind₂ as tind₂0
     return
       {tind : NatLike A C &
       Top_indFunArg_NatLike_pmtcty_RR0 A A₂ (BestR A_R) C C₂
         (fun (aa : A) (aa₂ : A₂) (aa_R : BestR A_R aa aa₂) =>
          BestR (C_R aa aa₂ aa_R)) tind tind₂0}
   with
   | SS2 _ _ ao₂ cao₂ d₂ =>
       let ao := BestTot21 A_R ao₂ in
       let ao_R := BestTot21R A_R ao₂ in
       let cao := BestTot21 (C_R ao ao₂ ao_R) cao₂ in
       let cao_R := BestTot21R (C_R ao ao₂ ao_R) cao₂ in
       let d_R :=
         totalPiHalfGood21 A A₂ A_R (fun a : A => C a -> C a -> NatLike A C)
           (fun a₂ : A₂ => C₂ a₂ -> C₂ a₂ -> NatLike A₂ C₂)
           (fun (a : A) (a₂ : A₂) (a_R : BestR A_R a a₂) =>
            R_PiS
              (fun (ca : C a) (ca₂ : C₂ a₂) (_ : BestR (C_R a a₂ a_R) ca ca₂)
               =>
               R_PiS
                 (fun (da : C a) (da₂ : C₂ a₂)
                    (_ : BestR (C_R a a₂ a_R) da da₂) =>
                  Top_indFunArg_NatLike_pmtcty_RR0 A A₂ 
                    (BestR A_R) C C₂
                    (fun (aa : A) (aa₂ : A₂) (aa_R : BestR A_R aa aa₂) =>
                     BestR (C_R aa aa₂ aa_R)))))
           (fun (a : A) (a₂ : A₂) (a_R : BestR A_R a a₂) =>
            totalPiHalfGood21 (C a) (C₂ a₂) (C_R a a₂ a_R)
              (fun _ : C a => C a -> NatLike A C)
              (fun _ : C₂ a₂ => C₂ a₂ -> NatLike A₂ C₂)
              (fun (ca : C a) (ca₂ : C₂ a₂) (_ : BestR (C_R a a₂ a_R) ca ca₂)
               =>
               R_PiS
                 (fun (da : C a) (da₂ : C₂ a₂)
                    (_ : BestR (C_R a a₂ a_R) da da₂) =>
                  Top_indFunArg_NatLike_pmtcty_RR0 A A₂ 
                    (BestR A_R) C C₂
                    (fun (aa : A) (aa₂ : A₂) (aa_R : BestR A_R aa aa₂) =>
                     BestR (C_R aa aa₂ aa_R))))
              (fun (ca : C a) (ca₂ : C₂ a₂) (_ : BestR (C_R a a₂ a_R) ca ca₂)
               =>
               totalPiHalfGood21 (C a) (C₂ a₂) (C_R a a₂ a_R)
                 (fun _ : C a => NatLike A C)
                 (fun _ : C₂ a₂ => NatLike A₂ C₂)
                 (fun (da : C a) (da₂ : C₂ a₂)
                    (_ : BestR (C_R a a₂ a_R) da da₂) =>
                  Top_indFunArg_NatLike_pmtcty_RR0 A A₂ 
                    (BestR A_R) C C₂
                    (fun (aa : A) (aa₂ : A₂) (aa_R : BestR A_R aa aa₂) =>
                     BestR (C_R aa aa₂ aa_R)))
                 (fun (da : C a) (da₂ : C₂ a₂)
                    (_ : BestR (C_R a a₂ a_R) da da₂) =>
                  Top_indFunArg_NatLike_pmtcty_RR0_iso A A₂ A_R C C₂ C_R)))
           d₂ in
       let d :=
         projT1 (forall a : A, C a -> C a -> NatLike A C)
           (fun d : forall a : A, C a -> C a -> NatLike A C =>
            R_PiS
              (fun (a : A) (a₂ : A₂) (a_R : BestR A_R a a₂) =>
               R_PiS
                 (fun (ca : C a) (ca₂ : C₂ a₂)
                    (_ : BestR (C_R a a₂ a_R) ca ca₂) =>
                  R_PiS
                    (fun (da : C a) (da₂ : C₂ a₂)
                       (_ : BestR (C_R a a₂ a_R) da da₂) =>
                     Top_indFunArg_NatLike_pmtcty_RR0 A A₂ 
                       (BestR A_R) C C₂
                       (fun (aa : A) (aa₂ : A₂) (aa_R : BestR A_R aa aa₂) =>
                        BestR (C_R aa aa₂ aa_R))))) d d₂) d_R in
       let d_R0 :=
         projT2 (forall a : A, C a -> C a -> NatLike A C)
           (fun d0 : forall a : A, C a -> C a -> NatLike A C =>
            R_PiS
              (fun (a : A) (a₂ : A₂) (a_R : BestR A_R a a₂) =>
               R_PiS
                 (fun (ca : C a) (ca₂ : C₂ a₂)
                    (_ : BestR (C_R a a₂ a_R) ca ca₂) =>
                  R_PiS
                    (fun (da : C a) (da₂ : C₂ a₂)
                       (_ : BestR (C_R a a₂ a_R) da da₂) =>
                     Top_indFunArg_NatLike_pmtcty_RR0 A A₂ 
                       (BestR A_R) C C₂
                       (fun (aa : A) (aa₂ : A₂) (aa_R : BestR A_R aa aa₂) =>
                        BestR (C_R aa aa₂ aa_R))))) d0 d₂) d_R in
       existT
         (fun tind : NatLike A C =>
          Top_indFunArg_NatLike_pmtcty_RR0 A A₂ (BestR A_R) C C₂
            (fun (aa : A) (aa₂ : A₂) (aa_R : BestR A_R aa aa₂) =>
             BestR (C_R aa aa₂ aa_R)) tind (SS2 A₂ C₂ ao₂ cao₂ d₂))
         (SS2 A C ao cao d)
         (Top_indFunArg_NatLike_pmtcty_RR0_constr_0_tot A A₂ 
            (BestR A_R) C C₂
            (fun (aa : A) (aa₂ : A₂) (aa_R : BestR A_R aa aa₂) =>
             BestR (C_R aa aa₂ aa_R)) ao ao₂ ao_R cao cao₂ cao_R d d₂ d_R0)
   end).
   
Run TemplateProgram (genParamIndTot false [] false true "Top.indFunArg.NatLike").

