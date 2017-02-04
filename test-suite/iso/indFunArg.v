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
 (d:forall (a:A) (ca: C a), NatLike A C),
       NatLike A C.

Run TemplateProgram (genParamInd [] true true "Top.indFunArg.NatLike").
Require Import ReflParam.Trecord.

Definition xxx :=
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
                                      (H : NatLike A C) {struct H} :
   {H0 : NatLike A₂ C₂ &
   Top_indFunArg_NatLike_pmtcty_RR0 A A₂ (BestR A_R) C C₂
     (fun (aa : A) (aa₂ : A₂) (aa_R : BestR A_R aa aa₂) =>
      BestR (C_R aa aa₂ aa_R)) H H0} :=
   match
     H as H0
     return
       {H1 : NatLike A₂ C₂ &
       Top_indFunArg_NatLike_pmtcty_RR0 A A₂ (BestR A_R) C C₂
         (fun (aa : A) (aa₂ : A₂) (aa_R : BestR A_R aa aa₂) =>
          BestR (C_R aa aa₂ aa_R)) H0 H1}
   with
   | SS2 _ _ ao cao d =>
       let ao₂ := BestTot12 A_R ao in
       let ao_R := BestTot12R A_R ao in
       let cao₂ := BestTot12 (C_R ao ao₂ ao_R) cao in
       let cao_R := BestTot12R (C_R ao ao₂ ao_R) cao in
       let d_R :=
         totalPiHalfGood A A₂ A_R (fun a : A => C a -> NatLike A C)
           (fun a₂ : A₂ => C₂ a₂ -> NatLike A₂ C₂)
           (fun (a : A) (a₂ : A₂) (a_R : BestR A_R a a₂) =>
            R_PiS
              (fun (ca : C a) (ca₂ : C₂ a₂) (_ : BestR (C_R a a₂ a_R) ca ca₂)
               =>
               Top_indFunArg_NatLike_pmtcty_RR0 A A₂ 
                 (BestR A_R) C C₂
                 (fun (aa : A) (aa₂ : A₂) (aa_R : BestR A_R aa aa₂) =>
                  BestR (C_R aa aa₂ aa_R))))
           (fun (a : A) (a₂ : A₂) (a_R : BestR A_R a a₂) =>
            totalPiHalfGood (C a) (C₂ a₂) (C_R a a₂ a_R)
              (fun _ : C a => NatLike A C) (fun _ : C₂ a₂ => NatLike A₂ C₂)
              (fun (ca : C a) (ca₂ : C₂ a₂) (_ : BestR (C_R a a₂ a_R) ca ca₂)
               =>
               Top_indFunArg_NatLike_pmtcty_RR0 A A₂ 
                 (BestR A_R) C C₂
                 (fun (aa : A) (aa₂ : A₂) (aa_R : BestR A_R aa aa₂) =>
                  BestR (C_R aa aa₂ aa_R)))
              (fun (ca : C a) (ca₂ : C₂ a₂) (_ : BestR (C_R a a₂ a_R) ca ca₂)
               => Top_indFunArg_NatLike_pmtcty_RR0_iso A A₂ A_R C C₂ C_R)) d
         in
       let d₂ := projT1 d_R in
       let d_R := projT2 d_R in
       existT
         (fun H0 : NatLike A₂ C₂ =>
          Top_indFunArg_NatLike_pmtcty_RR0 A A₂ (BestR A_R) C C₂
            (fun (aa : A) (aa₂ : A₂) (aa_R : BestR A_R aa aa₂) =>
             BestR (C_R aa aa₂ aa_R)) (SS2 A C ao cao d) H0)
         (SS2 A₂ C₂ ao₂ cao₂ d₂)
         (Top_indFunArg_NatLike_pmtcty_RR0_constr_0 A A₂ 
            (BestR A_R) C C₂
            (fun (aa : A) (aa₂ : A₂) (aa_R : BestR A_R aa aa₂) =>
             BestR (C_R aa aa₂ aa_R)) ao ao₂ ao_R cao cao₂ cao_R d d₂ d_R)
   end)
.

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
                                      (H : NatLike A C) {struct H} :
   {H0 : NatLike A₂ C₂ &
   Top_indFunArg_NatLike_pmtcty_RR0 A A₂ (BestR A_R) C C₂
     (fun (aa : A) (aa₂ : A₂) (aa_R : BestR A_R aa aa₂) =>
      BestR (C_R aa aa₂ aa_R)) H H0} :=
   match
     H as H0
     return
       {H1 : NatLike A₂ C₂ &
       Top_indFunArg_NatLike_pmtcty_RR0 A A₂ (BestR A_R) C C₂
         (fun (aa : A) (aa₂ : A₂) (aa_R : BestR A_R aa aa₂) =>
          BestR (C_R aa aa₂ aa_R)) H0 H1}
   with
   | SS2 _ _ ao cao d =>
       let ao₂ := BestTot12 A_R ao in
       let ao_R := BestTot12R A_R ao in
       let cao₂ := BestTot12 (C_R ao ao₂ ao_R) cao in
       let cao_R := BestTot12R (C_R ao ao₂ ao_R) cao in
       let d_R :=
         totalPiHalfGood A A₂ A_R (fun a : A => C a -> NatLike A C)
           (fun a₂ : A₂ => C₂ a₂ -> NatLike A₂ C₂)
           (fun (a : A) (a₂ : A₂) (a_R : BestR A_R a a₂) =>
            R_PiS
              (fun (ca : C a) (ca₂ : C₂ a₂) (_ : BestR (C_R a a₂ a_R) ca ca₂)
               =>
               Top_indFunArg_NatLike_pmtcty_RR0 A A₂ 
                 (BestR A_R) C C₂
                 (fun (aa : A) (aa₂ : A₂) (aa_R : BestR A_R aa aa₂) =>
                  BestR (C_R aa aa₂ aa_R))))
           (fun (a : A) (a₂ : A₂) (a_R : BestR A_R a a₂) =>
            totalPiHalfGood (C a) (C₂ a₂) (C_R a a₂ a_R)
              (fun _ : C a => NatLike A C) (fun _ : C₂ a₂ => NatLike A₂ C₂)
              (fun (ca : C a) (ca₂ : C₂ a₂) (_ : BestR (C_R a a₂ a_R) ca ca₂)
               =>
               Top_indFunArg_NatLike_pmtcty_RR0 A A₂ 
                 (BestR A_R) C C₂
                 (fun (aa : A) (aa₂ : A₂) (aa_R : BestR A_R aa aa₂) =>
                  BestR (C_R aa aa₂ aa_R)))
              (fun (ca : C a) (ca₂ : C₂ a₂) (_ : BestR (C_R a a₂ a_R) ca ca₂)
               => Top_indFunArg_NatLike_pmtcty_RR0_iso A A₂ A_R C C₂ C_R)) d
         in
       let d₂ :=
         projT1 (forall a₂ : A₂, C₂ a₂ -> NatLike A₂ C₂)
           (fun d₂ : forall a₂ : A₂, C₂ a₂ -> NatLike A₂ C₂ =>
            R_PiS
              (fun (a : A) (a₂ : A₂) (a_R : BestR A_R a a₂) =>
               R_PiS
                 (fun (ca : C a) (ca₂ : C₂ a₂)
                    (_ : BestR (C_R a a₂ a_R) ca ca₂) =>
                  Top_indFunArg_NatLike_pmtcty_RR0 A A₂ 
                    (BestR A_R) C C₂
                    (fun (aa : A) (aa₂ : A₂) (aa_R : BestR A_R aa aa₂) =>
                     BestR (C_R aa aa₂ aa_R)))) d d₂) d_R in
       let d_R0 :=
         projT2 (forall a₂ : A₂, C₂ a₂ -> NatLike A₂ C₂)
           (fun d₂0 : forall a₂ : A₂, C₂ a₂ -> NatLike A₂ C₂ =>
            R_PiS
              (fun (a : A) (a₂ : A₂) (a_R : BestR A_R a a₂) =>
               R_PiS
                 (fun (ca : C a) (ca₂ : C₂ a₂)
                    (_ : BestR (C_R a a₂ a_R) ca ca₂) =>
                  Top_indFunArg_NatLike_pmtcty_RR0 A A₂ 
                    (BestR A_R) C C₂
                    (fun (aa : A) (aa₂ : A₂) (aa_R : BestR A_R aa aa₂) =>
                     BestR (C_R aa aa₂ aa_R)))) d d₂0) d_R in
       existT
         (fun H0 : NatLike A₂ C₂ =>
          Top_indFunArg_NatLike_pmtcty_RR0 A A₂ (BestR A_R) C C₂
            (fun (aa : A) (aa₂ : A₂) (aa_R : BestR A_R aa aa₂) =>
             BestR (C_R aa aa₂ aa_R)) (SS2 A C ao cao d) H0)
         (SS2 A₂ C₂ ao₂ cao₂ d₂)
         (Top_indFunArg_NatLike_pmtcty_RR0_constr_0 A A₂ 
            (BestR A_R) C C₂
            (fun (aa : A) (aa₂ : A₂) (aa_R : BestR A_R aa aa₂) =>
             BestR (C_R aa aa₂ aa_R)) ao ao₂ ao_R cao cao₂ cao_R d d₂ d_R0)
   end).

Run TemplateProgram (genParamIndTot [] false true "Top.indFunArg.NatLike").

