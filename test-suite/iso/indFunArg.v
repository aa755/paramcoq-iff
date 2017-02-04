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


Run TemplateProgram (genParamIndTot [] false true "Top.indFunArg.NatLike").

Fixpoint Top_indFunArg_NatLike_pmtcty_RR0_iso (A A₂ : Set) (A_R : BestRel A A₂) 
                                      (C : A -> Set) (C₂ : A₂ -> Set)
                                      (C_R : forall (aa : A) (aa₂ : A₂),
                                             BestR A_R aa aa₂ ->
                                             (fun H H0 : Set => BestRel H H0) 
                                               (C aa) (C₂ aa₂)) 
                                      (H : NatLike A C) {struct H} : 
 sigT (fun n2 : NatLike A₂ C₂ => 
 Top_indFunArg_NatLike_pmtcty_RR0 _ _ (BestR A_R)  _ _ (fun _ _ ar => BestR (C_R _ _ ar))
  H n2).
refine(
   match H with
   | SS2 _ _ ao cao d =>
       let ao₂ := BestTot12 A_R ao in
       let ao_R := BestTot12R A_R ao in 
       let cao₂ := BestTot12 (C_R ao ao₂ ao_R) cao in
       let cao_R := BestTot12R (C_R ao ao₂ ao_R) cao in
       let d2r := totalPiHalfGood _ _ A_R 
        (fun a:A => forall (ca: C a), NatLike A C)
        (fun a₂:A₂ => forall (ca: C₂ a₂), NatLike A₂ C₂)
        (fun (a1 : A) (a2 : A₂) (ar : BestR A_R a1 a2) => 
          @R_PiS (C a1) (C₂ a2) (BestR (C_R _ _ ar)) 
          (fun (_ : C a1) => NatLike A C)
          (fun (_: C₂ a2) => NatLike A₂ C₂)
          (fun (ca1 : C a1) (ca2 : C₂ a2) (_ : BestR (C_R a1 a2 ar) ca1 ca2) 
          => Top_indFunArg_NatLike_pmtcty_RR0 _ _ 
            (BestR A_R)  _ _ (fun _ _ ar => BestR (C_R _ _ ar)))
          )
        (fun (a1 : A) (a2 : A₂) (ar : BestR A_R a1 a2) =>
           totalPiHalfGood (C a1) (C₂ a2) (C_R a1 a2 ar) (fun _ : C a1 => NatLike A C)
             (fun _ : C₂ a2 => NatLike A₂ C₂)
             (fun (a3 : C a1) (a4 : C₂ a2) (_ : BestR (C_R a1 a2 ar) a3 a4) =>
              Top_indFunArg_NatLike_pmtcty_RR0 A A₂ (BestR A_R) C C₂
                (fun (aa : A) (aa₂ : A₂) (ar0 : BestR A_R aa aa₂) => BestR (C_R aa aa₂ ar0)))
             (fun (a0 : C a1) (a3 : C₂ a2) (_ : BestR (C_R a1 a2 ar) a0 a3)
                 =>
              Top_indFunArg_NatLike_pmtcty_RR0_iso A A₂ A_R C C₂ C_R)) d
       in
       let c2 := SS2 A₂ C₂ ao₂ cao₂ (projT1 d2r) in
       existT _ c2 _
   end).

exists ao_R.
exists cao_R.
exists (projT2 d2r).
simpl. constructor.
Defined.


Locate totalPiHalfGood.

Print Top_indFunArg_NatLike_pmtcty_RR0_iso.
 (* |= ReflParam.common.36 = ReflParam.PiTypeR.43 *)