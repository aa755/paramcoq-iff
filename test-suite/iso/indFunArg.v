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

Print totalPiHalfGood (* has a universe: bad*).



Inductive NatLike (A:Set) (C: forall aa:A, Set): Set := 
(* | SS : forall (f:A->B) (c:C f)  (d:forall a:A, NatLike A B C)
     (e:forall (fi:A->B) (ci:C fi), NatLike A B C), NatLike A B C *) 
 | SS2 :  forall (ao:A) (cao: C ao) 
 (d:forall (a:A) (ca: C a), NatLike A C),
       NatLike A C.

Run TemplateProgram (genParamInd [] true true "Top.indFunArg.NatLike").
Require Import ReflParam.Trecord.

Run TemplateProgram (genParamIndTot [] true true "Top.indFunArg.NatLike").

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
        (fun a => forall (ca: C a), NatLike A C)
        (fun a => forall (ca: C₂ a), NatLike A₂ C₂)
        (fun a1 a2 ar => 
          @R_PiS (C a1) (C₂ a2) (BestR (C_R _ _ ar)) 
          (fun _ => NatLike A C)
          (fun _ => NatLike A₂ C₂)
          (fun _ _ _ => Top_indFunArg_NatLike_pmtcty_RR0 _ _ 
            (BestR A_R)  _ _ (fun _ _ ar => BestR (C_R _ _ ar)))
          )
        (fun a1 a2 ar => _) d
       in
       let c2 := SS2 A₂ C₂ ao₂ cao₂ (projT1 d2r) in
       existT _ c2 _
   end).

Unshelve.
Focus 2.
apply totalPiHalfGood.
intros ? ? ? ?. apply Top_indFunArg_NatLike_pmtcty_RR0_iso.
simpl.
exists ao_R.
exists cao_R.
exists (projT2 d2r).
simpl. constructor.
Defined.

Print Top_indFunArg_NatLike_pmtcty_RR_tot_0.
 (* |= ReflParam.common.36 = ReflParam.PiTypeR.43 *)