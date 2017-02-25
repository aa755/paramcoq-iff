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




Inductive NatLike (A:Set) (C: forall aa:A, Set): Prop := 
 | SS : forall  (d:forall a:A, NatLike A C), NatLike A C
(* | SS2 :  forall (ao:A) (cao: C ao) 
 (d:forall (a:A) (ca da: C a), NatLike A C),
       NatLike A C
       *).

(*
Run TemplateProgram (genParamInd [] true true "Top.indFunArgP.NatLike").
*)

Require Import ReflParam.Trecord.
Require Import ReflParam.anyRelIndProp.
Open Scope string_scope.
Open Scope N_scope.
Module Temp.
Run TemplateProgram (genParamIndProp [] true "Top.indFunArgP.NatLike").


Arguments projT1 : clear implicits.
Arguments projT2 : clear implicits.

Run TemplateProgram (mkIndEnv "indTransEnv" [
"Top.indFunArgP.NatLike" ]).


Set Printing Depth 10000.

Fixpoint iffc (A A₂ : Set) (A_R : BestRel A A₂) (C : A -> Set) (C₂ : A₂ -> Set)
  (C_R : forall (aa : A) (aa₂ : A₂),
         BestR A_R aa aa₂ -> (fun H H0 : Set => BestRel H H0) (C aa) (C₂ aa₂))
         (tind : NatLike A C) :
IffCompleteHalf (Top_indFunArgP_NatLike_pmtcty_RR0 _ _ (BestR A_R) _ _ 
  (fun _ _ ar => BestR (C_R _ _ ar)) ) tind.
refine(
(fix Top_indFunArgP_NatLike_pmtcty_RR0_iso (tind : NatLike A C) :
IffCompleteHalf (Top_indFunArgP_NatLike_pmtcty_RR0 _ _ (BestR A_R) _ _ 
  (fun _ _ ar => BestR (C_R _ _ ar))) tind :=
  match tind with
  | SS _ _ d =>
      let d₂ :=
        fun a₂ : A₂ =>
        let a := BestTot21 A_R a₂ in
        let a_R := BestTot21R A_R a₂ in
         proj1 (Top_indFunArgP_NatLike_pmtcty_RR0_iso (d a)) in
      let dr :=
        fun (a : A) (a₂ : A₂) 
        (ar : BestR A_R a a₂) =>
         proj2 (Top_indFunArgP_NatLike_pmtcty_RR0_iso (d a)) (d₂ a₂) in
      conj (SS A₂ C₂ d₂) _
  end) tind ).
  intros t2.
  pose proof (ProofIrrelevance.PI.proof_irrelevance _ t2 (SS A₂ C₂ d₂)).
  subst t2.
  exists. exact dr.
Defined.
End Temp.


Definition Top_indFunArgP_NatLike_pmtcty_RR0 :=
Temp.Top_indFunArgP_NatLike_pmtcty_RR0.

Definition Top_indFunArgP_NatLike_pmtcty_RR0_constr_0_tot :=
Temp.Top_indFunArgP_NatLike_pmtcty_RR0_constr_0.

Definition iffCompl :=
(fun (A A₂ : Set) (A_R : BestRel A A₂) (C : A -> Set) 
   (C₂ : A₂ -> Set)
   (C_R : forall (aa : A) (aa₂ : A₂),
          BestR A_R aa aa₂ ->
          (fun H H0 : Set => BestRel H H0) (C aa) (C₂ aa₂)) =>
 fix Top_indFunArgP_NatLike_pmtcty_RR0_iso (tind : NatLike A C) :
   NatLike A₂ C₂ /\
   (forall tind₂ : NatLike A₂ C₂,
    Top_indFunArgP_NatLike_pmtcty_RR0 A A₂ (BestR A_R) C C₂
      (fun (aa : A) (aa₂ : A₂) (aa_R : BestR A_R aa aa₂) =>
       BestR (C_R aa aa₂ aa_R)) tind tind₂) :=
   match
     tind as tind0
     return
       (NatLike A₂ C₂ /\
        (forall tind₂ : NatLike A₂ C₂,
         Top_indFunArgP_NatLike_pmtcty_RR0 A A₂ (BestR A_R) C C₂
           (fun (aa : A) (aa₂ : A₂) (aa_R : BestR A_R aa aa₂) =>
            BestR (C_R aa aa₂ aa_R)) tind0 tind₂))
   with
   | SS _ _ d =>
       let d_R :=
         piIffCompleteRel A A₂ A_R (fun _ : A => NatLike A C)
           (fun _ : A₂ => NatLike A₂ C₂)
           (fun (a : A) (a₂ : A₂) (_ : BestR A_R a a₂) =>
            Top_indFunArgP_NatLike_pmtcty_RR0 A A₂ 
              (BestR A_R) C C₂
              (fun (aa : A) (aa₂ : A₂) (aa_R : BestR A_R aa aa₂) =>
               BestR (C_R aa aa₂ aa_R)))
           (fun (a : A) (a₂ : A₂) (_ : BestR A_R a a₂) =>
            (fun (A0 A₂0 : Set) (A_R0 : BestRel A0 A₂0) 
               (C0 : A0 -> Set) (C₂0 : A₂0 -> Set)
               (_ : forall (aa : A0) (aa₂ : A₂0),
                    BestR A_R0 aa aa₂ ->
                    (fun H H0 : Set => BestRel H H0) (C0 aa) (C₂0 aa₂)) =>
             Top_indFunArgP_NatLike_pmtcty_RR0_iso) A A₂ A_R C C₂ C_R) d in
       let d₂ := proj1 d_R in
       let d_R0 := proj2 d_R in
       conj (SS A₂ C₂ d₂)
         match
           ProofIrrelevance.proof_irrelevance (NatLike A₂ C₂) 
             (SS A₂ C₂ d₂) d_R0 in (_ = trEqr)
           return
             ((fun _ : NatLike A₂ C₂ =>
               NatLike A₂ C₂ /\
               (forall tind₂0 : NatLike A₂ C₂,
                Top_indFunArgP_NatLike_pmtcty_RR0 A A₂ 
                  (BestR A_R) C C₂
                  (fun (aa : A) (aa₂ : A₂) (aa_R : BestR A_R aa aa₂) =>
                   BestR (C_R aa aa₂ aa_R)) (SS A C d) tind₂0)) trEqr)
         with
         | eq_refl =>
             fun _ : NatLike A₂ C₂ =>
             Top_indFunArgP_NatLike_pmtcty_RR0_constr_0_tot A A₂ 
               (BestR A_R) C C₂
               (fun (aa : A) (aa₂ : A₂) (aa_R : BestR A_R aa aa₂) =>
                BestR (C_R aa aa₂ aa_R)) d d₂ d_R0
         end
   end).


Run TemplateProgram (genParamIndPropIffComplete [false] [] true "Top.indFunArgP.NatLike").
(*
Error:  Coq: unsupported character in utf8 sequence.
*)

Goal (Top_indFunArgP_NatLike_pmtcty_RR0iff12=Top_indFunArgP_NatLike_pmtcty_RR0iff12).
unfold Top_indFunArgP_NatLike_pmtcty_RR0iff12.



(*
Run TemplateProgram (genWrappers indTransEnv). (* enable when CRRInvs are generated *)
*)