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


Inductive multInd (A I : Set) (B: I-> Set) (f: A-> I) (g: forall i, B i) 
  : forall (i:I) (b:B i), Set  :=  
mlind : forall a, multInd A I B f g (f a) (g (f a)).


Require Import SquiggleEq.UsefulTypes.

Run TemplateProgram (genParamInd [] true true "Top.multIndices2.multInd").
Print Top_multIndices2_multInd_pmtcty_RR0_indices_irr.

Require Import ReflParam.Trecord.
Module Temp.
Run TemplateProgram (genParamIndTot [] true (*iff*) true "Top.multIndices2.multInd").
End Temp.

(*
Run TemplateProgram (genParamIndTot [] false true "Top.multIndices2.multInd").
*)

Print Top_multIndices2_multInd_pmtcty_RR0_indices.

Lemma Top_multIndices2_multInd_pmtcty_RR0_indices_irrel 
(A A₂ : Set) (A_R : A -> A₂ -> Prop) (I I₂ : Set)
(I_R : I -> I₂ -> Prop) (B : I -> Set) (B₂ : I₂ -> Set)
(B_R : forall (H : I) (H0 : I₂),
       I_R H H0 -> (fun H1 H2 : Set => H1 -> H2 -> Prop) (B H) (B₂ H0)) 
(f : A -> I) (f₂ : A₂ -> I₂) (f_R : forall (H : A) (H0 : A₂), A_R H H0 -> I_R (f H) (f₂ H0))
(g : forall i : I, B i) (g₂ : forall i₂ : I₂, B₂ i₂)
(g_R : forall (i : I) (i₂ : I₂) (i_R : I_R i i₂), B_R i i₂ i_R (g i) (g₂ i₂)) 
(i : I) (i₂ : I₂) (i_R : I_R i i₂) (b : B i) (b₂ : B₂ i₂) (b_R : B_R i i₂ i_R b b₂)
   (irr : I_R i i₂) (brr: B_R i i₂ irr b b₂) :
  Top_multIndices2_multInd_pmtcty_RR0_indices _ _ A_R _ _ I_R _ _ B_R  _ _ f_R _ _ g_R _ _ i_R
  _ _ b_R irr brr.
Proof.
  pose proof (ProofIrrelevance.proof_irrelevance _ i_R irr) as Heq.
  subst irr.
  pose proof (ProofIrrelevance.proof_irrelevance _ b_R brr) as Heq.
  subst brr.
  constructor.
Defined.

Print Top_multIndices2_multInd_pmtcty_RR0.

Lemma Top_multIndices2_multInd_pmtcty_RR0_constr_0_irrel:
forall (A A₂ : Set) (A_R : A -> A₂ -> Prop) (I I₂ : Set) 
         (I_R : I -> I₂ -> Prop) (B : I -> Set) (B₂ : I₂ -> Set)
         (B_R : forall (H : I) (H0 : I₂), I_R H H0 -> B H -> B₂ H0 -> Prop) 
         (f : A -> I) (f₂ : A₂ -> I₂)
         (f_R : forall (H : A) (H0 : A₂), A_R H H0 -> I_R (f H) (f₂ H0))
         (g : forall i : I, B i) (g₂ : forall i₂ : I₂, B₂ i₂)
         (g_R : forall (i : I) (i₂ : I₂) (i_R : I_R i i₂), B_R i i₂ i_R (g i) (g₂ i₂))
         (a : A) (a₂ : A₂) (a_R : A_R a a₂) i_R1 b_R1,
Top_multIndices2_multInd_pmtcty_RR0 A A₂ 
                    A_R I I₂ I_R B B₂
                    B_R f f₂ f_R g g₂ g_R 
                    (f a) (f₂ a₂) i_R1 (g (f a)) (g₂ (f₂ a₂)) b_R1
                    (mlind A I B f g a) (mlind A₂ I₂ B₂ f₂ g₂ a₂).
Proof using.
  intros.
  simpl.
  pose proof (Top_multIndices2_multInd_pmtcty_RR0_indices_irrel
   _ _ A_R _ _ I_R _ _ B_R  _ _ f_R _ _ g_R _ _ (f_R a a₂ a_R)
  _ _ (g_R (f a) (f₂ a₂) (f_R a a₂ a_R)) i_R1 b_R1) as Heq.
  induction Heq.
  apply Top_multIndices2_multInd_pmtcty_RR0_constr_0.
Defined.  

Fixpoint Top_multIndices2_multInd_pmtcty_RR0_iso (A A₂ : Set) 
                                         (A_R : BestRel A A₂) 
                                         (I I₂ : Set) 
                                         (I_R : BestRel I I₂) 
                                         (B : I -> Set) 
                                         (B₂ : I₂ -> Set)
                                         (B_R : forall (H : I) (H0 : I₂),
                                                BestR I_R H H0 ->
                                                (fun H1 H2 : Set =>
                                                 BestRel H1 H2) 
                                                 (B H) 
                                                 (B₂ H0)) 
                                         (f : A -> I) 
                                         (f₂ : A₂ -> I₂)
                                         (f_R : BestR
                                                 (PiGoodSet A A₂ A_R
                                                 (fun _ : A => I)
                                                 (fun _ : A₂ => I₂)
                                                 (fun 
                                                 (H : A) 
                                                 (H0 : A₂)
                                                 (_ : BestR A_R H H0) => I_R))
                                                 f f₂)
                                         (g : forall i : I, B i)
                                         (g₂ : forall i₂ : I₂, B₂ i₂)
                                         (g_R : BestR
                                                 (PiGoodSet I I₂ I_R
                                                 (fun i : I => B i)
                                                 (fun i₂ : I₂ => B₂ i₂)
                                                 (fun 
                                                 (i : I) 
                                                 (i₂ : I₂)
                                                 (i_R : BestR I_R i i₂) =>
                                                 B_R i i₂ i_R)) g g₂) 
                                         (i : I) (i₂ : I₂)
                                         (i_R : BestR I_R i i₂) 
                                         (b : B i) 
                                         (b₂ : B₂ i₂)
                                         (b_R : BestR (B_R i i₂ i_R) b b₂)
                                         (H : multInd A I B f g i b) {struct
                                         H} :
   {H0 : multInd A₂ I₂ B₂ f₂ g₂ i₂ b₂ &
   Top_multIndices2_multInd_pmtcty_RR0 A A₂ (BestR A_R) I I₂ 
     (BestR I_R) B B₂
     (fun (H1 : I) (H2 : I₂) (H3 : BestR I_R H1 H2) => BestR (B_R H1 H2 H3))
     f f₂ f_R g g₂ g_R i i₂ i_R b b₂ b_R H H0} .

refine(
   match
     H as H0 in (multInd _ _ _ _ _ i0 b0)
     return
       (forall (i₂0 : I₂) (b₂0 : B₂ i₂0) (i_R0 : BestR I_R i0 i₂0)
          (b_R0 : BestR (B_R i0 i₂0 i_R0) b0 b₂0),
        {H1 : multInd A₂ I₂ B₂ f₂ g₂ i₂0 b₂0 &
        Top_multIndices2_multInd_pmtcty_RR0 A A₂ (BestR A_R) I I₂ 
          (BestR I_R) B B₂
          (fun (H2 : I) (H3 : I₂) (H4 : BestR I_R H2 H3) =>
           BestR (B_R H2 H3 H4)) f f₂ f_R g g₂ g_R i0 i₂0 i_R0 b0 b₂0 b_R0 H0
          H1})
   with
   | mlind _ _ _ _ _ a =>
       fun (i₂0 : I₂) (b₂0 : B₂ i₂0) (i_R0 : BestR I_R (f a) i₂0)
         (b_R0 : BestR (B_R (f a) i₂0 i_R0) (g (f a)) b₂0) =>
       let a₂ := BestTot12 A_R a in
       let a_R := BestTot12R A_R a in
       match
         BestOne12 (B_R (f a) i₂0 i_R0) (g (f a)) b₂0 
           (g₂ i₂0) b_R0 (g_R (f a) i₂0 i_R0) in (_ = trEqr)
         return
           ((fun b₂1 : B₂ i₂0 =>
             forall (i_R1 : BestR I_R (f a) i₂0)
               (b_R1 : BestR (B_R (f a) i₂0 i_R1) (g (f a)) b₂1),
             {H0 : multInd A₂ I₂ B₂ f₂ g₂ i₂0 b₂1 &
             Top_multIndices2_multInd_pmtcty_RR0 A A₂ 
               (BestR A_R) I I₂ (BestR I_R) B B₂
               (fun (H1 : I) (H2 : I₂) (H3 : BestR I_R H1 H2) =>
                BestR (B_R H1 H2 H3)) f f₂ f_R g g₂ g_R 
               (f a) i₂0 i_R1 (g (f a)) b₂1 b_R1 (mlind A I B f g a) H0})
              trEqr)
       with
       | eq_refl =>
           match
             BestOne12 I_R (f a) i₂0 (f₂ a₂) i_R0 (f_R a a₂ a_R) in
             (_ = trEqr)
             return
               ((fun i₂1 : I₂ =>
                 forall (i_R1 : BestR I_R (f a) i₂1)
                   (b_R1 : BestR (B_R (f a) i₂1 i_R1) (g (f a)) (g₂ i₂1)),
                 {H0 : multInd A₂ I₂ B₂ f₂ g₂ i₂1 (g₂ i₂1) &
                 Top_multIndices2_multInd_pmtcty_RR0 A A₂ 
                   (BestR A_R) I I₂ (BestR I_R) B B₂
                   (fun (H1 : I) (H2 : I₂) (H3 : BestR I_R H1 H2) =>
                    BestR (B_R H1 H2 H3)) f f₂ f_R g g₂ g_R 
                   (f a) i₂1 i_R1 (g (f a)) (g₂ i₂1) b_R1 
                   (mlind A I B f g a) H0}) trEqr)
           with
           | eq_refl =>
               fun (i_R1 : BestR I_R (f a) (f₂ a₂))
                 (b_R1 : BestR (B_R (f a) (f₂ a₂) i_R1) 
                           (g (f a)) (g₂ (f₂ a₂))) =>
               existT
                 (fun H0 : multInd A₂ I₂ B₂ f₂ g₂ (f₂ a₂) (g₂ (f₂ a₂)) =>
                  Top_multIndices2_multInd_pmtcty_RR0 A A₂ 
                    (BestR A_R) I I₂ (BestR I_R) B B₂
                    (fun (H1 : I) (H2 : I₂) (H3 : BestR I_R H1 H2) =>
                     BestR (B_R H1 H2 H3)) f f₂ f_R g g₂ g_R 
                    (f a) (f₂ a₂) i_R1 (g (f a)) (g₂ (f₂ a₂)) b_R1
                    (mlind A I B f g a) H0) (mlind A₂ I₂ B₂ f₂ g₂ a₂)
                 (Top_multIndices2_multInd_pmtcty_RR0_constr_0_irrel A A₂
                    (BestR A_R) I I₂ (BestR I_R) B B₂
                    (fun (H0 : I) (H1 : I₂) (H2 : BestR I_R H0 H1) =>
                     BestR (B_R H0 H1 H2)) f f₂ f_R g g₂ g_R a a₂ a_R i_R1 b_R1)
           end
       end i_R0 b_R0
   end i₂ b₂ i_R b_R).
Defined.

(*
Definition xxx : forall (A A₂ : Set) (A_R : Trecord.BestRel A A₂) (I I₂ : Set)
         (I_R : Trecord.BestRel I I₂) (B : I -> Set) (B₂ : I₂ -> Set)
         (B_R : forall (H : I) (H0 : I₂),
                Trecord.BestR I_R H H0 -> Trecord.BestRel (B H) (B₂ H0)) 
         (f : A -> I) (f₂ : A₂ -> I₂),
       Trecord.BestR
         (PiGoodSet A A₂ A_R (fun _ : A => I) (fun _ : A₂ => I₂)
            (fun (H : A) (H0 : A₂) (_ : Trecord.BestR A_R H H0) => I_R)) f f₂ ->
       forall (g : forall i : I, B i) (g₂ : forall i₂ : I₂, B₂ i₂),
       Trecord.BestR
         (PiGoodSet I I₂ I_R (fun i : I => B i) (fun i₂ : I₂ => B₂ i₂)
            (fun (i : I) (i₂ : I₂) (i_R : Trecord.BestR I_R i i₂) => B_R i i₂ i_R)) g g₂ ->
       forall (i : I) (i₂ : I₂) (i_R : Trecord.BestR I_R i i₂) (b : B i) (b₂ : B₂ i₂),
       Trecord.BestR (B_R i i₂ i_R) b b₂ ->
       multInd A I B f g i b -> multInd A₂ I₂ B₂ f₂ g₂ i₂ b₂ -> Prop.
intros.
eapply Top_multIndices2_multInd_pmtcty_RR0 
with (A_R := @BestR A A₂ A_R)
(I_R:= @BestR I I₂ I_R)
(B_R := fun i1 i2 ir => @BestR (B i1) (B₂ i2) (B_R i1 i2 ir)); eauto.
Defined.
*)


Print Top_multIndices2_multInd_pmtcty_RR0_constr_0.
Print Top_multIndices2_multInd_pmtcty_RR0.

(*   
      (* take the (combine cRetIndices indIndices) and go one by one. proof by induction on cRetIndices.
      forall (pair : list (TransArg STerm* TransArg Arg) ) c2:STerm, STerm 
   if pair = nil, return c2
   if pair = (ch, ih:IH)::tl then 
   @BestOne12 IH (tprime IH) (translate IH) ch ih (ptime ch) ir0 (translate ch)
   in transport 
   in tl, do some substitutions: replace (tprime ch) by (tprime ih).
   replace [ch] by (vrel (fst ih))
    *)
   set (peq := @BestOne12 I I₂ I_R (f a) i₂0 
(* so far this exactly matches the type of br above *)
   (f₂ a₂) i_R0 (f_R a a₂ a_R)).
   set (c22 := @transport I₂ (f₂ a₂) i₂0
      (fun i2:I₂ => multInd A₂ I₂ B₂ f₂ g₂ i2 
           (g₂ i2(*we had to convert this from (f₂ a₂) in c2 *)))
          peq c2).
   simpl in c22.
  (*
  assert (g₂ i₂0 = b₂0).
  apply (@BestOne12 (B (f a)) (B₂ i₂0) (B_R (f a) i₂0 i_R0) (g (f a)) b₂0).
  apply br.
  simpl in g_R.
  apply g_R.
  *)
  
  set (peq2 :=
@BestOne12 (B (f a)) (B₂ i₂0) (B_R (f a) i₂0 i_R0) (g (f a)) b₂0 
(* so far this exactly matches the type of br above *)
           (g₂ i₂0) br (g_R (f a) i₂0 (*we had to convert this from (f₂ a₂) in c2 *) 
           i_R0 (* [f a] was replaced with i_R0. it seems that this will
           be needed even if the second index was not dependent.  *) )).
           
  exact (@transport (B₂ i₂0) (g₂ i₂0) b₂0 (multInd A₂ I₂ B₂ f₂ g₂ i₂0) peq2 c22).
Defined.
*)





