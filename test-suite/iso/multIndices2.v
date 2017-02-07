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
Check Top_multIndices2_multInd_pmtcty_RR0_indices_irr. (* correct! *)
Print Top_multIndices2_multInd_pmtcty_RR0_constr_0_tot. (* correct! *)


Require Import ReflParam.Trecord.
Locate BestOne12.
Locate BestOne21.

Definition xx :=
(fun (A A₂ : Set) (A_R : BestRel A A₂) (I I₂ : Set) 
   (I_R : BestRel I I₂) (B : I -> Set) (B₂ : I₂ -> Set)
   (B_R : forall (H : I) (H0 : I₂),
          BestR I_R H H0 -> (fun H1 H2 : Set => BestRel H1 H2) (B H) (B₂ H0))
   (f : A -> I) (f₂ : A₂ -> I₂)
   (f_R : BestR
            (PiGoodSet A A₂ A_R (fun _ : A => I) (fun _ : A₂ => I₂)
               (fun (H : A) (H0 : A₂) (_ : BestR A_R H H0) => I_R)) f f₂)
   (g : forall i : I, B i) (g₂ : forall i₂ : I₂, B₂ i₂)
   (g_R : BestR
            (PiGoodSet I I₂ I_R (fun i : I => B i) 
               (fun i₂ : I₂ => B₂ i₂)
               (fun (i : I) (i₂ : I₂) (i_R : BestR I_R i i₂) => B_R i i₂ i_R))
            g g₂) =>
 fix
 Top_multIndices2_multInd_pmtcty_RR0_iso (i : I) (i₂ : I₂)
                                         (i_R : BestR I_R i i₂) 
                                         (b : B i) 
                                         (b₂ : B₂ i₂)
                                         (b_R : BestR (B_R i i₂ i_R) b b₂)
                                         (tind₂ : 
                                          multInd A₂ I₂ B₂ f₂ g₂ i₂ b₂)
                                         (tind tindo : multInd A I B f g i b)
                                         (tind_R : 
                                          Top_multIndices2_multInd_pmtcty_RR0
                                            A A₂ (BestR A_R) I I₂ 
                                            (BestR I_R) B B₂
                                            (fun (H : I) 
                                               (H0 : I₂)
                                               (H1 : BestR I_R H H0) =>
                                             BestR (B_R H H0 H1)) f f₂ f_R g
                                            g₂ g_R i i₂ i_R b b₂ b_R tind
                                            tind₂)
                                         (tind_Ro : 
                                          Top_multIndices2_multInd_pmtcty_RR0
                                            A A₂ (BestR A_R) I I₂ 
                                            (BestR I_R) B B₂
                                            (fun (H : I) 
                                               (H0 : I₂)
                                               (H1 : BestR I_R H H0) =>
                                             BestR (B_R H H0 H1)) f f₂ f_R g
                                            g₂ g_R i i₂ i_R b b₂ b_R tindo
                                            tind₂) {struct tind₂} :
   tind = tindo :=
   match
     tind₂ as tind₂0 in (multInd _ _ _ _ _ i₂0 b₂0)
     return
       (forall (i_R0 : BestR I_R i i₂0) (b_R0 : BestR (B_R i i₂0 i_R0) b b₂0),
        Top_multIndices2_multInd_pmtcty_RR0 A A₂ (BestR A_R) I I₂ 
          (BestR I_R) B B₂
          (fun (H : I) (H0 : I₂) (H1 : BestR I_R H H0) => BestR (B_R H H0 H1))
          f f₂ f_R g g₂ g_R i i₂0 i_R0 b b₂0 b_R0 tind tind₂0 ->
        Top_multIndices2_multInd_pmtcty_RR0 A A₂ (BestR A_R) I I₂ 
          (BestR I_R) B B₂
          (fun (H : I) (H0 : I₂) (H1 : BestR I_R H H0) => BestR (B_R H H0 H1))
          f f₂ f_R g g₂ g_R i i₂0 i_R0 b b₂0 b_R0 tindo tind₂0 ->
        tind = tindo)
   with
   | mlind _ _ _ _ _ a₂ =>
       match
         tind as tind0 in (multInd _ _ _ _ _ i0 b0)
         return
           (forall (i_R0 : BestR I_R i0 (f₂ a₂))
              (b_R0 : BestR (B_R i0 (f₂ a₂) i_R0) b0 (g₂ (f₂ a₂))),
            Top_multIndices2_multInd_pmtcty_RR0 A A₂ 
              (BestR A_R) I I₂ (BestR I_R) B B₂
              (fun (H : I) (H0 : I₂) (H1 : BestR I_R H H0) =>
               BestR (B_R H H0 H1)) f f₂ f_R g g₂ g_R i0 
              (f₂ a₂) i_R0 b0 (g₂ (f₂ a₂)) b_R0 tind0
              (mlind A₂ I₂ B₂ f₂ g₂ a₂) ->
            Top_multIndices2_multInd_pmtcty_RR0 A A₂ 
              (BestR A_R) I I₂ (BestR I_R) B B₂
              (fun (H : I) (H0 : I₂) (H1 : BestR I_R H H0) =>
               BestR (B_R H H0 H1)) f f₂ f_R g g₂ g_R i0 
              (f₂ a₂) i_R0 b0 (g₂ (f₂ a₂)) b_R0 tindo
              (mlind A₂ I₂ B₂ f₂ g₂ a₂) -> tind0 = tindo)
       with
       | mlind _ _ _ _ _ a =>
           fiat
             (forall (i_R0 : BestR I_R (f a) (f₂ a₂))
                (b_R0 : BestR (B_R (f a) (f₂ a₂) i_R0) (g (f a)) (g₂ (f₂ a₂))),
              Top_multIndices2_multInd_pmtcty_RR0 A A₂ 
                (BestR A_R) I I₂ (BestR I_R) B B₂
                (fun (H : I) (H0 : I₂) (H1 : BestR I_R H H0) =>
                 BestR (B_R H H0 H1)) f f₂ f_R g g₂ g_R 
                (f a) (f₂ a₂) i_R0 (g (f a)) (g₂ (f₂ a₂)) b_R0
                (mlind A I B f g a) (mlind A₂ I₂ B₂ f₂ g₂ a₂) ->
              Top_multIndices2_multInd_pmtcty_RR0 A A₂ 
                (BestR A_R) I I₂ (BestR I_R) B B₂
                (fun (H : I) (H0 : I₂) (H1 : BestR I_R H H0) =>
                 BestR (B_R H H0 H1)) f f₂ f_R g g₂ g_R 
                (f a) (f₂ a₂) i_R0 (g (f a)) (g₂ (f₂ a₂)) b_R0 tindo
                (mlind A₂ I₂ B₂ f₂ g₂ a₂) -> mlind A I B f g a = tindo)
       end
   end i_R b_R tind_R tind_Ro).
   
Run TemplateProgram (genParamIndOne [true] [] true "Top.multIndices2.multInd").

