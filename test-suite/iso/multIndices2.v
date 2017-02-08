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
mlin1d : forall a, multInd A I B f g (f a) (g (f a))
| mlin2d : forall a2a, multInd A I B f g (f a2a) (g (f a2a)).


Require Import SquiggleEq.UsefulTypes.

Run TemplateProgram (genParamInd [] true true "Top.multIndices2.multInd").
Check Top_multIndices2_multInd_pmtcty_RR0_indices_irr. (* correct! *)
Print Top_multIndices2_multInd_pmtcty_RR0_constr_0_tot. (* correct! *)


Require Import ReflParam.Trecord.
Locate BestOne12.
Locate BestOne21.

Run TemplateProgram (genParamIndTotAll [] true "Top.multIndices2.multInd").

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
                                         (tind : multInd A I B f g i b)
                                         (tind₂
                                          tind₂o : 
                                          multInd A₂ I₂ B₂ f₂ g₂ i₂ b₂)
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
                                            g₂ g_R i i₂ i_R b b₂ b_R tind
                                            tind₂o) {struct tind} :
   tind₂ = tind₂o :=
   match
     tind as tind0 in (multInd _ _ _ _ _ i0 b0)
     return
       (forall (i_R0 : BestR I_R i0 i₂) (b_R0 : BestR (B_R i0 i₂ i_R0) b0 b₂),
        Top_multIndices2_multInd_pmtcty_RR0 A A₂ (BestR A_R) I I₂ 
          (BestR I_R) B B₂
          (fun (H : I) (H0 : I₂) (H1 : BestR I_R H H0) => BestR (B_R H H0 H1))
          f f₂ f_R g g₂ g_R i0 i₂ i_R0 b0 b₂ b_R0 tind0 tind₂ ->
        Top_multIndices2_multInd_pmtcty_RR0 A A₂ (BestR A_R) I I₂ 
          (BestR I_R) B B₂
          (fun (H : I) (H0 : I₂) (H1 : BestR I_R H H0) => BestR (B_R H H0 H1))
          f f₂ f_R g g₂ g_R i0 i₂ i_R0 b0 b₂ b_R0 tind0 tind₂o ->
        tind₂ = tind₂o)
   with
   | mlin1d _ _ _ _ _ a =>
       match
         tind₂ as tind₂0 in (multInd _ _ _ _ _ i₂0 b₂0)
         return
           (forall (tind₂o0 : multInd A₂ I₂ B₂ f₂ g₂ i₂0 b₂0)
              (i_R0 : BestR I_R (f a) i₂0)
              (b_R0 : BestR (B_R (f a) i₂0 i_R0) (g (f a)) b₂0),
            Top_multIndices2_multInd_pmtcty_RR0 A A₂ 
              (BestR A_R) I I₂ (BestR I_R) B B₂
              (fun (H : I) (H0 : I₂) (H1 : BestR I_R H H0) =>
               BestR (B_R H H0 H1)) f f₂ f_R g g₂ g_R 
              (f a) i₂0 i_R0 (g (f a)) b₂0 b_R0 (mlin1d A I B f g a) tind₂0 ->
            Top_multIndices2_multInd_pmtcty_RR0 A A₂ 
              (BestR A_R) I I₂ (BestR I_R) B B₂
              (fun (H : I) (H0 : I₂) (H1 : BestR I_R H H0) =>
               BestR (B_R H H0 H1)) f f₂ f_R g g₂ g_R 
              (f a) i₂0 i_R0 (g (f a)) b₂0 b_R0 (mlin1d A I B f g a) tind₂o0 ->
            tind₂0 = tind₂o0)
       with
       | mlin1d _ _ _ _ _ a₂ =>
           fun (tind₂o0 : multInd A₂ I₂ B₂ f₂ g₂ (f₂ a₂) (g₂ (f₂ a₂)))
             (i_R0 : BestR I_R (f a) (f₂ a₂))
             (b_R0 : BestR (B_R (f a) (f₂ a₂) i_R0) (g (f a)) (g₂ (f₂ a₂)))
             (tind_R0 : Top_multIndices2_multInd_pmtcty_RR0 A A₂ 
                          (BestR A_R) I I₂ (BestR I_R) B B₂
                          (fun (H : I) (H0 : I₂) (H1 : BestR I_R H H0) =>
                           BestR (B_R H H0 H1)) f f₂ f_R g g₂ g_R 
                          (f a) (f₂ a₂) i_R0 (g (f a)) 
                          (g₂ (f₂ a₂)) b_R0 (mlin1d A I B f g a)
                          (mlin1d A₂ I₂ B₂ f₂ g₂ a₂))
             (tind_Ro0 : Top_multIndices2_multInd_pmtcty_RR0 A A₂ 
                           (BestR A_R) I I₂ (BestR I_R) B B₂
                           (fun (H : I) (H0 : I₂) (H1 : BestR I_R H H0) =>
                            BestR (B_R H H0 H1)) f f₂ f_R g g₂ g_R 
                           (f a) (f₂ a₂) i_R0 (g (f a)) 
                           (g₂ (f₂ a₂)) b_R0 (mlin1d A I B f g a) tind₂o0) =>
           let Hexeq :=
             Top_multIndices2_multInd_pmtcty_RR0_constr_0_inv A A₂
               (BestR A_R) I I₂ tind_Ro0 tind₂o0 i_R0 b_R0 tind_R0 tind_Ro0
               (fun (tind₂o1 : multInd A₂ I₂ B₂ f₂ g₂ (f₂ a₂) (g₂ (f₂ a₂)))
                  (i_R1 : BestR I_R (f a) (f₂ a₂))
                  (b_R1 : BestR (B_R (f a) (f₂ a₂) i_R1) 
                            (g (f a)) (g₂ (f₂ a₂)))
                  (_ : Top_multIndices2_multInd_pmtcty_RR0 A A₂ 
                         (BestR A_R) I I₂ (BestR I_R) B B₂
                         (fun (H : I) (H0 : I₂) (H1 : BestR I_R H H0) =>
                          BestR (B_R H H0 H1)) f f₂ f_R g g₂ g_R 
                         (f a) (f₂ a₂) i_R1 (g (f a)) 
                         (g₂ (f₂ a₂)) b_R1 (mlin1d A I B f g a)
                         (mlin1d A₂ I₂ B₂ f₂ g₂ a₂))
                  (_ : Top_multIndices2_multInd_pmtcty_RR0 A A₂ 
                         (BestR A_R) I I₂ (BestR I_R) B B₂
                         (fun (H : I) (H0 : I₂) (H1 : BestR I_R H H0) =>
                          BestR (B_R H H0 H1)) f f₂ f_R g g₂ g_R 
                         (f a) (f₂ a₂) i_R1 (g (f a)) 
                         (g₂ (f₂ a₂)) b_R1 (mlin1d A I B f g a) tind₂o1) =>
                existT
                  (fun i₂0 : I₂ =>
                   {b₂0 : B₂ i₂0 & multInd A₂ I₂ B₂ f₂ g₂ i₂0 b₂0}) 
                  (f₂ a₂)
                  (existT
                     (fun b₂0 : B₂ (f₂ a₂) =>
                      multInd A₂ I₂ B₂ f₂ g₂ (f₂ a₂) b₂0) 
                     (g₂ (f₂ a₂)) (mlin1d A₂ I₂ B₂ f₂ g₂ a₂)) =
                existT
                  (fun i₂0 : I₂ =>
                   {b₂0 : B₂ i₂0 & multInd A₂ I₂ B₂ f₂ g₂ i₂0 b₂0}) 
                  (f₂ a₂)
                  (existT
                     (fun b₂0 : B₂ (f₂ a₂) =>
                      multInd A₂ I₂ B₂ f₂ g₂ (f₂ a₂) b₂0) 
                     (g₂ (f₂ a₂)) tind₂o1))
               (fun (a0 : A) (a₂0 : A₂) =>
                match
                  tind₂o0 as tind₂o1 in (multInd _ _ _ _ _ i₂0 b₂0)
                  return
                    (forall (i_R1 : BestR I_R (f a0) i₂0)
                       (b_R1 : BestR (B_R (f a0) i₂0 i_R1) (g (f a0)) b₂0),
                     Top_multIndices2_multInd_pmtcty_RR0 A A₂ 
                       (BestR A_R) I I₂ (BestR I_R) B B₂
                       (fun (H : I) (H0 : I₂) (H1 : BestR I_R H H0) =>
                        BestR (B_R H H0 H1)) f f₂ f_R g g₂ g_R 
                       (f a0) i₂0 i_R1 (g (f a0)) b₂0 b_R1
                       (mlin1d A I B f g a0) tind₂o1 ->
                     existT
                       (fun i₂1 : I₂ =>
                        {b₂1 : B₂ i₂1 & multInd A₂ I₂ B₂ f₂ g₂ i₂1 b₂1})
                       (f₂ a₂0)
                       (existT
                          (fun b₂1 : B₂ (f₂ a₂0) =>
                           multInd A₂ I₂ B₂ f₂ g₂ (f₂ a₂0) b₂1) 
                          (g₂ (f₂ a₂0)) (mlin1d A₂ I₂ B₂ f₂ g₂ a₂0)) =
                     existT
                       (fun i₂1 : I₂ =>
                        {b₂1 : B₂ i₂1 & multInd A₂ I₂ B₂ f₂ g₂ i₂1 b₂1}) i₂0
                       (existT
                          (fun b₂1 : B₂ i₂0 => multInd A₂ I₂ B₂ f₂ g₂ i₂0 b₂1)
                          b₂0 tind₂o1))
                with
                | mlin1d _ _ _ _ _ a₂o =>
                    fun (i_R1 : BestR I_R (f a0) (f₂ a₂o))
                      (b_R1 : BestR (B_R (f a0) (f₂ a₂o) i_R1) 
                                (g (f a0)) (g₂ (f₂ a₂o)))
                      (_ : Top_multIndices2_multInd_pmtcty_RR0 A A₂
                             (BestR A_R) I I₂ (BestR I_R) B B₂
                             (fun (H : I) (H0 : I₂) (H1 : BestR I_R H H0) =>
                              BestR (B_R H H0 H1)) f f₂ f_R g g₂ g_R 
                             (f a0) (f₂ a₂o) i_R1 
                             (g (f a0)) (g₂ (f₂ a₂o)) b_R1
                             (mlin1d A I B f g a0)
                             (mlin1d A₂ I₂ B₂ f₂ g₂ a₂o)) =>
                    fiat
                      (existT
                         (fun i₂0 : I₂ =>
                          {b₂0 : B₂ i₂0 & multInd A₂ I₂ B₂ f₂ g₂ i₂0 b₂0})
                         (f₂ a₂0)
                         (existT
                            (fun b₂0 : B₂ (f₂ a₂0) =>
                             multInd A₂ I₂ B₂ f₂ g₂ (f₂ a₂0) b₂0)
                            (g₂ (f₂ a₂0)) (mlin1d A₂ I₂ B₂ f₂ g₂ a₂0)) =
                       existT
                         (fun i₂0 : I₂ =>
                          {b₂0 : B₂ i₂0 & multInd A₂ I₂ B₂ f₂ g₂ i₂0 b₂0})
                         (f₂ a₂o)
                         (existT
                            (fun b₂0 : B₂ (f₂ a₂o) =>
                             multInd A₂ I₂ B₂ f₂ g₂ (f₂ a₂o) b₂0)
                            (g₂ (f₂ a₂o)) (mlin1d A₂ I₂ B₂ f₂ g₂ a₂o)))
                | mlin2d _ _ _ _ _ a2a₂o =>
                    fun (i_R1 : BestR I_R (f a0) (f₂ a2a₂o))
                      (b_R1 : BestR (B_R (f a0) (f₂ a2a₂o) i_R1) 
                                (g (f a0)) (g₂ (f₂ a2a₂o)))
                      (tind_Ro1 : Top_multIndices2_multInd_pmtcty_RR0 A A₂
                                    (BestR A_R) I I₂ 
                                    (BestR I_R) B B₂
                                    (fun (H : I) (H0 : I₂)
                                       (H1 : BestR I_R H H0) =>
                                     BestR (B_R H H0 H1)) f f₂ f_R g g₂ g_R
                                    (f a0) (f₂ a2a₂o) i_R1 
                                    (g (f a0)) (g₂ (f₂ a2a₂o)) b_R1
                                    (mlin1d A I B f g a0)
                                    (mlin2d A₂ I₂ B₂ f₂ g₂ a2a₂o)) =>
                    match
                      tind_Ro1
                      return
                        (existT
                           (fun i₂0 : I₂ =>
                            {b₂0 : B₂ i₂0 & multInd A₂ I₂ B₂ f₂ g₂ i₂0 b₂0})
                           (f₂ a₂0)
                           (existT
                              (fun b₂0 : B₂ (f₂ a₂0) =>
                               multInd A₂ I₂ B₂ f₂ g₂ (f₂ a₂0) b₂0)
                              (g₂ (f₂ a₂0)) (mlin1d A₂ I₂ B₂ f₂ g₂ a₂0)) =
                         existT
                           (fun i₂0 : I₂ =>
                            {b₂0 : B₂ i₂0 & multInd A₂ I₂ B₂ f₂ g₂ i₂0 b₂0})
                           (f₂ a2a₂o)
                           (existT
                              (fun b₂0 : B₂ (f₂ a2a₂o) =>
                               multInd A₂ I₂ B₂ f₂ g₂ (f₂ a2a₂o) b₂0)
                              (g₂ (f₂ a2a₂o)) (mlin2d A₂ I₂ B₂ f₂ g₂ a2a₂o)))
                    with
                    end
                end i_R0 b_R0 tind_Ro0) in
           let Hexeq0 :=
             ProofIrrelevance.ProofIrrelevanceTheory.EqdepTheory.inj_pair2 I₂
               (fun i₂0 : I₂ =>
                {b₂0 : B₂ i₂0 & multInd A₂ I₂ B₂ f₂ g₂ i₂0 b₂0}) 
               (f₂ a₂)
               (existT
                  (fun b₂0 : B₂ (f₂ a₂) => multInd A₂ I₂ B₂ f₂ g₂ (f₂ a₂) b₂0)
                  (g₂ (f₂ a₂)) (mlin1d A₂ I₂ B₂ f₂ g₂ a₂))
               (existT
                  (fun b₂0 : B₂ (f₂ a₂) => multInd A₂ I₂ B₂ f₂ g₂ (f₂ a₂) b₂0)
                  (g₂ (f₂ a₂)) tind₂o0) Hexeq in
           let Hexeq1 :=
             ProofIrrelevance.ProofIrrelevanceTheory.EqdepTheory.inj_pair2
               (B₂ (f₂ a₂))
               (fun b₂0 : B₂ (f₂ a₂) => multInd A₂ I₂ B₂ f₂ g₂ (f₂ a₂) b₂0)
               (g₂ (f₂ a₂)) (mlin1d A₂ I₂ B₂ f₂ g₂ a₂) tind₂o0 Hexeq0 in
           Hexeq1
       | mlin2d _ _ _ _ _ a2a₂ =>
           fun (tind₂o0 : multInd A₂ I₂ B₂ f₂ g₂ (f₂ a2a₂) (g₂ (f₂ a2a₂)))
             (i_R0 : BestR I_R (f a) (f₂ a2a₂))
             (b_R0 : BestR (B_R (f a) (f₂ a2a₂) i_R0) 
                       (g (f a)) (g₂ (f₂ a2a₂)))
             (tind_R0 : Top_multIndices2_multInd_pmtcty_RR0 A A₂ 
                          (BestR A_R) I I₂ (BestR I_R) B B₂
                          (fun (H : I) (H0 : I₂) (H1 : BestR I_R H H0) =>
                           BestR (B_R H H0 H1)) f f₂ f_R g g₂ g_R 
                          (f a) (f₂ a2a₂) i_R0 (g (f a)) 
                          (g₂ (f₂ a2a₂)) b_R0 (mlin1d A I B f g a)
                          (mlin2d A₂ I₂ B₂ f₂ g₂ a2a₂))
             (_ : Top_multIndices2_multInd_pmtcty_RR0 A A₂ 
                    (BestR A_R) I I₂ (BestR I_R) B B₂
                    (fun (H : I) (H0 : I₂) (H1 : BestR I_R H H0) =>
                     BestR (B_R H H0 H1)) f f₂ f_R g g₂ g_R 
                    (f a) (f₂ a2a₂) i_R0 (g (f a)) 
                    (g₂ (f₂ a2a₂)) b_R0 (mlin1d A I B f g a) tind₂o0) =>
           match tind_R0 return (mlin2d A₂ I₂ B₂ f₂ g₂ a2a₂ = tind₂o0) with
           end
       end tind₂o
   | mlin2d _ _ _ _ _ a2a =>
       match
         tind₂ as tind₂0 in (multInd _ _ _ _ _ i₂0 b₂0)
         return
           (forall (tind₂o0 : multInd A₂ I₂ B₂ f₂ g₂ i₂0 b₂0)
              (i_R0 : BestR I_R (f a2a) i₂0)
              (b_R0 : BestR (B_R (f a2a) i₂0 i_R0) (g (f a2a)) b₂0),
            Top_multIndices2_multInd_pmtcty_RR0 A A₂ 
              (BestR A_R) I I₂ (BestR I_R) B B₂
              (fun (H : I) (H0 : I₂) (H1 : BestR I_R H H0) =>
               BestR (B_R H H0 H1)) f f₂ f_R g g₂ g_R 
              (f a2a) i₂0 i_R0 (g (f a2a)) b₂0 b_R0 
              (mlin2d A I B f g a2a) tind₂0 ->
            Top_multIndices2_multInd_pmtcty_RR0 A A₂ 
              (BestR A_R) I I₂ (BestR I_R) B B₂
              (fun (H : I) (H0 : I₂) (H1 : BestR I_R H H0) =>
               BestR (B_R H H0 H1)) f f₂ f_R g g₂ g_R 
              (f a2a) i₂0 i_R0 (g (f a2a)) b₂0 b_R0 
              (mlin2d A I B f g a2a) tind₂o0 -> tind₂0 = tind₂o0)
       with
       | mlin1d _ _ _ _ _ a₂ =>
           fun (tind₂o0 : multInd A₂ I₂ B₂ f₂ g₂ (f₂ a₂) (g₂ (f₂ a₂)))
             (i_R0 : BestR I_R (f a2a) (f₂ a₂))
             (b_R0 : BestR (B_R (f a2a) (f₂ a₂) i_R0) 
                       (g (f a2a)) (g₂ (f₂ a₂)))
             (tind_R0 : Top_multIndices2_multInd_pmtcty_RR0 A A₂ 
                          (BestR A_R) I I₂ (BestR I_R) B B₂
                          (fun (H : I) (H0 : I₂) (H1 : BestR I_R H H0) =>
                           BestR (B_R H H0 H1)) f f₂ f_R g g₂ g_R 
                          (f a2a) (f₂ a₂) i_R0 (g (f a2a)) 
                          (g₂ (f₂ a₂)) b_R0 (mlin2d A I B f g a2a)
                          (mlin1d A₂ I₂ B₂ f₂ g₂ a₂))
             (_ : Top_multIndices2_multInd_pmtcty_RR0 A A₂ 
                    (BestR A_R) I I₂ (BestR I_R) B B₂
                    (fun (H : I) (H0 : I₂) (H1 : BestR I_R H H0) =>
                     BestR (B_R H H0 H1)) f f₂ f_R g g₂ g_R 
                    (f a2a) (f₂ a₂) i_R0 (g (f a2a)) 
                    (g₂ (f₂ a₂)) b_R0 (mlin2d A I B f g a2a) tind₂o0) =>
           match tind_R0 return (mlin1d A₂ I₂ B₂ f₂ g₂ a₂ = tind₂o0) with
           end
       | mlin2d _ _ _ _ _ a2a₂ =>
           fun (tind₂o0 : multInd A₂ I₂ B₂ f₂ g₂ (f₂ a2a₂) (g₂ (f₂ a2a₂)))
             (i_R0 : BestR I_R (f a2a) (f₂ a2a₂))
             (b_R0 : BestR (B_R (f a2a) (f₂ a2a₂) i_R0) 
                       (g (f a2a)) (g₂ (f₂ a2a₂)))
             (tind_R0 : Top_multIndices2_multInd_pmtcty_RR0 A A₂ 
                          (BestR A_R) I I₂ (BestR I_R) B B₂
                          (fun (H : I) (H0 : I₂) (H1 : BestR I_R H H0) =>
                           BestR (B_R H H0 H1)) f f₂ f_R g g₂ g_R 
                          (f a2a) (f₂ a2a₂) i_R0 (g (f a2a)) 
                          (g₂ (f₂ a2a₂)) b_R0 (mlin2d A I B f g a2a)
                          (mlin2d A₂ I₂ B₂ f₂ g₂ a2a₂))
             (tind_Ro0 : Top_multIndices2_multInd_pmtcty_RR0 A A₂ 
                           (BestR A_R) I I₂ (BestR I_R) B B₂
                           (fun (H : I) (H0 : I₂) (H1 : BestR I_R H H0) =>
                            BestR (B_R H H0 H1)) f f₂ f_R g g₂ g_R 
                           (f a2a) (f₂ a2a₂) i_R0 
                           (g (f a2a)) (g₂ (f₂ a2a₂)) b_R0
                           (mlin2d A I B f g a2a) tind₂o0) =>
           let Hexeq :=
             Top_multIndices2_multInd_pmtcty_RR0_constr_1_inv A A₂
               (BestR A_R) I I₂ tind_Ro0 tind₂o0 i_R0 b_R0 tind_R0 tind_Ro0
               (fun
                  (tind₂o1 : multInd A₂ I₂ B₂ f₂ g₂ (f₂ a2a₂) (g₂ (f₂ a2a₂)))
                  (i_R1 : BestR I_R (f a2a) (f₂ a2a₂))
                  (b_R1 : BestR (B_R (f a2a) (f₂ a2a₂) i_R1) 
                            (g (f a2a)) (g₂ (f₂ a2a₂)))
                  (_ : Top_multIndices2_multInd_pmtcty_RR0 A A₂ 
                         (BestR A_R) I I₂ (BestR I_R) B B₂
                         (fun (H : I) (H0 : I₂) (H1 : BestR I_R H H0) =>
                          BestR (B_R H H0 H1)) f f₂ f_R g g₂ g_R 
                         (f a2a) (f₂ a2a₂) i_R1 (g (f a2a)) 
                         (g₂ (f₂ a2a₂)) b_R1 (mlin2d A I B f g a2a)
                         (mlin2d A₂ I₂ B₂ f₂ g₂ a2a₂))
                  (_ : Top_multIndices2_multInd_pmtcty_RR0 A A₂ 
                         (BestR A_R) I I₂ (BestR I_R) B B₂
                         (fun (H : I) (H0 : I₂) (H1 : BestR I_R H H0) =>
                          BestR (B_R H H0 H1)) f f₂ f_R g g₂ g_R 
                         (f a2a) (f₂ a2a₂) i_R1 (g (f a2a)) 
                         (g₂ (f₂ a2a₂)) b_R1 (mlin2d A I B f g a2a) tind₂o1)
                =>
                existT
                  (fun i₂0 : I₂ =>
                   {b₂0 : B₂ i₂0 & multInd A₂ I₂ B₂ f₂ g₂ i₂0 b₂0}) 
                  (f₂ a2a₂)
                  (existT
                     (fun b₂0 : B₂ (f₂ a2a₂) =>
                      multInd A₂ I₂ B₂ f₂ g₂ (f₂ a2a₂) b₂0) 
                     (g₂ (f₂ a2a₂)) (mlin2d A₂ I₂ B₂ f₂ g₂ a2a₂)) =
                existT
                  (fun i₂0 : I₂ =>
                   {b₂0 : B₂ i₂0 & multInd A₂ I₂ B₂ f₂ g₂ i₂0 b₂0}) 
                  (f₂ a2a₂)
                  (existT
                     (fun b₂0 : B₂ (f₂ a2a₂) =>
                      multInd A₂ I₂ B₂ f₂ g₂ (f₂ a2a₂) b₂0) 
                     (g₂ (f₂ a2a₂)) tind₂o1))
               (fun (a2a0 : A) (a2a₂0 : A₂) =>
                match
                  tind₂o0 as tind₂o1 in (multInd _ _ _ _ _ i₂0 b₂0)
                  return
                    (forall (i_R1 : BestR I_R (f a2a0) i₂0)
                       (b_R1 : BestR (B_R (f a2a0) i₂0 i_R1) (g (f a2a0)) b₂0),
                     Top_multIndices2_multInd_pmtcty_RR0 A A₂ 
                       (BestR A_R) I I₂ (BestR I_R) B B₂
                       (fun (H : I) (H0 : I₂) (H1 : BestR I_R H H0) =>
                        BestR (B_R H H0 H1)) f f₂ f_R g g₂ g_R 
                       (f a2a0) i₂0 i_R1 (g (f a2a0)) b₂0 b_R1
                       (mlin2d A I B f g a2a0) tind₂o1 ->
                     existT
                       (fun i₂1 : I₂ =>
                        {b₂1 : B₂ i₂1 & multInd A₂ I₂ B₂ f₂ g₂ i₂1 b₂1})
                       (f₂ a2a₂0)
                       (existT
                          (fun b₂1 : B₂ (f₂ a2a₂0) =>
                           multInd A₂ I₂ B₂ f₂ g₂ (f₂ a2a₂0) b₂1)
                          (g₂ (f₂ a2a₂0)) (mlin2d A₂ I₂ B₂ f₂ g₂ a2a₂0)) =
                     existT
                       (fun i₂1 : I₂ =>
                        {b₂1 : B₂ i₂1 & multInd A₂ I₂ B₂ f₂ g₂ i₂1 b₂1}) i₂0
                       (existT
                          (fun b₂1 : B₂ i₂0 => multInd A₂ I₂ B₂ f₂ g₂ i₂0 b₂1)
                          b₂0 tind₂o1))
                with
                | mlin1d _ _ _ _ _ a₂o =>
                    fun (i_R1 : BestR I_R (f a2a0) (f₂ a₂o))
                      (b_R1 : BestR (B_R (f a2a0) (f₂ a₂o) i_R1) 
                                (g (f a2a0)) (g₂ (f₂ a₂o)))
                      (tind_Ro1 : Top_multIndices2_multInd_pmtcty_RR0 A A₂
                                    (BestR A_R) I I₂ 
                                    (BestR I_R) B B₂
                                    (fun (H : I) (H0 : I₂)
                                       (H1 : BestR I_R H H0) =>
                                     BestR (B_R H H0 H1)) f f₂ f_R g g₂ g_R
                                    (f a2a0) (f₂ a₂o) i_R1 
                                    (g (f a2a0)) (g₂ (f₂ a₂o)) b_R1
                                    (mlin2d A I B f g a2a0)
                                    (mlin1d A₂ I₂ B₂ f₂ g₂ a₂o)) =>
                    match
                      tind_Ro1
                      return
                        (existT
                           (fun i₂0 : I₂ =>
                            {b₂0 : B₂ i₂0 & multInd A₂ I₂ B₂ f₂ g₂ i₂0 b₂0})
                           (f₂ a2a₂0)
                           (existT
                              (fun b₂0 : B₂ (f₂ a2a₂0) =>
                               multInd A₂ I₂ B₂ f₂ g₂ (f₂ a2a₂0) b₂0)
                              (g₂ (f₂ a2a₂0)) (mlin2d A₂ I₂ B₂ f₂ g₂ a2a₂0)) =
                         existT
                           (fun i₂0 : I₂ =>
                            {b₂0 : B₂ i₂0 & multInd A₂ I₂ B₂ f₂ g₂ i₂0 b₂0})
                           (f₂ a₂o)
                           (existT
                              (fun b₂0 : B₂ (f₂ a₂o) =>
                               multInd A₂ I₂ B₂ f₂ g₂ (f₂ a₂o) b₂0)
                              (g₂ (f₂ a₂o)) (mlin1d A₂ I₂ B₂ f₂ g₂ a₂o)))
                    with
                    end
                | mlin2d _ _ _ _ _ a2a₂o =>
                    fun (i_R1 : BestR I_R (f a2a0) (f₂ a2a₂o))
                      (b_R1 : BestR (B_R (f a2a0) (f₂ a2a₂o) i_R1)
                                (g (f a2a0)) (g₂ (f₂ a2a₂o)))
                      (_ : Top_multIndices2_multInd_pmtcty_RR0 A A₂
                             (BestR A_R) I I₂ (BestR I_R) B B₂
                             (fun (H : I) (H0 : I₂) (H1 : BestR I_R H H0) =>
                              BestR (B_R H H0 H1)) f f₂ f_R g g₂ g_R 
                             (f a2a0) (f₂ a2a₂o) i_R1 
                             (g (f a2a0)) (g₂ (f₂ a2a₂o)) b_R1
                             (mlin2d A I B f g a2a0)
                             (mlin2d A₂ I₂ B₂ f₂ g₂ a2a₂o)) =>
                    fiat
                      (existT
                         (fun i₂0 : I₂ =>
                          {b₂0 : B₂ i₂0 & multInd A₂ I₂ B₂ f₂ g₂ i₂0 b₂0})
                         (f₂ a2a₂0)
                         (existT
                            (fun b₂0 : B₂ (f₂ a2a₂0) =>
                             multInd A₂ I₂ B₂ f₂ g₂ (f₂ a2a₂0) b₂0)
                            (g₂ (f₂ a2a₂0)) (mlin2d A₂ I₂ B₂ f₂ g₂ a2a₂0)) =
                       existT
                         (fun i₂0 : I₂ =>
                          {b₂0 : B₂ i₂0 & multInd A₂ I₂ B₂ f₂ g₂ i₂0 b₂0})
                         (f₂ a2a₂o)
                         (existT
                            (fun b₂0 : B₂ (f₂ a2a₂o) =>
                             multInd A₂ I₂ B₂ f₂ g₂ (f₂ a2a₂o) b₂0)
                            (g₂ (f₂ a2a₂o)) (mlin2d A₂ I₂ B₂ f₂ g₂ a2a₂o)))
                end i_R0 b_R0 tind_Ro0) in
           let Hexeq0 :=
             ProofIrrelevance.ProofIrrelevanceTheory.EqdepTheory.inj_pair2 I₂
               (fun i₂0 : I₂ =>
                {b₂0 : B₂ i₂0 & multInd A₂ I₂ B₂ f₂ g₂ i₂0 b₂0}) 
               (f₂ a2a₂)
               (existT
                  (fun b₂0 : B₂ (f₂ a2a₂) =>
                   multInd A₂ I₂ B₂ f₂ g₂ (f₂ a2a₂) b₂0) 
                  (g₂ (f₂ a2a₂)) (mlin2d A₂ I₂ B₂ f₂ g₂ a2a₂))
               (existT
                  (fun b₂0 : B₂ (f₂ a2a₂) =>
                   multInd A₂ I₂ B₂ f₂ g₂ (f₂ a2a₂) b₂0) 
                  (g₂ (f₂ a2a₂)) tind₂o0) Hexeq in
           let Hexeq1 :=
             ProofIrrelevance.ProofIrrelevanceTheory.EqdepTheory.inj_pair2
               (B₂ (f₂ a2a₂))
               (fun b₂0 : B₂ (f₂ a2a₂) =>
                multInd A₂ I₂ B₂ f₂ g₂ (f₂ a2a₂) b₂0) 
               (g₂ (f₂ a2a₂)) (mlin2d A₂ I₂ B₂ f₂ g₂ a2a₂) tind₂o0 Hexeq0 in
           Hexeq1
       end tind₂o
   end i_R b_R tind_R tind_Ro).
