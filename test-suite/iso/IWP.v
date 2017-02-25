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

Inductive IWT (I A : Set) (B : A -> Set) (AI : A -> I) 
(BI : forall (a : A), B a -> I) : forall (i:I), Prop :=
iwt : forall (a : A) (lim: forall b : B a, IWT I A B AI BI (BI a b)),
     IWT I A B AI BI (AI a).

Inductive WT (A : Set) :  Prop :=
wt : forall (lim: WT A),
     WT A.

Require Import ReflParam.anyRelIndProp.
Run TemplateProgram (genParamIndProp [] true "Top.IWP.WT").
Module Temp.
Run TemplateProgram (genParamIndProp [] true "Top.IWP.IWT").
End Temp.

Definition Top_IWP_IWT_pmtcty_RR0 :=
Temp.Top_IWP_IWT_pmtcty_RR0.



Axiom 
Top_IWP_IWT_pmtcty_RR0_constr_0_tot
     : forall (I I₂ : Set) (I_R : I -> I₂ -> Prop) (A A₂ : Set) 
         (A_R : A -> A₂ -> Prop) (B : A -> Set) (B₂ : A₂ -> Set)
         (B_R : forall (H : A) (H0 : A₂), A_R H H0 -> B H -> B₂ H0 -> Prop) 
         (AI : A -> I) (AI₂ : A₂ -> I₂)
         (AI_R : forall (H : A) (H0 : A₂), A_R H H0 -> I_R (AI H) (AI₂ H0))
         (BI : forall a : A, B a -> I) (BI₂ : forall a₂ : A₂, B₂ a₂ -> I₂)
         (BI_R : forall (a : A) (a₂ : A₂) (a_R : A_R a a₂) (H : B a) (H0 : B₂ a₂),
                 B_R a a₂ a_R H H0 -> I_R (BI a H) (BI₂ a₂ H0)) 
         (a : A) (a₂ : A₂) (a_R : A_R a a₂) (lim : forall b : B a, IWT I A B AI BI (BI a b))
         (lim₂ : forall b₂ : B₂ a₂, IWT I₂ A₂ B₂ AI₂ BI₂ (BI₂ a₂ b₂)),
       (forall (b : B a) (b₂ : B₂ a₂) (b_R : B_R a a₂ a_R b b₂),
        Top_IWP_IWT_pmtcty_RR0 I I₂ I_R A A₂ A_R B B₂ B_R AI AI₂ AI_R BI BI₂ BI_R 
          (BI a b) (BI₂ a₂ b₂) (BI_R a a₂ a_R b b₂ b_R) (lim b) 
          (lim₂ b₂)) ->
       forall i_R : I_R (AI a) (AI₂ a₂),
       Top_IWP_IWT_pmtcty_RR0 I I₂ I_R A A₂ A_R B B₂ B_R AI AI₂ AI_R BI BI₂ BI_R
       (AI a) (AI₂ a₂) i_R (iwt _ _ _ _ _ a lim) (iwt _ _ _ _ _ a₂ lim₂).

Definition iffCompl :=
(fun (I I₂ : Set) (I_R : Trecord.BestRel I I₂) (A A₂ : Set)
   (A_R : Trecord.BestRel A A₂) (B : A -> Set) (B₂ : A₂ -> Set)
   (B_R : forall (H : A) (H0 : A₂),
          Trecord.BestR A_R H H0 ->
          (fun H1 H2 : Set => Trecord.BestRel H1 H2) (B H) (B₂ H0))
   (AI : A -> I) (AI₂ : A₂ -> I₂)
   (AI_R : Trecord.BestR
             (PiGoodSet A A₂ A_R (fun _ : A => I) 
                (fun _ : A₂ => I₂)
                (fun (H : A) (H0 : A₂) (_ : Trecord.BestR A_R H H0) => I_R))
             AI AI₂) (BI : forall a : A, B a -> I)
   (BI₂ : forall a₂ : A₂, B₂ a₂ -> I₂)
   (BI_R : Trecord.BestR
             (PiGoodSet A A₂ A_R (fun a : A => B a -> I)
                (fun a₂ : A₂ => B₂ a₂ -> I₂)
                (fun (a : A) (a₂ : A₂) (a_R : Trecord.BestR A_R a a₂) =>
                 PiGoodSet (B a) (B₂ a₂) (B_R a a₂ a_R) 
                   (fun _ : B a => I) (fun _ : B₂ a₂ => I₂)
                   (fun (H : B a) (H0 : B₂ a₂)
                      (_ : Trecord.BestR (B_R a a₂ a_R) H H0) => I_R))) BI
             BI₂) =>
 fix
 Top_IWP_IWT_pmtcty_RR0_iso (i : I) (i₂ : I₂) (i_R : Trecord.BestR I_R i i₂)
                            (tind : IWT I A B AI BI i) {struct tind} :
   IWT I₂ A₂ B₂ AI₂ BI₂ i₂ /\
   (forall tind₂ : IWT I₂ A₂ B₂ AI₂ BI₂ i₂,
    Top_IWP_IWT_pmtcty_RR0 I I₂ (Trecord.BestR I_R) A A₂ 
      (Trecord.BestR A_R) B B₂
      (fun (H : A) (H0 : A₂) (H1 : Trecord.BestR A_R H H0) =>
       Trecord.BestR (B_R H H0 H1)) AI AI₂ AI_R BI BI₂ BI_R i i₂ i_R tind
      tind₂) :=
   match
     tind as tind0 in (IWT _ _ _ _ _ i0)
     return
       (forall (i₂0 : I₂) (i_R0 : Trecord.BestR I_R i0 i₂0),
        IWT I₂ A₂ B₂ AI₂ BI₂ i₂0 /\
        (forall tind₂ : IWT I₂ A₂ B₂ AI₂ BI₂ i₂0,
         Top_IWP_IWT_pmtcty_RR0 I I₂ (Trecord.BestR I_R) A A₂
           (Trecord.BestR A_R) B B₂
           (fun (H : A) (H0 : A₂) (H1 : Trecord.BestR A_R H H0) =>
            Trecord.BestR (B_R H H0 H1)) AI AI₂ AI_R BI BI₂ BI_R i0 i₂0 i_R0
           tind0 tind₂))
   with
   | iwt _ _ _ _ _ a lim =>
       fun (i₂0 : I₂) (i_R0 : Trecord.BestR I_R (AI a) i₂0) =>
       let a₂ := Trecord.BestTot12 A_R a in
       let a_R := Trecord.BestTot12R A_R a in
       let lim_R :=
         piIffCompleteRel (B a) (B₂ a₂) (B_R a a₂ a_R)
           (fun b : B a => IWT I A B AI BI (BI a b))
           (fun b₂ : B₂ a₂ => IWT I₂ A₂ B₂ AI₂ BI₂ (BI₂ a₂ b₂))
           (fun (b : B a) (b₂ : B₂ a₂)
              (b_R : Trecord.BestR (B_R a a₂ a_R) b b₂) =>
            Top_IWP_IWT_pmtcty_RR0 I I₂ (Trecord.BestR I_R) A A₂
              (Trecord.BestR A_R) B B₂
              (fun (H : A) (H0 : A₂) (H1 : Trecord.BestR A_R H H0) =>
               Trecord.BestR (B_R H H0 H1)) AI AI₂ AI_R BI BI₂ BI_R 
              (BI a b) (BI₂ a₂ b₂) (BI_R a a₂ a_R b b₂ b_R))
           (fun (b : B a) (b₂ : B₂ a₂)
              (b_R : Trecord.BestR (B_R a a₂ a_R) b b₂) =>
            (fun (I0 I₂0 : Set) (I_R0 : Trecord.BestRel I0 I₂0)
               (A0 A₂0 : Set) (A_R0 : Trecord.BestRel A0 A₂0)
               (B0 : A0 -> Set) (B₂0 : A₂0 -> Set)
               (B_R0 : forall (H : A0) (H0 : A₂0),
                       Trecord.BestR A_R0 H H0 ->
                       (fun H1 H2 : Set => Trecord.BestRel H1 H2) 
                         (B0 H) (B₂0 H0)) (AI0 : A0 -> I0)
               (AI₂0 : A₂0 -> I₂0)
               (_ : Trecord.BestR
                      (PiGoodSet A0 A₂0 A_R0 (fun _ : A0 => I0)
                         (fun _ : A₂0 => I₂0)
                         (fun (H : A0) (H0 : A₂0)
                            (_ : Trecord.BestR A_R0 H H0) => I_R0)) AI0 AI₂0)
               (BI0 : forall a0 : A0, B0 a0 -> I0)
               (BI₂0 : forall a₂0 : A₂0, B₂0 a₂0 -> I₂0)
               (_ : Trecord.BestR
                      (PiGoodSet A0 A₂0 A_R0 (fun a0 : A0 => B0 a0 -> I0)
                         (fun a₂0 : A₂0 => B₂0 a₂0 -> I₂0)
                         (fun (a0 : A0) (a₂0 : A₂0)
                            (a_R0 : Trecord.BestR A_R0 a0 a₂0) =>
                          PiGoodSet (B0 a0) (B₂0 a₂0) 
                            (B_R0 a0 a₂0 a_R0) (fun _ : B0 a0 => I0)
                            (fun _ : B₂0 a₂0 => I₂0)
                            (fun (H : B0 a0) (H0 : B₂0 a₂0)
                               (_ : Trecord.BestR (B_R0 a0 a₂0 a_R0) H H0) =>
                             I_R0))) BI0 BI₂0) => Top_IWP_IWT_pmtcty_RR0_iso)
              I I₂ I_R A A₂ A_R B B₂ B_R AI AI₂ AI_R BI BI₂ BI_R 
              (BI a b) (BI₂ a₂ b₂) (BI_R a a₂ a_R b b₂ b_R)) lim in
       let lim₂ := proj1 lim_R in
       let lim_R0 := proj2 lim_R lim₂ in
       match
         Trecord.BestOne12 I_R (AI a) i₂0 (AI₂ a₂) i_R0 (AI_R a a₂ a_R) in
         (_ = trEqr)
         return
           ((fun i₂1 : I₂ =>
             forall i_R1 : Trecord.BestR I_R (AI a) i₂1,
             IWT I₂ A₂ B₂ AI₂ BI₂ i₂1 /\
             (forall tind₂ : IWT I₂ A₂ B₂ AI₂ BI₂ i₂1,
              Top_IWP_IWT_pmtcty_RR0 I I₂ (Trecord.BestR I_R) A A₂
                (Trecord.BestR A_R) B B₂
                (fun (H : A) (H0 : A₂) (H1 : Trecord.BestR A_R H H0) =>
                 Trecord.BestR (B_R H H0 H1)) AI AI₂ AI_R BI BI₂ BI_R 
                (AI a) i₂1 i_R1 (iwt I A B AI BI a lim) tind₂)) trEqr)
       with
       | eq_refl =>
           fun i_R1 : Trecord.BestR I_R (AI a) (AI₂ a₂) =>
           conj (iwt I₂ A₂ B₂ AI₂ BI₂ a₂ lim₂)
             (fun tind₂ : IWT I₂ A₂ B₂ AI₂ BI₂ i₂0 =>
              match
                ProofIrrelevance.proof_irrelevance 
                  (IWT I₂ A₂ B₂ AI₂ BI₂ i₂0) (iwt I₂ A₂ B₂ AI₂ BI₂ a₂ lim₂)
                  tind₂ in (_ = trEqr)
                return
                  ((fun tind₂0 : IWT I₂ A₂ B₂ AI₂ BI₂ (AI₂ a₂) =>
                    Top_IWP_IWT_pmtcty_RR0 I I₂ (Trecord.BestR I_R) A A₂
                      (Trecord.BestR A_R) B B₂
                      (fun (H : A) (H0 : A₂) (H1 : Trecord.BestR A_R H H0) =>
                       Trecord.BestR (B_R H H0 H1)) AI AI₂ AI_R BI BI₂ BI_R
                      (AI a) (AI₂ a₂) i_R1 (iwt I A B AI BI a lim) tind₂0)
                     trEqr)
              with
              | eq_refl =>
                  Top_IWP_IWT_pmtcty_RR0_constr_0_tot I I₂
                    (Trecord.BestR I_R) A A₂ (Trecord.BestR A_R) B B₂
                    (fun (H : A) (H0 : A₂) (H1 : Trecord.BestR A_R H H0) =>
                     Trecord.BestR (B_R H H0 H1)) AI AI₂ AI_R BI BI₂ BI_R a
                    a₂ a_R lim lim₂ lim_R0 i_R1
              end)
       end i_R0
   end i₂ i_R).
   

Run TemplateProgram (genParamIndPropIffComplete [false] [] true "Top.IWP.IWT").




Inductive multInd2 (A I : Set) (B: I-> Set) (f: A-> I) (g: forall i, B i) 
  : forall (i:I) (b:B i), Prop  :=  
mlind2 : forall a
(dd:forall (aa:A), multInd2 A I B f g (f aa) (g (f aa))),
multInd2 A I B f g (f a) (g (f a))

|mlind2d : forall aaaa
(ddd:forall (aaa:A), multInd2 A I B f g (f aaa) (g (f aaa))),
multInd2 A I B f g (f aaaa) (g (f aaaa)).


Run TemplateProgram (genParamIndProp [] true "Top.IWP.multInd2").
Print Top_IWP_multInd2_pmtcty_RR0.



         
(*
Inductive
Top_IWP_multInd2_pmtcty_RR0 (A A₂ : Set) (A_R : A -> A₂ -> Prop) 
(I I₂ : Set) (I_R : I -> I₂ -> Prop) (B : I -> Set) (B₂ : I₂ -> Set)
(B_R : forall (H : I) (H0 : I₂),
       I_R H H0 -> (fun H1 H2 : Set => H1 -> H2 -> Prop) (B H) (B₂ H0)) 
(f : A -> I) (f₂ : A₂ -> I₂)
(f_R : forall (H : A) (H0 : A₂), A_R H H0 -> I_R (f H) (f₂ H0)) 
(g : forall i : I, B i) (g₂ : forall i₂ : I₂, B₂ i₂)
(g_R : forall (i : I) (i₂ : I₂) (i_R : I_R i i₂), B_R i i₂ i_R (g i) (g₂ i₂))
  : forall (i : I) (i₂ : I₂) (i_R : I_R i i₂) (b : B i) (b₂ : B₂ i₂),
    B_R i i₂ i_R b b₂ -> multInd2 A I B f g i b -> multInd2 A₂ I₂ B₂ f₂ g₂ i₂ b₂ -> Prop :=
    Top_IWP_multInd2_pmtcty_RR0_constr_0 : forall (a : A) (a₂ : A₂) 
                                             (a_R : A_R a a₂)
                                             (dd : forall aa : A,
                                                   multInd2 A I B f g (f aa) (g (f aa)))
                                             (dd₂ : forall aa₂ : A₂,
                                                    multInd2 A₂ I₂ B₂ f₂ g₂ 
                                                      (f₂ aa₂) 
                                                      (g₂ (f₂ aa₂))),
                                           (forall (aa : A) 
                                              (aa₂ : A₂) (aa_R : A_R aa aa₂),
                                            Top_IWP_multInd2_pmtcty_RR0 A A₂ A_R I I₂
                                              I_R B B₂ B_R f f₂ f_R g g₂ g_R 
                                              (f aa) (f₂ aa₂) 
                                              (f_R aa aa₂ aa_R) 
                                              (g (f aa)) (g₂ (f₂ aa₂))
                                              (g_R (f aa) (f₂ aa₂) (f_R aa aa₂ aa_R))
                                              (dd aa) (dd₂ aa₂)) ->
                                           Top_IWP_multInd2_pmtcty_RR0 A A₂ A_R I I₂ I_R
                                             B B₂ B_R f f₂ f_R g g₂ g_R 
                                             (f a) (f₂ a₂) (f_R a a₂ a_R) 
                                             (g (f a)) (g₂ (f₂ a₂))
                                             (g_R (f a) (f₂ a₂) (f_R a a₂ a_R))
                                             (mlind2 A I B f g a dd)
                                             (mlind2 A₂ I₂ B₂ f₂ g₂ a₂ dd₂)
  | Top_IWP_multInd2_pmtcty_RR0_constr_1 : forall (aaaa : A) 
                                             (aaaa₂ : A₂) (aaaa_R : A_R aaaa aaaa₂)
                                             (ddd : forall aaa : A,
                                                    multInd2 A I B f g 
                                                      (f aaa) 
                                                      (g (f aaa)))
                                             (ddd₂ : forall aaa₂ : A₂,
                                                     multInd2 A₂ I₂ B₂ f₂ g₂ 
                                                       (f₂ aaa₂) 
                                                       (g₂ (f₂ aaa₂))),
                                           (forall (aaa : A) 
                                              (aaa₂ : A₂) (aaa_R : A_R aaa aaa₂),
                                            Top_IWP_multInd2_pmtcty_RR0 A A₂ A_R I I₂
                                              I_R B B₂ B_R f f₂ f_R g g₂ g_R 
                                              (f aaa) (f₂ aaa₂) 
                                              (f_R aaa aaa₂ aaa_R) 
                                              (g (f aaa)) (g₂ (f₂ aaa₂))
                                              (g_R (f aaa) (f₂ aaa₂)
                                                 (f_R aaa aaa₂ aaa_R)) 
                                              (ddd aaa) (ddd₂ aaa₂)) ->
                                           Top_IWP_multInd2_pmtcty_RR0 A A₂ A_R I I₂ I_R
                                             B B₂ B_R f f₂ f_R g g₂ g_R 
                                             (f aaaa) (f₂ aaaa₂) 
                                             (f_R aaaa aaaa₂ aaaa_R) 
                                             (g (f aaaa)) (g₂ (f₂ aaaa₂))
                                             (g_R (f aaaa) (f₂ aaaa₂)
                                                (f_R aaaa aaaa₂ aaaa_R))
                                             (mlind2d A I B f g aaaa ddd)
                                             (mlind2d A₂ I₂ B₂ f₂ g₂ aaaa₂ ddd₂)
*)