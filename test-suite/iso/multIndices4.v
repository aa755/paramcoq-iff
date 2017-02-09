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


Inductive multInd2 (A I : Set) (B: I-> Set) (f: A-> I) (g: forall i, B i) 
  : forall (i:I) (b:B i), Set  :=  
mlind2 : forall a
(dd:forall (aa:A), multInd2 A I B f g (f aa) (g (f aa))),
multInd2 A I B f g (f a) (g (f a))

|mlind2d : forall aaaa
(ddd:forall (aaa:A), multInd2 A I B f g (f aaa) (g (f aaa))),
multInd2 A I B f g (f aaaa) (g (f aaaa)).

Inductive multInd (A I : Set) (B: I-> Set) (f: A-> I) (g: forall i, B i) 
  : forall (i:I) (b:B i), Set  :=  
mlind : forall a
(dd:forall (aa:A), multInd A I B f g (f a) (g (f a))),
multInd A I B f g (f a) (g (f a)).


Require Import SquiggleEq.UsefulTypes.

Run TemplateProgram (genParamIndAll [] "Top.multIndices4.multInd").

Check Top_multIndices4_multInd_pmtcty_RR0_constr_0_inv.
(*
Top_multIndices4_multInd_pmtcty_RR0_constr_0_inv
     : forall (A A₂ : Set) (A_R : A -> A₂ -> Prop) (I I₂ : Set) 
         (I_R : I -> I₂ -> Prop) (B : I -> Set) (B₂ : I₂ -> Set)
         (B_R : forall (H : I) (H0 : I₂), I_R H H0 -> B H -> B₂ H0 -> Prop) 
         (f : A -> I) (f₂ : A₂ -> I₂)
         (f_R : forall (H : A) (H0 : A₂), A_R H H0 -> I_R (f H) (f₂ H0))
         (g : forall i : I, B i) (g₂ : forall i₂ : I₂, B₂ i₂)
         (g_R : forall (i : I) (i₂ : I₂) (i_R : I_R i i₂), B_R i i₂ i_R (g i) (g₂ i₂))
         (a : A) (a₂ : A₂) (dd : A -> multInd A I B f g (f a) (g (f a)))
         (dd₂ : A₂ -> multInd A₂ I₂ B₂ f₂ g₂ (f₂ a₂) (g₂ (f₂ a₂))) 
         (i_R : I_R (f a) (f₂ a₂)) (b_R : B_R (f a) (f₂ a₂) i_R (g (f a)) (g₂ (f₂ a₂)))
         (sigt_R : {a_R : A_R a a₂ &
                   {_
                   : forall (aa : A) (aa₂ : A₂),
                     A_R aa aa₂ ->
                     Top_multIndices4_multInd_pmtcty_RR0 A A₂ A_R I I₂ I_R B B₂ B_R f f₂ f_R
                       g g₂ g_R (f a) (f₂ a₂) (f_R a a₂ a_R) (g (f a)) 
                       (g₂ (f₂ a₂)) (g_R (f a) (f₂ a₂) (f_R a a₂ a_R)) 
                       (dd aa) (dd₂ aa₂) &
                   Top_multIndices4_multInd_pmtcty_RR0_indices A A₂ A_R I I₂ I_R B B₂ B_R f
                     f₂ f_R g g₂ g_R (f a) (f₂ a₂) (f_R a a₂ a_R) 
                     (g (f a)) (g₂ (f₂ a₂)) (g_R (f a) (f₂ a₂) (f_R a a₂ a_R)) i_R b_R}})
         (retTyp_R : forall (i_R0 : I_R (f a) (f₂ a₂))
                       (b_R0 : B_R (f a) (f₂ a₂) i_R0 (g (f a)) (g₂ (f₂ a₂))),
                     {a_R : A_R a a₂ &
                     {_
                     : forall (aa : A) (aa₂ : A₂),
                       A_R aa aa₂ ->
                       Top_multIndices4_multInd_pmtcty_RR0 A A₂ A_R I I₂ I_R B B₂ B_R f f₂
                         f_R g g₂ g_R (f a) (f₂ a₂) (f_R a a₂ a_R) 
                         (g (f a)) (g₂ (f₂ a₂)) (g_R (f a) (f₂ a₂) (f_R a a₂ a_R)) 
                         (dd aa) (dd₂ aa₂) &
                     Top_multIndices4_multInd_pmtcty_RR0_indices A A₂ A_R I I₂ I_R B B₂ B_R
                       f f₂ f_R g g₂ g_R (f a) (f₂ a₂) (f_R a a₂ a_R) 
                       (g (f a)) (g₂ (f₂ a₂)) (g_R (f a) (f₂ a₂) (f_R a a₂ a_R)) i_R0 b_R0}} ->
                     Trecord.IndicesInvUniv),
       (forall (a_R : A_R a a₂)
          (dd_R : forall (aa : A) (aa₂ : A₂),
                  A_R aa aa₂ ->
                  Top_multIndices4_multInd_pmtcty_RR0 A A₂ A_R I I₂ I_R B B₂ B_R f f₂ f_R g
                    g₂ g_R (f a) (f₂ a₂) (f_R a a₂ a_R) (g (f a)) 
                    (g₂ (f₂ a₂)) (g_R (f a) (f₂ a₂) (f_R a a₂ a_R)) 
                    (dd aa) (dd₂ aa₂)),
        retTyp_R (f_R a a₂ a_R) (g_R (f a) (f₂ a₂) (f_R a a₂ a_R))
          (existT
             (fun a_R0 : A_R a a₂ =>
              {_
              : forall (aa : A) (aa₂ : A₂),
                A_R aa aa₂ ->
                Top_multIndices4_multInd_pmtcty_RR0 A A₂ A_R I I₂ I_R B B₂ B_R f f₂ f_R g g₂
                  g_R (f a) (f₂ a₂) (f_R a a₂ a_R0) (g (f a)) (g₂ (f₂ a₂))
                  (g_R (f a) (f₂ a₂) (f_R a a₂ a_R0)) (dd aa) (dd₂ aa₂) &
              Top_multIndices4_multInd_pmtcty_RR0_indices A A₂ A_R I I₂ I_R B B₂ B_R f f₂
                f_R g g₂ g_R (f a) (f₂ a₂) (f_R a a₂ a_R0) (g (f a)) 
                (g₂ (f₂ a₂)) (g_R (f a) (f₂ a₂) (f_R a a₂ a_R0)) 
                (f_R a a₂ a_R) (g_R (f a) (f₂ a₂) (f_R a a₂ a_R))}) a_R
             (existT
                (fun
                   _ : forall (aa : A) (aa₂ : A₂),
                       A_R aa aa₂ ->
                       Top_multIndices4_multInd_pmtcty_RR0 A A₂ A_R I I₂ I_R B B₂ B_R f f₂
                         f_R g g₂ g_R (f a) (f₂ a₂) (f_R a a₂ a_R) 
                         (g (f a)) (g₂ (f₂ a₂)) (g_R (f a) (f₂ a₂) (f_R a a₂ a_R)) 
                         (dd aa) (dd₂ aa₂) =>
                 Top_multIndices4_multInd_pmtcty_RR0_indices A A₂ A_R I I₂ I_R B B₂ B_R f f₂
                   f_R g g₂ g_R (f a) (f₂ a₂) (f_R a a₂ a_R) (g (f a)) 
                   (g₂ (f₂ a₂)) (g_R (f a) (f₂ a₂) (f_R a a₂ a_R)) 
                   (f_R a a₂ a_R) (g_R (f a) (f₂ a₂) (f_R a a₂ a_R))) dd_R
                (Top_multIndices4_multInd_pmtcty_RR0_indicesc A A₂ A_R I I₂ I_R B B₂ B_R f
                   f₂ f_R g g₂ g_R (f a) (f₂ a₂) (f_R a a₂ a_R) 
                   (g (f a)) (g₂ (f₂ a₂)) (g_R (f a) (f₂ a₂) (f_R a a₂ a_R)))))) ->
       retTyp_R i_R b_R sigt_R
*)

Run TemplateProgram (genParamIndAll [] "Top.multIndices4.multInd2").
Require Import ReflParam.Trecord.

Run TemplateProgram (mkIndEnv "indTransEnv" ["Top.multIndices4.multInd";
"Top.multIndices4.multInd2"]).
Run TemplateProgram (genWrappers indTransEnv).


