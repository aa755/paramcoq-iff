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
Require Import ReflParam.paramDirect ReflParam.indType.
Require Import SquiggleEq.substitution.
Require Import ReflParam.PiTypeR.
Import ListNotations.
Open Scope string_scope.

Require Import ReflParam.PIWNew.

Require Import Template.Template.

Inductive IWP (I A : Set) (B : A -> Set) (AI : A -> I) 
(BI : forall (a : A), B a -> I) : forall (i:I), Prop :=
iwp : forall (a : A) (lim: forall b : B a, IWP I A B AI BI (BI a b)),
     IWP I A B AI BI (AI a).

Inductive WT (A : Set) :  Prop :=
wt : forall (lim: WT A),
     WT A.

Require Import ReflParam.indProp.
Run TemplateProgram (genParamIndProp [] true "Top.IWP.WT").
Run TemplateProgram (genParamIndProp [] true "Top.IWP.IWP").

Scheme IWP_indd := Induction for IWP Sort Prop. 

Print IWP_indd.

Run TemplateProgram (mkIndEnv "indTransEnv" ["Top.IWP.IWP"]).

Run TemplateProgram (genParam indTransEnv false true "Top.IWP.IWP_indd").


Print Top_IWP_IWP_pmtcty_RR0.
(*
Inductive
Top_IWP_IWP_pmtcty_RR0 (I I₂ : Set) (I_R : I -> I₂ -> Prop) (A A₂ : Set)
(A_R : A -> A₂ -> Prop) (B : A -> Set) (B₂ : A₂ -> Set)
(B_R : forall (H : A) (H0 : A₂),
       A_R H H0 -> (fun H1 H2 : Set => H1 -> H2 -> Prop) (B H) (B₂ H0)) 
(AI : A -> I) (AI₂ : A₂ -> I₂)
(AI_R : forall (H : A) (H0 : A₂), A_R H H0 -> I_R (AI H) (AI₂ H0))
(BI : forall a : A, B a -> I) (BI₂ : forall a₂ : A₂, B₂ a₂ -> I₂)
(BI_R : forall (a : A) (a₂ : A₂) (a_R : A_R a a₂),
        (fun (ff : B a -> I) (ff₂ : B₂ a₂ -> I₂) =>
         forall (H : B a) (H0 : B₂ a₂), B_R a a₂ a_R H H0 -> I_R (ff H) (ff₂ H0)) 
          (BI a) (BI₂ a₂))
  : forall (i : I) (i₂ : I₂),
    I_R i i₂ -> IWP I A B AI BI i -> IWP I₂ A₂ B₂ AI₂ BI₂ i₂ -> Prop :=
    Top_IWP_IWP_pmtcty_RR0_constr_0 : forall (a : A) (a₂ : A₂) (a_R : A_R a a₂)
                                        (lim : forall b : B a, IWP I A B AI BI (BI a b))
                                        (lim₂ : forall b₂ : B₂ a₂,
                                                IWP I₂ A₂ B₂ AI₂ BI₂ (BI₂ a₂ b₂)),
                                      (forall (b : B a) (b₂ : B₂ a₂)
                                         (b_R : B_R a a₂ a_R b b₂),
                                       Top_IWP_IWP_pmtcty_RR0 I I₂ I_R A A₂ A_R B B₂ B_R AI
                                         AI₂ AI_R BI BI₂ BI_R (BI a b) 
                                         (BI₂ a₂ b₂) (BI_R a a₂ a_R b b₂ b_R) 
                                         (lim b) (lim₂ b₂)) ->
                                      Top_IWP_IWP_pmtcty_RR0 I I₂ I_R A A₂ A_R B B₂ B_R AI
                                        AI₂ AI_R BI BI₂ BI_R (AI a) 
                                        (AI₂ a₂) (AI_R a a₂ a_R) 
                                        (iwp I A B AI BI a lim)
                                        (iwp I₂ A₂ B₂ AI₂ BI₂ a₂ lim₂)
*)
(*
Query commands should not be
inserted in scripts
Inductive
Top_IWP_IWT_pmtcty_RR0 (I I₂ : Set) (I_R : I -> I₂ -> Prop) 
(A A₂ : Set) (A_R : A -> A₂ -> Prop) (B : A -> Set) (B₂ : A₂ -> Set)
(B_R : forall (H : A) (H0 : A₂),
       A_R H H0 -> (fun H1 H2 : Set => H1 -> H2 -> Prop) (B H) (B₂ H0)) 
(AI : A -> I) (AI₂ : A₂ -> I₂)
(AI_R : forall (H : A) (H0 : A₂), A_R H H0 -> I_R (AI H) (AI₂ H0))
(BI : forall a : A, B a -> I) (BI₂ : forall a₂ : A₂, B₂ a₂ -> I₂)
(BI_R : forall (a : A) (a₂ : A₂) (a_R : A_R a a₂),
        (fun (ff : B a -> I) (ff₂ : B₂ a₂ -> I₂) =>
         forall (H : B a) (H0 : B₂ a₂), B_R a a₂ a_R H H0 -> I_R (ff H) (ff₂ H0)) 
          (BI a) (BI₂ a₂))
  : forall (i : I) (i₂ : I₂),
    I_R i i₂ -> IWT I A B AI BI i -> IWT I₂ A₂ B₂ AI₂ BI₂ i₂ -> Prop :=
    Top_IWP_IWT_pmtcty_RR0_constr_0 : forall (a : A) (a₂ : A₂) 
                                        (a_R : A_R a a₂)
                                        (lim : forall b : B a, IWT I A B AI BI (BI a b))
                                        (lim₂ : forall b₂ : B₂ a₂,
                                                IWT I₂ A₂ B₂ AI₂ BI₂ (BI₂ a₂ b₂)),
                                      (forall (b : B a) (b₂ : B₂ a₂)
                                         (b_R : B_R a a₂ a_R b b₂),
                                       Top_IWP_IWT_pmtcty_RR0 I I₂ I_R A A₂ A_R B B₂ B_R
                                         AI AI₂ AI_R BI BI₂ BI_R 
                                         (BI a b) (BI₂ a₂ b₂) 
                                         (BI_R a a₂ a_R b b₂ b_R) 
                                         (lim b) (lim₂ b₂)) ->
                                      Top_IWP_IWT_pmtcty_RR0 I I₂ I_R A A₂ A_R B B₂ B_R
                                        AI AI₂ AI_R BI BI₂ BI_R 
                                        (AI a) (AI₂ a₂) (AI_R a a₂ a_R)
                                        (iwt I A B AI BI a lim)
                                        (iwt I₂ A₂ B₂ AI₂ BI₂ a₂ lim₂)
*)


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