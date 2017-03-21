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

Definition xxx :=
(fun (I I₂ : Set) (I_R : I -> I₂ -> Prop) (A A₂ : Set)
   (A_R : A -> A₂ -> Prop) (B : A -> Set) (B₂ : A₂ -> Set)
   (B_R : forall (H : A) (H0 : A₂),
          A_R H H0 -> (fun H1 H2 : Set => H1 -> H2 -> Prop) (B H) (B₂ H0))
   (AI : A -> I) (AI₂ : A₂ -> I₂)
   (AI_R : forall (H : A) (H0 : A₂), A_R H H0 -> I_R (AI H) (AI₂ H0))
   (BI : forall a : A, B a -> I) (BI₂ : forall a₂ : A₂, B₂ a₂ -> I₂)
   (BI_R : forall (a : A) (a₂ : A₂) (a_R : A_R a a₂),
           (fun (ff : B a -> I) (ff₂ : B₂ a₂ -> I₂) =>
            forall (H : B a) (H0 : B₂ a₂),
            B_R a a₂ a_R H H0 -> I_R (ff H) (ff₂ H0)) 
             (BI a) (BI₂ a₂)) (P : forall i : I, IWP I A B AI BI i -> Prop)
   (P₂ : forall i₂ : I₂, IWP I₂ A₂ B₂ AI₂ BI₂ i₂ -> Prop)
   (P_R : forall (i : I) (i₂ : I₂) (i_R : I_R i i₂),
          (fun (ff : IWP I A B AI BI i -> Prop)
             (ff₂ : IWP I₂ A₂ B₂ AI₂ BI₂ i₂ -> Prop) =>
           forall (i0 : IWP I A B AI BI i) (i₂0 : IWP I₂ A₂ B₂ AI₂ BI₂ i₂),
           Top_IWP_IWP_pmtcty_RR0 I I₂ I_R A A₂ A_R B B₂ B_R AI AI₂ AI_R BI
             BI₂ BI_R i i₂ i_R i0 i₂0 ->
           (fun H H0 : Prop => H -> H0 -> Prop) (ff i0) (ff₂ i₂0)) 
            (P i) (P₂ i₂))
   (f : forall (a : A) (lim : forall b : B a, IWP I A B AI BI (BI a b)),
        (forall b : B a, P (BI a b) (lim b)) ->
        P (AI a) (iwp I A B AI BI a lim))
   (f₂ : forall (a₂ : A₂)
           (lim₂ : forall b₂ : B₂ a₂, IWP I₂ A₂ B₂ AI₂ BI₂ (BI₂ a₂ b₂)),
         (forall b₂ : B₂ a₂, P₂ (BI₂ a₂ b₂) (lim₂ b₂)) ->
         P₂ (AI₂ a₂) (iwp I₂ A₂ B₂ AI₂ BI₂ a₂ lim₂))
   (f_R : forall (a : A) (a₂ : A₂) (a_R : A_R a a₂),
          (fun
             (ff : forall lim : forall b : B a, IWP I A B AI BI (BI a b),
                   (forall b : B a, P (BI a b) (lim b)) ->
                   P (AI a) (iwp I A B AI BI a lim))
             (ff₂ : forall
                      lim₂ : forall b₂ : B₂ a₂,
                             IWP I₂ A₂ B₂ AI₂ BI₂ (BI₂ a₂ b₂),
                    (forall b₂ : B₂ a₂, P₂ (BI₂ a₂ b₂) (lim₂ b₂)) ->
                    P₂ (AI₂ a₂) (iwp I₂ A₂ B₂ AI₂ BI₂ a₂ lim₂)) =>
           forall (lim : forall b : B a, IWP I A B AI BI (BI a b))
             (lim₂ : forall b₂ : B₂ a₂, IWP I₂ A₂ B₂ AI₂ BI₂ (BI₂ a₂ b₂))
             (lim_R : forall (b : B a) (b₂ : B₂ a₂) (b_R : B_R a a₂ a_R b b₂),
                      Top_IWP_IWP_pmtcty_RR0 I I₂ I_R A A₂ A_R B B₂ B_R AI
                        AI₂ AI_R BI BI₂ BI_R (BI a b) 
                        (BI₂ a₂ b₂) (BI_R a a₂ a_R b b₂ b_R) 
                        (lim b) (lim₂ b₂)),
           (fun
              (ff0 : (forall b : B a, P (BI a b) (lim b)) ->
                     P (AI a) (iwp I A B AI BI a lim))
              (ff₂0 : (forall b₂ : B₂ a₂, P₂ (BI₂ a₂ b₂) (lim₂ b₂)) ->
                      P₂ (AI₂ a₂) (iwp I₂ A₂ B₂ AI₂ BI₂ a₂ lim₂)) =>
            forall (H : forall b : B a, P (BI a b) (lim b))
              (H0 : forall b₂ : B₂ a₂, P₂ (BI₂ a₂ b₂) (lim₂ b₂)),
            (forall (b : B a) (b₂ : B₂ a₂) (b_R : B_R a a₂ a_R b b₂),
             P_R (BI a b) (BI₂ a₂ b₂) (BI_R a a₂ a_R b b₂ b_R) 
               (lim b) (lim₂ b₂) (lim_R b b₂ b_R) 
               (H b) (H0 b₂)) ->
            P_R (AI a) (AI₂ a₂) (AI_R a a₂ a_R) (iwp I A B AI BI a lim)
              (iwp I₂ A₂ B₂ AI₂ BI₂ a₂ lim₂)
              (Top_IWP_IWP_pmtcty_RR0_constr_0 I I₂ I_R A A₂ A_R B B₂ B_R AI
                 AI₂ AI_R BI BI₂ BI_R a a₂ a_R lim lim₂ lim_R) 
              (ff0 H) (ff₂0 H0)) (ff lim) (ff₂ lim₂)) 
            (f a) (f₂ a₂)) =>
 let
   fix F (i : I) (i0 : IWP I A B AI BI i) {struct i0} : 
   P i i0 :=
     match i0 as i2 in (IWP _ _ _ _ _ i1) return (P i1 i2) with
     | iwp _ _ _ _ _ a lim => f a lim (fun b : B a => F (BI a b) (lim b))
     end in
 let
   fix F₂ (i₂ : I₂) (i₂0 : IWP I₂ A₂ B₂ AI₂ BI₂ i₂) {struct i₂0} :
     P₂ i₂ i₂0 :=
     match i₂0 as i₂2 in (IWP _ _ _ _ _ i₂1) return (P₂ i₂1 i₂2) with
     | iwp _ _ _ _ _ a₂ lim₂ =>
         f₂ a₂ lim₂ (fun b₂ : B₂ a₂ => F₂ (BI₂ a₂ b₂) (lim₂ b₂))
     end in
 fix
 F_R (i : I) (i₂ : I₂) (i_R : I_R i i₂) (i0 : IWP I A B AI BI i)
     (i₂0 : IWP I₂ A₂ B₂ AI₂ BI₂ i₂)
     (i_R0 : Top_IWP_IWP_pmtcty_RR0 I I₂ I_R A A₂ A_R B B₂ B_R AI AI₂ AI_R BI
               BI₂ BI_R i i₂ i_R i0 i₂0) {struct i_R0} :
   P_R i i₂ i_R i0 i₂0 i_R0 (F i i0) (F₂ i₂ i₂0) :=
   match
     (fun (i1 : I) (i2 : IWP I A B AI BI i1) =>
      match
        i2 as i4 in (IWP _ _ _ _ _ i3)
        return
          (match i4 as i6 in (IWP _ _ _ _ _ i5) return (P i5 i6) with
           | iwp _ _ _ _ _ a lim =>
               f a lim (fun b : B a => F (BI a b) (lim b))
           end = F i3 i4)
      with
      | iwp _ _ _ _ _ a lim => eq_refl
      end) i i0 in (_ = trEqr)
     return
       ((fun equ : P i i0 => P_R i i₂ i_R i0 i₂0 i_R0 equ (F₂ i₂ i₂0)) trEqr)
   with
   | eq_refl =>
       match
         (fun (i₂1 : I₂) (i₂2 : IWP I₂ A₂ B₂ AI₂ BI₂ i₂1) =>
          match
            i₂2 as i₂4 in (IWP _ _ _ _ _ i₂3)
            return
              (match
                 i₂4 as i₂6 in (IWP _ _ _ _ _ i₂5) return (P₂ i₂5 i₂6)
               with
               | iwp _ _ _ _ _ a₂ lim₂ =>
                   f₂ a₂ lim₂ (fun b₂ : B₂ a₂ => F₂ (BI₂ a₂ b₂) (lim₂ b₂))
               end = F₂ i₂3 i₂4)
          with
          | iwp _ _ _ _ _ a₂ lim₂ => eq_refl
          end) i₂ i₂0 in (_ = trEqr)
         return
           ((fun equ : P₂ i₂ i₂0 =>
             P_R i i₂ i_R i0 i₂0 i_R0
               match i0 as i2 in (IWP _ _ _ _ _ i1) return (P i1 i2) with
               | iwp _ _ _ _ _ a lim =>
                   f a lim (fun b : B a => F (BI a b) (lim b))
               end equ) trEqr)
       with
       | eq_refl =>
           match
             i_R0 as i_R2 in
             (Top_IWP_IWP_pmtcty_RR0_prop _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ i1
              i₂1 i_R1 i2 i₂2)
             return
               (P_R i1 i₂1 i_R1 i2 i₂2 i_R2
                  match i2 as i4 in (IWP _ _ _ _ _ i3) return (P i3 i4) with
                  | iwp _ _ _ _ _ a lim =>
                      f a lim (fun b : B a => F (BI a b) (lim b))
                  end
                  match
                    i₂2 as i₂4 in (IWP _ _ _ _ _ i₂3) return (P₂ i₂3 i₂4)
                  with
                  | iwp _ _ _ _ _ a₂ lim₂ =>
                      f₂ a₂ lim₂ (fun b₂ : B₂ a₂ => F₂ (BI₂ a₂ b₂) (lim₂ b₂))
                  end)
           with
           | Top_IWP_IWP_pmtcty_RR0_constr_0_prop _ _ _ _ _ _ _ _ _ _ _ _ _ _
             _ a a₂ a_R lim lim₂ lim_R =>
               f_R a a₂ a_R lim lim₂ lim_R
                 (fun b : B a => F (BI a b) (lim b))
                 (fun b₂ : B₂ a₂ => F₂ (BI₂ a₂ b₂) (lim₂ b₂))
                 (fun (b : B a) (b₂ : B₂ a₂) (b_R : B_R a a₂ a_R b b₂) =>
                  F_R (BI a b) (BI₂ a₂ b₂) (BI_R a a₂ a_R b b₂ b_R) 
                    (lim b) (lim₂ b₂) (lim_R b b₂ b_R))
           end
       end
   end).



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