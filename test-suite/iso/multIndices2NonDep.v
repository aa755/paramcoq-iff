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


Inductive multInd (A I : Set) (B:Set) (f: A-> I) (g: forall i, B) 
  : forall (i:I) (b:B), Set  :=  
mlind : forall a, multInd A I B f g (f a) (g (f a)).


Require Import SquiggleEq.UsefulTypes.

Run TemplateProgram (genParamInd [] true true "Top.multIndices2NonDep.multInd").
Run TemplateProgram (genParamIndTotAll [] true  "Top.multIndices2NonDep.multInd").

Require Import ReflParam.Trecord.

(*
Definition multIndices2Tot : forall (A A₂ : Set) 
                                           (A_R : BestRel A A₂) 
                                           (I I₂ : Set) 
                                           (I_R : BestRel I I₂) 
                                           (B B₂ : Set) 
                                           (B_R : BestRel B B₂) 
                                           (f : A -> I) 
                                           (f₂ : A₂ -> I₂)
                                           (f_R : 
                                            BestR
                                              (PiTSummary A A₂ A_R
                                                 (fun _ : A => I)
                                                 (fun _ : A₂ => I₂)
                                                 (fun 
                                                 (H : A) 
                                                 (H0 : A₂)
                                                 (_ : BestR A_R H H0) => I_R))
                                              f f₂) 
                                           (g : I -> B) 
                                           (g₂ : I₂ -> B₂)
                                           (g_R : 
                                            BestR
                                              (PiTSummary I I₂ I_R
                                                 (fun _ : I => B)
                                                 (fun _ : I₂ => B₂)
                                                 (fun 
                                                 (i : I) 
                                                 (i₂ : I₂)
                                                 (_ : BestR I_R i i₂) => B_R))
                                              g g₂) 
                                           (i : I) 
                                           (i₂ : I₂) 
                                           (i_R : BestR I_R i i₂) 
                                           (b : B) 
                                           (b₂ : B₂) 
                                           (b_R : BestR B_R b b₂)
                                           (H : multInd A I B f g i b),
   multInd A₂ I₂ B₂ f₂ g₂ i₂ b₂.
refine
(fix
 Top_multIndices2NonDep_multInd_pmtcty_RR0 (A A₂ : Set) 
                                           (A_R : BestRel A A₂) 
                                           (I I₂ : Set) 
                                           (I_R : BestRel I I₂) 
                                           (B B₂ : Set) 
                                           (B_R : BestRel B B₂) 
                                           (f : A -> I) 
                                           (f₂ : A₂ -> I₂)
                                           (f_R : 
                                            BestR
                                              (PiTSummary A A₂ A_R
                                                 (fun _ : A => I)
                                                 (fun _ : A₂ => I₂)
                                                 (fun 
                                                 (H : A) 
                                                 (H0 : A₂)
                                                 (_ : BestR A_R H H0) => I_R))
                                              f f₂) 
                                           (g : I -> B) 
                                           (g₂ : I₂ -> B₂)
                                           (g_R : 
                                            BestR
                                              (PiTSummary I I₂ I_R
                                                 (fun _ : I => B)
                                                 (fun _ : I₂ => B₂)
                                                 (fun 
                                                 (i : I) 
                                                 (i₂ : I₂)
                                                 (_ : BestR I_R i i₂) => B_R))
                                              g g₂) 
                                           (i : I) 
                                           (i₂ : I₂) 
                                           (i_R : BestR I_R i i₂) 
                                           (b : B) 
                                           (b₂ : B₂) 
                                           (b_R : BestR B_R b b₂)
                                           (H : multInd A I B f g i b)
                                           {struct H} :
   multInd A₂ I₂ B₂ f₂ g₂ i₂ b₂ :=
   match
     H in (multInd _ _ _ _ _ i0 b0)
     return
       (forall (i₂0 : I₂) (b₂0 : B₂),
        BestR I_R i0 i₂0 ->
        BestR B_R b0 b₂0 -> multInd A₂ I₂ B₂ f₂ g₂ i₂0 b₂0)
   with
   | mlind _ _ _ _ _ a =>
       fun (i₂0 : I₂) (b₂0 : B₂) (i_R0 : BestR I_R (f a) i₂0)
         (br : BestR B_R (g (f a)) b₂0) =>
       let a₂ := BestTot12 A_R a in
       let a_R := BestTot12R A_R a in 
       let c2 := mlind A₂ I₂ B₂ f₂ g₂ a₂ in _
   end i₂ b₂ i_R b_R).
   set (peq := @BestOne12 I I₂ I_R (f a) i₂0 
(* so far this exactly matches the type of br above *)
   (f₂ a₂) i_R0 (f_R a a₂ a_R)).
   set (c22 := @transport _ _ _ 
      (fun i2:I₂ => multInd A₂ I₂ B₂ f₂ g₂ i2 
           (g₂ i2(*we had to convert this from (f₂ a₂) in c2 *)))
          peq c2).
   simpl in c22.
  set (peq2 :=
@BestOne12 B B₂ B_R (g (f a)) b₂0
(* so far this exactly matches the type of br above *)
           (g₂ i₂0) br (g_R (f a) i₂0 (*we had to convert this from (f₂ a₂) in c2 *) 
           i_R0 (* [f a] was replaced with i_R0. it seems that this will
           be needed even if the second index was not dependent.  *) )).
           
  exact (@transport B₂ (g₂ i₂0) b₂0 (multInd A₂ I₂ B₂ f₂ g₂ i₂0) peq2 c22).
Defined.

*)

