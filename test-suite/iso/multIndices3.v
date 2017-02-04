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


Inductive multInd (A I : Set) (B: I-> Set) (C : forall (ic:I) (bc: B ic), Set )
(f: A-> I) (g: forall i, B i) (gb : forall (igb:I) (gb:B igb), C igb gb) 
  : forall (i:I) (b:B i) (c: C i b), Set  :=  
mlind : forall a, multInd A I B C f g gb (f a) (g (f a)) (gb (f a) (g (f a))).


Require Import SquiggleEq.UsefulTypes.

Run TemplateProgram (genParamInd [] true true "Top.multIndices3.multInd").

Require Import ReflParam.Trecord.

Run TemplateProgram (genParamIndTot [] true true "Top.multIndices3.multInd").
(* Success :)! this runs fast. the above runs slow.*)

(*
Definition xxx :
forall (A A₂ : Set) (A_R : Trecord.BestRel A A₂) (I I₂ : Set)
         (I_R : Trecord.BestRel I I₂) (B : I -> Set) (B₂ : I₂ -> Set)
         (B_R : forall (H : I) (H0 : I₂),
                Trecord.BestR I_R H H0 ->
                (fun H1 H2 : Set => Trecord.BestRel H1 H2) (B H) (B₂ H0))
         (C : forall ic : I, B ic -> Set) (C₂ : forall ic₂ : I₂, B₂ ic₂ -> Set)
         (C_R : forall (ic : I) (ic₂ : I₂) (ic_R : Trecord.BestR I_R ic ic₂),
                (fun (ff : B ic -> Set) (ff₂ : B₂ ic₂ -> Set) =>
                 forall (bc : B ic) (bc₂ : B₂ ic₂),
                 Trecord.BestR (B_R ic ic₂ ic_R) bc bc₂ ->
                 (fun H H0 : Set => Trecord.BestRel H H0) (ff bc) (ff₂ bc₂)) 
                  (C ic) (C₂ ic₂)) (f : A -> I) (f₂ : A₂ -> I₂),
       Trecord.BestR
         (PiGoodSet A A₂ A_R (fun _ : A => I) (fun _ : A₂ => I₂)
            (fun (H : A) (H0 : A₂) (_ : Trecord.BestR A_R H H0) => I_R)) f f₂ ->
       forall (g : forall i : I, B i) (g₂ : forall i₂ : I₂, B₂ i₂),
       Trecord.BestR
         (PiGoodSet I I₂ I_R (fun i : I => B i) (fun i₂ : I₂ => B₂ i₂)
            (fun (i : I) (i₂ : I₂) (i_R : Trecord.BestR I_R i i₂) => B_R i i₂ i_R)) g g₂ ->
       forall (gb : forall (igb : I) (gb : B igb), C igb gb)
         (gb₂ : forall (igb₂ : I₂) (gb₂ : B₂ igb₂), C₂ igb₂ gb₂),
       Trecord.BestR
         (PiGoodSet I I₂ I_R (fun igb : I => forall gb0 : B igb, C igb gb0)
            (fun igb₂ : I₂ => forall gb₂0 : B₂ igb₂, C₂ igb₂ gb₂0)
            (fun (igb : I) (igb₂ : I₂) (igb_R : Trecord.BestR I_R igb igb₂) =>
             PiGoodSet (B igb) (B₂ igb₂) (B_R igb igb₂ igb_R) (fun gb0 : B igb => C igb gb0)
               (fun gb₂0 : B₂ igb₂ => C₂ igb₂ gb₂0)
               (fun (gb0 : B igb) (gb₂0 : B₂ igb₂)
                  (gb_R : Trecord.BestR (B_R igb igb₂ igb_R) gb0 gb₂0) =>
                C_R igb igb₂ igb_R gb0 gb₂0 gb_R))) gb gb₂ ->
       forall (i : I) (i₂ : I₂) (i_R : Trecord.BestR I_R i i₂) (b : B i) 
         (b₂ : B₂ i₂) (b_R : Trecord.BestR (B_R i i₂ i_R) b b₂) 
         (c : C i b) (c₂ : C₂ i₂ b₂),
       Trecord.BestR (C_R i i₂ i_R b b₂ b_R) c c₂ ->
       multInd A I B C f g gb i b c -> multInd A₂ I₂ B₂ C₂ f₂ g₂ gb₂ i₂ b₂ c₂ -> Prop.
intros.
revert H3 H4.
eapply Top_multIndices3_multInd_pmtcty_RR0 
with (A_R := @BestR A A₂ A_R)
(I_R:= @BestR I I₂ I_R)
(B_R := fun i1 i2 ir => @BestR (B i1) (B₂ i2) (B_R i1 i2 ir))
(C_R := fun i1 i2 ir b1 b2 br => @BestR (C i1 b1) (C₂ i2 b2) (C_R i1 i2 ir b1 b2 br))
; eauto.
Defined.

*)
