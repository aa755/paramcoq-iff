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
  : forall (i:I) (b:B i), Set  :=  
mlind : forall a, multInd A I B C f g gb (f a) (g (f a)).


Require Import SquiggleEq.UsefulTypes.

Run TemplateProgram (genParamInd [] true true true "Top.multIndices3.multInd").

Require Import ReflParam.Trecord.

Set Printing All.

Run TemplateProgram (genParamIndTot [] true true "Top.multIndices3.multInd").


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





