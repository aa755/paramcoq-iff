
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

Require Import ReflParam.Trecord.
Require Import squiggle2.

Section iff.

   Lemma xx (Tm Tm₂ : Set) (Tm_R : BestRel Tm Tm₂) : False.
    set (f:= Top_squiggle2_divergesIff_pmtcty_RR _ _ Tm_R).
    simpl in f.
    unfold  Top_squiggle2_divergesIff_pmtcty_RR in f.
    destruct Tm_R as [Tm_R Rtot Rone].
    simpl in f.
    simpl in Rtot.
  Abort.

   Variables
      (Tm Tm₂ : Set)

      (Tm_R : Tm -> Tm₂ -> Prop)

      (Rtot : TotalHeteroRel Tm_R)

      (elimTerm : Tm -> tmExt Tm) (elimTerm₂ : Tm₂ -> tmExt Tm₂)

      (elimTerm_R : forall (a1 : Tm) (a2 : Tm₂),
                       Tm_R a1 a2 ->
                       Top_squiggle2_tmExt_pmtcty_RR0 Tm Tm₂ Tm_R (elimTerm a1) (elimTerm₂ a2))

      (applyBtm : Tm -> Tm -> Tm) (applyBtm₂ : Tm₂ -> Tm₂ -> Tm₂)

      (applyBtm_R : forall (a1 : Tm) (a2 : Tm₂),
                       Tm_R a1 a2 ->
                       forall (a3 : Tm) (a4 : Tm₂),
                         Tm_R a3 a4 -> Tm_R (applyBtm a1 a3) (applyBtm₂ a2 a4))

      (tl : Tm) (tl₂ : Tm₂) (tl_R : Tm_R tl tl₂) (tr : Tm) (tr₂ : Tm₂) 
      (tr_R : Tm_R tr tr₂).

   Lemma dvuni: (divergesIff _ elimTerm applyBtm tl tr) <->
                (divergesIff _ elimTerm₂ applyBtm₂ tl₂ tr₂).
     set (ff := proj1_sig (projT2 (dependsOnlyOnTotdivergesIff _ _ Tm_R Rtot))
                          _ _ elimTerm_R _ _ applyBtm_R
                          _ _ tl_R _ _ tr_R).
  pose proof (Trecord.Rtot ff) as Ht.
  simpl in Ht.
  apply Prop_RSpec in Ht.
  apply fst in Ht.
  unfold IffRel in Ht.
  apply tiffIff in Ht.
  apply Ht.
Qed.
