
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

Require Import ReflParam.Trecord.
Require Import squiggle2.

Section iff.

   Lemma xx (Tm Tm₂ : Set) (Tm_R : BestRel Tm Tm₂) : False.
    set (f:= Top_squiggle2_evaln_pmtcty_RR _ _ Tm_R).
    simpl in f.
    destruct Tm_R as [Tm_R Rtot Rone].
    simpl in f.
    unfold  Top_squiggle2_evaln_pmtcty_RR in f.
    simpl BestR in f.
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
                         Tm_R a3 a4 -> Tm_R (applyBtm a1 a3) (applyBtm₂ a2 a4)).

   Section eval.
   Variables
      (n n₂ : nat) (n_R : Coq_Init_Datatypes_nat_pmtcty_RR0 n n₂)
      (t : Tm) (t₂ : Tm₂) (t_R : Tm_R t t₂).

   Lemma evalnUni:

     Top_squiggle2_option_pmtcty_RR0 Tm Tm₂ Tm_R
                                     (evaln _ elimTerm applyBtm n t)
                                     (evaln _ elimTerm₂ applyBtm₂ n₂ t₂).

     set (ff := proj1_sig (projT2 (dependsOnlyOnRelEvaln _ _ Tm_R))
                          _ _ elimTerm_R _ _ applyBtm_R
                          _ _ n_R _ _ t_R).
  exact ff.
   Qed.
   End eval.
   Variables
      (n n₂ : nat) (n_R : Coq_Init_Datatypes_nat_pmtcty_RR0 n n₂)
      (tl : Tm) (tl₂ : Tm₂) (tl_R : Tm_R tl tl₂)
      (tr : Tm) (tr₂ : Tm₂) (tr_R : Tm_R tr tr₂).

   Require Import squiggle3.
   Lemma obsEqUni:
     (obsEq _ elimTerm applyBtm (evaln _ elimTerm applyBtm) n tl tr)
       <->
     (obsEq _ elimTerm₂ applyBtm₂ (evaln _ elimTerm₂ applyBtm₂) n₂ tl₂ tr₂).
   Proof.
     set (ff := proj1_sig (projT2 (obsEqExistsAOneFreeImpl _ _ Tm_R Rtot))
                          _ _ elimTerm_R _ _ applyBtm_R
                          _ _ evalnUni
                          _ _ n_R _ _ tl_R _ _ tr_R).
  pose proof (Trecord.Rtot ff) as Ht.
  simpl in Ht.
  apply Prop_RSpec in Ht.
  apply fst in Ht.
  unfold IffRel in Ht.
  apply tiffIff in Ht.
  apply Ht.
     
  Qed.
   
End iff.

Check obsEqUni.
Print Assumptions obsEqUni.