
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
Require Import squiggle4.

Section iff.

  Lemma xx
        (Tm Tm₂ : Set) (Tm_R : BestRel Tm Tm₂)
        (BTm BTm₂ : Set) (BTm_R : BestRel Tm Tm₂)

  : False.
    set (f:= Top_squiggle4_evaln_pmtcty_RR _ _ Tm_R).
    simpl in f.
    destruct Tm_R as [Tm_R Rtot Rone].
    simpl in f.
    unfold  Top_squiggle4_evaln_pmtcty_RR in f.
    simpl BestR in f.
    simpl in Rtot.
  Abort.

   Variables
      (Tm Tm₂ : Set)

      (Tm_R : Tm -> Tm₂ -> Prop)

      (Rtot : TotalHeteroRel Tm_R)

      (BTm BTm₂ : Set)

      (BTm_R : BTm -> BTm₂ -> Prop)

      (RtotB : TotalHeteroRel BTm_R)

      (tmKind : Tm -> TmKind Tm BTm) (tmKind₂ : Tm₂ -> TmKind Tm₂ BTm₂)

      (tmKind_R : forall (a1 : Tm) (a2 : Tm₂),
          Tm_R a1 a2 ->
          Top_squiggle4_TmKind_pmtcty_RR0
            Tm Tm₂ Tm_R
            BTm BTm₂ BTm_R
            (tmKind a1) (tmKind₂ a2))

      (applyBtm : BTm -> Tm -> Tm) (applyBtm₂ : BTm₂ -> Tm₂ -> Tm₂)

      (applyBtm_R : forall (a1 : BTm) (a2 : BTm₂),
                       BTm_R a1 a2 ->
                       forall (a3 : Tm) (a4 : Tm₂),
                         Tm_R a3 a4 -> Tm_R (applyBtm a1 a3) (applyBtm₂ a2 a4)).

   Section eval.
   Variables
      (n n₂ : nat) (n_R : Coq_Init_Datatypes_nat_pmtcty_RR0 n n₂)
      (t : Tm) (t₂ : Tm₂) (t_R : Tm_R t t₂).

   Lemma evalnUni:

     Top_squiggle4_option_pmtcty_RR0 Tm Tm₂ Tm_R
                                     (evaln _ _ applyBtm tmKind n t)
                                     (evaln _ _ applyBtm₂ tmKind₂ n₂ t₂).

     set (ff := proj1_sig (projT2 (evalnGoodnessFree _ _ Tm_R _ _ BTm_R))
                          _ _ applyBtm_R _ _ tmKind_R
                          _ _ n_R _ _ t_R).
  exact ff.
   Qed.
   End eval.
   Variables
      (n n₂ : nat) (n_R : Coq_Init_Datatypes_nat_pmtcty_RR0 n n₂)
      (tl : Tm) (tl₂ : Tm₂) (tl_R : Tm_R tl tl₂)
      (tr : Tm) (tr₂ : Tm₂) (tr_R : Tm_R tr tr₂).

   Lemma obsEqUni:
     (obsEq _ _ applyBtm tmKind (evaln _ _ applyBtm tmKind) n tl tr)
       <->
     (obsEq _ _ applyBtm₂ tmKind₂ (evaln _ _ applyBtm₂ tmKind₂) n₂ tl₂ tr₂).
   Proof.
     set (ff := proj1_sig (projT2 (obsEqExistsAOneFreeImpl _ _ Tm_R Rtot
                                                           _ _ BTm_R RtotB
                          ))
                          _ _ applyBtm_R _ _ tmKind_R
                          _ _ evalnUni
                          _ _ n_R _ _ tl_R _ _ tr_R).
  pose proof (Trecord.Rtot ff) as Ht.
  apply Prop_RSpec in Ht.
  apply fst in Ht.
  unfold IffRel in Ht.
  apply tiffIff in Ht.
  apply Ht.
  Qed.
   
End iff.

Check obsEqUni.
Print Assumptions obsEqUni.