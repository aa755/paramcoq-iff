Require Import squiggle4.
Require Import ReflParam.unusedVar.
Require Import JMeq.
Require Import ReflParam.common.
Require Import ReflParam.templateCoqMisc.
Require Import String.
Require Import List.
Require Import Template.Ast.
Require Import SquiggleEq.terms.
Require Import ReflParam.paramDirect ReflParam.indType.
Require Import ReflParam.indProp.
Require Import SquiggleEq.substitution.
Require Import ReflParam.PiTypeR.
Import ListNotations.
Open Scope string_scope.

Require Import ReflParam.Trecord.

Section Test.
Variables (A A₂ : Set)
(Ra : A -> A₂ -> Prop)
(pta : TotalHeteroRel Ra)
(B B₂ : Set)
(Rb : B -> B₂ -> Prop)
(ptb : TotalHeteroRel Rb)
(poa : oneToOne Ra)
.
Check(
fun (pob : oneToOne Rb) =>
let A_R := (@Build_GoodRel allProps _ _ Ra pta poa) in
let B_R := (@Build_GoodRel allProps _ _ Rb ptb pob) in
Top_squiggle4_obsEq_pmtcty_RR _ _ A_R _ _ B_R
).
Time 
ReduceAwayLamVar sthm := (
fun (pob : oneToOne Rb) =>
let A_R := (@Build_GoodRel allProps _ _ Ra pta poa) in
let B_R := (@Build_GoodRel allProps _ _ Rb ptb pob) in
Top_squiggle4_obsEq_pmtcty_RR _ _ A_R _ _ B_R
).

Check sthm.
Lemma testDefn (pob : oneToOne Rb):
let A_R := (@Build_GoodRel allProps _ _ Ra pta poa) in
let B_R := (@Build_GoodRel allProps _ _ Rb ptb pob) in
JMeq 
  (Top_squiggle4_obsEq_pmtcty_RR _ _ A_R _ _ B_R)
  sthm.
Proof using.
  reflexivity.
Qed.

End Test.
Lemma obsEqExistsAOneFreeImpl  : existsAOneFreeImpl2
  (Top_squiggle4_obsEq_pmtcty_RR).
Proof.
  eexists.
  eexists.
  intros. simpl in *.
  set (fvv:= Top_squiggle4_obsEq_pmtcty_RR _ _ A_R _ _ B_R).
  Time lazy in fvv.
Abort.


(*
Lemma dependsOnlyOnTotdivergesIff  : existsAOneFreeImpl
  (Top_squiggle2_divergesIff_pmtcty_RR).
Proof.
  eexists.
  eexists.
  intros.
  set (fvv:= Top_squiggle2_divergesIff_pmtcty_RR _ _ V_R).
  simpl in *.
  lazy in fvv.
  reflexivity. (* works *)
Defined.
*)
(*
Lemma dependsOnlyOnTotdivergesIff (V V₂ : Set) : @dependsOnlyOnRelTot V V₂ _
  (Top_squiggle2_divergesIff_pmtcty_RR V V₂).
Proof.
  intros ? ? ?.
  destruct V_R1.
  reflexivity.
Qed.
*)