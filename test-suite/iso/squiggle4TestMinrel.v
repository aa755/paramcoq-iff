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

Require Import ReflParam.unusedVar.
Declare ML Module "myplug".
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

Section Test2.
Variables (A A₂ : Set)
(Ra : A -> A₂ -> Prop)
(pta : TotalHeteroRel Ra)
(B B₂ : Set)
(Rb : B -> B₂ -> Prop)
(ptb : TotalHeteroRel Rb).

Check (
fun (poa : oneToOne Ra) =>
@sthm _ _ Ra pta _ _ Rb poa
).
Time Detect
(
fun (poa : oneToOne Ra) =>
sthm _ _ Ra pta _ _ Rb poa
).
(*The first argument may be omitted. The reduced term is:...
Finished transaction in 0.411 secs (0.327u,0.016s) (successful)
*)

Time 
ReduceAwayLamVar sthm2 := 
(
fun (poa : oneToOne Ra) =>
sthm A A₂ Ra pta B B₂ Rb poa
).

(*
Finished transaction in 0.26 secs (0.219u,0.004s) (successful)
*)

End Test2.

Lemma obsEqExistsAOneFreeImpl  : existsAOneFreeImpl2
  (Top_squiggle4_obsEq_pmtcty_RR).
Proof.
  eexists.
  eexists (sthm2 A A₂ Ra pta B B₂ Rb). intros. reflexivity. 
(*simpl in *.
  intros. simpl in *.
  eapply sthm2; eauto.
  set (fvv:= Top_squiggle4_obsEq_pmtcty_RR _ _ A_R _ _ B_R).
  Time lazy in fvv. *)
Qed.


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