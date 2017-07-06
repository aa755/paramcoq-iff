
Require Import squiggle5.
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
Variables 
(Tm Tm₂ : Set)
(Tmᵣ : Tm -> Tm₂ -> Prop)
(TmᵣTot : TotalHeteroRel Tmᵣ)
(BTm BTm₂ : Set)
(BTmᵣ : BTm -> BTm₂ -> Prop)
(BTmᵣTot : TotalHeteroRel BTmᵣ)
(TmᵣOne : oneToOne Tmᵣ)
.
Check(
fun (BTmᵣOne : oneToOne BTmᵣ) =>
let A_R := (@Build_GoodRel allProps _ _ Tmᵣ TmᵣTot TmᵣOne) in
let B_R := (@Build_GoodRel allProps _ _ BTmᵣ BTmᵣTot BTmᵣOne) in
Top_squiggle5_obseq_pmtcty_RR _ _ A_R _ _ B_R
).

Time Detect(
fun (BTmᵣOne : oneToOne BTmᵣ) =>
let A_R := (@Build_GoodRel allProps _ _ Tmᵣ TmᵣTot TmᵣOne) in
let B_R := (@Build_GoodRel allProps _ _ BTmᵣ BTmᵣTot BTmᵣOne) in
Top_squiggle5_obseq_pmtcty_RR _ _ A_R _ _ B_R
).

Time 
ReduceAwayLamVar sthm := (
fun (BTmᵣOne : oneToOne BTmᵣ) =>
let A_R := (@Build_GoodRel allProps _ _ Tmᵣ TmᵣTot TmᵣOne) in
let B_R := (@Build_GoodRel allProps _ _ BTmᵣ BTmᵣTot BTmᵣOne) in
Top_squiggle5_obseq_pmtcty_RR _ _ A_R _ _ B_R
).

Check sthm.
Lemma testDefn (BTmᵣOne : oneToOne BTmᵣ):
let A_R := (@Build_GoodRel allProps _ _ Tmᵣ TmᵣTot TmᵣOne) in
let B_R := (@Build_GoodRel allProps _ _ BTmᵣ BTmᵣTot BTmᵣOne) in
JMeq 
  (Top_squiggle5_obseq_pmtcty_RR _ _ A_R _ _ B_R)
  sthm.
Proof using.
  reflexivity.
Qed.

End Test.

Section Test2.
Variables 
(Tm Tm₂ : Set)
(Tmᵣ : Tm -> Tm₂ -> Prop)
(TmᵣTot : TotalHeteroRel Tmᵣ)
(BTm BTm₂ : Set)
(BTmᵣ : BTm -> BTm₂ -> Prop).

Check (
fun (poa : oneToOne Tmᵣ) =>
@sthm _ _ Tmᵣ TmᵣTot _ _ BTmᵣ poa
).
Time Detect
(
fun (poa : oneToOne Tmᵣ) =>
@sthm _ _ Tmᵣ TmᵣTot _ _ BTmᵣ poa
).
(*The first argument may be omitted. The reduced term is:...
Finished transaction in 1.694 secs (1.447u,0.011s) (successful)
*)

Time  ReduceAwayLamVar obseqStrongIso := 
(
fun (poa : oneToOne Tmᵣ) =>
@sthm _ _ Tmᵣ TmᵣTot _ _ BTmᵣ poa
).

(*
Finished transaction in 1.547 secs (1.259u,0.s) (successful)
*)

End Test2.

(* directly use sthm2 *)
Lemma obsEqExistsAOneFreeImpl  : existsAOneFreeImpl2
  (Top_squiggle5_obseq_pmtcty_RR).
Proof.
  eexists.
  eexists (obseqStrongIso A A₂ Ra pta B B₂ Rb). intros. reflexivity. 
Abort. (* Qed works, but this using Abort because this lemma should not be used, because it is weaker than sthm2 *)


Check obseqStrongIso.

Check Top_squiggle5_TmKind_pmtcty_RR0.

(* folding definitions and alpha renaming for readability *)
Definition obseqStrongIsoType :=
forall 
  (Tm Tm₂ : Set) (Tmᵣ : Tm -> Tm₂ -> Prop)
  (Tmᵣtot: TotalHeteroRel Tmᵣ)
  (BTm BTm₂ : Set) (BTmᵣ : BTm -> BTm₂ -> Prop)
  (applyBtm : BTm -> Tm -> Tm) (applyBtm₂ : BTm₂ -> Tm₂ -> Tm₂)
  (applyBtmᵣ : forall (b : BTm) (b₂ : BTm₂) (bᵣ: BTmᵣ b b₂) 
    (a : Tm) (a₂ : Tm₂) (aᵣ : Tmᵣ a a₂), Tmᵣ (applyBtm b a) (applyBtm₂ b₂ a₂))
  (tmKind : Tm -> TmKind Tm BTm)
  (tmKind₂ : Tm₂ -> TmKind Tm₂ BTm₂)
  (tmKindᵣ : forall (a : Tm) (a₂ : Tm₂)
        (aᵣ: Tmᵣ a a₂),
        Top_squiggle5_TmKind_pmtcty_RR0 Tm Tm₂ Tmᵣ BTm BTm₂ BTmᵣ (tmKind a)
          (tmKind₂ a₂))
  (tl : Tm) (tl₂ : Tm₂)
  (tlᵣ: Tmᵣ tl tl₂)
  (tr : Tm) (tr₂ : Tm₂)
  (trᵣ: Tmᵣ tr tr₂),
     BestRel (obseq Tm BTm applyBtm tmKind tl tr)
             (obseq Tm₂ BTm₂ applyBtm₂ tmKind₂ tl₂ tr₂).

Goal JMeq obseqStrongIsoType ltac:(let T:=type of obseqStrongIso in exact T).
reflexivity.
Qed.

Definition obseqWeakIsoType :=
(forall (Tm Tm₂ : Set) (Tm_R : BestRel Tm Tm₂) (BTm BTm₂ : Set)
   (BTm_R : BestRel BTm BTm₂) (applyBtm : BTm -> Tm -> Tm)
   (applyBtm₂ : BTm₂ -> Tm₂ -> Tm₂),
 (forall (a1 : BTm) (a2 : BTm₂),
  BestR BTm_R a1 a2 ->
  forall (a3 : Tm) (a4 : Tm₂),
  BestR Tm_R a3 a4 -> BestR Tm_R (applyBtm a1 a3) (applyBtm₂ a2 a4)) ->
 forall (tmKind : Tm -> TmKind Tm BTm) (tmKind₂ : Tm₂ -> TmKind Tm₂ BTm₂),
 (forall (a1 : Tm) (a2 : Tm₂),
  BestR Tm_R a1 a2 ->
  Top_squiggle5_TmKind_pmtcty_RR0 Tm Tm₂ (BestR Tm_R) BTm BTm₂ (BestR BTm_R)
    (tmKind a1) (tmKind₂ a2)) ->
 forall (tl : Tm) (tl₂ : Tm₂),
 BestR Tm_R tl tl₂ ->
 forall (tr : Tm) (tr₂ : Tm₂),
 BestR Tm_R tr tr₂ ->
 BestRel (forall a : nat, obsEq Tm BTm applyBtm tmKind a tl tr)
   (forall a : nat, obsEq Tm₂ BTm₂ applyBtm₂ tmKind₂ a tl₂ tr₂)).

Goal False.
let T:=type of Top_squiggle5_obseq_pmtcty_RR in let t:= eval simpl in T in idtac t.
Abort.

Goal JMeq obseqWeakIsoType ltac:(let T:=type of Top_squiggle5_obseq_pmtcty_RR in exact T).
reflexivity.
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