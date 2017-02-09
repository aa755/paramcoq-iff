

Require Import SquiggleEq.list.
Require Import SquiggleEq.UsefulTypes.
Require Import common.
Require Import SquiggleEq.tactics.


Require Import EqdepFacts.

Require Import JMeq.


Set Implicit Arguments.

Require Import Trecord.


Definition dependsOnlyOnRel (V V₂ : Set) {T:(BestRel V V₂)->Type} 
  (P: forall v: BestRel V V₂, T v):=
forall (V_R1 : BestRel V V₂) pt po,
let V_R2 := {| R:= BestR V_R1; Rtot := pt ; Rone := po |} in
 JMeq (P V_R1) (P V_R2).

Definition dependsOnlyOnRelTot (V V₂ : Set) {T:(BestRel V V₂)->Type} 
  (P: forall v: BestRel V V₂, T v):=
forall (V_R1 : BestRel V V₂) po,
let V_R2 : BestRel V V₂ 
:= @Build_GoodRel allProps V V₂ (BestR V_R1) (@Rtot allProps _ _ V_R1) po in
 JMeq (P V_R1) (P V_R2).


Definition existsAGoodnessFreeImpl {T: forall (V V₂ : Set) (V_R : BestRel V V₂), Type}
(P : forall (V V₂ : Set) (V_R : BestRel V V₂), T V V₂ V_R) : Type :=
forall 
(V V₂ : Set) (Rp: (V -> V₂ -> Prop)),
sigT (fun T:Type => sig (fun (f:T) =>
forall pt po, 
let V_R : BestRel V V₂ := {| R:= Rp; Rtot := pt ; Rone := po|} in
JMeq (P V V₂ V_R) f)).

Definition existsAOneFreeImpl {T: forall (V V₂ : Set) (V_R : BestRel V V₂), Type}
(P : forall (V V₂ : Set) (V_R : BestRel V V₂), T V V₂ V_R) : Type :=
forall 
(V V₂ : Set) (Rp: (V -> V₂ -> Prop)) pt,
sigT (fun T:Type => sig (fun (f:T) =>
forall po, 
let V_R : BestRel V V₂ := {| R:= Rp; Rtot := pt ; Rone := po|} in
JMeq (P V V₂ V_R) f)).