

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

Definition existsAGoodnessFreeImpl2 
{T: forall (A A₂ : Set) (A_R : BestRel A A₂) (B B₂ : Set) (B_R : BestRel B B₂), Type}
(P : forall (A A₂ : Set) (A_R : BestRel A A₂)
(B B₂ : Set) (B_R : BestRel B B₂) , T A A₂ A_R B B₂ B_R) : Type :=
forall 
(A A₂ : Set) (Ra: (A -> A₂ -> Prop))
(B B₂ : Set) (Rb: (B -> B₂ -> Prop)),
sigT (fun T:Type => sig (fun (f:T) =>
forall pta poa ptb pob, 
let A_R : BestRel A A₂ := {| R:= Ra; Rtot := pta ; Rone := poa|} in
let B_R : BestRel B B₂ := {| R:= Rb; Rtot := ptb ; Rone := pob|} in
JMeq (P A A₂ A_R B B₂ B_R) f)).

Definition existsAOneFreeImpl2 
{T: forall (A A₂ : Set) (A_R : BestRel A A₂) (B B₂ : Set) (B_R : BestRel B B₂), Type}
(P : forall (A A₂ : Set) (A_R : BestRel A A₂)
(B B₂ : Set) (B_R : BestRel B B₂) , T A A₂ A_R B B₂ B_R) : Type :=
forall 
(A A₂ : Set) (Ra: (A -> A₂ -> Prop)) pta 
(B B₂ : Set) (Rb: (B -> B₂ -> Prop)) ptb,
sigT (fun T:Type => sig (fun (f:T) =>
forall poa pob, 
let A_R : BestRel A A₂ := {| R:= Ra; Rtot := pta ; Rone := poa|} in
let B_R : BestRel B B₂ := {| R:= Rb; Rtot := ptb ; Rone := pob|} in
JMeq (P A A₂ A_R B B₂ B_R) f)).
