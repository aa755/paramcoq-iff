Require Import SquiggleEq.list.
Require Import SquiggleEq.UsefulTypes.
Require Import common.
Require Import SquiggleEq.tactics.

Arguments memberb {_} {_} x l.

Set Implicit Arguments.

(* transparent lemma for computations. Move to SquiggleEq *)
Lemma subsetb_memberb {T:Type} {dt :Deq T} (l1 l2 : list T):
  (subsetb _ l1 l2 = true)
  -> forall t, (memberb t l1) = true -> (memberb t l2) = true.
Proof using.
  intros  Hs ? Hm.
  remember (memberb t l2) as m2. symmetry in Heqm2.
  destruct m2;[reflexivity|].
  apply False_rect.
  setoid_rewrite assert_subsetb in Hs.
  setoid_rewrite assert_memberb in Hm.
  apply Bool.not_true_iff_false in Heqm2.
  setoid_rewrite assert_memberb in Heqm2.
  eauto.
Defined.

(*Prop is also considered a type here.*)
Inductive Props : Set := Total | OneToOne | Irrel.
Definition allProps : list Props := [Total; OneToOne ; Irrel].

Global Instance deq : Deq Props.
Proof using.
  apply @deqAsSumbool.
  unfold DeqSumbool. intros. unfold DecidableSumbool.
  repeat decide equality.
Defined.

Universe i.

Notation univ := (Type@{i}) (only parsing).


Polymorphic  Record GoodRel (select: list Props)
 (T₁ T₂: univ)  : Type (* nececcarily bigger than Set if univ, because of R*) :=
{
  R : T₁ -> T₂ -> univ;
  Rtot : if (memberb Total select) then TotalHeteroRel R else True;
  Rone : if (memberb OneToOne select) then oneToOne R else True;
  Rirrel : if (memberb Irrel select) then relIrrUptoEq R else True;
}.

Check (GoodRel allProps (True:Prop) (True:Prop)):Type.

Fail Check (GoodRel allProps (nat:Set) (nat:Set)):Set (* because of R, this has to be atleast 1 bigger than Set*).


Definition eraseRP  (sb ss: list Props)
  (sub: subsetb _ ss sb=true) (T₁ T₂:univ) (gb: GoodRel sb T₁ T₂ ) :
    (GoodRel ss T₁ T₂ ).
Proof.
  destruct gb.
  apply Build_GoodRel with (R:= R0);
  apply' subsetb_memberb sub.
- specialize (sub Total).
  destruct (memberb _ ss);[| exact I].
  specialize (sub eq_refl). rewrite sub in Rtot0.
  assumption.
- specialize (sub OneToOne).
  destruct (memberb _ ss);[| exact I].
  specialize (sub eq_refl). rewrite sub in Rone0.
  assumption.
- specialize (sub Irrel).
  destruct (memberb _ ss);[| exact I].
  specialize (sub eq_refl). rewrite sub in Rirrel0.
  assumption.
Defined.


Definition BestRel := GoodRel allProps.
Definition BestR := @R allProps.

