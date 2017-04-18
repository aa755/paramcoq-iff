Definition rInv {T1 T2:Set}  (R: T1 -> T2 -> Prop) :=
  fun a b => R b a.


Definition TotalHalf {T1 T2 : Set} (R: T1 -> T2 -> Prop) : Type :=
(forall (t1:T1), @sigT T2 (R t1)).

Definition OneToOneHalf  {A B : Set} (R : A -> B -> Prop) : Prop :=
forall a b1 b2,
  R a b1
  -> R a b2
  ->  b1=b2.

Definition Total {T1 T2 : Set} (R: T1 -> T2 -> Prop) : Type :=
(TotalHalf R) *
(TotalHalf (rInv R)).

Definition OneToOne  {A B : Set} (R : A -> B -> Prop) : Prop :=
OneToOneHalf R /\ (OneToOneHalf (rInv R)).

Require Import SquiggleEq.UsefulTypes.
Require Import SquiggleEq.tactics.

Definition isomorphic (A B : Set) :=
  sigT (fun f: A->B => sigT (fun g: B->A => bijection f g)).

Definition isomorphic2 (A B : Set) : Type :=
  sigT (fun R: A -> B -> Prop => (Total R * OneToOne R)%type).

Section iff.
  Variables (A B: Set).
  Lemma same12: isomorphic A B -> isomorphic2 A B.
  Proof.
    intros Hiso.
    destruct Hiso as [f Hiso].
    destruct Hiso as [g Hiso].
    hnf in Hiso. unfold left_identity in Hiso.
    repnd.
    exists (fun a b => f a = b).
    split; split.
    - intros a. exists (f a). reflexivity.
    - intros b. exists (g b). hnf. auto.
    - intros ? ? ? H1eq H2eq. congruence.
    - intros ? ? ? H1eq H2eq. congruence.
  Qed.

  Lemma same21: isomorphic2 A B -> isomorphic A B.
  Proof.
    intros Hiso.
    destruct Hiso as [R Hiso].
    destruct Hiso as [Tot One].
    unfold Total, OneToOne, TotalHalf, OneToOneHalf in *.
    repnd.
    exists (fun a => projT1 (Tot0 a)).
    exists (fun b => projT1 (Tot b)).
    split; unfold rInv in *.
    - intros a.
      destruct (Tot0 a) as [b ab].
      simpl. destruct (Tot b) as [a' ab'].
      simpl. hnf in ab'. unfold rInv in *. eauto.
    - intros b.
      destruct (Tot b) as [a ab]. 
      simpl. destruct (Tot0 a) as [b' ab'].
      simpl. hnf in ab'. unfold rInv in *. eauto.
  Qed.

End iff.