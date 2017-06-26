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

Require Import SquiggleEq.tactics.

Definition left_identity {S T : Type} (f: S -> T) (g: T-> S): Prop :=
  forall s: S , (g (f s)) = s.

Definition isomorphic (A B : Set)  :=
  sigT (fun f: A->B => sig (fun g: B->A =>  left_identity f g /\ left_identity g f)).

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

Print sigT.


Inductive sigTS (A : Set) (P : A -> Prop) : Prop :=  existT : forall x : A, P x -> sigTS A P.
Inductive sigTS2 (A : Set) (P : A -> Type) : Prop :=  existT2 : forall x : A, P x -> sigTS2 A P.

(*
Definition isomorphic3 (A B : Set) : Type := *)

Fail Check  (fun (A B : Set) => sigTS _ (fun R: A -> B -> Prop => (Total R * OneToOne R)%type)).
(*
The term "(Total R * OneToOne R)%type" has type "Type" while it is expected to have type 
"Prop" (universe inconsistency).
 *)

Fail Check  (fun (A B : Set) => sigTS2 _ (fun R: A -> B -> Prop => (Total R * OneToOne R)%type)).
(*
The term "sigTS2" of type "forall A : Set, (A -> Type) -> Prop"
cannot be applied to the terms
 "A -> B -> Prop" : "Type"
 "fun R : A -> B -> Prop => (Total R * OneToOne R)%type" : "(A -> B -> Prop) -> Type"
The 1st term has type "Type" which should be coercible to "Set".
 *)

Check  (fun (A B : Set) => sigTS (A->B) (fun f: A -> B => sigTS (B->A) (fun g => left_identity f g /\ left_identity g f ))).

Goal False.
  set (t:= isomorphic).
  unfold isomorphic in t.
  unfold left_identity in t.
Abort.