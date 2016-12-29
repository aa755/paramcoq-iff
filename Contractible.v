

Set Implicit Arguments.

Definition Contractible (T:Type):= forall (a b:T), a=b.

Section UP_iso.
  Variables A B : Type.
  Variable AtoB : A -> B.
  Variable BtoA : B -> A.

  Hypothesis AtoB_BtoA : forall a, AtoB (BtoA a) = a.
  Hypothesis A_UP : Contractible A.

  Theorem UP_iso : Contractible B.
  Proof.
    intros. unfold Contractible. intros.
    rewrite <- (AtoB_BtoA a).
    rewrite <- (AtoB_BtoA b).
    f_equal.
    apply A_UP.
  Qed.
End UP_iso.

