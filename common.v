Declare ML Module "paramcoq".

Notation "a <=> b" := (prod (a->b) (b->a)) (at level 100).

Definition USP 
{A₁ A₂ : Type} (A_R : A₁ -> A₂ -> Type) :Type :=
 forall x y (p1 p2: A_R x y), p1 = p2.

Parametricity Recursive eq.

Lemma eq_R_if : forall
  (A₁ A₂ : Type) (A_R : A₁ -> A₂ -> Type) 
  (A_R_USP : USP A_R)
  (x₁ px₁ : A₁) (x₂ px₂: A₂) 
  (x_R : A_R x₁ x₂) (px_R : A_R px₁ px₂) (p1 : x₁ = px₁) (p2: x₂ = px₂) ,
eq_R A₁ A₂ A_R x₁ x₂ x_R px₁ px₂ px_R p1 p2.
Proof using.
  intros. subst.
  pose proof (A_R_USP _ _ px_R x_R). subst.
  constructor.
Qed.


Definition TotalHeteroRel {T1 T2 : Type} (R: T1 -> T2 -> Type) : Type :=
(forall (t1:T1), @sigT T2 (R t1))*
(forall (t2:T2), @sigT _ (fun t1:T1 => R t1 t2)).

Inductive sigTP (A : Type) (P : A -> Type) : Prop :=
    existTP : forall x : A, P x -> sigTP A P.

Lemma sigTP_ex  (A : Type) (P : A -> Prop) :
  @sigTP A P <-> @ex A P.
Proof using.
  split; intros X; destruct X; econstructor; eauto.
Qed.

Definition TotalHeteroRelP {T1 T2 : Type} (R: T1 -> T2 -> Type) : Prop :=
(forall (t1:T1), @sigTP T2 (R t1))*
(forall (t2:T2), @sigTP _ (fun t1:T1 => R t1 t2)).

Lemma sigT_sigTP  (A : Type) (P : A -> Type) :
  @sigTP A P -> @sigT A P.
Proof using.
  intros X.
  Fail destruct X.
Abort.

Lemma sigT_sigTP  (A : Type) (P : A -> Type) :
  @sigT A P -> sigTP A P.
Proof using.
  intros X. destruct X. econstructor; eauto.
Qed.

Lemma implies_TotalHeteroRelP {T1 T2 : Type} (R: T1 -> T2 -> Type) :
  TotalHeteroRelP R -> TotalHeteroRel R.
Proof.
  unfold  TotalHeteroRel, TotalHeteroRelP.
  firstorder.
Abort.

Lemma implies_TotalHeteroRelP {T1 T2 : Type} (R: T1 -> T2 -> Type) :
  TotalHeteroRel R -> TotalHeteroRelP R.
Proof.
  unfold  TotalHeteroRel, TotalHeteroRelP.
  firstorder.
Qed.

Parametricity Recursive nat.

Lemma nat_R_eq : forall x y , nat_R x y <=> x = y.
Proof.
  induction x; intros y; split; intros Hy; subst; try inversion Hy; auto.
- constructor.
- subst. apply IHx in H2. congruence.
- constructor. apply IHx. reflexivity.
Qed.

Parametricity Recursive bool.
Lemma bool_R_eq : forall x y , bool_R x y <=> x = y.
Proof.
  induction x; intros y; split; intros Hy; subst; try inversion Hy; auto;
constructor.
Qed.

Lemma nat_R_refl : forall t, nat_R t t.
Proof. 
  intros. apply nat_R_eq. reflexivity.
Qed.

Require Import Coq.Logic.ExtensionalityFacts.

Definition iso (A B : Type) :=
sigT (fun f:A->B => sigT (fun g:B->A => is_inverse f g)).

(* note that this is, even classically, weaker than saying that
A and B are isomorphic. There may be things in A that are not in B.
However, it we also need to qualtify over the polymorphic type,
we would also need HeteroRel. Then, atleast classically,
the two imply isomorphism *)
Definition relIso  {A B : Type} (R : A -> B -> Type) : Prop :=
forall a1 a2 b1 b2,
  R a1 b1
  -> R a2 b2
  -> (a1=a2 <-> b1=b2).
