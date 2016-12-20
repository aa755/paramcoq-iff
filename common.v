
Notation "a <=> b" := (prod (a->b) (b->a)) (at level 100).

Definition rInv {T1 T2 T3: Type} (R: T1 -> T2 -> T3) :=
  fun a b => R b a.

Definition TotalHeteroRelHalf {T1 T2 : Type} (R: T1 -> T2 -> Type) : Type :=
(forall (t1:T1), @sigT T2 (R t1)).


Definition TotalHeteroRel {T1 T2 : Type} (R: T1 -> T2 -> Type) : Type :=
(TotalHeteroRelHalf R) *
(TotalHeteroRelHalf (rInv R)).


Definition Prop_R {A B : Prop} (R : A -> B -> Prop) : Prop 
 := (A <-> B) /\ (forall a b, R a b).


Lemma TotalHeteroRelSym {T1 T2 : Type} (R: T1 -> T2 -> Type) : 
  TotalHeteroRel R ->  TotalHeteroRel (rInv R).
Proof using.
  unfold TotalHeteroRel.
  tauto.
Qed.

(*
Lemma propForalClosedP (P: forall {A:Type}, A -> Prop)
  (trb: forall {A₁ A₂ : Type} (A_R : A₁ -> A₂ -> Type) 
      (tra: TotalHeteroRel A_R) a₁ a₂,
          A_R a₁ a₂ -> (P a₁ <-> P a₂)):
   let newP (A:Type):= (forall a:A, P a) in
   forall  {A₁ A₂ : Type} (A_R : A₁ -> A₂ -> Type) 
      (tra: TotalHeteroRel A_R), newP A₁ <-> newP A₂.
Proof using.
  simpl. intros.
  split; intros Hyp; intros a.
- destruct (snd tra a) as [ap]. unfold rInv in r.
  specialize (Hyp ap). eapply trb in r; eauto.
  tauto.
- destruct (fst tra a) as [ap]. rename a0 into r. unfold rInv in r.
  specialize (Hyp ap). eapply trb in r; eauto.
  tauto.
Qed.
*)

Declare ML Module "paramcoq".


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
Abort. (* not provable *)

Lemma sigT_sigTP  (A : Type) (P : A -> Type) :
  @sigT A P -> sigTP A P.
Proof using.
  intros X. destruct X. econstructor; eauto.
Qed.

Lemma implies_TotalHeteroRelP {T1 T2 : Type} (R: T1 -> T2 -> Type) :
  TotalHeteroRelP R -> TotalHeteroRel R.
Proof.
  unfold  TotalHeteroRel, TotalHeteroRelHalf, TotalHeteroRelP.
  firstorder.
Abort. (* not provable *)

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
Definition oneToOne  {A B : Type} (R : A -> B -> Type) : Prop :=
forall a1 a2 b1 b2,
  R a1 b1
  -> R a2 b2
  -> (a1=a2 <-> b1=b2).

Require Import Coq.Setoids.Setoid.

Lemma oneToOneSym {T1 T2 : Type} {R: T1 -> T2 -> Type} : 
  oneToOne R ->  oneToOne (rInv R).
Proof using.
  unfold oneToOne, rInv.
  intros.
  rewrite H; eauto.
  reflexivity.
Qed.

(* not in use *)
Definition rellIrrUptoIff  {A B : Type} (R : A -> B -> Type)  :=
 forall (TR: forall {a b}, (R a b)->Type) a b (p1 p2: R a b),
  TR p1 -> TR p2.

Require Import SquiggleEq.UsefulTypes.

Lemma rellIrrUptoEq  {A B : Type} (R : A -> B -> Type) :
rellIrrUptoIff R ->
forall a b (p1 p2: R a b), p1=p2.
Proof using.
  intros Hr ? ? ? ?.
  specialize (Hr (fun a' b' p => forall (pa:a = a') (pb:b=b'), p= 
    transport pb (@transport _ _ _ (fun x => R x b) pa p1)) a b p1 p2
    ).
  simpl in Hr.
  specialize (fun p => Hr p eq_refl eq_refl). simpl in Hr.
  symmetry. apply Hr.
  intros. unfold transport.
  (* need UIP_refl to finish the proof *)
Abort.

(* was something like this needed to define type families in Nuprl? *)
Definition rellIrrUptoEq  {A B : Type} (R : A -> B -> Type)  :=
 forall  a b (p1 p2: R a b), p1 = p2.

Definition rellIrrUptoEq4  {A B : Type} (R : A -> B -> Type)  :=
 forall  a1 b1 a2 b2 (p1 : R a1 b1) (p2 : R a2 b2) (e1:a1=a2) (e2:b1=b2),
    p2 = (transport e2 (@transport _ _ _ (fun x => R x b1) e1 p1)).

Lemma rellIrrUptoEq4_implies {A B : Type} (R : A -> B -> Type):
   rellIrrUptoEq4 R ->  rellIrrUptoEq R .
Proof.
  intros H4 ? ? ? ?.
  specialize (H4 _ _ _ _ p1 p2 eq_refl eq_refl).
  simpl in H4.
  auto.
Qed.


Lemma irrelSym {T1 T2 : Type} {R: T1 -> T2 -> Type}: 
  rellIrrUptoEq R ->  rellIrrUptoEq (rInv R).
Proof using.
  unfold rellIrrUptoEq, rInv.
  intros. eauto.
Qed.

(* TODO : put the axiomatic part in a separate file *)


Require Import ProofIrrelevance.

Lemma Prop_RSpec {A₁ A₂: Prop} (R : A₁ -> A₂ -> Prop):
  TotalHeteroRel R <=> Prop_R R.
Proof using.
  intros. split; intros Hyp;
  unfold Prop_R; unfold TotalHeteroRel, TotalHeteroRelHalf, rInv in *.
- destruct Hyp. split.
  + split; intros a; try destruct (s a);  try destruct (s0 a); eauto.
  + intros. destruct (s a).
    pose proof (proof_irrelevance _ x b). subst. assumption.
- intros. destruct Hyp. split; intros a; firstorder; eauto.
Qed.






