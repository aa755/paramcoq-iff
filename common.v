
Notation "a <=> b" := (prod (a->b) (b->a)) (at level 100).


Definition rInv {T1 T2 T3: Type} (R: T1 -> T2 -> T3) :=
  fun a b => R b a.

Definition rInvSP {T1 T2}  (R: T1 -> T2 -> Prop) :=
  fun a b => R b a.

Definition TotalHeteroRelHalf {T1 T2 : Type} (R: T1 -> T2 -> Type) : Type :=
(forall (t1:T1), @sigT T2 (R t1)).

(* TODO: rename it to aux *)
Definition IffCompleteHalf {T1 T2 : Prop} (R: T1 -> T2 -> Prop) (t1:T1) : Prop :=
(T2 /\ (forall (t2:T2), R t1 t2)).

(* TODO: make first i capital *)
Definition iffCompleteHalf {T1 T2 : Prop} (R: T1 -> T2 -> Prop) : Prop  := forall (t1:T1),
(T2 /\ (forall (t2:T2), R t1 t2)).

Definition CompleteRel  {A B : Type} (R : A -> B -> Type) : Type :=  (forall (a : A) (b : B), R a b).

(*
Definition CCompleteRel  {A B : Type} (R : A -> B -> Type) : Type
  :=  forall .
*)
Definition TotalHeteroRel {T1 T2 : Type} (R: T1 -> T2 -> Type) : Type :=
(TotalHeteroRelHalf R) *
(TotalHeteroRelHalf (rInv R)).

(* not that this does not even mention the relation *)
Definition IffRel {A B : Type} (_ : A -> B -> Type) : Type
  := (A <=> B).

Definition Prop_R {A B : Prop} (R : A -> B -> Prop) : Type
  := IffRel R * CompleteRel R.

Definition Prop_Rex {A B : Prop} (R : A -> B -> Prop) : Prop 
  := (A <-> B) /\ (exists a b, R a b) (* the later conjunct is crucial. see Prop_RTooWeak below. *).

Definition Prop_RTooWeak := 
fun {A B : Prop} (R : A -> B -> Type) =>  (A <-> B).


Lemma Prop_RTooWeakIsTooWeak {A₁ A₂: Prop} (R : A₁ -> A₂ -> Type):
  TotalHeteroRel R <=> Prop_RTooWeak R.
Proof using.
  intros. split; intros Hyp;
  unfold Prop_RTooWeak; unfold TotalHeteroRel, TotalHeteroRelHalf, rInv in *.
- destruct Hyp. split; intros a; try destruct (s a);  try destruct (s0 a); eauto.
- intros. destruct Hyp. split; intros a.
  + exists (H a). 
  (* R could be fun _ _ => False. So this is not provable.*)
Abort.



Definition symHeteroRelProp (P: forall {T1 T2 : Type}, (T1 -> T2 -> Type)->Type) :=
  forall {T1 T2 : Type} (R : T1 -> T2 -> Type) , P R -> P (rInv R).

Lemma TotalHeteroRelSym  :
symHeteroRelProp (@TotalHeteroRel).
Proof using.
  unfold symHeteroRelProp,TotalHeteroRel.
  tauto.
Qed.

Hint Resolve @TotalHeteroRelSym : rInv.


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



Require Import Coq.Logic.ExtensionalityFacts.

Definition iso (A B : Type) :=
sigT (fun f:A->B => sigT (fun g:B->A => is_inverse f g)).

(* note that this is, even classically, weaker than saying that
A and B are isomorphic. There may be things in A that are not in B.
However, it we also need to qualtify over the polymorphic type,
we would also need HeteroRel. Then, atleast classically,
the two imply isomorphism *)
Definition oneToOneHalf  {A B : Type} (R : A -> B -> Type) : Prop :=
forall a b1 b2,
  R a b1
  -> R a b2
  ->  b1=b2.

Definition oneToOne  {A B : Type} (R : A -> B -> Type) : Prop :=
oneToOneHalf R /\ (oneToOneHalf (rInv R)).

Lemma oneToOneOld {A B : Type} (R : A -> B -> Type):
(forall a1 a2 b1 b2,
  R a1 b1
  -> R a2 b2
  -> (a1=a2 <-> b1=b2))
<-> oneToOne R.
Proof using.
  unfold oneToOne, oneToOneHalf.
  firstorder; subst; eauto;
  eapply H; eauto.
Qed.


Require Import Coq.Setoids.Setoid.

Lemma oneToOneSym:  symHeteroRelProp (@oneToOne).
Proof using.
  unfold symHeteroRelProp, oneToOne, oneToOneHalf, rInv.
  intros. firstorder.
Qed.

Hint Resolve oneToOneSym : rInv.

(* not in use *)
Definition rellIrrUptoIff  {A B : Type} (R : A -> B -> Type)  :=
 forall (TR: forall {a b}, (R a b)->Type) a b (p1 p2: R a b),
  TR p1 -> TR p2.

Require Import SquiggleEq.UsefulTypes.

(*
Lemma relIrrUptoEq  {A B : Type} (R : A -> B -> Type) :
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
*)

(* was something like this needed to define type families in Nuprl? *)
Definition relIrrUptoEq  {A B : Type} (R : A -> B -> Type)  :=
 forall  a b (p1 p2: R a b), p1 = p2.

Definition rellIrrUptoEq4  {A B : Type} (R : A -> B -> Type)  :=
 forall  a1 b1 a2 b2 (p1 : R a1 b1) (p2 : R a2 b2) (e1:a1=a2) (e2:b1=b2),
    p2 = (transport e2 (@transport _ _ _ (fun x => R x b1) e1 p1)).

Lemma rellIrrUptoEq4_implies {A B : Type} (R : A -> B -> Type):
   rellIrrUptoEq4 R ->  relIrrUptoEq R .
Proof.
  intros H4 ? ? ? ?.
  specialize (H4 _ _ _ _ p1 p2 eq_refl eq_refl).
  simpl in H4.
  auto.
Qed.


Lemma irrelSym : 
  symHeteroRelProp (@relIrrUptoEq).
Proof using.
  unfold symHeteroRelProp,relIrrUptoEq, rInv.
  intros. eauto.
Qed.

Hint Resolve irrelSym : rInv.



Definition R_Pi {A1 A2 :Type} {A_R: A1 -> A2 -> Type}
  {B1: A1 -> Type}
  {B2: A2 -> Type} 
  (B_R: forall {a1 a2}, A_R a1 a2 -> (B1 a1) -> (B2 a2) -> Type)
  (f1: forall a, B1 a) (f2: forall a, B2 a) : Type
  :=
  forall a1 a2 (p: A_R a1 a2), B_R p (f1 a1) (f2 a2).

Definition R_PiS {A1 A2 :Set} {A_R: A1 -> A2 -> Prop}
  {B1: A1 -> Set}
  {B2: A2 -> Set} 
  (B_R: forall {a1 a2}, A_R a1 a2 -> (B1 a1) -> (B2 a2) -> Prop)
  (f1: forall a, B1 a) (f2: forall a, B2 a) : Prop
  :=
  forall a1 a2 (p: A_R a1 a2), B_R p (f1 a1) (f2 a2).

Definition R_PiP {A1 A2 :Set} {A_R: A1 -> A2 -> Prop}
  {B1: A1 -> Prop}
  {B2: A2 -> Prop} 
  (B_R: forall {a1 a2}, A_R a1 a2 -> (B1 a1) -> (B2 a2) -> Prop)
  (f1: forall a, B1 a) (f2: forall a, B2 a) : Prop
  :=
  forall a1 a2 (p: A_R a1 a2), B_R p (f1 a1) (f2 a2).

Definition rPiInv 
{A1 A2 :Type} {A_R: A1 -> A2 -> Type}
  {B1: A1 -> Type}
  {B2: A2 -> Type} 
  (B_R: forall a1 a2, A_R a1 a2 -> (B1 a1) -> (B2 a2) -> Type) :=
fun a2 a1 a_R => rInv (B_R a1 a2 a_R).

Definition rPiInvS
{A1 A2 : Set} {A_R: A1 -> A2 -> Prop}
  {B1: A1 -> Set}
  {B2: A2 -> Set} 
  (B_R: forall a1 a2, A_R a1 a2 -> (B1 a1) -> (B2 a2) -> Prop) :=
fun a2 a1 a_R => rInv (B_R a1 a2 a_R).

Lemma rPiInvPreservesSym
(P: forall {T1 T2 : Type}, (T1 -> T2 -> Type)->Type)
(sp: symHeteroRelProp (@P))
{A1 A2 :Type} {A_R: A1 -> A2 -> Type}
  {B1: A1 -> Type}
  {B2: A2 -> Type} 
  {B_R: forall a1 a2, A_R a1 a2 -> (B1 a1) -> (B2 a2) -> Type}
  (trb: forall a1 a2 (p:A_R a1 a2), P (B_R _ _ p)):
 (forall (a1 : A2) (a2 : A1) (p : rInv A_R a1 a2), P (rPiInv B_R a1 a2 p)).
Proof using.
  intros.

  eauto.
Qed.

Ltac rInv
  := (eauto with rInv; unfold rInv, symHeteroRelProp in *; try apply rPiInvPreservesSym;
     simpl; eauto with rInv).

(*
Lemma rPiInvTotal
{A1 A2 :Type} {A_R: A1 -> A2 -> Type}
  {B1: A1 -> Type}
  {B2: A2 -> Type} 
  {B_R: forall a1 a2, A_R a1 a2 -> (B1 a1) -> (B2 a2) -> Type}
  (trb: forall a1 a2 (p:A_R a1 a2), TotalHeteroRel (B_R _ _ p)):
 (forall (a1 : A2) (a2 : A1) (p : rInv A_R a1 a2), TotalHeteroRel (rPiInv B_R a1 a2 p)).
Proof using.
  rInv.
Qed.
*)


(* TODO : put the axiomatic part in a separate file *)


Require Import ProofIrrelevance.

Lemma Prop_RSpec {A₁ A₂: Prop} (R : A₁ -> A₂ -> Prop):
  TotalHeteroRel R <=> Prop_R R.
Proof using.
  intros. split; intros Hyp;
  unfold Prop_R; unfold TotalHeteroRel, TotalHeteroRelHalf, rInv in *.
- destruct Hyp. split.
  + split; intros a; try destruct (s a);  try destruct (s0 a); eauto.
  + intros a b. destruct (s a).
    pose proof (proof_irrelevance _ x b). subst. assumption.
- intros. destruct Hyp. split; intros a; firstorder; eauto.
Qed.


Lemma iffHalfTotal (A1 A2:Prop) (AR : A1 -> A2 -> Prop)
           (tot12 : iffCompleteHalf AR)
           (tot21 : iffCompleteHalf (rInvSP AR))
  : TotalHeteroRel AR.
Proof.
  apply Prop_RSpec.
  - split;[split|].
    + intros  Hh. apply tot12 in Hh. assumption.
    + intros  Hh. apply tot21 in Hh. assumption.
    + intros x y. destruct (tot12 x) as [_ Hh]. apply Hh.
Defined. 


Lemma Prop_RexSpec {A₁ A₂: Prop} (R : A₁ -> A₂ -> Prop):
  TotalHeteroRel R <=> Prop_Rex R.
Proof using.
  intros. split; intros Hyp;
  unfold Prop_R; unfold TotalHeteroRel, TotalHeteroRelHalf, rInv in *.
- destruct Hyp. split.
  + split; intros a; try destruct (s a);  try destruct (s0 a); eauto.
  + intros.
Abort.

Lemma propeOneToOne {A₁ A₂: Prop} (R : A₁ -> A₂ -> Prop):
  oneToOne R.
Proof using.
  unfold oneToOne, oneToOneHalf.
  split; intros; apply proof_irrelevance.
Qed.

Lemma tiffIff (P1 P2 : Prop): P1 <-> P2 <=> (P1 <=> P2).
Proof using.
  intros. tauto.
Defined.

Section Temp.
Variable A:Type.
Variable B:A->Prop.
Variable C:Set->Prop.
Variable D:Type->Prop.
Check ((forall (a:A), B a):Prop).
Check ((forall (a:Set), C a):Prop).
(* we will not be able to handle the case below because the relations for type 
dont have goodness props *)
Check ((forall (a:Type), D a):Prop).
End Temp.






