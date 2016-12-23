Require Import common.



Definition R_Fun {A1 A2 :Type} (A_R: A1 -> A2 -> Type)
  {B1 B2: Type}
  (B_R: B1 -> B2 -> Type)
  (f1: A1->B1) (f2: A2->B2) : Type
  :=
  @R_Pi A1 A2 A_R (fun _ => B1) (fun _ => B2)
  (fun _ _ _ => B_R) f1 f2.



(* the case of non-dependent functions is interesting because no extra 
[irrel] hypothesis is needed.*)
Lemma totalFun (A1 A2 :Type) (A_R: A1 -> A2 -> Type) 
  {B1 B2: Type}
  (B_R: B1 -> B2 -> Type)
  (trp : TotalHeteroRel A_R)
  (trb: TotalHeteroRel B_R)
  (oneToOneA_R: oneToOne A_R)
:
  TotalHeteroRel (R_Fun A_R B_R).
Proof.
  split.
- intros f1. apply snd in trp.
  eexists.
  Unshelve.
    Focus 2.
    intros a2. specialize (trp a2).
     destruct trp as [a11 ar].
    apply fst in trb.
    specialize (trb (f1 a11)).
    exact (projT1  trb).

  simpl.
  intros ? ? ?.
  destruct (trp a2) as [a1r ar].
  destruct (trb) as [b2 br].
  simpl.
  destruct (b2 (f1 a1r)). simpl.
  pose proof (proj2 oneToOneA_R _ _ _ _ p ar eq_refl).
  (* it may be possible to acheive this using univalence ase well
    A_R composed with A_R inv will be an isomorphism, thuse we can show a1=a1r. *)

  subst.
  assumption.
- intros f1. apply fst in trp.
  eexists.
  Unshelve.
    Focus 2.
    intros a2. specialize (trp a2).
     destruct trp as [a11 ar].
    apply snd in trb.
    specialize (trb (f1 a11)).
    exact (projT1  trb).

  simpl.
  intros a2 ? p.
  destruct (trp a2) as [a1r ar].
  destruct (trb) as [b2 br].
  simpl.
  destruct (br (f1 a1r)). simpl.
  pose proof (proj1 oneToOneA_R _ _ _ _ p ar eq_refl).
  subst.
  assumption.
Qed.

Require Import Coq.Logic.FunctionalExtensionality.

Lemma oneToOnePi (A1 A2 :Type) (A_R: A1 -> A2 -> Type) 
  (B1: A1 -> Type) 
  (B2: A2 -> Type) 
  (B_R: forall a1 a2, A_R a1 a2 -> (B1 a1) -> (B2 a2) -> Type)
  (tra : TotalHeteroRel A_R) 
  (oneToOneB_R: forall a1 a2 (a_r : A_R a1 a2), oneToOne (B_R a1 a2 a_r))
:
  oneToOne (R_Pi B_R).
Proof.
  split;intros f1 g1 f2 g2 H1r H2r;
  unfold R_Fun, R_Pi in *;
  intros Heq;subst; apply functional_extensionality_dep.
- intros a2.
  destruct (snd tra a2) as [a1 a1r].
  specialize (H2r _ _ a1r).
  specialize (H1r _ _ a1r).
  pose proof (proj1 (oneToOneB_R _ _ _) _ _ _ _ H2r H1r eq_refl).
  auto.
- intros a2.
  destruct (fst tra a2) as [a1 a1r].
  specialize (H2r _ _ a1r).
  specialize (H1r _ _ a1r).
  pose proof (proj2 (oneToOneB_R _ _ _) _ _ _ _ H2r H1r eq_refl).
  auto.
Qed.


Lemma totalPiHalf (A1 A2 :Type) (A_R: A1 -> A2 -> Type) 
  (trp : TotalHeteroRel A_R) 
  (B1: A1 -> Type) 
  (B2: A2 -> Type) 
  (B_R: forall a1 a2, A_R a1 a2 -> (B1 a1) -> (B2 a2) -> Type)
  (trb: forall a1 a2 (p:A_R a1 a2), TotalHeteroRel (B_R _ _ p))
  (oneToOneA_R: oneToOne A_R)
  (irrel : relIrrUptoEq A_R)
:
  TotalHeteroRelHalf (R_Pi B_R).
Proof.
  intros f1. apply snd in trp.
  eexists.
  Unshelve.
    Focus 2.
    intros a2. specialize (trp a2).
    destruct trp as [a1 ar]. (* this step fails with TotalHeteroRelP *)
    specialize (trb _ _ ar).
    apply fst in trb.
    specialize (trb (f1 a1)).
    exact (projT1 trb).

  simpl.
  intros ? ? par. (** [par] comes from intros in the Totality proof *)
  destruct (trp a2) as [a11 far].
  unfold rInv in far.
  (** [far] was obtained by destructing [trb] in the exhibited function.
     Right now, the types of [par] and [dar] are not even same ([a11] vs [a1]).*)
  pose proof (proj2 oneToOneA_R _ _ _ _ par far eq_refl) as Heq.
  (* it may be possible to acheive this using univalence ase well
    A_R composed with A_R inv will be an isomorphism, thuse we can show a1=a1r. *)

  symmetry in Heq. subst.
  destruct (trb a1 a2 far) as [b2 br].
  simpl.
  destruct (b2 (f1 a1)). simpl.
  (* now the types of [far] and [par] are same. 
  Why would they be same, though? In Nuprl2Coq,
  pers were into Prop. So, this issue didnt arise.
  Even the predicative version, there was a global invariang that for 
  same types, equalities were iff.
  
  In Nuprl, becuause the types of B_R a1 a2 far and
  B_R a1 a2 par are same, the global invariant 1) uniquely valued (<=2=>) will imply this
  subgoal.

  We can change the translation of Prod to be a record, with a new element which is a 
  proof that B_R is independent of the proof on A.
  oneToOne will be needed anyway and that would force us to used the univalent
  interpretation.
  *)
  specialize (irrel _ _ par far).
  subst. assumption.
Defined.

Print Assumptions totalPiHalf.



Require Import Coq.Setoids.Setoid.


Lemma totalPi (A1 A2 :Type) (A_R: A1 -> A2 -> Type) 
  (trp : TotalHeteroRel A_R) 
  (B1: A1 -> Type) 
  (B2: A2 -> Type) 
  (B_R: forall a1 a2, A_R a1 a2 -> (B1 a1) -> (B2 a2) -> Type)
  (trb: forall a1 a2 (p:A_R a1 a2), TotalHeteroRel (B_R _ _ p))
  (oneToOneA_R: oneToOne A_R)
  (irrel : relIrrUptoEq A_R)
:
  TotalHeteroRel (R_Pi B_R).
Proof.
  split.
- apply totalPiHalf; auto.
- pose proof (@totalPiHalf _ _ (rInv A_R) ltac:(rInv) B2 B1 (rPiInv B_R)
     ltac:(rInv) ltac:(rInv) ltac:(rInv)).
  unfold R_Pi, rPiInv, rInv in *.
  intros ?.
  unfold TotalHeteroRelHalf in X.
  intros.
  destruct X with (t1:=t1).
  eexists; intros; eauto.
Qed.



Lemma irrelEqPi (A1 A2 :Type) (A_R: A1 -> A2 -> Type) 
  (trp : TotalHeteroRel A_R) 
  (B1: A1 -> Type) 
  (B2: A2 -> Type) 
  (B_R: forall a1 a2, A_R a1 a2 -> (B1 a1) -> (B2 a2) -> Type)
  (trb: forall a1 a2 (p:A_R a1 a2), TotalHeteroRel (B_R _ _ p))
  (irrelB: forall a1 a2 (a_r : A_R a1 a2), relIrrUptoEq (B_R a1 a2 a_r))
:
  relIrrUptoEq (R_Pi B_R).
Proof.
  intros f1 f2 ? ?.
  unfold R_Pi in *.
  apply functional_extensionality_dep.
  intros a1.
  apply functional_extensionality_dep.
  intros a2.
  apply functional_extensionality_dep.
  intros ar.
  apply irrelB.
Qed.

(* The same holds for IWT -- see PIW.v *)


Require Import ProofIrrelevance.


Lemma oneToOnePiProp (A1 A2 :Type) (A_R: A1 -> A2 -> Type) 
  (B1: A1 -> Prop) 
  (B2: A2 -> Prop) 
  (B_R: forall a1 a2, A_R a1 a2 -> (B1 a1) -> (B2 a2) -> Prop)
(* Not needed for the Prop version
  (tra : TotalHeteroRel A_R)
  (oneToOneB_R: forall a1 a2 (a_r : A_R a1 a2), oneToOne (B_R a1 a2 a_r))
*)
:
  oneToOne (R_Pi B_R).
Proof.
  split; intros f1 g1 f2 g2 H1r H2r;
  unfold R_Fun, R_Pi in *;
  intros H; apply proof_irrelevance.
Qed.


Lemma propForalClosedP {A₁ A₂ : Type} (B₁: A₁ -> Prop) (B₂: A₂ -> Prop)
(A_R : A₁ -> A₂ -> Type) (tra: TotalHeteroRel A_R)
  (trb: forall
       a₁ a₂,
          A_R a₁ a₂ -> (B₁ a₁ <-> B₂ a₂)):
(forall a : A₁, B₁ a) <-> (forall a : A₂, B₂ a).
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

Lemma totalPiHalfProp (A1 A2 :Type) (A_R: A1 -> A2 -> Type) 
  (B1: A1 -> Prop) 
  (B2: A2 -> Prop) 
  (B_R: forall a1 a2, A_R a1 a2 -> (B1 a1) -> (B2 a2) -> Prop)
  (trp : TotalHeteroRel A_R) 
  (trb: forall a1 a2 (p:A_R a1 a2), TotalHeteroRel (B_R _ _ p))
(*  (oneToOneA_R: oneToOne A_R)
  (irrel : relIrrUptoEq A_R) *)
:
  TotalHeteroRel (R_Pi B_R).
Proof.
  unfold R_Pi.
  apply ((fun A B R => snd (@Prop_RSpec A B R))).
  unfold Prop_R.
  split.
  - apply propForalClosedP with (A_R0 := A_R);[assumption|].
    intros ? ? p.
    specialize (trb _ _ p).
    apply ((fst (@Prop_RSpec _ _ _) trb)).
  - intros f g ? ? p.
    specialize (trb _ _ p).
    pose proof ((fst (@Prop_RSpec _ _ _) trb)) as Hp.
    apply Hp.
Qed.
