
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
  (* extras *)  
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

Print Assumptions oneToOnePi.
(*
Axioms:
functional_extensionality_dep : forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
                                (forall x : A, f x = g x) -> f = g
 *)

Lemma totalPiHalfAux (A1 A2 :Type) (A_R: A1 -> A2 -> Type) 
  (trp : TotalHeteroRelHalf (rInv A_R)) 
  (B1: A1 -> Type) 
  (B2: A2 -> Type) 
  (B_R: forall a1 a2, A_R a1 a2 -> (B1 a1) -> (B2 a2) -> Type)
  (trb: forall a1 a2 (p:A_R a1 a2), TotalHeteroRelHalf (B_R _ _ p))
  (oneToOneA_R: oneToOne A_R)
  (irrel : relIrrUptoEq A_R)
:
  TotalHeteroRelHalf (R_Pi B_R).
Proof.
  intros f1.
  eexists.
  Unshelve.
    Focus 2.
    intros a2. specialize (trp a2).
    destruct trp as [a1 ar]. (* this step fails with TotalHeteroRelP *)
    specialize (trb _ _ ar).
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
  simpl.
  destruct (trb a1 a2 far (f1 a1)). simpl.
  (* now the types of [far] and [par] are same. 
  Why would they be same, though? 

  In Nuprl2Coq,
  pers were into Prop. So, this issue didnt arise.
  Even the predicative version, there was a global invariant that for 
  same types, equalities were iff. In Nuprl, becuause the types of B_R a1 a2 far and
  B_R a1 a2 par are same, the global invariant 1) uniquely valued (<=2=>) will imply this
  subgoal.

  Unlike Nuprl, where each pair of equal types had ONE unque PER, parametricity, by design, allows
  different relations between types denoting related implementations. Even in this isorel translation,
  we want to allow different isomorphisms.
  NEW: consider A:=Type, B:=(fun A:Type => A). clearly, B A1 A2 AR depends on AR, because it IS AR

  Doesn't make sense anymore: We can change the translation of Prod to be a record, with a new element which is a 
  proof that B_R is independent of the proof on A.
  oneToOne will be needed anyway and that would force us to used the univalent
  interpretation. 

  *)
  specialize (irrel _ _ par far).
  subst. assumption.
Defined.


Lemma totalPiHalf (A1 A2 :Type) (A_R: A1 -> A2 -> Type) 
  (trp : TotalHeteroRel A_R) 
  (B1: A1 -> Type) 
  (B2: A2 -> Type) 
  (B_R: forall a1 a2, A_R a1 a2 -> (B1 a1) -> (B2 a2) -> Type)
  (* extras *)
  (trb: forall a1 a2 (p:A_R a1 a2), TotalHeteroRel (B_R _ _ p))
  (oneToOneA_R: oneToOne A_R)
  (irrel : relIrrUptoEq A_R)
:
  TotalHeteroRelHalf (R_Pi B_R).
Proof.
  apply totalPiHalfAux; auto.
  - apply trp.
  - apply trb.
Defined.


Require Import Coq.Setoids.Setoid.


Lemma totalPi (A1 A2 :Type) (A_R: A1 -> A2 -> Type) 
  (B1: A1 -> Type) 
  (B2: A2 -> Type) 
  (B_R: forall a1 a2, A_R a1 a2 -> (B1 a1) -> (B2 a2) -> Type)
  (* extras *)
  (trp : TotalHeteroRel A_R) 
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

Print Assumptions totalPi.
(*
Closed under the global context
 *)


Lemma irrelEqPi (A1 A2 :Type) (A_R: A1 -> A2 -> Type) 
  (trp : TotalHeteroRel A_R) 
  (B1: A1 -> Type) 
  (B2: A2 -> Type) 
  (B_R: forall a1 a2, A_R a1 a2 -> (B1 a1) -> (B2 a2) -> Type)
  (* extras *)
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

Print Assumptions irrelEqPi.

(* The same holds for IWT -- see PIW.v *)

Require Import Trecord.

(* does not use proof irrelevance. This mentions a universe. Fix *)
Lemma PiGoodSet :
  forall (A1 A2 :Set) (A_R: BestRel A1 A2) 
  (B1: A1 -> Set) 
  (B2: A2 -> Set) 
  (B_R: forall a1 a2, BestR A_R a1 a2 -> BestRel (B1 a1) (B2 a2)),
  BestRel (forall a : A1, B1 a) (forall a : A2, B2 a).
Proof using.
  intros.
  exists  (fun (f1 : forall a : A1, B1 a) (f2 : forall a : A2, B2 a) =>
forall (a1 : A1) (a2 : A2) (p : BestR A_R a1 a2), BestR  (B_R a1 a2 p) (f1 a1) (f2 a2)
); simpl in *;
  destruct A_R; simpl in *;
  rename R into A_R.
- apply totalPi; (* needs all 3 on A *) eauto;[].
  intros a1 a2 ar. destruct (B_R a1 a2 ar). (* needs totality on B_R*) assumption.
- apply oneToOnePi; eauto.
  intros a1 a2 ar. destruct (B_R a1 a2 ar). (* needs oneToOne on B_R *) assumption.
- apply irrelEqPi; eauto; (* needs totality and irrel on B_R *)
  intros a1 a2 ar; destruct (B_R a1 a2 ar); assumption.
Defined.
Require Import List.
Import ListNotations.

Lemma totalPiHalfGood (A1 A2 :Set) (A_R: BestRel A1 A2) 
  (B1: A1 -> Set) 
  (B2: A2 -> Set) 
  (B_R: forall a1 a2, BestR A_R a1 a2 -> (B1 a1) -> (B2 a2) -> Prop)
  (trb: forall a1 a2 (p:BestR A_R a1 a2), TotalHeteroRelHalf (B_R _ _ p))
:
  TotalHeteroRelHalf (R_PiS B_R).
Proof.
  apply totalPiHalfAux; auto.
  - apply (Rtot A_R).
  - apply (Rone A_R).
  - apply (Rirrel A_R).
Defined.

Definition totalPiHalfGood2 :=
Eval compute in totalPiHalfGood.
Print totalPiHalfGood2. (* No universes *)

Definition PiGoodSet2 :=
Eval compute in PiGoodSet.

Print PiGoodSet2. (* No universes *)

Require Import ProofIrrelevance.

(*
This works when R in GoodRel has sort Prop.
Lemma PiTSummary 
  (A1 A2 :Set) (A_R: BestRel A1 A2) 
  (B1: A1 -> Set) 
  (B2: A2 -> Set) 
  (B_R: forall a1 a2, BestR A_R a1 a2 -> BestRel (B1 a1) (B2 a2))
  :
  BestRel (forall a : A1, B1 a) (forall a : A2, B2 a).
Proof using.
  exists  (fun (f1 : forall a : A1, B1 a) (f2 : forall a : A2, B2 a) =>
forall (a1 : A1) (a2 : A2) (p : BestR A_R a1 a2), BestR (B_R a1 a2 p) (f1 a1) (f2 a2)
); simpl;
  destruct A_R; simpl in *;
  rename R into A_R.
- apply totalPi; (* needs all 3 on A *) eauto.
  + intros a1 a2 ar. destruct (B_R a1 a2 ar). (* needs totality on B_R*) assumption.
  + intros ? ? ? ?. apply proof_irrelevance.
- apply oneToOnePi; eauto.
  intros a1 a2 ar. destruct (B_R a1 a2 ar). (* needs oneToOne on B_R *) assumption.
- exact I.
Defined.
*)




(** Now the Prop verion *)

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
  Check (forall a:A1, B1 a):Prop.
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


Lemma propForalClosedP2 {A₁ A₂ : Type} (B₁: A₁ -> Prop) (B₂: A₂ -> Prop)
(A_R : A₁ -> A₂ -> Type) (tra: TotalHeteroRel A_R)
  (trb: forall
       a₁ a₂,
          A_R a₁ a₂ -> (B₁ a₁ <=> B₂ a₂)):
(forall a : A₁, B₁ a) <=> (forall a : A₂, B₂ a).
Proof using.
  simpl. intros.
  split; intros Hyp; intros a.
- destruct (snd tra a) as [ap]. unfold rInv in r.
  specialize (Hyp ap). eapply trb in r. (* this need proof that the ARs are related *)
  tauto.
- destruct (fst tra a) as [ap]. rename a0 into r. unfold rInv in r.
  specialize (Hyp ap). eapply trb in r; eauto.
  tauto.
Qed.

Lemma propForalClosedP3 (A1 A2 :Type) (A_R: A1 -> A2 -> Type) 
  (B1: A1 -> Prop) 
  (B2: A2 -> Prop) 
  (B_R: forall a1 a2, A_R a1 a2 -> (B1 a1) -> (B2 a2) -> Type)
  (* extras *)
  (trp : TotalHeteroRel A_R) 
  (trb: forall a1 a2 (p:A_R a1 a2), IffRel (B_R _ _ p))
:
  IffRel (R_Pi B_R).
Proof.
  apply propForalClosedP2 with (A_R0 := A_R); auto.
Defined.

Lemma propForalClosedP4 (A1 A2 :Type) (A_R: A1 -> A2 -> Type) 
  (B1: A1 -> Prop) 
  (B2: A2 -> Prop) 
  (B_R: forall a1 a2, A_R a1 a2 -> (B1 a1) -> (B2 a2) -> Type)
  (* extras *)
  (tra : IffRel A_R) 
  (trb: forall a1 a2 (p:A_R a1 a2), IffRel (B_R _ _ p))
:
  IffRel (R_Pi B_R).
Proof.
  unfold IffRel in *.
  simpl in *. intros.
  split; intros Hyp; intros a.
  Fail tauto.
  Fail (firstorder; fail).
  (* Because the iff part of B is only accessible AFTER providing the ar argument,
    this is not provable. we need totality of A_R, not just iff *)
- set (a1:=snd tra a).
  specialize (Hyp a1). eapply trb in Hyp.
Abort.

Lemma propForalClosedP5 (A1 A2 :Type) (A_R: A1 -> A2 -> Type) 
  (B1: A1 -> Type) 
  (B2: A2 -> Type) 
  (B_R: forall a1 a2, A_R a1 a2 -> (B1 a1) -> (B2 a2) -> Type)
  (* extras *)
  (tra : TotalHeteroRel A_R) 
  (trb: forall a1 a2 (p:A_R a1 a2), IffRel (B_R _ _ p))
:
  IffRel (R_Pi B_R).
Proof.
  unfold IffRel in *.
  simpl in *. intros.
  simpl. intros.
  split; intros Hyp; intros a.
- destruct (snd tra a) as [ap]. unfold rInv in r.
  specialize (Hyp ap). eapply trb in r. (* this need proof that the ARs are related *)
  tauto.
- destruct (fst tra a) as [ap]. rename a0 into r. unfold rInv in r.
  specialize (Hyp ap). eapply trb in r; eauto.
  tauto.
Defined.

Print Assumptions propForalClosedP5.
(* Closed under the global context *)

Print Prop_R.


  Lemma piCompleteRel (A1 A2 :Type) (A_R: A1 -> A2 -> Type) 
  (B1: A1 -> Prop) 
  (B2: A2 -> Prop) 
  (B_R: forall a1 a2, A_R a1 a2 -> (B1 a1) -> (B2 a2) -> Prop)
  (trb: forall a1 a2 (p:A_R a1 a2), CompleteRel (B_R _ _ p))
(*  (oneToOneA_R: oneToOne A_R)
  (irrel : relIrrUptoEq A_R) *)
:
  CompleteRel (R_Pi B_R).
  Proof.
    intros  f1 f2 ? ? ?.
    apply trb.
  Qed.
  
Lemma totalPiProp (A1 A2 :Type) (A_R: A1 -> A2 -> Type) 
  (B1: A1 -> Prop) 
  (B2: A2 -> Prop) 
  (B_R: forall a1 a2, A_R a1 a2 -> (B1 a1) -> (B2 a2) -> Prop)
  (trp : TotalHeteroRel A_R) 
  (trb: forall a1 a2 (p:A_R a1 a2), TotalHeteroRel (B_R _ _ p))
(* 
These were needed in the version where the function type was not a Prop.
 (oneToOneA_R: oneToOne A_R)
  (irrel : relIrrUptoEq A_R) *)
:
  TotalHeteroRel (R_Pi B_R).
Proof.
  unfold R_Pi.
  apply ((fun A B R => snd (@Prop_RSpec A B R))).
  unfold Prop_R,  IffRel, CompleteRel.
  split.
  - apply tiffIff.
    apply propForalClosedP with (A_R0 := A_R);[assumption|].
    intros ? ? p.
    specialize (trb _ _ p).
    intros. apply tiffIff.
    apply ((fst (@Prop_RSpec _ _ _) trb)).
  - intros f g ? ? p.
    specialize (trb _ _ p).
    pose proof ((fst (@Prop_RSpec _ _ _) trb)) as Hp.
    apply Hp.
Qed.

Lemma PiGoodPropAux :
  forall (A1 A2 :Set) (A_R:  @GoodRel [Total] A1 A2) 
  (B1: A1 -> Prop) 
  (B2: A2 -> Prop) 
  (B_R: forall a1 a2, @R _ _ _ A_R a1 a2 ->  @GoodRel [Total] (B1 a1) (B2 a2)),
  BestRel (forall a : A1, B1 a) (forall a : A2, B2 a).
Proof using.
  intros.
  exists  (fun (f1 : forall a : A1, B1 a) (f2 : forall a : A2, B2 a) =>
forall (a1 : A1) (a2 : A2) (p : @R _ _ _ A_R a1 a2), @R _ _ _ (B_R a1 a2 p) (f1 a1) (f2 a2)
); simpl in *;
  destruct A_R; simpl in *;
  rename R into A_R.
- apply totalPiProp; try assumption.
  intros a1 a2 ar. destruct (B_R a1 a2 ar). (* needs totality on B_R*) assumption.
- apply oneToOnePiProp.
- intros ? ? ? ?. apply proof_irrelevance.
Defined.

Lemma PiGoodProp :
  forall (A1 A2 :Set) (A_R:  BestRel A1 A2) 
  (B1: A1 -> Prop) 
  (B2: A2 -> Prop) 
  (B_R: forall a1 a2, @R _ _ _ A_R a1 a2 ->  BestRel (B1 a1) (B2 a2)),
    BestRel (forall a : A1, B1 a) (forall a : A2, B2 a).
Proof using.
  intros.
  apply PiGoodPropAux with (A_R := cast_Good_onlyTotal A_R).
  intros ? ? ar. simpl in ar.
  specialize (B_R _ _ ar).
  apply cast_Good_onlyTotal.
  exact B_R.
Defined.


Lemma totalPiHalfDirect (A1 A2 :Type) (A_R: A1 -> A2 -> Type) 
  (B1: A1 -> Prop) 
  (B2: A2 -> Prop) 
  (B_R: forall a1 a2, A_R a1 a2 -> (B1 a1) -> (B2 a2) -> Prop)
  (trp : TotalHeteroRel A_R) 
  (trb: forall a1 a2 (p:A_R a1 a2), TotalHeteroRel (B_R _ _ p))
(* 
These were needed in the version where the function type was not a Prop.
 (oneToOneA_R: oneToOne A_R)
  (irrel : relIrrUptoEq A_R) *)
:
  TotalHeteroRelHalf (R_Pi B_R).
Proof.
  unfold R_Pi.
  intros f1.
  eexists.
  Unshelve.
    Focus 2.
    intros a2. 
    destruct (snd trp a2) as [a1 ar]. (* this step fails with TotalHeteroRelP *)
    specialize (trb _ _ ar).
    destruct (fst trb (f1 a1)).
(*
    exact (projT1 b).

  simpl.
  intros ? ? par. (** [par] comes from intros in the Totality proof *)
  destruct (trp a2) as [a11 far].
  unfold rInv in far.
  (** [far] was obtained by destructing [trb] in the exhibited function.
     Right now, the types of [par] and [dar] are not even same ([a11] vs [a1]).*)
  pose proof (proj2 oneToOneA_R _ _ _ _ par far eq_refl) as Heq.
  (* it may be possible to acheive this using univalence ase well
    A_R composed with A_R inv will be an isomorphism, thuse we can show a1=a1r. *)

  intros ?.
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
 *)
    Abort.

Print Assumptions totalPiProp.
(*
Axioms:
proof_irrelevance : forall (P : Prop) (p1 p2 : P), p1 = p2
 *)

Print Assumptions propForalClosedP.
Print Assumptions Prop_RSpec.

(*
Definition PiABTypeProp
  (A1 A2 :Set) (A_R: A1 -> A2 -> Prop) 
  (B1: A1 -> Set) 
  (B2: A2 -> Set)
  (B_R: forall a1 a2,  A_R a1 a2 ->  (B1 a1) -> (B2 a2) -> Prop) 
   (f1 : forall a : A1, B1 a) (f2 : forall a : A2, B2 a) : Prop :=
forall (a1 : A1) (a2 : A2) (p : A_R a1 a2), B_R a1 a2 p (f1 a1) (f2 a2).
*)

Definition PiATypeBSet (* A higher. A's higher/lower is taken care of in [translate] *)
  (A1 A2 :Type) (A_R: A1 -> A2 -> Type) 
  (B1: A1 -> Set) 
  (B2: A2 -> Set)
  (B_R: forall a1 a2,  A_R a1 a2 -> BestRel (B1 a1) (B2 a2))
  := (fun (f1 : forall a : A1, B1 a) (f2 : forall a : A2, B2 a) =>
forall (a1 : A1) (a2 : A2) (p : A_R a1 a2), BestR (B_R a1 a2 p) (f1 a1) (f2 a2)).

(* Not Allowed
PiATypeBProp (* A higher. A's higher/lower is taken care of in [translate] *)
  (A1 A2 :Type) (A_R: A1 -> A2 -> Type) 
  (B1: A1 -> Set) 
  (B2: A2 -> Set)
  (B_R: forall a1 a2,  A_R a1 a2 -> BestRel (B1 a1) (B2 a2))
  := (fun (f1 : forall a : A1, B1 a) (f2 : forall a : A2, B2 a) =>
forall (a1 : A1) (a2 : A2) (p : A_R a1 a2), BestR (B_R a1 a2 p) (f1 a1) (f2 a2)).
*)

(* a special case of the above, which is allowed. a.k.a impredicative polymorphism
A= Prop:Type
B:Prop 
What if A = nat -> Prop?
Any predicate over sets should be allowed?
In Lasson's theory, A  would be in Set_1
*)
Definition PiAEqPropBProp
(*  let A1:Type := Prop in
  let A2:Type := Prop in
  let A_R := BestRelP in *)
  (B1: Prop -> Prop) 
  (B2: Prop -> Prop)
  (B_R: forall a1 a2,  BestRelP a1 a2 -> BestRelP (B1 a1) (B2 a2))
  : BestRelP (forall a : Prop, B1 a) (forall a : Prop, B2 a).
Proof.
  unfold BestRelP in *.
  split; intros.
- rewrite <- (B_R a);[eauto | reflexivity].
- rewrite (B_R a);[eauto | reflexivity].
Qed.

Lemma TotalBestp:
TotalHeteroRel (fun x x0 : Prop => BestRel x x0).
Proof.
split; intros t; exists t; unfold rInv; simpl; apply GoodPropAsSet; unfold BestRelP;
    reflexivity.
Qed.

Definition PiAEqPropBPropNoErasure
(*  let A1:Type := Prop in
  let A2:Type := Prop in
  let A_R := BestRelP in *)
  (B1: Prop -> Prop) 
  (B2: Prop -> Prop)
  (B_R: forall (a1 a2 : Prop),  BestRel a1 a2 -> BestRel (B1 a1) (B2 a2))
  : BestRel (forall a : Prop, B1 a) (forall a : Prop, B2 a).
Proof.
  exists
  (fun f1 f2 =>
  forall (a1 : Prop) (a2 : Prop) (p : BestRel a1 a2), BestR (B_R a1 a2 p) (f1 a1) (f2 a2));
  simpl.
- pose proof (totalPiProp Prop Prop BestRel B1 B2) as Hp. simpl in Hp.
  specialize (Hp (fun a1 a2 ar => BestR (B_R a1 a2 ar))).
  simpl in Hp. apply Hp.
  + apply TotalBestp.
  + intros. destruct (B_R a1 a2 p). simpl in *. assumption.
- split; intros  ? ? ? ? ? ? ?; apply proof_irrelevance.
- intros  ? ? ? ?; apply proof_irrelevance.
Defined.


Definition PiASetBType
  (A1 A2 :Set) (A_R: BestRel A1 A2) 
  (B1: A1 -> Type) 
  (B2: A2 -> Type)
  (B_R: forall a1 a2,  BestR A_R a1 a2 -> (B1 a1) -> (B2 a2) -> Type)
  := (fun (f1 : forall a : A1, B1 a) (f2 : forall a : A2, B2 a) =>
forall (a1 : A1) (a2 : A2) (p : BestR A_R a1 a2), B_R a1 a2 p (f1 a1) (f2 a2)).


Definition PiASetBProp (A1 A2 : Set) 
  (A_R : BestRel A1 A2 (* just totality suffices *)) 
  (B1 : A1 -> Prop) (B2 : A2 -> Prop)
  (B_R : forall (a1 : A1) (a2 : A2), @BestR A1 A2 A_R a1 a2 -> BestRelP (B1 a1) (B2 a2))
   :  BestRelP (forall a : A1, B1 a) (forall a : A2, B2 a).
Proof using.
  destruct A_R. simpl in *.
  eapply propForalClosedP;[apply Rtot|].
  assumption.
Qed.

(* BestRelP can be problematic because it will force erasure *)

Section BestRelPForcesEraureOfLambda.
Variable A:Set.
Variable A_R : A->A-> Prop.
Let B: A -> Prop := fun  _ => True.
Let f : forall a, B a := fun _ => I.
Definition f_R : @BestRP (forall a, B a) (forall a, B a) (*Pi_R *) f f.
unfold BestRP.
(* f is a lambda. So f_R must be 3 lambdas *)
Fail exact (fun (a1:A) (a2:A) (arp: A_R a1 a2) => I).
simpl.
Abort.
End BestRelPForcesEraureOfLambda.

(* What is the translation of (A1 -> Prop) ? *)
Definition PiAEq2PropBProp
  (A1 A2 :Set) (A_R: BestRel A1 A2)
(*  let A1:Type := Prop in
  let A2:Type := Prop in
  let A_R := BestRelP in *)
  (B1: (A1 -> Prop) -> Prop) 
  (B2: (A2 -> Prop) -> Prop)
  (B_R: forall (a1: A1->Prop) (a2 : A2->Prop),
     R_Fun (BestR A_R) BestRel a1 a2 -> BestRel (B1 a1) (B2 a2))
  : BestRel (forall a, B1 a) (forall a, B2 a).
Proof using.
  exists
  (fun f1 f2 =>
  forall (a1: A1->Prop) (a2 : A2->Prop) (p : R_Fun (BestR A_R) BestRel a1 a2), 
    BestR (B_R a1 a2 p) (f1 a1) (f2 a2));
  simpl.
- pose proof (totalPiProp (A1 -> Prop) (A2 -> Prop) 
    (R_Fun (BestR A_R) BestRel) B1 B2) as Hp. simpl in Hp.
  specialize (Hp (fun a1 a2 ar => BestR (B_R a1 a2 ar))).
  simpl in Hp. apply Hp.
  + pose proof (@totalFun A1 A2 (BestR A_R) Prop Prop BestRel).
    simpl in *.
    replace ((fun x x0 : Prop => BestRel x x0)) with (BestRel:(Prop->Prop->Type)) in X;
      [| reflexivity].
    unfold R_Fun in *. simpl in *. unfold R_Pi in *.
    destruct A_R; simpl in *.
    apply X; auto.
    apply TotalBestp.
  + intros. destruct (B_R a1 a2 p). simpl in *. assumption.
- split; intros  ? ? ? ? ? ? ?; apply proof_irrelevance.
- intros  ? ? ? ?; apply proof_irrelevance.
Defined.

Definition PiAPropBType 
  (A1 A2 :Prop) (A_R: BestRelP A1 A2) 
  (B1: A1 -> Type) 
  (B2: A2 -> Type)
  (B_R: forall a1 a2,  BestRP a1 a2 -> (B1 a1) -> (B2 a2) -> Type)
  := (fun (f1 : forall a : A1, B1 a) (f2 : forall a : A2, B2 a) =>
forall (a1 : A1) (a2 : A2) (p : BestRP a1 a2), B_R a1 a2 p (f1 a1) (f2 a2)).

Definition PiAPropBSet
 (A1 A2 : Prop) 
  (A_R : BestRelP A1 A2) 
  (B1 : A1 -> Set) (B2 : A2 -> Set)
  (B_R : forall (a1 : A1) (a2 : A2), (@BestRP A1 A2) a1 a2 -> BestRel (B1 a1) (B2 a2))
   :  BestRel (forall a : A1, B1 a) (forall a : A2, B2 a).
Proof.
  eapply  PiGoodSet with (A_R:= GoodPropAsSet A_R).
  simpl. exact B_R.
Defined.

Definition PiAPropBProp
 (A1 A2 : Prop) 
  (A_R : BestRelP A1 A2) 
  (B1 : A1 -> Prop) (B2 : A2 -> Prop)
  (B_R : forall (a1 : A1) (a2 : A2), (@BestRP A1 A2) a1 a2 -> BestRelP (B1 a1) (B2 a2))
   :  BestRelP (forall a : A1, B1 a) (forall a : A2, B2 a).
Proof.
  unfold BestRelP, BestRP in *.
  firstorder;
  eauto.
Qed.

