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
Inductive Props : Set := Total | OneToOne (*| Irrel *).
Definition allProps : list Props := [Total; OneToOne (*; Irrel *) ].

Global Instance deq : Deq Props.
Proof using.
  apply @deqAsSumbool.
  unfold DeqSumbool. intros. unfold DecidableSumbool.
  repeat decide equality.
Defined.


Notation univ := (Set) (only parsing).

Definition IndicesInvUniv := Type.

(* use IndUnivs here? *)
(*Polymorphic *) Record GoodRel (select: list Props)
 (T₁ T₂: univ)  : IndicesInvUniv (* nececcarily bigger than Set if univ, because of R*) :=
{
  R : T₁ -> T₂ -> Prop (* Type ? *);
  Rtot : if (memberb Total select) then TotalHeteroRel R else True;
  Rone : if (memberb OneToOne select) then oneToOne R else True;
  
  (* Proof irrelevance is not needed anymore, after changing Type to Prop in R.
  This item is always deselected. Can be removed once we totatlly commit to Prop
  and decide that assuming Proof irrelevance is acceptable.
  About the latter, UIP was badly needed for the oneToOne of indexed inductives.
  If UIP <-> Proof Irrelevance, then we will be forced to have Proof irrelevance 
  be acceptable
  Rirrel : if (memberb Irrel select) then relIrrUptoEq R else True;
   *)
}.

Check (GoodRel allProps (True:Prop) (True:Prop)):Type.

Fail Check (GoodRel allProps (nat:Set) (nat:Set)):Set (* because of R, this has to be atleast 1 bigger than Set*).


Definition eraseRP  (sb ss: list Props)
  (sub: subsetb _ ss sb=true) (T₁ T₂:univ) (gb: GoodRel sb T₁ T₂ ) :
    (GoodRel ss T₁ T₂ ).
Proof.
  (* projecting a goodrel should compute to a goodRel. So no matching before
    returning a goodRel *)
  apply Build_GoodRel with (R:= @R sb _ _ gb);
     destruct gb; simpl in *;
  apply' subsetb_memberb sub.
- specialize (sub Total).
  destruct (memberb _ ss);[| exact I].
  specialize (sub eq_refl). rewrite sub in Rtot0.
  assumption.
- specialize (sub OneToOne).
  destruct (memberb _ ss);[| exact I].
  specialize (sub eq_refl). rewrite sub in Rone0.
  assumption.
Defined.

Definition onlyTotal : list Props := [Total].

Definition cast_Good_onlyTotal  (T₁ T₂:univ)  (gb: GoodRel allProps T₁ T₂ ) :
  (GoodRel onlyTotal T₁ T₂ ).
  apply eraseRP with (sb:=allProps);[reflexivity| assumption].
Defined.


Definition BestRel  : Set -> Set -> Type := GoodRel allProps (* [Total; OneToOne] *).
Definition BestR : forall T₁ T₂ : Set, GoodRel allProps T₁ T₂ -> T₁ -> T₂ -> Prop
  := @R allProps.

Definition mkBestRel (A1 A2:Set) (AR : A1 -> A2 -> Prop)
           (tot12 : TotalHeteroRelHalf AR)
           (tot21 : TotalHeteroRelHalf (rInvSP AR))
           (one12: oneToOneHalf AR)
           (one21: oneToOneHalf (rInvSP AR))
  : BestRel A1 A2.
Proof.
  exists AR; simpl.
  - split.
    + exact tot12. 
    + exact tot21. 
  - split.
    + exact one12. 
    + exact one21. 
Defined.

Definition mkBestRelProp (A1 A2:Prop) (AR : A1 -> A2 -> Prop)
           (tot12 : TotalHeteroRelHalf AR)
           (tot21 : TotalHeteroRelHalf (rInvSP AR))
  : BestRel A1 A2.
Proof.
  exists AR; simpl.
  - split.
    + exact tot12. 
    + exact tot21. 
  - apply propeOneToOne.
Defined.

Definition BestTot12 (T₁ T₂ : Set) (T_R: GoodRel allProps T₁ T₂) (t1:T₁) : T₂
  := projT1 ((fst (Rtot T_R)) t1).

Definition BestTot12R (T₁ T₂ : Set) (T_R: GoodRel allProps T₁ T₂) (t1:T₁)
  := projT2 ((fst (Rtot T_R)) t1).

Definition BestTot21 (T₁ T₂ : Set) (T_R: GoodRel allProps T₁ T₂) (t2:T₂) : T₁
  := projT1 ((snd (Rtot T_R)) t2).

Definition BestTot21R (T₁ T₂ : Set) (T_R: GoodRel allProps T₁ T₂) (t2:T₂)
  := projT2 ((snd (Rtot T_R)) t2).

Definition BestOne12 (A B : Set) (T_R: GoodRel allProps A B) (a :A) (b1 b2 :B)
  (r1 : R T_R a b1) (r2 : R T_R a b2) : b2=b1
  := eq_sym ((proj1 (Rone T_R)) a b1 b2 r1 r2).

Definition BestOne21 (A B : Set) (T_R: GoodRel allProps A B) (a1 :A) (b :B) (a2:A)
  (r1 : R T_R a1 b) (r2 : R T_R a2 b) : a2 = a1
  := eq_sym ((proj2 (Rone T_R)) b a1 a2 r1 r2).


Definition BestOneijjo (A B : Set) (T_R: GoodRel allProps A B) (a :A) (b1 b2 :B)
  (r1 : R T_R a b1) (r2 : R T_R a b2) : b1=b2
  :=  ((proj1 (Rone T_R)) a b1 b2 r1 r2).

Definition BestOneijjo21 (A B : Set) (T_R: GoodRel allProps A B) (b :B) (a1 a2:A)
  (r1 : R T_R a1 b) (r2 : R T_R a2 b) : a1 = a2
  :=  ((proj2 (Rone T_R)) b a1 a2 r1 r2).

Definition BestRelP : Prop -> Prop -> Prop := iff.
Definition BestRP (T₁ T₂ : Prop) (t₁ : T₁) (t₂ : T₂) : Prop := True.

Require Import ProofIrrelevance.

(*
The relation for Prop cannot be  (fun _ _ => True) as it breaks many things:
see the erasure section of onenote
https://onedrive.live.com/edit.aspx/Documents/Postdoc?cid=946e75b47b19a3b5&id=documents&wd=target%28parametricity%2Fpapers%2Flogic%2Ferasure.one%7CE3B57163-01F2-A447-8AD2-A7AA172DB692%2F%29
onenote:https://d.docs.live.net/946e75b47b19a3b5/Documents/Postdoc/parametricity/papers/logic/erasure.one#section-id={E3B57163-01F2-A447-8AD2-A7AA172DB692}&end
 *)

Definition GoodPropAsSet {A1 A2:Prop} (bp: BestRelP A1 A2) : BestRel A1 A2.
unfold BestRelP in bp.
exists (fun _ _ => True); simpl.
- apply Prop_RSpec. unfold Prop_R,IffRel,CompleteRel.
  apply tiffIff in bp.
  split; [assumption|]. intros ? ?. exact I.
- split; intros ? ?  ? ? ?; apply proof_irrelevance.
Defined.

