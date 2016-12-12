Section IW.

(* the type of indices *)
Variable I:Type.


(* selects the different constructors and the non-recursive arguments *)
Variable A:Type.


(* each member of B denotes one recursive occurrence in the constructor.
Only the cardinality matters *)
Variable B: A -> Type.

(* the index for the conclusion *)
Variable AI: A -> I.


(* the index for each recursive occurrence in B *)
Variable BI: forall a, B a -> I.


Inductive IWT : I ->Type :=
iwt : forall (a:A), (forall (b:B a), IWT (BI a b)) -> IWT (AI a).

Inductive IWP : I ->Prop :=
iwp : forall (a:A), (forall (b:B a), IWP (BI a b)) -> IWP (AI a).

Definition getA (i: I) (t : IWT i) : A :=
match t with
iwt a  _ => a
end.

End IW.

SearchAbout (nat -> Prop).
Print le.

(* leAA := (unit + nat) *)
Definition leWB (b:(unit + nat)):= if b then False else True.

Definition leAI n (b:(unit + nat)):=
    (match b with
              | inl _ => n
              | inr m => S m
              end).

Definition leBI n (b:(unit + nat)):=
    (match b with
              | inl _ => n
              | inr m => m
              end).


Definition leW (n:nat): nat -> Prop :=
  IWP nat (unit + nat) leWB (leAI n) (fun b _ => leBI n b).


Lemma leW_iff : forall n m, le n m <-> leW n m.
Proof using.
split; intro H.
- unfold leW. induction H.
  + apply (@iwp nat (unit + nat) leWB (leAI n) (fun b _ => leBI n b) (inl tt)).
    simpl.
    tauto.
  + apply (@iwp nat (unit + nat) leWB (leAI n) (fun b _ => leBI n b) (inr m)).
    simpl. intros _. assumption.
- induction H.
  subst. clear H. rename H0 into H.
  destruct a; simpl in *.
  + clear H. constructor.
  + constructor. tauto.
Qed.

Require Import common.

Parametricity Recursive IWP.
Parametricity Recursive IWT.
Parametricity Recursive list.

Check list_R.

Require Import List.
Import ListNotations.

Fixpoint list_R2 {A₁ A₂ : Type} (RA: A₁ -> A₂ -> Type) (l1: list A₁) (l2:list A₂) : Type :=
match l1 with
| [] => l2 = []
| h1::tl1 => @sigT (A₂ * (list A₂)) 
    (fun p => let (h2,tl2) := p in 
      (l2= h2::tl2) * (RA h1 h2) * (list_R2 RA tl1 tl2))%type
end.


Require Import common.
Print IWP_R.

Definition Prop_R {A B:Prop} (R:A->B->Prop) := 
(R=fun x y => True) /\ (A <-> B).


Lemma IWP_RPW_aux
(I₁ I₂ : Type) (I_R : I₁ -> I₂ -> Type) (A₁ A₂ : Type) (A_R : A₁ -> A₂ -> Type)
(B₁ : A₁ -> Type) (B₂ : A₂ -> Type)
(B_R : forall (H : A₁) (H0 : A₂), A_R H H0 -> B₁ H -> B₂ H0 -> Type)
(AI₁ : A₁ -> I₁) (AI₂ : A₂ -> I₂)
(AI_R : forall (H : A₁) (H0 : A₂), A_R H H0 -> I_R (AI₁ H) (AI₂ H0))
(BI₁ : forall a : A₁, B₁ a -> I₁) (BI₂ : forall a : A₂, B₂ a -> I₂)
(BI_R : forall (a₁ : A₁) (a₂ : A₂) (a_R : A_R a₁ a₂) (H : B₁ a₁) (H0 : B₂ a₂),
        B_R a₁ a₂ a_R H H0 -> I_R (BI₁ a₁ H) (BI₂ a₂ H0))
 (H : I₁) (H0 : I₂) (i_R : I_R H H0)
(* extra*)
(I_R_iso : oneToOne I_R) (*total Hetero not needed*)
(A_R_tot : TotalHeteroRelP A_R) (* TotalHeteroRel implies TotalHeteroRelP *)
(B_R_tot : forall (a₁ : A₁) (a₂ : A₂) (a_R : A_R a₁ a₂), TotalHeteroRelP (B_R _ _ a_R))
:
(IWP I₁ A₁ B₁ AI₁ BI₁ H) <-> (IWP I₂ A₂ B₂ AI₂ BI₂ H0).
Proof using.
  intros.
  rename H into i₁.
  rename H0 into i₂. split.
- intros Hyp.
  revert i_R.
  revert i₂.
  induction Hyp as [a₁ Ha Hb].
(* replace i₂ with something of the form (AI₂ a₂), so that the constructor of IWP
    can be invoked *)
  pose proof (fst A_R_tot a₁) as Haa.
  intros.
  destruct Haa as [a₂ a_R].
  pose proof (AI_R _ _ a_R) as ir2.
  pose proof (proj1 (I_R_iso _ _ _ _ i_R ir2) eq_refl) as Hir2.
  subst. clear ir2. constructor.
  intros b₂.
  pose proof (snd (B_R_tot _ _ a_R) b₂) as Hbr.
  destruct Hbr as [b₁ b_R].
  apply Hb with (b:=b₁).
  eapply BI_R; eauto.
(* same proof as above, except swap ₂ and ₁, fst and snd, proj1 and proj2 *)
- intros Hyp.
  revert i_R.
  revert i₁.
  induction Hyp as [a₂ Ha Hb].
  pose proof (snd A_R_tot a₂) as Haa.
  intros.
  destruct Haa as [a₁ a_R].
  pose proof (AI_R _ _ a_R) as ir2.
  pose proof (proj2 (I_R_iso _ _ _ _ i_R ir2) eq_refl) as Hir2.
  subst. clear ir2. constructor.
  intros b₁.
  pose proof (fst (B_R_tot _ _ a_R) b₁) as Hbr.
  destruct Hbr as [b₂ b_R].
  apply Hb with (b:=b₂).
  eapply BI_R; eauto.
Qed.

Definition IWP_RP
(I₁ I₂ : Type) (I_R : I₁ -> I₂ -> Type) (A₁ A₂ : Type) (A_R : A₁ -> A₂ -> Type)
(B₁ : A₁ -> Type) (B₂ : A₂ -> Type)
(B_R : forall (H : A₁) (H0 : A₂), A_R H H0 -> B₁ H -> B₂ H0 -> Type)
(AI₁ : A₁ -> I₁) (AI₂ : A₂ -> I₂)
(AI_R : forall (H : A₁) (H0 : A₂), A_R H H0 -> I_R (AI₁ H) (AI₂ H0))
(BI₁ : forall a : A₁, B₁ a -> I₁) (BI₂ : forall a : A₂, B₂ a -> I₂)
(BI_R : forall (a₁ : A₁) (a₂ : A₂) (a_R : A_R a₁ a₂) (H : B₁ a₁) (H0 : B₂ a₂),
        B_R a₁ a₂ a_R H H0 -> I_R (BI₁ a₁ H) (BI₂ a₂ H0))
 (H : I₁) (H0 : I₂) (i_R : I_R H H0) 
(I_R_iso : oneToOne I_R) (*total Hetero not needed*)
(A_R_tot : TotalHeteroRelP A_R) (* TotalHeteroRel implies TotalHeteroRelP *)
(B_R_tot : forall (a₁ : A₁) (a₂ : A₂) (a_R : A_R a₁ a₂), TotalHeteroRelP (B_R _ _ a_R))
:
{R: (IWP I₁ A₁ B₁ AI₁ BI₁ H) -> (IWP I₂ A₂ B₂ AI₂ BI₂ H0) -> Prop | Prop_R R}.
Proof using.
  unfold Prop_R.
  eexists; split; [reflexivity|].
  eapply IWP_RPW_aux; eauto.
Defined.


(* Check IWP_R_iwp_R, then replace IWP_R by proj1_sig IWP_RW *)
Lemma iwp_RW :
 forall (I₁ I₂ : Type) (I_R : I₁ -> I₂ -> Type) (A₁ A₂ : Type)
         (A_R : A₁ -> A₂ -> Type) (B₁ : A₁ -> Type) (B₂ : A₂ -> Type)
         (B_R : forall (H : A₁) (H0 : A₂), A_R H H0 -> B₁ H -> B₂ H0 -> Type)
         (AI₁ : A₁ -> I₁) (AI₂ : A₂ -> I₂)
         (AI_R : forall (H : A₁) (H0 : A₂), A_R H H0 -> I_R (AI₁ H) (AI₂ H0))
         (BI₁ : forall a : A₁, B₁ a -> I₁) (BI₂ : forall a : A₂, B₂ a -> I₂)
         (BI_R : forall (a₁ : A₁) (a₂ : A₂) (a_R : A_R a₁ a₂) (H : B₁ a₁) (H0 : B₂ a₂),
                 B_R a₁ a₂ a_R H H0 -> I_R (BI₁ a₁ H) (BI₂ a₂ H0)) 
         (a₁ : A₁) (a₂ : A₂) (a_R : A_R a₁ a₂)
         (H : forall b : B₁ a₁, IWP I₁ A₁ B₁ AI₁ BI₁ (BI₁ a₁ b))
         (H0 : forall b : B₂ a₂, IWP I₂ A₂ B₂ AI₂ BI₂ (BI₂ a₂ b))
(I_R_iso : oneToOne I_R) (*total Hetero not needed*)
(A_R_tot : TotalHeteroRelP A_R) (* TotalHeteroRel implies TotalHeteroRelP *)
(B_R_tot : forall (a₁ : A₁) (a₂ : A₂) (a_R : A_R a₁ a₂), TotalHeteroRelP (B_R _ _ a_R)),
       (forall (b₁ : B₁ a₁) (b₂ : B₂ a₂) (b_R : B_R a₁ a₂ a_R b₁ b₂),
        proj1_sig 
          (@IWP_RP I₁ I₂ I_R A₁ A₂ A_R B₁ B₂ B_R AI₁ AI₂ AI_R BI₁ BI₂ BI_R 
              (BI₁ a₁ b₁) (BI₂ a₂ b₂) (BI_R a₁ a₂ a_R b₁ b₂ b_R) 
              I_R_iso A_R_tot B_R_tot) 
          (H b₁) 
          (H0 b₂)) ->
        proj1_sig 
            (@IWP_RP I₁ I₂ I_R A₁ A₂ A_R B₁ B₂ B_R AI₁ AI₂ AI_R BI₁ BI₂ BI_R
            (AI₁ a₁) (AI₂ a₂) (AI_R a₁ a₂ a_R) I_R_iso A_R_tot B_R_tot)
         (iwp I₁ A₁ B₁ AI₁ BI₁ a₁ H)
         (iwp I₂ A₂ B₂ AI₂ BI₂ a₂ H0).
Proof using.
  intros. simpl in *. exact I.
Qed.

Print IWT_R.

Lemma IWT_R_total
(I₁ I₂ : Type) (I_R : I₁ -> I₂ -> Type) (A₁ A₂ : Type) (A_R : A₁ -> A₂ -> Type)
(B₁ : A₁ -> Type) (B₂ : A₂ -> Type)
(B_R : forall (H : A₁) (H0 : A₂), A_R H H0 -> B₁ H -> B₂ H0 -> Type)
(AI₁ : A₁ -> I₁) (AI₂ : A₂ -> I₂)
(AI_R : forall (H : A₁) (H0 : A₂), A_R H H0 -> I_R (AI₁ H) (AI₂ H0))
(BI₁ : forall a : A₁, B₁ a -> I₁) (BI₂ : forall a : A₂, B₂ a -> I₂)
(BI_R : forall (a₁ : A₁) (a₂ : A₂) (a_R : A_R a₁ a₂) (H : B₁ a₁) (H0 : B₂ a₂),
        B_R a₁ a₂ a_R H H0 -> I_R (BI₁ a₁ H) (BI₂ a₂ H0))
 (H : I₁) (H0 : I₂) (i_R : I_R H H0)
(* extra*)
(I_R_iso : oneToOne I_R) (*total Hetero not needed*)
(wierd : rellIrrUptoEq I_R)
(A_R_tot : TotalHeteroRel A_R)
(B_R_tot : forall (a₁ : A₁) (a₂ : A₂) (a_R : A_R a₁ a₂), TotalHeteroRel (B_R _ _ a_R))
(B_R_iso : forall (a₁ : A₁) (a₂ : A₂) (a_R : A_R a₁ a₂), oneToOne (B_R _ _ a_R))
(B_R_wierd : forall (a₁ : A₁) (a₂ : A₂) (a_R : A_R a₁ a₂), rellIrrUptoEq (B_R _ _ a_R))

:
  TotalHeteroRel (IWT_R _ _ I_R _ _ A_R _ _ B_R _ _ AI_R _ _ BI_R _ _ i_R).
Proof using.
  intros.
  rename H into i₁.
  rename H0 into i₂. split.
- intros Hyp.
  revert i_R.
  revert i₂.
  induction Hyp as [a₁ Ha Hb].
  pose proof (fst A_R_tot a₁) as Haa.
  intros.
  destruct Haa as [a₂ a_R].
  pose proof (AI_R _ _ a_R) as ir2.
  pose proof (proj1 (I_R_iso _ _ _ _ i_R ir2) eq_refl) as Hir2.
  subst.
  specialize (fun b₁ b₂ b_R => Hb b₁ (BI₂ a₂ b₂) (BI_R _ _ a_R _ _ b_R)).
  specialize (wierd _ _ i_R (AI_R a₁ a₂ a_R)). subst.
  clear ir2.
  exists (iwt I₂ A₂ B₂ AI₂ BI₂ a₂
    (fun b₂ => let b1p := (snd (B_R_tot _ _ a_R) b₂) 
    in (projT1 (Hb _ b₂ (projT2 b1p))))).
  constructor.
  intros. destruct (snd (B_R_tot a₁ a₂ a_R)).
  simpl.
  destruct (Hb x b₂ b). simpl in *. clear Hb.
  pose proof (proj2 (B_R_iso  _ _ _ _ _ _ _ b_R b) eq_refl). subst.
  pose proof (B_R_wierd _ _ _ _ _ b b_R). subst.
  exact i.
- (* the other side will be similar *)
Abort.

(*
Require Import Coq.Logic.JMeq.
 Require Import Coq.Program.Equality. *)
Require Import Coq.Logic.FunctionalExtensionality.


Require Import ProofIrrelevance.
Lemma IWT_R_iso
(I₁ I₂ : Type) (I_R : I₁ -> I₂ -> Type) (A₁ A₂ : Type) (A_R : A₁ -> A₂ -> Type)
(B₁ : A₁ -> Type) (B₂ : A₂ -> Type)
(B_R : forall (H : A₁) (H0 : A₂), A_R H H0 -> B₁ H -> B₂ H0 -> Type)
(AI₁ : A₁ -> I₁) (AI₂ : A₂ -> I₂)
(AI_R : forall (H : A₁) (H0 : A₂), A_R H H0 -> I_R (AI₁ H) (AI₂ H0))
(BI₁ : forall a : A₁, B₁ a -> I₁) (BI₂ : forall a : A₂, B₂ a -> I₂)
(BI_R : forall (a₁ : A₁) (a₂ : A₂) (a_R : A_R a₁ a₂) (H : B₁ a₁) (H0 : B₂ a₂),
        B_R a₁ a₂ a_R H H0 -> I_R (BI₁ a₁ H) (BI₂ a₂ H0))
 (H : I₁) (H0 : I₂) (i_R : I_R H H0)
(* extra*)
(I_R_iso : oneToOne I_R) (*total Hetero not needed*)
(wierd : rellIrrUptoEq I_R)
(A_R_tot : TotalHeteroRel A_R)
(A_R_iso : oneToOne A_R)
(A_R_wierd : rellIrrUptoEq A_R)
(B_R_tot : forall (a₁ : A₁) (a₂ : A₂) (a_R : A_R a₁ a₂), TotalHeteroRel (B_R _ _ a_R))
(B_R_iso : forall (a₁ : A₁) (a₂ : A₂) (a_R : A_R a₁ a₂), oneToOne (B_R _ _ a_R))
(B_R_wierd : forall (a₁ : A₁) (a₂ : A₂) (a_R : A_R a₁ a₂), rellIrrUptoEq (B_R _ _ a_R))

:
  oneToOne (IWT_R _ _ I_R _ _ A_R _ _ B_R _ _ AI_R _ _ BI_R _ _ i_R).
Proof using.

  rename H into i₁.
  rename H0 into i₂. intros l1 l2 r1 r2 ir1 ir2. split.
- revert l2 r2 ir2. induction ir1 as [ ? ? ? ? ? ? Hind].
  intros.
  subst.
  inversion ir2. clear H4. subst. clear ir2.
  pose proof (proj1 (A_R_iso _ _ _ _ a_R a_R0) eq_refl) as heq.
  symmetry in heq.
  subst.
  apply inj_pair2 in H9. subst.
  clear a_R0.
  f_equal.
  apply functional_extensionality_dep.
  intros b₂.
  destruct (B_R_tot _ _ a_R) as [btl btr].
  specialize (btr b₂).
  destruct btr as [b₁ br].
  eapply (Hind b₁ _ br );[| reflexivity].
  clear Hind.
  apply inj_pair2 in H7. subst.
  Fail apply X2.
  (* a_R1 came from inversion ir2 and a_R came from induction ir1.*)
  pose proof (A_R_wierd _ _ a_R a_R1).
  subst.
  apply X2.
- (* the other side will be similar *)
Abort.

Require Import Coq.Logic.JMeq.
Require Import Coq.Program.Equality.

Definition rellIrrUptoEq5  {A B : Type} (R : A -> B -> Type)  :=
 forall  a1 b1 a2 b2 (p1 : R a1 b1) (p2 : R a2 b2) (_:a1=a2) (_:b1=b2),
    @EqdepFacts.eq_dep _ (fun p => R (fst p) (snd p)) (a1,b1) p1 (a2,b2) p2 .

Lemma rellIrrUptoEq5_implies {A B : Type} (R : A -> B -> Type):
   rellIrrUptoEq5 R ->  rellIrrUptoEq R .
Proof.
  intros H4 ? ? ? ?.
  specialize (H4 _ _ _ _ p1 p2 eq_refl eq_refl).
  apply eq_dep_eq in H4.
  auto.
Qed.


Inductive unicity (A I:Type) (f: A-> I) : I-> Type :=
uni :  forall a, unicity A I f (f a).


Lemma  unicity_prove (A I:Type) (f: A-> I) i (p: unicity A I f i): 
@sigT A (fun a => @sigT (i=f a) (fun e => uni _ _ _ a =@transport _ _ _ (unicity A I f) e p)).
Proof using.
  destruct p.
  exists a. exists eq_refl. reflexivity.
Qed.

Require Import Coq.Logic.EqdepFacts.

Lemma JMeq_eq_dep : 
  forall U (P:U->Type) p q (x:P p) (y:P q), 
  p = q -> JMeq x y -> eq_dep U P p x q y.
Proof.
intros.
destruct H.
apply JMeq_eq in H0 as ->.
reflexivity.
Qed.

Require Import SquiggleEq.tactics.
Require Import SquiggleEq.LibTactics.

Lemma IWT_R_irrel
(I₁ I₂ : Type) (I_R : I₁ -> I₂ -> Type) (A₁ A₂ : Type) (A_R : A₁ -> A₂ -> Type)
(B₁ : A₁ -> Type) (B₂ : A₂ -> Type)
(B_R : forall (H : A₁) (H0 : A₂), A_R H H0 -> B₁ H -> B₂ H0 -> Type)
(AI₁ : A₁ -> I₁) (AI₂ : A₂ -> I₂)
(AI_R : forall (H : A₁) (H0 : A₂), A_R H H0 -> I_R (AI₁ H) (AI₂ H0))
(BI₁ : forall a : A₁, B₁ a -> I₁) (BI₂ : forall a : A₂, B₂ a -> I₂)
(BI_R : forall (a₁ : A₁) (a₂ : A₂) (a_R : A_R a₁ a₂) (H : B₁ a₁) (H0 : B₂ a₂),
        B_R a₁ a₂ a_R H H0 -> I_R (BI₁ a₁ H) (BI₂ a₂ H0))
 (H : I₁) (H0 : I₂) (i_R : I_R H H0)
(* extra*)
(A_R_wierd : rellIrrUptoEq A_R)
:
  rellIrrUptoEq (IWT_R _ _ I_R _ _ A_R _ _ B_R _ _ AI_R _ _ BI_R _ _ i_R).
Proof using.
  intros ? ? ?.
  induction p1 as [ ? ? ? ? ? ? Hind].
  intros ?.
  dependent destruction p2.
  clear x2.

  pose proof (@JMeq_eq_dep _ (fun i => (IWT I₁ A₁ B₁ AI₁ BI₁ i)) _ _ _ _ x0 x3)
    as Heq.
  apply (@EqdepFacts.f_eq_dep _ _ _ _ _ _ _  (getA I₁ A₁ B₁ AI₁ BI₁)) in Heq.
  simpl in Heq.
  apply eq_dep_non_dep in Heq.
  subst. clear x0.
  apply JMeq_eq in x3.

  (* the same for a₂0 *)
  pose proof (@JMeq_eq_dep _ (fun i => (IWT I₂ A₂ B₂ AI₂ BI₂ i)) _ _ _ _ x1 x4)
    as Heq.
  apply (@EqdepFacts.f_eq_dep _ _ _ _ _ _ _  (getA I₂ A₂ B₂ AI₂ BI₂)) in Heq.
  simpl in Heq.
  apply eq_dep_non_dep in Heq.
  subst. clear x1.
  apply JMeq_eq in x4. subst.
  
  pose proof (A_R_wierd _ _ a_R0 a_R). subst.
  inverts x3 as x3.
  apply inj_pair2 in x3. subst.

  inverts x4 as x4.
  apply inj_pair2 in x4. subst.

  apply JMeq_eq in x. subst.
  f_equal.
  
  apply functional_extensionality_dep.
  intros b₁.
  apply functional_extensionality_dep.
  intros b₂.
  apply functional_extensionality_dep.
  intros b_R.
  apply Hind.
Qed.
