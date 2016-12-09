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

Declare ML Module "paramcoq".
Require Import common.

Parametricity Recursive IWP.
Require Import common.
Print IWP_R.

Lemma IWP_iff (I₁ I₂ : Type) (I_R : I₁ -> I₂ -> Type) (A₁ A₂ : Type) (A_R : A₁ -> A₂ -> Type)
(B₁ : A₁ -> Type) (B₂ : A₂ -> Type)
(B_R : forall (H : A₁) (H0 : A₂), A_R H H0 -> B₁ H -> B₂ H0 -> Type)
(AI₁ : A₁ -> I₁) (AI₂ : A₂ -> I₂)
(AI_R : forall (H : A₁) (H0 : A₂), A_R H H0 -> I_R (AI₁ H) (AI₂ H0))
(BI₁ : forall a : A₁, B₁ a -> I₁) (BI₂ : forall a : A₂, B₂ a -> I₂)
(BI_R : forall (a₁ : A₁) (a₂ : A₂) (a_R : A_R a₁ a₂) (H : B₁ a₁) (H0 : B₂ a₂),
        B_R a₁ a₂ a_R H H0 -> I_R (BI₁ a₁ H) (BI₂ a₂ H0))
 (H : I₁) (H0 : I₂) (i_R : I_R H H0) 
(* extra*)
(I_R_iso : relIso I_R)
(A_R_tot : TotalHeteroRel A_R)
(B_R_tot : forall (a₁ : A₁) (a₂ : A₂) (a_R : A_R a₁ a₂), TotalHeteroRel (B_R _ _ a_R))
:
(IWP I₁ A₁ B₁ AI₁ BI₁ H) <-> (IWP I₂ A₂ B₂ AI₂ BI₂ H0)
.
Proof using.
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
