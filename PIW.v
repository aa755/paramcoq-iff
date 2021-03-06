
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

(*
Parametricity Recursive IWT.
Print IWT_R.
Parametricity Recursive IWP.
Print IWP_R.
*)

Inductive IWT_R (I₁ I₂ : Type) (I_R : I₁ -> I₂ -> Type) (A₁ A₂ : Type) (A_R : A₁ -> A₂ -> Type)
(B₁ : A₁ -> Type) (B₂ : A₂ -> Type)
(B_R : forall (H : A₁) (H0 : A₂), A_R H H0 -> B₁ H -> B₂ H0 -> Type) (AI₁ : A₁ -> I₁)
(AI₂ : A₂ -> I₂) (AI_R : forall (H : A₁) (H0 : A₂), A_R H H0 -> I_R (AI₁ H) (AI₂ H0))
(BI₁ : forall a : A₁, B₁ a -> I₁) (BI₂ : forall a : A₂, B₂ a -> I₂)
(BI_R : forall (a₁ : A₁) (a₂ : A₂) (a_R : A_R a₁ a₂) (H : B₁ a₁) (H0 : B₂ a₂),
        B_R a₁ a₂ a_R H H0 -> I_R (BI₁ a₁ H) (BI₂ a₂ H0))
  : forall (H : I₁) (H0 : I₂), I_R H H0 -> IWT I₁ A₁ B₁ AI₁ BI₁ H -> IWT I₂ A₂ B₂ AI₂ BI₂ H0 -> Type :=
    iwt_R : forall (a₁ : A₁) (a₂ : A₂) (a_R : A_R a₁ a₂)
                    (H : forall b : B₁ a₁, IWT I₁ A₁ B₁ AI₁ BI₁ (BI₁ a₁ b))
                    (H0 : forall b : B₂ a₂, IWT I₂ A₂ B₂ AI₂ BI₂ (BI₂ a₂ b)),
                  (forall (b₁ : B₁ a₁) (b₂ : B₂ a₂) (b_R : B_R a₁ a₂ a_R b₁ b₂),
                   IWT_R I₁ I₂ I_R A₁ A₂ A_R B₁ B₂ B_R AI₁ AI₂ AI_R BI₁ BI₂ BI_R 
                     (BI₁ a₁ b₁) (BI₂ a₂ b₂) (BI_R a₁ a₂ a_R b₁ b₂ b_R) 
                     (H b₁) (H0 b₂)) ->
                  IWT_R I₁ I₂ I_R A₁ A₂ A_R B₁ B₂ B_R AI₁ AI₂ AI_R BI₁ BI₂ BI_R 
                    (AI₁ a₁) (AI₂ a₂) (AI_R a₁ a₂ a_R) (iwt I₁ A₁ B₁ AI₁ BI₁ a₁ H)
                    (iwt I₂ A₂ B₂ AI₂ BI₂ a₂ H0).

Inductive IWP_R (I₁ I₂ : Type) (I_R : I₁ -> I₂ -> Type) (A₁ A₂ : Type) (A_R : A₁ -> A₂ -> Type)
(B₁ : A₁ -> Type) (B₂ : A₂ -> Type)
(B_R : forall (H : A₁) (H0 : A₂), A_R H H0 -> B₁ H -> B₂ H0 -> Type) (AI₁ : A₁ -> I₁)
(AI₂ : A₂ -> I₂) (AI_R : forall (H : A₁) (H0 : A₂), A_R H H0 -> I_R (AI₁ H) (AI₂ H0))
(BI₁ : forall a : A₁, B₁ a -> I₁) (BI₂ : forall a : A₂, B₂ a -> I₂)
(BI_R : forall (a₁ : A₁) (a₂ : A₂) (a_R : A_R a₁ a₂) (H : B₁ a₁) (H0 : B₂ a₂),
        B_R a₁ a₂ a_R H H0 -> I_R (BI₁ a₁ H) (BI₂ a₂ H0))
  : forall (H : I₁) (H0 : I₂), I_R H H0 -> IWP I₁ A₁ B₁ AI₁ BI₁ H -> IWP I₂ A₂ B₂ AI₂ BI₂ H0 -> Prop :=
    iwp_R : forall (a₁ : A₁) (a₂ : A₂) (a_R : A_R a₁ a₂)
                    (H : forall b : B₁ a₁, IWP I₁ A₁ B₁ AI₁ BI₁ (BI₁ a₁ b))
                    (H0 : forall b : B₂ a₂, IWP I₂ A₂ B₂ AI₂ BI₂ (BI₂ a₂ b)),
                  (forall (b₁ : B₁ a₁) (b₂ : B₂ a₂) (b_R : B_R a₁ a₂ a_R b₁ b₂),
                   IWP_R I₁ I₂ I_R A₁ A₂ A_R B₁ B₂ B_R AI₁ AI₂ AI_R BI₁ BI₂ BI_R 
                     (BI₁ a₁ b₁) (BI₂ a₂ b₂) (BI_R a₁ a₂ a_R b₁ b₂ b_R) 
                     (H b₁) (H0 b₂)) ->
                  IWP_R I₁ I₂ I_R A₁ A₂ A_R B₁ B₂ B_R AI₁ AI₂ AI_R BI₁ BI₂ BI_R 
                    (AI₁ a₁) (AI₂ a₂) (AI_R a₁ a₂ a_R) (iwp I₁ A₁ B₁ AI₁ BI₁ a₁ H)
                    (iwp I₂ A₂ B₂ AI₂ BI₂ a₂ H0).
Require Import List.
Import ListNotations.


Require Import common.
Print IWP_R.


Scheme IRP_indd := Induction for IWP Sort Prop. 

Require Import PiTypeR.

(* the statement and proof are independent of the parametricity translation *)
Lemma IWP_RPW_aux_half
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
(A_R_tot : TotalHeteroRel A_R) (* TotalHeteroRel implies TotalHeteroRelP *)
(B_R_tot : forall (a₁ : A₁) (a₂ : A₂) (a_R : A_R a₁ a₂), TotalHeteroRel (B_R _ _ a_R))
:
(IWP I₁ A₁ B₁ AI₁ BI₁ H) -> (IWP I₂ A₂ B₂ AI₂ BI₂ H0).
Proof using.
  rename H into i₁.
  rename H0 into i₂.
  intros Hyp.
  revert i_R.
  revert i₂.
  induction Hyp as [a₁ Ha Hb].
(* replace i₂ with something of the form (AI₂ a₂), so that the constructor of IWP
    can be invoked *)
  pose proof (fst A_R_tot a₁) as Haa.
  Check iwt.
  intros.
  destruct Haa as [a₂ a_R].
  pose proof (AI_R _ _ a_R) as ir2.
  pose proof (proj1 I_R_iso _ _ _ i_R ir2) as Hir2.
  subst. clear ir2. constructor.
  intros b₂.
  pose proof (snd (B_R_tot _ _ a_R) b₂) as Hbr.
  destruct Hbr as [b₁ b_R].
  apply Hb with (b:=b₁).
  eapply BI_R. apply b_R.
Defined.

Lemma IWP_RPW_aux_half2
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
(I_R_iso : oneToOne I_R)
(A_R_tot : TotalHeteroRel A_R)
(B_R_tot : forall (a₁ : A₁) (a₂ : A₂) (a_R : A_R a₁ a₂), IffRel (B_R _ _ a_R)) (* iff is not sufficient. need totalit *)
:
(IWP I₁ A₁ B₁ AI₁ BI₁ H) -> (IWP I₂ A₂ B₂ AI₂ BI₂ H0).
Proof using.
  rename H into i₁.
  rename H0 into i₂.
  intros Hyp.
  revert i_R.
  revert i₂.
  induction Hyp as [a₁ Ha Hb].
(* replace i₂ with something of the form (AI₂ a₂), so that the constructor of IWP
    can be invoked *)
  pose proof (fst A_R_tot a₁) as Haa.
  Check iwt.
  intros.
  destruct Haa as [a₂ a_R].
  pose proof (AI_R _ _ a_R) as ir2. (* similarly, iff wont be sufficient for A_R *)
  pose proof (proj1 I_R_iso _ _ _ i_R ir2) as Hir2.
  subst. clear ir2. constructor.
  intros b₂.
  pose proof (snd (B_R_tot _ _ a_R) b₂) as b1.
  apply Hb with (b:=b1).
  (* we need br to be able to invoke BI_R *)
  apply BI_R with (a_R := a_R).
Abort.


Print Assumptions IWP_RPW_aux_half.

Require Import Trecord.
Require Import SquiggleEq.UsefulTypes.

Fixpoint IWP_RPW_aux_half2
(I₁ I₂ : Set) (I_R : BestRel I₁ I₂) (A₁ A₂ : Set) (A_R : BestRel A₁ A₂)
(B₁ : A₁ -> Set) (B₂ : A₂ -> Set)
(B_R : forall (H : A₁) (H0 : A₂), BestR A_R H H0 -> BestRel (B₁ H) (B₂ H0))
(AI₁ : A₁ -> I₁) (AI₂ : A₂ -> I₂)
(AI_R : forall (H : A₁) (H0 : A₂), BestR A_R H H0 -> (BestR I_R) (AI₁ H) (AI₂ H0))
(BI₁ : forall a : A₁, B₁ a -> I₁) (BI₂ : forall a : A₂, B₂ a -> I₂)
(BI_R : forall (a₁ : A₁) (a₂ : A₂) (a_R : BestR A_R a₁ a₂) (H : B₁ a₁) (H0 : B₂ a₂),
        BestR (B_R a₁ a₂ a_R) H H0 -> (BestR I_R) (BI₁ a₁ H) (BI₂ a₂ H0))
 (H : I₁) (H0 : I₂) (i_R : BestR I_R H H0)
 (p1: IWP I₁ A₁ B₁ AI₁ BI₁ H) : (IWP I₂ A₂ B₂ AI₂ BI₂ H0) :=
(match p1 in IWP _ _ _ _ _ i1 return forall i2, BestR I_R i1 i2 -> IWP I₂ A₂ B₂ AI₂ BI₂ i2
with
| iwp _ _ _ _ _ a1 f1 => 
  let a2 := projT1 (fst (Rtot A_R) a1) in
  let ar := projT2 (fst (Rtot A_R) a1) in
  let f2 := (fun b2 => 
      let b1 := projT1 (snd (Rtot (B_R a1 a2 ar)) b2) in
      let br := projT2 (snd (Rtot (B_R a1 a2 ar)) b2) in
      (IWP_RPW_aux_half2  _ _ I_R _ _ A_R  _ _ B_R _ _  AI_R _ _ BI_R 
        _ _ (BI_R _ _ ar _ _ br) (f1 b1))
        ) in
  let c2 := (iwp I₂ A₂ B₂ AI₂ BI₂ a2 f2) in 
  fun i2 ir => 
    let peq := @BestOne12 I₁ I₂ I_R (AI₁ a1) i2 (AI₂ a2) ir (AI_R a1 a2 ar) in
    @transport I₂ (AI₂ a2) i2 (fun i : I₂ => IWP I₂ A₂ B₂ AI₂ BI₂ i) peq c2
  end) H0 i_R.


Require Import common.
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
(A_R_tot : TotalHeteroRel A_R) 
(B_R_tot : forall (a₁ : A₁) (a₂ : A₂) (a_R : A_R a₁ a₂), TotalHeteroRel (B_R _ _ a_R))
:
(IWP I₁ A₁ B₁ AI₁ BI₁ H) <-> (IWP I₂ A₂ B₂ AI₂ BI₂ H0).
Proof using.
  intros.
  rename H into i₁.
  rename H0 into i₂. split.
- eapply IWP_RPW_aux_half; eauto.
- eapply IWP_RPW_aux_half with (I_R := rInv I_R) (A_R := rInv A_R)
  (B_R:=rPiInv B_R); try assumption; [ | | | | ]; rInv.
Qed.

Lemma IWP_R_complete
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
(irrel : relIrrUptoEq I_R) (* automatic for Set *)
(I_R_iso : oneToOne I_R) (*total Hetero not needed*)
(A_R_tot : TotalHeteroRel A_R) (* TotalHeteroRel implies TotalHeteroRelP *)
(B_R_tot : forall (a₁ : A₁) (a₂ : A₂) (a_R : A_R a₁ a₂), TotalHeteroRel (B_R _ _ a_R))
:
  CompleteRel (IWP_R _ _ I_R _ _ A_R _ _ B_R _ _ AI_R _ _ BI_R _ _ i_R).
Proof.
  intros x y.
  rename H into i₁.
  rename H0 into i₂.
  revert i_R.
  revert y.
  revert i₂.
  induction x  as [xa xb Hind]  using IRP_indd.
  intros ? ? ?.
  set (y2 := IWP_RPW_aux_half _ _ _ _ _ _ _ _ _ _  _ AI_R _ _ BI_R _ _ i_R
                              I_R_iso A_R_tot B_R_tot (iwp I₁ A₁ B₁ AI₁ BI₁ xa xb)).
  pose proof (ProofIrrelevance.proof_irrelevance _ y y2).
  subst y.
  unfold y2.
  simpl. clear y2.
  destruct (fst A_R_tot xa) as [a₂ ar].
  pose proof (AI_R _ _ ar) as ir2.
  pose proof (proj1 I_R_iso _ _ _ i_R ir2) as Hir2.
  subst i₂.
  unfold eq_ind_r, eq_ind.
  rewrite <- ProofIrrelevance.ProofIrrelevanceTheory.EqdepTheory.eq_rect_eq.
  simpl.
  specialize (irrel _ _ i_R (AI_R xa a₂ ar)). subst.
  constructor.
  intros. apply Hind.
Qed.

Lemma IWP_R_complete_simpl
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
(irrel : relIrrUptoEq I_R) (* automatic for Set *)
(I_R_iso : oneToOne I_R) (*total Hetero not needed*)
(A_R_tot : TotalHeteroRel A_R) (* TotalHeteroRel implies TotalHeteroRelP *)
(B_R_tot : forall (a₁ : A₁) (a₂ : A₂) (a_R : A_R a₁ a₂), TotalHeteroRel (B_R _ _ a_R))
(x : IWP I₁ A₁ B₁ AI₁ BI₁ H)
:
(IWP I₂ A₂ B₂ AI₂ BI₂ H0) * (forall y : IWP I₂ A₂ B₂ AI₂ BI₂ H0,
IWP_R I₁ I₂ I_R A₁ A₂ A_R B₁ B₂ B_R AI₁ AI₂ AI_R BI₁ BI₂ BI_R H H0 i_R x y).
Proof.
  rename H into i₁.
  rename H0 into i₂.
  revert i_R.
  revert i₂.
  induction x  as [a₁ b₁ Hb]  using IRP_indd.
  pose proof (fst A_R_tot a₁) as Haa.
  destruct Haa as [a₂ a_R].
  intros.
  pose proof (AI_R _ _ a_R) as ir2. (* similarly, iff wont be sufficient for A_R *)
  pose proof (proj1 I_R_iso _ _ _ i_R ir2) as Hir2.
  subst. clear ir2.
  evar ( c2 : IWP I₂ A₂ B₂ AI₂ BI₂ (AI₂ a₂)).
  Unshelve. Focus 2.
     constructor.
     intros b₂.
     pose proof (snd (B_R_tot _ _ a_R) b₂) as b1.
     destruct b1 as [b1 br].
     apply Hb with (b:=b1). apply BI_R with (a_R:=a_R). exact br.
  (* the above is the same as iff *)

  split;[exact c2|].
  intro.
  
  (* this is the only extra step vs iff/totality *)  
  pose proof (ProofIrrelevance.proof_irrelevance _ y c2).
  subst y.
  unfold c2.
  simpl.

  (* the totality infrastructure already does this. it creates a proof
    of the equality of all the indices_Rs at once -- the generalized equality type.
    just matching on that proof should suffice here, perhaps the same way it already does
     *)
  specialize (irrel _ _ i_R (AI_R _ _ a_R)). subst.
  constructor.
  
  (* this step is trivial.can directly code. No need to use any Pi type combinator *)
  intros. 
  exact (snd (Hb _  _ _) _).
Defined.


Lemma IWP_RPW_aux_total
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
(A_R_tot : TotalHeteroRel A_R)
(B_R_tot : forall (a₁ : A₁) (a₂ : A₂) (a_R : A_R a₁ a₂), IffRel (B_R _ _ a_R))
:
  TotalHeteroRel (IWP_R _ _ I_R _ _ A_R _ _ B_R _ _ AI_R _ _ BI_R _ _ i_R).
Proof using.
  intros.
  eapply Prop_RSpec.
  (* this route needs completeness which is too much to ask for *)
Abort.


(* iff implies TotalHeteroRel -- we should return the relation \r1 r2 => True.
We can also return IWP_R -- see below *)
Definition IWP_RP2
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
(A_R_tot : TotalHeteroRel A_R)
(B_R_tot : forall (a₁ : A₁) (a₂ : A₂) (a_R : A_R a₁ a₂), TotalHeteroRel (B_R _ _ a_R))
:
{R: (IWP I₁ A₁ B₁ AI₁ BI₁ H) -> (IWP I₂ A₂ B₂ AI₂ BI₂ H0) -> Prop & TotalHeteroRel R}.
Proof using.
  exists (fun x y => True). simpl.
  split; intros a; unfold rInv.
- rewrite IWP_RPW_aux in a; eauto; try assumption.
- rewrite <-  IWP_RPW_aux in a; eauto; try assumption.
Defined.

(*
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
 *)

Definition IWT_RR :=
     fix
       ReflParam_PIWNew_IWT_RR0 (I I₂ : Type) (I_R : I -> I₂ -> Type) 
                                (A A₂ : Type) (A_R : A -> A₂ -> Type) 
                                (B : A -> Type) (B₂ : A₂ -> Type)
                                (B_R : forall (H1 : A) (H2 : A₂),
                                       A_R H1 H2 -> B H1 -> B₂ H2 -> Type) 
                                (AI : A -> I) (AI₂ : A₂ -> I₂)
                                (AI_R : forall (H1 : A) (H2 : A₂),
                                        A_R H1 H2 -> I_R (AI H1) (AI₂ H2))
                                (BI : forall a : A, B a -> I)
                                (BI₂ : forall a₂ : A₂, B₂ a₂ -> I₂)
                                (BI_R : forall (H1 : A) (H2 : A₂) 
                                          (H3 : A_R H1 H2) (H6 : B H1) 
                                          (H7 : B₂ H2),
                                        B_R H1 H2 H3 H6 H7 -> I_R (BI H1 H6) (BI₂ H2 H7))
                                (H : I) (H0 : I₂) (H1 : I_R H H0) 
                                (H2 : IWT I A B AI BI H) (H3 : IWT I₂ A₂ B₂ AI₂ BI₂ H0)
                                {struct H2} : Type :=
          let reT i1 i2 := forall (ir : I_R i1 i2), Type in
         (match H2 as iwt1 in IWT _ _ _ _ _ i1 return reT i1 H0 
         with
         | iwt _ _ _ _ _ a x =>
             match H3 as iwt2 in IWT _ _ _ _ _ i2 return reT (AI a) i2
             with
             | iwt _ _ _ _ _ a₂ x0 =>
              fun ir =>
                 {a_R : A_R a a₂ &
                 {_
                 : forall (a1 : B a) (a2 : B₂ a₂) (p : B_R a a₂ a_R a1 a2),
                   ReflParam_PIWNew_IWT_RR0 I I₂ I_R  A A₂ A_R B B₂ B_R AI AI₂ AI_R BI BI₂
                     BI_R (BI a a1) (BI₂ a₂ a2) (BI_R a a₂ a_R a1 a2 p) 
                     (x a1) (x0 a2) & (ir=(AI_R a a₂ a_R))}}
             end
          end) H1.

Lemma IWT_RR_complete
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
(irrel : relIrrUptoEq I_R)
(A_R_complete : CompleteRel A_R) (* this is a too strong assumption, especially
if A:Set even if the IWT/P is in Prop *)
:
  CompleteRel (IWT_RR _ _ I_R _ _ A_R _ _ B_R _ _ AI_R _ _ BI_R _ _ i_R).
Proof.
  intros x y.
  rename H into i₁.
  rename H0 into i₂.
  revert i_R.
  revert y.
  revert i₂.
  induction x as [xa xb Hind]. intros ? ?. destruct y as [ya yb].
  simpl. intros ?.
  exists (A_R_complete xa ya).
  eexists. intros. apply Hind.
  apply irrel.
Defined.


Lemma IWT_R_total_half
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
(irrel : relIrrUptoEq I_R)
(A_R_tot : TotalHeteroRel A_R)
(B_R_tot : forall (a₁ : A₁) (a₂ : A₂) (a_R : A_R a₁ a₂), TotalHeteroRel (B_R _ _ a_R))
(B_R_iso : forall (a₁ : A₁) (a₂ : A₂) (a_R : A_R a₁ a₂), oneToOne (B_R _ _ a_R))
(B_R_irrel : forall (a₁ : A₁) (a₂ : A₂) (a_R : A_R a₁ a₂), relIrrUptoEq (B_R _ _ a_R))

:
  TotalHeteroRelHalf (IWT_R _ _ I_R _ _ A_R _ _ B_R _ _ AI_R _ _ BI_R _ _ i_R).
Proof using.
  intros.
  rename H into i₁.
  rename H0 into i₂.
  intros Hyp.
  revert i_R.
  revert i₂.
  induction Hyp as [a₁ Ha Hb].
  pose proof (fst A_R_tot a₁) as Haa.
  intros.
  destruct Haa as [a₂ a_R].
  pose proof (AI_R _ _ a_R) as ir2.
  pose proof (proj1 I_R_iso _ _ _ i_R ir2) as Hir2.
  subst.
  specialize (fun b₁ b₂ b_R => Hb b₁ (BI₂ a₂ b₂) (BI_R _ _ a_R _ _ b_R)).
  (* the i_R in the lemma may not be of the form cretIndices_R. 
    So, irrel is needed *)
  specialize (irrel _ _ i_R (AI_R a₁ a₂ a_R)). subst.
  clear ir2.
  exists (iwt I₂ A₂ B₂ AI₂ BI₂ a₂
    (fun b₂ => let b1p := (snd (B_R_tot _ _ a_R) b₂) 
    in (projT1 (Hb _ b₂ (projT2 b1p))))).
  constructor.
  intros. destruct (snd (B_R_tot a₁ a₂ a_R)).
  unfold rInv in *.
  simpl.
  destruct (Hb x b₂ r). simpl in *. clear Hb.
  pose proof (proj2 (B_R_iso  _ _ _) _ _ _ b_R r). subst.
  pose proof (B_R_irrel _ _ _ _ _ r b_R). subst.
  exact i.
Defined.

Print IWT_R_total_half.
Print Assumptions IWT_R_total_half.
(*
Closed under the global context
*)

Set Implicit Arguments.

Lemma IWT_R_inv:
forall (I₁ I₂ : Type) (I_R : I₁ -> I₂ -> Type) (A₁ A₂ : Type) 
  (A_R : A₁ -> A₂ -> Type) (B₁ : A₁ -> Type) (B₂ : A₂ -> Type)
  (B_R : forall (H : A₁) (H0 : A₂), A_R H H0 -> B₁ H -> B₂ H0 -> Type) 
  (AI₁ : A₁ -> I₁) (AI₂ : A₂ -> I₂)
  (AI_R : forall (H : A₁) (H0 : A₂), A_R H H0 -> I_R (AI₁ H) (AI₂ H0))
  (BI₁ : forall a : A₁, B₁ a -> I₁) (BI₂ : forall a : A₂, B₂ a -> I₂)
  (BI_R : forall (a₁ : A₁) (a₂ : A₂) (a_R : A_R a₁ a₂) (H : B₁ a₁) (H0 : B₂ a₂),
          B_R a₁ a₂ a_R H H0 -> I_R (BI₁ a₁ H) (BI₂ a₂ H0)) (H : I₁) 
  (H0 : I₂) (i_R : I_R H H0) (t2 : IWT I₂ A₂ B₂ AI₂ BI₂ H0) (t1 : IWT I₁ A₁ B₁ AI₁ BI₁ H),
IWT_R I₂ I₁ (rInv I_R) A₂ A₁ (rInv A_R) B₂ B₁ (rPiInv B_R) AI₂ AI₁
  (fun (H1 : A₂) (H2 : A₁) (X : A_R H2 H1) => AI_R H2 H1 X) BI₂ BI₁
  (fun (a₁ : A₂) (a₂ : A₁) (a_R : A_R a₂ a₁) (H1 : B₂ a₁) (H2 : B₁ a₂)
     (X : rPiInv B_R a₁ a₂ a_R H1 H2) => BI_R a₂ a₁ a_R H2 H1 X) H0 H i_R t2 t1 ->
IWT_R I₁ I₂ I_R A₁ A₂ A_R B₁ B₂ B_R AI₁ AI₂ AI_R BI₁ BI₂ BI_R H H0 i_R t1 t2.
Proof using.
  unfold rPiInv, rInv.
  intros.
  induction X; constructor; eauto.
Qed.


(* we would need a way to invert (fun a b => R b a) relations of arbitrary type constuctors.
We have rInv and rPiInv for type vars and piTypes. But we would need to invert inductives
and to prove that the inversion preserves goodness *)

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
(irrel : relIrrUptoEq I_R)
(A_R_tot : TotalHeteroRel A_R)
(B_R_tot : forall (a₁ : A₁) (a₂ : A₂) (a_R : A_R a₁ a₂), TotalHeteroRel (B_R _ _ a_R))
(B_R_iso : forall (a₁ : A₁) (a₂ : A₂) (a_R : A_R a₁ a₂), oneToOne (B_R _ _ a_R))
(B_R_irrel : forall (a₁ : A₁) (a₂ : A₂) (a_R : A_R a₁ a₂), relIrrUptoEq (B_R _ _ a_R))

:
  TotalHeteroRel (IWT_R _ _ I_R _ _ A_R _ _ B_R _ _ AI_R _ _ BI_R _ _ i_R).
Proof using.
  split.
- apply IWT_R_total_half; auto.
- pose proof (@IWT_R_total_half _ _ (rInv I_R) _ _ (rInv A_R) _ _ (rPiInv B_R)
   AI₂ AI₁ ltac:(rInv)
  BI₂ BI₁ ltac:(rInv) _ _ i_R
  ltac:(rInv) ltac:(rInv) ltac:(rInv)
  ltac:(rInv) ltac:(rInv) ltac:(rInv)
) as Hh.
  (*  unfold TotalHeteroRelHalf, R_Pi, rPiInv, rInv in *. *)
  revert Hh. clear.
  intros ? t2. 
  specialize (Hh t2). destruct Hh as [t1 ?]; simpl in *.
  exists t1. apply IWT_R_inv. assumption.
Qed.


(*
Require Import Coq.Logic.JMeq.
 Require Import Coq.Program.Equality. *)
Require Import ProofIrrelevance.
Require Import Coq.Logic.FunctionalExtensionality.


Lemma IWT_R_iso_half
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
(A_R_iso : oneToOne A_R)
(A_R_irrel : relIrrUptoEq A_R)
(B_R_tot : forall (a₁ : A₁) (a₂ : A₂) (a_R : A_R a₁ a₂), TotalHeteroRel (B_R _ _ a_R))

:
  oneToOneHalf (IWT_R _ _ I_R _ _ A_R _ _ B_R _ _ AI_R _ _ BI_R _ _ i_R).
Proof using.
  rename H into i₁.
  rename H0 into i₂. intros l1 r1 r2 ir1 ir2.
  revert r2 ir2. induction ir1 as [ ? ? ? ? ? ? Hind].
  intros.
  subst.
  inversion ir2. clear H4. subst. clear ir2.
  pose proof ((proj1 A_R_iso) _ _ _ a_R a_R0 ) as heq.
  symmetry in heq.
  subst.
  apply inj_pair2 in H14. subst. 
    (* inj_pair2 depends on proof irrelevance, or at least UIP in I₂.
    In the global translation, in GoodRel, we can demand UIP on the sets on both sides.
    Proof irrelevance already implies it. is UIP weaker than PI?*)
  f_equal.
  apply functional_extensionality_dep.
  intros b₂.
  destruct (B_R_tot _ _ a_R) as [btl btr].
  specialize (btr b₂).
  destruct btr as [b₁ br].
  eapply (Hind b₁ _ br );[].
  clear Hind.
  apply inj_pair2 in H12. subst.
    (* inj_pair2 depends on proof irrelevance, or at least UIP in A₁.
    In the global translation, in GoodRel, we can demand UIP on the sets on both sides*)
  Fail apply X2.
  (* a_R1 came from inversion ir2 and a_R came from induction ir1.*)
  pose proof (A_R_irrel _ _ a_R a_R1).
  subst. auto.
Defined.

Print Assumptions IWT_R_iso_half.


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
(A_R_iso : oneToOne A_R)
(A_R_irrel : relIrrUptoEq A_R)
(B_R_tot : forall (a₁ : A₁) (a₂ : A₂) (a_R : A_R a₁ a₂), TotalHeteroRel (B_R _ _ a_R))

:
  oneToOne (IWT_R _ _ I_R _ _ A_R _ _ B_R _ _ AI_R _ _ BI_R _ _ i_R).
Proof using.
  split.
- apply IWT_R_iso_half; auto.
- pose proof (@IWT_R_iso_half _ _ (rInv I_R) _ _ (rInv A_R) _ _ (rPiInv B_R)
   AI₂ AI₁ ltac:(rInv)
  BI₂ BI₁ ltac:(rInv) _ _ i_R
  ltac:(rInv) ltac:(rInv) ltac:(rInv)
) as Hh.
  unfold TotalHeteroRelHalf, R_Pi, rPiInv, rInv in *.
  revert Hh. clear.
  intros ? ? ? ? p1 p2.
  unfold oneToOneHalf in Hh.
  specialize (Hh _ _ _ (IWT_R_inv _ _ p1) (IWT_R_inv _ _ p2)).
  assumption.
Qed.

Print Assumptions  IWT_R_iso.

Require Import Coq.Logic.JMeq.
Require Import Coq.Program.Equality.

Definition rellIrrUptoEq5  {A B : Type} (R : A -> B -> Type)  :=
 forall  a1 b1 a2 b2 (p1 : R a1 b1) (p2 : R a2 b2) (_:a1=a2) (_:b1=b2),
    @EqdepFacts.eq_dep _ (fun p => R (fst p) (snd p)) (a1,b1) p1 (a2,b2) p2 .

Lemma rellIrrUptoEq5_implies {A B : Type} (R : A -> B -> Type):
   rellIrrUptoEq5 R ->  relIrrUptoEq R .
Proof.
  intros H4 ? ? ? ?.
  specialize (H4 _ _ _ _ p1 p2 eq_refl eq_refl).
  apply eq_dep_eq in H4.
  auto.
Qed.

Unset Implicit Arguments.

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
(A_R_irrel : relIrrUptoEq A_R) (* to prove irrel, we only need irred (and some axioms) *)
:
  relIrrUptoEq (IWT_R _ _ I_R _ _ A_R _ _ B_R _ _ AI_R _ _ BI_R _ _ i_R).
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
  
  pose proof (A_R_irrel _ _ a_R0 a_R). subst.
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

Print Assumptions IWT_R_irrel.
(*
proof_irrelevance : forall (P : Prop) (p1 p2 : P), p1 = p2
functional_extensionality_dep : forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
                                (forall x : A, f x = g x) -> f = g
JMeq_eq : forall (A : Type) (x y : A), x ~= y -> x = y (* this may not be needed *)

*)


Definition IWP_ind2  : forall (I A : Type) (B : A -> Type) (AI : A -> I) (BI : forall a : A, B a -> I)
         (P : forall i : I, IWP I A B AI BI i -> Prop),
       (forall (a : A) (i : forall b : B a, IWP I A B AI BI (BI a b)),
        (forall b : B a, P (BI a b) (i b)) -> P (AI a) (iwp I A B AI BI a i)) ->
       forall (i : I) (i0 : IWP I A B AI BI i), P i i0
:= 
fun (I A : Type) (B : A -> Type) (AI : A -> I) (BI : forall a : A, B a -> I)
  (P : forall i : I, IWP I A B AI BI i -> Prop)
  (f : forall (a : A) (i : forall b : B a, IWP I A B AI BI (BI a b)),
       (forall b : B a, P (BI a b) (i b)) -> P (AI a) (iwp I A B AI BI a i)) =>
fix F (i : I) (i0 : IWP I A B AI BI i) {struct i0} : P i i0 :=
  match i0 as i2 in (IWP _ _ _ _ _ i1) return (P i1 i2) with
  | iwp _ _ _ _ _ a i1 => f a i1 (fun b : B a => F (BI a b) (i1 b))
  end.


(*IWP_RP above was better because less extras were needed.
In particular A_R iso and B_R iso and irrel was not needed.
So, we should have the translation of [Prop] and [Type] be the same.
However, we should separately translate inductives in [Type] and inductives in [Prop].
Similarly, we should separately translate functions into Type and functions into Prop

Without Proof irrelevance, IWP_R is stronger than Prop_R2. It says 
that the 2 proofs use the same constructors and those constructors "similar" arguments.
Prop_R2 says nothing about the 2 proofs, besides their existence.
However, with proof irrelevance, the difference is irrelevant.
However, as mentioned above, treating Prop specially, as in IWP_RP, results
in much fewer extrans, and this riddance may snowball upstream
and result in much stronger free theorems.*)
Lemma IWP_R_total
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
(irrel : relIrrUptoEq I_R)
(A_R_tot : TotalHeteroRel A_R)
(B_R_tot : forall (a₁ : A₁) (a₂ : A₂) (a_R : A_R a₁ a₂), TotalHeteroRel (B_R _ _ a_R))
(B_R_iso : forall (a₁ : A₁) (a₂ : A₂) (a_R : A_R a₁ a₂), oneToOne (B_R _ _ a_R))
(B_R_irrel : forall (a₁ : A₁) (a₂ : A₂) (a_R : A_R a₁ a₂), relIrrUptoEq (B_R _ _ a_R))

:
  TotalHeteroRelHalf (IWP_R _ _ I_R _ _ A_R _ _ B_R _ _ AI_R _ _ BI_R _ _ i_R).
Proof using.
  intros.
  rename H into i₁.
  rename H0 into i₂.
  intros Hyp.
  revert i_R.
  revert i₂.
  induction Hyp as [a₁ Ha Hb] using IWP_ind2.
  pose proof (fst A_R_tot a₁) as Haa.
  intros.
  destruct Haa as [a₂ a_R].
  pose proof (AI_R _ _ a_R) as ir2.
  pose proof ((proj1 I_R_iso) _ _ _ i_R ir2) as Hir2.
  subst.
  specialize (fun b₁ b₂ b_R => Hb b₁ (BI₂ a₂ b₂) (BI_R _ _ a_R _ _ b_R)).
  specialize (irrel _ _ i_R (AI_R a₁ a₂ a_R)). subst.
  clear ir2.
  exists (iwp I₂ A₂ B₂ AI₂ BI₂ a₂
    (fun b₂ => let b1p := (snd (B_R_tot _ _ a_R) b₂) 
    in (projT1 (Hb _ b₂ (projT2 b1p))))).
  constructor.
  intros. destruct (snd (B_R_tot a₁ a₂ a_R)).
  unfold rInv in *.
  simpl.
  destruct (Hb x b₂ r). simpl in *. clear Hb.
  pose proof ((proj2 (B_R_iso  _ _ _)) _ _ _ b_R r). subst.
  pose proof (B_R_irrel _ _ _ _ _ r b_R). subst.
  exact i; fail.
  Fail idtac.
Abort. (* done but not needed. see comments at the beginning*)


(*
Require Import Coq.Logic.JMeq.
 Require Import Coq.Program.Equality. *)
Require Import Coq.Logic.FunctionalExtensionality.


Definition IWP_R_rect := 
fun (I₁ I₂ : Type) (I_R : I₁ -> I₂ -> Type) (A₁ A₂ : Type) (A_R : A₁ -> A₂ -> Type)
  (B₁ : A₁ -> Type) (B₂ : A₂ -> Type)
  (B_R : forall (H : A₁) (H0 : A₂), A_R H H0 -> B₁ H -> B₂ H0 -> Type) 
  (AI₁ : A₁ -> I₁) (AI₂ : A₂ -> I₂)
  (AI_R : forall (H : A₁) (H0 : A₂), A_R H H0 -> I_R (AI₁ H) (AI₂ H0))
  (BI₁ : forall a : A₁, B₁ a -> I₁) (BI₂ : forall a : A₂, B₂ a -> I₂)
  (BI_R : forall (a₁ : A₁) (a₂ : A₂) (a_R : A_R a₁ a₂) (H : B₁ a₁) (H0 : B₂ a₂),
          B_R a₁ a₂ a_R H H0 -> I_R (BI₁ a₁ H) (BI₂ a₂ H0))
  (P : forall (i : I₁) (i0 : I₂) (i1 : I_R i i0) (i2 : IWP I₁ A₁ B₁ AI₁ BI₁ i)
         (i3 : IWP I₂ A₂ B₂ AI₂ BI₂ i0),
       IWP_R I₁ I₂ I_R A₁ A₂ A_R B₁ B₂ B_R AI₁ AI₂ AI_R BI₁ BI₂ BI_R i i0 i1 i2 i3 -> Prop)
  (f : forall (a₁ : A₁) (a₂ : A₂) (a_R : A_R a₁ a₂)
         (i : forall b : B₁ a₁, IWP I₁ A₁ B₁ AI₁ BI₁ (BI₁ a₁ b))
         (i0 : forall b : B₂ a₂, IWP I₂ A₂ B₂ AI₂ BI₂ (BI₂ a₂ b))
         (i1 : forall (b₁ : B₁ a₁) (b₂ : B₂ a₂) (b_R : B_R a₁ a₂ a_R b₁ b₂),
               IWP_R I₁ I₂ I_R A₁ A₂ A_R B₁ B₂ B_R AI₁ AI₂ AI_R BI₁ BI₂ BI_R 
                 (BI₁ a₁ b₁) (BI₂ a₂ b₂) (BI_R a₁ a₂ a_R b₁ b₂ b_R) 
                 (i b₁) (i0 b₂)),
       (forall (b₁ : B₁ a₁) (b₂ : B₂ a₂) (b_R : B_R a₁ a₂ a_R b₁ b₂),
        P (BI₁ a₁ b₁) (BI₂ a₂ b₂) (BI_R a₁ a₂ a_R b₁ b₂ b_R) (i b₁) (i0 b₂) (i1 b₁ b₂ b_R)) ->
       P (AI₁ a₁) (AI₂ a₂) (AI_R a₁ a₂ a_R) (iwp I₁ A₁ B₁ AI₁ BI₁ a₁ i)
         (iwp I₂ A₂ B₂ AI₂ BI₂ a₂ i0)
         (iwp_R I₁ I₂ I_R A₁ A₂ A_R B₁ B₂ B_R AI₁ AI₂ AI_R BI₁ BI₂ BI_R a₁ a₂ a_R i i0
            i1)) =>
fix
F (y : I₁) (y0 : I₂) (y1 : I_R y y0) (i : IWP I₁ A₁ B₁ AI₁ BI₁ y)
  (i0 : IWP I₂ A₂ B₂ AI₂ BI₂ y0)
  (i1 : IWP_R I₁ I₂ I_R A₁ A₂ A_R B₁ B₂ B_R AI₁ AI₂ AI_R BI₁ BI₂ BI_R y y0 y1 i i0) {struct
  i1} : P y y0 y1 i i0 i1 :=
  match
    i1 as i4 in (IWP_R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ y2 y3 y4 i2 i3)
    return (P y2 y3 y4 i2 i3 i4)
  with
  | iwp_R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a₁ a₂ a_R i2 i3 i4 =>
      f a₁ a₂ a_R i2 i3 i4
        (fun (b₁ : B₁ a₁) (b₂ : B₂ a₂) (b_R : B_R a₁ a₂ a_R b₁ b₂) =>
         F (BI₁ a₁ b₁) (BI₂ a₂ b₂) (BI_R a₁ a₂ a_R b₁ b₂ b_R) (i2 b₁) (i3 b₂) (i4 b₁ b₂ b_R))
  end.


(* this should be a trivial consequence of proof irrelevance *)
Lemma IWP_R_iso
(I₁ I₂ : Type) (I_R : I₁ -> I₂ -> Type) (A₁ A₂ : Type) (A_R : A₁ -> A₂ -> Type)
(B₁ : A₁ -> Type) (B₂ : A₂ -> Type)
(B_R : forall (H : A₁) (H0 : A₂), A_R H H0 -> B₁ H -> B₂ H0 -> Type)
(AI₁ : A₁ -> I₁) (AI₂ : A₂ -> I₂)
(AI_R : forall (H : A₁) (H0 : A₂), A_R H H0 -> I_R (AI₁ H) (AI₂ H0))
(BI₁ : forall a : A₁, B₁ a -> I₁) (BI₂ : forall a : A₂, B₂ a -> I₂)
(BI_R : forall (a₁ : A₁) (a₂ : A₂) (a_R : A_R a₁ a₂) (H : B₁ a₁) (H0 : B₂ a₂),
        B_R a₁ a₂ a_R H H0 -> I_R (BI₁ a₁ H) (BI₂ a₂ H0))
 (H : I₁) (H0 : I₂) (i_R : I_R H H0)
:
  oneToOne (IWP_R _ _ I_R _ _ A_R _ _ B_R _ _ AI_R _ _ BI_R _ _ i_R).
Proof using.
  split;intros ? ? ? ? ?; apply proof_irrelevance.
Qed.


Require Import Coq.Logic.JMeq.
Require Import Coq.Program.Equality.


Require Import Coq.Logic.EqdepFacts.

Require Import SquiggleEq.tactics.
Require Import SquiggleEq.LibTactics.


Lemma IWP_R_irrel
(I₁ I₂ : Type) (I_R : I₁ -> I₂ -> Type) (A₁ A₂ : Type) (A_R : A₁ -> A₂ -> Type)
(B₁ : A₁ -> Type) (B₂ : A₂ -> Type)
(B_R : forall (H : A₁) (H0 : A₂), A_R H H0 -> B₁ H -> B₂ H0 -> Type)
(AI₁ : A₁ -> I₁) (AI₂ : A₂ -> I₂)
(AI_R : forall (H : A₁) (H0 : A₂), A_R H H0 -> I_R (AI₁ H) (AI₂ H0))
(BI₁ : forall a : A₁, B₁ a -> I₁) (BI₂ : forall a : A₂, B₂ a -> I₂)
(BI_R : forall (a₁ : A₁) (a₂ : A₂) (a_R : A_R a₁ a₂) (H : B₁ a₁) (H0 : B₂ a₂),
        B_R a₁ a₂ a_R H H0 -> I_R (BI₁ a₁ H) (BI₂ a₂ H0))
 (H : I₁) (H0 : I₂) (i_R : I_R H H0)
(* extra
(A_R_irrel : relIrrUptoEq A_R)
*)
:
  relIrrUptoEq (IWP_R _ _ I_R _ _ A_R _ _ B_R _ _ AI_R _ _ BI_R _ _ i_R).
Proof using.
  intros ? ? ? ?.
  apply proof_irrelevance; fail.
Qed. 

Print Prop_R.
