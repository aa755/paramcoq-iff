(** the Set version of IWT *)
Section IWTS.

Variable A:Set.

Variable I:Set.

(* each member of B denotes one recursive occurrence in the constructor.
Only the cardinality matters *)
Variable B: A -> Set.

(* the index for the conclusion *)
Variable AI: A -> I.


(* the index for each recursive occurrence in B *)
Variable BI: forall a, B a -> I.


Inductive IWT : I ->Set :=
iwt : forall (a:A), (forall (b:B a), IWT (BI a b)) -> IWT (AI a).


Definition getA (i: I) (t : IWT i) : A :=
match t with
iwt a  _ => a
end.


End IWTS.
Check iwt.


(* Parametricity Recursive IWT. *)

Inductive IWT_R (A₁ A₂ : Set) (A_R : A₁ -> A₂ -> Set) (I₁ I₂ : Set) (I_R : I₁ -> I₂ -> Set)
(B₁ : A₁ -> Set) (B₂ : A₂ -> Set)
(B_R : forall (H : A₁) (H0 : A₂), A_R H H0 -> B₁ H -> B₂ H0 -> Set) 
(AI₁ : A₁ -> I₁) (AI₂ : A₂ -> I₂)
(AI_R : forall (H : A₁) (H0 : A₂), A_R H H0 -> I_R (AI₁ H) (AI₂ H0))
(BI₁ : forall a : A₁, B₁ a -> I₁) (BI₂ : forall a : A₂, B₂ a -> I₂)
(BI_R : forall (a₁ : A₁) (a₂ : A₂) (a_R : A_R a₁ a₂) (H : B₁ a₁) (H0 : B₂ a₂),
        B_R a₁ a₂ a_R H H0 -> I_R (BI₁ a₁ H) (BI₂ a₂ H0))
  : forall (H : I₁) (H0 : I₂),
    I_R H H0 -> IWT A₁ I₁ B₁ AI₁ BI₁ H -> IWT A₂ I₂ B₂ AI₂ BI₂ H0 -> Prop :=
    IWT_R_iwt_R : forall (a₁ : A₁) (a₂ : A₂) (a_R : A_R a₁ a₂)
                    (H : forall b : B₁ a₁, IWT A₁ I₁ B₁ AI₁ BI₁ (BI₁ a₁ b))
                    (H0 : forall b : B₂ a₂, IWT A₂ I₂ B₂ AI₂ BI₂ (BI₂ a₂ b)),
                  (forall (b₁ : B₁ a₁) (b₂ : B₂ a₂) (b_R : B_R a₁ a₂ a_R b₁ b₂),
                   IWT_R A₁ A₂ A_R I₁ I₂ I_R B₁ B₂ B_R AI₁ AI₂ AI_R BI₁ BI₂ BI_R 
                     (BI₁ a₁ b₁) (BI₂ a₂ b₂) (BI_R a₁ a₂ a_R b₁ b₂ b_R) 
                     (H b₁) (H0 b₂)) ->
                  IWT_R A₁ A₂ A_R I₁ I₂ I_R B₁ B₂ B_R AI₁ AI₂ AI_R BI₁ BI₂ BI_R 
                    (AI₁ a₁) (AI₂ a₂) (AI_R a₁ a₂ a_R) (iwt A₁ I₁ B₁ AI₁ BI₁ a₁ H)
                    (iwt A₂ I₂ B₂ AI₂ BI₂ a₂ H0).

Definition IWT_RC :=
      fix
       ReflParam_matchR_IWT_RR0 (A A₂ : Set) (A_R : A -> A₂ -> Prop) 
                                (I I₂ : Set) (I_R : I -> I₂ -> Prop) 
                                (B : A -> Set) (B₂ : A₂ -> Set)
                                (B_R : forall (a1 : A) (a2 : A₂),
                                       A_R a1 a2 -> B a1 -> B₂ a2 -> Prop) 
                                (AI : A -> I) (AI₂ : A₂ -> I₂)
                                (AI_R : forall (a1 : A) (a2 : A₂),
                                        A_R a1 a2 -> I_R (AI a1) (AI₂ a2))
                                (BI : forall a : A, B a -> I)
                                (BI₂ : forall a₂ : A₂, B₂ a₂ -> I₂)
                                (BI_R : forall (a1 : A) (a2 : A₂) 
                                          (p : A_R a1 a2) (a3 : B a1) 
                                          (a4 : B₂ a2),
                                        B_R a1 a2 p a3 a4 -> I_R (BI a1 a3) (BI₂ a2 a4))
                                (H : I) (H0 : I₂) (H1 : I_R H H0) 
                                (H2 : IWT A I B AI BI H) (H3 : IWT A₂ I₂ B₂ AI₂ BI₂ H0)
                                {struct H2} : Prop :=
          let reT i1 i2 := forall (ir : I_R i1 i2), Prop in
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
                   ReflParam_matchR_IWT_RR0 A A₂ A_R I I₂ I_R B B₂ B_R AI AI₂ AI_R BI BI₂
                     BI_R (BI a a1) (BI₂ a₂ a2) (BI_R a a₂ a_R a1 a2 p) 
                     (x a1) (x0 a2) & (ir=(AI_R a a₂ a_R))}}
             end
         end) H1.

Definition iwt_RC 
(A₁ A₂ : Set) (A_R : A₁ -> A₂ -> Prop) 
                                (I₁ I₂ : Set) (I_R : I₁ -> I₂ -> Prop) 
                                (B₁ : A₁ -> Set) (B₂ : A₂ -> Set)
                                (B_R : forall (a1 : A₁) (a2 : A₂),
                                       A_R a1 a2 -> B₁ a1 -> B₂ a2 -> Prop) 
                                (AI₁ : A₁ -> I₁) (AI₂ : A₂ -> I₂)
                                (AI_R : forall (a1 : A₁) (a2 : A₂),
                                        A_R a1 a2 -> I_R (AI₁ a1) (AI₂ a2))
                                (BI₁ : forall a : A₁, B₁ a -> I₁)
                                (BI₂ : forall a₂ : A₂, B₂ a₂ -> I₂)
                                (BI_R : forall (a1 : A₁) (a2 : A₂) 
                                          (p : A_R a1 a2) (a3 : B₁ a1) 
                                          (a4 : B₂ a2),
                                        B_R a1 a2 p a3 a4 -> I_R (BI₁ a1 a3) (BI₂ a2 a4))
                                        : forall (a₁ : A₁) (a₂ : A₂) (a_R : A_R a₁ a₂)
                    (H : forall b : B₁ a₁, IWT A₁ I₁ B₁ AI₁ BI₁ (BI₁ a₁ b))
                    (H0 : forall b : B₂ a₂, IWT A₂ I₂ B₂ AI₂ BI₂ (BI₂ a₂ b)),
                  (forall (b₁ : B₁ a₁) (b₂ : B₂ a₂) (b_R : B_R a₁ a₂ a_R b₁ b₂),
                   IWT_RC A₁ A₂ A_R I₁ I₂ I_R B₁ B₂ B_R AI₁ AI₂ AI_R BI₁ BI₂ BI_R 
                     (BI₁ a₁ b₁) (BI₂ a₂ b₂) (BI_R a₁ a₂ a_R b₁ b₂ b_R) 
                     (H b₁) (H0 b₂)) ->
                  IWT_RC A₁ A₂ A_R I₁ I₂ I_R B₁ B₂ B_R AI₁ AI₂ AI_R BI₁ BI₂ BI_R 
                    (AI₁ a₁) (AI₂ a₂) (AI_R a₁ a₂ a_R) (iwt A₁ I₁ B₁ AI₁ BI₁ a₁ H)
                    (iwt A₂ I₂ B₂ AI₂ BI₂ a₂ H0).
Proof using.
  intros. simpl.
  exists a_R.
  exists H1.
  exact eq_refl.
Defined.

Section ToFrom.

Variables (A₁ A₂ : Set) (A_R : A₁ -> A₂ -> Prop) (I₁ I₂ : Set) (I_R : I₁ -> I₂ -> Prop)
(B₁ : A₁ -> Set) (B₂ : A₂ -> Set)
(B_R : forall (H : A₁) (H0 : A₂), A_R H H0 -> B₁ H -> B₂ H0 -> Prop) 
(AI₁ : A₁ -> I₁) (AI₂ : A₂ -> I₂)
(AI_R : forall (H : A₁) (H0 : A₂), A_R H H0 -> I_R (AI₁ H) (AI₂ H0))
(BI₁ : forall a : A₁, B₁ a -> I₁) (BI₂ : forall a : A₂, B₂ a -> I₂)
(BI_R : forall (a₁ : A₁) (a₂ : A₂) (a_R : A_R a₁ a₂) (H : B₁ a₁) (H0 : B₂ a₂),
        B_R a₁ a₂ a_R H H0 -> I_R (BI₁ a₁ H) (BI₂ a₂ H0))
(i1 : I₁) (i2 : I₂) (ir : I_R i1 i2) 
(i1wt : IWT A₁ I₁ B₁ AI₁ BI₁ i1) (i2wt : IWT A₂ I₂ B₂ AI₂ BI₂ i2).

Definition toNew 
  (p: IWT_R _ _ A_R _ _ I_R _ _ B_R _ _ AI_R _ _ BI_R _ _ ir i1wt i2wt): 
  IWT_RC  _ _ A_R _ _ I_R _ _ B_R _ _ AI_R _ _ BI_R _ _ ir i1wt i2wt.
Proof using.
  induction p.
  simpl. eexists. eexists. apply H2. reflexivity.
Defined.


Definition fromNew 
  (p: IWT_RC _ _ A_R _ _ I_R _ _ B_R _ _ AI_R _ _ BI_R _ _ ir i1wt i2wt): 
  IWT_R  _ _ A_R _ _ I_R _ _ B_R _ _ AI_R _ _ BI_R _ _ ir i1wt i2wt.
Proof using.
 rename i1wt into i1wtt. (* section vars don't go away even after destructing *)
 rename i2wt into i2wtt.
 revert p.
 revert i2wtt.
 revert ir.
 revert i2.
 induction i1wtt as [a1 f Hind].
 intros ? ? ?. destruct i2wtt. simpl in *.
 intros p. destruct p as [ar pp].
 destruct pp as [pp pp2].
 subst.
 apply IWT_R_iwt_R.
 Fail exact pp.
 intros.
 apply Hind.
 apply pp.
Defined.

End ToFrom.

Section Iso.

Require Import FunctionalExtensionality.
  
Lemma toNew_fromNew_id
(A₁ A₂ : Set) (A_R : A₁ -> A₂ -> Prop) (I₁ I₂ : Set) (I_R : I₁ -> I₂ -> Prop)
(B₁ : A₁ -> Set) (B₂ : A₂ -> Set)
(B_R : forall (H : A₁) (H0 : A₂), A_R H H0 -> B₁ H -> B₂ H0 -> Prop) 
(AI₁ : A₁ -> I₁) (AI₂ : A₂ -> I₂)
(AI_R : forall (H : A₁) (H0 : A₂), A_R H H0 -> I_R (AI₁ H) (AI₂ H0))
(BI₁ : forall a : A₁, B₁ a -> I₁) (BI₂ : forall a : A₂, B₂ a -> I₂)
(BI_R : forall (a₁ : A₁) (a₂ : A₂) (a_R : A_R a₁ a₂) (H : B₁ a₁) (H0 : B₂ a₂),
        B_R a₁ a₂ a_R H H0 -> I_R (BI₁ a₁ H) (BI₂ a₂ H0))
(i1 : I₁) (i2 : I₂) (ir : I_R i1 i2) 
(i1wt : IWT A₁ I₁ B₁ AI₁ BI₁ i1) (i2wt : IWT A₂ I₂ B₂ AI₂ BI₂ i2)
: forall (p: IWT_RC _ _ A_R _ _ I_R _ _ B_R _ _ AI_R _ _ BI_R _ _ ir i1wt i2wt), 
  toNew _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 
  (fromNew _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p) = p.
Proof using.
 revert i2wt.
 revert ir.
 revert i2.
 induction i1wt.
 simpl.
 intros ? ? ?. destruct i2wt. simpl in *.
 intros p. destruct p as [ar pp].
 destruct pp as [pp pp2].
 subst. simpl.
 progress f_equal.
 progress f_equal.
 Fail progress f_equal.
 simpl. simpl.
 apply FunctionalExtensionality.functional_extensionality_dep.
 intros.
 apply FunctionalExtensionality.functional_extensionality_dep.
 intros.
 apply FunctionalExtensionality.functional_extensionality_dep.
 intros ?.
 apply H.
Qed.

Scheme IWT_Rfull := Induction for IWT_R Sort Prop.

Lemma fromNew_toNew_id
(A₁ A₂ : Set) (A_R : A₁ -> A₂ -> Prop) (I₁ I₂ : Set) (I_R : I₁ -> I₂ -> Prop)
(B₁ : A₁ -> Set) (B₂ : A₂ -> Set)
(B_R : forall (H : A₁) (H0 : A₂), A_R H H0 -> B₁ H -> B₂ H0 -> Prop) 
(AI₁ : A₁ -> I₁) (AI₂ : A₂ -> I₂)
(AI_R : forall (H : A₁) (H0 : A₂), A_R H H0 -> I_R (AI₁ H) (AI₂ H0))
(BI₁ : forall a : A₁, B₁ a -> I₁) (BI₂ : forall a : A₂, B₂ a -> I₂)
(BI_R : forall (a₁ : A₁) (a₂ : A₂) (a_R : A_R a₁ a₂) (H : B₁ a₁) (H0 : B₂ a₂),
        B_R a₁ a₂ a_R H H0 -> I_R (BI₁ a₁ H) (BI₂ a₂ H0))
(i1 : I₁) (i2 : I₂) (ir : I_R i1 i2) 
(i1wt : IWT A₁ I₁ B₁ AI₁ BI₁ i1) (i2wt : IWT A₂ I₂ B₂ AI₂ BI₂ i2)
: forall (p: IWT_R _ _ A_R _ _ I_R _ _ B_R _ _ AI_R _ _ BI_R _ _ ir i1wt i2wt), 
  fromNew _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 
  (toNew _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p) = p.
Proof using.
 intros p.
 induction p using IWT_Rfull.
 simpl. unfold eq_ind_r,  eq_ind, eq_rect. simpl.
 f_equal.
 apply FunctionalExtensionality.functional_extensionality_dep.
 intros.
 apply FunctionalExtensionality.functional_extensionality_dep.
 intros.
 apply FunctionalExtensionality.functional_extensionality_dep.
 intros. eauto.
Qed.

End Iso.

Print Assumptions fromNew.
(*
Closed under the global context
*)
Print Assumptions toNew.
(*
Closed under the global context
*)
