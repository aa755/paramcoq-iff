Section IW.

(* the type of indices *)
Variable I:Set.


(* selects the different constructors and the non-recursive arguments *)
Variable A:Set.


(* each member of B denotes one recursive occurrence in the constructor.
Only the cardinality matters *)
Variable B: A -> Set.

(* the index for the conclusion *)
Variable AI: A -> I.


(* the index for each recursive occurrence in B *)
Variable BI: forall a, B a -> I.


Inductive IWT : I ->Set :=
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

Definition IWT_RR :=
     fix
       ReflParam_PIWNew_IWT_RR0 (I I₂ : Set) (I_R : I -> I₂ -> Prop) 
                                (A A₂ : Set) (A_R : A -> A₂ -> Prop) 
                                (B : A -> Set) (B₂ : A₂ -> Set)
                                (B_R : forall (H1 : A) (H2 : A₂),
                                       A_R H1 H2 -> B H1 -> B₂ H2 -> Prop) 
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
                                {struct H2} : Prop :=
         match H2 with
         | iwt _ _ _ _ _ a x =>
             match H3 with
             | iwt _ _ _ _ _ a₂ x0 =>
                 {a_R : A_R a a₂ &
                 {_
                 : forall (H6 : B a) (H7 : B₂ a₂) (H8 : B_R a a₂ a_R H6 H7),
                   ReflParam_PIWNew_IWT_RR0 I I₂ I_R A A₂ A_R B B₂ B_R AI AI₂ AI_R BI BI₂
                     BI_R (BI a H6) (BI₂ a₂ H7) (BI_R a a₂ a_R H6 H7 H8) 
                     (x H6) (x0 H7) & True}}
             end
         end.

Require Import Trecord.
Require Import SquiggleEq.UsefulTypes.
Definition IWT_RRG :=
 fix
       ReflParam_PIWNew_IWT_RR0 (I I₂ : Set) (I_R : GoodRel [Total; OneToOne; Irrel] I I₂)
                                (A A₂ : Set) (A_R : GoodRel [Total; OneToOne; Irrel] A A₂)
                                (B : A -> Set) (B₂ : A₂ -> Set)
                                (B_R : forall (H1 : A) (H2 : A₂),
                                       (let (R, _, _, _) := A_R in R) H1 H2 ->
                                       GoodRel [Total; OneToOne; Irrel] (B H1) (B₂ H2))
                                (AI : A -> I) (AI₂ : A₂ -> I₂)
                                (AI_R : forall (a1 : A) (a2 : A₂),
                                        (let (R, _, _, _) := A_R in R) a1 a2 ->
                                        (let (R, _, _, _) := I_R in R) (AI a1) (AI₂ a2))
                                (BI : forall a : A, B a -> I)
                                (BI₂ : forall a₂ : A₂, B₂ a₂ -> I₂)
                                (BI_R : forall (a1 : A) (a2 : A₂)
                                          (p : (let (R, _, _, _) := A_R in R) a1 a2)
                                          (a3 : B a1) (a4 : B₂ a2),
                                        (let (R, _, _, _) := B_R a1 a2 p in R) a3 a4 ->
                                        (let (R, _, _, _) := I_R in R) 
                                          (BI a1 a3) (BI₂ a2 a4)) 
                                (H : I) (H0 : I₂) (H1 : (let (R, _, _, _) := I_R in R) H H0)
                                (H2 : IWT I A B AI BI H) (H3 : IWT I₂ A₂ B₂ AI₂ BI₂ H0)
                                {struct H2} : Prop :=
         match H2 with
         | iwt _ _ _ _ _ a x =>
             match H3 with
             | iwt _ _ _ _ _ a₂ x0 =>
                 {a_R : (let (R, _, _, _) := A_R in R) a a₂ &
                 {_
                 : forall (H6 : B a) (H7 : B₂ a₂)
                     (H8 : (let (R, _, _, _) := B_R a a₂ a_R in R) H6 H7),
                   ReflParam_PIWNew_IWT_RR0 I I₂ I_R A A₂ A_R B B₂ B_R AI AI₂ AI_R BI BI₂
                     BI_R (BI a H6) (BI₂ a₂ H7) (BI_R a a₂ a_R H6 H7 H8) 
                     (x H6) (x0 H7) & True}}
             end
         end.


Fixpoint IWT_RPW_aux_half2
(I I₂ : Set) (I_R : GoodRel [Total; OneToOne; Irrel] I I₂)
                                (A A₂ : Set) (A_R : GoodRel [Total; OneToOne; Irrel] A A₂)
                                (B : A -> Set) (B₂ : A₂ -> Set)
                                (B_R : forall (H1 : A) (H2 : A₂),
                                       (let (R, _, _, _) := A_R in R) H1 H2 ->
                                       GoodRel [Total; OneToOne; Irrel] (B H1) (B₂ H2))
                                (AI : A -> I) (AI₂ : A₂ -> I₂)
                                (AI_R : forall (a1 : A) (a2 : A₂),
                                        (let (R, _, _, _) := A_R in R) a1 a2 ->
                                        (let (R, _, _, _) := I_R in R) (AI a1) (AI₂ a2))
                                (BI : forall a : A, B a -> I)
                                (BI₂ : forall a₂ : A₂, B₂ a₂ -> I₂)
                                (BI_R : forall (a1 : A) (a2 : A₂)
                                          (p : (let (R, _, _, _) := A_R in R) a1 a2)
                                          (a3 : B a1) (a4 : B₂ a2),
                                        (let (R, _, _, _) := B_R a1 a2 p in R) a3 a4 ->
                                        (let (R, _, _, _) := I_R in R) 
                                          (BI a1 a3) (BI₂ a2 a4)) 
                                (i1 : I) (i2 : I₂) (ir : (let (R, _, _, _) := I_R in R) i1 i2)
                                (p1 : IWT I A B AI BI i1) {struct p1} :
   sigT  (fun (p2 : IWT I₂ A₂ B₂ AI₂ BI₂ i2) => 
   IWT_RRG I I₂ I_R A A₂ A_R B B₂ B_R AI AI₂ AI_R BI BI₂ BI_R i1 i2 ir  p1 p2 ).
refine(
(match p1 in IWT _ _ _ _ _ i1 return (forall (i2:I₂) (ir: BestR I_R i1 i2), 
(sigT  (fun (p2 : IWT I₂ A₂ B₂ AI₂ BI₂ i2) => 
   IWT_RRG I I₂ I_R A A₂ A_R B B₂ B_R AI AI₂ AI_R BI BI₂ BI_R i1 i2 ir  p1 p2 )))
with
| iwt _ _ _ _ _ a1 f1 => 
  let a2 := projT1 (fst (Rtot A_R) a1) in
  let ar := projT2 (fst (Rtot A_R) a1) in
  let f2 := (fun b2 => 
      let b1 := projT1 (snd (Rtot (B_R a1 a2 ar)) b2) in
      let br := projT2 (snd (Rtot (B_R a1 a2 ar)) b2) in
      projT1 (IWT_RPW_aux_half2  _ _ I_R _ _ A_R  _ _ B_R _ _  AI_R _ _ BI_R 
        _ _ (BI_R _ _ ar _ _ br) (f1 b1))
        ) in
  let c2 := (iwt I₂ A₂ B₂ AI₂ BI₂ a2 f2) in 
  fun i2 ir => 
     _
  end) i2 ir).
  pose proof (@BestOne12 I I₂ I_R (AI a1) i2 (AI₂ a2) ir (AI_R a1 a2 ar)).
  subst i2.
  exists c2.
  simpl.
  exists ar.
  eexists; eauto.
  unfold f2. simpl. clear c2. clear f2. unfold ar. clear ar.
  unfold a2. clear ir. clear a2. simpl.
  intros.
 
  destruct (IWT_RPW_aux_half2 I I₂ I_R A A₂ A_R B B₂ B_R AI AI₂ AI_R BI BI₂ BI_R
        (BI a1
           (projT1
              (snd
                 (Rtot (B_R a1 (projT1 (fst (Rtot A_R) a1)) (projT2 (fst (Rtot A_R) a1))))
                 H7))) (BI₂ (projT1 (fst (Rtot A_R) a1)) H7)
        (BI_R a1 (projT1 (fst (Rtot A_R) a1)) (projT2 (fst (Rtot A_R) a1))
           (projT1
              (snd
                 (Rtot (B_R a1 (projT1 (fst (Rtot A_R) a1)) (projT2 (fst (Rtot A_R) a1))))
                 H7)) H7
           (projT2
              (snd
                 (Rtot (B_R a1 (projT1 (fst (Rtot A_R) a1)) (projT2 (fst (Rtot A_R) a1))))
                 H7)))
        (f1
           (projT1
              (snd
                 (Rtot (B_R a1 (projT1 (fst (Rtot A_R) a1)) (projT2 (fst (Rtot A_R) a1))))
                 H7)))).
  simpl.
  intros.
  Unshelve.
  eauto.
  simpl.
  clear irrr.
  subst i2.
  
  subst i2.  

    clear ir.
  subst i2.
  exists c2c.
  simpl.
  rewrite (eq_sym peq).
  
  
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
  pose proof (proj1 I_R_iso _ _ _ _ i_R ir2 eq_refl) as Hir2.
  subst.
  specialize (fun b₁ b₂ b_R => Hb b₁ (BI₂ a₂ b₂) (BI_R _ _ a_R _ _ b_R)).
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
  pose proof (proj2 (B_R_iso  _ _ _) _ _ _ _ b_R r eq_refl). subst.
  pose proof (B_R_irrel _ _ _ _ _ r b_R). subst.
  exact i.
Defined.

    let c2c := @transport I₂ (AI₂ a2) i2 (fun i : I₂ => IWT I₂ A₂ B₂ AI₂ BI₂ i) peq c2
