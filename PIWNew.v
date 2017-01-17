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
                   ReflParam_PIWNew_IWT_RR0 I I₂ I_R  A A₂ A_R B B₂ B_R AI AI₂ AI_R BI BI₂
                     BI_R (BI a a1) (BI₂ a₂ a2) (BI_R a a₂ a_R a1 a2 p) 
                     (x a1) (x0 a2) & (ir=(AI_R a a₂ a_R))}}
             end
         end) H1.

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
          let reT i1 i2 := forall (ir : BestR I_R i1 i2), Prop in
         (match H2 as iwt1 in IWT _ _ _ _ _ i1 return reT i1 H0 
         with
         | iwt _ _ _ _ _ a x =>
             match H3 as iwt2 in IWT _ _ _ _ _ i2 return reT (AI a) i2
             with
             | iwt _ _ _ _ _ a₂ x0 =>
              fun ir =>
                 {a_R : BestR A_R a a₂ &
                 {_
                 : forall (a1 : B a) (a2 : B₂ a₂) (p : BestR (B_R a a₂ a_R) a1 a2),
                   ReflParam_PIWNew_IWT_RR0 I I₂ I_R  A A₂ A_R B B₂ B_R AI AI₂ AI_R BI BI₂
                     BI_R (BI a a1) (BI₂ a₂ a2) (BI_R a a₂ a_R a1 a2 p) 
                     (x a1) (x0 a2) & (ir=(AI_R a a₂ a_R))}}
             end
         end) H1.


Fixpoint IWT_RPW_aux_half1
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
   IWT I₂ A₂ B₂ AI₂ BI₂ i2 :=
(match p1 in IWT _ _ _ _ _ i1 return (forall (i2:I₂) (ir: BestR I_R i1 i2), 
  IWT I₂ A₂ B₂ AI₂ BI₂ i2)
with
| iwt _ _ _ _ _ a1 f1 => 
  let a2 := projT1 (fst (Rtot A_R) a1) in
  let ar := projT2 (fst (Rtot A_R) a1) in
  let f2 := (fun b2 => 
      let b1 := projT1 (snd (Rtot (B_R a1 a2 ar)) b2) in
      let br := projT2 (snd (Rtot (B_R a1 a2 ar)) b2) in
       (IWT_RPW_aux_half1  _ _ I_R _ _ A_R  _ _ B_R _ _  AI_R _ _ BI_R 
        _ _ (BI_R _ _ ar _ _ br) (f1 b1))
        ) in
  let c2 := (iwt I₂ A₂ B₂ AI₂ BI₂ a2 f2) in 
  fun i2 ir =>
  (* the part below hasn;t been implemented yet *)
    let peq := @BestOne12 I I₂ I_R (AI a1) i2 (AI₂ a2) ir (AI_R a1 a2 ar) in
    @transport I₂ (AI₂ a2) i2 (fun i : I₂ => IWT I₂ A₂ B₂ AI₂ BI₂ i) peq c2
  end) i2 ir.


Require Import PiTypeR.
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
let reT i1 p1 i2 ir :=
(sigT  (fun (p2 : IWT I₂ A₂ B₂ AI₂ BI₂ i2) => 
   IWT_RRG I I₂ I_R A A₂ A_R B B₂ B_R AI AI₂ AI_R BI BI₂ BI_R i1 i2 ir p1 p2 )) in
(match p1 in IWT _ _ _ _ _ i1 return (forall (i2:I₂) (ir: BestR I_R i1 i2),
  reT i1 p1 i2 ir )
with
| iwt _ _ _ _ _ a1 f1 => 
  let a2 := projT1 (fst (Rtot A_R) a1) in
  let ar := projT2 (fst (Rtot A_R) a1) in
  let f2r := ((totalPiHalfGood _ _ (B_R _ _ ar)) _ _ _ 
    (fun b1 b2 br => IWT_RPW_aux_half2  _ _ I_R _ _ A_R  _ _ B_R _ _  AI_R _ _ BI_R 
        _ _ (BI_R _ _ ar _ _ br)) f1) in
  let f2 := projT1 f2r in
  let fr := projT2 f2r in
  let c2 := (iwt _ _ _ _ _ a2 f2) in
  let c2r := (@existT _ _ ar (@existT _ _ fr Logic.I)) in
  fun i2 ir => 
    (fun (peq: AI₂ a2 = i2) => 
     @transport I₂ (AI₂ a2) i2 
        (fun i : I₂ =>  forall ir, reT _ (iwt _ _ _ _ _ a1 f1) i ir) peq 
         (fun ir => @existT _ _ c2 c2r) ir 
    )
      (@BestOne12 I I₂ I_R (AI a1) i2 (AI₂ a2) ir (AI_R a1 a2 ar))
  end i2 ir)).
Defined.

(* one less admit due to irrelevance of [RRGS] *)
Fixpoint IWT_RRGS_aux_half2
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
   IWT_RRGS I I₂ I_R A A₂ A_R B B₂ B_R AI AI₂ AI_R BI BI₂ BI_R i1 i2  p1 p2 ).
refine(
(match p1 in IWT _ _ _ _ _ i1 return (forall (i2:I₂) (ir: BestR I_R i1 i2), 
(sigT  (fun (p2 : IWT I₂ A₂ B₂ AI₂ BI₂ i2) => 
   IWT_RRGS I I₂ I_R A A₂ A_R B B₂ B_R AI AI₂ AI_R BI BI₂ BI_R i1 i2 p1 p2 )))
with
| iwt _ _ _ _ _ a1 f1 => 
  let a2 := projT1 (fst (Rtot A_R) a1) in
  let ar := projT2 (fst (Rtot A_R) a1) in
  let f2 := (fun b2 => 
      let b1 := projT1 (snd (Rtot (B_R a1 a2 ar)) b2) in
      let br := projT2 (snd (Rtot (B_R a1 a2 ar)) b2) in
      projT1 (IWT_RRGS_aux_half2  _ _ I_R _ _ A_R  _ _ B_R _ _  AI_R _ _ BI_R 
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
 (* this is the recursive term recRet. max one for each argument *)
  destruct (IWT_RRGS_aux_half2 I I₂ I_R A A₂ A_R B B₂ B_R AI AI₂ AI_R BI BI₂ BI_R
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
  simpl in *. 
 (* this is the recursive term recRet *)
  
  destruct ( (snd (Rtot (B_R a1 (projT1 (fst (Rtot A_R) a1)) (projT2 (fst (Rtot A_R) a1))))
               H7)).
               simpl in *.
  assert (@eq (B a1) x0 H6) by admit. subst.
  simpl in *. exact i.
Abort.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import ProofIrrelevance.

Print oneToOneHalf.
Fixpoint IWT_RPW_oneOneHalf
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
                                (i1 : I) (i2 : I₂) 
                                (ir : (let (R, _, _, _) := I_R in R) i1 i2)
                                (t1 : IWT I A B AI BI i1) 
                           (tx2 ty2: IWT I₂ A₂ B₂ AI₂ BI₂ i2)
 (ra :  IWT_RRGS I I₂ I_R A A₂ A_R B B₂ B_R AI AI₂ AI_R BI BI₂ BI_R i1 i2 t1 tx2)
 (rb :  IWT_RRGS I I₂ I_R A A₂ A_R B B₂ B_R AI AI₂ AI_R BI BI₂ BI_R i1 i2 t1 ty2)
      {struct t1} : (tx2=ty2).
Proof using.
destruct t1.
destruct tx2 as [a2 ff].
simpl in ra.
destruct ra as [ar ra].
destruct ra as [ffr _].
Show Proof.
assert (
existT (fun x : I₂ => IWT I₂ A₂ B₂ AI₂ BI₂ x) (AI₂ a2) (iwt I₂ A₂ B₂ AI₂ BI₂ a2 ff) =
     existT (fun x : I₂ => IWT I₂ A₂ B₂ AI₂ BI₂ x) (AI₂ a2) ty2) as Hex.
- destruct ty2. simpl in rb.
  destruct rb as [br rb].
  destruct rb as [ffrb _].
  pose proof (BestOne12 A_R _ _ _ ar br). subst.
  f_equal.
  f_equal.
  apply functional_extensionality_dep.
  intros b₂.
  set (b1 := BestTot21 (B_R _ _ ar) b₂).
  set (b1r := BestTot21R (B_R _ _ ar) b₂).
  unfold rInv in b1r.
  pose proof (Rirrel A_R _ _ ar br). subst.
  eapply IWT_RPW_oneOneHalf;[| apply ffr, b1r | apply ffrb, b1r]; simpl.
  apply BI_R with (p:=br). exact b1r.
- apply inj_pair2 in Hex. subst. reflexivity.
Defined.
 




