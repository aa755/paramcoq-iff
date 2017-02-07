
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
       ReflParam_PIWNew_IWT_RR0 (I I₂ : Set) (I_R : GoodRel [Total; OneToOne] I I₂)
                                (A A₂ : Set) (A_R : GoodRel [Total; OneToOne] A A₂)
                                (B : A -> Set) (B₂ : A₂ -> Set)
                                (B_R : forall (H1 : A) (H2 : A₂),
                                       (let (R, _, _) := A_R in R) H1 H2 ->
                                       GoodRel [Total; OneToOne] (B H1) (B₂ H2))
                                (AI : A -> I) (AI₂ : A₂ -> I₂)
                                (AI_R : forall (a1 : A) (a2 : A₂),
                                        (let (R, _, _) := A_R in R) a1 a2 ->
                                        (let (R, _, _) := I_R in R) (AI a1) (AI₂ a2))
                                (BI : forall a : A, B a -> I)
                                (BI₂ : forall a₂ : A₂, B₂ a₂ -> I₂)
                                (BI_R : forall (a1 : A) (a2 : A₂)
                                          (p : (let (R, _, _) := A_R in R) a1 a2)
                                          (a3 : B a1) (a4 : B₂ a2),
                                        (let (R, _, _) := B_R a1 a2 p in R) a3 a4 ->
                                        (let (R, _, _) := I_R in R) 
                                          (BI a1 a3) (BI₂ a2 a4)) 
                                (H : I) (H0 : I₂) (H1 : (let (R, _, _) := I_R in R) H H0)
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


Fixpoint IWT_iff_aux_half1
(I I₂ : Set) (I_R : GoodRel [Total; OneToOne] I I₂)
                                (A A₂ : Set) (A_R : GoodRel [Total; OneToOne] A A₂)
                                (B : A -> Set) (B₂ : A₂ -> Set)
                                (B_R : forall (H1 : A) (H2 : A₂),
                                       (let (R, _, _) := A_R in R) H1 H2 ->
                                       GoodRel [Total; OneToOne] (B H1) (B₂ H2))
                                (AI : A -> I) (AI₂ : A₂ -> I₂)
                                (AI_R : forall (a1 : A) (a2 : A₂),
                                        (let (R, _, _) := A_R in R) a1 a2 ->
                                        (let (R, _, _) := I_R in R) (AI a1) (AI₂ a2))
                                (BI : forall a : A, B a -> I)
                                (BI₂ : forall a₂ : A₂, B₂ a₂ -> I₂)
                                (BI_R : forall (a1 : A) (a2 : A₂)
                                          (p : (let (R, _, _) := A_R in R) a1 a2)
                                          (a3 : B a1) (a4 : B₂ a2),
                                        (let (R, _, _) := B_R a1 a2 p in R) a3 a4 ->
                                        (let (R, _, _) := I_R in R) 
                                          (BI a1 a3) (BI₂ a2 a4)) 
                                (i1 : I) (i2 : I₂) (ir : (let (R, _, _) := I_R in R) i1 i2)
                                (p1 : IWT I A B AI BI i1) {struct p1} :
   IWT I₂ A₂ B₂ AI₂ BI₂ i2 :=
(match p1 in IWT _ _ _ _ _ i1 return (forall (i2:I₂) (ir: BestR I_R i1 i2), 
  IWT I₂ A₂ B₂ AI₂ BI₂ i2)
with
| iwt _ _ _ _ _ a1 f1 => 
  (* in the indices_RR, the first varialbes need to be substituted by cRetIndices *)
  fun (i2: I₂) (ir: BestR I_R (AI a1) i2) =>
  let a2 := projT1 (fst (Rtot A_R) a1) in
  let ar := projT2 (fst (Rtot A_R) a1) in
  let f2 := (fun b2 => 
      let b1 := projT1 (snd (Rtot (B_R a1 a2 ar)) b2) in
      let br := projT2 (snd (Rtot (B_R a1 a2 ar)) b2) in
       (IWT_iff_aux_half1  _ _ I_R _ _ A_R  _ _ B_R _ _  AI_R _ _ BI_R 
        _ _ (BI_R _ _ ar _ _ br) (f1 b1))
        ) in
  let c2 : IWT I₂ A₂ B₂ AI₂ BI₂ (AI₂ a2) := (iwt I₂ A₂ B₂ AI₂ BI₂ a2 f2) in
  (* the part below hasn;t been implemented yet *)
    let peq := @BestOne12 I I₂ I_R (AI a1) i2 (AI₂ a2) ir (AI_R a1 a2 ar) in
    (@transport I₂ (AI₂ a2) i2 (fun i : I₂ => IWT I₂ A₂ B₂ AI₂ BI₂ i) peq c2)
      :IWT I₂ A₂ B₂ AI₂ BI₂ i2
  end) i2 ir.


Require Import PiTypeR.

Fixpoint IWT_RRG_tot_aux_half_combinator
(I I₂ : Set) (I_R : GoodRel [Total; OneToOne] I I₂)
                                (A A₂ : Set) (A_R : GoodRel [Total; OneToOne] A A₂)
                                (B : A -> Set) (B₂ : A₂ -> Set)
                                (B_R : forall (H1 : A) (H2 : A₂),
                                       (let (R, _, _) := A_R in R) H1 H2 ->
                                       GoodRel [Total; OneToOne] (B H1) (B₂ H2))
                                (AI : A -> I) (AI₂ : A₂ -> I₂)
                                (AI_R : forall (a1 : A) (a2 : A₂),
                                        (let (R, _, _) := A_R in R) a1 a2 ->
                                        (let (R, _, _) := I_R in R) (AI a1) (AI₂ a2))
                                (BI : forall a : A, B a -> I)
                                (BI₂ : forall a₂ : A₂, B₂ a₂ -> I₂)
                                (BI_R : forall (a1 : A) (a2 : A₂)
                                          (p : (let (R, _, _) := A_R in R) a1 a2)
                                          (a3 : B a1) (a4 : B₂ a2),
                                        (let (R, _, _) := B_R a1 a2 p in R) a3 a4 ->
                                        (let (R, _, _) := I_R in R) 
                                          (BI a1 a3) (BI₂ a2 a4)) 
                                (i1 : I) (i2 : I₂) (ir : (let (R, _, _) := I_R in R) i1 i2)
                                (p1 : IWT I A B AI BI i1)
                                {struct p1} :
   sigT  (fun (p2 : IWT I₂ A₂ B₂ AI₂ BI₂ i2) => 
   IWT_RRG I I₂ I_R A A₂ A_R B B₂ B_R AI AI₂ AI_R BI BI₂ BI_R i1 i2 ir  p1 p2 ).
 Proof.
  revert ir.
  revert i2.
  induction p1 as [a1 f1 Hind].
  set (a2 := projT1 (fst (Rtot A_R) a1)).
  set (ar := projT2 (fst (Rtot A_R) a1)).
  
  set (f2r :=totalPiHalfGood (B a1) (B₂ a2) (B_R a1 a2 ar) (fun b1 : B a1 => IWT I A B AI BI (BI a1 b1))
           (fun b2 : B₂ a2 => IWT I₂ A₂ B₂ AI₂ BI₂ (BI₂ a2 b2))
           (fun (b1 : B a1) (b2 : B₂ a2) (br : BestR (B_R a1 a2 ar) b1 b2)
              (p1 : IWT I A B AI BI (BI a1 b1)) (p2 : IWT I₂ A₂ B₂ AI₂ BI₂ (BI₂ a2 b2)) =>
            IWT_RRG I I₂ I_R A A₂ A_R B B₂ B_R AI AI₂ AI_R BI BI₂ BI_R (BI a1 b1) 
              (BI₂ a2 b2) (BI_R a1 a2 ar b1 b2 br) p1 p2)
           (fun (b1 : B a1) (b2 : B₂ a2) (br : BestR (B_R a1 a2 ar) b1 b2) =>
            IWT_RRG_tot_aux_half_combinator I I₂ I_R A A₂ A_R B B₂ B_R AI AI₂ AI_R BI BI₂ BI_R
              (BI a1 b1) (BI₂ a2 b2) (BI_R a1 a2 ar b1 b2 br)) f1).
  fold a2 in f2r.
  set (f2 := projT1 f2r).
  set (fr := projT2 f2r).
  set (c2 := (iwt _ _ _ _ _ a2 f2)).
  intros ? ?.

  (* do it one by one for all indices. or may a compinator? First make an inductive types
for indices, not indices_RRs. then the combinator will take indices of the first side and
the indices of the second side, and onetooneness of all indices_RRs and on mathing on it, change all indices all at once.

In onetoOne proof below, we are doing something different, we are rewriting from constructor proofs
 *)
  Fail pose proof (ProofIrrelevance.proof_irrelevance _ ir (AI_R a1 a2 ar)) (* too early *).
  pose proof (@BestOne12 I I₂ I_R (AI a1) i2 (AI₂ a2) ir (AI_R a1 a2 ar)) as onei.
  
  subst i2.
  Show Proof.
  (* now the types are same *)
  pose proof (ProofIrrelevance.proof_irrelevance _ (AI_R a1 a2 ar) ir).
  Show Proof.
  subst ir.
  Show Proof.

  exists c2.

  (* the part below is not needed for iff part. the part above is mostly same *)
  simpl.
  exists ar.
  exists fr.
  reflexivity.

  (* finally, we are left with mptcty_indices, an inductive generalizing eq.
   make a sepearate combinator that correspondingly generalizes proof irrelevance 
  and produces this proof under the assumption that  all the ingredients are Props, which they will be, because they
  are I_RRs of Sets/singleton Props *) 
Defined.

Arguments existT {A} {P} x p.

Fixpoint IWT_RRG_tot_no_combinator
(I I₂ : Set) (I_R : GoodRel [Total; OneToOne] I I₂)
                                (A A₂ : Set) (A_R : GoodRel [Total; OneToOne] A A₂)
                                (B : A -> Set) (B₂ : A₂ -> Set)
                                (B_R : forall (H1 : A) (H2 : A₂),
                                       (let (R, _, _) := A_R in R) H1 H2 ->
                                       GoodRel [Total; OneToOne] (B H1) (B₂ H2))
                                (AI : A -> I) (AI₂ : A₂ -> I₂)
                                (AI_R : forall (a1 : A) (a2 : A₂),
                                        (let (R, _, _) := A_R in R) a1 a2 ->
                                        (let (R, _, _) := I_R in R) (AI a1) (AI₂ a2))
                                (BI : forall a : A, B a -> I)
                                (BI₂ : forall a₂ : A₂, B₂ a₂ -> I₂)
                                (BI_R : forall (a1 : A) (a2 : A₂)
                                          (p : (let (R, _, _) := A_R in R) a1 a2)
                                          (a3 : B a1) (a4 : B₂ a2),
                                        (let (R, _, _) := B_R a1 a2 p in R) a3 a4 ->
                                        (let (R, _, _) := I_R in R) 
                                          (BI a1 a3) (BI₂ a2 a4)) 
                                (i1 : I) (i2 : I₂) (ir : (let (R, _, _) := I_R in R) i1 i2)
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
     (fun b1 b2 br => IWT_RRG_tot_no_combinator  _ _ I_R _ _ A_R  _ _ B_R _ _  AI_R _ _ BI_R 
         _ _ (BI_R _ _ ar _ _ br)) f1) in
   let f2 := projT1 f2r in
   let fr := projT2 f2r in
   let c2 := (iwt _ _ _ _ _ a2 f2) in
   fun i2 ir => 
     (fun (peq: AI₂ a2 = i2) => 
      @transport I₂ (AI₂ a2) i2 
         (fun i : I₂ =>  forall ir, reT _ (iwt _ _ _ _ _ a1 f1) i ir) peq 
         (fun ir => 
            let c2r := 
            existT ar
              (existT fr
                 (ProofIrrelevance.proof_irrelevance (BestR I_R (AI a1) (AI₂ a2)) ir
                    (AI_R a1 a2 ar)))
               in
              @existT _ _ c2 c2r) ir 
     )
       (@BestOne12 I I₂ I_R (AI a1) i2 (AI₂ a2) ir (AI_R a1 a2 ar))
   end i2 ir)).
Defined.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import ProofIrrelevance.

(** naming convention: unlike previous constructions, here there are two 2s and RRs.
In the other direction, there would be two 1s and RRs.
In each case, the first one is named as usual (id/vprime/vrel)
The second one of each category has an "o" (o for oneToOne) appende to its name.
The 
As the proof progresses, equality proofs are generated and _o's become _ 
(not the other way around).
*)
Fixpoint IWT_RPW_oneOneHalf
(I I₂ : Set) (I_R : GoodRel [Total; OneToOne] I I₂)
                                (A A₂ : Set) (A_R : GoodRel [Total; OneToOne] A A₂)
                                (B : A -> Set) (B₂ : A₂ -> Set)
                                (B_R : forall (H1 : A) (H2 : A₂),
                                       (let (R, _, _) := A_R in R) H1 H2 ->
                                       GoodRel [Total; OneToOne] (B H1) (B₂ H2))
                                (AI : A -> I) (AI₂ : A₂ -> I₂)
                                (AI_R : forall (a1 : A) (a2 : A₂),
                                        (let (R, _, _) := A_R in R) a1 a2 ->
                                        (let (R, _, _) := I_R in R) (AI a1) (AI₂ a2))
                                (BI : forall a : A, B a -> I)
                                (BI₂ : forall a₂ : A₂, B₂ a₂ -> I₂)
                                (BI_R : forall (a1 : A) (a2 : A₂)
                                          (p : (let (R, _, _) := A_R in R) a1 a2)
                                          (a3 : B a1) (a4 : B₂ a2),
                                        (let (R, _, _) := B_R a1 a2 p in R) a3 a4 ->
                                        (let (R, _, _) := I_R in R) 
                                          (BI a1 a3) (BI₂ a2 a4)) 
                                (i1 : I) (i2 : I₂) 
                                (ir : (let (R, _, _) := I_R in R) i1 i2)
                                (* the part above is just indArgs_R *)
                                (t1 : IWT I A B AI BI i1) 
                           (t2 t2o: IWT I₂ A₂ B₂ AI₂ BI₂ i2)
 (tr :  IWT_RRG I I₂ I_R A A₂ A_R B B₂ B_R AI AI₂ AI_R BI BI₂ BI_R i1 i2 ir t1 t2)
 (tro :  IWT_RRG I I₂ I_R A A₂ A_R B B₂ B_R AI AI₂ AI_R BI BI₂ BI_R i1 i2 ir t1 t2o)
      {struct t1} : (t2=t2o).
Proof using.
  destruct t1 as [a1 f1].
  
  (* this destruct also changes the type (specifically, the indices) of t2o.
    this is necessary for the conclusion t2 = t2o to be well typed.
   thus, t2o needs to be included in the Pi type *)
  destruct t2 as [a2 f2].
(* can these 3 steps be done later? No. becore destructing t2o, the indices equality
has to be cleared. done here as _.
When building terms, this is not a problem, as we just don't need to include
the (to be cleared) hyps as foralls when generalizing for equality *)
simpl in tr.

(* for branches ij, such that i<>j, use False_rect here. This part is not captured
in this example. *)
destruct tr as [ar tr].
destruct tr as [fr _].

(* just putting muliple exists should suffice here *)
assert (
@existT _ (fun x : I₂ => IWT I₂ A₂ B₂ AI₂ BI₂ x) (AI₂ a2) (iwt I₂ A₂ B₂ AI₂ BI₂ a2 f2) =
@existT _ (fun x : I₂ => IWT I₂ A₂ B₂ AI₂ BI₂ x) (AI₂ a2) t2o) as Hex.
(* in general, there would be one such construction for each constructor. 
Also, use false elim for constructors that dont match *)
- Show Proof.
  destruct t2o as [a2o f2o]. (* only indIndices and tro are in Pis *)
  Show Proof.
  simpl in tro.

(* Again,for branches ij, such that i<>j, use False_rect here. This part is not captured
in this example. *)
  
  destruct tro as [aro tro].
  destruct tro as [fro _]. (* the indices eq is not needed *)
  clear ir. (* ir was mentioned in the indiceseq which is now gone *)

  (* do the following 2 substitutions one by one for each constructor argument.
    the second step of replacing aro is not needed for recursive arguments. *)
  pose proof (BestOne12 A_R _ _ _ ar aro). subst a2o. (* A one to one *)
  pose proof (ProofIrrelevance.proof_irrelevance  _ aro ar). subst aro.
  
  pose proof (onePiHalfGood (B a1) (B₂ a2) (B_R a1 a2 ar) (fun b1 : B a1 => IWT I A B AI BI (BI a1 b1))
           (fun b2 : B₂ a2 => IWT I₂ A₂ B₂ AI₂ BI₂ (BI₂ a2 b2))
           (fun (b1 : B a1) (b2 : B₂ a2) (br : BestR (B_R a1 a2 ar) b1 b2)
              (p1 : IWT I A B AI BI (BI a1 b1)) (p2 : IWT I₂ A₂ B₂ AI₂ BI₂ (BI₂ a2 b2)) =>
            IWT_RRG I I₂ I_R A A₂ A_R B B₂ B_R AI AI₂ AI_R BI BI₂ BI_R (BI a1 b1) 
              (BI₂ a2 b2) (BI_R a1 a2 ar b1 b2 br) p1 p2)
           (fun (b1 : B a1) (b2 : B₂ a2) (br : BestR (B_R a1 a2 ar) b1 b2) =>
            IWT_RPW_oneOneHalf I I₂ I_R A A₂ A_R B B₂ B_R AI AI₂ AI_R BI BI₂ BI_R
              (BI a1 b1) (BI₂ a2 b2) (BI_R a1 a2 ar b1 b2 br))
              (* the part above was exactly the same as that for the totality case
               totalPiHalfGood was replaces with onePiHalfGood
               and the the name of the recursive call was update to IWT_RPW_oneOneHalf
               Also, also note the renames 
                *)
           f1 f2 f2o fr fro) as f2r.
  subst f2o.
  (* no need to substitute fro because recursive arguments cannot be mentioned in 
   cRetIndices or indices or later args *)
  
  reflexivity.
- (* the indices are exactly same in Hex. repeated application of inj_pair2 should work. *)
  apply inj_pair2 in Hex. subst. reflexivity.
Defined.

Require Import SquiggleEq.tactics.  
(* wont need this if [Set]=Prop 
Lemma IWT_RPW_irrel
(I I₂ : Set) (I_R : GoodRel [Total; OneToOne] I I₂)
                                (A A₂ : Set) (A_R : GoodRel [Total; OneToOne] A A₂)
                                (B : A -> Set) (B₂ : A₂ -> Set)
                                (B_R : forall (H1 : A) (H2 : A₂),
                                       (let (R, _, _) := A_R in R) H1 H2 ->
                                       GoodRel [Total; OneToOne] (B H1) (B₂ H2))
                                (AI : A -> I) (AI₂ : A₂ -> I₂)
                                (AI_R : forall (a1 : A) (a2 : A₂),
                                        (let (R, _, _) := A_R in R) a1 a2 ->
                                        (let (R, _, _) := I_R in R) (AI a1) (AI₂ a2))
                                (BI : forall a : A, B a -> I)
                                (BI₂ : forall a₂ : A₂, B₂ a₂ -> I₂)
                                (BI_R : forall (a1 : A) (a2 : A₂)
                                          (p : (let (R, _, _) := A_R in R) a1 a2)
                                          (a3 : B a1) (a4 : B₂ a2),
                                        (let (R, _, _) := B_R a1 a2 p in R) a3 a4 ->
                                        (let (R, _, _) := I_R in R) 
                                          (BI a1 a3) (BI₂ a2 a4))
                                (i1 : I) (i2 : I₂) 
                                (ir : (let (R, _, _) := I_R in R) i1 i2):
relIrrUptoEq (IWT_RRG _ _ I_R _ _ A_R _ _ B_R _ _ AI_R _ _ BI_R _ _ ir).
Proof using.
  unfold relIrrUptoEq.
  intro t1. induction t1. intro t2. destruct t2.
  simpl.
  intros.
   exrepnd. subst.
   pose proof (Rirrel A_R _ _ a_R0 a_R). subst.
   f_equal.
   assert (v=v0) by admit. (* needs functionalextensionality? *)
   subst.
   f_equal.
   (* need UIP on I_R *)
Abort.
*)


