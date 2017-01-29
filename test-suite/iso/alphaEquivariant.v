Require Import Parametricity.
Require Import List.
(* Require Import rpropG. *)
Require Export compInd.
Require Export common.


Definition pmap {A B} (f:A->B) (sw: A*A) : B*B:= 
match sw with
| pair a b => (f a, f b)
end.

Definition isInl {A B} (d: {A}+{B}) : bool:=
match d with
| left _ =>  true
| right _ => false
end.

Require Import Coq.Unicode.Utf8.



Set Imlicit Arguments.

Class DecEq (T:Type) :=
  decEq : forall (a b : T) , {a=b}+{a<>b}.

Section Tm.
Set Imlicit Arguments.


Variable V:Type.
Inductive Tm : Type :=
| var : V -> Tm
| lam : V -> Tm -> Tm
| app : Tm -> Tm -> Tm.

Fixpoint size (t:Tm) : nat :=
match t with
| var _ => 1
| app l r => 1 + (size l + size r)
| lam _ b => 1 + size b
end.

Require Import rpropL.

End Tm.

Parametricity Tm.
Parametricity size.
Print size_R.




Arguments var {_} v.
Arguments lam {_} v b.
Arguments app {_} f a.
Arguments size {_} t.

Fixpoint tmap {A B : Type} (f:A->B) (t : Tm A) : Tm B :=
match t with
| var v => var (f v)
| lam v b => lam (f v) (tmap f b)
| app g a => app (tmap f g) (tmap f a)
end.

Lemma size_map {A B : Type}: forall (f: A-> B)
   (t:Tm A), size t = size (tmap f t).
Proof.
  induction t; simpl; auto.
Qed.

Section Nom.

Context {V:Type} {vd: DecEq V}.

Definition swapVar (swapping : V * V)
           (v  : V)
: V :=
  let (a,b) := swapping in
  if decEq v a
  then b
  else if decEq v b
       then a
       else v.

Require Import Omega.
Parametricity Nat.add_comm.
Parametricity le_n_S.
Parametricity Peano.le_0_n.
Lemma le_plus_l : forall n m, (n ≤ n + m).
induction n; intro m.
- simpl. apply Peano.le_0_n.
- simpl. apply le_n_S. eauto.
Defined.


Parametricity Recursive le_plus_l.

Lemma Tm_rects: ∀ P : Tm V → Type,
(∀ v : V, P (var v))
→ (∀ t : Tm V, P t → ∀ t0 : Tm V, P t0 → P (app t t0)) 
→ (∀ (v : V) (t : Tm V), (forall (ts: Tm V),  size ts ≤ size t → P ts) → P (lam v t))
→ ∀ t : Tm V, P t.
Proof.
  intros ? Hv Ha Hl.
  assert (forall n t, size t = n -> P t) as Hass;[| eauto].
  induction n using comp_ind.
  intros t Heq. destruct t; [apply Hv | |]; simpl in Heq; subst.
- apply Hl; auto.
  intros.
  apply (X (size ts)); trivial. apply le_n_S. assumption.
- apply Ha; eapply X; try reflexivity; unfold lt;[| rewrite Nat.add_comm];
  rewrite <- Nat.add_succ_l; apply le_plus_l.
Defined.



Fixpoint remove  (l:list V) (r: V): list V :=
match l with
| nil => nil
| cons h tl => if (decEq h r) then (remove tl r) else h::(remove tl r)
end.


Lemma in_deq :
  forall x : V,
  forall l,
     {In x l} + {~In x l}.
Proof.
  induction l; simpl; auto.
  destruct (decEq a x); subst; auto.
  destruct IHl; auto.
  right.  tauto.
Defined.


Import ListNotations.

Fixpoint allVars  (t : Tm V) : list V :=
match t with
| var v => [v]
| lam v b => remove (allVars b) v
| app f a => (allVars f) ++ (allVars a) 
end.

Definition tswap (swapping : V * V) := (tmap (swapVar swapping)).

Inductive αeq : (Tm V) -> (Tm V) -> Prop :=
|αvar : forall v, αeq (var v) (var v)
|αapp : forall f1 f2 a1 a2,
  αeq f1 f2
  -> αeq a1 a2
  -> αeq (app f1 a1) (app f2 a2)
|αlam : forall v v1 v2 b1 b2,
   (~ In v ([v1;v2] ++ allVars b1 ++ allVars b2))
   -> αeq  (tswap (v1,v) b1) (tswap (v2,v) b2)
   -> αeq (lam v1 b1) (lam v2 b2).

Inductive αeqe : (Tm V) -> (Tm V) -> Prop :=
|αvare : forall v, αeqe (var v) (var v)
|αappe : forall f1 f2 a1 a2,
  αeqe f1 f2
  -> αeqe a1 a2
  -> αeqe (app f1 a1) (app f2 a2)
|αlame : forall v1 v2 b1 b2,
    (exists v, (~ In v ([v1;v2] ++ allVars b1 ++ allVars b2))
      /\ αeqe  (tswap (v1,v) b1) (tswap (v2,v) b2))
   -> αeqe (lam v1 b1) (lam v2 b2).

(*
https://github.coecis.cornell.edu/aa755/nuprl2coq/blob/vincent/coq/swap.v
*)
Definition TQs : nat -> Type :=
fun n => match n with O => bool | _ => V end.

(* dummy *)
Definition TEQs : nat -> Type :=
fun n =>  bool.

Fixpoint αeqrDummy (l r: Tm V) : RProp TQs TEQs:=
match (l,r) with
| (var v1, var v2) => injB _ _ (isInl (decEq v1 v2))
| (app f1 a1, app f2 a2) => rconj 0 eq_refl (αeqrDummy f1 f2) (αeqrDummy a1 a2)
| (lam v1 b1, lam v2 b2) => 
    let allv :=  ([v1;v2] ++ allVars b1 ++ allVars b2) in
    rforall _ _ 1 (fun v => injB _ _ (implb (isInl (in_deq v allv)) true))
(* termination check will screw up. Note that the statement of the
parametricity theorem doesn't depend on the definition, but only the type.
The proof does depend on the definition *)
| (_, _) => injB _ _ false
end.

Definition αeqr (l r: Tm V) : RProp TQs TEQs.
revert r. revert l.
apply (Tm_rects (fun _ => Tm V → RProp TQs TEQs)).
- intros v1 r.
  let tac := exact (injB  _ _ false) in destruct r;[ |tac|tac].
  exact (injB _ _ (isInl (decEq v1 v))).
- intros _ rf1 _ ra1 tr.
  let tac := exact (injB _ _ false) in destruct tr;[tac| tac |].
  rename tr1 into f2. rename tr2 into a2.
  exact (rconj  0 eq_refl (rf1 f2) (ra1 a2)).

- intros v1 b1 r tr.
  let tac := exact (injB _ _ false) in destruct tr;[tac| | tac].
  rename v into v2. rename tr into b2.
  refine (
  let allv :=  ([v1;v2] ++ allVars b1 ++ allVars b2) in
  rforall _ _ 1 (fun v => if (in_deq v allv) then (injB _ _ true) else _)).
  apply (fun p =>  r (tswap (v1,v) b1) p (tswap (v2,v) b2)).
  unfold tswap.
  rewrite <- size_map. reflexivity.
Defined.

Lemma  Nateq_decc : forall n, Nat.eq_dec n n = left eq_refl.
Proof.
  intros. induction n; auto.
  simpl. rewrite IHn. reflexivity.
Qed.

Check plus_n_O.

Lemma αeqr_app : forall v1 t1 v2 t2, 
  αeqr (app v1 t2) (app v2 t2)
  = rconj 0 eq_refl (αeqr v1 v2) (αeqr t1 t2).
Proof.
  intros. 
  simpl. unfold αeqr. simpl. unfold Tm_rects, comp_ind. simpl.
  rewrite Nateq_decc. simpl.
Abort.

(*
Lemma αeqr_val : forall v1 v2 
  αeqr (var v1) (var v2)
  = rconj V (αeqr v1 v2) (αeqr t1 t2).
Proof.
  intros. 
  simpl. unfold αeqr. simpl. unfold Tm_rects, comp_ind. simpl.
  rewrite Nateq_decc. simpl.
Qed.
*)

Lemma αeqr_lam : forall v1 b1 v2 b2, 
  αeqr (lam v1 b2) (lam v2 b2)
  = let allv :=  ([v1;v2] ++ allVars b1 ++ allVars b2) in
    rforall TQs TEQs 1 (fun v => 
        if (in_deq v allv) 
        then (injB _ _ true) 
        else αeqr (tswap (v1,v) b1)  (tswap (v2,v) b2)).
Abort.


Definition αeqrp a b := (rPropSemantics (αeqr a b)).

Lemma αeqr_correct: forall l r,
  (αeqrp l r) <-> αeq l r.
Proof.
  unfold αeqrp.
  induction l; intro r.
- simpl. unfold αeqr, Tm_rects, comp_ind. simpl. vm_compute.
  destruct r; try tauto.
Abort.



End Nom.




Parametricity  Tm_rects.


Parametricity remove.
Parametricity swapVar.

Parametricity αeqr.



(* R = fun x y => varClass x = 0 /\ varClass y =0. *)


Section Test.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Logic.Eqdep_dec.

Variable (Var:Type) (permute : Var -> Var) (dec: DecEq Var).
Hypothesis permuteInj (* iso *) : forall (a b:Var), a=b <-> (permute a) = (permute b).


Definition similar (a b : Var) : Prop := b= permute a.

Lemma similarImplementations : 
forall (a₁ a₂ : Var) (a_R : similar a₁ a₂) (b₁ b₂ : Var) (b_R : similar b₁ b₂),
sumbool_R (a₁ = b₁) (a₂ = b₂) (eq_R Var Var similar a₁ a₂ a_R b₁ b₂ b_R) 
  (a₁ <> b₁) (a₂ <> b₂)
  (not_R (a₁ = b₁) (a₂ = b₂) (eq_R Var Var similar a₁ a₂ a_R b₁ b₂ b_R)) 
  (dec a₁ b₁) (dec a₂ b₂).
Proof.
  intros. unfold similar in *. simpl in *.
  subst.
  destruct (dec a₁ b₁); auto.
- pose proof e as eb.
  apply permuteInj in eb.
  destruct (dec (permute a₁) (permute b₁)); try contradiction.
  constructor. subst. simpl.
  pose proof (UIP_dec dec e0 eq_refl) as X.
  rewrite X. constructor.

- pose proof n as nb.
  rewrite permuteInj in nb.
  destruct (dec (permute a₁) (permute b₁)); try contradiction.
  constructor.
  simpl. unfold not_R. simpl. intros.
  inversion H1. subst.
  contradiction.
Qed.



Require Import CMorphisms.

(*
Lemma rpropIff: 
  Proper ((RProp_R _ _ similar) ==> iff) (@rPropSemantics Var).
Proof using.
  intros ? ? Hr.
  induction Hr.
- inversion b1; reflexivity.
(* what if in some application we have to pick a relation that is not total? *)
- simpl in *. admit.
- simpl. split; intros Hh t.
  + eapply H; eauto. apply nat_R_refl.
  + eapply H; eauto; apply nat_R_refl.
Admitted.
*)


(* Definition equivariant (R: Tm -> Tm -> Prop) *)
Require Import Program.Basics.

Open Scope program_scope.
SearchAbout compose.
Let TQs := (@TQs Var).

Definition TQs_R  (H H0 : nat) (p: nat_R H H0) : TQs H -> TQs H0 -> Type.
destruct p.
- simpl. exact bool_R.
- simpl. exact similar.
Defined.



Definition TEQs_R  (H H0 : nat) (p: nat_R H H0) : TEQs H -> TEQs H0 -> Type.
exact bool_R.
Defined.



Lemma αeqrRespects :
  Proper ((Tm_R _ _ similar) ==> (Tm_R _ _ similar) 
      ==> (RProp_R  TQs TQs TQs_R TEQs TEQs TEQs_R))
     (@αeqr Var _).
Proof.
  pose proof  (αeqr_R Var Var similar _ _ similarImplementations).
  simpl in *.
  intros ? ? ? ? ? ?.
  apply X; auto.
Defined.



Definition lsimilar (a b : list Var) : Prop := b= List.map permute a.

Lemma lsimilar_listR : forall (l1 l2 : list Var), 
  ((list_R Var Var similar l1 l2) <=> lsimilar l1 l2).
Proof.
  unfold lsimilar.
  induction l1; destruct l2; simpl; try firstorder; try discriminate; try contradiction;
  try constructor.
  inversion X.
  inversion X.
  inversion X. subst. f_equal;eauto. apply IHl1. auto.

  inversion H. subst. reflexivity.
  inversion H. subst.
  apply IHl1. reflexivity.
Qed.

Lemma Tm_R_swap : forall (a b: Tm Var), (Tm_R _ _ similar a b) <=> (b = tmap permute a).
Proof.
  unfold similar.
  induction a; intros ?; split; intros Hx; try inversion Hx; subst; try clear Hx;
  auto; simpl; try constructor; auto.
- f_equal. apply IHa. assumption.
- clear H. apply IHa. reflexivity.
- f_equal;[ apply IHa1; assumption | apply IHa2; assumption].
- clear H. apply IHa1; auto.
- clear H. apply IHa2; auto.
Defined.

Lemma tv : TotalHeteroRel similar.
Admitted.

Lemma equivariantHalf (a b : Tm Var) : 
 (αeqrp (tmap permute a) (tmap permute b)) -> (αeqrp a b).
Proof.
  eapply rpropIff.
  eapply αeqrRespects ; apply Tm_R_swap; reflexivity.
  intros ? ? p. destruct p; simpl.
- split; intros t; destruct t; eexists; constructor.
- apply tv.
- intros ? ? ? ? ? ? ? ? ?.
  unfold TEQs, TEQs_R in *.
  apply bool_R_eq in X.
  apply bool_R_eq in X0.
  subst. tauto.
Qed.


Lemma equivariantHalfP (a b : Tm Var) : 
 (αeqrp (tmap permute a) (tmap permute b)) -> (αeqrp a b).
Proof.
  intros p.
  (* can we assume here that p only uses [dec]?
  While instantiating this lemma, we will have a particular implementation of Var, 
  nat, and thus allows on to use more than just [dec] in the proof.
  This will be illustrated below.
 *)
Abort.

Section NonParamProof.
  Variable (a : Tm Var).
  Variable toNatFromNat : (Var <=> nat). (* now all nominality is broken *)
  Lemma prefl : (αeqrp (tmap permute a) (tmap permute a)).
  Proof using toNatFromNat.
  Abort.

(*  Check (equivariantHalf a a prefl). *)
End NonParamProof.





(* the proofs proofs below are independent of the definition of remove
    (repace remove_R appropriately), which is great for complex functions *)

Lemma removeRespects :
  Proper (lsimilar ==> similar ==> lsimilar) (@remove Var _).
Proof.
  intros ? ? ? ? ? ?.
  apply lsimilar_listR in H. apply lsimilar_listR.
  pose proof  (remove_R Var Var similar _ _ similarImplementations);
    auto.
Qed.


Lemma removeEquivariant :
  forall la r, 
    map permute (remove la r) = remove (map permute la) (permute r).
Proof.
  simpl.
  intros ? ?.
  pose proof (removeRespects la (map permute la) eq_refl r (permute r) eq_refl) as H.
  unfold lsimilar in H.
  congruence.
Qed.

(* the proof did not have to reason at all about how swapVar computes, unlike
the previous proof *)
Lemma swapVarPerm:
  forall p v, 
    permute (swapVar p v) = swapVar (pmap permute p) (permute v).
Proof.
  simpl.
  intros ? ?.
  pose proof  (swapVar_R Var Var similar _ _ similarImplementations) as Hx.
  unfold similar in *. unfold pmap in *. destruct p.
  erewrite <- Hx; eauto.
  constructor; reflexivity.
Qed.






Variable vc : Var -> bool.


Definition similarvc (a b : Var) : Prop := 
  a=b /\ vc a = true /\ vc b = true.

Lemma similarImplementationsVC : 
forall (a₁ a₂ : Var) (a_R : similarvc a₁ a₂) (b₁ b₂ : Var) (b_R : similarvc b₁ b₂),
sumbool_R (a₁ = b₁) (a₂ = b₂) (eq_R Var Var similarvc a₁ a₂ a_R b₁ b₂ b_R) 
  (a₁ <> b₁) (a₂ <> b₂)
  (not_R (a₁ = b₁) (a₂ = b₂) (eq_R Var Var similarvc a₁ a₂ a_R b₁ b₂ b_R)) 
  (dec a₁ b₁) (dec a₂ b₂).
  intros. unfold similar in *. simpl in *.
  unfold similarvc in *. destruct a_R, b_R. subst.
  destruct (dec a₂ b₂) ; subst; econstructor; auto ; try econstructor; eauto.

+ simpl. destruct a, a0.
  pose proof (UIP_dec Bool.bool_dec e e1) as X.
  pose proof (UIP_dec Bool.bool_dec e0 e2) as Xx.
  subst.
  constructor.

+  simpl. unfold not_R. simpl. intros.
  inversion H1. subst.
   contradiction.
Defined.

Ltac repnd :=
  repeat match goal with
           | [ H : _ /\ _ |- _ ] =>
               let name := fresh H in destruct H as [name H]
           | [ H : prod _ _ |- _ ] =>
               let name := fresh H in destruct H as [name H]
         end.
Lemma lsimilarvc_listR : forall (l1 l2 : list Var), 
  (list_R Var Var similarvc l1 l2) <=> 
      (l1=l2 /\ Forall (fun x => vc x = true) l1).
Proof.
  unfold similarvc.
  induction l1; destruct l2; simpl; split; intros X;
  simpl in  *; inversion X; eauto 5; try constructor; eauto; subst; try tauto; repnd;
  subst;
  try discriminate; try constructor; eauto; try tauto; try congruence.
- inversion X. subst. f_equal. apply IHl1; auto.
- eapply IHl1; eauto.
- inversion H. subst. inversion X. subst. auto.
- inversion H. subst.  apply IHl1. split; auto.
  inversion X. auto.
Qed.


Lemma removeRespectsVC :
  forall (l: list Var) r, 
  Forall (fun x => vc x = true) l
  -> vc r = true
  -> Forall (fun x => vc x = true) (remove l r ).
Proof.
  intros ? ? Hl Hr.
  apply (lsimilarvc_listR _ (remove l r)).
  pose proof  (remove_R Var Var _ _ _ similarImplementationsVC) as H; auto.
  simpl in H.
  apply H; auto.
- apply lsimilarvc_listR; auto.
- split; auto.
Qed.


End Test.


