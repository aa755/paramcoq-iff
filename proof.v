Require Import Coq.Classes.DecidableClass.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import SquiggleEq.export.
Require Import SquiggleEq.UsefulTypes.
Require Import SquiggleEq.list.
Require Import SquiggleEq.LibTactics.
Require Import SquiggleEq.tactics.
Require Import SquiggleEq.AssociationList.
Require Import ExtLib.Structures.Monads.
Require Import templateCoqMisc.
Require Import Template.Template.
Require Import Template.Ast.

Require Import paramDirect.

Require Import Program.
Open Scope program_scope.


Reserved Notation " A ↪ B " (at level 80).

(* TODO: preproc : unflatten all applications to binary *)
(* similar to PTS.Beta *)
Inductive red : STerm -> STerm -> Prop := 
| beta : forall x A Sa b v,
  (mkApp (mkLamS x A Sa b) [v]) ↪ (apply_bterm (bterm [x] b) [v])
| congruence :
    forall n o lbt1 lbt2,
    n < length (lbt1) (* reduction happens only in the nth bterm *)
    -> length lbt1 = length lbt2
    -> (forall m, m<>n -> selectbt lbt1 m = selectbt lbt2 m)
    -> let b1 := (selectbt lbt1 n) in let b2 := (selectbt lbt1 n) in
       get_vars b1= get_vars b2
    -> (get_nt b1) ↪ (get_nt b2)
    -> (oterm o lbt1) ↪ (oterm o lbt2)
where "M ↪ N" := (red M N).

Require Import Coq.Relations.Relation_Operators.

Definition defEq : STerm -> STerm -> Prop :=
clos_refl_sym_trans _ red.

Infix  "≡" := defEq (at level 80).
 


(* (free_vars (tvmap vprime t)) = map vprime (free_vars t) *)

Let tprime : STerm -> STerm :=  tvmap vprime.
Let btprime : SBTerm -> SBTerm :=  tvmap_bterm vprime.

(* Lemma 2.1 in Lasson.
Unlike in Certicoq, here we are talking about reduction, which
can happen even under binders. So, we don't have the luxury
of only talking about closed terms. So alpha equality is inevitable in later lemmas.
In this lemma, by ensuring that freshVars commutes with vprime, we may be
able to get it with strict equality
*)


Require Import Psatz.

Local Opaque BinNat.N.add .



Lemma vPrimeNeqV : forall v,  v <> vprime v.
Proof.
  intros ? Heq. apply (f_equal fst) in Heq.
  simpl in Heq. lia.
Qed.

Lemma vRelNeqV : forall v,  v <> vrel v.
Proof.
  intros ? Heq. apply (f_equal fst) in Heq.
  simpl in Heq. lia.
Qed.

Lemma vRelNeqVPrime : forall v, vprime v <> vrel v.
Proof.
  intros ? Heq. apply (f_equal fst) in Heq.
  simpl in Heq. lia.
Qed.

Hint Rewrite (fun v => not_eq_beq_var_false _ _ (vPrimeNeqV v)) : Param.
Hint Rewrite (fun v => not_eq_beq_var_false _ _ (vRelNeqVPrime v)) : Param.
Hint Rewrite (fun v => not_eq_beq_var_false _ _ (vRelNeqV v)) : Param.


Require Import NArith.

Definition varClass1 (v:V) : N := proj1_sig (varClass v).

Lemma varClassVPrime : forall v, varClass1 (vprime v) = 
  (1+ varClass1 v) mod 3.
Proof using.
  intros. unfold varClass1. simpl.
  rewrite N.add_mod;[| lia].
  refl.
Qed.  

Lemma varClassVRel : forall v, varClass1 (vrel v) = 
  (2+ varClass1 v) mod 3.
Proof using.
  intros. unfold varClass1. simpl.
  rewrite N.add_mod;[| lia].
  refl.
Qed.  

Hint Rewrite varClassVPrime varClassVRel : Param.

Lemma varClassNotEq : forall v1 v2, 
     (varClass1 v1 <> varClass1 v2) -> beq_var v1 v2 = false.
Proof.
  intros ? ? Heq.
  apply not_eq_beq_var_false.
  congruence.
Qed.

Hint Resolve vRelNeqVPrime vRelNeqV vPrimeNeqV : Param.

Lemma decideFalse P `{Decidable P} : ~P -> decide P = false.
Proof.
apply Decidable_sound_alt.
Qed.

Lemma nameMapAppInj s :
injective_fun (nameMap (fun x : ident => String.append x s)).
(* append is injective *)
Admitted.

Lemma vRelInjective : injective_fun vrel.
Proof using.
  intros v1 v2 Heq.
  destruct v1, v2.
  unfold vrel in *.
  simpl in *.
  inverts Heq.
  f_equal; [lia|].
  unfold nameMap.
  apply nameMapAppInj in H1.
  assumption.
Qed.

Lemma vPrimeInjective : injective_fun vprime.
Proof using.
  intros v1 v2 Heq.
  destruct v1, v2.
  unfold vrel in *.
  simpl in *.
  inverts Heq.
  f_equal; [lia|].
  apply nameMapAppInj in H1.
  assumption.
Qed.


Lemma vRelInjective2 v1 v2 : v1 <> v2 ->
  vrel v1 <> vrel v2.
Proof using.
  intros Heq.
  intros Hc.
  apply vRelInjective in Hc. contradiction.
Qed.
  
Hint Rewrite varClassVPrime: Param.
Hint Rewrite varClassVRel: Param.

Local Transparent BinNat.N.add .

Ltac hideRHS rhs :=
match goal with
  [ |- _ = ?r] => set (rhs:= r)
  end.
  
  Local Opaque vprime.
  Local Opaque vrel.

(* use parametricity? *)
Lemma substAuxPrimeCommute: forall (A B: STerm) (x:V),
(* NO need to assume that vars in a and b and the var x have class 0 *)
tprime (ssubst_aux A [(x,B)]) =
ssubst_aux (tprime A) [(vprime x,tprime B)].
Admitted.

(* use parametricity? *)
Lemma fvarsPrimeCommute t:
free_vars (tprime t) =
map vprime (free_vars t).
Admitted.

Lemma ifThenElseMap {A B:Type} (f: A->B) (b:bool) (t e : A):
  f (if b then t else e) = if b then (f t) else (f e).
Proof using.
  destruct b; auto.
Qed.

(* Move *)
Definition vAllRelated (v: V) : list V :=
  [v; vprime v; vrel v].


Lemma translateFvars (t:STerm) :
subset
  (free_vars (translate true t)) 
  (flat_map vAllRelated (free_vars t)).
Admitted.

(* generalize vAllRelated as a function that returns disjoint lists on different inputs *)
Lemma vAllRelatedFlatDisj lva lvb:
varsOfClass (lva ++ lvb) userVar
-> disjoint lva lvb
-> disjoint (flat_map vAllRelated lva) (flat_map vAllRelated lvb).
Proof using.
  intros Hvc Hd. unfold disjoint.
  setoid_rewrite in_flat_map.
  unfold disjoint in Hd.
  apply  varsOfClassApp in Hvc.
  destruct Hvc as [Hvca Hvcb].
  intros ? H1ex. destruct H1ex as [v1  H1ex].
  destruct H1ex.
  intros H2ex. destruct H2ex as [v2  H2ex].
  destruct H2ex.
  unfold vAllRelated in *.
  repeat (in_reasoning); subst; try contradiction; eauto with Param.
  firstorder.
- apply Hvcb in H1. apply (f_equal (@proj1_sig _ _ )) in H1.
  setoid_rewrite varClassVPrime in H1.
  apply Hvca in H. apply (f_equal (@proj1_sig _ _ )) in H.
  setoid_rewrite H in H1. compute in H1. lia.
- apply Hvcb in H1. apply (f_equal (@proj1_sig _ _ )) in H1.
  setoid_rewrite varClassVRel in H1.
  apply Hvca in H. apply (f_equal (@proj1_sig _ _ )) in H.
  setoid_rewrite H in H1. compute in H1. lia.
- apply Hvcb in H1. apply (f_equal (@proj1_sig _ _ )) in H1.
  apply Hvca in H. apply (f_equal (@proj1_sig _ _ )) in H.
  setoid_rewrite varClassVPrime in H.
  setoid_rewrite H1 in H. compute in H. lia.
- apply vPrimeInjective in H2.  subst. firstorder.
- apply (f_equal varClass1) in H2.
  autorewrite with Param in H2.
  unfold varClass1 in H2.
  setoid_rewrite (Hvca _ H) in H2.
  setoid_rewrite (Hvcb _ H1) in H2.
  compute in H2. lia.
- apply Hvcb in H1. apply (f_equal (@proj1_sig _ _ )) in H1.
  apply Hvca in H. apply (f_equal (@proj1_sig _ _ )) in H.
  setoid_rewrite varClassVRel in H.
  setoid_rewrite H1 in H. compute in H. lia.
- apply (f_equal varClass1) in H2.
  autorewrite with Param in H2.
  unfold varClass1 in H2.
  setoid_rewrite (Hvca _ H) in H2.
  setoid_rewrite (Hvcb _ H1) in H2.
  compute in H2. lia.
- apply vRelInjective in H2.  subst. firstorder.
Qed.
 

Lemma translateFvarsDisj (t:STerm) lv:
varsOfClass (free_vars t  ++ lv) userVar
-> disjoint (free_vars t ) lv
-> disjoint (free_vars (translate true t)) (flat_map vAllRelated lv).
Proof using.
  intros Hvc Hd.
  eapply subset_disjoint;[apply translateFvars|].
  apply vAllRelatedFlatDisj; auto.
Qed.


Lemma translateSubstCommute : forall (A B: STerm) (x:V),
(* A must have been preprocessed with uniq_change_bvars_alpha *)
disjoint (free_vars B ++ free_vars A) (bound_vars A)
-> NoDup (bound_vars A)
-> varsOfClass (x::(all_vars A (* ++ all_vars B*) )) userVar
->
let tr := translate true in
tr (ssubst_aux A [(x,B)])
= (ssubst_aux (tr A) [(x,B); (vprime x, tprime B); (vrel x, tr B)]).
Proof.
  simpl.
  induction A as [| o lbt Hind]  using NTerm_better_ind ; 
    intros B x Hdis Hdup Hvc;[|destruct o]; try refl;
    [ | | | | | | | |].
(* variable *)
- hideRHS rhs.
  simpl.
  rewrite beq_deq.
  cases_if as hd; subst.
  + simpl. unfold rhs. simpl.
    rewrite <- beq_var_refl.
    autorewrite with Param. refl.
  + simpl. unfold rhs. clear rhs.
    unfold all_vars in Hvc. simpl in *.
    unfold varsOfClass, lforall in Hvc.
    simpl in *; dLin_hyp.
    let tac:=
      autorewrite with Param;
      unfold varClass1;
      try setoid_rewrite Hyp; try setoid_rewrite Hyp0;
      compute; congruence in
    do 2 rewrite varClassNotEq by tac.
    rewrite not_eq_beq_var_false; auto;[].
    apply vRelInjective2. assumption.
(* Lambda *)
- destruct lbt as [| b  lbt]; simpl; [refl|].
  (* process each BTerm before going to the next *)
  destruct b as [lv lamTyp].
  destruct lv as [|];[| refl].
  destruct lbt as [| b2  lbt]; [refl |].
  destruct b2 as [b2lv lamBody].
  destruct b2lv as [|lamVar b2lv];[refl|].
  destruct b2lv as [|];[|refl].
  destruct lbt as [|]; [| refl].
  hideRHS rhs. simpl.
  Local Opaque ssubst_bterm_aux.
  unfold rhs. clear rhs. simpl.
  unfold transLam, mkAppBeta. simpl.
  Local Transparent ssubst_bterm_aux.
    set (b:= match argSort with
                     | Some s => isPropOrSet s
                     | None => false
                     end
                     ).

  simpl ssubst_bterm_aux at 1.
  rewrite <- ssubst_aux_sub_filter2  with (l:=[vprime x; vrel x])
  (sub:=[(x, B); (vprime x, tprime B); (vrel x, translate true B)]) by admit.
  Local Opaque ssubst_bterm_aux. simpl.
  repeat rewrite deq_refl.
  repeat rewrite decideFalse by eauto with Param.
  symmetry.
  repeat rewrite decideFalse by eauto with Param.
  f_equal.
  f_equal.
  Local Transparent ssubst_bterm_aux.
  Local Opaque ssubst_aux sub_filter. simpl.
  f_equal.
  f_equal.
  rewrite decide_decideP.
  destruct (decideP (lamVar = x)).
  + clear Hind. (* ssubst gets filtered out. so no Hind needed *)
    subst.
    Local Transparent ssubst_aux sub_filter. simpl.
    repeat rewrite deq_refl.
    repeat rewrite decideFalse by eauto with Param.
    repeat rewrite sub_filter_nil_r. simpl.
    repeat rewrite deq_refl.
    repeat rewrite decideFalse by eauto with Param.
    simpl.
    unfold beq_var.
    repeat rewrite deq_refl.
    repeat rewrite decideFalse by eauto with Param.
    rewrite <- ssubst_aux_sub_filter2  with (l:=[vrel x])
      (sub:=[(vprime x, tprime B); (vrel x, translate true B)]) by admit.
    simpl.
    unfold beq_var.
    repeat rewrite deq_refl.
    repeat rewrite decideFalse by eauto with Param.
    rewrite <- substAuxPrimeCommute.
    repeat rewrite ssubst_aux_nil.
    do 5 f_equal.
    (* because in lhs the var got filtered out, we never substituted 
    so no ssubst_aux around (translate true lamBody).
    So f_equal easily gets it. No Ind Hyp was needed
    *)
    do 2 f_equal.
    unfold mkApp. simpl.
    do 3 f_equal. unfold id. simpl.
    Local Opaque ssubst_aux. simpl in Hdis.
    disjoint_reasoningv2.
    symmetry.
    rewrite ssubst_aux_trivial_disj;[| noRepDis2].
    rewrite ssubst_aux_trivial_disj;[refl|].
    rewrite cons_as_app in Hvc.
    rwsimpl Hvc. repnd.
    assert (disjoint (free_vars (translate true lamTyp)) [vrel x]).
     apply disjoint_sym in Hdis2.
      apply translateFvarsDisj in Hdis2;[| noRepDis2].
      unfold vAllRelated in Hdis2. simpl in Hdis2.
      noRepDis2; fail.
    destruct b; simpl; disjoint_reasoningv2.
    * intros ? Hin.  rewrite in_single_iff.
      intros ?. subst.
      apply Hvc3 in Hin.
      apply (f_equal (@proj1_sig _ _)) in Hin.
      setoid_rewrite varClassVRel in Hin.
      unfold varClass1 in Hin.
      setoid_rewrite (Hvc0 x ltac:(cpx)) in Hin.
      compute in Hin. lia.
    * intros ? Hin. rewrite fvarsPrimeCommute in Hin.
      rewrite in_single_iff.
      intros ?. subst.
      apply in_map_iff in Hin. exrepnd.
      apply (f_equal varClass1) in Hin0.
      autorewrite with Param in Hin0.
      unfold varClass1 in Hin0.
      setoid_rewrite (Hvc0 x ltac:(cpx)) in Hin0.
      setoid_rewrite (Hvc3 a ltac:(cpx)) in Hin0.
      compute in Hin0. lia.
  (* here, substitution for [x] actually happens *)
  +
  (* need to automate varClasses *)
Abort.

