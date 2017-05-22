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

(* Move to templateCoqMisc *)
Definition varCycleLen := 3.

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

Lemma vRelNeqVPrime : forall (v:V), vprime v <> vrel v.
Proof.
  intros ? Heq. apply (f_equal fst) in Heq.
  simpl in Heq. lia.
Qed.

Require Import NArith.

(** Move to templateCoqMisc *)
Definition vBase (v: V) : N :=
  let vn := fst v in
  (vn - (N.modulo vn varCycleLen))%N.

Lemma vBaseId v :
  varClass v = userVar -> vBase v = fst v.
Proof using.
  intros Heq.
  destruct v; simpl in *.
  apply (f_equal (@proj1_sig _ _ )) in Heq. unfold vBase.
  simpl in *. setoid_rewrite Heq. lia.
Qed.  

Lemma vBasePrime v :
  varClass v = userVar -> vBase (vprime v) = fst v.
Proof using.
  intros Heq.
  destruct v; simpl in *.
  apply (f_equal (@proj1_sig _ _ )) in Heq. unfold vBase.
  simpl in *. rewrite N.add_mod by (compute;lia).
  setoid_rewrite Heq. unfold varCycleLen.
  change ((1 mod 3 + 0) mod 3) with 1.
  lia.
Qed.

Lemma vBaseRel v :
  varClass v = userVar -> vBase (vrel v) = fst v.
Proof using.
  intros Heq.
  destruct v; simpl in *.
  apply (f_equal (@proj1_sig _ _ )) in Heq. unfold vBase.
  simpl in *. rewrite N.add_mod by (compute;lia).
  setoid_rewrite Heq. unfold varCycleLen.
  change ((2 mod 3 + 0) mod 3) with 2.
  lia.
Qed.

Hint Rewrite (fun v => not_eq_beq_var_false _ _ (vPrimeNeqV v)) : Param.
Hint Rewrite (fun v => not_eq_beq_var_false _ _ (vRelNeqVPrime v)) : Param.
Hint Rewrite (fun v => not_eq_beq_var_false _ _ (vRelNeqV v)) : Param.


Require Import NArith.

Definition varClass1 (v:V) : N := proj1_sig (varClass v).

Lemma varClassVPrime : forall v, varClass1 (vprime v) = 
  (1+ varClass1 v) mod varCycleLen.
Proof using.
  intros. unfold varClass1. simpl.
  rewrite N.add_mod;[| lia].
  refl.
Qed.  

Lemma varClassVRel : forall v, varClass1 (vrel v) = 
  (2+ varClass1 v) mod varCycleLen.
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
(* append is injective at the first argument *)
Admitted.

(** unconditional, even though we use vrel only userVars *)
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

(** unconditional, even though we use vrel only userVars *)
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

Hint Resolve vPrimeInjective : injective_fun.
Hint Resolve vRelInjective : injective_fun.
Local Transparent BinNat.N.add .

Ltac hideRHS rhs :=
match goal with
  [ |- _ = ?r] => set (rhs:= r)
  end.
  
  Local Opaque vprime.
  Local Opaque vrel.

(* use parametricity? *)
Lemma substAuxPrimeCommute: forall (t: STerm) (sub:Substitution),
(* NO need to assume that vars in a and b and the var x have class 0 *)
tprime (ssubst_aux t sub) =
ssubst_aux (tprime t) (ALMap vprime tprime sub).
Proof using.
  induction t using NTerm_better_ind; intro.
- simpl. unfold sub_find. rewrite ALFindMap by eauto with injective_fun.
  dALFind ss; setoid_rewrite <- Heqss; refl.
- simpl. unfold tprime, tvmap. simpl. f_equal. repeat rewrite map_map.
  apply eq_maps.
  intros b Hin. destruct b.
  specialize (H _ _ Hin). unfold compose. simpl. f_equal.
  unfold sub_filter. rewrite ALEndoMapFilterCommute by eauto with injective_fun.
  apply H.
Qed.  

Corollary substAuxPrimeCommute1 : forall (A B: STerm) (x:V),
 (* NO need to assume that vars in a and b and the var x have class 0 *)
tprime (ssubst_aux A [(x,B)]) =
ssubst_aux (tprime A) [(vprime x,tprime B)].
Proof using.
  intros. rewrite substAuxPrimeCommute. refl.
Qed.

(* delete! *)
Lemma  map_flat_map (A B C : Type) (f : B -> list C) (g : C -> A) (l : list B):
    map g (flat_map f l) = flat_map ((map g) ∘ f) l.
Proof using.
  induction l; auto.
  simpl. rewrite map_app. rewrite IHl. refl.
Qed.

(* can use parametricity instead, once we deal with universe-polymorpic types such as NTerm *)
Lemma fvarsPrimeCommute t:
free_vars (tprime t) =
map vprime (free_vars t).
Proof using.
  induction t using NTerm_better_ind;[refl|].
  simpl. rewrite flat_map_map,  map_flat_map.
  apply eq_flat_maps.
  intros b Hin. destruct b. unfold compose. simpl.
  specialize (H _ _ Hin). setoid_rewrite H.
  unfold remove_nvars.
  erewrite <- map_diff_commute by eauto with injective_fun.
  refl.
Qed.

Lemma ifThenElseMap {A B:Type} (f: A->B) (b:bool) (t e : A):
  f (if b then t else e) = if b then (f t) else (f e).
Proof using.
  destruct b; auto.
Qed.


Lemma translateFvars ienv (t:STerm) :
subset
  (free_vars (translate true ienv t)) 
  (flat_map vAllRelated (free_vars t)).
Proof using.
Admitted. (* very confident about this.*)

(* delete *)
Lemma disjoint_map_if (A B : Type) (f : A -> B) (l1 l2 : list A):
  injective_fun f ->
  disjoint l1 l2 -> disjoint (map f l1) (map f l2).
Proof using.
  intros Hinj. unfold disjoint. unfold injective_fun in Hinj.
  intros Hd ? Hin Hinc.
  apply in_map_iff in Hin. exrepnd. subst.
  apply in_map_iff in Hinc. exrepnd.
  apply Hinj in Hinc0. subst. firstorder.
Qed.


(* generalize vAllRelated as a function that returns disjoint lists on different inputs *)
Lemma vAllRelatedFlatDisjFst lva lvb:
varsOfClass (lva ++ lvb) userVar
-> disjoint (map fst lva) (map fst lvb)
-> disjoint (flat_map vAllRelated lva) (flat_map vAllRelated lvb).
Proof using.
  intros Hvc Hd.
  apply disjoint_map with (f:= vBase).
  apply  varsOfClassApp in Hvc.
  destruct Hvc as [Hvca Hvcb].
  do 2 rewrite map_flat_map.
  unfold vAllRelated, compose. simpl.
  setoid_rewrite flat_map_fapp with (f:= fun x => [vBase x]).
  setoid_rewrite flat_map_fapp with (f:= fun x => [vBase (vprime x)]).
(*  let rec tac l :=
      match l with
        | ?h::?tl => 
        setoid_rewrite eqset_flat_maps at ltac:h;
          [| intros  ? ?;
                     try rewrite vBaseId;
                     try rewrite vBasePrime;
                     try rewrite vBaseRel;
                     [apply eq_set_refl | eauto]]; tac tl
        | _ => idtac "nil"
       end in tac ([1]). *)
  setoid_rewrite eqset_flat_maps at 1.
    Focus 2.
    intros  ? ?. rewrite vBaseId; [apply eq_set_refl | eauto].
  setoid_rewrite eqset_flat_maps at 2.
    Focus 2.
    intros  ? ?. rewrite vBasePrime; [apply eq_set_refl | eauto].
  setoid_rewrite eqset_flat_maps at 3.
    Focus 2.
    intros  ? ?. rewrite vBaseRel; [apply eq_set_refl | eauto].
  setoid_rewrite eqset_flat_maps at 4.
    Focus 2.
    intros  ? ?. rewrite vBaseId; [apply eq_set_refl | eauto].
  setoid_rewrite eqset_flat_maps at 5.
    Focus 2.
    intros  ? ?. rewrite vBasePrime; [apply eq_set_refl | eauto].
  setoid_rewrite eqset_flat_maps at 6.
    Focus 2.
    intros  ? ?. rewrite vBaseRel; [apply eq_set_refl | eauto].
    repeat rewrite flat_map_single.
    disjoint_reasoningv.
Qed.

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

Lemma translateFvarsDisj ienv (t:STerm) lv:
varsOfClass (free_vars t  ++ lv) userVar
-> disjoint (free_vars t ) lv
-> disjoint (free_vars (translate true ienv t)) (flat_map vAllRelated lv).
Proof using.
  intros Hvc Hd.
  eapply subset_disjoint;[apply translateFvars|].
  apply vAllRelatedFlatDisj; auto.
Qed.

(* beta reduction in mkApp was only for efficiency and we dont consider
  that in the proof *)
Lemma mkAppNoBeta : mkAppBeta = mkApp. Admitted.

Local Opaque castIfNeeded mkAppBeta.

(* for this to work, replace mkAppBeta with mkApp in lambda case of translate  *)
Lemma translateSubstCommute ienv : forall (A B: STerm) (x:V),
(* A must have been preprocessed with uniq_change_bvars_alpha *)
disjoint (free_vars B ++ free_vars A) (bound_vars A)
-> NoDup (bound_vars A)
-> varsOfClass (x::(all_vars A (* ++ all_vars B*) )) userVar
->
let tr := translate true ienv in
tr (ssubst_aux A [(x,B)])
= (ssubst_aux (tr A) [(x,B); (vprime x, tprime B); (vrel x, tr B)]).
Proof.
  simpl.
  induction A as [| o lbt Hind]  using NTerm_better_ind ; 
    intros B x Hdis Hdup Hvc;[|destruct o]; try refl;
    [ | | | | | | | | | |].
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
- simpl. destruct lbt as [| b  lbt]; simpl; [refl|].
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
  Local Transparent ssubst_bterm_aux.
  simpl ssubst_bterm_aux at 1.
  unfold all_vars in Hvc.
  rewrite cons_as_app in Hvc.
  rwsimpl Hvc. fold V in lamVar.  repnd.
  pose proof Hvc0 as Hvcxb.
  specialize (Hvc0 x ltac:(cpx)). simpl in Hvc0.
  apply (f_equal (@proj1_sig _ _ )) in Hvc0. simpl in Hvc0.
  (* regardless of whether lamVar==x, substitution may happen in the lamTyp. So,
    we take care of it (the outermoset 2 lams) before making cases on that*)
  rewrite <- ssubst_aux_sub_filter2
  with
    (l:=[vprime x; vrel x])
      (sub:=[(x, B); (vprime x, tprime B); (vrel x, translate true ienv B)]).
  Focus 2.
   noRepDis2; apply Hvc3 in H; apply (f_equal (@proj1_sig _ _ )) in H;
      try setoid_rewrite varClassVRel in H;
      try setoid_rewrite varClassVPrime in H;
      simpl in H; setoid_rewrite Hvc0 in H;
      invertsn H.
  Local Opaque  ssubst_bterm_aux. simpl.
  do 2 rewrite deq_refl. symmetry.
  do 3 rewrite decideFalse by eauto with Param.
  simpl in *. repeat rewrite app_nil_r in *.
  do 2 progress f_equal.
  Local Transparent ssubst_bterm_aux.
  Local Opaque ssubst_aux sub_filter.
  simpl.
  do 2 progress f_equal. simpl.
  Local Transparent ssubst_aux.
  simpl ssubst_aux at 1. rewrite sub_filter_nil_r.
  rewrite <- ssubst_aux_sub_filter2
  with
    (l:=[x; vrel x])
      (sub:= (sub_filter [(x, B); (vprime x, tprime B); (vrel x, translate true ienv B)] [lamVar])).
  Focus 2.
    rewrite fvarsPrimeCommute.
    noRepDis2; apply in_map_iff in H;
      exrepnd; apply Hvc3 in H1; apply (f_equal (@proj1_sig _ _ )) in H1;
        apply (f_equal varClass1) in H0;
        autorewrite with Param in H0;
        setoid_rewrite H1 in H0;
        setoid_rewrite Hvc0 in H0; inverts H0.
  rewrite sub_filter_swap.
  rewrite sub_filter_nil_r.
  Local Transparent sub_filter. simpl sub_filter at 1.
  Local Opaque sub_filter.
  do 2 rewrite deq_refl. symmetry.
  symmetry. do 3 rewrite decideFalse by eauto with Param.
  rewrite cons_as_app in Hvc. rwsimpl Hvc. repnd.
  pose proof Hvc4 as Hvclb.
  specialize (Hvc4 lamVar ltac:(cpx)). simpl in Hvc4.
  apply (f_equal (@proj1_sig _ _ )) in Hvc4. simpl in Hvc4.
  rewrite sub_filter_disjoint1.
  Focus 2. simpl.
    (apply disjoint_neq_iff; simpl; intros Hc; apply (f_equal varClass1) in Hc;
    autorewrite with Param in Hc;
    setoid_rewrite Hvc0 in Hc;
    setoid_rewrite Hvc4 in Hc; inverts Hc).
  rewrite <- substAuxPrimeCommute1. 
  do 5 progress f_equal.
  (* the type of the (vrel lamVar) and the body lamBody remain.
     the type of lamVar and (tprime lamVar) are already taken care of *)
  simpl.
  rewrite decide_decideP.
  match goal with
    [ |-  context [@decideP ?p ?d] ] => destruct (@decideP p d)
  end.
  + clear Hind. (* ssubst gets filtered out. so no Hind needed *)
    subst. Local Transparent sub_filter. simpl.
    do 1 rewrite deq_refl. 
    do 2 rewrite decideFalse by eauto with Param. simpl.
    do 1 rewrite deq_refl.
    do 1 rewrite decideFalse by eauto with Param. 
    simpl.
    do 1 rewrite deq_refl.
    
    (* get the first BTerm (lamTyp) to match up *)
    do 2 rewrite ssubst_aux_nil.
    do 4 f_equal. symmetry.
    rewrite ssubst_aux_trivial_disj;[| simpl; noRepDis2].
    rewrite ssubst_aux_trivial_disj;[refl|].
    rewrite mkAppNoBeta. simpl.
    disjoint_reasoningv;
      [| in_reasoning; sp; revert H; fold not; eauto with Param;
      try apply vRelNeqVPrime;
      try apply vRelNeqV].
    Local Transparent castIfNeeded.
    unfold castIfNeeded, projTyRel in H.
    assert (disjoint (free_vars (translate true ienv lamTyp)) [vrel x]).
      apply disjoint_singleton_l in Hdis2.
      apply disjoint_sym in Hdis2. 
      apply translateFvarsDisj with (ienv:=ienv) in Hdis2;
        [unfold vAllRelated in Hdis2; simpl in Hdis2; noRepDis2 |].
      rwsimplC. dands; auto; fail.
    revert H.
    case_if; intros ?; unfold id in *; simpl in H1;
      repeat rewrite in_app_iff  in H1; sp; revert H1; apply disjoint_singleton_l;
        apply disjoint_sym; auto; clear H H0.
    * noRepDis2. apply Hvc3 in H; apply (f_equal (@proj1_sig _ _ )) in H;
      setoid_rewrite varClassVRel in H;
      simpl in H; setoid_rewrite Hvc0 in H;
      invertsn H. (* copied from above *)
    * noRepDis2. rewrite fvarsPrimeCommute in H. apply in_map_iff in H.
      exrepnd. apply Hvc3 in H1;  apply (f_equal (@proj1_sig _ _ )) in H1;
        apply (f_equal varClass1) in H0;
        autorewrite with Param in H0.
        setoid_rewrite H1 in H0.
        setoid_rewrite Hvc0 in H0; inverts H0.
  (* here, substitution for [x] actually happens *)
  + pose proof n as Hd. apply disjoint_neq_iff in Hd.
    apply vAllRelatedFlatDisj in Hd;[| rwsimplC; tauto].
    simpl in Hd.
    rewrite sub_filter_disjoint1 with (lf := [lamVar]) (* start from innermost filter *)
      by (simpl; disjoint_reasoningv2).
    rewrite sub_filter_disjoint1 with (lf := [vprime lamVar]) (* start from innermost filter *)
      by (simpl; disjoint_reasoningv2).
    rewrite sub_filter_disjoint1 with (lf := [vrel lamVar]) (* start from innermost filter *)
      by (simpl; disjoint_reasoningv2).
    rewrite cons_as_app in Hdis, Hdup.
    disjoint_reasoningv2.
    setoid_rewrite (disjoint_remove_nvars_l  [lamVar]) in Hdis.
    rewrite <- Hind with (lv := [lamVar]); auto; try disjoint_reasoningv2.
    SearchAbout NoDup app.
    SearchAbout remove_nvars disjoint.
    SearchAbout sub_filter eq disjoint.
    
    (* need to automate varClasses *)
- (* Pi case will have the real new difference. Also, in the lambda case, 
    we have the castIfNeeded *)
Abort.
*)
Lemma translateRedCommute : forall (A B: STerm),
(* preconditions *)
A ↪ B
-> (translate true [] A) ↪ (translate true [] B).
Abort.

Lemma translateDefnEqCommute : forall (A B: STerm),
(* preconditions *)
A ≡ B
-> (translate true []A) ≡ (translate true [] B).
Abort.

(* define the typing relation. primitive rules for the terms denoting SigT and SigT_rect,
eq and eq_rect2 (dependent version) 
Also define subtyping? subtyping comes before typing?
*)

(* pick out a core language that excludes inductives – only covers Lasson;s 
first translation *)
Inductive inSrcLanuage : STerm -> Prop :=.

(* abstraction theorem for the translation of terms satisfying inSrcLanuage.
The desination uses full typing rules.
https://onedrive.live.com/edit.aspx/Documents/Postdoc?cid=946e75b47b19a3b5&id=documents&wd=target%28parametricity%2Fpapers%2Flogic%2Fproof.one%7C4AAB4EEB-90BF-4FC7-BBB1-7C61980BE1EB%2F%29
onenote:https://d.docs.live.net/946e75b47b19a3b5/Documents/Postdoc/parametricity/papers/logic/proof.one#section-id={4AAB4EEB-90BF-4FC7-BBB1-7C61980BE1EB}&end
*)
