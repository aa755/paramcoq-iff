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

(* Reserved Notation " A ↪ B " (at level 80). *)

Lemma NoDupSinleton {A:Type} (a:A): NoDup [a].
Proof using.
  repeat constructor.
  simpl. tauto.
Qed.  
(* Move to templateCoqMisc. change it to 5 or more *)
Definition varCycleLen := 3.

(* TODO: preproc : unflatten all applications to binary *)
(* similar to PTS.Beta. need to take one step *)
Inductive red (substf: list V -> STerm -> Substitution -> STerm):
  ((*outerBVars*)list V) -> STerm -> STerm -> Prop := 
| beta : forall outerBvars x A Sa b arg,
  red substf outerBvars (mkApp (mkLamS x A Sa b) [arg])  (substf outerBvars b [(x,arg)])
| congruence :
    forall outerBvars n o lbt1 lbt2,
    n < length (lbt1) (* reduction happens only in the nth bterm *)
    -> length lbt1 = length lbt2
    -> (forall m, m<>n -> selectbt lbt1 m = selectbt lbt2 m)
    -> let b1 := (selectbt lbt1 n) in let b2 := (selectbt lbt2 n) in
       get_vars b1= get_vars b2
    -> red substf (get_vars b1 ++ outerBvars) (get_nt b1) (get_nt b2)
    -> red substf outerBvars (oterm o lbt1)  (oterm o lbt2).
(* clause for alpha equality? *)
Require Import Coq.Relations.Relation_Operators.

Definition redS := red bcSubst. 
(** for the correctness of translate on [tl] and [tr], we need to assume that
 [outerBvars] includes the free vars of [tl] and [tr]. No such assumption is needed here *)
Lemma redPreservesBC: forall (outerBvars:list V) (tl tr : STerm),
    redS outerBvars tl tr -> checkBC outerBvars tl = true -> checkBC outerBvars tr = true.
Proof using.
  intros ? ? ? Hred.
  induction Hred.
Local Opaque decide.
- simpl.
  rewrite decide_true by (try constructor).
  rewrite decide_true by disjoint_reasoning.
  rewrite decide_true by (try apply NoDupSinleton).
  intros Hr. fold V in x.
  ring_simplify in Hr.
  repeat rewrite andb_true in Hr.
  repeat rewrite Decidable_spec in Hr.
  repnd. apply bcSubstBetaPreservesBC with (o:=CApply 1).
  simpl.
  setoid_rewrite decide_true;
    try apply NoDupSinleton; try constructor; try disjoint_reasoningv2.
  ring_simplify. repeat rewrite andb_true.
  tauto.
- simpl. do 2 rewrite ball_map_true.
  intros Hl ? Hin. pose proof Hin as Hsel.
  apply in_selectbt in Hsel. exrepnd. subst.
  rename n0 into m.
  destruct (decideP (m=n));
    [subst | rewrite <- H1 by assumption; apply Hl; apply selectbt_in; congruence].
  pose proof Hsel1 as Hsel2.
  rewrite <- H0 in Hsel2.
  eapply selectbt_in in Hsel2.
  specialize (Hl  _ Hsel2).
  destruct (selectbt lbt1 n) as [lv1 tl]. 
  destruct (selectbt lbt2 n) as [lv tr].  simpl in *. subst.
  repeat rewrite andb_true in *. repnd. dands; auto.
Qed.

Definition defEqS   (outerBVars:list V) :   STerm -> STerm -> Prop :=
clos_refl_sym_trans _ (redS outerBVars).

(* Infix  "≡" := defEq (at level 80). *)
 


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
(** append is injective at the first argument *)
Admitted. (** very confident about this *)

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
Admitted. (** confident about this. note that it is unconditional, and it says [subset] not [eq_set]*)


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


Fixpoint mkAppUnFlattened (f: STerm) (args: list STerm) : STerm :=
  match args with
  | [] => f
  | h::tl => mkAppUnFlattened (mkAppNoCheck f [h]) tl
  end.

(* beta reduction in mkApp was only for efficiency and we dont consider
  that in the proof *)
Lemma mkAppNoBeta : mkAppBeta = mkAppNoCheck. Admitted.

Local Opaque castIfNeeded mkAppBeta.

(* this comes up again and again *)
Lemma vDisjointUserVar (la lb: list V) :
  varsOfClass la userVar
  -> varsOfClass lb userVar
  -> disjoint la (map vprime lb ++ map vrel lb).
Proof using.
  intros Ha Hb.
  disjoint_reasoning; intros ? Hin Hc; apply in_map_iff in Hc; exrepnd;
    try apply Ha in Hin; try apply Hb in Hin; subst;
      try apply Ha in Hc1; try apply Hb in Hc1;
        apply (f_equal (@proj1_sig _ _ )) in Hc1;
        apply (f_equal (@proj1_sig _ _ )) in Hin;
        try setoid_rewrite varClassVPrime in Hin;
        try setoid_rewrite varClassVRel in Hin;
        rewrite N.add_mod in Hin by (unfold varCycleLen; lia);
        setoid_rewrite Hc1 in Hin; inverts Hin.
Qed.  
  
Lemma vDisjointPrimeUserVar (la lb: list V) :
  varsOfClass la userVar
  -> varsOfClass lb userVar
  -> disjoint (map vprime la) (lb ++ map vrel lb).
Proof using.
  intros Ha Hb.
  pose proof (vDisjointUserVar _ _ Hb Ha).
  repeat disjoint_reasoning2.
  clear H H0.
  intros ? Hin Hinc.
  apply in_map_iff in Hin.
  apply in_map_iff in Hinc.
  exrepnd. subst.
  apply (f_equal varClass1) in Hinc0.
  apply Ha in Hin1.
  apply Hb in Hinc1.
  apply (f_equal (@proj1_sig _ _ )) in Hinc1.
  apply (f_equal (@proj1_sig _ _ )) in Hin1.
  rewrite varClassVPrime in Hinc0.
  rewrite varClassVRel in Hinc0.
  setoid_rewrite Hin1 in Hinc0.
  setoid_rewrite Hinc1 in Hinc0.
  invertsn Hinc0.
Qed.

Lemma vDisjointTPrimeUserVar (t:STerm) (lb: list V) :
  varsOfClass (free_vars t) userVar
  -> varsOfClass lb userVar
  -> disjoint (free_vars (tprime t)) (lb ++ map vrel lb).
Proof using.
  rewrite fvarsPrimeCommute.
  apply vDisjointPrimeUserVar.
Qed.

Lemma ssubst_trim (t:STerm) x b1 b2 b3:
  varsOfClass (free_vars t) userVar        
  -> varsOfClass [x] userVar        
  -> ssubst_aux t [(x, b1); (vprime x, b2); (vrel x, b3)] = ssubst_aux t [(x, b1)].
Proof using.
  intros H1v H2v.
  rewrite <- ssubst_aux_sub_filter2 with (l:= [vprime x; vrel x]);
    [| apply vDisjointUserVar with (lb:=[x]); assumption].
  simpl.
  do 2 rewrite deq_refl.
  do 3 rewrite decideFalse by eauto with Param.
  refl.
Qed.

Lemma ssubst_trim_prime (t:STerm) x b1 b2 b3:
varsOfClass (free_vars t) userVar        
-> varsOfClass [x] userVar        
-> ssubst_aux (tprime t) [(x, b1); (vprime x, b2); (vrel x, b3)] =
ssubst_aux (tprime t) [(vprime x, b2)].
Proof using.
  intros H1v H2v.
  rewrite <- ssubst_aux_sub_filter2 with (l:= [x; vrel x]);
    [|rewrite fvarsPrimeCommute;  apply vDisjointPrimeUserVar with (lb:=[x]); assumption].
  simpl.
  do 2 rewrite deq_refl.
  do 3 rewrite decideFalse by eauto with Param. refl.
Qed.

Require Import Morphisms.

(* Move to SquiggleEq *)
Global Instance  properEqsetCons {A : Type}:
  Proper (eq ==> eq_set ==> eq_set) (@cons A).
Proof using.
  intros ? ? ? ? ? ?. subst.
  unfold eq_set, subset in *. simpl in *.
  firstorder.
Qed.

(* Move to SquiggleEq *)
Definition singleton {A:Type} (a:A) : list A := [a].

(* Move to SquiggleEq *)
Lemma varsOfClassConsIff {NVar VClass : Type} {H0 : VarClass NVar VClass}:
    forall v1 ( lv2 : list NVar) (vc : VClass),
    varsOfClass (v1:: lv2) vc <-> varsOfClass (singleton v1) vc /\ varsOfClass lv2 vc.
Proof using.
  intros. rewrite <- varsOfClassApp. refl.
Qed.  

(* Move to SquiggleEq *)
Lemma noDupConsIff {A : Type}:
  forall a (lb : list A), NoDup (a::lb) <-> NoDup (singleton a) /\ NoDup lb /\ disjoint [a] lb.
Proof using.
  intros. rewrite <- noDupApp. refl.
Qed.

(* Move to SquiggleEq *)
Hint Rewrite @noDupApp @all_vars_ot @allvars_bterm @varsOfClassConsIff @noDupConsIff: SquiggleEq.

(*
Ltac procVc Hvc :=
  simpl in Hvc;
  rewrite all_vars_ot in Hvc;
  simpl in Hvc;
  do 2 rewrite allvars_bterm in Hvc;
  rewrite app_nil_l in Hvc;
  unfold all_vars in Hvc;
  autorewrite with list in Hvc;
  rewrite cons_as_app in Hvc;
  rwsimpl Hvc.
 *)


Ltac destructDecideP :=
  match goal with
    [ |-  context [@decideP ?p ?d] ] => destruct (@decideP p d)
  end.
(*
(* for this to work, replace mkAppBeta with mkApp in lambda case of translate  *)
Lemma translateSubstCommute ienv : forall (A B: STerm) (x:V),
    (* A must have been preprocessed with change_bvars_alpha *)
disjoint (bound_vars B) (bound_vars A) (* A will be alpha renamed before substitution to ensure this *)
-> checkBC (free_vars B ++ (remove_nvars [x]  (free_vars A))) B = true 
-> checkBC (free_vars A ++ free_vars B) A = true 
-> varsOfClass (x::(all_vars A (* ++ all_vars B*) )) userVar
->
let tr := translate true ienv in
tr (ssubst_aux A [(x,B)])
= (ssubst_aux (tr A) [(x,B); (vprime x, tprime B); (vrel x, tr B)]).
Proof.
  simpl.
  induction A as [| o lbt Hind]  using NTerm_better_ind ; 
    intros B x Hdis H1bc H2bc Hvc;[|destruct o]; try refl;
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

- (* Lambda *)
  Local Opaque transLam.
  simpl. destruct lbt as [| b  lbt]; simpl; [refl|].
  let tac := try reflexivity in destructbtdeep2 b tac.
  rename bnt into lamTyp.
  (* process each BTerm before going to the next *)
  destruct lbt as [| b2  lbt]; [refl |].
  let tac := try reflexivity in destructbtdeep2 b2 tac.
  rename b2lv1 into lamVar.
  rename b2nt into lamBody.
  Local Opaque sub_filter.
  destruct lbt; [ |refl].
  Local Opaque decide.
  simpl in *.
  repeat rewrite app_nil_r in H1bc.
  repeat rewrite app_nil_r in H2bc.
  rewrite decide_true in H2bc;[| disjoint_reasoningv].
  ring_simplify in H2bc.
  fold V in lamVar.
  repeat rewrite andb_true in H2bc. repnd.
  rewrite Decidable_spec in H2bc.
  rwsimpl Hdis. rwsimpl Hdup. rwsimpl Hvc.
  fold V in lamVar.  repnd.  
  clear Hvc4 Hvc2. unfold singleton in *.
  rewrite sub_filter_nil_r.
Abort.
 *)

Lemma checkBCLamAux (lamVar x:V) (lamBody lamTyp B: STerm ): 
  disjoint (bound_vars B) [lamVar]
  -> (checkBC (free_vars B ++ remove x (free_vars lamTyp ++ remove lamVar (free_vars lamBody))) B =
         true)
  -> (checkBC (free_vars B ++ remove x (free_vars lamBody)) B = true).
Proof using.
   intros Hdis H2nd.
   apply (fst (checkBCStrengthen [lamVar])) in H2nd;[| assumption].
      revert H2nd. apply (fst checkBCSubset).
      rewrite remove_app.
      setoid_rewrite eqset_app_comm at 4.
      do 2 rewrite app_assoc.
      apply subset_app_r.
      setoid_rewrite eqset_app_comm at 3.
      do 1 rewrite <- app_assoc.
      apply subsetvAppLR;[eauto|].
      rewrite remove_comm. apply removeConsCancel.
Qed.

(* used in the lambda case and the pi case *)
Lemma transLamSubstCommute:
forall (ienv : indEnv) (argSort : option sort) (lamTyp : STerm) (lamVar : V) (lamBody : STerm),
  (
forall (nt : STerm) (lv : list (N * name)),
         bterm [] lamTyp = bterm lv nt \/ bterm [lamVar] lamBody = bterm lv nt \/ False ->
         forall (B : STerm) (x : V),
         disjoint (bound_vars B) (bound_vars nt) ->
         checkBC (free_vars B ++ remove x (free_vars nt)) B = true ->
         checkBC (free_vars nt ++ free_vars B) nt = true ->
         varsOfClass (x :: all_vars nt) userVar ->
         translate true ienv (ssubst_aux nt [(x, B)]) =
         ssubst_aux (translate true ienv nt)
           [(x, B); (vprime x, tprime B); (vrel x, translate true ienv B)] )
  ->
  forall (B : STerm) (x : V),
  disjoint (bound_vars B) (bound_vars lamTyp ++ lamVar :: bound_vars lamBody) ->
  checkBC ((free_vars lamTyp ++ remove lamVar (free_vars lamBody)) ++ free_vars B) lamTyp =
          true ->
  checkBC (lamVar :: (free_vars lamTyp ++ remove lamVar (free_vars lamBody)) ++ free_vars B)
            lamBody = true ->
checkBC (free_vars B ++ remove x (free_vars lamTyp ++ remove lamVar (free_vars lamBody))) B =
true ->
  disjoint [lamVar] ((free_vars lamTyp ++ remove lamVar (free_vars lamBody)) ++ free_vars B) ->
  varsOfClass [x] userVar ->
  varsOfClass (all_vars lamTyp) userVar ->
  varsOfClass [lamVar] userVar ->
  varsOfClass (all_vars lamBody) userVar ->
  transLam true (translate true ienv) (lamVar, (ssubst_aux lamTyp [(x, B)], argSort))
    (translate true ienv (ssubst_aux lamBody (sub_filter [(x, B)] [lamVar]))) =
  ssubst_aux
    (transLam true (translate true ienv) (lamVar, (lamTyp, argSort)) (translate true ienv lamBody))
    [(x, B ); (vprime x, tprime B); (vrel x, translate true ienv B)].
Proof using.
  intros ? ? ? ? ? Hind ? ? H2d H1nd H3nd H2nd H1d H1vc H2vc H3vc H4vc.
  hideRHS rhs. simpl.
  Local Opaque ssubst_bterm_aux.
  unfold rhs. clear rhs. simpl.
  Local Transparent ssubst_bterm_aux.
  simpl ssubst_bterm_aux at 1.
  unfold all_vars in *. rwsimpl H2vc. rwsimpl H4vc.
  rwsimpl Hvc.
  rewrite ssubst_trim by tauto.
  Local Opaque  ssubst_bterm_aux.
  symmetry.
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
      (sub:= (sub_filter [(x, B); (vprime x, tprime B); (vrel x, translate true ienv B)] [lamVar]));
     [ |apply vDisjointTPrimeUserVar with (lb := [x]); tauto].
  rewrite sub_filter_swap.
  rewrite sub_filter_nil_r.
  Local Transparent sub_filter. simpl sub_filter at 1.
  Local Opaque sub_filter.
  do 2 rewrite deq_refl. symmetry.
  symmetry. do 3 rewrite decideFalse by eauto with Param.
  rename H3vc into Hvclv.
  rename H1vc into Hvcxb.
  pose proof (vDisjointPrimeUserVar _ _ Hvcxb Hvclv) as Hdiss.
  rewrite disjoint_app_r in Hdiss. apply proj1 in Hdiss.
  rewrite sub_filter_disjoint1 by assumption.
  clear Hdiss.
  rewrite <- substAuxPrimeCommute1. 
  do 5 progress f_equal.
  (* the type of the (vrel lamVar) and the body lamBody remain.
     the type of lamVar and (tprime lamTyp) are already taken care of *)
  simpl.
  rewrite decide_decideP.
  destructDecideP.
  + clear Hind. (* ssubst gets filtered out. so no Hind needed *)
    subst. Local Transparent sub_filter. simpl.
    do 1 rewrite deq_refl. 
    do 2 rewrite decideFalse by eauto with Param. simpl.
    do 1 rewrite deq_refl.
    do 1 rewrite decideFalse by eauto with Param. 
    simpl.
    do 1 rewrite deq_refl.
    
    (* get the second BTerm [translate lamBody] to match up *)
    do 2 rewrite ssubst_aux_nil.

    do 4 f_equal. symmetry.
    
    (* now we only have [translate lamTyp] to worry about.
       In the RHS subst (after translate), we have a subst of length 1 (only for [vrel x]):
       the first 2 items have been filtered out.
       In the translation, [translate lamTyp] is in the scope of the binders
       [x:lamType] and [(vprime x):tprime lamType]. So those get filtered out in the RHS
       substitution. That's why no shadowing.

       We don't (can't) use the induction hypothesis.
       Indeed, it was filtered out in the first step after +.

       In the next branch (+), we will have a substitution of length 3 and use the induction
       hypothesis.*)
    rewrite ssubst_aux_trivial_disj;[| simpl; noRepDis2].
    rewrite ssubst_aux_trivial_disj;[refl|].
    rewrite mkAppNoBeta. simpl.
    disjoint_reasoningv2; try apply disjoint_neq_iff;
      try apply vRelNeqVPrime;
      try apply vRelNeqV.
    Local Transparent castIfNeeded.
    unfold castIfNeeded, projTyRel. rename H1d1 into H1d2.
    assert (disjoint (free_vars (translate true ienv lamTyp)) [vrel x]).
      apply disjoint_sym in H1d2.
      apply translateFvarsDisj with (ienv:=ienv) in H1d2;
        [unfold vAllRelated in H1d2; simpl in H1d2; noRepDis2 |].
      rwsimplC. dands; eauto with SquiggleEq.
    case_if; rwsimplC; unfold id in *; auto.
    disjoint_reasoningv2; auto.
    * pose proof (vDisjointUserVar _ _ H2vc0 Hvcxb).
      simpl in *. disjoint_reasoningv2.
    * pose proof (vDisjointTPrimeUserVar _ _ H2vc0 Hvcxb).
      simpl in *. disjoint_reasoningv2.

  +   (* here, substitution for [x] actually happens *)
    pose proof n as Hd. apply disjoint_neq_iff in Hd.
    apply vAllRelatedFlatDisj in Hd; [| rwsimplC; eauto with SquiggleEq; fail].
    simpl in Hd. 
    rewrite sub_filter_disjoint1 with (lf := [lamVar]) (* start from innermost filter *)
      by (simpl; disjoint_reasoningv2).
    rewrite sub_filter_disjoint1 with (lf := [vprime lamVar]) (* start from innermost filter *)
      by (simpl; disjoint_reasoningv2).
    rewrite sub_filter_disjoint1 with (lf := [vrel lamVar]) (* start from innermost filter *)
      by (simpl; disjoint_reasoningv2).
    assert (checkBC (free_vars B ++ remove x (free_vars lamTyp)) B = true).
      revert H2nd. apply (fst checkBCSubset).
      rewrite remove_app. rewrite app_assoc. apply subset_app_r. eauto; fail.
    assert (checkBC (free_vars B ++ remove x (free_vars lamBody)) B = true).
      revert H2nd. apply checkBCLamAux. disjoint_reasoningv2.
    assert (checkBC (free_vars lamBody ++ free_vars B) lamBody = true).
      revert H3nd. apply (fst checkBCSubset).
      rewrite cons_as_app. rewrite app_assoc.
      apply subsetvAppLR;[| reflexivity].
      rewrite eqset_app_comm.
      rewrite <- app_assoc.
      apply subset_app_l.
      rewrite eqset_app_comm.
      apply removeConsCancel.
    assert (checkBC (free_vars lamTyp ++ free_vars B) lamTyp = true).
      revert H1nd. apply (fst checkBCSubset).
      apply subsetvAppLR;[| reflexivity].
      apply subset_app_r. reflexivity.
         
    disjoint_reasoningv2.
(*    setoid_rewrite (disjoint_remove_nvars_l  [lamVar]) in H1d5.
    setoid_rewrite remove_nvars_nop  in H1d5;[| disjoint_reasoningv2]. *)
    rewrite <- Hind with (lv := [lamVar]); auto; try disjoint_reasoningv2;
      [ |  rwsimplC; dands; eauto with SquiggleEq].
    do 2 progress f_equal.
    symmetry.

    (* Unlike the previous bullet (+), here we need to use the induction hypothesis
       for [translate lamTyp]. See the last comment in the above bullet. 
       Unlike the subgoal there, here the substitution in RHS has length 3.
     *)
    rewrite mkAppNoBeta. simpl. unfold mkAppNoCheck. simpl.
    do 6 (rewrite not_eq_beq_var_false; [ | noRepDis2]). 
    do 3 (progress f_equal).
    Ltac tac Hind := (apply Hind with (lv:=[]); auto;
        try (disjoint_reasoningv2); try (rewrite cons_as_app; rwsimplC; eauto with SquiggleEq)).
    Ltac tacOld Hind := (apply Hind with (lv:=[]); auto;
                         [disjoint_reasoningv2| rewrite cons_as_app; rwsimplC; eauto with SquiggleEq]).
    cases_if;
      [
        simpl; unfold projTyRel, mkConstApp, mkApp, mkAppNoCheck;
        simpl; do 4 (progress f_equal);
        [  | f_equal | do 2 progress f_equal; tac Hind]
      | unfold id; tac Hind
      ];
    symmetry;[ apply ssubst_trim| rewrite ssubst_trim_prime]; auto.
    rewrite substAuxPrimeCommute1. refl.
Qed.

Ltac revertAll :=
  repeat match goal with
   | [H:_ |- _] => revert H
   end.
Ltac eqList :=
    repeat match goal with
             [|- cons _ _ = cons _ _] => f_equal
                                         end.

(**
Note that in the LHS, [translate] is called on [(ssubst_aux A [(x,B)])], which
may have duplicate bound variables, even though [A] has unique bound variables.
Consider [A:= x x] and [B:= \y.y].

In the paper, we said that [translate] assumes that the input has unique boundvars.
That would make the LHS illegitimate.
We do need some condition: see examples/capture.v where a form of repeated boundvars
causes capture.
Perhaps we need a weaker condition: Barendredgt convention seems to suffice for this proof.
Why not make the weakest condition that suffices?

Then, if we prove that [translate] preserves alpha equality for terms only containing
uservars and in barendredgt convention, we'll be done.
beta does not preserve BC. so the subst function used in red will
need to take [B], which is already in BC and rename
it ti [B'] such that its bvars to be disjoint from [all_vars A]. [B'] is also in BC.
(this is kinda what would happen if we did the substitution A[B/x] in DB world and converted back to named)
in LHS, we will have [B']. In RHS, we will have something alpha equal to [translate B]
such that its bvars are disjoint from [all_vars (translate A)].
But, [translate B] is alpha equal to [translate B']. after rewriting, we can invoke this lemma

(We could instead precompose [translate] with a function to make boundvars [NoDup].
But then we would have to reason about alpha equality in the proof below. 
[translate] does not unconditionally
respect alpha equality, as examples/capture.v shows. so we cannot "rewrite" after the proof)

When proving preservation of reduction, we will get in trouble because [NoDup].
*)

(* for this to work, replace mkAppBeta with mkApp in lambda case of translate  *)
Lemma translateSubstCommute ienv : forall (A B: STerm) (x:V),
    (* A must have been preprocessed with change_bvars_alpha *)
disjoint (bound_vars B) (bound_vars A) (* A will be alpha renamed before substitution to ensure this *)
-> checkBC (free_vars B ++ (remove_nvars [x]  (free_vars A))) B = true 
-> checkBC (free_vars A ++ free_vars B) A = true 
-> varsOfClass (x::(all_vars A (* ++ all_vars B*) )) userVar
->
let tr := translate true ienv in
tr (ssubst_aux A [(x,B)])
= (ssubst_aux (tr A) [(x,B); (vprime x, tprime B); (vrel x, tr B)]).
(* currently, nothing prevents the translation of A from picking bvars that free in B. tr A
 only looks at A and is free to pick anything that is not free on parts of A that it looks at.
 unless we have all free vars of B free in all subterms of A (impossible), there can be
a problem if we allow the translation to keep picking arbitrary bound vars. All the bvars
in the translation
must be obtained by a function of the input. Then we may also be able to obtain many free
theorems by parametricity. Seems we need 5 class. Or use a combinator for Pi. But then we need
to tackle universe issues *)
Proof.
  simpl.
  induction A as [| o lbt Hind]  using NTerm_better_ind ; 
    intros B x Hdis H1bc H2bc Hvc;[|destruct o]; try refl;
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

- (* Lambda *)
  Local Opaque transLam.
  simpl. destruct lbt as [| b  lbt]; simpl; [refl|].
  let tac := try reflexivity in destructbtdeep2 b tac.
  rename bnt into lamTyp.
  (* process each BTerm before going to the next *)
  destruct lbt as [| b2  lbt]; [refl |].
  let tac := try reflexivity in destructbtdeep2 b2 tac.
  rename b2lv1 into lamVar.
  rename b2nt into lamBody.
  Local Opaque sub_filter.
  destruct lbt; [ |refl].
  Local Opaque decide.
  simpl in *.
  repeat rewrite app_nil_r in H1bc.
  repeat rewrite app_nil_r in H2bc.
  rewrite decide_true in H2bc;[| disjoint_reasoningv].
  ring_simplify in H2bc.
  fold V in lamVar.
  repeat rewrite andb_true in H2bc. repnd.
  rewrite Decidable_spec in H2bc.
  rwsimpl Hdis. rwsimpl Hdup. rwsimpl Hvc.
  fold V in lamVar.  repnd.  
  clear Hvc4 Hvc2. unfold singleton in *.
  rewrite sub_filter_nil_r.
  eapply transLamSubstCommute; eauto.
- (* Pi *)
  Local Opaque transLam.
  simpl. destruct lbt as [| b  lbt]; simpl; [refl|].
  let tac := try reflexivity in destructbtdeep2 b tac.
  rename bnt into piVarType.
  (* process each BTerm before going to the next *)
  destruct lbt as [| b2  lbt]; [refl |].
  let tac := try reflexivity in destructbtdeep2 b2 tac.
  rename b2lv1 into piVar.
  rename b2nt into piRangeType.
  simpl in *.
  destruct lbt; [ |refl].
  rwsimpl Hdis. rwsimpl Hdup. rwsimpl Hvc.
  unfold all_vars in Hvc. rwsimpl Hvc.
  fold V in piVar.  repnd.
  repnd.
  repeat match goal with
  [H: varsOfClass [] _ |- _ ] => clear H
  end.        
  unfold singleton in *.
  repeat rewrite sub_filter_nil_r.
  
  (* so far, same as that of the lambda case, except for different naming *)
  unfold mkPiRNew.
  simpl in *.
  repeat rewrite app_nil_r in H1bc.
  repeat rewrite app_nil_r in H2bc.
  rewrite decide_true in H2bc;[| disjoint_reasoningv].
  ring_simplify in H2bc.
  repeat rewrite andb_true in H2bc. repnd.
  rewrite Decidable_spec in H2bc.

  (* The 2 cases generated by the destruct below are very different.
    In the None (anyrel) case, we manually make the lambdas.
     (Initially, I used a combinator, but ran into universe issues)
    In the Some (isorel case), we make make a constant (combinator) applied to arguments:
     in this case we know that the domain and the codomain are in Set/Prop: 
    We have disabled forall T:Type: True : Prop. *)
  Local Transparent sub_filter.
  assert (checkBC (free_vars B ++ remove x (free_vars piVarType)) B = true).
    revert H1bc. apply checkBCSubset. rewrite remove_app.
    rewrite  app_assoc.
    apply subset_app_r. reflexivity.
  assert (checkBC (free_vars piVarType ++ free_vars B) piVarType = true).
    revert H2bc3.
    apply checkBCSubset. apply subsetvAppLR;[| reflexivity].
    apply subset_app_r. reflexivity.
  destruct (needGoodnessPi true argsort bodySort).
  + simpl. unfold mkAppNoCheck, tvmap. simpl.
    repeat rewrite sub_filter_nil_r. simpl. f_equal.
    let rwTac := (clear Hind; repeat rewrite decideFalse by eauto with Param;
                   rewrite ssubst_aux_nil, ssubst_aux_trivial_disj;[refl|];
                   try (apply vDisjointTPrimeUserVar with (lb:=[x]); assumption);
                     try (apply vDisjointUserVar with (lb:=[x]); assumption)) in
    eqList; f_equal; symmetry;
      [ apply ssubst_trim
      | rewrite ssubst_trim_prime by auto; rewrite substAuxPrimeCommute1 | | | | ]; auto;
        symmetry;
        [ eapply Hind; eauto; [disjoint_reasoningv2| unfold all_vars; rwsimplC;
          eauto with SquiggleEq; fail]
        | f_equal; eqList; f_equal; symmetry; [apply ssubst_trim; assumption|]
        | f_equal; eqList; f_equal; symmetry;
          [rewrite ssubst_trim_prime by assumption;symmetry; apply substAuxPrimeCommute1 |]
        | eapply transLamSubstCommute; eauto; [|]; unfold all_vars; rwsimplC;
          eauto with SquiggleEq ];[|];
      simpl;
    rewrite (@decide_decideP (piVar=x) _);
    destructDecideP; subst; repeat rewrite deq_refl;
      [rwTac | | rwTac |]; simpl; [|];
    rename n into Hd;
    apply disjoint_neq_iff in Hd;
    (apply vAllRelatedFlatDisj in Hd; [| rwsimplC; eauto with SquiggleEq; fail]);
    simpl in Hd; repeat rewrite decideFalse by
        (apply disjoint_neq_iff;simpl; disjoint_reasoningv2);
    [apply ssubst_trim; auto |]; [].
    rewrite ssubst_trim_prime by assumption.
    symmetry. apply substAuxPrimeCommute1.
    Local Transparent decide.
  + (* no extra proofs because this Pi Type is in a higher universe. This part
      is same as the AnyRel translation *)
    admit.
- (* sort *)
  simpl. destruct lbt; [ | refl]. simpl map. cbv iota.
  rewrite ssubst_aux_trivial_disj;[refl | simpl; disjoint_reasoningv2]. 
  (* exactly same proof for all terms that take no lbt *)
- (* cast *) admit. (* not in the core calculus *)
- (* constant in the environment . also not a part of the core *)
  simpl. destruct lbt; [ | refl]. simpl map. cbv iota.
  rewrite ssubst_aux_trivial_disj;[refl | simpl; disjoint_reasoningv2].
- (* constructor constant in the env : note: it does not contain the constructor's args:
    need wo apply it explicitly. Thus, this case is exactly like the constant case:
    this is just a technicality that the kernel uses a different tag for the constructor 
    constants*)
  simpl. destruct lbt; [ | refl]. simpl map. cbv iota.
  rewrite ssubst_aux_trivial_disj;[refl | simpl; disjoint_reasoningv2].
- (* inductive constant in the env : note: it does not contain the inductives's args:
    need wo apply it explicitly. Thus, this case is exactly like the constant case:
    this is just a technicality that the kernel uses a different tag for the constructor 
    constants*)
  simpl. destruct lbt; [ | refl]. simpl map. cbv iota.
  rewrite ssubst_aux_trivial_disj;[refl | simpl; disjoint_reasoningv2].
- (* Fix : this will be complicated *) admit.
- (* app *)
  Local Transparent sub_filter.
  simpl. 
  (** We assume the Coq produces only well formed applications, with each app having only 1 arg.
     We can put a preprocessing phase to nest in cases of multiple args*)
  assert (map num_bvars lbt = [ 0; 0 ]%nat) as Hwf by admit.
  destruct lbt as [| f lbt]; [reflexivity | ]. simpl.
  let tac := invertsn Hwf in destructbtdeep2 f tac.
  simpl.
  destruct lbt as [| a lbt]; inverts Hwf as Ha Hwf.
  destruct lbt as [|]; [ | invertsn Hwf].
  let tac := invertsn Ha in destructbtdeep2 a tac.
  Local Opaque decide.
  simpl in *. unfold all_vars in Hvc. simpl in Hvc.
  autorewrite with list in *.
  rewrite cons_as_app in Hvc.
  rwsimpl Hvc. clear Hwf. repnd.
  do 2 (rewrite decide_true in H2bc;[| disjoint_reasoningv2]). 
  ring_simplify in H2bc. repeat rewrite  andb_true in H2bc. repnd.
  disjoint_reasoningv2.
  assert (checkBC (free_vars B ++ remove x (free_vars fnt)) B =true).
    revert H1bc. apply checkBCSubset. rewrite remove_app.
    rewrite  app_assoc.
    apply subset_app_r. reflexivity.
  assert ( checkBC (free_vars fnt ++ free_vars B) fnt = true).
    revert H2bc0.
    apply checkBCSubset. apply subsetvAppLR;[| reflexivity].
    apply subset_app_r. reflexivity.
  assert (checkBC (free_vars B ++ remove x (free_vars ant)) B =true).
    revert H1bc. apply checkBCSubset. rewrite remove_app.
    apply subsetvAppLR; [reflexivity|]. apply subset_app_l. reflexivity.
  assert ( checkBC (free_vars ant ++ free_vars B) ant = true).
    revert H2bc.
    apply checkBCSubset. rewrite <- app_assoc.
    apply subset_app_l. reflexivity.
    
  rewrite mkAppNoBeta. unfold mkApp, mkAppNoCheck. simpl.
  clear Hvc0.
   let tac := (progress f_equal) in
   let htac :=
      apply Hind with (lv:=[]); auto;
        try (disjoint_reasoningv2); try (rewrite cons_as_app; rwsimplC; eauto with SquiggleEq) in
            do 3 tac;[ htac | do 1 tac| do 2 tac;[ | tac; htac ] ];[ | ]; symmetry;
          [ apply ssubst_trim; assumption | ].
  rewrite ssubst_trim_prime by assumption.
  symmetry. apply substAuxPrimeCommute1.
- (* match : this will be complicated *) admit.
Fail idtac.
Admitted.

Definition goodInput (outerBvars : list V) (t:STerm) : Prop :=
  (varsOfClass (all_vars t) userVar) /\ (checkBC outerBvars t = true).


(** there is a much more elegant proof of this *)
Lemma translateRespectsAlpha ienv (a b: STerm) :
  goodInput (free_vars a) a -> goodInput (free_vars b) b -> alpha_eq a b -> alpha_eq (translate true ienv a) (translate true ienv b).
Proof using.
  intros H1g H2g Hal.
  induction Hal as [|op lbt lbt2 Hlen Hbt];[refl| destruct op].
(* Lambda *)
- Local Opaque transLam.
  simpl.
  destruct lbt as [| b  lbt]; simpl; simpl in Hlen;
    dlist_len lbt2; [  refl|]. rename lbt0 into b2.
  let tac := try reflexivity in destructbtdeep2 b tac.
  rename bnt into lamTyp.
  (* process each BTerm before going to the next *)
(*  destruct lbt as [| b2  lbt]; [refl |].
  let tac := try reflexivity in destructbtdeep2 b2 tac.
  rename b2lv1 into lamVar.
  rename b2nt into lamBody.
  Local Opaque sub_filter.
  destruct lbt; [ |refl].
  Local Opaque decide.
  simpl in *.
    
  *)  
Admitted.

(* delete *)
Ltac add_changebvar_spec4 cb Hn:=
match goal with 
| [ |- context[@change_bvars_alpha ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?lv ?nt] ] =>
   pose proof (@change_bvars_alpha_spec2 a1 a2 a3  a5 a4 _ a6 nt lv) as Hn;
    remember (@change_bvars_alpha a1 a2 a3 a4 a5 a6 lv nt) as cb
| [ |- context[@change_bvars_alphabt ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?lv ?nt] ] =>
  pose proof (@change_bvars_alphabt_spec2 a1 a2 a3  a5 a4 _ a6 lv nt) as Hn;
    remember (@change_bvars_alphabt a1 a2 a3 a4 a5 a6 lv nt) as cb
end.

Lemma translate_bcsubst_commute ienv (outerBvars : list V) : forall (A B: STerm) (x:V),
    let lam := bterm [x] A in
    let apT := (oterm (CApply 1) [lam ; bterm [] B]) in
subset (free_vars apT) outerBvars
-> checkBC outerBvars apT =true
-> varsOfClass (x::(all_vars A (* ++ all_vars B*) )) userVar
-> let tr := translate true ienv in
  alpha_eq
    (tr (bcSubst outerBvars A [(x,B)]))
    ((bcSubst (flat_map vAllRelated outerBvars) (tr A) [(x,B); (vprime x, tprime B); (vrel x, tr B)])).
Proof.
  simpl.
  intros ? ? ? Hs Hbc Hvc.
  simpl in Hbc.
  setoid_rewrite decide_true in Hbc at 2;[| disjoint_reasoningv].
  ring_simplify in Hbc.
  repeat rewrite andb_true in Hbc.
  repnd.
  unfold bcSubst.
  add_changebvar_spec4 Ap Hn. clear HeqAp.
  add_changebvar_spec4 Atp Htn. clear HeqAtp.
  simpl in *. 
  rewrite app_nil_r in *.
  repnd.
  pose proof Hn2 as Hal.
  rewrite cons_as_app in Hvc. rwsimpl Hvc. repnd.
  pose proof Hvc as Hvcb.
  unfold all_vars in Hvcb. rwsimpl Hvcb. repnd.
  clear Hvc0. unfold singleton in *.
  assert ( subset (free_vars A) (x :: outerBvars)) as H1s.
    eapply subset_trans.
    apply removeConsCancel with (r:=x). apply subset_cons2.
    eapply subset_trans;[| apply Hs].
    apply subset_app_r. reflexivity.

  apply (translateRespectsAlpha ienv) in Hal.
  Focus 2.
    split; [assumption|].
    revert Hbc3. apply (fst checkBCSubset). apply H1s.

  Focus 2.
    split; [admit (*  varsOfClass (all_vars Ap) userVar *)|].
    revert Hn0. apply (fst checkBCSubset).
    rewrite cons_as_app. rewrite app_assoc.
    apply subset_app_r. rewrite <- Hn2. apply H1s.

  (*rewrite Htn in Hn.*)
  symmetry.
  rewrite <- ssubst_ssubst_aux;[| simpl].
  Focus 2.
    (* vars RHS are a subset of (flat_map vAllRelated (free_vars B)) 
     because  (bound_vars Atp) only has vars of class [userVar], it suffices to
     replace the RHS merely with (free_vars B) 
    *)
     revert Htn1. revert Hs.  (* now these should be enough *) rewrite app_nil_r.
  (*
  subset (remove x (free_vars A) ++ free_vars B) outerBvars ->
  disjoint
    (x
     :: vprime x
        :: vrel x
           :: flat_map vAllRelated outerBvars ++
              bound_vars B ++ bound_vars (tprime B) ++ bound_vars (translate true ienv B))
    (bound_vars Atp) ->
  disjoint (bound_vars Atp)
    (free_vars B ++ free_vars (tprime B) ++ free_vars (translate true ienv B))
*)
    admit.

  rewrite Htn2 in Hal.
  rewrite Hal.
  symmetry.
  
  rewrite translateSubstCommute;
    [ | disjoint_reasoningv2 | | | (*  varsOfClass (x :: all_vars Ap) userVar *) admit] .
  Focus 2.
    revert Hbc1. apply (fst checkBCSubset).
    rewrite eqset_app_comm. simpl. rewrite <- Hn2. assumption.

  Focus 2.
    revert Hn0. apply (fst checkBCSubset). rewrite cons_as_app. rewrite app_assoc.
    apply subset_app_r. rewrite <- Hn2. apply subset_app.
    split;[apply H1s|].
    apply subset_app_l. eapply subset_trans;[| apply Hs]. apply subset_app_l. reflexivity.

  rewrite  ssubst_ssubst_aux;[refl| simpl]. rewrite app_nil_r.
    
(*
disjoint (bound_vars (translate true ienv Ap))
    (free_vars B ++ free_vars (tprime B) ++ free_vars (translate true ienv B)
 true because [Ap] avoides [outerBvars] and  [outerBvars] includes [free_vars B]
*)  
Abort.

(** this is refutable, hence only a temporary hack. 
  In the end, replace [mkAppBeta] witn [mkAppUnFlattened ]in [translate] *)
Lemma mkAppSimpl : mkAppBeta = mkAppUnFlattened. Admitted.

Lemma mkAppCongrLeft sf (outerBvars: list V) (FL FR arg :STerm)  :
  red sf outerBvars FL FR
  -> red sf outerBvars (mkApp FL [arg]) (mkApp FR [arg]).
Proof using.
  intros Hr.
  apply congruence with (n:=0%nat); simpl; auto.
  intros m Hneq. destruct m; simpl; auto. lia.
Qed.

Inductive clos_refl_sym_trans (R : Relation_Definitions.relation STerm)
  : Relation_Definitions.relation STerm :=
    rst_step : forall x y : STerm, R x y -> clos_refl_sym_trans R x y
  | rst_refl : forall x y: STerm, alpha_eq x y -> clos_refl_sym_trans R x y
  | rst_sym : forall x y : STerm, clos_refl_sym_trans R x y -> clos_refl_sym_trans R y x
  | rst_trans : forall x y z : STerm,
                clos_refl_sym_trans R x y ->
                clos_refl_sym_trans R y z -> clos_refl_sym_trans R x z.

(* target language, where we dont have to worry about shadowing *)
Definition defEqT :   STerm -> STerm -> Prop :=
clos_refl_sym_trans (red (fun _ => ssubst) []).

Lemma translateRedCommute ienv : forall (A B: STerm) outerBvars,
(* subset (free_vars A) outerBVars -> checkBC outerBVars A = true*)
 redS outerBvars A B
(* 3 beta reductions *)        
-> defEqT (translate true ienv A) (translate true ienv B).
Proof using.
  intros ? ? ? Hred. induction Hred.
- simpl. Local Transparent transLam. unfold transLam. simpl.
  rewrite  mkAppSimpl. simpl.

  eapply rst_trans;
   [apply rst_step; apply mkAppCongrLeft; apply mkAppCongrLeft;apply beta|].
  eapply rst_trans.
  
  simpl. apply rst_step. apply mkAppCongrLeft.
  Fail apply beta. (* the lambda bterm needs to be visible. need another version of ssubst that doesn't
    do unnecessary renamings as much as possible *)
  (* blows up. because bcSubst has to go over mkLam before [beta] can unify.
     Solutions:
      1) make change_bvar_alphabt skip renaming if not necessary. here the variable [vprime x]
         already satisfies the desired specs. [vprime x] is not [x]. It is not in [outerBvars]
         because of the hypothesis [check outerBvars A= true]. It is not in 
         [flat_map bound_vars [arg]] because its class is different.
--->  2) use normal safe substitution (ssubst) in the conclusion. the BC stuff is only needed
         BEFORE the translation.
         Make another version of subst that delays renaming even more (deeper), until it actually
         hits a bterm with a problematic bound variable.
      3) In the target, use a reduction rule that directly does beta for 3 apps and 3 lams
   *)
(*   [apply rst_step; apply mkAppCongrLeft;apply beta|]. *)
Abort.

Lemma translateDefnEqCommute ienv : forall (A B: STerm) outerBvars,
(* preconditions *)
defEqS outerBvars A B
-> defEqT (translate true ienv A) (translate true ienv B).
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
