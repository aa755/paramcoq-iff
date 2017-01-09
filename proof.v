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

Inductive red : STerm -> STerm -> Prop := .


(* Move *)
Definition tvmap_bterm := 
fun {V1 V2 O : Type} (fv : V1-> V2) =>
@tmap_bterm V1 V2 O O fv (@id O).

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

Lemma substPrimeCommute: forall (A B: STerm) (x:V),
(* NO need to assume that vars in a and b and the var x have class 0 *)
let bt:= (bterm [x] A) in
tprime (apply_bterm bt [B]) =
(apply_bterm (btprime bt) [(tprime B)]).
Admitted.

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


Lemma vRelInjective v1 v2 : v1 <> v2 ->
  vrel v1 <> vrel v2.
Proof using.
  intros Heq.
  unfold vrel.
  intros Hc.
  destruct v1, v2.
  simpl in *.
  apply Heq.
  clear Heq.
  inverts Hc.
  f_equal; [lia|].
  SearchAbout String.append.
  SearchAbout String.get.
  destruct n0, n2; try inverts H1;[refl|].
  clear H0 n1. 
Admitted. (* append is injective *)
  
Hint Rewrite varClassVPrime: Param.
Hint Rewrite varClassVRel: Param.

Local Transparent BinNat.N.add .

Ltac hideRHS rhs :=
match goal with
  [ |- _ = ?r] => set (rhs:= r)
  end.
  
Lemma translateSubstCommute : forall (A B: STerm) (x:V),
(* disjoint (free_vars B) (bound_vars A) 
->*)
varsOfClass (x::(all_vars A (* ++ all_vars B*) )) userVar
->
let tr := translate true in
tr (ssubst_aux A [(x,B)])
= (ssubst_aux (tr A) [(x,B); (vprime x, tprime B); (vrel x, tr B)]).
Proof.
  simpl.
  induction A using NTerm_better_ind; intros B x Hvc;[|destruct o]; try refl;
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
    apply vRelInjective. assumption.
(* Lambda *)
- destruct lbt as [| b  lbt]; simpl; [refl|].
  (* process each BTerm before going to the next *)
  destruct b as [lv lamTyp].
  destruct lv as [|];[| refl].
  destruct lbt as [| b2  lbt]; [refl |].
  destruct b2 as [b2lv lamBody].
  destruct b2lv as [|lamVar b2lv];[refl|].
  destruct b2lv as [|];[|refl].
  destruct lbt as [| b3 lbt]; [| refl].
  hideRHS rhs. simpl.
  unfold transLam. simpl. unfold mkAppBeta. simpl.
  rewrite decide_decideP.
  
  destruct (decideP (lamVar = x)).
  + rewrite ssubst_aux_nil. subst. simpl.
    unfold rhs. clear rhs.
    Local Opaque ssubst_bterm_aux.
    simpl. f_equal.
    
     f_equal. 
    set (b:= match argSort with
                     | Some s => isPropOrSet s
                     | None => false
                     end
                     ).
    
                     
    
    rewrite deq_refl.
    do 2 rewrite decideFalse by eauto with Param.
    autorewrite with SquiggleEq.
    rewrite decideFalse by eauto with Param.
    SearchAbout decide.
    repeat rewrite decide_decideP.
    cases_if.
    fold (@beq_var _ _ x (vprime x)).
    autorewrite with Param.
    f_equal.
    cases_if.
    Local Transparent transLamAux. simpl.
(*
hasSortSetOrProp (ssubst_aux nt [(x, B)]
  (ssubst_aux
                 ((if hasSortSetOrProp nt
                   then
                    fun t : 
                    ...
                    )
*)

Abort.  








