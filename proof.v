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


Lemma translateSubstCommute : forall (A B: STerm) (x:V),
(* disjoint (free_vars B) (bound_vars A) 
->*)
let tr := translate true in
tr (ssubst_aux A [(x,B)])
= (ssubst_aux (tr A) [(x,B); (vprime x, tprime B); (vrel x, tr B)]).
Proof.
  simpl.
  induction A using NTerm_better_ind; intros B x.
- match goal with
  [ |- _ = ?r] => set (rhs:= r)
  end.
  simpl.
  rewrite beq_deq.
  cases_if as hd; subst.
  + simpl. unfold rhs. simpl.
    rewrite <- beq_var_refl.
    autorewrite with Param. refl.
  + simpl. unfold rhs. simpl.
     








