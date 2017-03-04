Require Import ReflParam.common.
Require Import ReflParam.templateCoqMisc.
Require Import String.
Require Import List.
Require Import Template.Ast.
Require Import SquiggleEq.terms.
Require Import ReflParam.paramDirect ReflParam.indType.
Require Import SquiggleEq.substitution.
Require Import ReflParam.PiTypeR.
Import ListNotations.
Require Import squiggle2.
Open Scope string_scope.

Require Import ReflParam.Trecord.


Set Imlicit Arguments.


Open Scope nat_scope.
Section Squiggle3.
  (* Variable V:Set. This interface is too abstract for exposing V *)
  Variable Tm:Set.
  (*
  Variable app: Tm -> Tm -> Tm.
  Variable lam: Tm -> Tm.
  Variable num: nat -> Tm.
  *)
  Variable elimTerm:  Tm -> (tmExt Tm).

  (* Tm now stands for NTerm + BTerm. the arg of a lam must be a BTerm.
   This is a nop if Tm was a NTerm. *)
  Variable applyBtm: Tm -> Tm -> Tm.
  Variable evaln: nat -> Tm -> option Tm.

(* just this would be an example. However, because it is not recursive,
 even tauto may be able to prove it. Even if we only show this on paper,
we should have a more complex (recursively defined undefined relation)
in the appendix *)
Definition divergesIff (tl tr:Tm) : Prop :=
  (forall (nsteps:nat), eqs _ (isNone (evaln nsteps tl)) true) <->
  (forall (nsteps:nat), eqs _ (isNone (evaln nsteps tr)) true).

Fixpoint obsEq (k:nat)(tl tr:Tm) {struct k}: Prop :=
  divergesIff tl tr /\ (* need to eliminate the oneOne of Prop inductives and use PI *)
  forall (nsteps:nat), 
match k with | 0 => eqs _ 0 1 | S k =>
    match evaln nsteps tl, evaln nsteps tr with
    | Some vl, Some vr => 
          match elimTerm vl, elimTerm vr with
          | enum nl , enum nr => eqs _ nl nr
          | elam btl , elam btr =>
              forall (ta: Tm), obsEq k (applyBtm btl ta) (applyBtm btr ta)
          | eapp fl al , eapp fr ar =>
            obsEq k fl fr /\ obsEq k al ar
          | _,_ => eqs _ 0 1
          end
    | _, _  => eqs _ 0 0
    end
end.

End Squiggle3.


Run TemplateProgram (mkIndEnv "indTransEnv" [
"Coq.Init.Datatypes.bool" ; "Coq.Init.Datatypes.nat";
"Coq.Init.Logic.and"; "Top.squiggle2.eqs"; 
 "Top.squiggle2.option"; 
 (* "Top.squiggle2.sum";  "Top.squiggle2.list"; "Top.squiggle2.prod"; *)
 "Top.squiggle2.tmExt"]).

Run TemplateProgram (genWrappers indTransEnv).


Run TemplateProgram (genParam indTransEnv true true "Top.squiggle3.divergesIff").
(* quick *)
Run TemplateProgram (genParam indTransEnv true true "Top.squiggle3.obsEq").
(* bloated *)

Opaque 
Coq_Init_Datatypes_bool_pmtcty_RR0_constr_0_inv Coq_Init_Datatypes_bool_pmtcty_RR0_constr_0_tot Coq_Init_Datatypes_bool_pmtcty_RR0_constr_1 Coq_Init_Datatypes_bool_pmtcty_RR0_constr_1_inv Coq_Init_Datatypes_bool_pmtcty_RR0_constr_1_tot Coq_Init_Datatypes_nat_pmtcty_RR0 Coq_Init_Datatypes_nat_pmtcty_RR0_constr_0 Coq_Init_Datatypes_nat_pmtcty_RR0_constr_0_inv Coq_Init_Datatypes_nat_pmtcty_RR0_constr_0_tot Coq_Init_Datatypes_nat_pmtcty_RR0_constr_1 Coq_Init_Datatypes_nat_pmtcty_RR0_constr_1_inv Coq_Init_Datatypes_nat_pmtcty_RR0_constr_1_tot Coq_Init_Logic_and_pmtcty_RR0 Coq_Init_Logic_and_pmtcty_RR0_constr_0 Coq_Init_Logic_and_pmtcty_RR0_constr_0_inv Coq_Init_Logic_and_pmtcty_RR0_constr_0_tot Top_squiggle2_eqs_pmtcty_RR0 Top_squiggle2_eqs_pmtcty_RR0_constr_0 Top_squiggle2_eqs_pmtcty_RR0_constr_0_inv Top_squiggle2_eqs_pmtcty_RR0_constr_0_tot Top_squiggle2_option_pmtcty_RR0 Top_squiggle2_option_pmtcty_RR0_constr_0 Top_squiggle2_option_pmtcty_RR0_constr_0_inv Top_squiggle2_option_pmtcty_RR0_constr_0_tot Top_squiggle2_option_pmtcty_RR0_constr_1 Top_squiggle2_option_pmtcty_RR0_constr_1_inv Top_squiggle2_option_pmtcty_RR0_constr_1_tot Top_squiggle2_tmExt_pmtcty_RR0 Top_squiggle2_tmExt_pmtcty_RR0_constr_0 Top_squiggle2_tmExt_pmtcty_RR0_constr_0_inv Top_squiggle2_tmExt_pmtcty_RR0_constr_0_tot Top_squiggle2_tmExt_pmtcty_RR0_constr_1 Top_squiggle2_tmExt_pmtcty_RR0_constr_1_inv Top_squiggle2_tmExt_pmtcty_RR0_constr_1_tot Top_squiggle2_tmExt_pmtcty_RR0_constr_2 Top_squiggle2_tmExt_pmtcty_RR0_constr_2_inv Top_squiggle2_tmExt_pmtcty_RR0_constr_2_tot
.

Require Import ReflParam.unusedVar.

Lemma obsEqExistsAOneFreeImpl  : existsAOneFreeImpl
  (Top_squiggle3_obsEq_pmtcty_RR).
Proof.
  eexists.
  eexists.
  intros.
  set (fvv:= Top_squiggle3_obsEq_pmtcty_RR _ _ V_R).
  simpl in *.
  lazy in fvv.
  reflexivity.
Defined.

(*
Lemma dependsOnlyOnTotdivergesIff  : existsAOneFreeImpl
  (Top_squiggle2_divergesIff_pmtcty_RR).
Proof.
  eexists.
  eexists.
  intros.
  set (fvv:= Top_squiggle2_divergesIff_pmtcty_RR _ _ V_R).
  simpl in *.
  lazy in fvv.
  reflexivity. (* works *)
Defined.
*)
(*
Lemma dependsOnlyOnTotdivergesIff (V V₂ : Set) : @dependsOnlyOnRelTot V V₂ _
  (Top_squiggle2_divergesIff_pmtcty_RR V V₂).
Proof.
  intros ? ? ?.
  destruct V_R1.
  reflexivity.
Qed.
*)