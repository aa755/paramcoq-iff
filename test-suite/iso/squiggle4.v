Require Import ReflParam.common.
Require Import ReflParam.templateCoqMisc.
Require Import String.
Require Import List.
Require Import Template.Ast.
Require Import SquiggleEq.terms.
Require Import ReflParam.paramDirect ReflParam.indType.
Require Import ReflParam.indProp.
Require Import SquiggleEq.substitution.
Require Import ReflParam.PiTypeR.
Import ListNotations.
Open Scope string_scope.

Require Import ReflParam.Trecord.


Set Imlicit Arguments.

Inductive eqs {A : Set} (x : A) : forall (a:A), Prop :=  
  eq_refls : eqs x x.

Inductive option (A : Set) : Set :=  Some : A -> option A | None : option A.
Arguments Some {A} _.
Arguments None {A}.

Infix "=" := eqs : type_scope.
Notation True := (true=true).
Notation False := (false=true).

Definition isNone {A:Set} (oa: option A) :=
  match oa with
  | Some _ => false
  | None => true
  end.
Infix "+" := sum:type_scope.
(*
Definition beq (b1 b2 : bool) := eqs bool b1 b2.
 *)


Open Scope nat_scope.

Section Squiggle4.
  (* Variable V:Set. This interface is too abstract for exposing V *)
Variables (Tm BTm : Set).
Variable applyBtm: BTm -> Tm -> Tm.

Inductive TmKind :=
| elam (bt: BTm) 
| eapp (f a: Tm) 
| enum (n: nat)
| evar.

Variable tmKind:  Tm -> TmKind.

Section eval.

Variable evaln: nat -> Tm -> option Tm.

(* just this would be an example. However, because it is not recursive,
 even tauto may be able to prove it. Even if we only show this on paper,
we should have a more complex (recursively defined undefined relation)
in the appendix *)
Definition divergesIff (tl tr:Tm) : Prop :=
  (forall (nsteps:nat), (isNone (evaln nsteps tl)) = true) <->
  (forall (nsteps:nat), (isNone (evaln nsteps tr)) = true).

 (* need to eliminate the oneOne of Prop inductives and use PI *)
 
(*  
(fun _ => 0) 2
(fun _ => 0) 4

This rule will judge the above to be different. We never see inside non-canonical
terms!
 | eapp fl al , eapp fr ar => obsEq k fl fr /\ obsEq k al ar 
*)

Fixpoint obsEq (k:nat) (tl tr:Tm) {struct k}: Prop :=
divergesIff tl tr /\ forall (nsteps:nat), 
match k with | 0 => True | S k =>
  match evaln nsteps tl, evaln nsteps tr with
  | Some vl, Some vr => 
     match tmKind vl, tmKind vr with
     | enum nl , enum nr => nl = nr
     | elam btl , elam btr => forall (ta: Tm), obsEq k (applyBtm btl ta) (applyBtm btr ta)
     | _,_ => False
     end
  | _, _  => True
  end
end.

End eval.

Open Scope nat_scope.
Fixpoint evaln (n:nat) (t:Tm): option Tm :=
match n with
| 0 => None | S n => 
  match (tmKind t)
  with
  | evar => None
  | elam _ | enum _ => Some t
  | eapp f a =>
    match evaln n f, evaln n a with
    | Some f, Some a =>
      match (tmKind f) with
      | elam bt => evaln n (applyBtm bt a)
      | _ => None
      end
    | _,_ => None
    end
  end
end.

End Squiggle4.

Arguments elam {Tm} {BTm} bt.
Arguments eapp {Tm} {BTm} f a.
Arguments enum {Tm} {BTm} n.
Arguments evar {Tm} {BTm}.


Run TemplateProgram (genParamIndAll [] "Coq.Init.Datatypes.bool").
Run TemplateProgram (genParamIndAll [] "Coq.Init.Datatypes.nat").
Run TemplateProgram (genParamIndPropAll [] "Top.squiggle4.eqs").
Run TemplateProgram (genParamIndAll [] "Top.squiggle4.option").

(* and, unlike exists, allows singleton elim because the 2 args of its constructor
are proofs *)
Run TemplateProgram (genParamIndPropAll [] "Coq.Init.Logic.and").
Run TemplateProgram (genParamIndAll [] "Top.squiggle4.TmKind").

Run TemplateProgram (mkIndEnv "indTransEnv" [
"Coq.Init.Datatypes.bool" ; "Coq.Init.Datatypes.nat";
(* "Coq.Init.Logic.and";  "Top.squiggle4.eqs"; *)
 "Top.squiggle4.option"; 
 (* "Top.squiggle2.sum";  "Top.squiggle2.list"; "Top.squiggle2.prod"; *)
 "Top.squiggle4.TmKind"]).

Run TemplateProgram (genWrappers indTransEnv).

Run TemplateProgram (genParam indTransEnv true true "Top.squiggle4.evaln").
(* slow and the result is bloated *)

Run TemplateProgram (genParam indTransEnv true true "Top.squiggle4.isNone").

Run TemplateProgram (genParam indTransEnv true true "Coq.Init.Logic.iff").


Run TemplateProgram (genParam indTransEnv true true "Top.squiggle4.divergesIff").
(* quick *)
Run TemplateProgram (genParam indTransEnv true true "Top.squiggle4.obsEq").
(* bloated *)

(*
Opaque 
Coq_Init_Datatypes_bool_pmtcty_RR0_constr_0_inv Coq_Init_Datatypes_bool_pmtcty_RR0_constr_0_tot Coq_Init_Datatypes_bool_pmtcty_RR0_constr_1 Coq_Init_Datatypes_bool_pmtcty_RR0_constr_1_inv Coq_Init_Datatypes_bool_pmtcty_RR0_constr_1_tot Coq_Init_Datatypes_nat_pmtcty_RR0 Coq_Init_Datatypes_nat_pmtcty_RR0_constr_0 Coq_Init_Datatypes_nat_pmtcty_RR0_constr_0_inv Coq_Init_Datatypes_nat_pmtcty_RR0_constr_0_tot Coq_Init_Datatypes_nat_pmtcty_RR0_constr_1 Coq_Init_Datatypes_nat_pmtcty_RR0_constr_1_inv Coq_Init_Datatypes_nat_pmtcty_RR0_constr_1_tot Coq_Init_Logic_and_pmtcty_RR0 Coq_Init_Logic_and_pmtcty_RR0_constr_0 
Coq_Init_Logic_and_pmtcty_RR0_constr_0_tot Top_squiggle4_eqs_pmtcty_RR0 Top_squiggle4_eqs_pmtcty_RR0_constr_0 
Top_squiggle4_eqs_pmtcty_RR0_constr_0_tot Top_squiggle4_option_pmtcty_RR0 Top_squiggle4_option_pmtcty_RR0_constr_0 Top_squiggle4_option_pmtcty_RR0_constr_0_inv Top_squiggle4_option_pmtcty_RR0_constr_0_tot Top_squiggle4_option_pmtcty_RR0_constr_1 Top_squiggle4_option_pmtcty_RR0_constr_1_inv Top_squiggle4_option_pmtcty_RR0_constr_1_tot Top_squiggle4_TmKind_pmtcty_RR0 
Top_squiggle4_TmKind_pmtcty_RR0_constr_0 
Top_squiggle4_TmKind_pmtcty_RR0_constr_0_inv 
Top_squiggle4_TmKind_pmtcty_RR0_constr_0_tot 
Top_squiggle4_TmKind_pmtcty_RR0_constr_1 
Top_squiggle4_TmKind_pmtcty_RR0_constr_1_inv 
Top_squiggle4_TmKind_pmtcty_RR0_constr_1_tot 
Top_squiggle4_TmKind_pmtcty_RR0_constr_2 
Top_squiggle4_TmKind_pmtcty_RR0_constr_2_inv 
Top_squiggle4_TmKind_pmtcty_RR0_constr_2_tot
Top_squiggle4_TmKind_pmtcty_RR0_constr_3 
Top_squiggle4_TmKind_pmtcty_RR0_constr_3_inv 
Top_squiggle4_TmKind_pmtcty_RR0_constr_3_tot
.
*)
Require Import ReflParam.unusedVar.
Require Import JMeq.

Definition existsAGoodnessFreeImpl2 
{T: forall (A A₂ : Set) (A_R : BestRel A A₂) (B B₂ : Set) (B_R : BestRel B B₂), Type}
(P : forall (A A₂ : Set) (A_R : BestRel A A₂)
(B B₂ : Set) (B_R : BestRel B B₂) , T A A₂ A_R B B₂ B_R) : Type :=
forall 
(A A₂ : Set) (Ra: (A -> A₂ -> Prop))
(B B₂ : Set) (Rb: (B -> B₂ -> Prop)),
sigT (fun T:Type => sig (fun (f:T) =>
forall pta poa ptb pob, 
let A_R : BestRel A A₂ := {| R:= Ra; Rtot := pta ; Rone := poa|} in
let B_R : BestRel B B₂ := {| R:= Rb; Rtot := ptb ; Rone := pob|} in
JMeq (P A A₂ A_R B B₂ B_R) f)).

Definition existsAOneFreeImpl2 
{T: forall (A A₂ : Set) (A_R : BestRel A A₂) (B B₂ : Set) (B_R : BestRel B B₂), Type}
(P : forall (A A₂ : Set) (A_R : BestRel A A₂)
(B B₂ : Set) (B_R : BestRel B B₂) , T A A₂ A_R B B₂ B_R) : Type :=
forall 
(A A₂ : Set) (Ra: (A -> A₂ -> Prop)) pta 
(B B₂ : Set) (Rb: (B -> B₂ -> Prop)) ptb,
sigT (fun T:Type => sig (fun (f:T) =>
forall poa pob, 
let A_R : BestRel A A₂ := {| R:= Ra; Rtot := pta ; Rone := poa|} in
let B_R : BestRel B B₂ := {| R:= Rb; Rtot := ptb ; Rone := pob|} in
JMeq (P A A₂ A_R B B₂ B_R) f)).

(*
Lemma evalnGoodnessFree  : existsAGoodnessFreeImpl2
  (Top_squiggle4_evaln_pmtcty_RR).
  eexists.
  eexists.
  intros.
  set (fvv:= Top_squiggle4_evaln_pmtcty_RR _ _ A_R _ _ B_R).
  simpl in *.
  unfold Top_squiggle4_evaln_pmtcty_RR in fvv.
  simpl in fvv.
  simpl in *.
  do 10(
  unfold
Coq_Init_Datatypes_bool_pmtcty_RR0_constr_0_inv_iso, 
Coq_Init_Datatypes_bool_pmtcty_RR0_constr_1_inv_iso, 
Coq_Init_Datatypes_nat_pmtcty_RR0_iso, 
Coq_Init_Datatypes_nat_pmtcty_RR0_constr_0_inv_iso, 
Coq_Init_Datatypes_nat_pmtcty_RR0_constr_0_iso, 
Coq_Init_Datatypes_nat_pmtcty_RR0_constr_1_inv_iso, 
Coq_Init_Datatypes_nat_pmtcty_RR0_constr_1_iso, 
Coq_Init_Logic_and_pmtcty_RR0_iso, 
Top_squiggle4_eqs_pmtcty_RR0_iso, 
Top_squiggle4_option_pmtcty_RR0_iso, 
Top_squiggle4_option_pmtcty_RR0_constr_0_inv_iso, 
Top_squiggle4_option_pmtcty_RR0_constr_0_iso, 
Top_squiggle4_option_pmtcty_RR0_constr_1_inv_iso, 
Top_squiggle4_option_pmtcty_RR0_constr_1_iso, 
Top_squiggle4_TmKind_pmtcty_RR0_iso, 
Top_squiggle4_TmKind_pmtcty_RR0_constr_0_inv_iso, 
Top_squiggle4_TmKind_pmtcty_RR0_constr_0_iso, 
Top_squiggle4_TmKind_pmtcty_RR0_constr_1_inv_iso, 
Top_squiggle4_TmKind_pmtcty_RR0_constr_1_iso, 
Top_squiggle4_TmKind_pmtcty_RR0_constr_2_inv_iso, 
Top_squiggle4_TmKind_pmtcty_RR0_constr_2_iso,
Top_squiggle4_TmKind_pmtcty_RR0_constr_3_inv_iso, 
Top_squiggle4_TmKind_pmtcty_RR0_constr_3_iso
in fvv;
  cbn in fvv;
  simpl in *;
  cbn in * ) .
  reflexivity.
Defined.  (* works *)
*)
