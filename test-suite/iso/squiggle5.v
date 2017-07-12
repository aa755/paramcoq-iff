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

Section Squiggle5.
  (* Variable V:Set. This interface is too abstract for exposing V *)
Variables (Tm BTm : Set).
Variable applyBtm: BTm -> Tm -> Tm.

Inductive TmKind :=
| elam (bt: BTm) 
| eapp (f a: Tm) 
| enum (n: nat)
| evar.

Variable tmKind:  Tm -> TmKind.

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

Definition obseq (tl tr:Tm) := forall (k:nat), obsEq k tl tr.

End Squiggle5.

Arguments elam {Tm} {BTm} bt.
Arguments eapp {Tm} {BTm} f a.
Arguments enum {Tm} {BTm} n.
Arguments evar {Tm} {BTm}.


Run TemplateProgram (genParamIndAll [] "Coq.Init.Datatypes.bool").
Run TemplateProgram (genParamIndAll [] "Coq.Init.Datatypes.nat").
Run TemplateProgram (genParamIndPropAll [] "Top.squiggle5.eqs").
Run TemplateProgram (genParamIndAll [] "Top.squiggle5.option").

(* and, unlike exists, allows singleton elim because the 2 args of its constructor
are proofs *)
Run TemplateProgram (genParamIndPropAll [] "Coq.Init.Logic.and").
Run TemplateProgram (genParamIndAll [] "Top.squiggle5.TmKind").

Run TemplateProgram (mkIndEnv "indTransEnv" [
"Coq.Init.Datatypes.bool" ; "Coq.Init.Datatypes.nat";
(* "Coq.Init.Logic.and";  "Top.squiggle5.eqs"; *)
 "Top.squiggle5.option"; 
 (* "Top.squiggle2.sum";  "Top.squiggle2.list"; "Top.squiggle2.prod"; *)
 "Top.squiggle5.TmKind"]).

Run TemplateProgram (genWrappers indTransEnv).

Run TemplateProgram (genParam indTransEnv true true "Top.squiggle5.evaln").
(* slow and the result is bloated *)

Run TemplateProgram (genParam indTransEnv true true "Top.squiggle5.isNone").

Run TemplateProgram (genParam indTransEnv true true "Coq.Init.Logic.iff").


Run TemplateProgram (genParam indTransEnv true true "Top.squiggle5.divergesIff").
(* quick *)
Run TemplateProgram (genParam indTransEnv true true "Top.squiggle5.obsEq").
(* bloated *)
Run TemplateProgram (genParam indTransEnv true true "Top.squiggle5.obseq").

Require Import ReflParam.unusedVar.

(*
Lemma obsEqExistsAOneFreeImpl  : existsAOneFreeImpl2
  (Top_squiggle5_obsEq_pmtcty_RR).
Proof.
  eexists.
  eexists.
  intros.
  set (fvv:= Top_squiggle5_obsEq_pmtcty_RR _ _ A_R _ _ B_R).
  simpl in *.
  lazy in fvv.
  reflexivity.
Defined.
*)