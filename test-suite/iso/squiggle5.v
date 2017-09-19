(*
Warning! When viewing the file interactively in a Coq editor, the -top arument
must be passed. use the script ./coqid.sh, which should be invoked as follows:

./coqid.sh squiggle5

Note that there is no .v at the end. The script will then pass the argument "-top squiggle5"
to coqtop. No special handling is needed for coqc: it already assumes that the top level module
is squiggle5 (instead of "Top")
*)

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

(** Just like [eq] from the standard library. But in [Set], so that IsoRel works *)
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


Open Scope nat_scope.

Section Squiggle5.
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


Definition divergesIff (tl tr:Tm) : Prop :=
  (forall (nsteps:nat), (isNone (evaln nsteps tl)) = true) <->
  (forall (nsteps:nat), (isNone (evaln nsteps tr)) = true).

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


(** Before we translate definition, we must translate all its dependencies : other definitions
mentioned in its body. Someday, this dependency calculation would be automated, like in paramcoq [Lasson and Keller]
For now, we translate items one by one, in the order of dependencies.*)
Run TemplateProgram (genParamIndAll [] "Coq.Init.Datatypes.bool").
Run TemplateProgram (genParamIndAll [] "Coq.Init.Datatypes.nat").
Run TemplateProgram (genParamIndPropAll [] "Top.squiggle5.eqs").
Run TemplateProgram (genParamIndAll [] "Top.squiggle5.option").

Run TemplateProgram (genParamIndPropAll [] "Coq.Init.Logic.and").
Run TemplateProgram (genParamIndAll [] "Top.squiggle5.TmKind").

Run TemplateProgram (mkIndEnv "indTransEnv" [
"Coq.Init.Datatypes.bool" ; "Coq.Init.Datatypes.nat";
 "Top.squiggle5.option"; 
 "Top.squiggle5.TmKind"]).

Run TemplateProgram (genWrappers indTransEnv).

Run TemplateProgram (genParam indTransEnv true true "Top.squiggle5.evaln").

Run TemplateProgram (genParam indTransEnv true true "Top.squiggle5.isNone").

Run TemplateProgram (genParam indTransEnv true true "Coq.Init.Logic.iff").


Run TemplateProgram (genParam indTransEnv true true "Top.squiggle5.divergesIff").
Run TemplateProgram (genParam indTransEnv true true "Top.squiggle5.obsEq").
Run TemplateProgram (genParam indTransEnv true true "Top.squiggle5.obseq").

