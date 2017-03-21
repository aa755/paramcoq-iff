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
Open Scope string_scope.

Print sig.

Inductive sigs (A : Set) (P : A -> Prop) : Prop :=
 existss : forall (x : A) (p:P x), sigs A P.

Require Import ReflParam.indProp.
Run TemplateProgram (genParamIndProp [] true "Top.exists.sigs").

Print Top_exists_sigs_pmtcty_RR0.

Print sigs_ind.

Definition sigs_inds := 
fun (A : Set) (P : A -> Prop) (P0 : Prop) (f : forall x : A, P x -> P0) (s : sigs A P) =>
match s with
| existss _ _ x x0 => f x x0
end.

Run TemplateProgram (mkIndEnv "indTransEnv" ["Top.exists.sigs"]).

Run TemplateProgram (genParam indTransEnv false true "Top.exists.sigs_inds").
