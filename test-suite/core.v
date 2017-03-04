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

Definition appTest  := fun (A : Set) (B: forall A, Set) (f: (forall a:A, B a)) (a:A)=>
 f a.

Let mode := true.


Definition ids : forall A : Set, A -> A := fun (A : Set) (x : A) => x.
Definition idsT  := forall A : Set, A -> A.



Run TemplateProgram (genParam [] mode true "appTest").
Eval compute in appTest_RR.

Run TemplateProgram (genParam [] mode true "idsT").
Eval compute in idsT_RR.

Print idsT.

Parametricity idsT.

(* Given f: some Pi Type, prove that the new theorem implies the old *)
Eval vm_compute in idsT_RR.


Run TemplateProgram (genParam [] mode true "ids").
Eval compute in ids_RR.

Definition idsTT  := fun A : Set => forall a:A, A.

Parametricity Recursive idsTT.

Run TemplateProgram (genParam [] mode true "idsTT").
Eval compute in idsTT_RR.

Print idsTT_RR.

Definition s := Set.
Run TemplateProgram (genParam [] mode  true "s").

Eval compute in s_RR.

Definition propIff : Type := forall A:Set, Prop.

Run TemplateProgram (genParam [] mode true "propIff").

Eval compute in propIff_RR.

Definition propIff2 : Prop := forall A:Prop, A.

Run TemplateProgram (genParam [] mode  true "propIff2").

Run TemplateProgram (printTerm "propIff2").

Eval compute in propIff2_RR.

Goal propIff2_RR = fun _ _ => True.
unfold propIff2_RR.
Print PiTSummary.
unfold PiATypeBSet. simpl.
Print PiATypeBSet.
Abort.

Definition p := Prop.
Run TemplateProgram (genParam [] mode  true "p").

Eval compute in p_RR.
