
(* Can use this once the completeness for inductive props is done
Inductive isEven : nat -> Prop :=
| ev0 : isEven 0
| evSS : forall n, isEven n -> isEven (S (S n)).

Lemma isEvenTwice (n:nat) : isEven (2*n).
  simpl.
  rewrite <- plus_n_O.
  induction n; try constructor.
  simpl.
  rewrite <- plus_n_Sm.
  constructor; assumption.
Qed.
*)

Inductive eqs {A : Set} (x : A) : forall (a:A), Prop :=  
  eq_refls : eqs x x.

Infix "=" := eqs : type_scope.

Section NatAbs.
(* if we make a record, the record lives in a higher universe. Not a problem
because we don't need goodness for the record, we just need it for the fields
However, it is currently a problem because TemplateCoq doesn't work for universes. *)

Variable  Nat : Set.
Variable  NO : Nat.
Variable  NS : Nat -> Nat.
Variable  Nadd : Nat -> Nat -> Nat.

Definition addComm : Prop := forall (n1 n2: Nat), Nadd n1 n2 = Nadd n2 n1.
End NatAbs.

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

Require Import ReflParam.Trecord.

Run TemplateProgram (genParamIndAll [] "Top.natAbs.eqs").

(*
Run TemplateProgram (mkIndEnv "indTransEnv" [
 "Top.natAbs.eqs" ]).
*)
Run TemplateProgram (genParam [] true true "Top.natAbs.addComm"). (* quick*)

Goal False.
let T:= type of Top_natAbs_addComm_pmtcty_RR in 
let T := eval simpl in T in
idtac T.
(*
(forall (Nat Nat₂ : Set) (Nat_R : BestRel Nat Nat₂) (Nadd : Nat -> Nat -> Nat)
   (Nadd₂ : Nat₂ -> Nat₂ -> Nat₂),
 (forall (a1 : Nat) (a2 : Nat₂),
  BestR Nat_R a1 a2 ->
  forall (a3 : Nat) (a4 : Nat₂), BestR Nat_R a3 a4 -> BestR Nat_R (Nadd a1 a3) (Nadd₂ a2 a4)) ->
 BestRel (forall a n2 : Nat, Nadd a n2 = Nadd n2 a)
   (forall a n2₂ : Nat₂, Nadd₂ a n2₂ = Nadd₂ n2₂ a))
*)
Abort.
