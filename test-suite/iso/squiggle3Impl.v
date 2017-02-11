Require Import ReflParam.common.
Require Import ReflParam.templateCoqMisc.
Require Import String.
Require Import List.
Require Import Template.Ast.
Require Import SquiggleEq.terms.
Require Import ReflParam.paramDirect.
Require Import SquiggleEq.substitution.
Require Import ReflParam.PiTypeR.
Import ListNotations.
Require Import squiggle2.
Open Scope string_scope.

Require Import ReflParam.Trecord.

Inductive Opid : Set :=
| lam
| app
| num (n:nat).

Open Scope nat_scope.

Definition opBindingsLam (o: Opid) : list nat :=
  match o with
  | lam => [1]
  | app => [0;0]
  | num _ => []
  end.

Global Instance sigOpid : GenericTermSig Opid :=
  Build_GenericTermSig _ opBindingsLam.

Require Import SquiggleEq.terms2.
Require Import SquiggleEq.varImplZ.
Require Import SquiggleEq.wftermSet.

Definition Tm : Set := (@WTermSet BinNums.positive Opid _ + @WBTermSet BinNums.positive Opid _).
