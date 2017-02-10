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
Open Scope string_scope.

Require Import ReflParam.Trecord.

(*

Inductive sigs (A : Set) (P : A -> Prop) : Set :=
 existss : forall x : A, P x -> sigs A P.
 *)
Inductive Op : Set :=
 | lam
 | app 
 | num (n : nat)
(* | primRec 
  
  Variable primRec: Tm (* num*) ->Tm (* base case*) ->Tm (* rec case *) -> Tm.
 *)
.

Set Imlicit Arguments.

Inductive eqs (A : Set) (x : A) : forall (a:A), Prop :=  
eq_refls : eqs A x x.

(*
Definition beq (b1 b2 : bool) := eqs bool b1 b2.
Infix "≡" := beq (at level 80).
 *)
Section Squiggle.
  (* Variable V:Set. This interface is too abstract for exposing V *)
  Variable Tm:Set.
  Variable BTm:Set.
  Variable mkTerm : Op -> list (Tm + BTm) -> option Tm.
  Variable elimTerm : Tm -> option (Op* list (Tm+BTm)).
  Variable applyBtm: BTm -> Tm -> Tm.

Fixpoint evaln (n:nat) (t:Tm): option Tm :=
match n with
|0%nat => None
| S n =>
  match (elimTerm t)
  with
  | Some (lam, _)
  | Some (num _, _) => Some t
  | Some (app, [inl f; inl a]) =>
    match evaln n f, evaln n a with
    | Some f, Some a =>
      match (elimTerm f) with
      | Some (lam, [inr bt]) =>
        Some (applyBtm bt a)
      | _ => None
      end
    | _,_ => None
    end        
  | _ => None                    
  end
end.

(*
Fixpoint preOrd (n:nat) (t:Tm): option Tm :=
*)  

End Squiggle.
