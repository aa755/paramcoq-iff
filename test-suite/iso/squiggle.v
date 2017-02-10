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

Inductive existp (A : Set) (P : A -> Prop) : Prop :=
  exist : forall x : A, P x -> existp A P.
  
Lemma PiGoodPropAux :
  forall (A1 A2 :Set) (A_R:  @GoodRel [Total] A1 A2) 
  (B1: A1 -> Prop) 
  (B2: A2 -> Prop) 
  (B_R: forall a1 a2, @R _ _ _ A_R a1 a2 ->  @GoodRel [Total] (B1 a1) (B2 a2)),
  BestRel (existp _ B1) (existp _ B2).
Admitted.

Inductive option (A : Set) : Set :=  Some : A -> option A | None : option A.
Inductive sum (A B : Set) : Set :=  inl : A -> sum A B | inr : B -> sum A B.
Inductive list (A : Set) : Set :=  nil : list A | cons : A -> list A -> list A.
Print prod.
Inductive prod (A B : Set) : Set :=  pair : A -> B -> prod A B.

Arguments Some {A} _.
Arguments None {A}.

Arguments inl {A} {B} _.
Arguments inr {A} {B} _.

Arguments nil {A}.
Arguments cons {A} _ _.

Arguments pair {A} {B} _ _.

Notation " ( x , y ) " := (pair x y).
(*
Notation "[ ]" := nil (format "[ ]") : list_scope.
*)
Notation "[ x ]" := (cons x nil) : list_scope.
Notation "[ x , y , .. , z ]" := (cons x (cons y .. (cons z nil) ..)) : list_scope.

Definition isNone {A:Set} (oa: option A) :=
  match oa with
  | Some _ => false
  | None => true
  end.
Infix "+" := sum:type_scope.
(*
Definition beq (b1 b2 : bool) := eqs bool b1 b2.
Infix "≡" := beq (at level 80).
 *)
Section Squiggle.
  (* Variable V:Set. This interface is too abstract for exposing V *)
  Variable Tm:Set.
  Variable BTm:Set.
  Variable mkTerm : Op -> list (Tm + BTm) -> option Tm.
  Variable elimTerm : Tm -> option (prod Op (list (Tm+BTm))).
  Variable applyBtm: BTm -> Tm -> Tm.

Fixpoint evaln (n:nat) (t:Tm): option Tm :=
match n with
|0%nat => None
| S n =>
  match (elimTerm t)
  with
  | Some (lam, _)
  | Some (num _, _) => Some t
  | Some (app, [inl f, inl a]) =>
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

Open Scope nat_scope.
Fixpoint sqlek (k:nat) (tl tr:Tm): Prop :=
  forall (nl:nat), 
    match (evaln nl tl) with
    | None => eqs _ 0 0
    | Some vl => existp _ (fun (nr:nat) =>
        match (evaln nl tl) with
        | None => eqs _ 0 1
        | Some vr =>
          match elimTerm vl, elimTerm vr with
          | Some (num nl, _), Some (num nr,_) => eqs _ nl nr
          | Some (lam,[inr btl]), Some (lam,[inr btr]) =>
            match k with
            | 0 => eqs _ 0 1
            | S k =>
              forall (ta: Tm), sqlek k (applyBtm btl ta) (applyBtm btr ta)
            end
          | _ , _=> eqs _ 0 1
          end
        end
                         )
    end.
  (*
  match (elimTerm tl), (elimTerm tr) with
  | (num n1, _), (num n2,_) => eqs _ n1 n2
  | (lam [inr ])
*)  



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
    match evaln nsteps tl, evaln nsteps tr with
    | Some vl, Some vr => 
          match elimTerm vl, elimTerm vr with
          | Some (num nl, _), Some (num nr,_) => eqs _ nl nr
          | Some (lam,[inr btl]), Some (lam,[inr btr]) =>
            match k with
            | 0 => eqs _ 0 1
            | S k =>
              forall (ta: Tm), obsEq k (applyBtm btl ta) (applyBtm btr ta)
            end
          | _ , _=> eqs _ 0 1
          end
    | _, _  => eqs _ 0 0
    end.

End Squiggle.

Print obsEq.

Print option.
Run TemplateProgram (genParamIndAll [] "Coq.Init.Datatypes.bool").
Run TemplateProgram (genParamIndAll [] "Top.squiggle.eqs").
Run TemplateProgram (genParamIndAll [] "Coq.Init.Datatypes.nat").
Run TemplateProgram (genParamIndAll [] "Top.squiggle.option").
Run TemplateProgram (genParamIndAll [] "Top.squiggle.sum").
Run TemplateProgram (genParamIndAll [] "Top.squiggle.list").
Run TemplateProgram (genParamIndAll [] "Top.squiggle.prod").
(* and, unlike exists, allows singleton elim because the 2 args of its constructor
are proofs *)
Run TemplateProgram (genParamIndAll [] "Coq.Init.Logic.and").
Run TemplateProgram (genParamIndAll [] "Top.squiggle.Op").


Run TemplateProgram (mkIndEnv "indTransEnv" [
"Coq.Init.Datatypes.bool" ; "Coq.Init.Datatypes.nat";
"Coq.Init.Logic.and"; "Top.squiggle.eqs"; 
 "Top.squiggle.option"; "Top.squiggle.sum"; "Top.squiggle.Op";
  "Top.squiggle.list"; "Top.squiggle.prod"]).

Run TemplateProgram (genWrappers indTransEnv).

Run TemplateProgram (genParam indTransEnv true true "Top.squiggle.evaln").
(* slow and the result is bloated *)

Run TemplateProgram (genParam indTransEnv true true "Top.squiggle.isNone").

Run TemplateProgram (genParam indTransEnv true true "Coq.Init.Logic.iff").

Run TemplateProgram (genParam indTransEnv true true "Top.squiggle.divergesIff").
(* quick *)
Run TemplateProgram (genParam indTransEnv true true "Top.squiggle.obsEq").
(* bloated *)