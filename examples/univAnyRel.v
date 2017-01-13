Require Import Coq.Unicode.Utf8.

Universe i.
Universe j.

(* relations for Type{i} cannot be in Prop because it fails Type{i}:Type{i}*)
Fail Check ( (λ(x x': Type@{i}), x → x' → Prop) 
  : ((λ(x x': Type@{j}), x → x' → Prop)  Type@{i}  Type@{i})).
(* on simplifying the above line: *)
Fail Check ((λ(x x': Type@{i}), x → x' → Prop) : Type@{i} → Type@{i} → Prop).


(* specialization of the above for Type{i} := [Set] *)
Fail Check ((Set → Set  → Prop) : Type@{i} → Type@{i} → Prop).


(* forall i, relations for Type{i} cannot be in Type@{i}*)
Check ((λ(x x': Type@{i}), x → x' → Type@{i}) : Type@{i} → Type@{i} → Type@{j}).
(** Set Printing All.
       i < j
        *)



(* what does this represent? *)
Fail Check ((Type@{i} -> Type@{i} -> Prop) : Type@{i}).
Check ((Type@{i} -> Type@{i} -> Prop) : Type@{j}).

(** Set Printing All.
      |= Set < j
       i < j
        *)

Check (Type -> Type -> False : Prop).
Fail Check (Set -> Set -> Prop : Prop).
Fail Check (Type -> Type -> Prop : Prop).
Fail Check (Prop -> Prop -> Prop : Prop).


(**
All 3 give the same Error:
The term "Prop" has type "Type" while it is expected to have type
"Prop" (universe inconsistency).
*)

(* [Set] can live in [Prop]. This is then the translation for Set:Type{i} *)
Check ( (λ(x x': Set), x → x' → Prop) 
  : ((λ(x x': Type@{i}), x → x' → Type@{i})  Set Set)).

Check ( (λ(x x': Set), x → x' → Prop) 
        : (Set → Set → Type@{i})).

(** * Subtyping 

We know that Set :> Type. Does the parametricity translation need to preserve this?
Let A:Set
Let's check whetner [[Set]] A A:> [[Type]] A A.
*)

Section SubtypTest.
  Variable A:Set.
  Variable v : (λ(x x': Set), x → x' → Prop) A A.
  Check (v: ((λ(x x': Type@{i}), x → x' → Type@{i}) A A)).
End SubtypTest.





