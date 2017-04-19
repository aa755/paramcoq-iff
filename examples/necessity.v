
Definition left_identity {S T : Type} (f: S -> T) (g: T-> S): Prop :=
  forall s: S , (g (f s)) = s.

(** isomorphism w.r.t. the structure (T,=) *)
Definition isomorphic (A B : Set) : Prop :=
  ex (fun f: A->B => ex (fun g: B->A =>  left_identity f g /\ left_identity g f)).

Section Necessity.
  Variables (A1 A2 : Set).
(** Suppose that there is a tool T than can, for ANY closed [P] of type [Set -> Prop], 
produce a proof of [P A1 <-> P A2]. 
In the style of reverse mathematics (https://en.wikipedia.org/wiki/Reverse_mathematics), 
to prove that the assumption of isomorphism was necessary for the tool,
we assume that the tool always succeeds, and prove [isomorphic A1 A2].

We instantiate the tool T for [P:= (isomorphic A1)] to get a proof of 
[isomorphic A1 A1 <-> isomorphic A1 A2], which implies [isomorphic A1 A2].
Qed.
 *)
  Check ((isomorphic A1) : Set -> Prop).
End Necessity.