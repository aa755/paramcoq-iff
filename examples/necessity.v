
Definition left_identity {S T : Type} (f: S -> T) (g: T-> S): Prop :=
  forall s: S , (g (f s)) = s.

(** isomorphism w.r.t. the structure (T,=). Also, see isomorphic.v in the same directory for
  a characterization in terms of Total and OneToOne. *)
Definition isomorphic (A B : Set) : Prop :=
  ex (fun f: A->B => ex (fun g: B->A =>  left_identity f g /\ left_identity g f)).

Section Necessity.
  Variables (A1 A2 : Set).
(** Suppose that there is a tool T than can, for ANY [P] of type [Set -> Prop], 
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

Section FineGrainedNecessity.

(** 
It makes sense to take a more closer look at the assumptions made for specific
propositional constructs in Coq and ask whether those were necessary.
For example, we for indexed inductive propositions to behave uniformly, we assume
that the relation for the index types is one to one.
Was this assumption necessary?
We show that it is necessary at least for the equality types, which are indexed inductive types:
 *)

  Print Coq.Init.Logic.eq.
  (** Inductive eq (A : Type) (x : A) : A (* index *) -> Prop :=  
      eq_refl : x = x 
   *)


  (* = is a notation for the above proposition *)
  Locate "=".
  
  (**
 For eq to behave uniformly, we must prove the following: 
*)
  Lemma eqUnif (A1 A2:Set) (AR : A1 -> A2 -> Prop) (* some assumption about AR *)
        (l1: A1) (l2: A2) (lR : AR l1 l2)
        (r1: A1) (r2: A2) (rR : AR r1 r2) :
    (l1 =  r1) <-> (l2 = r2).
  Abort.

(** 
The above is precisely the definition of one to one!  
In fact, we obtained our definition of one to one by just 
extracting what we had to prove for the uniformity of the equality type. 

What is surprising is that it sufficies even for other indexed inductive 
types and propositions, and that we can compositionally build the proof 
of one-to-one-ness (and totality) for composite types (the index type may be a composite type).
 *)

  Require Import Coq.Unicode.Utf8.

(** our current definition of one to one is slightly different but logically equivalent. *)
Definition OneToOne {A B : Set} (R : A → B → Prop) : Prop := (∀ (a:A) (b1 b2: B), R a b1 → R a b2 → b1=b2) ∧ (∀ (b:B) (a1 a2: A), R a1 b → R a2 b → a1=a2).

(** The above is logically equivalent to: *)

Lemma oneToOneOld {A B : Set} (R : A -> B -> Prop):
(forall a1 a2 b1 b2,
  R a1 b1
  -> R a2 b2
  -> (a1=a2 <-> b1=b2))
<-> OneToOne R.
Proof using.
  unfold OneToOne.
  firstorder; subst; eauto;
  eapply H; eauto.
Qed.

End FineGrainedNecessity.