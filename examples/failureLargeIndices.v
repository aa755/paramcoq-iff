
(* Monad nat : Set. But we may not be able to generate totality (let alone goodness)
for it. The current totality proof needs irrel for indices.
Can we get rid of that usage?
Clearly this Monad cannot be encoded as an IWTS because there the index type I had type set.
but Set does not have type Set *)
Inductive  Monad : forall (A:Set) , Set :=
  ret : Monad nat.

(*
Inductive  MonadLarge : forall (A:Set) , Set :=
  retl : forall A:Set, MonadLarge (list A).
Error: Large non-propositional inductive types must be in Type.
 *)

(* MonadLarge nat is in type Type. So we don't need to generate any goodness.
  Also, for now, it is not a part of the language of interest, because it mentions Type *)
Inductive  MonadLarge : forall (A:Set) , Type :=
  retl : forall A:Set, MonadLarge (list A).
