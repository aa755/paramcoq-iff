Inductive Vec (A:Set) : forall n1 n2:nat, Set :=
nil : Vec A 0 0.

Check Vec.
(*
Vec
     : Set -> nat -> nat -> Set
     
When we have cons, we will obviously need A_R.
We want to get rid of n1 and n2?
Why is that justified?
In the type of Vec, there is absolutely no difference between parameters and indices --
we can write another Vec of the same type where all of them are params or all
of them are indices.
Perhaps the principle is the difference between Sort and Type in the domain of Pi Type.
If so, we will not want to erase the indices_R of the following
*)

Inductive Monad  : Type -> Type :=
ret : forall T, Monad T.

(*
If we cannot erase the index here, we will be forced to keep the equalities
and implement the hard things anyway. So there is no advantage of trying
to enforce irrelevance over small type domains in function types, because
that seems ugly to implement, as discussed in this file
*)


