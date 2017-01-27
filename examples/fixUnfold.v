Function zero {A:Set} (p:A=A) := 0.
Print zero.

(*
zero = fun (A : Set) (_ : A = A) => 0
     : forall A : Set, A = A -> nat
 *)

Fixpoint zerof {A:Set} (p:A=A) (a:A):=
  match p with
  | eq_refl => a (* because the return type is not so constrained, this works *)
  end.
(* if there was a legitimate recursive call, the subterm must be of the same constrained type.
*)

Print zerof.

Lemma indepDestruct {A:Set} (p:A=A): zero p = zero p.
Proof using.
  intros. 
  Fail destruct p. reflexivity.
Abort.

(* would it suffice to say that our method worked on everything in the stdlib *)