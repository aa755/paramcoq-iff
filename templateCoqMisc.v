Require Import Template.Template.
Require Import Template.Ast.
Require Import Coq.Lists.List.

Fixpoint mkLamL (lt: list (name *term)) (b: term) 
  : term :=
match lt with
| nil => b
| a::tl =>  tLambda (fst a) (snd a )(mkLamL tl b)
end.


Definition mkFun  (A B: term) : term :=
  tProd nAnon A B.

(* copied from
https://coq.inria.fr/library/Coq.Unicode.Utf8_core.html#
*)
Notation "x ↪ y" := (mkFun x y)
  (at level 99, y at level 200, right associativity).

Definition nameMap (f: ident -> ident) (n:name): name :=
match n with
| nNamed s => nNamed (f s)
| nAnon => nAnon
end.

Fixpoint mapDbIndices (f:nat -> nat) (t:term) : term :=
match t with
| tRel n => tRel (f n)
| _ => (* mapDbIndices f t *) t
end.

Require Import ExtLib.Structures.Monads.

Global Instance tmMonad : Monad TemplateMonad :=
  Build_Monad _ (@tmReturn) (@tmBind).

Ltac cexact ids := 
  (let T := eval compute in ids in exact T).

Definition printTerm (name  : ident): TemplateMonad unit :=
  (tmBind (tmQuote name true) tmPrint).


