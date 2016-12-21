Require Import Coq.Classes.DecidableClass.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import SquiggleEq.export.
Require Import SquiggleEq.UsefulTypes.
Require Import SquiggleEq.list.
Require Import SquiggleEq.LibTactics.
Require Import SquiggleEq.tactics.
Require Import SquiggleEq.AssociationList.

Require Import Template.Template.
Require Import Template.Ast.

Fixpoint mkLamL (lt: list (name *term)) (b: term) 
  : term :=
match lt with
| nil => b
| a::tl =>  tLambda (fst a) (snd a )(mkLamL tl b)
end.

(* DB binders can have same names *)
Let newL := (mkLamL [(nNamed "a1",(tInd (mkInd "Coq.Init.Datatypes.nat" 0)));
(nAnon ,(tInd (mkInd "Coq.Init.Datatypes.nat" 0)))] (tRel 0)).

Run TemplateProgram (tmMkDefinition ("idd") newL).
Print idd.

Definition mkFun  (A B: term) : term :=
  tProd nAnon A B.

(* copied from
https://coq.inria.fr/library/Coq.Unicode.Utf8_core.html#
*)
Notation "x → y" := (mkFun x y)
  (at level 99, y at level 200, right associativity).


(*

Definition mkProd {n:nat} (A B: Term n) : Term n :=
  mkSig (freshVar vOrig (free_vars B)) A B.

Fixpoint mkPiL {n:nat} (lb: list (V*Term n)) (b: Term n) 
  : Term n :=
match lb with
| nil => b
| a::tl =>  mkPi (fst a) (snd a )(mkPiL tl b)
end.

*)



Check id.

Quote Definition id_syntax := ltac:(let t:= eval compute in @id in exact t).

Definition dbIndexNew n := n*3.
Definition dbIndexOfPrime n := n*3+1.
Definition dbIndexOfRel n := n*3 + 2.

Definition nameOfPrime n := String.append n "_2".
Definition nameOfRel n := String.append n "_R".

Definition nameMap (f: ident -> ident) (n:name): name :=
match n with
| nNamed s => nNamed (f s)
| nAnon => nAnon
end.

Fixpoint mapDbIndices (f:nat -> nat) (t:term) : term :=
match t with
| tRel n => tRel (f n)
| _ => t
end.

(* can be Prop for set *)
Definition translateSort (s:sort) : sort := s.

Fixpoint translate (t:term) : term :=
match t with
| tRel n => tRel (dbIndexOfRel n)
| tSort s => 
      mkLamL 
        [(nAnon (* Coq picks some name like H *), t);
         (nAnon, t)]
         ((tRel 1) → (tRel 1)→ (tSort (translateSort s)))
| tLambda nm typ bd =>
  let A := mapDbIndices dbIndexNew typ in
  let A' := mapDbIndices dbIndexOfPrime typ in
  let A_R := tApp (translate typ) [tRel 1; tRel 1] in
  mkLamL [(nm, A);
            (nameMap nameOfPrime nm, A');
            (nameMap nameOfRel nm, A_R)]
         (translate bd)
| _ => t
end.



