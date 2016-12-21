Require Import Coq.Classes.DecidableClass.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import SquiggleEq.export.
Require Import SquiggleEq.UsefulTypes.
Require Import SquiggleEq.list.
Require Import SquiggleEq.LibTactics.
Require Import SquiggleEq.tactics.
Require Import SquiggleEq.AssociationList.
Require Import ExtLib.Structures.Monads.
Require Import templateCoqMisc.
Require Import Template.Template.
Require Import Template.Ast.

(* DB binders can have same names *)
Let newL := (mkLamL [(nNamed "a1",(tInd (mkInd "Coq.Init.Datatypes.nat" 0)));
(nAnon ,(tInd (mkInd "Coq.Init.Datatypes.nat" 0)))] (tRel 0)).

Run TemplateProgram (tmMkDefinition true ("idd") newL).
Print idd.


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


(* can be Prop for set *)
Definition translateSort (s:sort) : sort := s.

Fixpoint translate (t:term) : term :=
match t with
| tRel n => tRel (dbIndexOfRel n)
| tSort s => 
      mkLamL 
        [(nAnon (* Coq picks some name like H *), t);
         (nAnon, t)]
         ((tRel 1) ↪ (tRel 1) ↪ (tSort (translateSort s)))
| tLambda nm typ bd =>
  let A := mapDbIndices dbIndexNew typ in
  let A' := mapDbIndices dbIndexOfPrime typ in
  let A_R := tApp (translate typ) [tRel 1; tRel 0] in
  mkLamL [(nm, A);
            (nameMap nameOfPrime nm, A');
            (nameMap nameOfRel nm, A_R)]
         (translate bd)
| _ => t
end.

Import MonadNotation.
Open Scope monad_scope.

Definition genParam (id: ident) : TemplateMonad unit :=
  id_s <- tmQuote id false;;
(*  _ <- tmPrint id_s;; *)
  match id_s with
  Some (inl t) => 
    (@tmMkDefinition false (nameOfRel id)  _ (translate t))
    (* tmPrint (translate t) *)
  | _ => ret tt
  end.

(* Move *)
Definition printTerm (name  : ident): TemplateMonad unit :=
  (tmBind (tmQuote name true) tmPrint).

Definition ids : forall A : Set, A -> A := fun (A : Set) (x : A) => x.

Ltac cexact ids := 
(let T := eval compute in ids in exact T).


Quote Definition idss := ltac:(cexact ids).

Print idss.

Declare ML Module "paramcoq".


Parametricity Recursive ids.

Run TemplateProgram (printTerm "ids_R").
Eval compute in (translate idss).

(Some
   (inl
      (tLambda (nNamed "A₁") (tSort sSet)
         (tLambda (nNamed "A₂") (tSort sSet)
            (tLambda (nNamed "A_R")
               (tProd nAnon (tRel 1) (tProd nAnon (tRel 1) (tSort sSet)))
               (tLambda (nNamed "x₁") (tRel 2)
                  (tLambda (nNamed "x₂") (tRel 2)
                     (tLambda (nNamed "x_R") (tApp (tRel 2) [tRel 1; tRel 0]) (tRel 0)))))))))

Quote Recur

Print idss.

Make Definition ddd := ltac:(cexact (translate idss)).
Print ddd.

Run TemplateProgram (printTerm "ids").

Run TemplateProgram (genParam "ids").




