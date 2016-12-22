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

Definition dbIndexNew n := n*3+2.
Definition dbIndexOfPrime n := n*3+1.
Definition dbIndexOfRel n := n*3.

Definition nameOfPrime n := String.append n "_2".
Definition nameOfRel n := String.append n "_R".

Require Import Program.
Open Scope program_scope.

Require Import Coq.Init.Nat.

(* can be Prop for set *)
Definition translateSort (s:sort) : sort := s.
Definition mkTyRel (T1 T2 sort: term) :=
  T1 ↪ T2 ↪ sort.
Definition projTyRel (T: term) := T.


Fixpoint translate (t:term) : term :=
match t with
| tRel n => tRel (dbIndexOfRel n)
| tSort s => 
      mkLamL 
        [(nAnon (* Coq picks some name like H *), t);
         (nAnon, t)]
         (mkTyRel (tRel 1)  (tRel 1) (tSort (translateSort s)))
| tLambda nm typ bd =>
  let A := mapDbIndices dbIndexNew typ in
  let A' := mapDbIndices (S ∘ dbIndexOfPrime) typ in
  let A_R := tApp (mapDbIndices (add 2) (projTyRel (translate typ))) [tRel 1; tRel 0] in
  mkLamL [(nm, A);
            (nameMap nameOfPrime nm, A');
            (nameMap nameOfRel nm, A_R)]
         ((translate bd))
| _ => t
end.

Import MonadNotation.
Open Scope monad_scope.

Definition genParam (id: ident) : TemplateMonad unit :=
  id_s <- tmQuote id true;;
(*  _ <- tmPrint id_s;; *)
  match id_s with
  Some (inl t) => 
    let t_R := (translate t) in
    tmPrint t_R;;
    (@tmMkDefinition true (String.append id "_RR")  term t_R)
    (* tmPrint (translate t) *)
  | _ => ret tt
  end.

(* Move *)
Definition printTerm (name  : ident): TemplateMonad unit :=
  (tmBind (tmQuote name true) tmPrint).

Definition ids : forall A : Set, A -> A := fun (A : Set) (x : A) => x.

Ltac cexact ids := 
(let T := eval compute in ids in exact T).

Run TemplateProgram (genParam "ids").

Declare ML Module "paramcoq".

Parametricity Recursive ids.

Check (eq_refl : ids_RR=ids_R).

Run TemplateProgram (printTerm "ids").

Require Import Trecord.
Import TyRel.
Require Import common.
Print ids_R.

Definition allProps : list Props := [Total; OneToOne ; Irrel].

Definition ids_RN : forall (A₁ A₂ : Set) (A_R : GoodRel A₁ A₂ allProps) (x₁ : A₁) (x₂ : A₂),
       R A_R x₁ x₂ -> R A_R x₁ x₂
:= 
fun (A₁ A₂ : Set) (A_R :GoodRel A₁ A₂ allProps) (x₁ : A₁) (x₂ : A₂) 
  (x_R : R A_R x₁ x₂) => x_R.


Run TemplateProgram (printTerm "ids_RN").



