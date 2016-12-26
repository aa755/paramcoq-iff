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
(*
Definition mkTyRel (T1 T2 sort: term) : term :=
  T1 ↪ T2 ↪ sort.
Definition projTyRel (T1 T2 T_R: term) : term := T_R.
*)

Definition mkTyRel (T1 T2 sort: term) : term :=
tApp 
  (tConst "ReflParam.Trecord.BestRel") 
  [T1; T2].

Definition projTyRel (T1 T2 T_R: term) : term := 
tApp (tConst "ReflParam.Trecord.BestR")
 [T1; T2; T_R].

Definition hasSortSetOrProp (t:term) : bool :=
(* Fix: need to use definitional equality *)
match t with
| tCast _  _ (tSort sSet) => true
| tCast _  _ (tSort sProp) => true
| _ => false
end.

Definition removeHeadCast (t:term) : term :=
(* Fix: need to use definitional equality *)
match t with
| tCast t  _ (tSort _) => t
| _ => t
end.

Definition ids : forall A : Set, A -> A := fun (A : Set) (x : A) => x.
Definition idsT  := forall A : Set, A -> A.

Run TemplateProgram (printTerm "ids").
Run TemplateProgram (printTerm "idsT").

(* collect the places where the extra type info is needed, and add those annotations
beforehand.
Alternatively, keep trying in order: Prop -> Set -> Type*)

Fixpoint translate (t:term) : term :=
match t with
| tRel n => tRel (dbIndexOfRel n)
| tSort s => 
      mkLamL 
        [(nAnon (* Coq picks some name like H *), t);
         (nAnon, t)]
         (mkTyRel (tRel 1)  (tRel 0) (tSort (translateSort s)))
| tProd nm A B =>
  let A1 := mapDbIndices dbIndexNew (removeHeadCast A) in
  let A2 := mapDbIndices (S ∘dbIndexOfPrime) (removeHeadCast A) in
  let B1 := mapDbIndices dbIndexNew (removeHeadCast B) in
  let B2 := mapDbIndices (S ∘ dbIndexOfPrime) (removeHeadCast B) in
  let f := if (hasSortSetOrProp A) (* if A has type Type but not Set or Prop *)
      then (fun t =>
      projTyRel (mapDbIndices (add 2) A) (mapDbIndices (add 1) A2) (mapDbIndices (add 2) t))
      else id in
  let A_R := tApp (mapDbIndices (add 2) (f (translate A))) [tRel 1; tRel 0] in
  mkLamL [(nm, A);
            (nameMap nameOfPrime nm, A2);
            (nameMap nameOfRel nm, A_R)]
         ((translate B))
| tLambda nm A b =>
  let A1 := mapDbIndices dbIndexNew (removeHeadCast A) in
  let A2 := mapDbIndices (S ∘ dbIndexOfPrime) (removeHeadCast A) in
  let f := if (hasSortSetOrProp A) then 
           (fun t =>
      projTyRel (mapDbIndices (add 2) A1) (mapDbIndices (add 1) A2) (mapDbIndices (add 2) t))
      else id in
  let A_R := tApp (mapDbIndices (add 2) (f (translate A))) [tRel 1; tRel 0] in
  mkLamL [(nm, A1);
            (nameMap nameOfPrime nm, A2);
            (nameMap nameOfRel nm, A_R)]
         ((translate b))
| tCast tc _ _ => translate tc
| _ =>  t
end.

Import MonadNotation.
Open Scope monad_scope.

Definition genParam (b:bool) (id: ident) : TemplateMonad unit :=
  id_s <- tmQuote id true;;
(*  _ <- tmPrint id_s;; *)
  match id_s with
  Some (inl t) => 
    let t_R := (translate t) in
    trr <- tmReduce Ast.all t_R;;
    tmPrint trr  ;;
     if b then (@tmMkDefinition true (String.append id "_RR")  term t_R) else (tmReturn tt)
  | _ => ret tt
  end.



Declare ML Module "paramcoq".

Parametricity Recursive ids.


Run TemplateProgram (printTerm "ids").

Require Import Trecord.
Require Import common.
Print ids_R.




Definition ids_RN : forall (A₁ A₂ : Set) (A_R : BestRel A₁ A₂ ) (x₁ : A₁) (x₂ : A₂),
       R A_R x₁ x₂ -> R A_R x₁ x₂
:= 
fun (A₁ A₂ : Set) (A_R :BestRel A₁ A₂) (x₁ : A₁) (x₂ : A₂) 
  (x_R : BestR A_R x₁ x₂) => x_R.

Run TemplateProgram (printTerm "ids").

Run TemplateProgram (printTerm "ids_RN").

(*
(Some
   (inl
      (tLambda (nNamed "A₁") (tSort sSet)
         (tLambda (nNamed "A₂") (tSort sSet)
            (tLambda (nNamed "A_R")
               (tApp (tConst "ReflParam.Trecord.BestRel") [tRel 1; tRel 0])
               (tLambda (nNamed "x₁") (tRel 2)
                  (tLambda (nNamed "x₂") (tRel 2)
                     (tLambda (nNamed "x_R")
                        (tApp (tConst "ReflParam.Trecord.BestR")
                           [tRel 4; tRel 3; tRel 2; tRel 1; tRel 0]) 
                        (tRel 0)))))))))

*)

Definition idT := fun (A : Set) => A.

Run TemplateProgram (genParam true "ids").
Check (eq_refl : ids_RR=ids_RN).
Eval compute in ids_RR.


Definition s := Set.
Run TemplateProgram (genParam true "s").

Print s_RR.
Definition s_RRT := fun H H0 : Type => BestRel H H0.
Eval compute in (s_RRT Set Set).


SearchAbout (nat->Type).

(*
The type of forall also depends on the type of B

Variable A:Type.
Variable B:A->Set.
Check (forall a:A, B a):Type.
Fail Check (forall a:A, B a):Set.

*)


Quote Definition nt := (nat:Type).
Check nat->Type.

Print nt.
