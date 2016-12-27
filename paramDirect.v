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

Require Import NArith.
Require Import Trecord.
Require Import common.

Let V:Type := (N*name).


Open Scope N_scope.

Let vprime (v:V) : V := (1+(fst v), nameMap (fun x => String.append x "₂") (snd v)).
Let vrel (v:V) : V := (2+(fst v), nameMap (fun x => String.append x "_R") (snd v)).

Notation mkLam x A b :=
  (oterm CLambda [bterm [] A; bterm [x] b]).

Notation mkPi x A b :=
  (oterm CProd [bterm [] A; bterm [x] b]).

(* because of length, this cannot be used as a pattern *)
Definition mkApp (f: STerm) (args: list STerm) : STerm :=
  oterm (CApply (length args)) ((bterm [] f)::(map (bterm []) args)).

Notation mkConst s:=
  (oterm (CConst s) []).

Notation mkSort s  :=
  (oterm (CSort s) []).

Notation mkCast t ck typ :=
  (oterm (CCast ck) [bterm [] t; bterm [] typ]).


Definition mkTyRel (T1 T2 sort: STerm) : STerm :=
mkApp 
  (mkConst "ReflParam.Trecord.BestRel") 
  [T1; T2].

Definition projTyRel (T1 T2 T_R: STerm) : STerm := 
mkApp (mkConst "ReflParam.Trecord.BestR")
 [T1; T2; T_R].

Definition hasSortSetOrProp (t:STerm) : bool :=
match t with
| mkCast t _ (mkSort sSet) => true
| mkCast t _ (mkSort sProp) => true
| _ => false
end.

Definition removeHeadCast (t:STerm) : STerm :=
match t with
| mkCast t  _ (mkSort _) => t
| _ => t
end.

Definition ids : forall A : Set, A -> A := fun (A : Set) (x : A) => x.
Definition idsT  := forall A : Set, A -> A.

Run TemplateProgram (printTerm "ids").
Run TemplateProgram (printTerm "idsT").

Fixpoint mkLamL (lb: list (V*STerm)) (b: STerm) 
  : STerm :=
match lb with
| nil => b
| a::tl =>  mkLam (fst a) (snd a )(mkLamL tl b)
end.

Fixpoint mkPiL (lb: list (V*STerm)) (b: STerm) 
  : STerm :=
match lb with
| nil => b
| a::tl =>  mkPi (fst a) (snd a )(mkPiL tl b)
end.

Require Import PiTypeR.

Definition mkPiR (A1 A2 A_R B1 B2 B_R : STerm) : STerm := 
mkApp (mkConst "ReflParam.PiTypeR.PiTSummary")
  [A1;A2;A_R;B1;B2;B_R].

(* can be used only find binding an mkPi whose body has NO free variables at all,
e.g. Set *)

(* Definition dummyVar : V := (0, nAnon). *)
(* collect the places where the extra type info is needed, and add those annotations
beforehand.
Alternatively, keep trying in order: Prop -> Set -> Type*)

Definition transLam translate nm A b :=
  let A1 := (removeHeadCast A) in
  let A2 := tvmap vprime A1 in
  let f := if (hasSortSetOrProp A) then 
           (fun t => projTyRel A1 A2 t)
      else id in
  mkLamL [(nm, A1);
            (vprime nm, A2);
            (vrel nm, mkApp (f (translate A)) [vterm nm; vterm (vprime nm)])]
         ((translate b)).

Universe j.
(* Move *)
Polymorphic Definition PiTHigher
  (A1 A2 :Type) (A_R: A1 -> A2 -> Type) 
  (B1: A1 -> Type) 
  (B2: A2 -> Type)
  (B_R: forall a1 a2,  A_R a1 a2 ->  (B1 a1) -> (B2 a2) -> Type)
  := (R_Pi B_R).

Eval compute in PiTHigher.

Definition mkPiRHigher (A1 A2 A_R B1 B2 B_R : STerm) : STerm := 
mkApp (mkConst "PiTHigher")
 [A1;A2;A_R;B1;B2;B_R].

Eval compute in PiTHigher.

Let PiTHigher2
  (A1 A2 :Type) (A_R: A1 -> A2 -> Type) 
  (B1: A1 -> Type) 
  (B2: A2 -> Type)
  (B_R: forall a1 a2,  A_R a1 a2 ->  (B1 a1) -> (B2 a2) -> Type)
  := (fun (f1 : forall a : A1, B1 a) (f2 : forall a : A2, B2 a) =>
forall (a1 : A1) (a2 : A2) (p : A_R a1 a2), B_R a1 a2 p (f1 a1) (f2 a2)).

Notation PiTHigher3 B_R := (R_Pi B_R).

Print R_Pi.
Let xx :=
(PiTHigher2 Set Set (fun H H0 : Set => BestRel H H0)
   (fun A : Set => (A) -> A)
   (fun A₂ : Set => (A₂) -> A₂)
   (fun (A A₂ : Set) (A_R : BestRel A A₂) =>
    BestR (PiTSummary A A₂ A_R (fun _ : A => A) (fun _ : A₂ => A₂)
      (fun (H : A) (H0 : A₂) (_ : BestR A_R H H0) => A_R)))).

(*
Definition mkPiRHigher2 (A1 A2 A_R B1 B2 B_R : STerm) : STerm := 
  mkLamL ()
*)

Fixpoint translate (t:STerm) : STerm :=
match t with
| vterm n => vterm (vrel n)
| mkSort s =>
  let v1 := (0, nAnon) in
  let v2 := (3, nAnon) in
(* because the body of the lambda is closed, no capture possibility*)
      mkLamL
        [(v1 (* Coq picks some name like H *), t);
         (v2, t)]
         (mkTyRel (vterm v1) (vterm v2) (mkSort (translateSort s)))
| mkCast tc _ _ => translate tc
| mkLam nm A b => transLam translate nm A b
| mkPi nm A B =>
  let A1 := (removeHeadCast A) in
  let A2 := tvmap vprime A1 in
  let B1 := (mkLam nm A1 (removeHeadCast B)) in
  let B2 := tvmap vprime B1 in
  let B_R := transLam translate nm (removeHeadCast A) (removeHeadCast B) in
  let Asp := (hasSortSetOrProp A) in
  let Bsp := (hasSortSetOrProp B) in
  let good := andb Bsp Asp in
  let f := if Asp
            then (fun t => projTyRel A1 A2 t)
            else id in
  if good 
    then (mkPiR A1 A2 (translate A) B1 B2 B_R)
    else (mkPiRHigher A1 A2 (f (translate A)) B1 B2 B_R)
| _ => t
end.


Import MonadNotation.
Open Scope monad_scope.

Definition genParam (b:bool) (id: ident) : TemplateMonad unit :=
  id_s <- tmQuoteSq id true;;
(*  _ <- tmPrint id_s;; *)
  match id_s with
  Some (inl t) => 
    let t_R := (translate t) in
    trr <- tmReduce Ast.all t_R;;
    tmPrint trr  ;;
    trrt <- tmReduce Ast.all (fromSqNamed t_R);;
    tmPrint trrt  ;;
     if b then (@tmMkDefinitionSq (String.append id "_RR")  t_R) else (tmReturn tt)
  | _ => ret tt
  end.

(*
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
*)





Declare ML Module "paramcoq".

Parametricity Recursive ids.


Run TemplateProgram (printTerm "ids").




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

Run TemplateProgram (printTerm "idsT").

Definition idT := fun (A : Set) => A.
Run TemplateProgram (genParam true "idsT").

Run TemplateProgram (genParam true "ids").
Check (eq_refl : ids_RR=ids_RN).
Eval compute in ids_RR.

Definition idsTT  := fun A : Set => forall a:A, A.

Run TemplateProgram (printTerm "idsTT").


Print Universes.

Notation one := 1.

Quote Definition dd := (one).
Print dd.
Run TemplateProgram (printTermSq "R_Pi").

Print R_Pi.

Run TemplateProgram (genParam true "idsT").
(*
The term "BestRel H H0" has type "Type@{max(ReflParam.common.31, i+1)}"
while it is expected to have type "Type@{j}" (universe inconsistency).
*)

Parametricity Recursive idsTT.
Print idsTT_R.
Eval compute in idsTT_RR.

Print idsTT_RR.

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
