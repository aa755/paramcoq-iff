Require Import Coq.Classes.DecidableClass.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import SquiggleEq.export.
Require Import SquiggleEq.UsefulTypes.
Require Import SquiggleEq.list.
Require Import SquiggleEq.LibTactics.
Require Import SquiggleEq.tactics.
Require Import SquiggleEq.AssociationList.

Section VarSort.

Variable V:Set.

Set Implicit Arguments.


Section MaxUniv.

(* max universe. 0 denotes [Set] *)
Variable n : nat.

Set Implicit Arguments.

Inductive Opid : Set :=
(* x, which is var, we get for free *)
 | pSort : forall m, (PeanoNat.Nat.leb m n = true) -> Opid
 | pLam
 | pPi
 | pSig
 | pApp
 | pProjSig : bool (* true := fst, false := snd *) -> Opid
 | pPair : bool (* true := fst, false := snd *) -> Opid
(* pNat *)
(* p0 *)
(* pS *)
(* pPrimRec *).

Definition OpBindings (c : Opid) 
    : list nat :=
  match c with
  | pSort _ _ => [0]
  | pLam => [0,1] (* contains type as well  *)
  | pPi => [0,1]
  | pSig => [0,1]
  | pProjSig _ => [0]
  | pPair _ => [0;0]
  | pApp => [0;0]
  end.


End MaxUniv.
Let Term : nat -> Set := (fun n => (@NTerm V (Opid n))).



(* We can define the semantics of Term 1, by going as TermplateCoq.Term.
Then, one would have to manually reflect it using the "Make Definition" command.
Else, we can also just pretty print as a string, and dump the contents to a .v file. *)

(*
There is no way to give semantics where t:Term i is mapped to {T:Type | T}.
Think about (oterm (pLam) (bterm [x] (vterm x))). We want it to map it to
fun x => x. Suppose V:=string. There is no way to convert the string "x" to the binder x in fun x => x.
There is not even a way to get a fresh binders. the "fresh" function is only available in Ltac.
If there were such a function in Coq, we could cook up well-typed open terms, which is impossible.

Perhaps thats why the "Make Definition" command of template-Coq is external
*)

(*
Because there is no internal semantics function, we cannot use it to reduce the typehood of codes
to the typehood of the semantics. It may be best to formalize the typehood.
*)

(* v' in the translation on paper *)
Variable vprime : V -> V.
(* v_R in the translation on paper *)
Variable vrel : V -> V.
(* later, axiomatize that the output of vprime and the outputs of vrel and the inputs to these functions
are in (3) disctinct classes *)

Definition mkLam {n:nat} (x: V) (A b: Term n) : Term n :=
  oterm (pLam _) [bterm [] A; bterm [x] b].

Definition mkPi {n:nat} (x: V) (A b: Term n) : Term n :=
  oterm (pLam _) [bterm [] A; bterm [x] b].

Definition mkSig {n:nat} (x: V) (A b: Term n) : Term n :=
  oterm (pSig _) [bterm [] A; bterm [x] b].

Definition mkApp {n:nat}  (A B: Term n) : Term n :=
  oterm (pApp _) [bterm [] A; bterm [] B].

(* use fold_left. *)
Fixpoint mkAppL {n:nat}  (f : Term n) (args : list (Term n)) : Term n :=
match args with
| nil => f
| a::tl => mkAppL (mkApp f a) tl
end.

Inductive VClass := vOrig | vPrim | vRel.

Context `{VarType V VClass}.

(* Move to Squiggle *)


Definition mkFun {n:nat} (A B: Term n) : Term n :=
  mkPi (freshVar vOrig (free_vars B)) A B.

Definition mkProd {n:nat} (A B: Term n) : Term n :=
  mkSig (freshVar vOrig (free_vars B)) A B.

Fixpoint mkLamL {n:nat} (lb: list (V*Term n)) (b: Term n) 
  : Term n :=
match lb with
| nil => b
| a::tl =>  mkLam (fst a) (snd a )(mkLamL tl b)
end.

Fixpoint mkPiL {n:nat} (lb: list (V*Term n)) (b: Term n) 
  : Term n :=
match lb with
| nil => b
| a::tl =>  mkPi (fst a) (snd a )(mkPiL tl b)
end.


Notation "x → y" := (mkFun x y)
  (at level 99, y at level 200, right associativity).

Let dvar := (freshVar vOrig []).

Definition mkTR {n:nat} (A B s: Term n): Term n :=
  let lv := (freshVars 3 (Some vOrig) (free_vars B ++ free_vars A) []) in
  let R := nth 0 lv dvar in
  let a := nth 1 lv dvar in
  let b := nth 2 lv dvar in
 mkSig R (A → B → s) 
    (mkProd 
      (mkPi a A (mkSig b B (mkAppL (vterm R) [vterm a; vterm b]))) 
      (mkPi b B (mkSig a A (mkAppL (vterm R) [vterm a; vterm b]))) 
      ).

Definition pfst {n:nat} (T: Term n): Term n :=
oterm (pProjSig _ true) [bterm [] T].

Fixpoint translate {n:nat} (t:Term n) : Term n :=
match t with
| vterm v => vterm (vrel v)
| oterm (pSort _ _ n) [] => 
  let x:= dvar in
  mkLamL [(x,t);(vprime x, t)] (mkTR (vterm x) (vterm (vprime x)) t)
| oterm (pPi _) [bterm [] A; bterm [x] B] =>
  let f:= (freshVar vOrig (free_vars A ++ free_vars B)) in
  let A':= tvmap vprime A in
  let B':= tvmap vprime B in
  let t' := oterm (pPi _) [bterm [] A'; bterm [x] B'] in 
  let tA := translate A in 
  let tB := translate B in 
(* fix : make a sigma type, with proof of totality of the relation below *)
 mkLamL 
  [(f,t);(vprime f,t')]
  (mkPiL 
   [(x,A);(vprime x, A');(vrel x, mkAppL (pfst tA) [vterm x; vterm (vprime x)])]
    (mkAppL (pfst tB) [mkApp (vterm f) (vterm x); 
                    mkApp (vterm (vprime f)) (vterm (vprime x))]))
| _ => oterm (pApp _) nil
end.

(*
because any type can be provided for instantiating an existential, as in RProp rforall,all type constructors must preserve 
  the property required by such instantiations.
E.g., because we have (nat->nat) : Type,
we have [[nat->nat]]: [[Type]] (nat -> nat) (nat -> nat),
which computes to saying that [[nat->nat]] is a total relation.
*)

Print VarType.
End VarSort.

(*delete. import common.*)
Definition TotalHeteroRel {T1 T2 : Type} (R: T1 -> T2 -> Type) : Type :=
(forall (t1:T1), @sigT T2 (R t1))*
(forall (t2:T2), @sigT _ (fun t1:T1 => R t1 t2)).
(*delete. import common.*)

Definition R_Pi {A1 A2 :Type} {A_R: A1 -> A2 -> Type}
  {B1: A1 -> Type}
  {B2: A2 -> Type} 
  (B_R: forall {a1 a2}, A_R a1 a2 -> (B1 a1) -> (B2 a2) -> Type)
  (f1: forall a, B1 a) (f2: forall a, B2 a) : Type
  :=
  forall a1 a2 (p: A_R a1 a2), B_R p (f1 a1) (f2 a2).



Lemma totalPi (A1 A2 :Type) (A_R: A1 -> A2 -> Type) 
  (trp : TotalHeteroRel A_R) 
  (B1: A1 -> Type) 
  (B2: A2 -> Type) 
  (B_R: forall a1 a2, A_R a1 a2 -> (B1 a1) -> (B2 a2) -> Type)
  (trb: forall a1 a2 (p:A_R a1 a2), TotalHeteroRel (B_R _ _ p))
:
  TotalHeteroRel (R_Pi B_R).
Proof.
  split.
- intros f1. apply snd in trp.
  eexists.
  Unshelve.
    Focus 2.
    intros a2. specialize (trp a2). destruct trp as [a11 ar].
    specialize (trb _ _ ar).
    apply fst in trb.
    specialize (trb (f1 a11)). exact (projT1 trb).
  simpl.
  intros ? ? ?.
  destruct (trp a2) as [a1r ar].
  destruct (trb a1r a2 ar) as [b2 br].
  simpl.
  destruct (b2 (f1 a1r)). simpl.
  specialize (br x). destruct br.
  specialize (b2 x0). destruct b2.
Abort.

Lemma totalImpl (A1 A2 B1 B2 :Type) 
  (A_R: A1 -> A2 -> Type) 
  (B_R: B1 -> B2 -> Type) 
  (arp : TotalHeteroRel A_R) 
  (brp : TotalHeteroRel B_R) :
  let RImpl := fun f1 f2 => 
(forall a1 a1r a2, 
      A_R a1 a2 
      -> A_R a1r a2 
      -> B_R (f1 a1r) (f2 a2) 
      -> B_R (f1 a1) (f2 a2))
  ->
    (forall a1 a2, A_R a1 a2 -> B_R (f1 a1) (f2 a2))
     in
  TotalHeteroRel RImpl.
Proof.
  split.
- intros f1.
  eexists.
  Unshelve.
    Focus 2.
    intros a2. apply snd in arp.
    specialize (arp a2). destruct arp as [a11 ar].
    apply fst in brp.
    specialize (brp (f1 a11)). exact (projT1 brp).
  simpl.
  intros ? ? ? ?.
  specialize (fun ar => X _ ar _ X0).
(* we can certainly cook up bad functions *)
  destruct (snd arp a2) as [a1r ar]. simpl in *.
  specialize (X _ ar).
  destruct (fst brp (f1 a1r)) as [b2 br]. simpl in *.
 eauto; fail.
Abort.

Definition ftransport {A1 A2 B1 B2 :Type}
  (A_R: A1 -> A2 -> Type) 
  (B_R: B1 -> B2 -> Type) 
  (arp : TotalHeteroRel A_R) 
  (brp : TotalHeteroRel B_R)
  (f1: A1 -> B1) : A2 -> B2.
    intros a2. apply snd in arp.
    specialize (arp a2). destruct arp as [a11 ar].
    apply fst in brp.
    specialize (brp (f1 a11)). exact (projT1 brp).
Defined.

Lemma totalImpl (A1 A2 B1 B2 :Type) 
  (A_R: A1 -> A2 -> Type) 
  (B_R: B1 -> B2 -> Type) 
  (arp : TotalHeteroRel A_R) 
  (brp : TotalHeteroRel B_R) :
  let RImpl := fun f1 f2 => 
    (forall a1 a2, A_R a1 a2 -> B_R (f1 a1) (f2 a2))
     in
  TotalHeteroRel RImpl.
Proof.
  split.
- intros f1.
  exists (ftransport arp brp f1).
  simpl.
  intros ? ? ?. unfold ftransport.
(* we can certainly cook up bad functions *)
  destruct (snd arp a2) as [a1r ar]. simpl in *.
  destruct (fst brp (f1 a1r)) as [b2 br]. simpl in *.
  (* there is no way to use the A_Rs to bet B_Rs about f1.
  because there is only 1 B_R hypothesis, zig-zagness wont help.
    We cannot assume that f1 behaves
    parametrically.*)
Abort.

Definition totalRelPiClosed := forall (A1 A2 B1 B2 :Type)
  (A_R: A1 -> A2 -> Type) 
  (B_R: B1 -> B2 -> Type) 
  (arp : TotalHeteroRel A_R) 
  (brp : TotalHeteroRel B_R),
  let RImpl := fun f1 f2 => 
    (forall a1 a2, A_R a1 a2 -> B_R (f1 a1) (f2 a2))
     in
  TotalHeteroRel RImpl.

Locate is_evenb.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Init.Nat.

Lemma counterEx : totalRelPiClosed -> False.
Proof.
  intros Hc. set (R:= fun x y => even x = even y). 
  evar (T: TotalHeteroRel R).
  Unshelve.
    Focus 2.
     (split; intros x; exists x; reflexivity).
  specialize (Hc nat nat nat nat R R T T).
  simpl in *.
  apply fst in Hc.
  set (bad := fun n =>
  match n with
  | O => 1
  | _ => 0
  end).
  specialize (Hc bad).
  simpl in Hc.
  destruct Hc as [f2 p].
  assert (f2 = ftransport T T bad) by admit.
    (* true by parametricity. if A1=A2, B1=B2, and have HeterRels pick indentical
       elements, the only way to construct a B from an A is to use f1 exactly once.
https://onedrive.live.com/edit.aspx/Documents/Postdoc?cid=946e75b47b19a3b5&id=documents&wd=target%28parametricity%2Ftheory.one%7CB23D752F-C19A-4F84-BCA5-B8772CAB76D4%2FTotal%20hetero%20rel%20not%20closed%20under%20function%20types%7C1EE46CCF-C669-4157-8495-84454400EB7C%2F%29
*)
  subst.
  specialize (p 0 2 eq_refl). unfold ftransport in p.
  simpl in p. unfold R in p. simpl in p. inversion p; fail.
  Fail idtac. (* done, except the above admit *)
Abort.

Lemma totalConj (A1 A2 B1 B2 :Type) 
  (A_R: A1 -> A2 -> Type) 
  (B_R: B1 -> B2 -> Type) 
  (arp : TotalHeteroRel A_R) 
  (brp : TotalHeteroRel B_R) :
  let RImpl := fun f1 f2 => 
  prod (A_R (fst f1) (fst f2)) (B_R (snd f1) (snd f2))
     in
  TotalHeteroRel RImpl.
Proof.
  intros. unfold RImpl. clear RImpl.
  split.
- intros. apply fst in arp. apply fst in brp.
  destruct t1 as [a1 b1].
  specialize (arp a1).
  specialize (brp b1).
  destruct arp as [a2 pa].
  destruct brp as [b2 pb].
  exists (a2,b2). simpl. tauto.
- (*similar*)
Abort.

(* perhaps contra variant type constructors are the only problem *)






