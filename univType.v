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
Require Import common.
Require Import Trecord.

Definition setTrans : GoodRel [Total; OneToOne; Irrel] Set Set.
(* apply Build_GoodRel with  (R:=fun H H0 : Set => BestRel H H0). *)
Abort.



Lemma TSet: TotalHeteroRelHalf (fun H H0 : Set => BestRel H H0).
Proof using.
  intros s1. exists s1.
(*
s1 : Set
______________________________________(1/1)
BestRel s1 s1
*)
(* use the identity relation *)
Abort.

Lemma OneSet: oneToOneHalf 
  (fun S₁ S₂ : Set => BestRel S₁ S₂).
(*the relation says that says that S₁ and S₂ are isomporphic types (upto eq).
Then one to one requires univalence.
And irrel implies UIP. The two are contradictory. *)
Proof using.
  intros  ? ? ? ? H1b H2b H1eq.
  destruct H1b.
  destruct H2b.
  unfold allProps in *. simpl in *.
  rename R0 into R2.
(*

a1 = a2
.    .
 .    .
.    .
 .    .
b1 =? b2


Consider a1 = b1= a
now we have a ~ b2 (a isomorphic to b2). They may not be equal unless we admit univalence.
But univalence goes against the idea of having parametricity relations be proof
irrelevant.

If we reject that idea and do not require relations to be proof irrelevant, 
we would be forced to get rid of irrel hyps in PiTypeR.v
and PIW.v
Is that riddance possible?
Even if it is, it assuming univalence makes this work less useful in comparison to HoTT.
Still, the free theorems may go beyond HoTT

oneToOne was a critical requirement for TotalHeter for Pi Types. So we need this proof.

Have [Set] be [Prop]? Then we wont need the irrel argument.
*)


(* Alternatively, translate Type as before. Only Set will be translated specially.
this means that the main advantate of our approach would be in polymorphic propositions
in about T:Set. For most applications, where ts are ASTs, this suffices
*)
Abort.

Lemma irrelSet: rellIrrUptoEq
  (fun S₁ S₂ : Set => BestRel S₁ S₂).
Proof using.
  intros ? ? ? ?.
  (* these may be two different isomorphisms and may not be equal *)
Abort.

(* In the translation of Pi, can the x_R be of type Cast (A_R _ _)? If so, 
irrel may not be needed, and thus we can ditch proof irrelevance for 
the univalence axiom. The advantage over HoTT will then be that we get stronger
free theorems in some cases. 
Casting will also make it compulsary to not match on x_r, and thus use 
the alternate version of translation of inductives and fixpoints.
We can have both versions – the proof irrelevance version and the univalence version
*)

