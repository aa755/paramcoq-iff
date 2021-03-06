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
Require Import ReflParam.common.
Require Import ReflParam.Trecord.

(* The type of this definition is what we eanted [Type] Set Set to be.
Now, [Type] Set Set is Set -> Set -> Type *)
Definition setTrans : GoodRel [Total; OneToOne] Set Set.
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
  intros  A B₁ B₂ H1b H2b.
  destruct H1b.
  destruct H2b.
  unfold allProps in *. simpl in *.
  rename R0 into R2.
(*

   A
  . .
.    .
 .    .
.    .
 .    .
B₁ =? B₂


Consider A₁ = B₁= A₂ = A
Now we have A ~ B₂ (A isomorphic to B2). 
They may not be equal (the questionmark link) unless we admit univalence.
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

Require Import Coq.Numbers.BinNums.

Lemma NotOneOneSet: (oneToOneHalf 
  (fun S₁ S₂ : Set => BestRel S₁ S₂)) -> False.
Proof using.
 intros Hc.
 unfold oneToOneHalf in Hc.
 specialize (Hc nat nat N).
 simpl in Hc.
(*BestRel nat nat -> BestRel nat N -> nat = N *)
Abort.

Lemma irrelSet: relIrrUptoEq
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

Notation Type_R := (fun T1 T2 => T1 -> T2 -> Type) (only parsing).


(** The case of Prop:Type *)
Definition Prop_R :  Type_R Prop Prop.
  simpl.
  intros P1 P2. exact (BestRel P1 P2).
Defined.

(** The case of Set:Type *)
Definition Set_R :  Type_R Set Set.
  simpl.
  intros P1 P2. exact (BestRel P1 P2).
Defined.


(*
Definition Prop_R2 :  BestRel Prop Prop.
  simpl.
  exists (fun P1 P2:Prop => BestRelP P1 P2); simpl.
  simpl
Defined.
*)



(** * Subtyping 

We know that Set :> Type. Does the parametricity translation need to preserve this?
Let A:Set
Let's check whetner [[Set]] A A:> [[Type]] A A.
Unlike the AnyRel translation, BestR needs to be added here. This can be problematic.
*)


Require Import Coq.Unicode.Utf8.

Section SubtypTest.
  Variable A:Set.
  Variable A_R : (λ(x x': Set), BestRel x x') A A.
  Check (BestR A_R: ((λ(x x': Type@{i}), x → x' → Type@{i}) A A)).
(** We may be able to ask Coq to mark all uses of subtyping by a Cast.
     Then we can translate (cast (cast t Set) Type) as projTyRel t.
  According to Figure 1 of Lasson12, there is only one other subtyping rule :
   covariance of the codomain of dependent function types.
  For such rules, we need to put the projTyrel under a lambda.
  In general, given an encoding of the subtyping rule, an explicit
  casting function can be computed by recursing on it.
*)
End SubtypTest.

