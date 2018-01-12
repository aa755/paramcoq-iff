Require Import List.
Import ListNotations.
Require Import Morphisms.
Require Import paramDirect.
Require Import indType.
Require Import indProp.
Require Import ReflParam.Trecord.
Require Import ReflParam.common.
Require Import ReflParam.unusedVar.
Require Import ReduceAwayVar.ReduceAwayVar.

Ltac typeof T := let tp := type of T in exact tp.
Notation IsoRel := BestRel.

Inductive eqs {V : Set} (x : V) : forall (a:V), Prop :=  
  eq_refls : eqs x x.
Infix "=" := eqs : type_scope.

Require Import String.
Open Scope string_scope.
Run TemplateProgram (mkIndEnv "indTransEnv" [
                                "Coq.Init.Datatypes.bool" ; "Coq.Init.Datatypes.nat"]).

Run TemplateProgram (genParamIndAll indTransEnv "Coq.Init.Datatypes.bool").
Run TemplateProgram (genParamIndAll indTransEnv "Coq.Init.Datatypes.nat").
Run TemplateProgram (genParamIndPropAll indTransEnv "Top.eqs").
Run TemplateProgram (genWrappers indTransEnv).

Notation bool_R' := Coq_Init_Datatypes_bool_pmtcty_RR0.
Notation nat_R' := Coq_Init_Datatypes_nat_pmtcty_RR0.
Definition Deq_R'
 {V₁ V₂: Set} (V_R: V₁ -> V₂ -> Prop)
 (eqb₁: V₁ -> V₁ -> bool)
 (eqb₂: V₂ -> V₂ -> bool) := 
 forall (al₁: V₁) (al₂: V₂) (al_R: V_R al₁ al₂)
        (ar₁: V₁) (ar₂: V₂) (ar_R: V_R ar₁ ar₂),
   bool_R'
     (eqb₁ al₁ ar₁)
     (eqb₂ al₂ ar₂).

Definition InfSeq_R' {V₁ V₂: Set} (V_R : V₁ -> V₂ -> Prop)
           (l₁ : nat -> V₁)
           (l₂ : nat -> V₂):=
  (forall n₁ n₂ : nat, nat_R' n₁ n₂
                       -> V_R (l₁ n₁) (l₂ n₂)).


Declare ML Module "paramcoq".
Parametricity Recursive bool.

Lemma bool_R_eq b1 b2:
  bool_R b1 b2 -> b1 = b2.
Proof using.
  intros H.
  inversion H; constructor.
Qed.

Lemma eq_bool_R b1 b2:
  b1= b2 -> bool_R b1 b2.
Proof using.
  intros H. destruct b1, b2; try constructor; inversion H.
Qed.

Lemma bool_R'_eq b1 b2:
  bool_R' b1 b2 -> b1 = b2.
Proof using.
  intros H. destruct b1, b2; simpl in *; tauto.
Qed.

Lemma eq_bool_R' b1 b2:
  b1= b2 -> bool_R' b1 b2.
Proof using.
  intros H. destruct b1, b2; try constructor; inversion H.
Qed.





(*{{{
Todo: 
1) a better name choice for isPermutation, or just drop it.
2) Better notation for eqb == true.

Start here. 

I will start with a brief illustration of how parametricity can be
used to get free proofs.
Lets start with an example from nominal logic.
We have this definition noDupb, which returns a boolean indicating 
whether the list has duplictes.
It is parametrized by an equality decider eqb.
The definition uses inb, which checks whether a list contains an element.
}}}*)


Fixpoint inb {V:Set} (eqb : V-> V-> bool)
         (a:V) (l:list V) : bool :=
  match l with
  | [] => false
  | h::tl => eqb a h || inb eqb a tl
  end.

Fixpoint noDupb {V:Set} (eqb : V-> V-> bool)
         (l: list V) : bool :=
  match l with
  | [] => true
  | h::tl => noDupb eqb tl && negb (inb eqb h tl)
  end.

Module M.
Inductive list_R {V₁ V₂ : Type}
  (V_R : V₁ -> V₂ -> Type) : list V₁ -> list V₂ -> Type :=
| nil_R : list_R V_R nil nil
| cons_R : forall (h : V₁) (h₂ : V₂) (tl : list V₁) (tl₂ : list V₂),
    V_R h h₂
    -> list_R V_R tl tl₂
    -> list_R V_R (cons h tl) (cons h₂ tl₂).
End M.

Section Equivariance.
Context {V:Set} (eqb: V -> V -> bool).
(*{{{
Suppose we have a type V and its equality decider.
In some domains we may want to prove specific choices of V's don't matter.
For example, when formalizing languages with variable bindings,
V could represent variable names.
As another example, if V denotes memory addresses, we may want to prove
that meanings are preserved irrespective of the memory addresses at
which our data structures are stored.

This property is called Equivariance in nominal logic.
It is usually defined in terms of permutations.
Let π be a permutation of variables.
}}}*)

Variable π: V->V.

(*{{{ ignore.  Hypothesis eqbEquivalence : Equivalence eqp. 
}}}*)

(*{{{
For now, we only need π to be injective.
More formally, 
(π v1) and (π v2) are equal, according to the equality decider,
iff v1 and v2 are equal.
}}}*)
Hypothesis π_inj: forall (v1 v2:V),
    eqb (π v1) (π v2) = eqb v1 v2.


Let eqp  a b := eqb a b = true.
(* Infix "==" := eqp (at level 50).   *)
Local Notation "a == b" := (eqb a b=true) (at level 50).  
Hypothesis eqbProper :
  Proper ((fun a b => a == b ) ==> (fun a b => a == b ) ==> eq) eqb.

(*{{{
Now we can state equivariance of noDupb as follows:
Suppose we have two lists l1 and l2.
this hypothesis says that elements of l2 are obtained by applying the permutatiom pi to elements of l2.

noDupb has a fixpoint. we will probably have to go by induction.
noDupb mentions inb which itself is a fixpoint. So we will perhaps
need another induction and have to state the right property for inb.
		 
In general, the more complex the body, the more complex the proof.
This is anoying because by Coq's parametricity, 
we know that all functions of this type (check noDupb, pause) are equivariant.

Fortunately, we can get such proofs almosy for free using a parametricity plugin.
}}}*)
Lemma noDupbEquivariant l1 l2:
  M.list_R (fun v1 v2 => v2 == (π v1)) l1 l2
  -> noDupb eqb l1 = noDupb eqb l2.
Abort.

(* paramcoq plugin

Keller, Chantal, and Marc Lasson. “Parametricity in an Impredicative Sort.” Computer Science Logic, September 27, 2012. https://doi.org/10.4230/LIPIcs.CSL.2012.399.
*)

Parametricity Recursive noDupb.

(*{{{ 
The plugin can be invoked like this. It creates this constant which is a proof of the following theorem. I will call it the parametricity theorem of noDup.
The statement looks complicated. Let me simplify it for you.
}}}*)
Check Top_o_noDupb_R.

(* turn on the beautify mode of company coq *)
Definition Deq_R
 {V₁ V₂: Set} (V_R: V₁ -> V₂ -> Set)
 (eqb₁: V₁ -> V₁ -> bool)
 (eqb₂: V₂ -> V₂ -> bool) := 
 forall (al₁: V₁) (al₂: V₂) (al_R: V_R al₁ al₂)
        (ar₁: V₁) (ar₂: V₂) (ar_R: V_R ar₁ ar₂),
   bool_R (eqb₁ al₁ ar₁)
          (eqb₂ al₂ ar₂).


(*{{{ 
This is the simplified statement. you can see that my simplfication did not change the meaning:
the simplified statement is definitionally equal to the old one.
			
The type of [noDupb] (see defn above) is a function type. 
The function has has 3 inputs: V, eqb, and l.
Intuitively, two functions are related when for all related inputs, they produce related outputs.
  For each such variable,
we have a 1 and 2 versions: e.g. we have an V1 and an V2: We can consider them as the 2 instantiations
of the interface. Then we have a variable V_R about how the instantiations are related.
Similarly, we have 2 instantiaions for the equality decider: eqb1 for the type V1 and eqb2 for V2.
The next assumption is a proof that eqb1 and eqb2 are related. eqb1 and eqb2 are functions.
Functions are related if for related inputs they produce related outputs.
then we have 2 lists: l1 of V1s and l2 of V2s.
then the final hypothesis says that l1 and l2 are related, which means that their respective
arguments are related according to Vr.
The conclusion says that the 2 instantiations of the function noDupb are related.
}}}*)

Definition noDup_R_Type :=
 forall
 (V₁ V₂ : Set) (V_R : V₁ -> V₂ -> Set)
 (eqb₁ : V₁ -> V₁ -> bool)
 (eqb₂ : V₂ -> V₂ -> bool)
 (eqb_R : Deq_R V_R eqb₁ eqb₂)
 (l₁ : list V₁)
 (l₂ : list V₂)
 (l_R: list_R _ _ V_R l₁ l₂),
   bool_R (noDupb eqb₁ l₁)
          (noDupb eqb₂ l₂).

Check (Top_o_noDupb_R:noDup_R_Type).
												
Print bool_R.

Lemma eqb_r: Deq_R (fun v1 v2 => v2 == (π v1)) eqb eqb.
Proof using π_inj eqbProper.
  intros ? ? ? ? ? ?.
  apply eq_bool_R.
  rewrite (eqbProper _ _ al_R _ _ ar_R).
  symmetry. apply π_inj.
Qed.


(*{{{
Lets come back to this lemma which is says that noDup is equivariant. 
Previously we did it by unfolding definitions and doing induction several times.
We can avoid all that by using the parametricity theorem of noDup.
}}}*)
Lemma noDupbEquivariant la1 la2:
  list_R _ _ (fun v1 v2 => v2 == (π v1)) la1 la2
  -> noDupb eqb la1 = noDupb eqb la2.
Proof using π_inj eqbProper.
  intros. apply bool_R_eq.
  (* delete this and fill this live. Note that Coq can infer everything except V_R*)
  apply Top_o_noDupb_R
    with (V₁:= V)
         (V₂:= V)
         (V_R:= (fun v1 v2 => v2 == (π v1)))
         (eqb₁:=eqb)
         (eqb₂:=eqb); try assumption.
  exact eqb_r.
Qed.
(* this proof only depends on the type of noDupb *)


(*{{{
The parametricity tool that I used so far in the talk is not our contribution.
To explain our contribution, consider this example noDupInf which just
like noDupb, but for infinite lists. This predicate says that an infinite list
has no duplicates. Now, our predicate is undecidable. So we are returning
a Prop instead of a bool. As we will see next, as a result of this change,
we get useless abstraction theorems from the old parametricity plugin.
}}}*)
Definition noDupInf
           (l: nat -> V) : Prop :=
  forall n1 n2, (l n1 == l n2) -> n1=n2.

Definition noDupInf3 
           (l: nat -> V) : Prop :=
  forall n1 n2 a,  (l n1) == a ->  a  == (l n2) -> n1=n2.

Definition noDupInf2
           (l: nat -> V) : Prop :=
  forall n1 n2, (l n1) = (l n2) -> n1=n2.


End Equivariance.


Parametricity Recursive noDupInf.
Check Top_o_noDupInf_R.

Definition InfSeq_R {V₁ V₂: Set} (V_R : V₁ -> V₂ -> Set)
           (l₁ : nat -> V₁)
           (l₂ : nat -> V₂):=
  (forall n₁ n₂ : nat, nat_R n₁ n₂ -> V_R (l₁ n₁) (l₂ n₂)).

Definition Prop_R (P₁ P₂ : Prop) : Type :=
  P₁ -> P₂ -> Prop.

(*{{{ Here is the statememt of the theorem produced by paramcoq.
the main difference is that the outputs are now related
by Prop_R because noDupInf returns a Prop.
 }}}*)
Definition noDupInf_R_Type :=
 forall
  (V₁ V₂ : Set) (V_R : V₁ -> V₂ -> Set)
  (eqb₁ : V₁ -> V₁ -> bool)
  (eqb₂ : V₂ -> V₂ -> bool)
  (eqb_R : Deq_R V_R eqb₁ eqb₂)
  (l₁ : nat -> V₁)
  (l₂ : nat -> V₂)
  (l_R: InfSeq_R V_R l₁ l₂),
   Prop_R
     (noDupInf eqb₁ l₁)
     (noDupInf eqb₂ l₂).

Check (Top_o_noDupInf_R:noDupInf_R_Type).

(*{{{ The theorem is useless because its conclusion is
useless. Any two propositions are related according to Prop_R.
 }}}*)

Lemma Prop_R_Trivial: forall (P1 P2: Prop), Prop_R P1 P2.
Proof. unfold Prop_R. simpl. intros P1 P2. intros p1 p2. exact False. Qed.

Lemma Prop_R_Trivial2: Prop_R True False.
Proof. apply Prop_R_Trivial. Qed.



(*{{{ This is what we would want the relation on propositions:
we would want related propositions to be logically equivalent.
Our main contribution is a new parametricity theory with this notion
of related propositions. we also have an implementation which we
call paramcoq-iff
}}}*)
Definition Prop_R_ideal (P₁ P₂ : Prop) := (P₁ <-> P₂).

(*{{{ Our actual definition is slightly different. but it implies iff
}}}*)
Definition Prop_Riff (P₁ P₂ : Prop) : Type :=
  IsoRel P₁ P₂.

Lemma Prop_Riff_iff (P₁ P₂ : Prop) :
  Prop_Riff P₁ P₂ -> (P₁ <-> P₂).
Proof. apply IsoRel_implies_iff. Qed.


(*{{{ Now the relatiin for props is very similar to the relation for bool 
}}}*)
Print bool_R.

(* invoke paramcoq-iff *)
Run TemplateProgram (genParam indTransEnv paramDirect.IsoRel true "Top.noDupInf").
Check Top_noDupInf_pmtcty_RR.


Section Pruning.
Variables 
(V V₂ : Set)
(Vᵣ : V -> V₂ -> Prop)
(VᵣTot : TotalHeteroRel Vᵣ)
.

Time 
ReduceAwayLamVar noDupInf_Riff := (
fun (VᵣOne : oneToOne Vᵣ) =>
let V_R := (@Build_GoodRel allProps _ _ Vᵣ VᵣTot VᵣOne) in
Top_noDupInf_pmtcty_RR _ _ V_R
).

End Pruning.


Definition noDupInf_Riff_Type :=
 forall
  (V₁ V₂ : Set) (V_R : V₁ -> V₂ -> Prop)
  (eqb₁ : V₁ -> V₁ -> bool)
  (eqb₂ : V₂ -> V₂ -> bool)
  (eqb_R : Deq_R' V_R eqb₁ eqb₂)
  (l₁ : nat -> V₁)
  (l₂ : nat -> V₂)
  (l_R: InfSeq_R' V_R l₁ l₂),
   Prop_Riff
     (noDupInf eqb₁ l₁)
     (noDupInf eqb₂ l₂).

Check (noDupInf_Riff:noDupInf_Riff_Type).

Module Inf.
Section Equivariance.
Variable V:Set.
Variable eqb : V -> V -> bool.
Variable π: V->V.
Hypothesis π_inj: forall (a1 a2:V),
    eqb (π a1) (π a2) = eqb a1 a2.

Let eqp  (a b:V) := eqb a b = true.
Hypothesis eqbProper :
  Proper (eqp ==> eqp ==> eq) eqb.
Definition isPermutation (a1 a2 : V) := eqb a2 (π a1) = true.

Lemma eqb_r: Deq_R' isPermutation eqb eqb.
Proof using π_inj eqbProper.
  intros ? ? ? ? ? ?.
  apply eq_bool_R'.
  rewrite (eqbProper _ _ al_R _ _ ar_R).
  symmetry. apply π_inj.
Qed.

Lemma noDupInf_Equivariant
      (l1 l2 : nat-> V):
  InfSeq_R' isPermutation l1 l2
  -> (noDupInf eqb l1 <-> noDupInf eqb l2).
Proof using π_inj eqbProper.
  intros. apply  Prop_Riff_iff.
  apply noDupInf_Riff with (Vᵣ := isPermutation); simpl; auto.
  exact eqb_r.
Qed.
End Equivariance.
End Inf.

(* mention ObsEq example in paper*)

(*{{{
Stronger conclusion, same assumptions => stronger free theorem :)
Sometimes, the free theorem makes stronger assumptions :( 
}}}*)


Run TemplateProgram (genParam indTransEnv true true "Top.noDupInf3").
Check Top_noDupInf3_pmtcty_RR.

Section Pruning3.
Variables 
(V V₂ : Set)
(Vᵣ : V -> V₂ -> Prop)
(VᵣTot : TotalHeteroRel Vᵣ)
.

Time 
ReduceAwayLamVar noDupInf3_Riff := (
fun (VᵣOne : oneToOne Vᵣ) =>
let V_R := (@Build_GoodRel allProps _ _ Vᵣ VᵣTot VᵣOne) in
Top_noDupInf3_pmtcty_RR _ _ V_R
).

End Pruning3.

Definition noDupInf3_Riff_Type :=
 forall
  (V₁ V₂ : Set) (V_R : V₁ -> V₂ -> Prop) (V_Rtot: TotalHeteroRel V_R)
  (eqb₁ : V₁ -> V₁ -> bool)
  (eqb₂ : V₂ -> V₂ -> bool)
  (eqb_R : Deq_R' V_R eqb₁ eqb₂)
  (l₁ : nat -> V₁)
  (l₂ : nat -> V₂)
  (l_R: InfSeq_R' V_R l₁ l₂),
   Prop_Riff
     (noDupInf3 eqb₁ l₁)
     (noDupInf3 eqb₂ l₂).

Check (noDupInf3_Riff:noDupInf3_Riff_Type).
 

Run TemplateProgram (genParam indTransEnv true true "Top.noDupInf2").
Check Top_noDupInf2_pmtcty_RR.

Section Pruning2.
Variables 
(V V₂ : Set)
(Vᵣ : V -> V₂ -> Prop)
(VᵣOne : oneToOne Vᵣ)
.

Time ReduceAwayLamVar noDupInf2_Riff := (
fun (VᵣTot : TotalHeteroRel Vᵣ) =>
let V_R := (@Build_GoodRel allProps _ _ Vᵣ VᵣTot VᵣOne) in
Top_noDupInf2_pmtcty_RR _ _ V_R
).

End Pruning2.

Check noDupInf2_Riff.


Definition noDupInf2_Riff_Type :=
 forall
  (V₁ V₂ : Set) (V_R : V₁ -> V₂ -> Prop) (V_Rone: oneToOne V_R)
  (l₁ : nat -> V₁)
  (l₂ : nat -> V₂)
  (l_R: InfSeq_R' V_R l₁ l₂),
   Prop_Riff
     (noDupInf2 l₁)
     (noDupInf2 l₂).

Check (noDupInf2_Riff:noDupInf2_Riff_Type).



(* univalence *)
  (* Summary slide *)
  
(* problems 

* nat_R, bool_R vs =
*

*)

