Require Import ReflParam.common.
Require Import ReflParam.templateCoqMisc.
Require Import String.
Require Import List.
Require Import Template.Ast.
Require Import SquiggleEq.terms.
Require Import ReflParam.paramDirect.
Require Import SquiggleEq.substitution.
Require Import ReflParam.PiTypeR.
Import ListNotations.
Open Scope string_scope.

Require Import ReflParam.Trecord.


Section Tm.
Set Imlicit Arguments.

Inductive eqs (A : Set) (x : A) : forall (a:A), Prop :=  
eq_refls : eqs A x x.
Inductive sigs (A : Set) (P : A -> Prop) : Set :=
 existss : forall x : A, P x -> sigs A P.

Definition beq (b1 b2 : bool) := eqs bool b1 b2.
Infix "≡" := beq (at level 80).

Definition and (A B:Prop):=
  forall (b:bool), if b then A else B.

Variable V:Set.

Inductive Tm : Set :=
| var : V -> Tm
| lam : V -> Tm -> Tm
| app : Tm -> Tm -> Tm.

(* not needed *)
Fixpoint size (t:Tm) : nat :=
match t with
| var _ => 1
| app l r => 1 + (size l + size r)
| lam _ b => 1 + size b
end.

Variable veq : V -> V -> bool.

Fixpoint inFreeVarsOf (t:Tm) (v:V) : bool :=
  match t with
  | var vv => veq vv v
  | app l r => orb (inFreeVarsOf l v)  (inFreeVarsOf r v)
  | lam vv b => if (veq vv v) then false else (inFreeVarsOf b v)
  end.

Definition inFreeVarsIff (t1 t2:Tm) (v:V) : Prop :=
  beq (inFreeVarsOf t1 v) (inFreeVarsOf t2 v).

Definition sameFreeVars (t1 t2:Tm) : Prop :=
  forall (v:V), inFreeVarsIff t1 t2 v.

Fixpoint inAllVarsOf v (t:Tm) : bool :=
  match t with
  | var vv => veq vv v
  | app l r => orb (inAllVarsOf v l)  (inAllVarsOf v r)
  | lam vv b => orb (veq vv v) (inAllVarsOf v b)
  end.

Fixpoint substAux (v:V)  (u t:Tm) : Tm :=
  match t with
  | var vv => if veq vv v then u else t
  | app l r => app (substAux v u l) (substAux v u r)
  | lam vv b => if veq vv v then t else lam vv (substAux v u b)
  end.

Fixpoint alphaEq (fuel:nat) (t1 t2:Tm) {struct fuel}: Prop :=
  match fuel, t1,t2 with
    | S fuel, var v1, var v2 => beq (veq v1 v2) true
    | S fuel, app l1 r1, app l2 r2 =>
      and (alphaEq fuel l1 l2) (alphaEq fuel r1 r2)
    | S fuel, lam v1 b1, lam v2 b2 =>
      forall (vf:V), (inAllVarsOf vf t1) ≡  false
                ->  (inAllVarsOf vf t2) ≡ false 
                -> alphaEq fuel
                          (substAux v1 (var vf) b1)
                          (substAux v2 (var vf) b2)
    |  _, _, _  => true ≡ false
  end.

Definition alphaEqq  (t1 t2:Tm) : Set :=
 sigs nat (fun fuel:nat => alphaEq fuel t1 t2).

End Tm.


Definition beqType := bool -> bool -> Prop.

Run TemplateProgram (genParamIndAll [] "Coq.Init.Datatypes.bool").
Run TemplateProgram (genParamIndAll [] "Top.alphaEquivariant.Tm").
Run TemplateProgram (genParamIndAll [] "Top.alphaEquivariant.eqs").
Run TemplateProgram (genParamIndAll [] "Coq.Init.Datatypes.nat").
Run TemplateProgram (genParamIndAll [] "Top.alphaEquivariant.sigs").


Run TemplateProgram (mkIndEnv "indTransEnv" [
"Coq.Init.Datatypes.bool" ; "Coq.Init.Datatypes.nat";
"Top.alphaEquivariant.Tm"; "Top.alphaEquivariant.eqs"; 
"Top.alphaEquivariant.sigs"]).

Run TemplateProgram (genWrappers indTransEnv).


Run TemplateProgram (genParam indTransEnv true true "Top.alphaEquivariant.and").


(* define a Set version of eq, then automatically translate beq *)
Run TemplateProgram (genParam [] true true "beqType").

Check Top_alphaEquivariant_eqs_pmtcty_RR0iff12.


Run TemplateProgram (genParam indTransEnv true true "Top.alphaEquivariant.beq").

Run TemplateProgram (genParam indTransEnv true true "Coq.Init.Datatypes.orb").

Run TemplateProgram (genParam indTransEnv true true 
"Top.alphaEquivariant.inFreeVarsOf").

Run TemplateProgram (genParam indTransEnv true true "Top.alphaEquivariant.inFreeVarsIff").

Run TemplateProgram (genParam indTransEnv true true "Top.alphaEquivariant.sameFreeVars").

Definition sameFreeVars_RRs := 
fun (V V₂ : Set) (V_R : BestRel V V₂) (veq : V -> V -> bool) (veq₂ : V₂ -> V₂ -> bool)
  (veq_R : BestR
             (PiGoodSet V V₂ V_R (fun _ : V => V -> bool) (fun _ : V₂ => V₂ -> bool)
                (fun (H : V) (H0 : V₂) (_ : BestR V_R H H0) =>
                 PiGoodSet V V₂ V_R (fun _ : V => bool) (fun _ : V₂ => bool)
                   (fun (H1 : V) (H2 : V₂) (_ : BestR V_R H1 H2) =>
                    Coq_Init_Datatypes_bool_pmtcty_RR0_iso))) veq veq₂) 
  (t1 : Tm V) (t1₂ : Tm V₂)
  (t1_R : BestR (Top_alphaEquivariant_Tm_pmtcty_RR0_iso V V₂ V_R) t1 t1₂) 
  (t2 : Tm V) (t2₂ : Tm V₂)
  (t2_R : BestR (Top_alphaEquivariant_Tm_pmtcty_RR0_iso V V₂ V_R) t2 t2₂) =>
PiGoodProp V V₂ V_R (fun v : V => inFreeVarsIff V veq t1 t2 v)
  (fun v₂ : V₂ => inFreeVarsIff V₂ veq₂ t1₂ t2₂ v₂)
  (fun (v : V) (v₂ : V₂) (v_R : BestR V_R v v₂) =>
   Top_alphaEquivariant_inFreeVarsIff_pmtcty_RR V V₂ V_R veq veq₂ veq_R t1 t1₂ t1_R t2 t2₂
     t2_R v v₂ v_R).

Require Import EqdepFacts.

Require Import JMeq.
Require Import ReflParam.unusedVar.

Print inFreeVarsIff.
Print Top_alphaEquivariant_Tm_pmtcty_RR0_indices.

Lemma dependsOnlyOnRelFV (V V₂ : Set) : @dependsOnlyOnRel V V₂ _ 
  (Top_alphaEquivariant_inFreeVarsIff_pmtcty_RR V V₂).
Proof.
  intros ? ? Heq. simpl.
  destruct V_R1.
  reflexivity.
Defined.



Lemma inFVarsIff2 : existsAGoodnessFreeImpl
  Top_alphaEquivariant_inFreeVarsIff_pmtcty_RR .
Proof.
  eexists.
  eexists.
  intros.
  set (fvv:= Top_alphaEquivariant_inFreeVarsIff_pmtcty_RR _ _ V_R).
  simpl in *.
  compute in *.
  reflexivity.
Defined.

Arguments existT {A} {P} x t.
Arguments exist {A} {P} x t.
Print inFVarsIff2.


(*
Lemma xxx  V  V₂ : exists A:Type , exists x:((GoodRel [Total] V  V₂)->A),
forall (V_R : BestRel V V₂),  
JMeq (x (@eraseRP allProps [Total] eq_refl _ _ V_R))
(sameFreeVars_RRs V  V₂ V_R).
simpl.
 (* exists sameFreeVars_RR; reflexivity *)
unfold sameFreeVars_RRs.
eexists.
eexists. intros.
unfold PiGoodProp. simpl.
unfold cast_Good_onlyTotal, eraseRP.
simpl.
destruct V_R. simpl.
compute.
reflexivity.
*)
(*
JMeq (?x (eraseRP [Total] eq_refl V_R))
  (fun (veq : V -> V -> bool) (veq₂ : V₂ -> V₂ -> bool)
     (veq_R : forall (a1 : V) (a2 : V₂),
              BestR V_R a1 a2 ->
              forall (a3 : V) (a4 : V₂),
              BestR V_R a3 a4 ->
              BestR Coq_Init_Datatypes_bool_pmtcty_RR0 (veq a1 a3) (veq₂ a2 a4))
     (t1 : Tm V) (t1₂ : Tm V₂)
     (t1_R : Temp.Top_alphaEquivariant_Tm_pmtcty_RR0 V V₂ V_R t1 t1₂) 
     (t2 : Tm V) (t2₂ : Tm V₂)
     (t2_R : Temp.Top_alphaEquivariant_Tm_pmtcty_RR0 V V₂ V_R t2 t2₂) =>
   PiGoodPropAux V V₂ (cast_Good_onlyTotal V_R) (fun v : V => inFreeVarsIff V veq t1 t2 v)
     (fun v₂ : V₂ => inFreeVarsIff V₂ veq₂ t1₂ t2₂ v₂)
     (fun (a1 : V) (a2 : V₂) (ar : R V_R a1 a2) =>
      cast_Good_onlyTotal
        (Top_alphaEquivariant_inFreeVarsIff_pmtcty_RR V V₂ V_R veq veq₂ veq_R t1 t1₂ t1_R
           t2 t2₂ t2_R a1 a2 ar)))
*)


Run TemplateProgram (genParam indTransEnv true true "Top.alphaEquivariant.inAllVarsOf").


Local Transparent Coq_Init_Datatypes_bool_pmtcty_RR0.


Run TemplateProgram (genParam indTransEnv true true "Top.alphaEquivariant.substAux").

Run TemplateProgram (genParam indTransEnv true true "Top.alphaEquivariant.alphaEq").
Run TemplateProgram (genParam indTransEnv true true "Top.alphaEquivariant.alphaEqq").

(*
Transport needs to be inlined or set at the right universe
The term "@UsefulTypes.transport" of type
 "forall (T : Type) (a b : T) (P : T -> Type), a = b -> P a -> P b"
*)


Section isoIff.
Variable V : Set.
Variable V₂ : Set.
Hypothesis V_R : BestRel V V₂.
Variable veq : V -> V -> bool.
Variable veq₂ : V₂ -> V₂ -> bool.
Hypothesis veq_R : BestR
              (PiGoodSet V V₂ V_R (fun _ : V => V -> bool)
                 (fun _ : V₂ => V₂ -> bool)
                 (fun (H : V) (H0 : V₂) (_ : BestR V_R H H0) =>
                  PiGoodSet V V₂ V_R (fun _ : V => bool)
                    (fun _ : V₂ => bool)
                    (fun (H1 : V) (H2 : V₂) (_ : BestR V_R H1 H2) =>
                     Coq_Init_Datatypes_bool_pmtcty_RR0_iso))) veq veq₂.

(* the new "free thm" implies iff *)
Lemma alphaIff2 : forall 
(fuel1 fuel2 : nat)
(fuelR : Coq_Init_Datatypes_nat_pmtcty_RR0 fuel1 fuel2)
(tml tmr : Tm V) (tml2 tmr2 : Tm V₂)
(tmRL : Top_alphaEquivariant_Tm_pmtcty_RR0 V V₂ (BestR V_R)
  tml tml2)
(tmRR : Top_alphaEquivariant_Tm_pmtcty_RR0 V V₂ (BestR V_R)
  tmr tmr2),
(alphaEq V veq fuel1 tml tmr) <-> (alphaEq V₂ veq₂ fuel2 tml2 tmr2).
Proof using V_R veq_R.
  intros.
  pose proof (Top_alphaEquivariant_alphaEq_pmtcty_RR
     V V₂ V_R veq veq₂ veq_R fuel1 fuel2 fuelR) as H.
  simpl in H.
  specialize (H tml tml2 tmRL tmr tmr2 tmRR).
  simpl in H.
  pose proof (Rtot H) as Ht.
  simpl in Ht.
  apply Prop_RSpec in Ht.
  apply fst in Ht.
  unfold IffRel in Ht.
  apply tiffIff in Ht.
  apply Ht.
Qed.



End isoIff.

Lemma dependsOnlyOnTotAlpha (V V₂ : Set) : @dependsOnlyOnRelTot V V₂ _
  (Top_alphaEquivariant_alphaEq_pmtcty_RR V V₂).
Proof.
  intros ? ? ?.
  destruct V_R1.
  reflexivity.
Qed.

(* sanity check: this should NOT be provable *)
Lemma dependsOnlyOnRelAlpha (V V₂ : Set) : @dependsOnlyOnRel V V₂ _
  (Top_alphaEquivariant_alphaEq_pmtcty_RR V V₂).
Proof.
  intros ? ? ? ?.
  destruct V_R1.
  Fail reflexivity.
Abort.

Lemma alphaIff : existsAOneFreeImpl
  Top_alphaEquivariant_alphaEq_pmtcty_RR .
Proof.
  eexists.
  eexists.
  intros.
  set (fvv:= Top_alphaEquivariant_alphaEq_pmtcty_RR _ _ V_R).
  simpl in *.
  lazy in fvv.
  reflexivity.
Defined.

Lemma dependsOnlyOnTotAlphaq (V V₂ : Set) : @dependsOnlyOnRelTot V V₂ _
  (Top_alphaEquivariant_alphaEqq_pmtcty_RR V V₂).
Proof.
  intros ? ? ?.
  destruct V_R1.
  reflexivity.
Qed.

(*
Lemma alphaEqqIff : existsAOneFreeImpl
  Top_alphaEquivariant_alphaEqq_pmtcty_RR .
Proof.
  eexists.
  eexists.
  intros.
  set (fvv:= Top_alphaEquivariant_alphaEqq_pmtcty_RR _ _ V_R).
  simpl in *.
  vm_compute in fvv.
  reflexivity.
Defined.
*)

Section isoIff2.
Variable V : Set.
Variable V₂ : Set.
Hypothesis V_R : GoodRel [Total] V V₂.
Variable veq : V -> V -> bool.
Variable veq₂ : V₂ -> V₂ -> bool.
Hypothesis veq_R : forall (a1 : V) (a2 : V₂),
@R _ _ _ V_R a1 a2 ->
forall (a3 : V) (a4 : V₂),
@R _ _ _ V_R a3 a4 -> Coq_Init_Datatypes_bool_pmtcty_RR0 (veq a1 a3) (veq₂ a2 a4).

(* the new "free thm" implies iff *)
Lemma alphaIff3 : forall 
(fuel1 fuel2 : nat)
(fuelR : Coq_Init_Datatypes_nat_pmtcty_RR0 fuel1 fuel2)
(tml tmr : Tm V) (tml2 tmr2 : Tm V₂)
(tmRL : Top_alphaEquivariant_Tm_pmtcty_RR0 V V₂ (@R _ _ _ V_R)
  tml tml2)
(tmRR : Top_alphaEquivariant_Tm_pmtcty_RR0 V V₂ (@R _ _ _ V_R)
  tmr tmr2),
(alphaEq V veq fuel1 tml tmr) <-> (alphaEq V₂ veq₂ fuel2 tml2 tmr2).
Proof using V_R veq_R.
  intros.
  destruct V_R. simpl in *.
  set (ff := proj1_sig (projT2 (alphaIff _ _ R Rtot)) _ _ veq_R _ _ fuelR
    _ _ tmRL _ _ tmRR).
  pose proof (Trecord.Rtot ff) as Ht.
  simpl in Ht.
  apply Prop_RSpec in Ht.
  apply fst in Ht.
  unfold IffRel in Ht.
  apply tiffIff in Ht.
  apply Ht.
Qed.

End isoIff2.
(* no axioms. all green*)