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


Definition beq (b1 b2 : bool) := b1=b2.
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

End Tm.


Definition beqType := bool -> bool -> Prop.

Module Temp.
Run TemplateProgram (genParamInd [] true true true "Coq.Init.Datatypes.bool").
Run TemplateProgram (genParamInd [] true true true "Top.alphaEquivariant.Tm").
Run TemplateProgram (genParamInd [] true true true "Coq.Init.Datatypes.nat").
End Temp.

Import Temp.

Definition isBestRel {A1 A2: Set} (R: A1-> A2 -> Prop) : Type := TotalHeteroRel R
                 * oneToOne R.
                 
Axiom goodBool : isBestRel Coq_Init_Datatypes_bool_pmtcty_RR0.
Axiom goodNat : isBestRel Coq_Init_Datatypes_nat_pmtcty_RR0.

Run TemplateProgram (mkIndEnv "indTransEnv" ["Top.alphaEquivariant.Tm";
"Coq.Init.Datatypes.bool" ; "Coq.Init.Datatypes.nat"]).


Definition Coq_Init_Datatypes_bool_pmtcty_RR0 : BestRel bool bool.
Proof.
  exists Coq_Init_Datatypes_bool_pmtcty_RR0; simpl.
- apply goodBool.
- apply goodBool.
- intros ? ? ? ?. apply ProofIrrelevance.PI.proof_irrelevance.  
Defined.

Definition xx : IndicesInvUniv := Prop.


Run TemplateProgram (genParam indTransEnv true true "and").



Definition Coq_Init_Datatypes_nat_pmtcty_RR0 : BestRel nat nat.
Proof.
  exists Coq_Init_Datatypes_nat_pmtcty_RR0; simpl.
- apply goodNat.
- apply goodNat.
- intros ? ? ? ?. apply ProofIrrelevance.PI.proof_irrelevance.  
Defined.

Run TemplateProgram (genParam [] true true "beqType").
Axiom beq_RR : ltac:(let t:= eval lazy in (beqType_RR beq beq) in exact t).

Local Opaque Coq_Init_Datatypes_bool_pmtcty_RR0.
(*
beq_RR
     : forall H H0 : bool,
       Coq_Init_Datatypes_bool_pmtcty_RR0 H H0 ->
       forall H1 H2 : bool,
       Coq_Init_Datatypes_bool_pmtcty_RR0 H1 H2 ->
       GoodRel [Total; OneToOne; Irrel] (H = H1) (H0 = H2)
 *)

Axiom goodTm : forall (V V₂ : Set) (V_R : BestRel V V₂),
isBestRel (Top_alphaEquivariant_Tm_pmtcty_RR0 _ _ V_R).


Definition Top_alphaEquivariant_Tm_pmtcty_RR0 (V V₂ : Set) (V_R : BestRel V V₂) 
 : BestRel (Tm V) (Tm V₂).
Proof.
  exists (Top_alphaEquivariant_Tm_pmtcty_RR0 _ _ V_R); simpl.
- apply goodTm.
- apply goodTm.
- intros ? ? ? ?. apply ProofIrrelevance.PI.proof_irrelevance.  
Defined.


Run TemplateProgram (genParam indTransEnv true true "orb").

Definition Coq_Init_Datatypes_orb_pmtcty_RR := orb_RR.

Run TemplateProgram (genParam indTransEnv true true "inFreeVarsOf").
Definition Top_alphaEquivariant_inFreeVarsOf_pmtcty_RR := inFreeVarsOf_RR.
Axiom Top_alphaEquivariant_beq_pmtcty_RR : beqType_RR beq beq.

Run TemplateProgram (genParam indTransEnv true true "inFreeVarsIff").

Definition Top_alphaEquivariant_inFreeVarsIff_pmtcty_RR := 
inFreeVarsIff_RR.

Run TemplateProgram (genParam indTransEnv true true "sameFreeVars").
Print sameFreeVars_RR.

Definition sameFreeVars_RRs := 
(fun (V V₂ : Set) (V_R : BestRel V V₂) (veq : V -> V -> bool) 
     (veq₂ : V₂ -> V₂ -> bool)
     (veq_R : forall (a1 : V) (a2 : V₂),
              R V_R a1 a2 ->
              forall (a3 : V) (a4 : V₂),
              R V_R a3 a4 -> R Coq_Init_Datatypes_bool_pmtcty_RR0 (veq a1 a3) (veq₂ a2 a4))
     (t1 : Tm V) (t1₂ : Tm V₂)
     (t1_R : Temp.Top_alphaEquivariant_Tm_pmtcty_RR0 V V₂ V_R t1 t1₂) 
     (t2 : Tm V) (t2₂ : Tm V₂)
     (t2_R : Temp.Top_alphaEquivariant_Tm_pmtcty_RR0 V V₂ V_R t2 t2₂) =>
   PiGoodSet V V₂ V_R (fun v : V => inFreeVarsIff V veq t1 t2 v)
     (fun v₂ : V₂ => inFreeVarsIff V₂ veq₂ t1₂ t2₂ v₂)
     (fun (v : V) (v₂ : V₂) (v_R : BestR V_R v v₂) =>
      Top_alphaEquivariant_inFreeVarsIff_pmtcty_RR V V₂ V_R veq veq₂ veq_R t1 t1₂ t1_R t2
        t2₂ t2_R v v₂ v_R)).

Require Import EqdepFacts.

Definition dependsOnlyOnRel (V V₂ : Set) {T:(BestRel V V₂)->Type} 
  (P: forall v: BestRel V V₂, T v):=
forall (V_R1 : BestRel V V₂) pt po pi,
let V_R2 := {| R:= BestR V_R1; Rtot := pt ; Rone := po; Rirrel:= pi  |} in
 eq_dep _ _ _ (P V_R1) _ (P V_R2).

Lemma dependsOnlyOnRelFV (V V₂ : Set) : dependsOnlyOnRel V V₂ (inFreeVarsIff_RR V V₂).
Proof.
  intros ? ? Heq.
  destruct V_R1.
  simpl.
  simpl. unfold inFreeVarsIff_RR. simpl.
  unfold Top_alphaEquivariant_inFreeVarsOf_pmtcty_RR.
  unfold inFreeVarsOf_RR. simpl.
  simpl in Heq.
  Print Temp.Top_alphaEquivariant_Tm_pmtcty_RR0.
Abort.
Require Import JMeq.

Lemma xxx  V  V₂ : exists A:Type , exists x:((GoodRel [Total] V  V₂)->A),
forall (V_R : BestRel V V₂),  
JMeq (x (@eraseRP allProps [Total] eq_refl _ _ V_R))
(sameFreeVars_RRs V  V₂ V_R).
simpl.
 (* exists sameFreeVars_RR; reflexivity *)
unfold sameFreeVars_RRs.
eexists.
eexists. intros.
Abort.

Run TemplateProgram (genParam indTransEnv true true "inAllVarsOf").


Local Transparent Coq_Init_Datatypes_bool_pmtcty_RR0.

Definition Top_alphaEquivariant_and_pmtcty_RR := and_RR.

(*
Proof.
  intros ? ?. simpl. intros ? ? ? ?.
  (* beq uses eq.  once we have oneToOne of eq, this should be automatic. *)
Admitted.
*)

Definition Top_alphaEquivariant_inAllVarsOf_pmtcty_RR := 
inAllVarsOf_RR.

Run TemplateProgram (genParam indTransEnv true true "substAux").

Definition  Top_alphaEquivariant_substAux_pmtcty_RR := substAux_RR.


Run TemplateProgram (genParam indTransEnv true true "alphaEq").

(*
Transport needs to be inlined or set at the right universe
The term "@UsefulTypes.transport" of type
 "forall (T : Type) (a b : T) (P : T -> Type), a = b -> P a -> P b"
*)



Section isoIff.
Variable V : Set.
Variable V₂ : Set.
Axiom V_R : BestRel V V₂.
Variable veq : V -> V -> bool.
Variable veq₂ : V₂ -> V₂ -> bool.
Axiom veq_R : BestR
              (PiGoodSet V V₂ V_R (fun _ : V => V -> bool)
                 (fun _ : V₂ => V₂ -> bool)
                 (fun (H : V) (H0 : V₂) (_ : BestR V_R H H0) =>
                  PiGoodSet V V₂ V_R (fun _ : V => bool)
                    (fun _ : V₂ => bool)
                    (fun (H1 : V) (H2 : V₂) (_ : BestR V_R H1 H2) =>
                     Coq_Init_Datatypes_bool_pmtcty_RR0))) veq veq₂.


Lemma alphaIff2 : forall 
(fuel1 fuel2 : nat)
(fuelR : Temp.Coq_Init_Datatypes_nat_pmtcty_RR0 fuel1 fuel2)
(tml tmr : Tm V) (tml2 tmr2 : Tm V₂)
(tmRL : Temp.Top_alphaEquivariant_Tm_pmtcty_RR0 V V₂ V_R
  tml tml2)
(tmRR : Temp.Top_alphaEquivariant_Tm_pmtcty_RR0 V V₂ V_R
  tmr tmr2),
(alphaEq V veq fuel1 tml tmr) <-> (alphaEq V₂ veq₂ fuel2 tml2 tmr2).
Proof using.
  intros.
  pose proof (alphaEq_RR V V₂ V_R veq veq₂ veq_R fuel1 fuel2 fuelR) as H.
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

Definition alphaEqRR := 
(fun (V V₂ : Set) (V_R : BestRel V V₂) (veq : V -> V -> bool)
   (veq₂ : V₂ -> V₂ -> bool)
   (veq_R : BestR
              (PiGoodSet V V₂ V_R (fun _ : V => V -> bool)
                 (fun _ : V₂ => V₂ -> bool)
                 (fun (H : V) (H0 : V₂) (_ : BestR V_R H H0) =>
                  PiGoodSet V V₂ V_R (fun _ : V => bool)
                    (fun _ : V₂ => bool)
                    (fun (H1 : V) (H2 : V₂) (_ : BestR V_R H1 H2) =>
                     Coq_Init_Datatypes_bool_pmtcty_RR0))) veq veq₂) =>
 let
   fix alphaEq (fuel : nat) (t1 t2 : Tm V) {struct fuel} : Prop :=
     match fuel with
     | 0%nat => beq true false
     | S fuel0 =>
         match t1 with
         | var _ v1 =>
             match t2 with
             | var _ v2 => beq (veq v1 v2) true
             | lam _ _ _ => beq true false
             | app _ _ _ => beq true false
             end
         | lam _ v1 b1 =>
             match t2 with
             | var _ _ => beq true false
             | lam _ v2 b2 =>
                 forall vf : V,
                 beq (inAllVarsOf V veq vf t1) false ->
                 beq (inAllVarsOf V veq vf t2) false ->
                 alphaEq fuel0 (substAux V veq v1 (var V vf) b1)
                   (substAux V veq v2 (var V vf) b2)
             | app _ _ _ => beq true false
             end
         | app _ l1 r1 =>
             match t2 with
             | var _ _ => beq true false
             | lam _ _ _ => beq true false
             | app _ l2 r2 => and (alphaEq fuel0 l1 l2) (alphaEq fuel0 r1 r2)
             end
         end
     end in
 let
   fix alphaEq₂ (fuel₂ : nat) (t1₂ t2₂ : Tm V₂) {struct fuel₂} : Prop :=
     match fuel₂ with
     | 0%nat => beq true false
     | S fuel₂0 =>
         match t1₂ with
         | var _ v1₂ =>
             match t2₂ with
             | var _ v2₂ => beq (veq₂ v1₂ v2₂) true
             | lam _ _ _ => beq true false
             | app _ _ _ => beq true false
             end
         | lam _ v1₂ b1₂ =>
             match t2₂ with
             | var _ _ => beq true false
             | lam _ v2₂ b2₂ =>
                 forall vf₂ : V₂,
                 beq (inAllVarsOf V₂ veq₂ vf₂ t1₂) false ->
                 beq (inAllVarsOf V₂ veq₂ vf₂ t2₂) false ->
                 alphaEq₂ fuel₂0 (substAux V₂ veq₂ v1₂ (var V₂ vf₂) b1₂)
                   (substAux V₂ veq₂ v2₂ (var V₂ vf₂) b2₂)
             | app _ _ _ => beq true false
             end
         | app _ l1₂ r1₂ =>
             match t2₂ with
             | var _ _ => beq true false
             | lam _ _ _ => beq true false
             | app _ l2₂ r2₂ =>
                 and (alphaEq₂ fuel₂0 l1₂ l2₂) (alphaEq₂ fuel₂0 r1₂ r2₂)
             end
         end
     end in
 fix
 alphaEq_R (fuel fuel₂ : nat)
           (fuel_R : BestR Coq_Init_Datatypes_nat_pmtcty_RR0 fuel fuel₂)
           (t1 : Tm V) (t1₂ : Tm V₂)
           (t1_R : BestR (Top_alphaEquivariant_Tm_pmtcty_RR0 V V₂ V_R) t1 t1₂)
           (t2 : Tm V) (t2₂ : Tm V₂)
           (t2_R : BestR (Top_alphaEquivariant_Tm_pmtcty_RR0 V V₂ V_R) t2 t2₂)
           {struct fuel} :
   (fun H H0 : Prop => BestRel H H0) (alphaEq fuel t1 t2)
     (alphaEq₂ fuel₂ t1₂ t2₂) :=
   match
     (fun (fuel0 : nat) (t3 t4 : Tm V) =>
      match
        fuel0 as fuel1
        return
          (match fuel1 with
           | 0%nat => beq true false
           | S fuel2 =>
               match t3 with
               | var _ v1 =>
                   match t4 with
                   | var _ v2 => beq (veq v1 v2) true
                   | lam _ _ _ => beq true false
                   | app _ _ _ => beq true false
                   end
               | lam _ v1 b1 =>
                   match t4 with
                   | var _ _ => beq true false
                   | lam _ v2 b2 =>
                       forall vf : V,
                       beq (inAllVarsOf V veq vf t3) false ->
                       beq (inAllVarsOf V veq vf t4) false ->
                       alphaEq fuel2 (substAux V veq v1 (var V vf) b1)
                         (substAux V veq v2 (var V vf) b2)
                   | app _ _ _ => beq true false
                   end
               | app _ l1 r1 =>
                   match t4 with
                   | var _ _ => beq true false
                   | lam _ _ _ => beq true false
                   | app _ l2 r2 =>
                       and (alphaEq fuel2 l1 l2) (alphaEq fuel2 r1 r2)
                   end
               end
           end = alphaEq fuel1 t3 t4)
      with
      | 0%nat => eq_refl
      | S x => eq_refl
      end) fuel t1 t2 in (_ = trEqr)
     return
       ((fun equ : Prop =>
         (fun H H0 : Prop => BestRel H H0) equ (alphaEq₂ fuel₂ t1₂ t2₂))
          trEqr)
   with
   | eq_refl =>
       match
         (fun (fuel₂0 : nat) (t1₂0 t2₂0 : Tm V₂) =>
          match
            fuel₂0 as fuel₂1
            return
              (match fuel₂1 with
               | 0%nat => beq true false
               | S fuel₂2 =>
                   match t1₂0 with
                   | var _ v1₂ =>
                       match t2₂0 with
                       | var _ v2₂ => beq (veq₂ v1₂ v2₂) true
                       | lam _ _ _ => beq true false
                       | app _ _ _ => beq true false
                       end
                   | lam _ v1₂ b1₂ =>
                       match t2₂0 with
                       | var _ _ => beq true false
                       | lam _ v2₂ b2₂ =>
                           forall vf₂ : V₂,
                           beq (inAllVarsOf V₂ veq₂ vf₂ t1₂0) false ->
                           beq (inAllVarsOf V₂ veq₂ vf₂ t2₂0) false ->
                           alphaEq₂ fuel₂2
                             (substAux V₂ veq₂ v1₂ (var V₂ vf₂) b1₂)
                             (substAux V₂ veq₂ v2₂ (var V₂ vf₂) b2₂)
                       | app _ _ _ => beq true false
                       end
                   | app _ l1₂ r1₂ =>
                       match t2₂0 with
                       | var _ _ => beq true false
                       | lam _ _ _ => beq true false
                       | app _ l2₂ r2₂ =>
                           and (alphaEq₂ fuel₂2 l1₂ l2₂)
                             (alphaEq₂ fuel₂2 r1₂ r2₂)
                       end
                   end
               end = alphaEq₂ fuel₂1 t1₂0 t2₂0)
          with
          | 0%nat => eq_refl
          | S x => eq_refl
          end) fuel₂ t1₂ t2₂ in (_ = trEqr)
         return
           ((fun equ : Prop =>
             (fun H H0 : Prop => BestRel H H0)
               match fuel with
               | 0%nat => beq true false
               | S fuel0 =>
                   match t1 with
                   | var _ v1 =>
                       match t2 with
                       | var _ v2 => beq (veq v1 v2) true
                       | lam _ _ _ => beq true false
                       | app _ _ _ => beq true false
                       end
                   | lam _ v1 b1 =>
                       match t2 with
                       | var _ _ => beq true false
                       | lam _ v2 b2 =>
                           forall vf : V,
                           beq (inAllVarsOf V veq vf t1) false ->
                           beq (inAllVarsOf V veq vf t2) false ->
                           alphaEq fuel0 (substAux V veq v1 (var V vf) b1)
                             (substAux V veq v2 (var V vf) b2)
                       | app _ _ _ => beq true false
                       end
                   | app _ l1 r1 =>
                       match t2 with
                       | var _ _ => beq true false
                       | lam _ _ _ => beq true false
                       | app _ l2 r2 =>
                           and (alphaEq fuel0 l1 l2) (alphaEq fuel0 r1 r2)
                       end
                   end
               end equ) trEqr)
       with
       | eq_refl =>
           match
             fuel as fuel0
             return
               ((fun fuel1 fuel₂0 : nat =>
                 BestR Coq_Init_Datatypes_nat_pmtcty_RR0 fuel1 fuel₂0 ->
                 (fun H H0 : Prop => BestRel H H0)
                   match fuel1 with
                   | 0%nat => beq true false
                   | S fuel2 =>
                       match t1 with
                       | var _ v1 =>
                           match t2 with
                           | var _ v2 => beq (veq v1 v2) true
                           | lam _ _ _ => beq true false
                           | app _ _ _ => beq true false
                           end
                       | lam _ v1 b1 =>
                           match t2 with
                           | var _ _ => beq true false
                           | lam _ v2 b2 =>
                               forall vf : V,
                               beq (inAllVarsOf V veq vf t1) false ->
                               beq (inAllVarsOf V veq vf t2) false ->
                               alphaEq fuel2
                                 (substAux V veq v1 (var V vf) b1)
                                 (substAux V veq v2 (var V vf) b2)
                           | app _ _ _ => beq true false
                           end
                       | app _ l1 r1 =>
                           match t2 with
                           | var _ _ => beq true false
                           | lam _ _ _ => beq true false
                           | app _ l2 r2 =>
                               and (alphaEq fuel2 l1 l2)
                                 (alphaEq fuel2 r1 r2)
                           end
                       end
                   end
                   match fuel₂0 with
                   | 0%nat => beq true false
                   | S fuel₂1 =>
                       match t1₂ with
                       | var _ v1₂ =>
                           match t2₂ with
                           | var _ v2₂ => beq (veq₂ v1₂ v2₂) true
                           | lam _ _ _ => beq true false
                           | app _ _ _ => beq true false
                           end
                       | lam _ v1₂ b1₂ =>
                           match t2₂ with
                           | var _ _ => beq true false
                           | lam _ v2₂ b2₂ =>
                               forall vf₂ : V₂,
                               beq (inAllVarsOf V₂ veq₂ vf₂ t1₂) false ->
                               beq (inAllVarsOf V₂ veq₂ vf₂ t2₂) false ->
                               alphaEq₂ fuel₂1
                                 (substAux V₂ veq₂ v1₂ (var V₂ vf₂) b1₂)
                                 (substAux V₂ veq₂ v2₂ (var V₂ vf₂) b2₂)
                           | app _ _ _ => beq true false
                           end
                       | app _ l1₂ r1₂ =>
                           match t2₂ with
                           | var _ _ => beq true false
                           | lam _ _ _ => beq true false
                           | app _ l2₂ r2₂ =>
                               and (alphaEq₂ fuel₂1 l1₂ l2₂)
                                 (alphaEq₂ fuel₂1 r1₂ r2₂)
                           end
                       end
                   end) fuel0 fuel₂)
           with
           | 0%nat =>
               match
                 fuel₂ as fuel₂0
                 return
                   ((fun fuel0 fuel₂1 : nat =>
                     BestR Coq_Init_Datatypes_nat_pmtcty_RR0 fuel0 fuel₂1 ->
                     (fun H H0 : Prop => BestRel H H0)
                       match fuel0 with
                       | 0%nat => beq true false
                       | S fuel1 =>
                           match t1 with
                           | var _ v1 =>
                               match t2 with
                               | var _ v2 => beq (veq v1 v2) true
                               | lam _ _ _ => beq true false
                               | app _ _ _ => beq true false
                               end
                           | lam _ v1 b1 =>
                               match t2 with
                               | var _ _ => beq true false
                               | lam _ v2 b2 =>
                                   forall vf : V,
                                   beq (inAllVarsOf V veq vf t1) false ->
                                   beq (inAllVarsOf V veq vf t2) false ->
                                   alphaEq fuel1
                                     (substAux V veq v1 (var V vf) b1)
                                     (substAux V veq v2 (var V vf) b2)
                               | app _ _ _ => beq true false
                               end
                           | app _ l1 r1 =>
                               match t2 with
                               | var _ _ => beq true false
                               | lam _ _ _ => beq true false
                               | app _ l2 r2 =>
                                   and (alphaEq fuel1 l1 l2)
                                     (alphaEq fuel1 r1 r2)
                               end
                           end
                       end
                       match fuel₂1 with
                       | 0%nat => beq true false
                       | S fuel₂2 =>
                           match t1₂ with
                           | var _ v1₂ =>
                               match t2₂ with
                               | var _ v2₂ => beq (veq₂ v1₂ v2₂) true
                               | lam _ _ _ => beq true false
                               | app _ _ _ => beq true false
                               end
                           | lam _ v1₂ b1₂ =>
                               match t2₂ with
                               | var _ _ => beq true false
                               | lam _ v2₂ b2₂ =>
                                   forall vf₂ : V₂,
                                   beq (inAllVarsOf V₂ veq₂ vf₂ t1₂) false ->
                                   beq (inAllVarsOf V₂ veq₂ vf₂ t2₂) false ->
                                   alphaEq₂ fuel₂2
                                     (substAux V₂ veq₂ v1₂ (var V₂ vf₂) b1₂)
                                     (substAux V₂ veq₂ v2₂ (var V₂ vf₂) b2₂)
                               | app _ _ _ => beq true false
                               end
                           | app _ l1₂ r1₂ =>
                               match t2₂ with
                               | var _ _ => beq true false
                               | lam _ _ _ => beq true false
                               | app _ l2₂ r2₂ =>
                                   and (alphaEq₂ fuel₂2 l1₂ l2₂)
                                     (alphaEq₂ fuel₂2 r1₂ r2₂)
                               end
                           end
                       end) 0%nat fuel₂0)
               with
               | 0%nat =>
                   fun
                     fuel_R0 : BestR Coq_Init_Datatypes_nat_pmtcty_RR0 0%nat
                                 0%nat =>
                   Coq_Init_Datatypes_nat_pmtcty_RR0_constr_0_inv fuel_R0
                     (fun
                        _ : BestR Coq_Init_Datatypes_nat_pmtcty_RR0 0%nat
                              0%nat =>
                      (fun H H0 : Prop => BestRel H H0)
                        match 0%nat with
                        | 0%nat => beq true false
                        | S fuel0 =>
                            match t1 with
                            | var _ v1 =>
                                match t2 with
                                | var _ v2 => beq (veq v1 v2) true
                                | lam _ _ _ => beq true false
                                | app _ _ _ => beq true false
                                end
                            | lam _ v1 b1 =>
                                match t2 with
                                | var _ _ => beq true false
                                | lam _ v2 b2 =>
                                    forall vf : V,
                                    beq (inAllVarsOf V veq vf t1) false ->
                                    beq (inAllVarsOf V veq vf t2) false ->
                                    alphaEq fuel0
                                      (substAux V veq v1 (var V vf) b1)
                                      (substAux V veq v2 (var V vf) b2)
                                | app _ _ _ => beq true false
                                end
                            | app _ l1 r1 =>
                                match t2 with
                                | var _ _ => beq true false
                                | lam _ _ _ => beq true false
                                | app _ l2 r2 =>
                                    and (alphaEq fuel0 l1 l2)
                                      (alphaEq fuel0 r1 r2)
                                end
                            end
                        end
                        match 0%nat with
                        | 0%nat => beq true false
                        | S fuel₂0 =>
                            match t1₂ with
                            | var _ v1₂ =>
                                match t2₂ with
                                | var _ v2₂ => beq (veq₂ v1₂ v2₂) true
                                | lam _ _ _ => beq true false
                                | app _ _ _ => beq true false
                                end
                            | lam _ v1₂ b1₂ =>
                                match t2₂ with
                                | var _ _ => beq true false
                                | lam _ v2₂ b2₂ =>
                                    forall vf₂ : V₂,
                                    beq (inAllVarsOf V₂ veq₂ vf₂ t1₂) false ->
                                    beq (inAllVarsOf V₂ veq₂ vf₂ t2₂) false ->
                                    alphaEq₂ fuel₂0
                                      (substAux V₂ veq₂ v1₂ (var V₂ vf₂) b1₂)
                                      (substAux V₂ veq₂ v2₂ (var V₂ vf₂) b2₂)
                                | app _ _ _ => beq true false
                                end
                            | app _ l1₂ r1₂ =>
                                match t2₂ with
                                | var _ _ => beq true false
                                | lam _ _ _ => beq true false
                                | app _ l2₂ r2₂ =>
                                    and (alphaEq₂ fuel₂0 l1₂ l2₂)
                                      (alphaEq₂ fuel₂0 r1₂ r2₂)
                                end
                            end
                        end)
                     (Top_alphaEquivariant_beq_pmtcty_RR true true
                        Coq_Init_Datatypes_bool_pmtcty_RR0_constr_0 false
                        false Coq_Init_Datatypes_bool_pmtcty_RR0_constr_1)
               | S fuel₂0 =>
                   fun
                     fuel_R0 : BestR Coq_Init_Datatypes_nat_pmtcty_RR0 0%nat
                                 (S fuel₂0) =>
                   match
                     fuel_R0
                     return
                       ((fun H H0 : Prop => BestRel H H0)
                          match 0%nat with
                          | 0%nat => beq true false
                          | S fuel0 =>
                              match t1 with
                              | var _ v1 =>
                                  match t2 with
                                  | var _ v2 => beq (veq v1 v2) true
                                  | lam _ _ _ => beq true false
                                  | app _ _ _ => beq true false
                                  end
                              | lam _ v1 b1 =>
                                  match t2 with
                                  | var _ _ => beq true false
                                  | lam _ v2 b2 =>
                                      forall vf : V,
                                      beq (inAllVarsOf V veq vf t1) false ->
                                      beq (inAllVarsOf V veq vf t2) false ->
                                      alphaEq fuel0
                                        (substAux V veq v1 (var V vf) b1)
                                        (substAux V veq v2 (var V vf) b2)
                                  | app _ _ _ => beq true false
                                  end
                              | app _ l1 r1 =>
                                  match t2 with
                                  | var _ _ => beq true false
                                  | lam _ _ _ => beq true false
                                  | app _ l2 r2 =>
                                      and (alphaEq fuel0 l1 l2)
                                        (alphaEq fuel0 r1 r2)
                                  end
                              end
                          end
                          match S fuel₂0 with
                          | 0%nat => beq true false
                          | S fuel₂1 =>
                              match t1₂ with
                              | var _ v1₂ =>
                                  match t2₂ with
                                  | var _ v2₂ => beq (veq₂ v1₂ v2₂) true
                                  | lam _ _ _ => beq true false
                                  | app _ _ _ => beq true false
                                  end
                              | lam _ v1₂ b1₂ =>
                                  match t2₂ with
                                  | var _ _ => beq true false
                                  | lam _ v2₂ b2₂ =>
                                      forall vf₂ : V₂,
                                      beq (inAllVarsOf V₂ veq₂ vf₂ t1₂) false ->
                                      beq (inAllVarsOf V₂ veq₂ vf₂ t2₂) false ->
                                      alphaEq₂ fuel₂1
                                        (substAux V₂ veq₂ v1₂ 
                                           (var V₂ vf₂) b1₂)
                                        (substAux V₂ veq₂ v2₂ 
                                           (var V₂ vf₂) b2₂)
                                  | app _ _ _ => beq true false
                                  end
                              | app _ l1₂ r1₂ =>
                                  match t2₂ with
                                  | var _ _ => beq true false
                                  | lam _ _ _ => beq true false
                                  | app _ l2₂ r2₂ =>
                                      and (alphaEq₂ fuel₂1 l1₂ l2₂)
                                        (alphaEq₂ fuel₂1 r1₂ r2₂)
                                  end
                              end
                          end)
                   with
                   end
               end
           | S fuel0 =>
               match
                 fuel₂ as fuel₂0
                 return
                   ((fun fuel1 fuel₂1 : nat =>
                     BestR Coq_Init_Datatypes_nat_pmtcty_RR0 fuel1 fuel₂1 ->
                     (fun H H0 : Prop => BestRel H H0)
                       match fuel1 with
                       | 0%nat => beq true false
                       | S fuel2 =>
                           match t1 with
                           | var _ v1 =>
                               match t2 with
                               | var _ v2 => beq (veq v1 v2) true
                               | lam _ _ _ => beq true false
                               | app _ _ _ => beq true false
                               end
                           | lam _ v1 b1 =>
                               match t2 with
                               | var _ _ => beq true false
                               | lam _ v2 b2 =>
                                   forall vf : V,
                                   beq (inAllVarsOf V veq vf t1) false ->
                                   beq (inAllVarsOf V veq vf t2) false ->
                                   alphaEq fuel2
                                     (substAux V veq v1 (var V vf) b1)
                                     (substAux V veq v2 (var V vf) b2)
                               | app _ _ _ => beq true false
                               end
                           | app _ l1 r1 =>
                               match t2 with
                               | var _ _ => beq true false
                               | lam _ _ _ => beq true false
                               | app _ l2 r2 =>
                                   and (alphaEq fuel2 l1 l2)
                                     (alphaEq fuel2 r1 r2)
                               end
                           end
                       end
                       match fuel₂1 with
                       | 0%nat => beq true false
                       | S fuel₂2 =>
                           match t1₂ with
                           | var _ v1₂ =>
                               match t2₂ with
                               | var _ v2₂ => beq (veq₂ v1₂ v2₂) true
                               | lam _ _ _ => beq true false
                               | app _ _ _ => beq true false
                               end
                           | lam _ v1₂ b1₂ =>
                               match t2₂ with
                               | var _ _ => beq true false
                               | lam _ v2₂ b2₂ =>
                                   forall vf₂ : V₂,
                                   beq (inAllVarsOf V₂ veq₂ vf₂ t1₂) false ->
                                   beq (inAllVarsOf V₂ veq₂ vf₂ t2₂) false ->
                                   alphaEq₂ fuel₂2
                                     (substAux V₂ veq₂ v1₂ (var V₂ vf₂) b1₂)
                                     (substAux V₂ veq₂ v2₂ (var V₂ vf₂) b2₂)
                               | app _ _ _ => beq true false
                               end
                           | app _ l1₂ r1₂ =>
                               match t2₂ with
                               | var _ _ => beq true false
                               | lam _ _ _ => beq true false
                               | app _ l2₂ r2₂ =>
                                   and (alphaEq₂ fuel₂2 l1₂ l2₂)
                                     (alphaEq₂ fuel₂2 r1₂ r2₂)
                               end
                           end
                       end) (S fuel0) fuel₂0)
               with
               | 0%nat =>
                   fun
                     fuel_R0 : BestR Coq_Init_Datatypes_nat_pmtcty_RR0
                                 (S fuel0) 0%nat =>
                   match
                     fuel_R0
                     return
                       ((fun H H0 : Prop => BestRel H H0)
                          match S fuel0 with
                          | 0%nat => beq true false
                          | S fuel1 =>
                              match t1 with
                              | var _ v1 =>
                                  match t2 with
                                  | var _ v2 => beq (veq v1 v2) true
                                  | lam _ _ _ => beq true false
                                  | app _ _ _ => beq true false
                                  end
                              | lam _ v1 b1 =>
                                  match t2 with
                                  | var _ _ => beq true false
                                  | lam _ v2 b2 =>
                                      forall vf : V,
                                      beq (inAllVarsOf V veq vf t1) false ->
                                      beq (inAllVarsOf V veq vf t2) false ->
                                      alphaEq fuel1
                                        (substAux V veq v1 (var V vf) b1)
                                        (substAux V veq v2 (var V vf) b2)
                                  | app _ _ _ => beq true false
                                  end
                              | app _ l1 r1 =>
                                  match t2 with
                                  | var _ _ => beq true false
                                  | lam _ _ _ => beq true false
                                  | app _ l2 r2 =>
                                      and (alphaEq fuel1 l1 l2)
                                        (alphaEq fuel1 r1 r2)
                                  end
                              end
                          end
                          match 0%nat with
                          | 0%nat => beq true false
                          | S fuel₂0 =>
                              match t1₂ with
                              | var _ v1₂ =>
                                  match t2₂ with
                                  | var _ v2₂ => beq (veq₂ v1₂ v2₂) true
                                  | lam _ _ _ => beq true false
                                  | app _ _ _ => beq true false
                                  end
                              | lam _ v1₂ b1₂ =>
                                  match t2₂ with
                                  | var _ _ => beq true false
                                  | lam _ v2₂ b2₂ =>
                                      forall vf₂ : V₂,
                                      beq (inAllVarsOf V₂ veq₂ vf₂ t1₂) false ->
                                      beq (inAllVarsOf V₂ veq₂ vf₂ t2₂) false ->
                                      alphaEq₂ fuel₂0
                                        (substAux V₂ veq₂ v1₂ 
                                           (var V₂ vf₂) b1₂)
                                        (substAux V₂ veq₂ v2₂ 
                                           (var V₂ vf₂) b2₂)
                                  | app _ _ _ => beq true false
                                  end
                              | app _ l1₂ r1₂ =>
                                  match t2₂ with
                                  | var _ _ => beq true false
                                  | lam _ _ _ => beq true false
                                  | app _ l2₂ r2₂ =>
                                      and (alphaEq₂ fuel₂0 l1₂ l2₂)
                                        (alphaEq₂ fuel₂0 r1₂ r2₂)
                                  end
                              end
                          end)
                   with
                   end
               | S fuel₂0 =>
                   fun
                     fuel_R0 : BestR Coq_Init_Datatypes_nat_pmtcty_RR0
                                 (S fuel0) (S fuel₂0) =>
                   Coq_Init_Datatypes_nat_pmtcty_RR0_constr_1_inv fuel0
                     fuel₂0 fuel_R0
                     (fun
                        _ : BestR Coq_Init_Datatypes_nat_pmtcty_RR0 
                              (S fuel0) (S fuel₂0) =>
                      (fun H H0 : Prop => BestRel H H0)
                        match S fuel0 with
                        | 0%nat => beq true false
                        | S fuel1 =>
                            match t1 with
                            | var _ v1 =>
                                match t2 with
                                | var _ v2 => beq (veq v1 v2) true
                                | lam _ _ _ => beq true false
                                | app _ _ _ => beq true false
                                end
                            | lam _ v1 b1 =>
                                match t2 with
                                | var _ _ => beq true false
                                | lam _ v2 b2 =>
                                    forall vf : V,
                                    beq (inAllVarsOf V veq vf t1) false ->
                                    beq (inAllVarsOf V veq vf t2) false ->
                                    alphaEq fuel1
                                      (substAux V veq v1 (var V vf) b1)
                                      (substAux V veq v2 (var V vf) b2)
                                | app _ _ _ => beq true false
                                end
                            | app _ l1 r1 =>
                                match t2 with
                                | var _ _ => beq true false
                                | lam _ _ _ => beq true false
                                | app _ l2 r2 =>
                                    and (alphaEq fuel1 l1 l2)
                                      (alphaEq fuel1 r1 r2)
                                end
                            end
                        end
                        match S fuel₂0 with
                        | 0%nat => beq true false
                        | S fuel₂1 =>
                            match t1₂ with
                            | var _ v1₂ =>
                                match t2₂ with
                                | var _ v2₂ => beq (veq₂ v1₂ v2₂) true
                                | lam _ _ _ => beq true false
                                | app _ _ _ => beq true false
                                end
                            | lam _ v1₂ b1₂ =>
                                match t2₂ with
                                | var _ _ => beq true false
                                | lam _ v2₂ b2₂ =>
                                    forall vf₂ : V₂,
                                    beq (inAllVarsOf V₂ veq₂ vf₂ t1₂) false ->
                                    beq (inAllVarsOf V₂ veq₂ vf₂ t2₂) false ->
                                    alphaEq₂ fuel₂1
                                      (substAux V₂ veq₂ v1₂ (var V₂ vf₂) b1₂)
                                      (substAux V₂ veq₂ v2₂ (var V₂ vf₂) b2₂)
                                | app _ _ _ => beq true false
                                end
                            | app _ l1₂ r1₂ =>
                                match t2₂ with
                                | var _ _ => beq true false
                                | lam _ _ _ => beq true false
                                | app _ l2₂ r2₂ =>
                                    and (alphaEq₂ fuel₂1 l1₂ l2₂)
                                      (alphaEq₂ fuel₂1 r1₂ r2₂)
                                end
                            end
                        end)
                     (fun
                        fuel_R1 : BestR Coq_Init_Datatypes_nat_pmtcty_RR0
                                    fuel0 fuel₂0 =>
                      match
                        t1 as t3
                        return
                          ((fun (t4 : Tm V) (t1₂0 : Tm V₂) =>
                            BestR
                              (Top_alphaEquivariant_Tm_pmtcty_RR0 V V₂ V_R)
                              t4 t1₂0 ->
                            (fun H H0 : Prop => BestRel H H0)
                              match t4 with
                              | var _ v1 =>
                                  match t2 with
                                  | var _ v2 => beq (veq v1 v2) true
                                  | lam _ _ _ => beq true false
                                  | app _ _ _ => beq true false
                                  end
                              | lam _ v1 b1 =>
                                  match t2 with
                                  | var _ _ => beq true false
                                  | lam _ v2 b2 =>
                                      forall vf : V,
                                      beq (inAllVarsOf V veq vf t1) false ->
                                      beq (inAllVarsOf V veq vf t2) false ->
                                      alphaEq fuel0
                                        (substAux V veq v1 (var V vf) b1)
                                        (substAux V veq v2 (var V vf) b2)
                                  | app _ _ _ => beq true false
                                  end
                              | app _ l1 r1 =>
                                  match t2 with
                                  | var _ _ => beq true false
                                  | lam _ _ _ => beq true false
                                  | app _ l2 r2 =>
                                      and (alphaEq fuel0 l1 l2)
                                        (alphaEq fuel0 r1 r2)
                                  end
                              end
                              match t1₂0 with
                              | var _ v1₂ =>
                                  match t2₂ with
                                  | var _ v2₂ => beq (veq₂ v1₂ v2₂) true
                                  | lam _ _ _ => beq true false
                                  | app _ _ _ => beq true false
                                  end
                              | lam _ v1₂ b1₂ =>
                                  match t2₂ with
                                  | var _ _ => beq true false
                                  | lam _ v2₂ b2₂ =>
                                      forall vf₂ : V₂,
                                      beq (inAllVarsOf V₂ veq₂ vf₂ t1₂) false ->
                                      beq (inAllVarsOf V₂ veq₂ vf₂ t2₂) false ->
                                      alphaEq₂ fuel₂0
                                        (substAux V₂ veq₂ v1₂ 
                                           (var V₂ vf₂) b1₂)
                                        (substAux V₂ veq₂ v2₂ 
                                           (var V₂ vf₂) b2₂)
                                  | app _ _ _ => beq true false
                                  end
                              | app _ l1₂ r1₂ =>
                                  match t2₂ with
                                  | var _ _ => beq true false
                                  | lam _ _ _ => beq true false
                                  | app _ l2₂ r2₂ =>
                                      and (alphaEq₂ fuel₂0 l1₂ l2₂)
                                        (alphaEq₂ fuel₂0 r1₂ r2₂)
                                  end
                              end) t3 t1₂)
                      with
                      | var _ v1 =>
                          match
                            t1₂ as t1₂0
                            return
                              ((fun (t3 : Tm V) (t1₂1 : Tm V₂) =>
                                BestR
                                  (Top_alphaEquivariant_Tm_pmtcty_RR0 V V₂
                                     V_R) t3 t1₂1 ->
                                (fun H H0 : Prop => BestRel H H0)
                                  match t3 with
                                  | var _ v2 =>
                                      match t2 with
                                      | var _ v3 => beq (veq v2 v3) true
                                      | lam _ _ _ => beq true false
                                      | app _ _ _ => beq true false
                                      end
                                  | lam _ v2 b1 =>
                                      match t2 with
                                      | var _ _ => beq true false
                                      | lam _ v3 b2 =>
                                          forall vf : V,
                                          beq (inAllVarsOf V veq vf t1) false ->
                                          beq (inAllVarsOf V veq vf t2) false ->
                                          alphaEq fuel0
                                            (substAux V veq v2 (var V vf) b1)
                                            (substAux V veq v3 (var V vf) b2)
                                      | app _ _ _ => beq true false
                                      end
                                  | app _ l1 r1 =>
                                      match t2 with
                                      | var _ _ => beq true false
                                      | lam _ _ _ => beq true false
                                      | app _ l2 r2 =>
                                          and (alphaEq fuel0 l1 l2)
                                            (alphaEq fuel0 r1 r2)
                                      end
                                  end
                                  match t1₂1 with
                                  | var _ v1₂ =>
                                      match t2₂ with
                                      | var _ v2₂ => beq (veq₂ v1₂ v2₂) true
                                      | lam _ _ _ => beq true false
                                      | app _ _ _ => beq true false
                                      end
                                  | lam _ v1₂ b1₂ =>
                                      match t2₂ with
                                      | var _ _ => beq true false
                                      | lam _ v2₂ b2₂ =>
                                          forall vf₂ : V₂,
                                          beq (inAllVarsOf V₂ veq₂ vf₂ t1₂)
                                            false ->
                                          beq (inAllVarsOf V₂ veq₂ vf₂ t2₂)
                                            false ->
                                          alphaEq₂ fuel₂0
                                            (substAux V₂ veq₂ v1₂
                                               (var V₂ vf₂) b1₂)
                                            (substAux V₂ veq₂ v2₂
                                               (var V₂ vf₂) b2₂)
                                      | app _ _ _ => beq true false
                                      end
                                  | app _ l1₂ r1₂ =>
                                      match t2₂ with
                                      | var _ _ => beq true false
                                      | lam _ _ _ => beq true false
                                      | app _ l2₂ r2₂ =>
                                          and (alphaEq₂ fuel₂0 l1₂ l2₂)
                                            (alphaEq₂ fuel₂0 r1₂ r2₂)
                                      end
                                  end) (var V v1) t1₂0)
                          with
                          | var _ v1₂ =>
                              fun
                                t1_R0 : BestR
                                          (Top_alphaEquivariant_Tm_pmtcty_RR0
                                             V V₂ V_R) 
                                          (var V v1) 
                                          (var V₂ v1₂) =>
                              Top_alphaEquivariant_Tm_pmtcty_RR0_constr_0_inv
                                V V₂ V_R v1 v1₂ t1_R0
                                (fun
                                   _ : BestR
                                         (Top_alphaEquivariant_Tm_pmtcty_RR0
                                            V V₂ V_R) 
                                         (var V v1) 
                                         (var V₂ v1₂) =>
                                 (fun H H0 : Prop => BestRel H H0)
                                   match var V v1 with
                                   | var _ v2 =>
                                       match t2 with
                                       | var _ v3 => beq (veq v2 v3) true
                                       | lam _ _ _ => beq true false
                                       | app _ _ _ => beq true false
                                       end
                                   | lam _ v2 b1 =>
                                       match t2 with
                                       | var _ _ => beq true false
                                       | lam _ v3 b2 =>
                                           forall vf : V,
                                           beq (inAllVarsOf V veq vf t1)
                                             false ->
                                           beq (inAllVarsOf V veq vf t2)
                                             false ->
                                           alphaEq fuel0
                                             (substAux V veq v2 (var V vf) b1)
                                             (substAux V veq v3 (var V vf) b2)
                                       | app _ _ _ => beq true false
                                       end
                                   | app _ l1 r1 =>
                                       match t2 with
                                       | var _ _ => beq true false
                                       | lam _ _ _ => beq true false
                                       | app _ l2 r2 =>
                                           and (alphaEq fuel0 l1 l2)
                                             (alphaEq fuel0 r1 r2)
                                       end
                                   end
                                   match var V₂ v1₂ with
                                   | var _ v1₂0 =>
                                       match t2₂ with
                                       | var _ v2₂ =>
                                           beq (veq₂ v1₂0 v2₂) true
                                       | lam _ _ _ => beq true false
                                       | app _ _ _ => beq true false
                                       end
                                   | lam _ v1₂0 b1₂ =>
                                       match t2₂ with
                                       | var _ _ => beq true false
                                       | lam _ v2₂ b2₂ =>
                                           forall vf₂ : V₂,
                                           beq (inAllVarsOf V₂ veq₂ vf₂ t1₂)
                                             false ->
                                           beq (inAllVarsOf V₂ veq₂ vf₂ t2₂)
                                             false ->
                                           alphaEq₂ fuel₂0
                                             (substAux V₂ veq₂ v1₂0
                                                (var V₂ vf₂) b1₂)
                                             (substAux V₂ veq₂ v2₂
                                                (var V₂ vf₂) b2₂)
                                       | app _ _ _ => beq true false
                                       end
                                   | app _ l1₂ r1₂ =>
                                       match t2₂ with
                                       | var _ _ => beq true false
                                       | lam _ _ _ => beq true false
                                       | app _ l2₂ r2₂ =>
                                           and (alphaEq₂ fuel₂0 l1₂ l2₂)
                                             (alphaEq₂ fuel₂0 r1₂ r2₂)
                                       end
                                   end)
                                (fun v1_R : BestR V_R v1 v1₂ =>
                                 match
                                   t2 as t3
                                   return
                                     ((fun (t4 : Tm V) (t2₂0 : Tm V₂) =>
                                       BestR
                                         (Top_alphaEquivariant_Tm_pmtcty_RR0
                                            V V₂ V_R) t4 t2₂0 ->
                                       (fun H H0 : Prop => BestRel H H0)
                                         match t4 with
                                         | var _ v2 => beq (veq v1 v2) true
                                         | lam _ _ _ => beq true false
                                         | app _ _ _ => beq true false
                                         end
                                         match t2₂0 with
                                         | var _ v2₂ =>
                                             beq (veq₂ v1₂ v2₂) true
                                         | lam _ _ _ => beq true false
                                         | app _ _ _ => beq true false
                                         end) t3 t2₂)
                                 with
                                 | var _ v2 =>
                                     match
                                       t2₂ as t2₂0
                                       return
                                         ((fun (t3 : Tm V) (t2₂1 : Tm V₂) =>
                                           BestR
                                             (Top_alphaEquivariant_Tm_pmtcty_RR0
                                                V V₂ V_R) t3 t2₂1 ->
                                           (fun H H0 : Prop => BestRel H H0)
                                             match t3 with
                                             | var _ v3 =>
                                                 beq (veq v1 v3) true
                                             | lam _ _ _ => beq true false
                                             | app _ _ _ => beq true false
                                             end
                                             match t2₂1 with
                                             | var _ v2₂ =>
                                                 beq (veq₂ v1₂ v2₂) true
                                             | lam _ _ _ => beq true false
                                             | app _ _ _ => beq true false
                                             end) 
                                            (var V v2) t2₂0)
                                     with
                                     | var _ v2₂ =>
                                         fun
                                           t2_R0 : 
                                            BestR
                                              (Top_alphaEquivariant_Tm_pmtcty_RR0
                                                 V V₂ V_R) 
                                              (var V v2) 
                                              (var V₂ v2₂) =>
                                         Top_alphaEquivariant_Tm_pmtcty_RR0_constr_0_inv
                                           V V₂ V_R v2 v2₂ t2_R0
                                           (fun
                                              _ : 
                                               BestR
                                                 (Top_alphaEquivariant_Tm_pmtcty_RR0
                                                 V V₂ V_R) 
                                                 (var V v2) 
                                                 (var V₂ v2₂) =>
                                            (fun H H0 : Prop => BestRel H H0)
                                              match var V v2 with
                                              | var _ v3 =>
                                                 beq (veq v1 v3) true
                                              | lam _ _ _ => beq true false
                                              | app _ _ _ => beq true false
                                              end
                                              match var V₂ v2₂ with
                                              | var _ v2₂0 =>
                                                 beq (veq₂ v1₂ v2₂0) true
                                              | lam _ _ _ => beq true false
                                              | app _ _ _ => beq true false
                                              end)
                                           (fun v2_R : BestR V_R v2 v2₂ =>
                                            Top_alphaEquivariant_beq_pmtcty_RR
                                              (veq v1 v2) 
                                              (veq₂ v1₂ v2₂)
                                              (veq_R v1 v1₂ v1_R v2 v2₂ v2_R)
                                              true true
                                              Coq_Init_Datatypes_bool_pmtcty_RR0_constr_0)
                                     | lam _ v₂ t₂ =>
                                         fun
                                           t2_R0 : 
                                            BestR
                                              (Top_alphaEquivariant_Tm_pmtcty_RR0
                                                 V V₂ V_R) 
                                              (var V v2) 
                                              (lam V₂ v₂ t₂) =>
                                         match
                                           t2_R0
                                           return
                                             ((fun H H0 : Prop =>
                                               BestRel H H0)
                                                match var V v2 with
                                                | var _ v3 =>
                                                 beq (veq v1 v3) true
                                                | lam _ _ _ => beq true false
                                                | app _ _ _ => beq true false
                                                end
                                                match lam V₂ v₂ t₂ with
                                                | var _ v2₂ =>
                                                 beq (veq₂ v1₂ v2₂) true
                                                | lam _ _ _ => beq true false
                                                | app _ _ _ => beq true false
                                                end)
                                         with
                                         end
                                     | app _ t₂ t0₂ =>
                                         fun
                                           t2_R0 : 
                                            BestR
                                              (Top_alphaEquivariant_Tm_pmtcty_RR0
                                                 V V₂ V_R) 
                                              (var V v2) 
                                              (app V₂ t₂ t0₂) =>
                                         match
                                           t2_R0
                                           return
                                             ((fun H H0 : Prop =>
                                               BestRel H H0)
                                                match var V v2 with
                                                | var _ v3 =>
                                                 beq (veq v1 v3) true
                                                | lam _ _ _ => beq true false
                                                | app _ _ _ => beq true false
                                                end
                                                match app V₂ t₂ t0₂ with
                                                | var _ v2₂ =>
                                                 beq (veq₂ v1₂ v2₂) true
                                                | lam _ _ _ => beq true false
                                                | app _ _ _ => beq true false
                                                end)
                                         with
                                         end
                                     end
                                 | lam _ v t =>
                                     match
                                       t2₂ as t2₂0
                                       return
                                         ((fun (t3 : Tm V) (t2₂1 : Tm V₂) =>
                                           BestR
                                             (Top_alphaEquivariant_Tm_pmtcty_RR0
                                                V V₂ V_R) t3 t2₂1 ->
                                           (fun H H0 : Prop => BestRel H H0)
                                             match t3 with
                                             | var _ v2 =>
                                                 beq (veq v1 v2) true
                                             | lam _ _ _ => beq true false
                                             | app _ _ _ => beq true false
                                             end
                                             match t2₂1 with
                                             | var _ v2₂ =>
                                                 beq (veq₂ v1₂ v2₂) true
                                             | lam _ _ _ => beq true false
                                             | app _ _ _ => beq true false
                                             end) 
                                            (lam V v t) t2₂0)
                                     with
                                     | var _ v2₂ =>
                                         fun
                                           t2_R0 : 
                                            BestR
                                              (Top_alphaEquivariant_Tm_pmtcty_RR0
                                                 V V₂ V_R) 
                                              (lam V v t) 
                                              (var V₂ v2₂) =>
                                         match
                                           t2_R0
                                           return
                                             ((fun H H0 : Prop =>
                                               BestRel H H0)
                                                match lam V v t with
                                                | var _ v2 =>
                                                 beq (veq v1 v2) true
                                                | lam _ _ _ => beq true false
                                                | app _ _ _ => beq true false
                                                end
                                                match var V₂ v2₂ with
                                                | var _ v2₂0 =>
                                                 beq (veq₂ v1₂ v2₂0) true
                                                | lam _ _ _ => beq true false
                                                | app _ _ _ => beq true false
                                                end)
                                         with
                                         end
                                     | lam _ v₂ t₂ =>
                                         fun
                                           t2_R0 : 
                                            BestR
                                              (Top_alphaEquivariant_Tm_pmtcty_RR0
                                                 V V₂ V_R) 
                                              (lam V v t) 
                                              (lam V₂ v₂ t₂) =>
                                         Top_alphaEquivariant_Tm_pmtcty_RR0_constr_1_inv
                                           V V₂ V_R v v₂ t t₂ t2_R0
                                           (fun
                                              _ : 
                                               BestR
                                                 (Top_alphaEquivariant_Tm_pmtcty_RR0
                                                 V V₂ V_R) 
                                                 (lam V v t) 
                                                 (lam V₂ v₂ t₂) =>
                                            (fun H H0 : Prop => BestRel H H0)
                                              match lam V v t with
                                              | var _ v2 =>
                                                 beq (veq v1 v2) true
                                              | lam _ _ _ => beq true false
                                              | app _ _ _ => beq true false
                                              end
                                              match lam V₂ v₂ t₂ with
                                              | var _ v2₂ =>
                                                 beq (veq₂ v1₂ v2₂) true
                                              | lam _ _ _ => beq true false
                                              | app _ _ _ => beq true false
                                              end)
                                           (fun (_ : BestR V_R v v₂)
                                              (_ : 
                                               BestR
                                                 (Top_alphaEquivariant_Tm_pmtcty_RR0
                                                 V V₂ V_R) t t₂) =>
                                            Top_alphaEquivariant_beq_pmtcty_RR
                                              true true
                                              Coq_Init_Datatypes_bool_pmtcty_RR0_constr_0
                                              false false
                                              Coq_Init_Datatypes_bool_pmtcty_RR0_constr_1)
                                     | app _ t₂ t0₂ =>
                                         fun
                                           t2_R0 : 
                                            BestR
                                              (Top_alphaEquivariant_Tm_pmtcty_RR0
                                                 V V₂ V_R) 
                                              (lam V v t) 
                                              (app V₂ t₂ t0₂) =>
                                         match
                                           t2_R0
                                           return
                                             ((fun H H0 : Prop =>
                                               BestRel H H0)
                                                match lam V v t with
                                                | var _ v2 =>
                                                 beq (veq v1 v2) true
                                                | lam _ _ _ => beq true false
                                                | app _ _ _ => beq true false
                                                end
                                                match app V₂ t₂ t0₂ with
                                                | var _ v2₂ =>
                                                 beq (veq₂ v1₂ v2₂) true
                                                | lam _ _ _ => beq true false
                                                | app _ _ _ => beq true false
                                                end)
                                         with
                                         end
                                     end
                                 | app _ t t0 =>
                                     match
                                       t2₂ as t2₂0
                                       return
                                         ((fun (t3 : Tm V) (t2₂1 : Tm V₂) =>
                                           BestR
                                             (Top_alphaEquivariant_Tm_pmtcty_RR0
                                                V V₂ V_R) t3 t2₂1 ->
                                           (fun H H0 : Prop => BestRel H H0)
                                             match t3 with
                                             | var _ v2 =>
                                                 beq (veq v1 v2) true
                                             | lam _ _ _ => beq true false
                                             | app _ _ _ => beq true false
                                             end
                                             match t2₂1 with
                                             | var _ v2₂ =>
                                                 beq (veq₂ v1₂ v2₂) true
                                             | lam _ _ _ => beq true false
                                             | app _ _ _ => beq true false
                                             end) 
                                            (app V t t0) t2₂0)
                                     with
                                     | var _ v2₂ =>
                                         fun
                                           t2_R0 : 
                                            BestR
                                              (Top_alphaEquivariant_Tm_pmtcty_RR0
                                                 V V₂ V_R) 
                                              (app V t t0) 
                                              (var V₂ v2₂) =>
                                         match
                                           t2_R0
                                           return
                                             ((fun H H0 : Prop =>
                                               BestRel H H0)
                                                match app V t t0 with
                                                | var _ v2 =>
                                                 beq (veq v1 v2) true
                                                | lam _ _ _ => beq true false
                                                | app _ _ _ => beq true false
                                                end
                                                match var V₂ v2₂ with
                                                | var _ v2₂0 =>
                                                 beq (veq₂ v1₂ v2₂0) true
                                                | lam _ _ _ => beq true false
                                                | app _ _ _ => beq true false
                                                end)
                                         with
                                         end
                                     | lam _ v₂ t₂ =>
                                         fun
                                           t2_R0 : 
                                            BestR
                                              (Top_alphaEquivariant_Tm_pmtcty_RR0
                                                 V V₂ V_R) 
                                              (app V t t0) 
                                              (lam V₂ v₂ t₂) =>
                                         match
                                           t2_R0
                                           return
                                             ((fun H H0 : Prop =>
                                               BestRel H H0)
                                                match app V t t0 with
                                                | var _ v2 =>
                                                 beq (veq v1 v2) true
                                                | lam _ _ _ => beq true false
                                                | app _ _ _ => beq true false
                                                end
                                                match lam V₂ v₂ t₂ with
                                                | var _ v2₂ =>
                                                 beq (veq₂ v1₂ v2₂) true
                                                | lam _ _ _ => beq true false
                                                | app _ _ _ => beq true false
                                                end)
                                         with
                                         end
                                     | app _ t₂ t0₂ =>
                                         fun
                                           t2_R0 : 
                                            BestR
                                              (Top_alphaEquivariant_Tm_pmtcty_RR0
                                                 V V₂ V_R) 
                                              (app V t t0) 
                                              (app V₂ t₂ t0₂) =>
                                         Top_alphaEquivariant_Tm_pmtcty_RR0_constr_2_inv
                                           V V₂ V_R t t₂ t0 t0₂ t2_R0
                                           (fun
                                              _ : 
                                               BestR
                                                 (Top_alphaEquivariant_Tm_pmtcty_RR0
                                                 V V₂ V_R) 
                                                 (app V t t0) 
                                                 (app V₂ t₂ t0₂) =>
                                            (fun H H0 : Prop => BestRel H H0)
                                              match app V t t0 with
                                              | var _ v2 =>
                                                 beq (veq v1 v2) true
                                              | lam _ _ _ => beq true false
                                              | app _ _ _ => beq true false
                                              end
                                              match app V₂ t₂ t0₂ with
                                              | var _ v2₂ =>
                                                 beq (veq₂ v1₂ v2₂) true
                                              | lam _ _ _ => beq true false
                                              | app _ _ _ => beq true false
                                              end)
                                           (fun
                                              (_ : 
                                               BestR
                                                 (Top_alphaEquivariant_Tm_pmtcty_RR0
                                                 V V₂ V_R) t t₂)
                                              (_ : 
                                               BestR
                                                 (Top_alphaEquivariant_Tm_pmtcty_RR0
                                                 V V₂ V_R) t0 t0₂) =>
                                            Top_alphaEquivariant_beq_pmtcty_RR
                                              true true
                                              Coq_Init_Datatypes_bool_pmtcty_RR0_constr_0
                                              false false
                                              Coq_Init_Datatypes_bool_pmtcty_RR0_constr_1)
                                     end
                                 end t2_R)
                          | lam _ v1₂ b1₂ =>
                              fun
                                t1_R0 : BestR
                                          (Top_alphaEquivariant_Tm_pmtcty_RR0
                                             V V₂ V_R) 
                                          (var V v1) 
                                          (lam V₂ v1₂ b1₂) =>
                              match
                                t1_R0
                                return
                                  ((fun H H0 : Prop => BestRel H H0)
                                     match var V v1 with
                                     | var _ v2 =>
                                         match t2 with
                                         | var _ v3 => beq (veq v2 v3) true
                                         | lam _ _ _ => beq true false
                                         | app _ _ _ => beq true false
                                         end
                                     | lam _ v2 b1 =>
                                         match t2 with
                                         | var _ _ => beq true false
                                         | lam _ v3 b2 =>
                                             forall vf : V,
                                             beq (inAllVarsOf V veq vf t1)
                                               false ->
                                             beq (inAllVarsOf V veq vf t2)
                                               false ->
                                             alphaEq fuel0
                                               (substAux V veq v2 
                                                 (var V vf) b1)
                                               (substAux V veq v3 
                                                 (var V vf) b2)
                                         | app _ _ _ => beq true false
                                         end
                                     | app _ l1 r1 =>
                                         match t2 with
                                         | var _ _ => beq true false
                                         | lam _ _ _ => beq true false
                                         | app _ l2 r2 =>
                                             and (alphaEq fuel0 l1 l2)
                                               (alphaEq fuel0 r1 r2)
                                         end
                                     end
                                     match lam V₂ v1₂ b1₂ with
                                     | var _ v1₂0 =>
                                         match t2₂ with
                                         | var _ v2₂ =>
                                             beq (veq₂ v1₂0 v2₂) true
                                         | lam _ _ _ => beq true false
                                         | app _ _ _ => beq true false
                                         end
                                     | lam _ v1₂0 b1₂0 =>
                                         match t2₂ with
                                         | var _ _ => beq true false
                                         | lam _ v2₂ b2₂ =>
                                             forall vf₂ : V₂,
                                             beq
                                               (inAllVarsOf V₂ veq₂ vf₂ t1₂)
                                               false ->
                                             beq
                                               (inAllVarsOf V₂ veq₂ vf₂ t2₂)
                                               false ->
                                             alphaEq₂ fuel₂0
                                               (substAux V₂ veq₂ v1₂0
                                                 (var V₂ vf₂) b1₂0)
                                               (substAux V₂ veq₂ v2₂
                                                 (var V₂ vf₂) b2₂)
                                         | app _ _ _ => beq true false
                                         end
                                     | app _ l1₂ r1₂ =>
                                         match t2₂ with
                                         | var _ _ => beq true false
                                         | lam _ _ _ => beq true false
                                         | app _ l2₂ r2₂ =>
                                             and (alphaEq₂ fuel₂0 l1₂ l2₂)
                                               (alphaEq₂ fuel₂0 r1₂ r2₂)
                                         end
                                     end)
                              with
                              end
                          | app _ l1₂ r1₂ =>
                              fun
                                t1_R0 : BestR
                                          (Top_alphaEquivariant_Tm_pmtcty_RR0
                                             V V₂ V_R) 
                                          (var V v1) 
                                          (app V₂ l1₂ r1₂) =>
                              match
                                t1_R0
                                return
                                  ((fun H H0 : Prop => BestRel H H0)
                                     match var V v1 with
                                     | var _ v2 =>
                                         match t2 with
                                         | var _ v3 => beq (veq v2 v3) true
                                         | lam _ _ _ => beq true false
                                         | app _ _ _ => beq true false
                                         end
                                     | lam _ v2 b1 =>
                                         match t2 with
                                         | var _ _ => beq true false
                                         | lam _ v3 b2 =>
                                             forall vf : V,
                                             beq (inAllVarsOf V veq vf t1)
                                               false ->
                                             beq (inAllVarsOf V veq vf t2)
                                               false ->
                                             alphaEq fuel0
                                               (substAux V veq v2 
                                                 (var V vf) b1)
                                               (substAux V veq v3 
                                                 (var V vf) b2)
                                         | app _ _ _ => beq true false
                                         end
                                     | app _ l1 r1 =>
                                         match t2 with
                                         | var _ _ => beq true false
                                         | lam _ _ _ => beq true false
                                         | app _ l2 r2 =>
                                             and (alphaEq fuel0 l1 l2)
                                               (alphaEq fuel0 r1 r2)
                                         end
                                     end
                                     match app V₂ l1₂ r1₂ with
                                     | var _ v1₂ =>
                                         match t2₂ with
                                         | var _ v2₂ =>
                                             beq (veq₂ v1₂ v2₂) true
                                         | lam _ _ _ => beq true false
                                         | app _ _ _ => beq true false
                                         end
                                     | lam _ v1₂ b1₂ =>
                                         match t2₂ with
                                         | var _ _ => beq true false
                                         | lam _ v2₂ b2₂ =>
                                             forall vf₂ : V₂,
                                             beq
                                               (inAllVarsOf V₂ veq₂ vf₂ t1₂)
                                               false ->
                                             beq
                                               (inAllVarsOf V₂ veq₂ vf₂ t2₂)
                                               false ->
                                             alphaEq₂ fuel₂0
                                               (substAux V₂ veq₂ v1₂
                                                 (var V₂ vf₂) b1₂)
                                               (substAux V₂ veq₂ v2₂
                                                 (var V₂ vf₂) b2₂)
                                         | app _ _ _ => beq true false
                                         end
                                     | app _ l1₂0 r1₂0 =>
                                         match t2₂ with
                                         | var _ _ => beq true false
                                         | lam _ _ _ => beq true false
                                         | app _ l2₂ r2₂ =>
                                             and (alphaEq₂ fuel₂0 l1₂0 l2₂)
                                               (alphaEq₂ fuel₂0 r1₂0 r2₂)
                                         end
                                     end)
                              with
                              end
                          end
                      | lam _ v1 b1 =>
                          match
                            t1₂ as t1₂0
                            return
                              ((fun (t3 : Tm V) (t1₂1 : Tm V₂) =>
                                BestR
                                  (Top_alphaEquivariant_Tm_pmtcty_RR0 V V₂
                                     V_R) t3 t1₂1 ->
                                (fun H H0 : Prop => BestRel H H0)
                                  match t3 with
                                  | var _ v2 =>
                                      match t2 with
                                      | var _ v3 => beq (veq v2 v3) true
                                      | lam _ _ _ => beq true false
                                      | app _ _ _ => beq true false
                                      end
                                  | lam _ v2 b2 =>
                                      match t2 with
                                      | var _ _ => beq true false
                                      | lam _ v3 b3 =>
                                          forall vf : V,
                                          beq (inAllVarsOf V veq vf t1) false ->
                                          beq (inAllVarsOf V veq vf t2) false ->
                                          alphaEq fuel0
                                            (substAux V veq v2 (var V vf) b2)
                                            (substAux V veq v3 (var V vf) b3)
                                      | app _ _ _ => beq true false
                                      end
                                  | app _ l1 r1 =>
                                      match t2 with
                                      | var _ _ => beq true false
                                      | lam _ _ _ => beq true false
                                      | app _ l2 r2 =>
                                          and (alphaEq fuel0 l1 l2)
                                            (alphaEq fuel0 r1 r2)
                                      end
                                  end
                                  match t1₂1 with
                                  | var _ v1₂ =>
                                      match t2₂ with
                                      | var _ v2₂ => beq (veq₂ v1₂ v2₂) true
                                      | lam _ _ _ => beq true false
                                      | app _ _ _ => beq true false
                                      end
                                  | lam _ v1₂ b1₂ =>
                                      match t2₂ with
                                      | var _ _ => beq true false
                                      | lam _ v2₂ b2₂ =>
                                          forall vf₂ : V₂,
                                          beq (inAllVarsOf V₂ veq₂ vf₂ t1₂)
                                            false ->
                                          beq (inAllVarsOf V₂ veq₂ vf₂ t2₂)
                                            false ->
                                          alphaEq₂ fuel₂0
                                            (substAux V₂ veq₂ v1₂
                                               (var V₂ vf₂) b1₂)
                                            (substAux V₂ veq₂ v2₂
                                               (var V₂ vf₂) b2₂)
                                      | app _ _ _ => beq true false
                                      end
                                  | app _ l1₂ r1₂ =>
                                      match t2₂ with
                                      | var _ _ => beq true false
                                      | lam _ _ _ => beq true false
                                      | app _ l2₂ r2₂ =>
                                          and (alphaEq₂ fuel₂0 l1₂ l2₂)
                                            (alphaEq₂ fuel₂0 r1₂ r2₂)
                                      end
                                  end) (lam V v1 b1) t1₂0)
                          with
                          | var _ v1₂ =>
                              fun
                                t1_R0 : BestR
                                          (Top_alphaEquivariant_Tm_pmtcty_RR0
                                             V V₂ V_R) 
                                          (lam V v1 b1) 
                                          (var V₂ v1₂) =>
                              match
                                t1_R0
                                return
                                  ((fun H H0 : Prop => BestRel H H0)
                                     match lam V v1 b1 with
                                     | var _ v2 =>
                                         match t2 with
                                         | var _ v3 => beq (veq v2 v3) true
                                         | lam _ _ _ => beq true false
                                         | app _ _ _ => beq true false
                                         end
                                     | lam _ v2 b2 =>
                                         match t2 with
                                         | var _ _ => beq true false
                                         | lam _ v3 b3 =>
                                             forall vf : V,
                                             beq (inAllVarsOf V veq vf t1)
                                               false ->
                                             beq (inAllVarsOf V veq vf t2)
                                               false ->
                                             alphaEq fuel0
                                               (substAux V veq v2 
                                                 (var V vf) b2)
                                               (substAux V veq v3 
                                                 (var V vf) b3)
                                         | app _ _ _ => beq true false
                                         end
                                     | app _ l1 r1 =>
                                         match t2 with
                                         | var _ _ => beq true false
                                         | lam _ _ _ => beq true false
                                         | app _ l2 r2 =>
                                             and (alphaEq fuel0 l1 l2)
                                               (alphaEq fuel0 r1 r2)
                                         end
                                     end
                                     match var V₂ v1₂ with
                                     | var _ v1₂0 =>
                                         match t2₂ with
                                         | var _ v2₂ =>
                                             beq (veq₂ v1₂0 v2₂) true
                                         | lam _ _ _ => beq true false
                                         | app _ _ _ => beq true false
                                         end
                                     | lam _ v1₂0 b1₂ =>
                                         match t2₂ with
                                         | var _ _ => beq true false
                                         | lam _ v2₂ b2₂ =>
                                             forall vf₂ : V₂,
                                             beq
                                               (inAllVarsOf V₂ veq₂ vf₂ t1₂)
                                               false ->
                                             beq
                                               (inAllVarsOf V₂ veq₂ vf₂ t2₂)
                                               false ->
                                             alphaEq₂ fuel₂0
                                               (substAux V₂ veq₂ v1₂0
                                                 (var V₂ vf₂) b1₂)
                                               (substAux V₂ veq₂ v2₂
                                                 (var V₂ vf₂) b2₂)
                                         | app _ _ _ => beq true false
                                         end
                                     | app _ l1₂ r1₂ =>
                                         match t2₂ with
                                         | var _ _ => beq true false
                                         | lam _ _ _ => beq true false
                                         | app _ l2₂ r2₂ =>
                                             and (alphaEq₂ fuel₂0 l1₂ l2₂)
                                               (alphaEq₂ fuel₂0 r1₂ r2₂)
                                         end
                                     end)
                              with
                              end
                          | lam _ v1₂ b1₂ =>
                              fun
                                t1_R0 : BestR
                                          (Top_alphaEquivariant_Tm_pmtcty_RR0
                                             V V₂ V_R) 
                                          (lam V v1 b1) 
                                          (lam V₂ v1₂ b1₂) =>
                              Top_alphaEquivariant_Tm_pmtcty_RR0_constr_1_inv
                                V V₂ V_R v1 v1₂ b1 b1₂ t1_R0
                                (fun
                                   _ : BestR
                                         (Top_alphaEquivariant_Tm_pmtcty_RR0
                                            V V₂ V_R) 
                                         (lam V v1 b1) 
                                         (lam V₂ v1₂ b1₂) =>
                                 (fun H H0 : Prop => BestRel H H0)
                                   match lam V v1 b1 with
                                   | var _ v2 =>
                                       match t2 with
                                       | var _ v3 => beq (veq v2 v3) true
                                       | lam _ _ _ => beq true false
                                       | app _ _ _ => beq true false
                                       end
                                   | lam _ v2 b2 =>
                                       match t2 with
                                       | var _ _ => beq true false
                                       | lam _ v3 b3 =>
                                           forall vf : V,
                                           beq (inAllVarsOf V veq vf t1)
                                             false ->
                                           beq (inAllVarsOf V veq vf t2)
                                             false ->
                                           alphaEq fuel0
                                             (substAux V veq v2 (var V vf) b2)
                                             (substAux V veq v3 (var V vf) b3)
                                       | app _ _ _ => beq true false
                                       end
                                   | app _ l1 r1 =>
                                       match t2 with
                                       | var _ _ => beq true false
                                       | lam _ _ _ => beq true false
                                       | app _ l2 r2 =>
                                           and (alphaEq fuel0 l1 l2)
                                             (alphaEq fuel0 r1 r2)
                                       end
                                   end
                                   match lam V₂ v1₂ b1₂ with
                                   | var _ v1₂0 =>
                                       match t2₂ with
                                       | var _ v2₂ =>
                                           beq (veq₂ v1₂0 v2₂) true
                                       | lam _ _ _ => beq true false
                                       | app _ _ _ => beq true false
                                       end
                                   | lam _ v1₂0 b1₂0 =>
                                       match t2₂ with
                                       | var _ _ => beq true false
                                       | lam _ v2₂ b2₂ =>
                                           forall vf₂ : V₂,
                                           beq (inAllVarsOf V₂ veq₂ vf₂ t1₂)
                                             false ->
                                           beq (inAllVarsOf V₂ veq₂ vf₂ t2₂)
                                             false ->
                                           alphaEq₂ fuel₂0
                                             (substAux V₂ veq₂ v1₂0
                                                (var V₂ vf₂) b1₂0)
                                             (substAux V₂ veq₂ v2₂
                                                (var V₂ vf₂) b2₂)
                                       | app _ _ _ => beq true false
                                       end
                                   | app _ l1₂ r1₂ =>
                                       match t2₂ with
                                       | var _ _ => beq true false
                                       | lam _ _ _ => beq true false
                                       | app _ l2₂ r2₂ =>
                                           and (alphaEq₂ fuel₂0 l1₂ l2₂)
                                             (alphaEq₂ fuel₂0 r1₂ r2₂)
                                       end
                                   end)
                                (fun (v1_R : BestR V_R v1 v1₂)
                                   (b1_R : BestR
                                             (Top_alphaEquivariant_Tm_pmtcty_RR0
                                                V V₂ V_R) b1 b1₂) =>
                                 match
                                   t2 as t3
                                   return
                                     ((fun (t4 : Tm V) (t2₂0 : Tm V₂) =>
                                       BestR
                                         (Top_alphaEquivariant_Tm_pmtcty_RR0
                                            V V₂ V_R) t4 t2₂0 ->
                                       (fun H H0 : Prop => BestRel H H0)
                                         match t4 with
                                         | var _ _ => beq true false
                                         | lam _ v2 b2 =>
                                             forall vf : V,
                                             beq (inAllVarsOf V veq vf t1)
                                               false ->
                                             beq (inAllVarsOf V veq vf t2)
                                               false ->
                                             alphaEq fuel0
                                               (substAux V veq v1 ... b1)
                                               (substAux V veq v2 ... b2)
                                         | app _ _ _ => beq true false
                                         end
                                         match t2₂0 with
                                         | var _ _ => beq true false
                                         | lam _ v2₂ b2₂ =>
                                             forall vf₂ : V₂,
                                             beq
                                               (inAllVarsOf V₂ veq₂ vf₂ t1₂)
                                               false ->
                                             beq
                                               (inAllVarsOf V₂ veq₂ vf₂ t2₂)
                                               false ->
                                             alphaEq₂ fuel₂0
                                               (substAux V₂ veq₂ v1₂ ... b1₂)
                                               (substAux V₂ veq₂ v2₂ ... b2₂)
                                         | app _ _ _ => beq true false
                                         end) t3 t2₂)
                                 with
                                 | var _ v =>
                                     match
                                       t2₂ as t2₂0
                                       return
                                         ((fun (t3 : Tm V) (t2₂1 : Tm V₂) =>
                                           BestR
                                             (Top_alphaEquivariant_Tm_pmtcty_RR0
                                                V V₂ V_R) t3 t2₂1 ->
                                           (fun H H0 : Prop => BestRel H H0)
                                             match t3 with
                                             | var _ _ => beq true false
                                             | lam _ v2 b2 =>
                                                 forall vf : V,
                                                 beq (...) false ->
                                                 beq ... false ->
                                                 alphaEq fuel0 ... ...
                                             | app _ _ _ => beq true false
                                             end
                                             match t2₂1 with
                                             | var _ _ => beq true false
                                             | lam _ v2₂ b2₂ =>
                                                 forall vf₂ : V₂,
                                                 beq (...) false ->
                                                 beq ... false ->
                                                 alphaEq₂ fuel₂0 ... ...
                                             | app _ _ _ => beq true false
                                             end) 
                                            (var V v) t2₂0)
                                     with
                                     | var _ v₂ =>
                                         fun
                                           t2_R0 : 
                                            BestR
                                              (Top_alphaEquivariant_Tm_pmtcty_RR0
                                                 V V₂ V_R) 
                                              (var V v) 
                                              (var V₂ v₂) =>
                                         Top_alphaEquivariant_Tm_pmtcty_RR0_constr_0_inv
                                           V V₂ V_R v v₂ t2_R0
                                           (fun
                                              _ : 
                                               BestR
                                                 (Top_alphaEquivariant_Tm_pmtcty_RR0
                                                 V V₂ V_R) 
                                                 (var V v) 
                                                 (var V₂ v₂) =>
                                            (fun H H0 : Prop => BestRel H H0)
                                              match var V v with
                                              | var _ _ => beq true false
                                              | lam _ v2 b2 =>
                                                 forall vf : V,
                                                 beq
                                                 (inAllVarsOf V veq vf t1)
                                                 false ->
                                                 beq
                                                 (inAllVarsOf V veq vf t2)
                                                 false ->
                                                 alphaEq fuel0
                                                 (substAux V veq v1 (...) b1)
                                                 (substAux V veq v2 (...) b2)
                                              | app _ _ _ => beq true false
                                              end
                                              match var V₂ v₂ with
                                              | var _ _ => beq true false
                                              | lam _ v2₂ b2₂ =>
                                                 forall vf₂ : V₂,
                                                 beq
                                                 (inAllVarsOf V₂ veq₂ vf₂ t1₂)
                                                 false ->
                                                 beq
                                                 (inAllVarsOf V₂ veq₂ vf₂ t2₂)
                                                 false ->
                                                 alphaEq₂ fuel₂0
                                                 (substAux V₂ veq₂ v1₂ 
                                                 (...) b1₂)
                                                 (substAux V₂ veq₂ v2₂ 
                                                 (...) b2₂)
                                              | app _ _ _ => beq true false
                                              end)
                                           (fun _ : BestR V_R v v₂ =>
                                            Top_alphaEquivariant_beq_pmtcty_RR
                                              true true
                                              Coq_Init_Datatypes_bool_pmtcty_RR0_constr_0
                                              false false
                                              Coq_Init_Datatypes_bool_pmtcty_RR0_constr_1)
                                     | lam _ v2₂ b2₂ =>
                                         fun
                                           t2_R0 : 
                                            BestR
                                              (Top_alphaEquivariant_Tm_pmtcty_RR0
                                                 V V₂ V_R) 
                                              (var V v) 
                                              (lam V₂ v2₂ b2₂) =>
                                         match
                                           t2_R0
                                           return
                                             ((fun H H0 : Prop =>
                                               BestRel H H0)
                                                match var V v with
                                                | var _ _ => beq true false
                                                | lam _ v2 b2 =>
                                                 forall vf : V,
                                                 beq
                                                 (inAllVarsOf V veq vf t1)
                                                 false ->
                                                 beq (...) false ->
                                                 alphaEq fuel0 (...) (...)
                                                | app _ _ _ => beq true false
                                                end
                                                match lam V₂ v2₂ b2₂ with
                                                | var _ _ => beq true false
                                                | lam _ v2₂0 b2₂0 =>
                                                 forall vf₂ : V₂,
                                                 beq
                                                 (inAllVarsOf V₂ veq₂ vf₂ t1₂)
                                                 false ->
                                                 beq (...) false ->
                                                 alphaEq₂ fuel₂0 (...) (...)
                                                | app _ _ _ => beq true false
                                                end)
                                         with
                                         end
                                     | app _ t₂ t0₂ =>
                                         fun
                                           t2_R0 : 
                                            BestR
                                              (Top_alphaEquivariant_Tm_pmtcty_RR0
                                                 V V₂ V_R) 
                                              (var V v) 
                                              (app V₂ t₂ t0₂) =>
                                         match
                                           t2_R0
                                           return
                                             ((fun H H0 : Prop =>
                                               BestRel H H0)
                                                match var V v with
                                                | var _ _ => beq true false
                                                | lam _ v2 b2 =>
                                                 forall vf : V,
                                                 beq
                                                 (inAllVarsOf V veq vf t1)
                                                 false ->
                                                 beq (...) false ->
                                                 alphaEq fuel0 (...) (...)
                                                | app _ _ _ => beq true false
                                                end
                                                match app V₂ t₂ t0₂ with
                                                | var _ _ => beq true false
                                                | lam _ v2₂ b2₂ =>
                                                 forall vf₂ : V₂,
                                                 beq
                                                 (inAllVarsOf V₂ veq₂ vf₂ t1₂)
                                                 false ->
                                                 beq (...) false ->
                                                 alphaEq₂ fuel₂0 (...) (...)
                                                | app _ _ _ => beq true false
                                                end)
                                         with
                                         end
                                     end
                                 | lam _ v2 b2 =>
                                     match
                                       t2₂ as t2₂0
                                       return
                                         ((fun (t3 : Tm V) (t2₂1 : Tm V₂) =>
                                           BestR
                                             (Top_alphaEquivariant_Tm_pmtcty_RR0
                                                V V₂ V_R) t3 t2₂1 ->
                                           (fun H H0 : Prop => BestRel H H0)
                                             match t3 with
                                             | var _ _ => beq true false
                                             | lam _ v3 b3 =>
                                                 forall vf : V,
                                                 beq (...) false ->
                                                 beq ... false ->
                                                 alphaEq fuel0 ... ...
                                             | app _ _ _ => beq true false
                                             end
                                             match t2₂1 with
                                             | var _ _ => beq true false
                                             | lam _ v2₂ b2₂ =>
                                                 forall vf₂ : V₂,
                                                 beq (...) false ->
                                                 beq ... false ->
                                                 alphaEq₂ fuel₂0 ... ...
                                             | app _ _ _ => beq true false
                                             end) 
                                            (lam V v2 b2) t2₂0)
                                     with
                                     | var _ v₂ =>
                                         fun
                                           t2_R0 : 
                                            BestR
                                              (Top_alphaEquivariant_Tm_pmtcty_RR0
                                                 V V₂ V_R) 
                                              (lam V v2 b2) 
                                              (var V₂ v₂) =>
                                         match
                                           t2_R0
                                           return
                                             ((fun H H0 : Prop =>
                                               BestRel H H0)
                                                match lam V v2 b2 with
                                                | var _ _ => beq true false
                                                | lam _ v3 b3 =>
                                                 forall vf : V,
                                                 beq
                                                 (inAllVarsOf V veq vf t1)
                                                 false ->
                                                 beq (...) false ->
                                                 alphaEq fuel0 (...) (...)
                                                | app _ _ _ => beq true false
                                                end
                                                match var V₂ v₂ with
                                                | var _ _ => beq true false
                                                | lam _ v2₂ b2₂ =>
                                                 forall vf₂ : V₂,
                                                 beq
                                                 (inAllVarsOf V₂ veq₂ vf₂ t1₂)
                                                 false ->
                                                 beq (...) false ->
                                                 alphaEq₂ fuel₂0 (...) (...)
                                                | app _ _ _ => beq true false
                                                end)
                                         with
                                         end
                                     | lam _ v2₂ b2₂ =>
                                         fun
                                           t2_R0 : 
                                            BestR
                                              (Top_alphaEquivariant_Tm_pmtcty_RR0
                                                 V V₂ V_R) 
                                              (lam V v2 b2) 
                                              (lam V₂ v2₂ b2₂) =>
                                         Top_alphaEquivariant_Tm_pmtcty_RR0_constr_1_inv
                                           V V₂ V_R v2 v2₂ b2 b2₂ t2_R0
                                           (fun
                                              _ : 
                                               BestR
                                                 (Top_alphaEquivariant_Tm_pmtcty_RR0
                                                 V V₂ V_R) 
                                                 (lam V v2 b2)
                                                 (lam V₂ v2₂ b2₂) =>
                                            (fun H H0 : Prop => BestRel H H0)
                                              match lam V v2 b2 with
                                              | var _ _ => beq true false
                                              | lam _ v3 b3 =>
                                                 forall vf : V,
                                                 beq
                                                 (inAllVarsOf V veq vf t1)
                                                 false ->
                                                 beq
                                                 (inAllVarsOf V veq vf t2)
                                                 false ->
                                                 alphaEq fuel0
                                                 (substAux V veq v1 (...) b1)
                                                 (substAux V veq v3 (...) b3)
                                              | app _ _ _ => beq true false
                                              end
                                              match lam V₂ v2₂ b2₂ with
                                              | var _ _ => beq true false
                                              | lam _ v2₂0 b2₂0 =>
                                                 forall vf₂ : V₂,
                                                 beq
                                                 (inAllVarsOf V₂ veq₂ vf₂ t1₂)
                                                 false ->
                                                 beq
                                                 (inAllVarsOf V₂ veq₂ vf₂ t2₂)
                                                 false ->
                                                 alphaEq₂ fuel₂0
                                                 (substAux V₂ veq₂ v1₂ 
                                                 (...) b1₂)
                                                 (substAux V₂ veq₂ v2₂0 
                                                 (...) b2₂0)
                                              | app _ _ _ => beq true false
                                              end)
                                           (fun (v2_R : BestR V_R v2 v2₂)
                                              (b2_R : 
                                               BestR
                                                 (Top_alphaEquivariant_Tm_pmtcty_RR0
                                                 V V₂ V_R) b2 b2₂) =>
                                            PiGoodSet V V₂ V_R
                                              (fun vf : V =>
                                               beq 
                                                 (inAllVarsOf V veq vf t1)
                                                 false ->
                                               beq 
                                                 (inAllVarsOf V veq vf t2)
                                                 false ->
                                               alphaEq fuel0
                                                 (substAux V veq v1
                                                 (var V vf) b1)
                                                 (substAux V veq v2
                                                 (var V vf) b2))
                                              (fun vf₂ : V₂ =>
                                               beq
                                                 (inAllVarsOf V₂ veq₂ vf₂ t1₂)
                                                 false ->
                                               beq
                                                 (inAllVarsOf V₂ veq₂ vf₂ t2₂)
                                                 false ->
                                               alphaEq₂ fuel₂0
                                                 (substAux V₂ veq₂ v1₂
                                                 (var V₂ vf₂) b1₂)
                                                 (substAux V₂ veq₂ v2₂
                                                 (var V₂ vf₂) b2₂))
                                              (fun 
                                                 (vf : V) 
                                                 (vf₂ : V₂)
                                                 (vf_R : BestR V_R vf vf₂) =>
                                               PiGoodSet
                                                 (beq
                                                 (inAllVarsOf V veq vf t1)
                                                 false)
                                                 (beq
                                                 (inAllVarsOf V₂ veq₂ vf₂ t1₂)
                                                 false)
                                                 (Top_alphaEquivariant_beq_pmtcty_RR
                                                 (inAllVarsOf V veq vf t1)
                                                 (inAllVarsOf V₂ veq₂ vf₂ t1₂)
                                                 (Top_alphaEquivariant_inAllVarsOf_pmtcty_RR
                                                 V V₂ V_R veq veq₂ veq_R vf
                                                 vf₂ vf_R t1 t1₂ t1_R) false
                                                 false
                                                 Coq_Init_Datatypes_bool_pmtcty_RR0_constr_1)
                                                 (fun _ : beq (...) false =>
                                                 beq
                                                 (inAllVarsOf V veq vf t2)
                                                 false ->
                                                 alphaEq fuel0
                                                 (substAux V veq v1 ... b1)
                                                 (substAux V veq v2 ... b2))
                                                 (fun _ : beq (...) false =>
                                                 beq
                                                 (inAllVarsOf V₂ veq₂ vf₂ t2₂)
                                                 false ->
                                                 alphaEq₂ fuel₂0
                                                 (substAux V₂ veq₂ v1₂ ...
                                                 b1₂)
                                                 (substAux V₂ veq₂ v2₂ ...
                                                 b2₂))
                                                 (fun 
                                                 (H : beq (...) false)
                                                 (H0 : beq (...) false)
                                                 (_ : BestR (...) H H0) =>
                                                 PiGoodSet 
                                                 (beq (...) false)
                                                 (beq (...) false)
                                                 (Top_alphaEquivariant_beq_pmtcty_RR
                                                 (...) 
                                                 (...) 
                                                 (...) false false
                                                 Coq_Init_Datatypes_bool_pmtcty_RR0_constr_1)
                                                 (fun ... =>
                                                 alphaEq fuel0 ... ...)
                                                 (fun ... =>
                                                 alphaEq₂ fuel₂0 ... ...)
                                                 (fun ... ... ... =>
                                                 alphaEq_R fuel0 fuel₂0
                                                 fuel_R1 ... ... ... ... ...
                                                 ...))))
                                     | app _ t₂ t0₂ =>
                                         fun
                                           t2_R0 : 
                                            BestR
                                              (Top_alphaEquivariant_Tm_pmtcty_RR0
                                                 V V₂ V_R) 
                                              (lam V v2 b2) 
                                              (app V₂ t₂ t0₂) =>
                                         match
                                           t2_R0
                                           return
                                             ((fun H H0 : Prop =>
                                               BestRel H H0)
                                                match lam V v2 b2 with
                                                | var _ _ => beq true false
                                                | lam _ v3 b3 =>
                                                 forall vf : V,
                                                 beq
                                                 (inAllVarsOf V veq vf t1)
                                                 false ->
                                                 beq (...) false ->
                                                 alphaEq fuel0 (...) (...)
                                                | app _ _ _ => beq true false
                                                end
                                                match app V₂ t₂ t0₂ with
                                                | var _ _ => beq true false
                                                | lam _ v2₂ b2₂ =>
                                                 forall vf₂ : V₂,
                                                 beq
                                                 (inAllVarsOf V₂ veq₂ vf₂ t1₂)
                                                 false ->
                                                 beq (...) false ->
                                                 alphaEq₂ fuel₂0 (...) (...)
                                                | app _ _ _ => beq true false
                                                end)
                                         with
                                         end
                                     end
                                 | app _ t t0 =>
                                     match
                                       t2₂ as t2₂0
                                       return
                                         ((fun (t3 : Tm V) (t2₂1 : Tm V₂) =>
                                           BestR
                                             (Top_alphaEquivariant_Tm_pmtcty_RR0
                                                V V₂ V_R) t3 t2₂1 ->
                                           (fun H H0 : Prop => BestRel H H0)
                                             match t3 with
                                             | var _ _ => beq true false
                                             | lam _ v2 b2 =>
                                                 forall vf : V,
                                                 beq (...) false ->
                                                 beq ... false ->
                                                 alphaEq fuel0 ... ...
                                             | app _ _ _ => beq true false
                                             end
                                             match t2₂1 with
                                             | var _ _ => beq true false
                                             | lam _ v2₂ b2₂ =>
                                                 forall vf₂ : V₂,
                                                 beq (...) false ->
                                                 beq ... false ->
                                                 alphaEq₂ fuel₂0 ... ...
                                             | app _ _ _ => beq true false
                                             end) 
                                            (app V t t0) t2₂0)
                                     with
                                     | var _ v₂ =>
                                         fun
                                           t2_R0 : 
                                            BestR
                                              (Top_alphaEquivariant_Tm_pmtcty_RR0
                                                 V V₂ V_R) 
                                              (app V t t0) 
                                              (var V₂ v₂) =>
                                         match
                                           t2_R0
                                           return
                                             ((fun H H0 : Prop =>
                                               BestRel H H0)
                                                match app V t t0 with
                                                | var _ _ => beq true false
                                                | lam _ v2 b2 =>
                                                 forall vf : V,
                                                 beq
                                                 (inAllVarsOf V veq vf t1)
                                                 false ->
                                                 beq (...) false ->
                                                 alphaEq fuel0 (...) (...)
                                                | app _ _ _ => beq true false
                                                end
                                                match var V₂ v₂ with
                                                | var _ _ => beq true false
                                                | lam _ v2₂ b2₂ =>
                                                 forall vf₂ : V₂,
                                                 beq
                                                 (inAllVarsOf V₂ veq₂ vf₂ t1₂)
                                                 false ->
                                                 beq (...) false ->
                                                 alphaEq₂ fuel₂0 (...) (...)
                                                | app _ _ _ => beq true false
                                                end)
                                         with
                                         end
                                     | lam _ v2₂ b2₂ =>
                                         fun
                                           t2_R0 : 
                                            BestR
                                              (Top_alphaEquivariant_Tm_pmtcty_RR0
                                                 V V₂ V_R) 
                                              (app V t t0) 
                                              (lam V₂ v2₂ b2₂) =>
                                         match
                                           t2_R0
                                           return
                                             ((fun H H0 : Prop =>
                                               BestRel H H0)
                                                match app V t t0 with
                                                | var _ _ => beq true false
                                                | lam _ v2 b2 =>
                                                 forall vf : V,
                                                 beq
                                                 (inAllVarsOf V veq vf t1)
                                                 false ->
                                                 beq (...) false ->
                                                 alphaEq fuel0 (...) (...)
                                                | app _ _ _ => beq true false
                                                end
                                                match lam V₂ v2₂ b2₂ with
                                                | var _ _ => beq true false
                                                | lam _ v2₂0 b2₂0 =>
                                                 forall vf₂ : V₂,
                                                 beq
                                                 (inAllVarsOf V₂ veq₂ vf₂ t1₂)
                                                 false ->
                                                 beq (...) false ->
                                                 alphaEq₂ fuel₂0 (...) (...)
                                                | app _ _ _ => beq true false
                                                end)
                                         with
                                         end
                                     | app _ t₂ t0₂ =>
                                         fun
                                           t2_R0 : 
                                            BestR
                                              (Top_alphaEquivariant_Tm_pmtcty_RR0
                                                 V V₂ V_R) 
                                              (app V t t0) 
                                              (app V₂ t₂ t0₂) =>
                                         Top_alphaEquivariant_Tm_pmtcty_RR0_constr_2_inv
                                           V V₂ V_R t t₂ t0 t0₂ t2_R0
                                           (fun
                                              _ : 
                                               BestR
                                                 (Top_alphaEquivariant_Tm_pmtcty_RR0
                                                 V V₂ V_R) 
                                                 (app V t t0) 
                                                 (app V₂ t₂ t0₂) =>
                                            (fun H H0 : Prop => BestRel H H0)
                                              match app V t t0 with
                                              | var _ _ => beq true false
                                              | lam _ v2 b2 =>
                                                 forall vf : V,
                                                 beq
                                                 (inAllVarsOf V veq vf t1)
                                                 false ->
                                                 beq
                                                 (inAllVarsOf V veq vf t2)
                                                 false ->
                                                 alphaEq fuel0
                                                 (substAux V veq v1 (...) b1)
                                                 (substAux V veq v2 (...) b2)
                                              | app _ _ _ => beq true false
                                              end
                                              match app V₂ t₂ t0₂ with
                                              | var _ _ => beq true false
                                              | lam _ v2₂ b2₂ =>
                                                 forall vf₂ : V₂,
                                                 beq
                                                 (inAllVarsOf V₂ veq₂ vf₂ t1₂)
                                                 false ->
                                                 beq
                                                 (inAllVarsOf V₂ veq₂ vf₂ t2₂)
                                                 false ->
                                                 alphaEq₂ fuel₂0
                                                 (substAux V₂ veq₂ v1₂ 
                                                 (...) b1₂)
                                                 (substAux V₂ veq₂ v2₂ 
                                                 (...) b2₂)
                                              | app _ _ _ => beq true false
                                              end)
                                           (fun
                                              (_ : 
                                               BestR
                                                 (Top_alphaEquivariant_Tm_pmtcty_RR0
                                                 V V₂ V_R) t t₂)
                                              (_ : 
                                               BestR
                                                 (Top_alphaEquivariant_Tm_pmtcty_RR0
                                                 V V₂ V_R) t0 t0₂) =>
                                            Top_alphaEquivariant_beq_pmtcty_RR
                                              true true
                                              Coq_Init_Datatypes_bool_pmtcty_RR0_constr_0
                                              false false
                                              Coq_Init_Datatypes_bool_pmtcty_RR0_constr_1)
                                     end
                                 end t2_R)
                          | app _ l1₂ r1₂ =>
                              fun
                                t1_R0 : BestR
                                          (Top_alphaEquivariant_Tm_pmtcty_RR0
                                             V V₂ V_R) 
                                          (lam V v1 b1) 
                                          (app V₂ l1₂ r1₂) =>
                              match
                                t1_R0
                                return
                                  ((fun H H0 : Prop => BestRel H H0)
                                     match lam V v1 b1 with
                                     | var _ v2 =>
                                         match t2 with
                                         | var _ v3 => beq (veq v2 v3) true
                                         | lam _ _ _ => beq true false
                                         | app _ _ _ => beq true false
                                         end
                                     | lam _ v2 b2 =>
                                         match t2 with
                                         | var _ _ => beq true false
                                         | lam _ v3 b3 =>
                                             forall vf : V,
                                             beq (inAllVarsOf V veq vf t1)
                                               false ->
                                             beq (inAllVarsOf V veq vf t2)
                                               false ->
                                             alphaEq fuel0
                                               (substAux V veq v2 
                                                 (var V vf) b2)
                                               (substAux V veq v3 
                                                 (var V vf) b3)
                                         | app _ _ _ => beq true false
                                         end
                                     | app _ l1 r1 =>
                                         match t2 with
                                         | var _ _ => beq true false
                                         | lam _ _ _ => beq true false
                                         | app _ l2 r2 =>
                                             and (alphaEq fuel0 l1 l2)
                                               (alphaEq fuel0 r1 r2)
                                         end
                                     end
                                     match app V₂ l1₂ r1₂ with
                                     | var _ v1₂ =>
                                         match t2₂ with
                                         | var _ v2₂ =>
                                             beq (veq₂ v1₂ v2₂) true
                                         | lam _ _ _ => beq true false
                                         | app _ _ _ => beq true false
                                         end
                                     | lam _ v1₂ b1₂ =>
                                         match t2₂ with
                                         | var _ _ => beq true false
                                         | lam _ v2₂ b2₂ =>
                                             forall vf₂ : V₂,
                                             beq
                                               (inAllVarsOf V₂ veq₂ vf₂ t1₂)
                                               false ->
                                             beq
                                               (inAllVarsOf V₂ veq₂ vf₂ t2₂)
                                               false ->
                                             alphaEq₂ fuel₂0
                                               (substAux V₂ veq₂ v1₂
                                                 (var V₂ vf₂) b1₂)
                                               (substAux V₂ veq₂ v2₂
                                                 (var V₂ vf₂) b2₂)
                                         | app _ _ _ => beq true false
                                         end
                                     | app _ l1₂0 r1₂0 =>
                                         match t2₂ with
                                         | var _ _ => beq true false
                                         | lam _ _ _ => beq true false
                                         | app _ l2₂ r2₂ =>
                                             and (alphaEq₂ fuel₂0 l1₂0 l2₂)
                                               (alphaEq₂ fuel₂0 r1₂0 r2₂)
                                         end
                                     end)
                              with
                              end
                          end
                      | app _ l1 r1 =>
                          match
                            t1₂ as t1₂0
                            return
                              ((fun (t3 : Tm V) (t1₂1 : Tm V₂) =>
                                BestR
                                  (Top_alphaEquivariant_Tm_pmtcty_RR0 V V₂
                                     V_R) t3 t1₂1 ->
                                (fun H H0 : Prop => BestRel H H0)
                                  match t3 with
                                  | var _ v1 =>
                                      match t2 with
                                      | var _ v2 => beq (veq v1 v2) true
                                      | lam _ _ _ => beq true false
                                      | app _ _ _ => beq true false
                                      end
                                  | lam _ v1 b1 =>
                                      match t2 with
                                      | var _ _ => beq true false
                                      | lam _ v2 b2 =>
                                          forall vf : V,
                                          beq (inAllVarsOf V veq vf t1) false ->
                                          beq (inAllVarsOf V veq vf t2) false ->
                                          alphaEq fuel0
                                            (substAux V veq v1 (var V vf) b1)
                                            (substAux V veq v2 (var V vf) b2)
                                      | app _ _ _ => beq true false
                                      end
                                  | app _ l2 r2 =>
                                      match t2 with
                                      | var _ _ => beq true false
                                      | lam _ _ _ => beq true false
                                      | app _ l3 r3 =>
                                          and (alphaEq fuel0 l2 l3)
                                            (alphaEq fuel0 r2 r3)
                                      end
                                  end
                                  match t1₂1 with
                                  | var _ v1₂ =>
                                      match t2₂ with
                                      | var _ v2₂ => beq (veq₂ v1₂ v2₂) true
                                      | lam _ _ _ => beq true false
                                      | app _ _ _ => beq true false
                                      end
                                  | lam _ v1₂ b1₂ =>
                                      match t2₂ with
                                      | var _ _ => beq true false
                                      | lam _ v2₂ b2₂ =>
                                          forall vf₂ : V₂,
                                          beq (inAllVarsOf V₂ veq₂ vf₂ t1₂)
                                            false ->
                                          beq (inAllVarsOf V₂ veq₂ vf₂ t2₂)
                                            false ->
                                          alphaEq₂ fuel₂0
                                            (substAux V₂ veq₂ v1₂
                                               (var V₂ vf₂) b1₂)
                                            (substAux V₂ veq₂ v2₂
                                               (var V₂ vf₂) b2₂)
                                      | app _ _ _ => beq true false
                                      end
                                  | app _ l1₂ r1₂ =>
                                      match t2₂ with
                                      | var _ _ => beq true false
                                      | lam _ _ _ => beq true false
                                      | app _ l2₂ r2₂ =>
                                          and (alphaEq₂ fuel₂0 l1₂ l2₂)
                                            (alphaEq₂ fuel₂0 r1₂ r2₂)
                                      end
                                  end) (app V l1 r1) t1₂0)
                          with
                          | var _ v1₂ =>
                              fun
                                t1_R0 : BestR
                                          (Top_alphaEquivariant_Tm_pmtcty_RR0
                                             V V₂ V_R) 
                                          (app V l1 r1) 
                                          (var V₂ v1₂) =>
                              match
                                t1_R0
                                return
                                  ((fun H H0 : Prop => BestRel H H0)
                                     match app V l1 r1 with
                                     | var _ v1 =>
                                         match t2 with
                                         | var _ v2 => beq (veq v1 v2) true
                                         | lam _ _ _ => beq true false
                                         | app _ _ _ => beq true false
                                         end
                                     | lam _ v1 b1 =>
                                         match t2 with
                                         | var _ _ => beq true false
                                         | lam _ v2 b2 =>
                                             forall vf : V,
                                             beq (inAllVarsOf V veq vf t1)
                                               false ->
                                             beq (inAllVarsOf V veq vf t2)
                                               false ->
                                             alphaEq fuel0
                                               (substAux V veq v1 
                                                 (var V vf) b1)
                                               (substAux V veq v2 
                                                 (var V vf) b2)
                                         | app _ _ _ => beq true false
                                         end
                                     | app _ l2 r2 =>
                                         match t2 with
                                         | var _ _ => beq true false
                                         | lam _ _ _ => beq true false
                                         | app _ l3 r3 =>
                                             and (alphaEq fuel0 l2 l3)
                                               (alphaEq fuel0 r2 r3)
                                         end
                                     end
                                     match var V₂ v1₂ with
                                     | var _ v1₂0 =>
                                         match t2₂ with
                                         | var _ v2₂ =>
                                             beq (veq₂ v1₂0 v2₂) true
                                         | lam _ _ _ => beq true false
                                         | app _ _ _ => beq true false
                                         end
                                     | lam _ v1₂0 b1₂ =>
                                         match t2₂ with
                                         | var _ _ => beq true false
                                         | lam _ v2₂ b2₂ =>
                                             forall vf₂ : V₂,
                                             beq
                                               (inAllVarsOf V₂ veq₂ vf₂ t1₂)
                                               false ->
                                             beq
                                               (inAllVarsOf V₂ veq₂ vf₂ t2₂)
                                               false ->
                                             alphaEq₂ fuel₂0
                                               (substAux V₂ veq₂ v1₂0
                                                 (var V₂ vf₂) b1₂)
                                               (substAux V₂ veq₂ v2₂
                                                 (var V₂ vf₂) b2₂)
                                         | app _ _ _ => beq true false
                                         end
                                     | app _ l1₂ r1₂ =>
                                         match t2₂ with
                                         | var _ _ => beq true false
                                         | lam _ _ _ => beq true false
                                         | app _ l2₂ r2₂ =>
                                             and (alphaEq₂ fuel₂0 l1₂ l2₂)
                                               (alphaEq₂ fuel₂0 r1₂ r2₂)
                                         end
                                     end)
                              with
                              end
                          | lam _ v1₂ b1₂ =>
                              fun
                                t1_R0 : BestR
                                          (Top_alphaEquivariant_Tm_pmtcty_RR0
                                             V V₂ V_R) 
                                          (app V l1 r1) 
                                          (lam V₂ v1₂ b1₂) =>
                              match
                                t1_R0
                                return
                                  ((fun H H0 : Prop => BestRel H H0)
                                     match app V l1 r1 with
                                     | var _ v1 =>
                                         match t2 with
                                         | var _ v2 => beq (veq v1 v2) true
                                         | lam _ _ _ => beq true false
                                         | app _ _ _ => beq true false
                                         end
                                     | lam _ v1 b1 =>
                                         match t2 with
                                         | var _ _ => beq true false
                                         | lam _ v2 b2 =>
                                             forall vf : V,
                                             beq (inAllVarsOf V veq vf t1)
                                               false ->
                                             beq (inAllVarsOf V veq vf t2)
                                               false ->
                                             alphaEq fuel0
                                               (substAux V veq v1 
                                                 (var V vf) b1)
                                               (substAux V veq v2 
                                                 (var V vf) b2)
                                         | app _ _ _ => beq true false
                                         end
                                     | app _ l2 r2 =>
                                         match t2 with
                                         | var _ _ => beq true false
                                         | lam _ _ _ => beq true false
                                         | app _ l3 r3 =>
                                             and (alphaEq fuel0 l2 l3)
                                               (alphaEq fuel0 r2 r3)
                                         end
                                     end
                                     match lam V₂ v1₂ b1₂ with
                                     | var _ v1₂0 =>
                                         match t2₂ with
                                         | var _ v2₂ =>
                                             beq (veq₂ v1₂0 v2₂) true
                                         | lam _ _ _ => beq true false
                                         | app _ _ _ => beq true false
                                         end
                                     | lam _ v1₂0 b1₂0 =>
                                         match t2₂ with
                                         | var _ _ => beq true false
                                         | lam _ v2₂ b2₂ =>
                                             forall vf₂ : V₂,
                                             beq
                                               (inAllVarsOf V₂ veq₂ vf₂ t1₂)
                                               false ->
                                             beq
                                               (inAllVarsOf V₂ veq₂ vf₂ t2₂)
                                               false ->
                                             alphaEq₂ fuel₂0
                                               (substAux V₂ veq₂ v1₂0
                                                 (var V₂ vf₂) b1₂0)
                                               (substAux V₂ veq₂ v2₂
                                                 (var V₂ vf₂) b2₂)
                                         | app _ _ _ => beq true false
                                         end
                                     | app _ l1₂ r1₂ =>
                                         match t2₂ with
                                         | var _ _ => beq true false
                                         | lam _ _ _ => beq true false
                                         | app _ l2₂ r2₂ =>
                                             and (alphaEq₂ fuel₂0 l1₂ l2₂)
                                               (alphaEq₂ fuel₂0 r1₂ r2₂)
                                         end
                                     end)
                              with
                              end
                          | app _ l1₂ r1₂ =>
                              fun
                                t1_R0 : BestR
                                          (Top_alphaEquivariant_Tm_pmtcty_RR0
                                             V V₂ V_R) 
                                          (app V l1 r1) 
                                          (app V₂ l1₂ r1₂) =>
                              Top_alphaEquivariant_Tm_pmtcty_RR0_constr_2_inv
                                V V₂ V_R l1 l1₂ r1 r1₂ t1_R0
                                (fun
                                   _ : BestR
                                         (Top_alphaEquivariant_Tm_pmtcty_RR0
                                            V V₂ V_R) 
                                         (app V l1 r1) 
                                         (app V₂ l1₂ r1₂) =>
                                 (fun H H0 : Prop => BestRel H H0)
                                   match app V l1 r1 with
                                   | var _ v1 =>
                                       match t2 with
                                       | var _ v2 => beq (veq v1 v2) true
                                       | lam _ _ _ => beq true false
                                       | app _ _ _ => beq true false
                                       end
                                   | lam _ v1 b1 =>
                                       match t2 with
                                       | var _ _ => beq true false
                                       | lam _ v2 b2 =>
                                           forall vf : V,
                                           beq (inAllVarsOf V veq vf t1)
                                             false ->
                                           beq (inAllVarsOf V veq vf t2)
                                             false ->
                                           alphaEq fuel0
                                             (substAux V veq v1 (var V vf) b1)
                                             (substAux V veq v2 (var V vf) b2)
                                       | app _ _ _ => beq true false
                                       end
                                   | app _ l2 r2 =>
                                       match t2 with
                                       | var _ _ => beq true false
                                       | lam _ _ _ => beq true false
                                       | app _ l3 r3 =>
                                           and (alphaEq fuel0 l2 l3)
                                             (alphaEq fuel0 r2 r3)
                                       end
                                   end
                                   match app V₂ l1₂ r1₂ with
                                   | var _ v1₂ =>
                                       match t2₂ with
                                       | var _ v2₂ => beq (veq₂ v1₂ v2₂) true
                                       | lam _ _ _ => beq true false
                                       | app _ _ _ => beq true false
                                       end
                                   | lam _ v1₂ b1₂ =>
                                       match t2₂ with
                                       | var _ _ => beq true false
                                       | lam _ v2₂ b2₂ =>
                                           forall vf₂ : V₂,
                                           beq (inAllVarsOf V₂ veq₂ vf₂ t1₂)
                                             false ->
                                           beq (inAllVarsOf V₂ veq₂ vf₂ t2₂)
                                             false ->
                                           alphaEq₂ fuel₂0
                                             (substAux V₂ veq₂ v1₂
                                                (var V₂ vf₂) b1₂)
                                             (substAux V₂ veq₂ v2₂
                                                (var V₂ vf₂) b2₂)
                                       | app _ _ _ => beq true false
                                       end
                                   | app _ l1₂0 r1₂0 =>
                                       match t2₂ with
                                       | var _ _ => beq true false
                                       | lam _ _ _ => beq true false
                                       | app _ l2₂ r2₂ =>
                                           and (alphaEq₂ fuel₂0 l1₂0 l2₂)
                                             (alphaEq₂ fuel₂0 r1₂0 r2₂)
                                       end
                                   end)
                                (fun
                                   (l1_R : BestR
                                             (Top_alphaEquivariant_Tm_pmtcty_RR0
                                                V V₂ V_R) l1 l1₂)
                                   (r1_R : BestR
                                             (Top_alphaEquivariant_Tm_pmtcty_RR0
                                                V V₂ V_R) r1 r1₂) =>
                                 match
                                   t2 as t3
                                   return
                                     ((fun (t4 : Tm V) (t2₂0 : Tm V₂) =>
                                       BestR
                                         (Top_alphaEquivariant_Tm_pmtcty_RR0
                                            V V₂ V_R) t4 t2₂0 ->
                                       (fun H H0 : Prop => BestRel H H0)
                                         match t4 with
                                         | var _ _ => beq true false
                                         | lam _ _ _ => beq true false
                                         | app _ l2 r2 =>
                                             and (alphaEq fuel0 l1 l2)
                                               (alphaEq fuel0 r1 r2)
                                         end
                                         match t2₂0 with
                                         | var _ _ => beq true false
                                         | lam _ _ _ => beq true false
                                         | app _ l2₂ r2₂ =>
                                             and (alphaEq₂ fuel₂0 l1₂ l2₂)
                                               (alphaEq₂ fuel₂0 r1₂ r2₂)
                                         end) t3 t2₂)
                                 with
                                 | var _ v =>
                                     match
                                       t2₂ as t2₂0
                                       return
                                         ((fun (t3 : Tm V) (t2₂1 : Tm V₂) =>
                                           BestR
                                             (Top_alphaEquivariant_Tm_pmtcty_RR0
                                                V V₂ V_R) t3 t2₂1 ->
                                           (fun H H0 : Prop => BestRel H H0)
                                             match t3 with
                                             | var _ _ => beq true false
                                             | lam _ _ _ => beq true false
                                             | app _ l2 r2 =>
                                                 and 
                                                 (alphaEq fuel0 l1 l2)
                                                 (alphaEq fuel0 r1 r2)
                                             end
                                             match t2₂1 with
                                             | var _ _ => beq true false
                                             | lam _ _ _ => beq true false
                                             | app _ l2₂ r2₂ =>
                                                 and
                                                 (alphaEq₂ fuel₂0 l1₂ l2₂)
                                                 (alphaEq₂ fuel₂0 r1₂ r2₂)
                                             end) 
                                            (var V v) t2₂0)
                                     with
                                     | var _ v₂ =>
                                         fun
                                           t2_R0 : 
                                            BestR
                                              (Top_alphaEquivariant_Tm_pmtcty_RR0
                                                 V V₂ V_R) 
                                              (var V v) 
                                              (var V₂ v₂) =>
                                         Top_alphaEquivariant_Tm_pmtcty_RR0_constr_0_inv
                                           V V₂ V_R v v₂ t2_R0
                                           (fun
                                              _ : 
                                               BestR
                                                 (Top_alphaEquivariant_Tm_pmtcty_RR0
                                                 V V₂ V_R) 
                                                 (var V v) 
                                                 (var V₂ v₂) =>
                                            (fun H H0 : Prop => BestRel H H0)
                                              match var V v with
                                              | var _ _ => beq true false
                                              | lam _ _ _ => beq true false
                                              | app _ l2 r2 =>
                                                 and 
                                                 (alphaEq fuel0 l1 l2)
                                                 (alphaEq fuel0 r1 r2)
                                              end
                                              match var V₂ v₂ with
                                              | var _ _ => beq true false
                                              | lam _ _ _ => beq true false
                                              | app _ l2₂ r2₂ =>
                                                 and
                                                 (alphaEq₂ fuel₂0 l1₂ l2₂)
                                                 (alphaEq₂ fuel₂0 r1₂ r2₂)
                                              end)
                                           (fun _ : BestR V_R v v₂ =>
                                            Top_alphaEquivariant_beq_pmtcty_RR
                                              true true
                                              Coq_Init_Datatypes_bool_pmtcty_RR0_constr_0
                                              false false
                                              Coq_Init_Datatypes_bool_pmtcty_RR0_constr_1)
                                     | lam _ v₂ t₂ =>
                                         fun
                                           t2_R0 : 
                                            BestR
                                              (Top_alphaEquivariant_Tm_pmtcty_RR0
                                                 V V₂ V_R) 
                                              (var V v) 
                                              (lam V₂ v₂ t₂) =>
                                         match
                                           t2_R0
                                           return
                                             ((fun H H0 : Prop =>
                                               BestRel H H0)
                                                match var V v with
                                                | var _ _ => beq true false
                                                | lam _ _ _ => beq true false
                                                | app _ l2 r2 =>
                                                 and 
                                                 (alphaEq fuel0 l1 l2)
                                                 (alphaEq fuel0 r1 r2)
                                                end
                                                match lam V₂ v₂ t₂ with
                                                | var _ _ => beq true false
                                                | lam _ _ _ => beq true false
                                                | app _ l2₂ r2₂ =>
                                                 and
                                                 (alphaEq₂ fuel₂0 l1₂ l2₂)
                                                 (alphaEq₂ fuel₂0 r1₂ r2₂)
                                                end)
                                         with
                                         end
                                     | app _ l2₂ r2₂ =>
                                         fun
                                           t2_R0 : 
                                            BestR
                                              (Top_alphaEquivariant_Tm_pmtcty_RR0
                                                 V V₂ V_R) 
                                              (var V v) 
                                              (app V₂ l2₂ r2₂) =>
                                         match
                                           t2_R0
                                           return
                                             ((fun H H0 : Prop =>
                                               BestRel H H0)
                                                match var V v with
                                                | var _ _ => beq true false
                                                | lam _ _ _ => beq true false
                                                | app _ l2 r2 =>
                                                 and 
                                                 (alphaEq fuel0 l1 l2)
                                                 (alphaEq fuel0 r1 r2)
                                                end
                                                match app V₂ l2₂ r2₂ with
                                                | var _ _ => beq true false
                                                | lam _ _ _ => beq true false
                                                | app _ l2₂0 r2₂0 =>
                                                 and
                                                 (alphaEq₂ fuel₂0 l1₂ l2₂0)
                                                 (alphaEq₂ fuel₂0 r1₂ r2₂0)
                                                end)
                                         with
                                         end
                                     end
                                 | lam _ v t =>
                                     match
                                       t2₂ as t2₂0
                                       return
                                         ((fun (t3 : Tm V) (t2₂1 : Tm V₂) =>
                                           BestR
                                             (Top_alphaEquivariant_Tm_pmtcty_RR0
                                                V V₂ V_R) t3 t2₂1 ->
                                           (fun H H0 : Prop => BestRel H H0)
                                             match t3 with
                                             | var _ _ => beq true false
                                             | lam _ _ _ => beq true false
                                             | app _ l2 r2 =>
                                                 and 
                                                 (alphaEq fuel0 l1 l2)
                                                 (alphaEq fuel0 r1 r2)
                                             end
                                             match t2₂1 with
                                             | var _ _ => beq true false
                                             | lam _ _ _ => beq true false
                                             | app _ l2₂ r2₂ =>
                                                 and
                                                 (alphaEq₂ fuel₂0 l1₂ l2₂)
                                                 (alphaEq₂ fuel₂0 r1₂ r2₂)
                                             end) 
                                            (lam V v t) t2₂0)
                                     with
                                     | var _ v₂ =>
                                         fun
                                           t2_R0 : 
                                            BestR
                                              (Top_alphaEquivariant_Tm_pmtcty_RR0
                                                 V V₂ V_R) 
                                              (lam V v t) 
                                              (var V₂ v₂) =>
                                         match
                                           t2_R0
                                           return
                                             ((fun H H0 : Prop =>
                                               BestRel H H0)
                                                match lam V v t with
                                                | var _ _ => beq true false
                                                | lam _ _ _ => beq true false
                                                | app _ l2 r2 =>
                                                 and 
                                                 (alphaEq fuel0 l1 l2)
                                                 (alphaEq fuel0 r1 r2)
                                                end
                                                match var V₂ v₂ with
                                                | var _ _ => beq true false
                                                | lam _ _ _ => beq true false
                                                | app _ l2₂ r2₂ =>
                                                 and
                                                 (alphaEq₂ fuel₂0 l1₂ l2₂)
                                                 (alphaEq₂ fuel₂0 r1₂ r2₂)
                                                end)
                                         with
                                         end
                                     | lam _ v₂ t₂ =>
                                         fun
                                           t2_R0 : 
                                            BestR
                                              (Top_alphaEquivariant_Tm_pmtcty_RR0
                                                 V V₂ V_R) 
                                              (lam V v t) 
                                              (lam V₂ v₂ t₂) =>
                                         Top_alphaEquivariant_Tm_pmtcty_RR0_constr_1_inv
                                           V V₂ V_R v v₂ t t₂ t2_R0
                                           (fun
                                              _ : 
                                               BestR
                                                 (Top_alphaEquivariant_Tm_pmtcty_RR0
                                                 V V₂ V_R) 
                                                 (lam V v t) 
                                                 (lam V₂ v₂ t₂) =>
                                            (fun H H0 : Prop => BestRel H H0)
                                              match lam V v t with
                                              | var _ _ => beq true false
                                              | lam _ _ _ => beq true false
                                              | app _ l2 r2 =>
                                                 and 
                                                 (alphaEq fuel0 l1 l2)
                                                 (alphaEq fuel0 r1 r2)
                                              end
                                              match lam V₂ v₂ t₂ with
                                              | var _ _ => beq true false
                                              | lam _ _ _ => beq true false
                                              | app _ l2₂ r2₂ =>
                                                 and
                                                 (alphaEq₂ fuel₂0 l1₂ l2₂)
                                                 (alphaEq₂ fuel₂0 r1₂ r2₂)
                                              end)
                                           (fun (_ : BestR V_R v v₂)
                                              (_ : 
                                               BestR
                                                 (Top_alphaEquivariant_Tm_pmtcty_RR0
                                                 V V₂ V_R) t t₂) =>
                                            Top_alphaEquivariant_beq_pmtcty_RR
                                              true true
                                              Coq_Init_Datatypes_bool_pmtcty_RR0_constr_0
                                              false false
                                              Coq_Init_Datatypes_bool_pmtcty_RR0_constr_1)
                                     | app _ l2₂ r2₂ =>
                                         fun
                                           t2_R0 : 
                                            BestR
                                              (Top_alphaEquivariant_Tm_pmtcty_RR0
                                                 V V₂ V_R) 
                                              (lam V v t) 
                                              (app V₂ l2₂ r2₂) =>
                                         match
                                           t2_R0
                                           return
                                             ((fun H H0 : Prop =>
                                               BestRel H H0)
                                                match lam V v t with
                                                | var _ _ => beq true false
                                                | lam _ _ _ => beq true false
                                                | app _ l2 r2 =>
                                                 and 
                                                 (alphaEq fuel0 l1 l2)
                                                 (alphaEq fuel0 r1 r2)
                                                end
                                                match app V₂ l2₂ r2₂ with
                                                | var _ _ => beq true false
                                                | lam _ _ _ => beq true false
                                                | app _ l2₂0 r2₂0 =>
                                                 and
                                                 (alphaEq₂ fuel₂0 l1₂ l2₂0)
                                                 (alphaEq₂ fuel₂0 r1₂ r2₂0)
                                                end)
                                         with
                                         end
                                     end
                                 | app _ l2 r2 =>
                                     match
                                       t2₂ as t2₂0
                                       return
                                         ((fun (t3 : Tm V) (t2₂1 : Tm V₂) =>
                                           BestR
                                             (Top_alphaEquivariant_Tm_pmtcty_RR0
                                                V V₂ V_R) t3 t2₂1 ->
                                           (fun H H0 : Prop => BestRel H H0)
                                             match t3 with
                                             | var _ _ => beq true false
                                             | lam _ _ _ => beq true false
                                             | app _ l3 r3 =>
                                                 and 
                                                 (alphaEq fuel0 l1 l3)
                                                 (alphaEq fuel0 r1 r3)
                                             end
                                             match t2₂1 with
                                             | var _ _ => beq true false
                                             | lam _ _ _ => beq true false
                                             | app _ l2₂ r2₂ =>
                                                 and
                                                 (alphaEq₂ fuel₂0 l1₂ l2₂)
                                                 (alphaEq₂ fuel₂0 r1₂ r2₂)
                                             end) 
                                            (app V l2 r2) t2₂0)
                                     with
                                     | var _ v₂ =>
                                         fun
                                           t2_R0 : 
                                            BestR
                                              (Top_alphaEquivariant_Tm_pmtcty_RR0
                                                 V V₂ V_R) 
                                              (app V l2 r2) 
                                              (var V₂ v₂) =>
                                         match
                                           t2_R0
                                           return
                                             ((fun H H0 : Prop =>
                                               BestRel H H0)
                                                match app V l2 r2 with
                                                | var _ _ => beq true false
                                                | lam _ _ _ => beq true false
                                                | app _ l3 r3 =>
                                                 and 
                                                 (alphaEq fuel0 l1 l3)
                                                 (alphaEq fuel0 r1 r3)
                                                end
                                                match var V₂ v₂ with
                                                | var _ _ => beq true false
                                                | lam _ _ _ => beq true false
                                                | app _ l2₂ r2₂ =>
                                                 and
                                                 (alphaEq₂ fuel₂0 l1₂ l2₂)
                                                 (alphaEq₂ fuel₂0 r1₂ r2₂)
                                                end)
                                         with
                                         end
                                     | lam _ v₂ t₂ =>
                                         fun
                                           t2_R0 : 
                                            BestR
                                              (Top_alphaEquivariant_Tm_pmtcty_RR0
                                                 V V₂ V_R) 
                                              (app V l2 r2) 
                                              (lam V₂ v₂ t₂) =>
                                         match
                                           t2_R0
                                           return
                                             ((fun H H0 : Prop =>
                                               BestRel H H0)
                                                match app V l2 r2 with
                                                | var _ _ => beq true false
                                                | lam _ _ _ => beq true false
                                                | app _ l3 r3 =>
                                                 and 
                                                 (alphaEq fuel0 l1 l3)
                                                 (alphaEq fuel0 r1 r3)
                                                end
                                                match lam V₂ v₂ t₂ with
                                                | var _ _ => beq true false
                                                | lam _ _ _ => beq true false
                                                | app _ l2₂ r2₂ =>
                                                 and
                                                 (alphaEq₂ fuel₂0 l1₂ l2₂)
                                                 (alphaEq₂ fuel₂0 r1₂ r2₂)
                                                end)
                                         with
                                         end
                                     | app _ l2₂ r2₂ =>
                                         fun
                                           t2_R0 : 
                                            BestR
                                              (Top_alphaEquivariant_Tm_pmtcty_RR0
                                                 V V₂ V_R) 
                                              (app V l2 r2) 
                                              (app V₂ l2₂ r2₂) =>
                                         Top_alphaEquivariant_Tm_pmtcty_RR0_constr_2_inv
                                           V V₂ V_R l2 l2₂ r2 r2₂ t2_R0
                                           (fun
                                              _ : 
                                               BestR
                                                 (Top_alphaEquivariant_Tm_pmtcty_RR0
                                                 V V₂ V_R) 
                                                 (app V l2 r2)
                                                 (app V₂ l2₂ r2₂) =>
                                            (fun H H0 : Prop => BestRel H H0)
                                              match app V l2 r2 with
                                              | var _ _ => beq true false
                                              | lam _ _ _ => beq true false
                                              | app _ l3 r3 =>
                                                 and 
                                                 (alphaEq fuel0 l1 l3)
                                                 (alphaEq fuel0 r1 r3)
                                              end
                                              match app V₂ l2₂ r2₂ with
                                              | var _ _ => beq true false
                                              | lam _ _ _ => beq true false
                                              | app _ l2₂0 r2₂0 =>
                                                 and
                                                 (alphaEq₂ fuel₂0 l1₂ l2₂0)
                                                 (alphaEq₂ fuel₂0 r1₂ r2₂0)
                                              end)
                                           (fun
                                              (l2_R : 
                                               BestR
                                                 (Top_alphaEquivariant_Tm_pmtcty_RR0
                                                 V V₂ V_R) l2 l2₂)
                                              (r2_R : 
                                               BestR
                                                 (Top_alphaEquivariant_Tm_pmtcty_RR0
                                                 V V₂ V_R) r2 r2₂) =>
                                            Top_alphaEquivariant_and_pmtcty_RR
                                              (alphaEq fuel0 l1 l2)
                                              (alphaEq₂ fuel₂0 l1₂ l2₂)
                                              (alphaEq_R fuel0 fuel₂0 fuel_R1
                                                 l1 l1₂ l1_R l2 l2₂ l2_R)
                                              (alphaEq fuel0 r1 r2)
                                              (alphaEq₂ fuel₂0 r1₂ r2₂)
                                              (alphaEq_R fuel0 fuel₂0 fuel_R1
                                                 r1 r1₂ r1_R r2 r2₂ r2_R))
                                     end
                                 end t2_R)
                          end
                      end t1_R)
               end
           end fuel_R
       end
   end).
