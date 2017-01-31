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

Set Printing All.

Run TemplateProgram (genParam indTransEnv true true "and").

Definition Coq_Init_Datatypes_nat_pmtcty_RR0 : BestRel nat nat.
Proof.
  exists Coq_Init_Datatypes_nat_pmtcty_RR0; simpl.
- apply goodNat.
- apply goodNat.
- intros ? ? ? ?. apply ProofIrrelevance.PI.proof_irrelevance.  
Defined.

Run TemplateProgram (genParam [] true true "beqType").
Local Opaque Coq_Init_Datatypes_bool_pmtcty_RR0.
Axiom beq_RR : ltac:(let t:= eval lazy in (beqType_RR beq beq) in exact t).
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


Fixpoint idb (b:bool) := b.
Run TemplateProgram (genParam indTransEnv true true "idb").
Eval compute in idb_RR.
Print Assumptions idb_RR. (* the goodness proof uses proof irrelevance for irrel 
and an axiom. the axiom should go away once the goodness code is complete*)

(* the :Set cast is present *)
Run TemplateProgram (printTermSq "Coq.Init.Datatypes.orb").
Set Printing All.


(* Run TemplateProgram (printTermSq "Coq.Init.Datatypes.orb"). *)
Run TemplateProgram (genParam indTransEnv true true "orb").

Definition Coq_Init_Datatypes_orb_pmtcty_RR := orb_RR.

Run TemplateProgram (genParam indTransEnv true true "inAllVarsOf").
Local Transparent Coq_Init_Datatypes_bool_pmtcty_RR0.


Lemma  Top_alphaEquivariant_beq_pmtcty_RR : beqType_RR beq beq.
Proof.
  intros ? ?. simpl. intros ? ? ? ?.
  (* beq uses eq.  once we have oneToOne of eq, this should be automatic. *)
Admitted.

Definition Top_alphaEquivariant_inAllVarsOf_pmtcty_RR := 
inAllVarsOf_RR.

Run TemplateProgram (genParam indTransEnv true true "substAux").

Definition  Top_alphaEquivariant_substAux_pmtcty_RR := substAux_RR.

Locate and.
Run TemplateProgram (genParam indTransEnv true true "and").

Run TemplateProgram (genParam indTransEnv true true "alphaEq").


Lemma ddd :
(forall (V V₂ : Set) (V_R : BestRel V V₂) (veq : V -> V -> bool)
         (veq₂ : V₂ -> V₂ -> bool),
       BestR
         (PiTSummary V V₂ V_R (fun _ : V => V -> bool) (fun _ : V₂ => V₂ -> bool)
            (fun (H : V) (H0 : V₂) (_ : BestR V_R H H0) =>
             PiTSummary V V₂ V_R (fun _ : V => bool) (fun _ : V₂ => bool)
               (fun (H1 : V) (H2 : V₂) (_ : BestR V_R H1 H2) =>
                Coq_Init_Datatypes_bool_pmtcty_RR0))) veq veq₂ ->
       forall (v : V) (v₂ : V₂),
       BestR V_R v v₂ ->
       forall (t : Tm V) (t₂ : Tm V₂),
       BestR (Top_alphaEquivariant_Tm_pmtcty_RR0 V V₂ V_R) t t₂ ->
       BestR Coq_Init_Datatypes_bool_pmtcty_RR0
         ((fix inAllVarsOf (v0 : V) (t0 : Tm V) {struct t0} : bool :=
             match t0 with
             | var _ vv => veq vv v0
             | lam _ vv b => (veq vv v0 || inAllVarsOf v0 b)%bool
             | alphaEquivariant.app _ l r => (inAllVarsOf v0 l || inAllVarsOf v0 r)%bool
             end) v t)
         ((fix inAllVarsOf₂ (v₂0 : V₂) (t₂0 : Tm V₂) {struct t₂0} : bool :=
             match t₂0 with
             | var _ vv₂ => veq₂ vv₂ v₂0
             | lam _ vv₂ b₂ => (veq₂ vv₂ v₂0 || inAllVarsOf₂ v₂0 b₂)%bool
             | alphaEquivariant.app _ l₂ r₂ =>
                 (inAllVarsOf₂ v₂0 l₂ || inAllVarsOf₂ v₂0 r₂)%bool
             end) v₂ t₂)) = True.
simpl. 
(*
(forall (V V₂ : Set) (V_R : BestRel V V₂) (veq : V -> V -> bool) (veq₂ : V₂ -> V₂ -> bool),
 (forall (a1 : V) (a2 : V₂),
  R V_R a1 a2 ->
  forall (a3 : V) (a4 : V₂),
  R V_R a3 a4 -> Temp.Coq_Init_Datatypes_bool_pmtcty_RR0 (veq a1 a3) (veq₂ a2 a4)) ->
 forall (v : V) (v₂ : V₂),
 BestR V_R v v₂ ->
 forall (t : Tm V) (t₂ : Tm V₂),
 Temp.Top_alphaEquivariant_Tm_pmtcty_RR0 V V₂ V_R t t₂ ->
 Temp.Coq_Init_Datatypes_bool_pmtcty_RR0
   ((fix inAllVarsOf (v0 : V) (t0 : Tm V) {struct t0} : bool :=
       match t0 with
       | var _ vv => veq vv v0
       | lam _ vv b => (veq vv v0 || inAllVarsOf v0 b)%bool
       | alphaEquivariant.app _ l r => (inAllVarsOf v0 l || inAllVarsOf v0 r)%bool
       end) v t)
   ((fix inAllVarsOf₂ (v₂0 : V₂) (t₂0 : Tm V₂) {struct t₂0} : bool :=
       match t₂0 with
       | var _ vv₂ => veq₂ vv₂ v₂0
       | lam _ vv₂ b₂ => (veq₂ vv₂ v₂0 || inAllVarsOf₂ v₂0 b₂)%bool
       | alphaEquivariant.app _ l₂ r₂ => (inAllVarsOf₂ v₂0 l₂ || inAllVarsOf₂ v₂0 r₂)%bool
       end) v₂ t₂)) = True
Note that al goodness proofs vanished. V_R can be replaced with R V_R
*)


Check inAllVarsOf_RR.

(*
*)


