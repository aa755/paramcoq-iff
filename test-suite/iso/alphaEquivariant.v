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
  match (fuel, t1,t2) with
    | (S fuel, var v1, var v2) => beq (veq v1 v2) true
    | (S fuel, app l1 r1, app l2 r2) =>
      and (alphaEq fuel l1 l2) (alphaEq fuel r1 r2)
    | (S fuel, lam v1 b1, lam v2 b2) =>
      forall (vf:V), (inAllVarsOf vf t1) ≡  false
                ->  (inAllVarsOf vf t2) ≡ false 
                -> alphaEq fuel
                          (substAux v1 (var vf) b1)
                          (substAux v2 (var vf) b2)
    | ( _, _, _ ) => true ≡ false
  end.

End Tm.

Check beq.
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

Definition beqType := bool -> bool -> Prop.

Module Temp.
Run TemplateProgram (genParamInd [] true true true "Coq.Init.Datatypes.bool").
Run TemplateProgram (genParamInd [] true true true "Top.alphaEquivariant.Tm").
End Temp.

Import Temp.

Definition isBestRel {A1 A2: Set} (R: A1-> A2 -> Prop) : Type := TotalHeteroRel R
                 * oneToOne R.
                 
Axiom goodBool : isBestRel Coq_Init_Datatypes_bool_pmtcty_RR0.


Definition Coq_Init_Datatypes_bool_pmtcty_RR0 : BestRel bool bool.
Proof.
  exists Coq_Init_Datatypes_bool_pmtcty_RR0; simpl.
- apply goodBool.
- apply goodBool.
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

Run TemplateProgram (mkIndEnv "indTransEnv" ["Top.alphaEquivariant.Tm";
"Coq.Init.Datatypes.bool"]).

Run TemplateProgram (genParam indTransEnv true true "Coq.Init.Datatypes.orb").


Run TemplateProgram (genParam indTransEnv true true "inAllVarsOf").



