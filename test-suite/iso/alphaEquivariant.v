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

Definition xx : IndicesInvUniv := Prop.


Run TemplateProgram (genParam indTransEnv true true "and"). (* success!*)



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


(* Run TemplateProgram (printTermSq "Coq.Init.Datatypes.orb"). *)
Run TemplateProgram (genParam indTransEnv true true "orb").

Definition Coq_Init_Datatypes_orb_pmtcty_RR := orb_RR.

Run TemplateProgram (genParam indTransEnv true true "inAllVarsOf").
Local Transparent Coq_Init_Datatypes_bool_pmtcty_RR0.

Definition Top_alphaEquivariant_and_pmtcty_RR := and_RR.

Axiom Top_alphaEquivariant_beq_pmtcty_RR : beqType_RR beq beq.
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
Abort.


Module iff1.
Definition Vimpl1 : Set := nat.
Definition Vimpl2 : Set := nat.
Definition VimplRGood := Coq_Init_Datatypes_nat_pmtcty_RR0.

(*
Goal False.
let T:= type of (alphaEq_RR Vimpl1 Vimpl2 VimplRGood) in
let T := eval simpl in T in
idtac T.
Abort.

(forall (veq : Vimpl1 -> Vimpl1 -> bool) (veq₂ : Vimpl2 -> Vimpl2 -> bool),
 (forall (a1 : Vimpl1) (a2 : Vimpl2),
  Temp.Coq_Init_Datatypes_nat_pmtcty_RR0 a1 a2 ->
  forall (a3 : Vimpl1) (a4 : Vimpl2),
  Temp.Coq_Init_Datatypes_nat_pmtcty_RR0 a3 a4 ->
  Temp.Coq_Init_Datatypes_bool_pmtcty_RR0 (veq a1 a3) (veq₂ a2 a4)) ->
 forall fuel fuel₂ : nat,
 Temp.Coq_Init_Datatypes_nat_pmtcty_RR0 fuel fuel₂ ->
 forall (t1 : Tm Vimpl1) (t1₂ : Tm Vimpl2),
 Temp.Top_alphaEquivariant_Tm_pmtcty_RR0 Vimpl1 Vimpl2 VimplRGood t1 t1₂ ->
 forall (t2 : Tm Vimpl1) (t2₂ : Tm Vimpl2),
 Temp.Top_alphaEquivariant_Tm_pmtcty_RR0 Vimpl1 Vimpl2 VimplRGood t2 t2₂ ->
 BestRel
   ((fix alphaEq (fuel0 : nat) (t0 t3 : Tm Vimpl1) {struct fuel0} : Prop :=
       match fuel0 with
       | 0%nat => beq true false
       | S fuel1 =>
           match t0 with
           | var _ v1 =>
               match t3 with
               | var _ v2 => beq (veq v1 v2) true
               | lam _ _ _ => beq true false
               | app _ _ _ => beq true false
               end
           | lam _ v1 b1 =>
               match t3 with
               | var _ _ => beq true false
               | lam _ v2 b2 =>
                   forall vf : Vimpl1,
                   beq (inAllVarsOf Vimpl1 veq vf t0) false ->
                   beq (inAllVarsOf Vimpl1 veq vf t3) false ->
                   alphaEq fuel1 (substAux Vimpl1 veq v1 (var Vimpl1 vf) b1)
                     (substAux Vimpl1 veq v2 (var Vimpl1 vf) b2)
               | app _ _ _ => beq true false
               end
           | app _ l1 r1 =>
               match t3 with
               | var _ _ => beq true false
               | lam _ _ _ => beq true false
               | app _ l2 r2 => and (alphaEq fuel1 l1 l2) (alphaEq fuel1 r1 r2)
               end
           end
       end) fuel t1 t2)
   ((fix alphaEq₂ (fuel₂0 : nat) (t1₂0 t2₂0 : Tm Vimpl2) {struct fuel₂0} : Prop :=
       match fuel₂0 with
       | 0%nat => beq true false
       | S fuel₂1 =>
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
                   forall vf₂ : Vimpl2,
                   beq (inAllVarsOf Vimpl2 veq₂ vf₂ t1₂0) false ->
                   beq (inAllVarsOf Vimpl2 veq₂ vf₂ t2₂0) false ->
                   alphaEq₂ fuel₂1 (substAux Vimpl2 veq₂ v1₂ (var Vimpl2 vf₂) b1₂)
                     (substAux Vimpl2 veq₂ v2₂ (var Vimpl2 vf₂) b2₂)
               | app _ _ _ => beq true false
               end
           | app _ l1₂ r1₂ =>
               match t2₂0 with
               | var _ _ => beq true false
               | lam _ _ _ => beq true false
               | app _ l2₂ r2₂ => and (alphaEq₂ fuel₂1 l1₂ l2₂) (alphaEq₂ fuel₂1 r1₂ r2₂)
               end
           end
       end) fuel₂ t1₂ t2₂))
*)
Definition veq := Nat.eqb.
Definition veq₂ := Nat.eqb.

  
(* should be easy to prove *)
Axiom  veq_R :
(forall (a1 : Vimpl1) (a2 : Vimpl2),
  Temp.Coq_Init_Datatypes_nat_pmtcty_RR0 a1 a2 ->
  forall (a3 : Vimpl1) (a4 : Vimpl2),
  Temp.Coq_Init_Datatypes_nat_pmtcty_RR0 a3 a4 ->
  Temp.Coq_Init_Datatypes_bool_pmtcty_RR0 (veq a1 a3) (veq₂ a2 a4)).

Definition fuel :nat :=3.
Definition fuel₂ :nat :=3.

Run TemplateProgram (genParam indTransEnv true true "fuel").

Lemma alphaIff : forall 
(fuel1 fuel2 : nat)
(fuelR : Temp.Coq_Init_Datatypes_nat_pmtcty_RR0 fuel1 fuel2)
(tml tmr tml2 tmr2 : Tm nat)
(tmRL : Temp.Top_alphaEquivariant_Tm_pmtcty_RR0 Vimpl1 Vimpl2 VimplRGood
  tml tml2)
(tmRR : Temp.Top_alphaEquivariant_Tm_pmtcty_RR0 Vimpl1 Vimpl2 VimplRGood
  tmr tmr2),
(alphaEq Vimpl1 veq fuel1 tml tmr) <-> (alphaEq Vimpl2 veq₂ fuel2 tml2 tmr2).
Proof using.
  intros.
  pose proof (alphaEq_RR Vimpl1 Vimpl2 VimplRGood veq veq₂ veq_R fuel1 fuel2 fuelR) as H.
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


End iff1.


