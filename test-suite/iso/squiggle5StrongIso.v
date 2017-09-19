
Require Import squiggle5.
Require Import ReflParam.unusedVar.
Require Import JMeq.
Require Import ReflParam.common.
Require Import ReflParam.templateCoqMisc.
Require Import String.
Require Import List.
Require Import Template.Ast.
Require Import SquiggleEq.terms.
Require Import ReflParam.paramDirect ReflParam.indType.
Require Import ReflParam.indProp.
Require Import SquiggleEq.substitution.
Require Import ReflParam.PiTypeR.
Import ListNotations.
Open Scope string_scope.

Require Import ReflParam.Trecord.
Require Import ReflParam.unusedVar.

(** https://github.com/aa755/ReduceAwayVar *)
Require Import ReduceAwayVar.ReduceAwayVar.
(** the above plugin only tries to eliminate one variable at a time.
So, we invoke it twice: once to eliminate the OneToOne hypothesis for BTmᵣ,
then for Tmᵣ*)

Section Test.
Variables 
(Tm Tm₂ : Set)
(Tmᵣ : Tm -> Tm₂ -> Prop)
(TmᵣTot : TotalHeteroRel Tmᵣ)
(TmᵣOne : oneToOne Tmᵣ)
(BTm BTm₂ : Set)
(BTmᵣ : BTm -> BTm₂ -> Prop)
(BTmᵣTot : TotalHeteroRel BTmᵣ)
.

(* The plugin takes a lambda term and tries to eliminate the first argument. 
(The result is declared as [sthm].)
In the
process, it may be able to eliminate other variables too. In this case, it 
successfully eliminates even the variable [BTmᵣTot] declared above *)
Time ReduceAwayLamVar sthm := (
fun (BTmᵣOne : oneToOne BTmᵣ) (* plugin's goal is to eliminate this*) =>
(* for now, we manually eta expand the pair type with the relation and its 2 proofs *)
let A_R := (@Build_GoodRel allProps _ _ Tmᵣ TmᵣTot TmᵣOne) in
let B_R := (@Build_GoodRel allProps _ _ BTmᵣ BTmᵣTot BTmᵣOne) in
Top_squiggle5_obseq_pmtcty_RR _ _ A_R _ _ B_R (* the result of weak isorel translation *)
).


(** As expected, [sthm], which is the output of the [ReduceAwayLamVar] plugin,
is definitionally equal to the input, because the [reflexivity] proof works.*)
Lemma testDefn (BTmᵣOne : oneToOne BTmᵣ):
let A_R := (@Build_GoodRel allProps _ _ Tmᵣ TmᵣTot TmᵣOne) in
let B_R := (@Build_GoodRel allProps _ _ BTmᵣ BTmᵣTot BTmᵣOne) in
JMeq 
  (Top_squiggle5_obseq_pmtcty_RR _ _ A_R _ _ B_R)
  sthm.
Proof using.
  reflexivity.
Qed.

End Test.
Notation π₁ := BestR.
Notation IsoRel := BestRel.
Check sthm.

(*
forall (Tm Tm₂ : Set) (Tmᵣ : Tm -> Tm₂ -> Prop)
         (TmᵣTot : TotalHeteroRel Tmᵣ) (TmᵣOne : oneToOne Tmᵣ)
         (BTm BTm₂ : Set) 
         (BTmᵣ : BTm -> BTm₂ -> Prop)
         (* The plugin managed to eliminate not only the [OneToOne] hypothesis for BTmᵣ, but also the [Total] hypothesis *)
         (applyBtm : BTm -> Tm -> Tm) (applyBtm₂ : BTm₂ -> Tm₂ -> Tm₂),
       (forall (a1 : BTm) (a2 : BTm₂),
        BTmᵣ a1 a2 ->
        π₁
          (PiGoodSet Tm Tm₂ {| R := Tmᵣ; Rtot := TmᵣTot; Rone := TmᵣOne |}
             (fun _ : Tm => Tm) (fun _ : Tm₂ => Tm₂)
             (fun (H : Tm) (H0 : Tm₂)
                (_ : π₁ {| R := Tmᵣ; Rtot := TmᵣTot; Rone := TmᵣOne |} H H0)
              => {| R := Tmᵣ; Rtot := TmᵣTot; Rone := TmᵣOne |}))
          (applyBtm a1) (applyBtm₂ a2)) ->
       forall (tmKind : Tm -> TmKind Tm BTm)
         (tmKind₂ : Tm₂ -> TmKind Tm₂ BTm₂),
       (forall (a1 : Tm) (a2 : Tm₂),
        π₁ {| R := Tmᵣ; Rtot := TmᵣTot; Rone := TmᵣOne |} a1 a2 ->
        Top_squiggle5_TmKind_pmtcty_RR0 Tm Tm₂
          (π₁ {| R := Tmᵣ; Rtot := TmᵣTot; Rone := TmᵣOne |}) BTm BTm₂ BTmᵣ
          (tmKind a1) (tmKind₂ a2)) ->
       forall (tl : Tm) (tl₂ : Tm₂),
       π₁ {| R := Tmᵣ; Rtot := TmᵣTot; Rone := TmᵣOne |} tl tl₂ ->
       forall (tr : Tm) (tr₂ : Tm₂),
       π₁ {| R := Tmᵣ; Rtot := TmᵣTot; Rone := TmᵣOne |} tr tr₂ ->
       IsoRel (forall a : nat, obsEq Tm BTm applyBtm tmKind a tl tr)
         (forall a : nat, obsEq Tm₂ BTm₂ applyBtm₂ tmKind₂ a tl₂ tr₂)
*)


(* Now, we do the same for Tmᵣ: eliminate the hypothesis requiring it to be OneToOne.*)
Section Test2.
Variables 
(Tm Tm₂ : Set)
(Tmᵣ : Tm -> Tm₂ -> Prop)
(TmᵣTot : TotalHeteroRel Tmᵣ)
(BTm BTm₂ : Set)
(BTmᵣ : BTm -> BTm₂ -> Prop).

Time  ReduceAwayLamVar obseqStrongIso := 
(
fun (poa : oneToOne Tmᵣ) =>
@sthm _ _ Tmᵣ TmᵣTot poa _ _ BTmᵣ (* [sthm] was produced by the first invocation (above) *)
).

(*
Finished transaction in 1.547 secs (1.259u,0.s) (successful)
*)

End Test2.

Check obseqStrongIso.

(*
obseqStrongIso
     : forall (Tm Tm₂ : Set) (Tmᵣ : Tm -> Tm₂ -> Prop),
       TotalHeteroRel Tmᵣ ->
       (* the OneToOne hypothesis was eliminated for Tmᵣ *)
       forall (BTm BTm₂ : Set) 
       (BTmᵣ : BTm -> BTm₂ -> Prop)
         (applyBtm : BTm -> Tm -> Tm) (applyBtm₂ : BTm₂ -> Tm₂ -> Tm₂),
       (forall (a1 : BTm) (a2 : BTm₂),
        BTmᵣ a1 a2 ->
        forall (a3 : Tm) (a4 : Tm₂),
        Tmᵣ a3 a4 -> Tmᵣ (applyBtm a1 a3) (applyBtm₂ a2 a4)) ->
       forall (tmKind : Tm -> TmKind Tm BTm)
         (tmKind₂ : Tm₂ -> TmKind Tm₂ BTm₂),
       (forall (a1 : Tm) (a2 : Tm₂),
        Tmᵣ a1 a2 ->
        Top_squiggle5_TmKind_pmtcty_RR0 Tm Tm₂ Tmᵣ BTm BTm₂ BTmᵣ (tmKind a1)
          (tmKind₂ a2)) ->
       forall (tl : Tm) (tl₂ : Tm₂),
       Tmᵣ tl tl₂ ->
       forall (tr : Tm) (tr₂ : Tm₂),
       Tmᵣ tr tr₂ ->
       BestRel (forall a : nat, obsEq Tm BTm applyBtm tmKind a tl tr)
         (forall a : nat, obsEq Tm₂ BTm₂ applyBtm₂ tmKind₂ a tl₂ tr₂)

*)


(* folding definitions and alpha renaming in above for readability *)
Definition obseqStrongIsoType :=
forall 
  (Tm Tm₂ : Set) (Tmᵣ : Tm -> Tm₂ -> Prop)
  (Tmᵣtot: TotalHeteroRel Tmᵣ)
  (BTm BTm₂ : Set) (BTmᵣ : BTm -> BTm₂ -> Prop)
  (applyBtm : BTm -> Tm -> Tm) (applyBtm₂ : BTm₂ -> Tm₂ -> Tm₂)
  (applyBtmᵣ : forall (b : BTm) (b₂ : BTm₂) (bᵣ: BTmᵣ b b₂) 
    (a : Tm) (a₂ : Tm₂) (aᵣ : Tmᵣ a a₂), Tmᵣ (applyBtm b a) (applyBtm₂ b₂ a₂))
  (tmKind : Tm -> TmKind Tm BTm)
  (tmKind₂ : Tm₂ -> TmKind Tm₂ BTm₂)
  (tmKindᵣ : forall (a : Tm) (a₂ : Tm₂)
        (aᵣ: Tmᵣ a a₂),
        Top_squiggle5_TmKind_pmtcty_RR0 Tm Tm₂ Tmᵣ BTm BTm₂ BTmᵣ (tmKind a)
          (tmKind₂ a₂))
  (tl : Tm) (tl₂ : Tm₂)
  (tlᵣ: Tmᵣ tl tl₂)
  (tr : Tm) (tr₂ : Tm₂)
  (trᵣ: Tmᵣ tr tr₂),
     IsoRel (obseq Tm BTm applyBtm tmKind tl tr)
             (obseq Tm₂ BTm₂ applyBtm₂ tmKind₂ tl₂ tr₂).

(** confirming that our readability improvement did not change the meaning *)
Goal JMeq obseqStrongIsoType ltac:(let T:=type of obseqStrongIso in exact T).
reflexivity.
Qed.

