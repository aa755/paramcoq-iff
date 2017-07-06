(*
abhishek@brixpro:~/parametricity/reflective-paramcoq/test-suite/iso$ ./coqid.sh IWTS
*)

Require Import SquiggleEq.terms.


Require Import ReflParam.common.
Require Import ReflParam.templateCoqMisc.
Require Import String.
Require Import List.
Require Import Template.Ast.
Require Import SquiggleEq.terms.
Require Import ReflParam.paramDirect ReflParam.indType.
Require Import SquiggleEq.substitution.
Require Import ReflParam.PiTypeR.
Import ListNotations.
Open Scope string_scope.

Require Import ReflParam.PIWNew.

Require Import Template.Template.

Inductive IWT (I A : Set) (B : A -> Set) (AI : A -> I) 
(BI : forall (a : A), B a -> I) : forall (i:I), Set :=
    iwt : forall (a : A) (lim: forall b : B a, IWT I A B AI BI (BI a b)),
     IWT I A B AI BI (AI a).
    
Run TemplateProgram (genParamIndAll [] "Top.IWTS.IWT").

Print Assumptions Top_IWTS_IWT_pmtcty_RR0tot12.
Print Assumptions Top_IWTS_IWT_pmtcty_RR0one12.

Run TemplateProgram (mkIndEnv "indTransEnv" ["Top.IWTS.IWT"]).
Require Import ReflParam.Trecord.
Print Top_IWTS_IWT_pmtcty_RR0_constr_0_tot.
Run TemplateProgram (genWrappers indTransEnv).

(* Set version *)
Definition IWT_recs :=
fun (I A : Set) (B : A -> Set) (AI : A -> I) (BI : forall a : A, B a -> I)
  (P : forall i : I, IWT I A B AI BI i -> Set)
  (f : forall (a : A) (lim : forall b : B a, IWT I A B AI BI (BI a b)),
       (forall b : B a, P (BI a b) (lim b)) -> P (AI a) (iwt I A B AI BI a lim)) =>
fix F (i : I) (i0 : IWT I A B AI BI i) {struct i0} : P i i0 :=
  match i0 as i2 in (IWT _ _ _ _ _ i1) return (P i1 i2) with
  | iwt _ _ _ _ _ a lim => f a lim (fun b : B a => F (BI a b) (lim b))
  end.

Run TemplateProgram (genParam indTransEnv IsoRel true "Top.IWTS.IWT_recs").

Print Top_IWTS_IWT_recs_pmtcty_RR.

Section Comp.
(*
Now we want to verify that the IsoRel translation (before unused-var analysis) preserves
reductions.
*)

Variables (I A : Set) (B : A -> Set) (AI : A -> I)  (BI : forall (a : A), B a -> I)
  (P : forall i : I, IWT I A B AI BI i -> Set)
  (f : forall (a : A) (lim : forall b : B a, IWT I A B AI BI (BI a b)),
       (forall b : B a, P (BI a b) (lim b)) -> P (AI a) (iwt I A B AI BI a lim))
  (a:A) 
  (lim: forall b : B a, IWT I A B AI BI (BI a b)).

Definition LHS := IWT_recs _ _ _ _ _ _ f _ (iwt _ _ _ _ _ a lim).
Definition RHS := f a lim (fun b : B a => IWT_recs _ _ _ _ _ _ f (BI a b) (lim b)).

(** To show that the equality holds definitionally, the proof must be reflexivity. *)
Lemma iotaRed  :
  LHS  = RHS.
Proof using. reflexivity. Qed.

(** Below, we check that this iota reduction is preserved after IsoRel translation  
*)

End Comp.

(** perform the IsoRel translation of LHS and RHS to respectively generate 
Top_IWTS_LHS_pmtcty_RR and Top_IWTS_RHS_pmtcty_RR
*)
Run TemplateProgram (genParam indTransEnv IsoRel true "Top.IWTS.LHS").
Run TemplateProgram (genParam indTransEnv IsoRel true "Top.IWTS.RHS").

Lemma IsoRelPreservesIotaDefinitionallyDirect:
Top_IWTS_LHS_pmtcty_RR = Top_IWTS_RHS_pmtcty_RR.
Proof.
reflexivity.
Qed.
