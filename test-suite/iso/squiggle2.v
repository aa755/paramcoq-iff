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


Set Imlicit Arguments.

Inductive eqs (A : Set) (x : A) : forall (a:A), Prop :=  
  eq_refls : eqs A x x.

(*
Inductive existp (A : Set) (P : A -> Prop) : Prop :=
  exist : forall x : A, P x -> existp A P.
  
Lemma PiGoodPropAux :
  forall (A1 A2 :Set) (A_R:  @GoodRel [Total] A1 A2) 
  (B1: A1 -> Prop) 
  (B2: A2 -> Prop) 
  (B_R: forall a1 a2, @R _ _ _ A_R a1 a2 ->  @GoodRel [Total] (B1 a1) (B2 a2)),
  BestRel (existp _ B1) (existp _ B2).
Admitted.
 *)
Inductive option (A : Set) : Set :=  Some : A -> option A | None : option A.
Arguments Some {A} _.
Arguments None {A}.

(*
Inductive sum (A B : Set) : Set :=  inl : A -> sum A B | inr : B -> sum A B.
Inductive list (A : Set) : Set :=  nil : list A | cons : A -> list A -> list A.
Print prod.
Inductive prod (A B : Set) : Set :=  pair : A -> B -> prod A B.


Arguments inl {A} {B} _.
Arguments inr {A} {B} _.

Arguments nil {A}.
Arguments cons {A} _ _.

Arguments pair {A} {B} _ _.

Notation " ( x , y ) " := (pair x y).
(*
Notation "[ ]" := nil (format "[ ]") : list_scope.
*)
Notation "[ x ]" := (cons x nil) : list_scope.
Notation "[ x , y , .. , z ]" := (cons x (cons y .. (cons z nil) ..)) : list_scope.
*)

Definition isNone {A:Set} (oa: option A) :=
  match oa with
  | Some _ => false
  | None => true
  end.
Infix "+" := sum:type_scope.
(*
Definition beq (b1 b2 : bool) := eqs bool b1 b2.
Infix "≡" := beq (at level 80).
 *)

Inductive tmExt (Tm:Set) :=
  | elam (bt: Tm) 
  | eapp (f a: Tm) 
  | enum (n: nat).
Arguments elam {Tm} bt.
Arguments eapp {Tm} f a.
Arguments enum {Tm} n.
Section Squiggle.
  (* Variable V:Set. This interface is too abstract for exposing V *)
  Variable Tm:Set.
  (*
  Variable app: Tm -> Tm -> Tm.
  Variable lam: Tm -> Tm.
  Variable num: nat -> Tm.
  *)
  Variable elimTerm:  Tm -> (tmExt Tm).

  (* Tm now stands for NTerm + BTerm. the arg of a lam must be a BTerm.
   This is a nop if Tm was a NTerm. *)
  Variable applyBtm: Tm -> Tm -> Tm.

Fixpoint evaln (n:nat) (t:Tm): option Tm :=
match n with
|0%nat => None
| S n =>
  match (elimTerm t)
  with
  | elam _
  | enum _ => Some t
  | eapp f a =>
    match evaln n f, evaln n a with
    | Some f, Some a =>
      match (elimTerm f) with
      | elam bt =>
        Some (applyBtm bt a)
      | _ => None
      end
    | _,_ => None
    end        
  end
end.

Open Scope nat_scope.
(*
Fixpoint sqlek (k:nat) (tl tr:Tm): Prop :=
  forall (nl:nat), 
    match (evaln nl tl) with
    | None => eqs _ 0 0
    | Some vl => existp _ (fun (nr:nat) =>
        match (evaln nl tl) with
        | None => eqs _ 0 1
        | Some vr =>
          match elimTerm vl, elimTerm vr with
          | Some (num nl, _), Some (num nr,_) => eqs _ nl nr
          | Some (lam,[inr btl]), Some (lam,[inr btr]) =>
            match k with
            | 0 => eqs _ 0 1
            | S k =>
              forall (ta: Tm), sqlek k (applyBtm btl ta) (applyBtm btr ta)
            end
          | _ , _=> eqs _ 0 1
          end
        end
                         )
    end.
 *)

  (*
  match (elimTerm tl), (elimTerm tr) with
  | (num n1, _), (num n2,_) => eqs _ n1 n2
  | (lam [inr ])
*)  



(* just this would be an example. However, because it is not recursive,
 even tauto may be able to prove it. Even if we only show this on paper,
we should have a more complex (recursively defined undefined relation)
in the appendix *)
Definition divergesIff (tl tr:Tm) : Prop :=
  (forall (nsteps:nat), eqs _ (isNone (evaln nsteps tl)) true) <->
  (forall (nsteps:nat), eqs _ (isNone (evaln nsteps tr)) true).

Fixpoint obsEq (k:nat)(tl tr:Tm) {struct k}: Prop :=
  divergesIff tl tr /\ (* need to eliminate the oneOne of Prop inductives and use PI *)
  forall (nsteps:nat), 
match k with | 0 => eqs _ 0 1 | S k =>
    match evaln nsteps tl, evaln nsteps tr with
    | Some vl, Some vr => 
          match elimTerm vl, elimTerm vr with
          | enum nl , enum nr => eqs _ nl nr
          | elam btl , elam btr =>
              forall (ta: Tm), obsEq k (applyBtm btl ta) (applyBtm btr ta)
          | eapp fl al , eapp fr ar =>
            obsEq k fl fr /\ obsEq k al ar
          | _,_ => eqs _ 0 1
          end
    | _, _  => eqs _ 0 0
    end
end.

End Squiggle.

Print obsEq.

Print option.
Run TemplateProgram (genParamIndAll [] "Coq.Init.Datatypes.bool").
Run TemplateProgram (genParamIndAll [] "Top.squiggle2.eqs").
Run TemplateProgram (genParamIndAll [] "Coq.Init.Datatypes.nat").
Run TemplateProgram (genParamIndAll [] "Top.squiggle2.option").
(*
Run TemplateProgram (genParamIndAll [] "Top.squiggle2.sum").
Run TemplateProgram (genParamIndAll [] "Top.squiggle2.list").
Run TemplateProgram (genParamIndAll [] "Top.squiggle2.prod").
*)

(* and, unlike exists, allows singleton elim because the 2 args of its constructor
are proofs *)
Run TemplateProgram (genParamIndAll [] "Coq.Init.Logic.and").
Run TemplateProgram (genParamIndAll [] "Top.squiggle2.tmExt").


Run TemplateProgram (mkIndEnv "indTransEnv" [
"Coq.Init.Datatypes.bool" ; "Coq.Init.Datatypes.nat";
"Coq.Init.Logic.and"; "Top.squiggle2.eqs"; 
 "Top.squiggle2.option"; 
 (* "Top.squiggle2.sum";  "Top.squiggle2.list"; "Top.squiggle2.prod"; *)
 "Top.squiggle2.tmExt"]).

Run TemplateProgram (genWrappers indTransEnv).

Run TemplateProgram (genParam indTransEnv true true "Top.squiggle2.evaln").
(* slow and the result is bloated *)

Run TemplateProgram (genParam indTransEnv true true "Top.squiggle2.isNone").

Run TemplateProgram (genParam indTransEnv true true "Coq.Init.Logic.iff").

Run TemplateProgram (genParam indTransEnv true true "Top.squiggle2.divergesIff").
(* quick *)
Run TemplateProgram (genParam indTransEnv true true "Top.squiggle2.obsEq").
(* bloated *)

Eval compute in (oldIndNames indTransEnv).
Opaque 
Coq_Init_Datatypes_bool_pmtcty_RR0_constr_0_inv Coq_Init_Datatypes_bool_pmtcty_RR0_constr_0_tot Coq_Init_Datatypes_bool_pmtcty_RR0_constr_1 Coq_Init_Datatypes_bool_pmtcty_RR0_constr_1_inv Coq_Init_Datatypes_bool_pmtcty_RR0_constr_1_tot Coq_Init_Datatypes_nat_pmtcty_RR0 Coq_Init_Datatypes_nat_pmtcty_RR0_constr_0 Coq_Init_Datatypes_nat_pmtcty_RR0_constr_0_inv Coq_Init_Datatypes_nat_pmtcty_RR0_constr_0_tot Coq_Init_Datatypes_nat_pmtcty_RR0_constr_1 Coq_Init_Datatypes_nat_pmtcty_RR0_constr_1_inv Coq_Init_Datatypes_nat_pmtcty_RR0_constr_1_tot Coq_Init_Logic_and_pmtcty_RR0 Coq_Init_Logic_and_pmtcty_RR0_constr_0 Coq_Init_Logic_and_pmtcty_RR0_constr_0_inv Coq_Init_Logic_and_pmtcty_RR0_constr_0_tot Top_squiggle2_eqs_pmtcty_RR0 Top_squiggle2_eqs_pmtcty_RR0_constr_0 Top_squiggle2_eqs_pmtcty_RR0_constr_0_inv Top_squiggle2_eqs_pmtcty_RR0_constr_0_tot Top_squiggle2_option_pmtcty_RR0 Top_squiggle2_option_pmtcty_RR0_constr_0 Top_squiggle2_option_pmtcty_RR0_constr_0_inv Top_squiggle2_option_pmtcty_RR0_constr_0_tot Top_squiggle2_option_pmtcty_RR0_constr_1 Top_squiggle2_option_pmtcty_RR0_constr_1_inv Top_squiggle2_option_pmtcty_RR0_constr_1_tot Top_squiggle2_tmExt_pmtcty_RR0 Top_squiggle2_tmExt_pmtcty_RR0_constr_0 Top_squiggle2_tmExt_pmtcty_RR0_constr_0_inv Top_squiggle2_tmExt_pmtcty_RR0_constr_0_tot Top_squiggle2_tmExt_pmtcty_RR0_constr_1 Top_squiggle2_tmExt_pmtcty_RR0_constr_1_inv Top_squiggle2_tmExt_pmtcty_RR0_constr_1_tot Top_squiggle2_tmExt_pmtcty_RR0_constr_2 Top_squiggle2_tmExt_pmtcty_RR0_constr_2_inv Top_squiggle2_tmExt_pmtcty_RR0_constr_2_tot
.


Require Import ReflParam.unusedVar.

Lemma dependsOnlyOnRelEvaln  : existsAGoodnessFreeImpl
  (Top_squiggle2_evaln_pmtcty_RR).
  eexists.
  eexists.
  intros.
  set (fvv:= Top_squiggle2_evaln_pmtcty_RR _ _ V_R).
  simpl in *.
  unfold Top_squiggle2_evaln_pmtcty_RR in fvv.
  simpl in fvv.
  simpl in *.
  do 10(
  unfold
Coq_Init_Datatypes_bool_pmtcty_RR0_constr_0_inv_iso, 
Coq_Init_Datatypes_bool_pmtcty_RR0_constr_1_inv_iso, 
Coq_Init_Datatypes_nat_pmtcty_RR0_iso, 
Coq_Init_Datatypes_nat_pmtcty_RR0_constr_0_inv_iso, 
Coq_Init_Datatypes_nat_pmtcty_RR0_constr_0_iso, 
Coq_Init_Datatypes_nat_pmtcty_RR0_constr_1_inv_iso, 
Coq_Init_Datatypes_nat_pmtcty_RR0_constr_1_iso, 
Coq_Init_Logic_and_pmtcty_RR0_iso, 
Coq_Init_Logic_and_pmtcty_RR0_constr_0_inv_iso, 
Coq_Init_Logic_and_pmtcty_RR0_constr_0_iso, 
Top_squiggle2_eqs_pmtcty_RR0_iso, 
Top_squiggle2_eqs_pmtcty_RR0_constr_0_inv_iso, 
Top_squiggle2_eqs_pmtcty_RR0_constr_0_iso, 
Top_squiggle2_option_pmtcty_RR0_iso, 
Top_squiggle2_option_pmtcty_RR0_constr_0_inv_iso, 
Top_squiggle2_option_pmtcty_RR0_constr_0_iso, 
Top_squiggle2_option_pmtcty_RR0_constr_1_inv_iso, 
Top_squiggle2_option_pmtcty_RR0_constr_1_iso, 
Top_squiggle2_tmExt_pmtcty_RR0_iso, 
Top_squiggle2_tmExt_pmtcty_RR0_constr_0_inv_iso, 
Top_squiggle2_tmExt_pmtcty_RR0_constr_0_iso, 
Top_squiggle2_tmExt_pmtcty_RR0_constr_1_inv_iso, 
Top_squiggle2_tmExt_pmtcty_RR0_constr_1_iso, 
Top_squiggle2_tmExt_pmtcty_RR0_constr_2_inv_iso, 
Top_squiggle2_tmExt_pmtcty_RR0_constr_2_iso in fvv;
  cbn in fvv;
  simpl in *;
  cbn in *).
  reflexivity.
Defined.  (* works *)
  
(*
Lemma dependsOnlyOnTotobsEq  : existsAOneFreeImpl
  (Top_squiggle2_obsEq_pmtcty_RR).
Proof.
  eexists.
  eexists.
  intros.
  set (fvv:= Top_squiggle2_obsEq_pmtcty_RR _ _ V_R).
  simpl in *.
  cbn in fvv.
  unfold Top_squiggle2_obsEq_pmtcty_RR,
  Top_squiggle2_divergesIff_pmtcty_RR,
  Top_squiggle2_evaln_pmtcty_RR in fvv
  .
  do 10(
  unfold
Coq_Init_Datatypes_bool_pmtcty_RR0_constr_0_inv_iso, 
Coq_Init_Datatypes_bool_pmtcty_RR0_constr_1_inv_iso, 
Coq_Init_Datatypes_nat_pmtcty_RR0_iso, 
Coq_Init_Datatypes_nat_pmtcty_RR0_constr_0_inv_iso, 
Coq_Init_Datatypes_nat_pmtcty_RR0_constr_0_iso, 
Coq_Init_Datatypes_nat_pmtcty_RR0_constr_1_inv_iso, 
Coq_Init_Datatypes_nat_pmtcty_RR0_constr_1_iso, 
Coq_Init_Logic_and_pmtcty_RR0_iso, 
Coq_Init_Logic_and_pmtcty_RR0_constr_0_inv_iso, 
Coq_Init_Logic_and_pmtcty_RR0_constr_0_iso, 
Top_squiggle2_eqs_pmtcty_RR0_iso, 
Top_squiggle2_eqs_pmtcty_RR0_constr_0_inv_iso, 
Top_squiggle2_eqs_pmtcty_RR0_constr_0_iso, 
Top_squiggle2_option_pmtcty_RR0_iso, 
Top_squiggle2_option_pmtcty_RR0_constr_0_inv_iso, 
Top_squiggle2_option_pmtcty_RR0_constr_0_iso, 
Top_squiggle2_option_pmtcty_RR0_constr_1_inv_iso, 
Top_squiggle2_option_pmtcty_RR0_constr_1_iso, 
Top_squiggle2_tmExt_pmtcty_RR0_iso, 
Top_squiggle2_tmExt_pmtcty_RR0_constr_0_inv_iso, 
Top_squiggle2_tmExt_pmtcty_RR0_constr_0_iso, 
Top_squiggle2_tmExt_pmtcty_RR0_constr_1_inv_iso, 
Top_squiggle2_tmExt_pmtcty_RR0_constr_1_iso, 
Top_squiggle2_tmExt_pmtcty_RR0_constr_2_inv_iso, 
Top_squiggle2_tmExt_pmtcty_RR0_constr_2_iso in fvv;
  cbn in fvv;
  simpl in *;
  cbn in *.
  reflexivity.
Defined.
*)
(*
Lemma dependsOnlyOnTotdivergesIff  : existsAOneFreeImpl
  (Top_squiggle2_divergesIff_pmtcty_RR).
Proof.
  eexists.
  eexists.
  intros.
  set (fvv:= Top_squiggle2_divergesIff_pmtcty_RR _ _ V_R).
  simpl in *.
  lazy in fvv.
  reflexivity. (* works *)
Defined.
*)
(*
Lemma dependsOnlyOnTotdivergesIff (V V₂ : Set) : @dependsOnlyOnRelTot V V₂ _
  (Top_squiggle2_divergesIff_pmtcty_RR V V₂).
Proof.
  intros ? ? ?.
  destruct V_R1.
  reflexivity.
Qed.
*)