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
Require Import templateCoqMisc.
Require Import Template.Template.
Require Import Template.Ast.

Require Import paramDirect.

Require Import Program.
Open Scope program_scope.

Inductive red : STerm -> STerm -> Prop := .


(* Move *)
Definition tvmap_bterm := 
fun {V1 V2 O : Type} (fv : V1-> V2) =>
@tmap_bterm V1 V2 O O fv (@id O).

(* (free_vars (tvmap vprime t)) = map vprime (free_vars t) *)

Let tprime : STerm -> STerm :=  tvmap vprime.
Let btprime : SBTerm -> SBTerm :=  tvmap_bterm vprime.

(* Lemma 2.1 in Lasson.
Unlike in Certicoq, here we are talking about reduction, which
can happen even under binders. So, we don't have the luxury
of only talking about closed terms. So alpha equality is inevitable in later lemmas.
In this lemma, by ensuring that freshVars commutes with vprime, we may be
able to get it with strict equality
*)


Require Import Psatz.

Local Opaque BinNat.N.add .


Lemma vPrimeNeqV : forall v,  v <> vprime v.
Proof.
  intros ? Heq. apply (f_equal fst) in Heq.
  simpl in Heq. lia.
Qed.

Lemma vRelNeqV : forall v,  v <> vrel v.
Proof.
  intros ? Heq. apply (f_equal fst) in Heq.
  simpl in Heq. lia.
Qed.

Lemma vRelNeqVPrime : forall v, vprime v <> vrel v.
Proof.
  intros ? Heq. apply (f_equal fst) in Heq.
  simpl in Heq. lia.
Qed.

Hint Rewrite (fun v => not_eq_beq_var_false _ _ (vPrimeNeqV v)) : Param.
Hint Rewrite (fun v => not_eq_beq_var_false _ _ (vRelNeqVPrime v)) : Param.
Hint Rewrite (fun v => not_eq_beq_var_false _ _ (vRelNeqV v)) : Param.


Require Import NArith.

Definition varClass1 (v:V) : N := proj1_sig (varClass v).

Lemma varClassVPrime : forall v, varClass1 (vprime v) = 
  (1+ varClass1 v) mod 3.
Proof using.
  intros. unfold varClass1. simpl.
  rewrite N.add_mod;[| lia].
  refl.
Qed.  

Lemma varClassVRel : forall v, varClass1 (vrel v) = 
  (2+ varClass1 v) mod 3.
Proof using.
  intros. unfold varClass1. simpl.
  rewrite N.add_mod;[| lia].
  refl.
Qed.  

Lemma varClassNotEq : forall v1 v2, 
     (varClass1 v1 <> varClass1 v2) -> beq_var v1 v2 = false.
Proof.
  intros ? ? Heq.
  apply not_eq_beq_var_false.
  congruence.
Qed.

Hint Resolve vRelNeqVPrime vRelNeqV vPrimeNeqV : Param.

Lemma decideFalse P `{Decidable P} : ~P -> decide P = false.
Proof.
apply Decidable_sound_alt.
Qed.


Lemma vRelInjective v1 v2 : v1 <> v2 ->
  vrel v1 <> vrel v2.
Proof using.
  intros Heq.
  unfold vrel.
  intros Hc.
  destruct v1, v2.
  simpl in *.
  apply Heq.
  clear Heq.
  inverts Hc.
  f_equal; [lia|].
  SearchAbout String.append.
  SearchAbout String.get.
  destruct n0, n2; try inverts H1;[refl|].
  clear H0 n1. 
Admitted. (* append is injective *)
  
Hint Rewrite varClassVPrime: Param.
Hint Rewrite varClassVRel: Param.

Local Transparent BinNat.N.add .

Ltac hideRHS rhs :=
match goal with
  [ |- _ = ?r] => set (rhs:= r)
  end.
  
  Local Opaque vprime.
  Local Opaque vrel.

Lemma substAuxPrimeCommute: forall (A B: STerm) (x:V),
(* NO need to assume that vars in a and b and the var x have class 0 *)
tprime (ssubst_aux A [(x,B)]) =
ssubst_aux (tprime A) [(vprime x,tprime B)].
Admitted.

Lemma ifThenElseMap {A B:Type} (f: A->B) (b:bool) (t e : A):
  f (if b then t else e) = if b then (f t) else (f e).
Proof using.
  destruct b; auto.
Qed.

Lemma translateSubstCommute : forall (A B: STerm) (x:V),
(* disjoint (free_vars B) (bound_vars A) 
->*)
varsOfClass (x::(all_vars A (* ++ all_vars B*) )) userVar
->
let tr := translate true in
tr (ssubst_aux A [(x,B)])
= (ssubst_aux (tr A) [(x,B); (vprime x, tprime B); (vrel x, tr B)]).
Proof.
  simpl.
  induction A using NTerm_better_ind; intros B x Hvc;[|destruct o]; try refl;
    [ | | | | | | | |].
(* variable *)
- hideRHS rhs.
  simpl.
  rewrite beq_deq.
  cases_if as hd; subst.
  + simpl. unfold rhs. simpl.
    rewrite <- beq_var_refl.
    autorewrite with Param. refl.
  + simpl. unfold rhs. clear rhs.
    unfold all_vars in Hvc. simpl in *.
    unfold varsOfClass, lforall in Hvc.
    simpl in *; dLin_hyp.
    let tac:=
      autorewrite with Param;
      unfold varClass1;
      try setoid_rewrite Hyp; try setoid_rewrite Hyp0;
      compute; congruence in
    do 2 rewrite varClassNotEq by tac.
    rewrite not_eq_beq_var_false; auto;[].
    apply vRelInjective. assumption.
(* Lambda *)
- destruct lbt as [| b  lbt]; simpl; [refl|].
  (* process each BTerm before going to the next *)
  destruct b as [lv lamTyp].
  destruct lv as [|];[| refl].
  destruct lbt as [| b2  lbt]; [refl |].
  destruct b2 as [b2lv lamBody].
  destruct b2lv as [|lamVar b2lv];[refl|].
  destruct b2lv as [|];[|refl].
  destruct lbt as [|]; [| refl].
  hideRHS rhs. simpl.
  Local Opaque ssubst_bterm_aux.
  unfold rhs. clear rhs. simpl.
  unfold transLam, mkAppBeta. simpl.
  Local Transparent ssubst_bterm_aux.
    set (b:= match argSort with
                     | Some s => isPropOrSet s
                     | None => false
                     end
                     ).

  simpl ssubst_bterm_aux at 1.
  rewrite <- ssubst_aux_sub_filter2  with (l:=[vprime x; vrel x])
  (sub:=[(x, B); (vprime x, tprime B); (vrel x, translate true B)]) by admit.
  Local Opaque ssubst_bterm_aux. simpl.
  repeat rewrite deq_refl.
  repeat rewrite decideFalse by eauto with Param.
  symmetry.
  repeat rewrite decideFalse by eauto with Param.
  f_equal.
  f_equal.
  Local Transparent ssubst_bterm_aux.
  Local Opaque ssubst_aux sub_filter. simpl.
  f_equal.
  f_equal.
  rewrite decide_decideP.
  destruct (decideP (lamVar = x)).
  + subst.
    Local Transparent ssubst_aux sub_filter. simpl.
    repeat rewrite deq_refl.
    repeat rewrite decideFalse by eauto with Param.
    repeat rewrite sub_filter_nil_r. simpl.
    repeat rewrite deq_refl.
    repeat rewrite decideFalse by eauto with Param.
    simpl.
    unfold beq_var.
    repeat rewrite deq_refl.
    repeat rewrite decideFalse by eauto with Param.
    rewrite <- ssubst_aux_sub_filter2  with (l:=[vrel x])
      (sub:=[(vprime x, tprime B); (vrel x, translate true B)]) by admit.
    simpl.
    unfold beq_var.
    repeat rewrite deq_refl.
    repeat rewrite decideFalse by eauto with Param.
    rewrite <- substAuxPrimeCommute.
    repeat rewrite ssubst_aux_nil.
    do 7 f_equal.
    unfold mkApp. simpl.
    do 3 f_equal. unfold id. simpl. destruct b.
    unfold projTyRel, mkConstApp, mkApp. simpl.
    simpl.
    f_equal. 
    f_equal. 
    f_equal; f_equal;[|f_equal| do 2 f_equal].
    (* the two inferable arguments of projTyRel are causing problems.
      It seems that [[A]] must be let bound outside the scope of x and vprime x.
      Use 5 classes of vars?*)

Abort.

Definition capture (T: nat -> Set) (x:nat) (x: T x) := x.

Parametricity Recursive capture.

Print ReflParam_o_proof_o_v_o_capture_R .

Run TemplateProgram (printTermSq "capture").

Definition captureSyntax :=
(mkLamS (0, nNamed "T")
   (mkPiS (0, nAnon) (mkConstInd (mkInd "Coq.Init.Datatypes.nat" 0)) 
      (Some sSet) (mkSort sSet) None) None
   (mkLamS (3, nNamed "x") (mkConstInd (mkInd "Coq.Init.Datatypes.nat" 0)) 
      (Some sSet)
      (mkLamS (3, nNamed "x") (* changed 6 to 3*)
         (oterm (CApply 1)
            [bterm [] (vterm (0, nNamed "T")); bterm [] (vterm (3, nNamed "x"))])
         (Some sSet) (vterm (3, nNamed "x"))))).

Eval vm_compute in (translate false captureSyntax).

Definition captureTranslateSyntax
     := mkLamS (0, nNamed "T")
         (mkPiS (0, nAnon) (mkConstInd (mkInd "Coq.Init.Datatypes.nat" 0)) 
            (Some sSet) (mkSort sSet) None) None
         (mkLamS (1, nNamed "T₂")
            (mkPiS (1, nAnon) (mkConstInd (mkInd "Coq.Init.Datatypes.nat" 0)) 
               (Some sSet) (mkSort sSet) None) None
            (mkLamS (2, nNamed "T_R")
               (oterm (CApply 2)
                  [bterm []
                     (mkLamS (30, nNamed "ff")
                        (mkPiS (0, nAnon) (mkConstInd (mkInd "Coq.Init.Datatypes.nat" 0))
                           None
                           (oterm (CApply 1)
                              [bterm []
                                 (mkLamS (0, nAnon)
                                    (mkConstInd (mkInd "Coq.Init.Datatypes.nat" 0)) None
                                    (mkSort sSet)); bterm [] (vterm (0, nAnon))]) None) None
                        (mkLamS (31, nNamed "ff₂")
                           (mkPiS (1, nAnon) (mkConstInd (mkInd "Coq.Init.Datatypes.nat" 0))
                              None
                              (oterm (CApply 1)
                                 [bterm []
                                    (mkLamS (1, nAnon)
                                       (mkConstInd (mkInd "Coq.Init.Datatypes.nat" 0)) None
                                       (mkSort sSet)); bterm [] (vterm (1, nAnon))]) None)
                           None
                           (mkPiS (0, nAnon) (mkConstInd (mkInd "Coq.Init.Datatypes.nat" 0))
                              None
                              (mkPiS (1, nAnon)
                                 (mkConstInd (mkInd "Coq.Init.Datatypes.nat" 0)) None
                                 (mkPiS (2, nAnon)
                                    (oterm (CApply 2)
                                       [bterm [] (mkConst "Coq_Init_Datatypes_nat_RR0");
                                       bterm [] (vterm (0, nAnon));
                                       bterm [] (vterm (1, nAnon))]) None
                                    (oterm (CApply 2)
                                       [bterm []
                                          (oterm (CApply 3)
                                             [bterm []
                                                (mkLamS (0, nAnon)
                                                   (mkConstInd
                                                      (mkInd "Coq.Init.Datatypes.nat" 0))
                                                   None
                                                   (mkLamS (1, nAnon)
                                                      (mkConstInd
                                                         (mkInd "Coq.Init.Datatypes.nat" 0))
                                                      None
                                                      (mkLamS (2, nAnon)
                                                         (oterm 
                                                            (CApply 2)
                                                            [bterm []
                                                               (mkConst
                                                               "Coq_Init_Datatypes_nat_RR0");
                                                            bterm [] (vterm (0, nAnon));
                                                            bterm [] (vterm (1, nAnon))])
                                                         None
                                                         (mkLamS 
                                                            (0, nAnon) 
                                                            (mkSort sSet) None
                                                            (mkLamS 
                                                               (3, nAnon) 
                                                               (mkSort sSet) None
                                                               (mkPiS 
                                                               (6, nAnon) 
                                                               (vterm (0, nAnon)) None
                                                               (mkPiS 
                                                               (9, nAnon) 
                                                               (vterm (3, nAnon)) None
                                                               (mkSort sProp) None) None))))));
                                             bterm [] (vterm (0, nAnon));
                                             bterm [] (vterm (1, nAnon));
                                             bterm [] (vterm (2, nAnon))]);
                                       bterm []
                                         (oterm (CApply 1)
                                            [bterm [] (vterm (30, nNamed "ff"));
                                            bterm [] (vterm (0, nAnon))]);
                                       bterm []
                                         (oterm (CApply 1)
                                            [bterm [] (vterm (31, nNamed "ff₂"));
                                            bterm [] (vterm (1, nAnon))])]) None) None) None)));
                  bterm [] (vterm (0, nNamed "T")); bterm [] (vterm (1, nNamed "T₂"))]) None
               (mkLamS (3, nNamed "x") (mkConstInd (mkInd "Coq.Init.Datatypes.nat" 0)) None
                  (mkLamS (4, nNamed "x₂") (mkConstInd (mkInd "Coq.Init.Datatypes.nat" 0))
                     None
                     (mkLamS (5, nNamed "x_R")
                        (oterm (CApply 2)
                           [bterm [] (mkConst "Coq_Init_Datatypes_nat_RR0");
                           bterm [] (vterm (3, nNamed "x"));
                           bterm [] (vterm (4, nNamed "x₂"))]) None
                        (mkLamS (3, nNamed "x")
                           (oterm (CApply 1)
                              [bterm [] (vterm (0, nNamed "T"));
                              bterm [] (vterm (3, nNamed "x"))]) None
                           (mkLamS (4, nNamed "x₂")
                              (oterm (CApply 1)
                                 [bterm [] (vterm (1, nNamed "T₂"));
                                 bterm [] (vterm (4, nNamed "x₂"))]) None
                              (mkLamS (5, nNamed "x_R")
                                 (oterm (CApply 2)
                                    [bterm []
                                       (oterm (CApply 3)
                                          [bterm [] (vterm (2, nNamed "T_R"));
                                          bterm [] (vterm (3, nNamed "x"));
                                          bterm [] (vterm (4, nNamed "x₂")); (* capture *)
                                          bterm [] (vterm (5, nNamed "x_R"))]);
                                    bterm [] (vterm (3, nNamed "x"));
                                    bterm [] (vterm (4, nNamed "x₂"))]) None
                                 (vterm (5, nNamed "x_R")))))))))).


Local Transparent vprime vrel ssubst_aux ssubst_bterm_aux N.add transLam.
Run TemplateProgram (genParam false true "capture").
Print capture_RR.
Run TemplateProgram (tmMkDefinitionSq "captureFromSyn" captureSyntax).
Run TemplateProgram (tmMkDefinitionSq "captureTranslate" captureTranslateSyntax).
(*
In environment
T : nat -> Set
T₂ : nat -> Set
T_R : forall H H0 : nat, Coq_Init_Datatypes_nat_RR0 H H0 -> T H -> T₂ H0 -> Prop
x : nat
x₂ : nat
x_R : Coq_Init_Datatypes_nat_RR0 x x₂
x0 : T x
x₂0 : T₂ x₂
The term "x0" has type "T x" while it is expected to have type "nat".
*)







