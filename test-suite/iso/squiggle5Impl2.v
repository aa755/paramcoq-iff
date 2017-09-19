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
Require Import squiggle5.
Open Scope string_scope.
Require Import Coq.btauto.Btauto.
Require Import SquiggleEq.LibTactics.

Lemma nat_R_Refl (n:nat):
  Coq_Init_Datatypes_nat_pmtcty_RR0 n n.
Proof using.
  induction n; simpl;[constructor|].
  exists IHn. constructor.
Defined.

Require Import ReflParam.Trecord.
Require Import SquiggleEq.terms2.
Require Import SquiggleEq.varImplZ.
Require Import SquiggleEq.wftermSet.


Inductive Opid : Set :=
| lam
| app
| num (n:nat).

Definition V := BinNums.positive.
(** using a library that generically defines substitution and alpha equality: https://github.com/aa755/SquiggleEq *)
Definition Tm : Set := @NTerm V Opid (* for unextracted efficiency, not carrying the proof of well formedness. e.g. [oterm lam []] is allowed *).
Definition BTm : Set := (V*Tm).

Definition elimTerm (t:Tm) :  TmKind Tm BTm :=
match t with
| vterm _ => evar
| oterm o lbt=>
  match o, lbt with
  | lam, [(bterm [v] t)] => elam (v,t)
  | app, [bterm [] f; bterm [] a] => eapp f a
  | num n, [] => enum n
  | _,_ => evar 
  (* ill-formed term. from the point of view of evaluation 
    (only closed terms) and observational equivalence, 
      there is no difference between variables and garbage terms.*)
  end
end.

Definition applyBtm (b:BTm) (u:Tm) :  Tm:=
  let (v,t) := b in (subst t v u).

Require Import SquiggleEq.alphaeq.

Module alphaInst.

Definition Tm_R (t1 t2 :Tm) : Prop:= alpha_eq t1 t2.

Definition BTm_R (bt1 bt2 :BTm) : Prop:=
  let (v1, t1) := bt1 in
  let (v2, t2) := bt2 in
  alpha_eq_bterm (bterm [v1] t1) (bterm [v2] t2).


Lemma totalTm_R : TotalHeteroRel Tm_R.
  split;  intros x; exists x; apply alpha_eq_refl.
Defined.

(** The strong isorel translation reduces away this requirement 
Lemma totalBTm_R : TotalHeteroRel BTm_R.
  split;  intros x; exists x; destruct x; apply alphaeqbt_refl.
Defined.
*)

Require Import SquiggleEq.list.

(** show that the the interface operations respect the relation *)

(** on alpha equal terms, elimTerm returns related answers *)
Lemma elimTerm_R :
   (forall (a1 : Tm) (a2 : Tm),
        Tm_R a1 a2 ->
        Top_squiggle5_TmKind_pmtcty_RR0 Tm Tm Tm_R BTm BTm BTm_R (elimTerm a1) (elimTerm a2)).
Proof using.
  intros ? ? Hr.
  hnf in Hr.
  inverts Hr.
  - constructor. 
  - rename H into Hlen. rename H0 into Hb.
    destruct op; simpl.
    + destruct lbt1 as [| b lbt1]; simpl in *; 
        dlist_len_name lbt2 b2;[constructor|].
      destruct b as [lv nt].
      alphahypsd2.
      destruct b2 as [lv2 nt2].
      pose proof Hb0bt as Hblen.
      apply alpha_eq_bterm_lenbvars in Hblen.
      destruct lv as [| v lv]; simpl in *;
        dlist_len_name lv2 v2;[ constructor |].
      destruct lv as [|]; simpl in *;
        dlist_len_name lv2 vv;[ | constructor].
      destruct lbt1 as [|]; simpl in *; 
        dlist_len_name lbt2 b2;[constructor|]; auto; try constructor.

    + destruct lbt1 as [| b lbt1]; simpl in *; 
        dlist_len_name lbt2 b2;[constructor|].
      destruct b as [lv nt].
      alphahypsd2.
      destruct b2 as [lv2 nt2].
      pose proof Hb0bt as Hblen.
      apply alpha_eq_bterm_lenbvars in Hblen.
      destruct lv as [|]; simpl in *;
        dlist_len_name lv2 vv;[ | constructor].
      destruct lbt1 as [| al lbt1]; simpl in *; 
        dlist_len_name lbt2 ar;[constructor|]; auto; try constructor.
      destruct al as [alvl al].
      destruct ar as [arvl ar].
      unfold tactics.ltac_something in Hb.
      alphahypsd3.
      alphahypsd2.
      alphahypsd3.
      pose proof Hb1bt as Hblen.
      apply alpha_eq_bterm_lenbvars in Hblen.
      destruct alvl as [|]; simpl in *;
        dlist_len_name arvl vv;[ | constructor].
      alphahypsd3.
      destruct lbt1 as [|]; simpl in *; 
        dlist_len_name lbt2 ar;[constructor|]; auto; try constructor; auto; constructor.
    + destruct lbt1 as [|]; simpl in *;
      dlist_len_name lbt2 ar;[constructor|];
         auto; try constructor; auto; try constructor.
      exact (nat_R_Refl n).
Qed.

Lemma applyBTerm_R :
(forall (a1 : BTm) (a2 : BTm),
        BTm_R a1 a2 ->
        forall (a3 : Tm) (a4 : Tm), Tm_R a3 a4 -> Tm_R (applyBtm a1 a3) (applyBtm a2 a4)).
Proof using.
  intros.
  destruct a1 as [? sl].
  destruct a2 as [? sr].
  unfold Tm_R in *.
  simpl in *.
  apply apply_bterm_alpha_congr  with (lnt1 := [a3]) (lnt2 := [a4]) in H; auto.
  prove_bin_rel_nterm.
Qed.

(** Above, we showed that all operations in the interface respect the relation alpha
equality. Now, we are ready to get the free theorem *)

Require Import ReflParam.Trecord.

Require Import squiggle5StrongIso.

Lemma obsEqRespectsAlpha :
forall tl tl₂ : Tm,
Tm_R tl tl₂ ->
forall tr tr₂ : Tm,
Tm_R tr tr₂ ->
obseq Tm BTm applyBtm elimTerm tl tr <->
obseq Tm BTm applyBtm elimTerm tl₂ tr₂.
Proof using.
 intros.
 apply IsoRel_implies_iff.
 apply (obseqStrongIso _ _ Tm_R totalTm_R _ _ BTm_R _ _ applyBTerm_R _ _ elimTerm_R);
   assumption.
Qed.

End alphaInst.
