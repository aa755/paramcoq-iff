(*
abhishek@brixpro:~/parametricity/reflective-paramcoq/test-suite$ ./coqid.sh indFunArg
*)

Require Import SquiggleEq.terms.


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

Require Import ReflParam.PIWNew.

Require Import Template.Template.

Require Import ReflParam.matchR. (* shadows Coq.Init.Datatypes.list *)
Require Import List.
Run TemplateProgram (mkIndEnv "indTransEnv" ["ReflParam.matchR.Vec"]).

Check vcons.
Require Import Top.nat.

Open Scope N_scope.
(* Arguments existT {A} {P} x p. *)

(*
Arguments existT : clear implicits.

Arguments eq_refl : clear implicits.
*)

(*
fix
ReflParam_matchR_Vec_RR0 (C C₂ : Set) (C_R : C -> C₂ -> Prop) (m m₂ : nat)
                         (m_R : nat_RR m m₂) (H : Vec C m) (H0 : Vec C₂ m₂) {struct H} :
  Prop :=
  match H in (Vec _ m0) return (nat_RR m0 m₂ -> Prop) with
  | vnil _ =>
      match H0 in (Vec _ m₂0) return (nat_RR 0 m₂0 -> Prop) with
      | vnil _ =>
          fun m_R0 : nat_RR 0 0 =>
          existT (nat_RR 0 0) (fun _ : nat_RR 0 0 => True) m_R0 I =
          existT (nat_RR 0 0) (fun _ : nat_RR 0 0 => True) O_RR I
      | vcons _ n₂ _ _ => fun _ : nat_RR 0 (S n₂) => False
      end
  | vcons _ n c vc =>
      match H0 in (Vec _ m₂0) return (nat_RR (S n) m₂0 -> Prop) with
      | vnil _ => fun _ : nat_RR (S n) 0 => False
      | vcons _ n₂ c₂ vc₂ =>
          fun m_R0 : nat_RR (S n) (S n₂) =>
          {n_R : nat_RR n n₂ &
          {_ : C_R c c₂ &
          {_ : ReflParam_matchR_Vec_RR0 C C₂ C_R n n₂ n_R vc vc₂ &
          existT (nat_RR (S n) (S n₂)) (fun _ : nat_RR (S n) (S n₂) => True) m_R0 I =
          existT (nat_RR (S n) (S n₂)) (fun _ : nat_RR (S n) (S n₂) => True) 
            (S_RR n n₂ n_R) I}}}
      end
  end m_R

ReflParam_matchR_Vec_RR0 is defined

*)
Run TemplateProgram (genParamInd [] false true true "ReflParam.matchR.Vec").

Notation Vec_RR := ReflParam_matchR_Vec_RR0.

Definition vcons_RR  : forall (C₁ C₂ : Set) (C_R : C₁ -> C₂ -> Prop) (n₁ n₂ : nat) (n_R : nat_RR n₁ n₂)
  (H : C₁) (H0 : C₂) (c_R : C_R H H0) (H1 : Vec C₁ n₁) (H2 : Vec C₂ n₂)
  (v_R : Vec_RR C₁ C₂ C_R n₁ n₂ n_R H1 H2),
  Vec_RR C₁ C₂ C_R (S n₁) (S n₂) (S_RR n₁ n₂ n_R) 
         (vcons C₁ n₁ H H1) (vcons C₂ n₂ H0 H2).
Proof.
  intros.
    simpl.

  exists n_R. exists c_R. exists v_R. reflexivity.
Defined.

Definition vcons_RRAutoGenFixed :=
(fun (C C₂ : Set) (C_R : C -> C₂ -> Prop) (n n₂ : nat) 
   (n_R : nat_RR n n₂) (c : C) (c₂ : C₂) (c_R : C_R c c₂) 
   (vc : Vec C n) (vc₂ : Vec C₂ n₂)
   (vc_R : ReflParam_matchR_Vec_RR0 C C₂ C_R n n₂ n_R vc vc₂) =>
 existT (nat_RR n n₂)
   (fun n_R0 : nat_RR n n₂ =>
    {_ : C_R c c₂ &
    {vc_R0 : ReflParam_matchR_Vec_RR0 C C₂ C_R n n₂ n_R0 vc vc₂ &
    existT (nat_RR (S n) (S n₂)) (fun _ : nat_RR (S n) (S n₂) => True) vc_R0
      I =
    existT (nat_RR (S n) (S n₂)) (fun _ : nat_RR (S n) (S n₂) => True)
      (S_RR n n₂ n_R0) I}}) n_R
   (existT (C_R c c₂)
      (fun _ : C_R c c₂ =>
       {vc_R0 : ReflParam_matchR_Vec_RR0 C C₂ C_R n n₂ n_R vc vc₂ &
       existT (nat_RR (S n) (S n₂)) (fun _ : nat_RR (S n) (S n₂) => True)
         vc_R0 I =
       existT (nat_RR (S n) (S n₂)) (fun _ : nat_RR (S n) (S n₂) => True)
         (S_RR n n₂ n_R) I}) c_R
      (existT (ReflParam_matchR_Vec_RR0 C C₂ C_R n n₂ n_R vc vc₂)
         (fun vc_R0 : ReflParam_matchR_Vec_RR0 C C₂ C_R n n₂ n_R vc vc₂ =>
          existT (nat_RR (S n) (S n₂)) (fun _ : nat_RR (S n) (S n₂) => True)
            vc_R0 I =
          existT (nat_RR (S n) (S n₂)) (fun _ : nat_RR (S n) (S n₂) => True)
            (S_RR n n₂ n_R) I) vc_R
         (eq_refl {_ : nat_RR (S n) (S n₂) & True}
            (existT (nat_RR (S n) (S n₂))
               (fun _ : nat_RR (S n) (S n₂) => True) 
               (S_RR n n₂ n_R) I))))).
(*
Arguments existT {A} {P} x p.
(fun (C C₂ : Set) (C_R : C -> C₂ -> Prop) (n n₂ : nat) 
   (n_R : nat_RR n n₂) (H : C) (H0 : C₂) (H1 : C_R H H0) 
   (H2 : Vec C n) (H3 : Vec C₂ n₂)
   (H4 : ReflParam_matchR_Vec_RR0 C C₂ C_R n n₂ n_R H2 H3) =>
 existT n_R
   (existT H1
      (existT H4
         (eq_refl {_ : nat_RR (S n) (S n₂) & True} (existT (S_RR n n₂ n_R) I))))).

*)

SearchAbout Vec.
(* Print ReflParam_matchR_Vec_RR0_paramConstr_1_paramInv. *)
(*
ReflParam_matchR_Vec_RR0_paramConstr_1_paramInv = 
fun (C C₂ : Set) (C_R : C -> C₂ -> Prop) (n n₂ : nat) (H : C) 
  (H0 : C₂) (H1 : Vec C n) (H2 : Vec C₂ n₂)
  (sigt : {n_R : nat_RR n n₂ &
          {_ : C_R H H0 &
          {_ : ReflParam_matchR_Vec_RR0 C C₂ C_R n n₂ n_R H1 H2 & True}}})
  (retTyp : Set)
  (rett : forall n_R : nat_RR n n₂,
          C_R H H0 -> ReflParam_matchR_Vec_RR0 C C₂ C_R n n₂ n_R H1 H2 -> retTyp) =>
let n_R := projT1 sigt in
let H3 := projT1 (projT2 sigt) in
let H4 := projT1 (projT2 (projT2 sigt)) in rett n_R H3 H4

     : forall (C C₂ : Set) (C_R : C -> C₂ -> Prop) (n n₂ : nat) 
         (H : C) (H0 : C₂) (H1 : Vec C n) (H2 : Vec C₂ n₂),
       {n_R : nat_RR n n₂ &
       {_ : C_R H H0 & {_ : ReflParam_matchR_Vec_RR0 C C₂ C_R n n₂ n_R H1 H2 & True}}} ->
       forall retTyp : Set,
       (forall n_R : nat_RR n n₂,
        C_R H H0 -> ReflParam_matchR_Vec_RR0 C C₂ C_R n n₂ n_R H1 H2 -> retTyp) ->
       retTyp

*)

(*
vcons_RR = 
fun (C C₂ : Set) (C_R : C -> C₂ -> Prop) (n n₂ : nat)
  (n_R : Coq_Init_Datatypes_nat_RR0 n n₂) (H : C) (H0 : C₂) (H1 : C_R H H0) 
  (H2 : Vec C n) (H3 : Vec C₂ n₂) (H4 : ReflParam_matchR_Vec_RR0 C C₂ C_R n n₂ n_R H2 H3) =>
existT n_R (existT H1 (existT H4 I))
*)
 

(* Notation Vec_RR := ReflParam_matchR_Vec_RR0. *)
(* Notation vcons_RR := ReflParam_matchR_Vec_RR0_paramConstr_1. *)

(*Definition vcons_RR {C₁ C₂ : Set} {C_R : C₁ -> C₂ -> Prop}
(n₁ n₂ : nat) (n_R : nat_RR n₁ n₂)
 (H : C₁) (H0 : C₂) (c_R: C_R H H0)
 (H1 : Vec C₁ n₁) (H2 : Vec C₂ n₂)
 (v_R : Vec_RR C₁ C₂ C_R n₁ n₂ n_R H1 H2):
  Vec_RR C₁ C₂ C_R (S n₁) (S n₂) (S_RR n₁ n₂ n_R)
  (vcons C₁ n₁ H H1) (vcons C₂ n₂ H0 H2) :=
  existT
  (fun n_R0 : nat_RR n₁ n₂ =>
   {_ : C_R H H0 & {_ : Vec_RR C₁ C₂ C_R n₁ n₂ n_R0 H1 H2 & True}}) n_R
  (existT (fun _ : C_R H H0 => {_ : Vec_RR C₁ C₂ C_R n₁ n₂ n_R H1 H2 & True}) c_R
     (existT (fun _ : Vec_RR C₁ C₂ C_R n₁ n₂ n_R H1 H2 => True) v_R I)).
*)
(*
Proof.
simpl. eexists; eexists; eauto.
Defined.
*)

Require Import SquiggleEq.UsefulTypes.
Fixpoint ReflParam_matchR_vAppend_RR (C₁ C₂ : Set) (C_R : C₁ -> C₂ -> Prop) (n₁ n₂ : nat) 
   (n_R : nat_RR n₁ n₂) (m₁ m₂ : nat) (m_R : nat_RR m₁ m₂)
   (vl₁ : Vec C₁ n₁) (vl₂ : Vec C₂ n₂)
   (vl_R : Vec_RR C₁ C₂ C_R n₁ n₂ n_R vl₁ vl₂)
   (vr₁ : Vec C₁ m₁) (vr₂ : Vec C₂ m₂)
   (vr_R : Vec_RR C₁ C₂ C_R m₁ m₂ m_R vr₁ vr₂) {struct vl₁ }:
    Vec_RR C₁ C₂ C_R (n₁ + m₁) (n₂ + m₂) (add_RR n₁ n₂ n_R m₁ m₂ m_R)
         (vAppend vl₁ vr₁) (vAppend vl₂ vr₂).
refine (
let reT := fun n₁ vl₁ n₂ vl₂ => 
forall n_R: nat_RR n₁ n₂,
Vec_RR C₁ C₂ C_R n₁ n₂ n_R vl₁ vl₂
-> 
Vec_RR C₁ C₂ C_R (n₁ + m₁) (n₂ + m₂) (add_RR n₁ n₂ n_R m₁ m₂ m_R)
         (vAppend vl₁ vr₁) (vAppend vl₂ vr₂)  in 
(match vl₁ in Vec _ n₁ return reT n₁ vl₁ n₂ vl₂ with
| vnil _ =>  
  match vl₂ in (Vec _ n₂) return reT 0 (vnil _) n₂ vl₂ with
  | vnil _ => fun _ _ => vr_R
  | vcons _ _ _ _ => fun _ v_R => False_rect _ v_R
  end

| vcons _ n₁ hl₁ tl₁ => 
  match vl₂ in (Vec _ n₂) return reT (S n₁) (vcons _ n₁ hl₁ tl₁) n₂ vl₂ with
  | vnil _ =>  fun _ v_R => False_rect _ v_R
  | vcons _ _ hl₂ tl₂ => fun _ v_R =>
    let n_R := projT2 v_R in
    let v_R := projT2 v_R in
    let hl_R := projT1 v_R in
    let tl_R := projT1 (projT2 v_R) in
    let peq := projT2 (projT2 v_R) in
    let old := (vcons_RR _ _ C_R _ _ _ _ _ hl_R _ _ 
     (ReflParam_matchR_vAppend_RR _ _ _ _ _ _ _ _ _ _ _ tl_R  _ _ vr_R))
    in _
  end
end) n_R vl_R).
simpl vAppend. simpl add_RR.
rewrite peq. exact old.
Defined.

Definition Vec_rect_type :=
forall (C : Set) (P : forall n : nat, Vec C n -> Set),
       P 0 (vnil C) ->
       (forall (n : nat) (c : C) (v : Vec C n), P n v -> P (S n) (vcons C n c v)) ->
       forall (n : nat) (v : Vec C n), P n v.


Require Import SquiggleEq.tactics.

Notation vAppend_RR := ReflParam_matchR_vAppend_RR.

Print sigT_rect.

Print ReflParam_matchR_Vec_RR0.

Definition vAppend2_RR3 (C₁ C₂ : Set) (C_R : C₁ -> C₂ -> Prop) (m₁ m₂ : nat) 
  (m_R : nat_RR m₁ m₂)
  (cdef₁ : C₁) (cdef₂ : C₂) (cdef_R : C_R cdef₁ cdef₂)
  (vr₁ : Vec C₁ m₁) (vr₂ : Vec C₂ m₂) (vr : Vec_RR C₁ C₂ C_R m₁ m₂ m_R vr₁ vr₂):
  C_R (vAppend2  cdef₁ vr₁) (vAppend2 cdef₂ vr₂) :=
(
let reT n1 n2 v1 v2 (* indices and values. move the _Rs to the body, as Pi args  *) :=
      forall (nr: nat_RR n1 n2)
        (vapr: Vec_RR C₁ C₂ C_R n1 n2 nr v1 v2),
     C_R match v1 with
      | vnil _ => cdef₁
      | vcons _ _ hl _ => hl
      end match v2 with
          | vnil _ => cdef₂
          | vcons _ _ hl _ => hl
          end in

(* the "as vap1" part cannot be inlined.
"vAppend vr₁ vr₁" has type "Vec C₁ (m₁ + m₁)" while vap1 has type "Vec C₁ n1"
*)
match vAppend vr₁ vr₁ as vap1 in Vec _ n1
  return reT n1 (m₂+m₂)(*prime of index of discriminee *) 
      vap1 (vAppend vr₂ vr₂) (* prime of discriminee*)
with
| vnil _ => 
    match vAppend vr₂ vr₂ as vap2 in Vec _ n2
      return reT O (*index of this constr:vnil*) n2 (* from in *)
          (vnil _) vap2
      with  
      | vnil _ => fun (nr : nat_RR 0 0) (_ : Vec_RR C₁ C₂ C_R 0 0 nr (vnil C₁) (vnil C₂))  => cdef_R
      | vcons _ n2 hl2 v2 =>
        fun (nr : nat_RR 0 (S n2))
          (vr0 : Vec_RR C₁ C₂ C_R 0 (S n2) nr (vnil C₁) (vcons C₂ n2 hl2 v2))
        => False_rect
            (*reT 0 (S n2) (vnil C₁) (vcons C₂ n2 hl2 v2) nr vr0 -- then strip the 2 pis*)
            _ vr0 (* always the last lambda *)
      end
| vcons _ n1 hl tl =>
    match vAppend vr₂ vr₂ as vap2 in Vec _ n2
      return reT (S n1) (*index of this constr*) n2 (* from in *)
          (vcons _ _ hl tl) vap2
      with  
      | vnil _ => fun _ vr => False_rect _ vr
      | vcons _ _ hl _ => fun _ v_R =>
    let v_R := projT2 v_R in
    let hl_R := projT1 v_R in
    let tl_R := projT1 (projT2 v_R)
        in hl_R
      end

end (add_RR m₁ m₂ m_R m₁ m₂ m_R) 
  (vAppend_RR _ _ _ _ _ _ _ _ vr _ _ vr)
).
Check indTransEnv.
Run TemplateProgram (genParam indTransEnv false true "vAppend2"). (* success!*)
Print vAppend2_RR.

(*
vAppend2_RR = 
fun (C C₂ : Set) (C_R : C -> C₂ -> Prop) (m m₂ : nat) (m_R : nat_RR m m₂) 
  (cdef : C) (cdef₂ : C₂) (cdef_R : C_R cdef cdef₂) (vr : Vec C m) 
  (vr₂ : Vec C₂ m₂) (vr_R : Vec_RR C C₂ C_R m m₂ m_R vr vr₂) =>
match
  vAppend vr vr as vapx in (Vec _ n)
  return
    (forall n_R : nat_RR n (m₂ + m₂),
     Vec_RR C C₂ C_R n (m₂ + m₂) n_R vapx (vAppend vr₂ vr₂) ->
     C_R match vapx with
         | vnil _ => cdef
         | vcons _ _ hl _ => hl
         end match vAppend vr₂ vr₂ with
             | vnil _ => cdef₂
             | vcons _ _ hl₂ _ => hl₂
             end)
with
| vnil _ =>
    match
      vAppend vr₂ vr₂ as vapx₂ in (Vec _ n₂)
      return
        (forall n_R : nat_RR 0 n₂,
         Vec_RR C C₂ C_R 0 n₂ n_R (vnil C) vapx₂ ->
         C_R cdef match vapx₂ with
                  | vnil _ => cdef₂
                  | vcons _ _ hl₂ _ => hl₂
                  end)
    with
    | vnil _ =>
        fun (n_R : nat_RR 0 0) (vapx_R : Vec_RR C C₂ C_R 0 0 n_R (vnil C) (vnil C₂)) =>
        ReflParam_matchR_Vec_RR0_paramConstr_0_paramInv C C₂ C_R vapx_R
          (C_R match vnil C with
               | vnil _ => cdef
               | vcons _ _ hl _ => hl
               end match vnil C₂ with
                   | vnil _ => cdef₂
                   | vcons _ _ hl₂ _ => hl₂
                   end) cdef_R
    | vcons _ n'₂ hl₂ tl₂ =>
        fun (n_R : nat_RR 0 (S n'₂))
          (vapx_R : Vec_RR C C₂ C_R 0 (S n'₂) n_R (vnil C) (vcons C₂ n'₂ hl₂ tl₂)) =>
        False_rectt
          (C_R match vnil C with
               | vnil _ => cdef
               | vcons _ _ hl _ => hl
               end
             match vcons C₂ n'₂ hl₂ tl₂ with
             | vnil _ => cdef₂
             | vcons _ _ hl₂0 _ => hl₂0
             end) vapx_R
    end
| vcons _ n' hl tl =>
    match
      vAppend vr₂ vr₂ as vapx₂ in (Vec _ n₂)
      return
        (forall n_R : nat_RR (S n') n₂,
         Vec_RR C C₂ C_R (S n') n₂ n_R (vcons C n' hl tl) vapx₂ ->
         C_R hl match vapx₂ with
                | vnil _ => cdef₂
                | vcons _ _ hl₂ _ => hl₂
                end)
    with
    | vnil _ =>
        fun (n_R : nat_RR (S n') 0)
          (vapx_R : Vec_RR C C₂ C_R (S n') 0 n_R (vcons C n' hl tl) (vnil C₂)) =>
        False_rectt
          (C_R match vcons C n' hl tl with
               | vnil _ => cdef
               | vcons _ _ hl0 _ => hl0
               end match vnil C₂ with
                   | vnil _ => cdef₂
                   | vcons _ _ hl₂ _ => hl₂
                   end) vapx_R
    | vcons _ n'₂ hl₂ tl₂ =>
        fun (n_R : nat_RR (S n') (S n'₂))
          (vapx_R : Vec_RR C C₂ C_R (S n') (S n'₂) n_R (vcons C n' hl tl)
                      (vcons C₂ n'₂ hl₂ tl₂)) =>
        ReflParam_matchR_Vec_RR0_paramConstr_1_paramInv C C₂ C_R n' n'₂ hl hl₂ tl tl₂ vapx_R
          (C_R match vcons C n' hl tl with
               | vnil _ => cdef
               | vcons _ _ hl0 _ => hl0
               end
             match vcons C₂ n'₂ hl₂ tl₂ with
             | vnil _ => cdef₂
             | vcons _ _ hl₂0 _ => hl₂0
             end)
          (fun (n'_R : nat_RR n' n'₂) (hl_R : C_R hl hl₂)
             (_ : Vec_RR C C₂ C_R n' n'₂ n'_R tl tl₂) => hl_R)
    end
end (add_RR m m₂ m_R m m₂ m_R) (vAppend_RR m m₂ m_R m m₂ m_R vr vr₂ vr_R vr vr₂ vr_R)
     : forall (C C₂ : Set) (C_R : C -> C₂ -> Prop) (m m₂ : nat) 
         (m_R : nat_RR m m₂) (cdef : C) (cdef₂ : C₂),
       C_R cdef cdef₂ ->
       forall (vr : Vec C m) (vr₂ : Vec C₂ m₂),
       Vec_RR C C₂ C_R m m₂ m_R vr vr₂ ->
       C_R match vAppend vr vr with
           | vnil _ => cdef
           | vcons _ _ hl _ => hl
           end match vAppend vr₂ vr₂ with
               | vnil _ => cdef₂
               | vcons _ _ hl₂ _ => hl₂
               end
*)

