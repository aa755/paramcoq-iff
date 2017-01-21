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

Inductive Vec (C : Set) : nat -> Set :=
    vnil : Vec C 0 | vcons : forall n : nat, C -> Vec C n -> Vec C (n+1).

Run TemplateProgram (mkIndEnv "indTransEnv" ["Top.vecSRevAuto.Vec"]).
    
Require Import Top.nat.

Definition one_RR : nat_RR 1 1.
apply S_RR. apply O_RR.
Defined.

Run TemplateProgram (genParamInd [] false true true "Top.vecSRevAuto.Vec").

(*
(fix
 Top_vecSRevAuto_Vec_RR0 (C C₂ : Set) (C_R : C -> C₂ -> Prop) (H H0 : nat)
                         (H1 : nat_RR H H0) (H2 : Vec C H) (H3 : Vec C₂ H0) {struct H2} :
   Prop :=
   match H2 in (Vec _ H4) return (nat_RR H4 H0 -> Prop) with
   | vnil _ =>
       match H3 in (Vec _ H4) return (nat_RR 0 H4 -> Prop) with
       | vnil _ =>
           fun H4 : nat_RR 0 0 =>
           existT (nat_RR 0 0) (fun _ : nat_RR 0 0 => True) H4 I =
           existT (nat_RR 0 0) (fun _ : nat_RR 0 0 => True) O_RR I
       | vcons _ n₂ _ _ => fun _ : nat_RR 0 (n₂ + 1) => False
       end
   | vcons _ n x x0 =>
       match H3 in (Vec _ H4) return (nat_RR (n + 1) H4 -> Prop) with
       | vnil _ => fun _ : nat_RR (n + 1) 0 => False
       | vcons _ n₂ x1 x2 =>
           fun H4 : nat_RR (n + 1) (n₂ + 1) =>
           {n_R : nat_RR n n₂ &
           {_ : C_R x x1 &
           {_ : Top_vecSRevAuto_Vec_RR0 C C₂ C_R n n₂ n_R x0 x2 &
           existT (nat_RR (n + 1) (n₂ + 1)) (fun _ : nat_RR (n + 1) (n₂ + 1) => True) H4 I =
           existT (nat_RR (n + 1) (n₂ + 1)) (fun _ : nat_RR (n + 1) (n₂ + 1) => True)
             (add_RR n n₂ n_R 1 1 (S_RR 0 0 O_RR)) I}}}
       end
   end H1)
Top_vecSRevAuto_Vec_RR0 is defined
(fun (C C₂ : Set) (C_R : C -> C₂ -> Prop) (n n₂ : nat) (n_R : nat_RR n n₂) 
   (H : C) (H0 : C₂) (H1 : C_R H H0) (H2 : Vec C n) (H3 : Vec C₂ n₂)
   (H4 : Top_vecSRevAuto_Vec_RR0 C C₂ C_R n n₂ n_R H2 H3) =>
 existT (nat_RR n n₂)
   (fun n_R0 : nat_RR n n₂ =>
    {_ : C_R H H0 &
    {_ : Top_vecSRevAuto_Vec_RR0 C C₂ C_R n n₂ n_R0 H2 H3 &
    existT (nat_RR (n + 1) (n₂ + 1)) (fun _ : nat_RR (n + 1) (n₂ + 1) => True)
      (add_RR n n₂ n_R 1 1 (S_RR 0 0 O_RR)) I =
    existT (nat_RR (n + 1) (n₂ + 1)) (fun _ : nat_RR (n + 1) (n₂ + 1) => True)
      (add_RR n n₂ n_R0 1 1 (S_RR 0 0 O_RR)) I}}) n_R
   (existT (C_R H H0)
      (fun _ : C_R H H0 =>
       {_ : Top_vecSRevAuto_Vec_RR0 C C₂ C_R n n₂ n_R H2 H3 &
       existT (nat_RR (n + 1) (n₂ + 1)) (fun _ : nat_RR (n + 1) (n₂ + 1) => True)
         (add_RR n n₂ n_R 1 1 (S_RR 0 0 O_RR)) I =
       existT (nat_RR (n + 1) (n₂ + 1)) (fun _ : nat_RR (n + 1) (n₂ + 1) => True)
         (add_RR n n₂ n_R 1 1 (S_RR 0 0 O_RR)) I}) H1
      (existT (Top_vecSRevAuto_Vec_RR0 C C₂ C_R n n₂ n_R H2 H3)
         (fun _ : Top_vecSRevAuto_Vec_RR0 C C₂ C_R n n₂ n_R H2 H3 =>
          existT (nat_RR (n + 1) (n₂ + 1)) (fun _ : nat_RR (n + 1) (n₂ + 1) => True)
            (add_RR n n₂ n_R 1 1 (S_RR 0 0 O_RR)) I =
          existT (nat_RR (n + 1) (n₂ + 1)) (fun _ : nat_RR (n + 1) (n₂ + 1) => True)
            (add_RR n n₂ n_R 1 1 (S_RR 0 0 O_RR)) I) H4
         (eq_refl {_ : nat_RR (n + 1) (n₂ + 1) & True}
            (existT (nat_RR (n + 1) (n₂ + 1)) (fun _ : nat_RR (n + 1) (n₂ + 1) => True)
               (add_RR n n₂ n_R 1 1 (S_RR 0 0 O_RR)) I)))))
Top_vecSRevAuto_Vec_RR0_paramConstr_1 is defined
(fun (C C₂ : Set) (_ : C -> C₂ -> Prop) =>
 eq_refl {_ : nat_RR 0 0 & True} (existT (nat_RR 0 0) (fun _ : nat_RR 0 0 => True) O_RR I))
Top_vecSRevAuto_Vec_RR0_paramConstr_0 is defined

*)
Notation Vec_RR := Top_vecSRevAuto_Vec_RR0.
Notation vcons_RR := Top_vecSRevAuto_Vec_RR0_paramConstr_1.
Notation vnil_RR := Top_vecSRevAuto_Vec_RR0_paramConstr_0.


Declare ML Module "paramcoq".
Parametricity Recursive Vec_rect.

Require Import SquiggleEq.tactics.

Require Import SquiggleEq.UsefulTypes.

Lemma eta_sigt {A : Type} {P : A -> Type} (x: sigT P):
x = existT _ _ (projT1 x) (projT2 x).
Proof using.
  intros. destruct x. simpl. refl.
Defined.

Lemma eta_sigtI {A : Type} (x: sigT (fun _:A=> True)):
x = existT _ _ (projT1 x) I.
Proof using.
  intros. destruct x. simpl. destruct t. refl.
Defined.


Lemma eq_rect_sigt2 (A : Type)  :
let T := sigT (fun _:A => True) in
forall (x : T) (P : forall (a:A), eq x (existT _ _ a I) -> Type),
       P (projT1 x) (eta_sigtI x) -> forall (a:A) (e : eq x (existT _ _ a I)), 
        P a e.
Proof.
  intros. subst. exact X.
Defined.


Definition vcons_RRInv
 (C C₂ : Set) (C_R : C -> C₂ -> Prop) (n n₂ : nat) 
 (c₁ : C) (c₂ : C₂) 
   (v₁ : Vec C n) (v₂ : Vec C₂ n₂)
   (nro : nat_RR (n + 1) (n₂ + 1)) (* add outer indices_RR in order. in match, need to apply this *)  
   (sigt : Vec_RR C C₂ C_R (n + 1) (n₂ + 1) nro (vcons C n c₁ v₁)
    (vcons C₂ n₂ c₂ v₂))
   (retTyp : forall (nr: nat_RR (n + 1) (n₂ + 1)) (* parametrize it by the pis in caseRetTyp*)  
        (vr : Vec_RR C C₂ C_R (n + 1) (n₂ + 1) nr (vcons C n c₁ v₁) (vcons C₂ n₂ c₂ v₂)) ,Set)
   (rett : forall (nr : nat_RR n n₂) 
            (cr: C_R c₁ c₂) (vr: Vec_RR C C₂ C_R n n₂ nr v₁ v₂),
           retTyp (add_RR _ _ nr _ _ one_RR) (vcons_RR C C₂ C_R n n₂ nr _ _  cr v₁ v₂ vr) 
            (* apply the ret to constrRetIndices *)
           )
   : retTyp nro sigt.
Proof using.
Arguments existT {A} {P} x p.
rename sigt into v_R. simpl in v_R.
Show Proof.
    revert v_R. 
Show Proof.
    apply sigT_rect.
Show Proof.
    intros nrc. apply sigT_rect.
Show Proof.
    intros crc. apply sigT_rect. (* A and P are implicit, but are clearly a part of P0 *)
Show Proof.
    intros vrc peq.
Show Proof. simpl in *.
Show Proof.
    revert peq.
Show Proof.
    revert nro.
Show Proof.
    apply eq_rect_sigt2.
Show Proof.
    apply rett.
Defined.

Fixpoint Vec_rect_RR (C₁ C₂ : Set) (C_R : C₁ -> C₂ -> Prop) (P₁ : forall n : nat, Vec C₁ n -> Set)
         (P₂ : forall n : nat, Vec C₂ n -> Set)
         (P_R : forall (n₁ n₂ : nat) (n_R : nat_RR n₁ n₂) 
                  (v₁ : Vec C₁ n₁) (v₂ : Vec C₂ n₂),
                Vec_RR C₁ C₂ C_R n₁ n₂ n_R v₁ v₂ -> P₁ n₁ v₁ -> P₂ n₂ v₂ -> Set)
         (f₁ : P₁ 0 (vnil C₁)) 
         (f₂ : P₂ 0 (vnil C₂))
       (f_R: P_R 0 0 O_RR (vnil C₁) (vnil C₂) (vnil_RR C₁ C₂ C_R) f₁ f₂)
         (f₁0 : forall (n : nat) (c : C₁) (v : Vec C₁ n),
                P₁ n v -> P₁ (n + 1) (vcons C₁ n c v))
         (f₂0 : forall (n : nat) (c : C₂) (v : Vec C₂ n),
                P₂ n v -> P₂ (n + 1) (vcons C₂ n c v))
       (f0_R: forall (n₁ n₂ : nat) (n_R : nat_RR n₁ n₂) (c₁ : C₁) 
          (c₂ : C₂) (c_R : C_R c₁ c₂) (v₁ : Vec C₁ n₁) (v₂ : Vec C₂ n₂)
          (v_R : Vec_RR C₁ C₂ C_R n₁ n₂ n_R v₁ v₂) (H : P₁ n₁ v₁) 
          (H0 : P₂ n₂ v₂),
        P_R n₁ n₂ n_R v₁ v₂ v_R H H0 ->
        P_R (n₁ + 1) (n₂ + 1)
          (add_RR n₁ n₂ n_R 1 1 one_RR)
          (vcons C₁ n₁ c₁ v₁) (vcons C₂ n₂ c₂ v₂)
          (vcons_RR C₁ C₂ C_R n₁ n₂ n_R c₁ c₂ c_R v₁ v₂ v_R) 
          (f₁0 n₁ c₁ v₁ H) (f₂0 n₂ c₂ v₂ H0))
       (n₁ n₂ : nat) (n_R : nat_RR n₁ n₂) (v₁ : Vec C₁ n₁) 
         (v₂ : Vec C₂ n₂) (v_R : Vec_RR C₁ C₂ C_R n₁ n₂ n_R v₁ v₂) {struct v₁} :
       P_R n₁ n₂ n_R v₁ v₂ v_R (Vec_rect C₁ P₁ f₁ f₁0 n₁ v₁) (Vec_rect C₂ P₂ f₂ f₂0 n₂ v₂).
  revert v_R.
  revert n_R.
  destruct v₁;
   destruct v₂; intros.
  - admit.
  - simpl in v_R. apply False_rect. assumption.
  - simpl in v_R. apply False_rect. assumption.
  - simpl.
    pose proof (vcons_RRInv _ _ _ _ _ _ _ _ _ n_R v_R) as rw.
    apply rw.
    intros.
    apply f0_R.
    apply (Vec_rect_RR _ _ C_R _ _ P_R _ _ f_R _ _ f0_R).
    
(*
exact(
                      eq_rect_sigt2 (nat_RR (n + 1) (n0 + 1))
                        (existT (add_RR n n0 nrc 1 1 (S_RR 0 0 O_RR))
                           I)
                        (fun (a : nat_RR (n + 1) (n0 + 1))
                           (e : existT
                                  (add_RR n n0 nrc 1 1
                                     (S_RR 0 0 O_RR)) I = 
                                existT a I) =>
                         P_R (n + 1) (n0 + 1) a 
                           (vcons C₁ n c v₁) 
                           (vcons C₂ n0 c0 v₂)
                           (existT nrc (existT crc (existT vrc e)))
                           (f₁0 n c v₁ (Vec_rect C₁ P₁ f₁ f₁0 n v₁))
                           (f₂0 n0 c0 v₂
                              (Vec_rect C₂ P₂ f₂ f₂0 n0 v₂))) f0_R
                        n_R peq).
*)

    Fail idtac.
Abort.
Print sigT_rect.

Arguments existT {A} P x p.
 (*success!*)

Definition vcons_RRInv
 (C C₂ : Set) (C_R : C -> C₂ -> Prop) (n n₂ : nat) 
 (c₁ : C) (c₂ : C₂) 
   (v₁ : Vec C n) (v₂ : Vec C₂ n₂)
   (nro : nat_RR (n + 1) (n₂ + 1)) (* add outer indices_RR in order *)  
   (sigt : Vec_RR C C₂ C_R (n + 1) (n₂ + 1) nro (vcons C n c₁ v₁)
    (vcons C₂ n₂ c₂ v₂))
   (retTyp : forall n1 n2 (nr: nat_RR n1 n2) v1 v2 (vr : Top_vecSRevAuto_Vec_RR0 C C₂ C_R n1 n2 nr v1 v2), Set)
   (rett : forall (nr : nat_RR n n₂)
            (cr: C_R c₁ c₂) (vr: Vec_RR C C₂ C_R n n₂ nr v₁ v₂),
           retTyp (n + 1) (n₂ + 1) (add_RR _ _ nr _ _ one_RR) (vcons C n c₁ v₁) (vcons C₂ n₂ c₂ v₂) 
            (vcons_RR C C₂ C_R n n₂ nr _ _  cr v₁ v₂ vr))
   : retTyp (n + 1) (n₂ + 1) nro (vcons C n c₁ v₁) (vcons C₂ n₂ c₂ v₂) sigt.
Admitted.

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

