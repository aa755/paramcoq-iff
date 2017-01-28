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
Require Import Top.nat.
Run TemplateProgram (mkIndEnv "indTransEnv" ["ReflParam.matchR.Vec"]).

Check vcons.

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
(*
(fix
 ReflParam_matchR_Vec_pmtcty_RR0 (C C₂ : Set) (C_R : C -> C₂ -> Prop) 
                                 (m m₂ : nat) (m_R : nat_RR m m₂) 
                                 (H : Vec C m) (H0 : Vec C₂ m₂) {struct H} : Prop :=
   match H in (Vec _ m0) return (nat_RR m0 m₂ -> Prop) with
   | vnil _ =>
       match H0 in (Vec _ m₂0) return (nat_RR 0 m₂0 -> Prop) with
       | vnil _ =>
           fun m_R0 : nat_RR 0 0 =>
           ReflParam_matchR_Vec_pmtcty_RR0_indices C C₂ C_R 0 0
             Coq_Init_Datatypes_nat_pmtcty_RR0_constr_0 m_R0
       | vcons _ n₂ _ _ => fun _ : nat_RR 0 (S n₂) => False
       end
   | vcons _ n c vc =>
       match H0 in (Vec _ m₂0) return (nat_RR (S n) m₂0 -> Prop) with
       | vnil _ => fun _ : nat_RR (S n) 0 => False
       | vcons _ n₂ c₂ vc₂ =>
           fun m_R0 : nat_RR (S n) (S n₂) =>
           {n_R : nat_RR n n₂ &
           {_ : C_R c c₂ &
           {_ : ReflParam_matchR_Vec_pmtcty_RR0 C C₂ C_R n n₂ n_R vc vc₂ &
           ReflParam_matchR_Vec_pmtcty_RR0_indices C C₂ C_R (S n) 
             (S n₂) (O_RR n n₂ n_R) m_R0}}}
       end
   end m_R)
(fun (C C₂ : Set) (C_R : C -> C₂ -> Prop) (n n₂ : nat) (c : C) (c₂ : C₂) 
   (vc : Vec C n) (vc₂ : Vec C₂ n₂) (m_R : nat_RR (S n) (S n₂))
   (sigt_R : {n_R : nat_RR n n₂ &
             {_ : C_R c c₂ &
             {_ : ReflParam_matchR_Vec_pmtcty_RR0 C C₂ C_R n n₂ n_R vc vc₂ &
             ReflParam_matchR_Vec_pmtcty_RR0_indices C C₂ C_R (S n) 
               (S n₂) (O_RR n n₂ n_R) m_R}}})
   (retTyp_R : forall m_R0 : nat_RR (S n) (S n₂),
               {n_R : nat_RR n n₂ &
               {_ : C_R c c₂ &
               {_ : ReflParam_matchR_Vec_pmtcty_RR0 C C₂ C_R n n₂ n_R vc vc₂ &
               ReflParam_matchR_Vec_pmtcty_RR0_indices C C₂ C_R 
                 (S n) (S n₂) (O_RR n n₂ n_R) m_R0}}} -> Set)
   (rett_R : forall (n_R : nat_RR n n₂) (c_R : C_R c c₂)
               (vc_R : ReflParam_matchR_Vec_pmtcty_RR0 C C₂ C_R n n₂ n_R vc vc₂),
             retTyp_R (O_RR n n₂ n_R)
               (existT (nat_RR n n₂)
                  (fun n_R0 : nat_RR n n₂ =>
                   {_ : C_R c c₂ &
                   {_ : ReflParam_matchR_Vec_pmtcty_RR0 C C₂ C_R n n₂ n_R0 vc vc₂ &
                   ReflParam_matchR_Vec_pmtcty_RR0_indices C C₂ C_R 
                     (S n) (S n₂) (O_RR n n₂ n_R0) (O_RR n n₂ n_R)}}) n_R
                  (existT (C_R c c₂)
                     (fun _ : C_R c c₂ =>
                      {_ : ReflParam_matchR_Vec_pmtcty_RR0 C C₂ C_R n n₂ n_R vc vc₂ &
                      ReflParam_matchR_Vec_pmtcty_RR0_indices C C₂ C_R 
                        (S n) (S n₂) (O_RR n n₂ n_R) (O_RR n n₂ n_R)}) c_R
                     (existT (ReflParam_matchR_Vec_pmtcty_RR0 C C₂ C_R n n₂ n_R vc vc₂)
                        (fun _ : ReflParam_matchR_Vec_pmtcty_RR0 C C₂ C_R n n₂ n_R vc vc₂ =>
                         ReflParam_matchR_Vec_pmtcty_RR0_indices C C₂ C_R 
                           (S n) (S n₂) (O_RR n n₂ n_R) (O_RR n n₂ n_R)) vc_R
                        (ReflParam_matchR_Vec_pmtcty_RR0_indicesc C C₂ C_R 
                           (S n) (S n₂) (O_RR n n₂ n_R)))))) =>
 sigT_rec
   (fun
      sigt_R0 : {n_R : nat_RR n n₂ &
                {_ : C_R c c₂ &
                {_ : ReflParam_matchR_Vec_pmtcty_RR0 C C₂ C_R n n₂ n_R vc vc₂ &
                ReflParam_matchR_Vec_pmtcty_RR0_indices C C₂ C_R 
                  (S n) (S n₂) (O_RR n n₂ n_R) m_R}}} => retTyp_R m_R sigt_R0)
   (fun n_R : nat_RR n n₂ =>
    sigT_rec
      (fun
         sigt_R0 : {_ : C_R c c₂ &
                   {_ : ReflParam_matchR_Vec_pmtcty_RR0 C C₂ C_R n n₂ n_R vc vc₂ &
                   ReflParam_matchR_Vec_pmtcty_RR0_indices C C₂ C_R 
                     (S n) (S n₂) (O_RR n n₂ n_R) m_R}} =>
       retTyp_R m_R
         (existT (nat_RR n n₂)
            (fun n_R0 : nat_RR n n₂ =>
             {_ : C_R c c₂ &
             {_ : ReflParam_matchR_Vec_pmtcty_RR0 C C₂ C_R n n₂ n_R0 vc vc₂ &
             ReflParam_matchR_Vec_pmtcty_RR0_indices C C₂ C_R (S n) 
               (S n₂) (O_RR n n₂ n_R0) m_R}}) n_R sigt_R0))
      (fun c_R : C_R c c₂ =>
       sigT_rec
         (fun
            sigt_R0 : {_ : ReflParam_matchR_Vec_pmtcty_RR0 C C₂ C_R n n₂ n_R vc vc₂ &
                      ReflParam_matchR_Vec_pmtcty_RR0_indices C C₂ C_R 
                        (S n) (S n₂) (O_RR n n₂ n_R) m_R} =>
          retTyp_R m_R
            (existT (nat_RR n n₂)
               (fun n_R0 : nat_RR n n₂ =>
                {_ : C_R c c₂ &
                {_ : ReflParam_matchR_Vec_pmtcty_RR0 C C₂ C_R n n₂ n_R0 vc vc₂ &
                ReflParam_matchR_Vec_pmtcty_RR0_indices C C₂ C_R 
                  (S n) (S n₂) (O_RR n n₂ n_R0) m_R}}) n_R
               (existT (C_R c c₂)
                  (fun _ : C_R c c₂ =>
                   {_ : ReflParam_matchR_Vec_pmtcty_RR0 C C₂ C_R n n₂ n_R vc vc₂ &
                   ReflParam_matchR_Vec_pmtcty_RR0_indices C C₂ C_R 
                     (S n) (S n₂) (O_RR n n₂ n_R) m_R}) c_R sigt_R0)))
         (fun (vc_R : ReflParam_matchR_Vec_pmtcty_RR0 C C₂ C_R n n₂ n_R vc vc₂)
            (sigt_R0 : ReflParam_matchR_Vec_pmtcty_RR0_indices C C₂ C_R 
                         (S n) (S n₂) (O_RR n n₂ n_R) m_R) =>
          match
            sigt_R0 as sigt_R1 in (ReflParam_matchR_Vec_pmtcty_RR0_indices _ _ _ _ _ _ m_R0)
            return
              (retTyp_R m_R0
                 (existT (nat_RR n n₂)
                    (fun n_R0 : nat_RR n n₂ =>
                     {_ : C_R c c₂ &
                     {_ : ReflParam_matchR_Vec_pmtcty_RR0 C C₂ C_R n n₂ n_R0 vc vc₂ &
                     ReflParam_matchR_Vec_pmtcty_RR0_indices C C₂ C_R 
                       (S n) (S n₂) (O_RR n n₂ n_R0) m_R0}}) n_R
                    (existT (C_R c c₂)
                       (fun _ : C_R c c₂ =>
                        {_ : ReflParam_matchR_Vec_pmtcty_RR0 C C₂ C_R n n₂ n_R vc vc₂ &
                        ReflParam_matchR_Vec_pmtcty_RR0_indices C C₂ C_R 
                          (S n) (S n₂) (O_RR n n₂ n_R) m_R0}) c_R
                       (existT (ReflParam_matchR_Vec_pmtcty_RR0 C C₂ C_R n n₂ n_R vc vc₂)
                          (fun _ : ReflParam_matchR_Vec_pmtcty_RR0 C C₂ C_R n n₂ n_R vc vc₂
                           =>
                           ReflParam_matchR_Vec_pmtcty_RR0_indices C C₂ C_R 
                             (S n) (S n₂) (O_RR n n₂ n_R) m_R0) vc_R sigt_R1))))
          with
          | ReflParam_matchR_Vec_pmtcty_RR0_indicesc _ _ _ _ _ _ => rett_R n_R c_R vc_R
          end))) sigt_R)
(fun (C C₂ : Set) (C_R : C -> C₂ -> Prop) (n n₂ : nat) (n_R : nat_RR n n₂) 
   (c : C) (c₂ : C₂) (c_R : C_R c c₂) (vc : Vec C n) (vc₂ : Vec C₂ n₂)
   (vc_R : ReflParam_matchR_Vec_pmtcty_RR0 C C₂ C_R n n₂ n_R vc vc₂) =>
 existT (nat_RR n n₂)
   (fun n_R0 : nat_RR n n₂ =>
    {_ : C_R c c₂ &
    {_ : ReflParam_matchR_Vec_pmtcty_RR0 C C₂ C_R n n₂ n_R0 vc vc₂ &
    ReflParam_matchR_Vec_pmtcty_RR0_indices C C₂ C_R (S n) (S n₂) 
      (O_RR n n₂ n_R0) (O_RR n n₂ n_R)}}) n_R
   (existT (C_R c c₂)
      (fun _ : C_R c c₂ =>
       {_ : ReflParam_matchR_Vec_pmtcty_RR0 C C₂ C_R n n₂ n_R vc vc₂ &
       ReflParam_matchR_Vec_pmtcty_RR0_indices C C₂ C_R (S n) (S n₂) 
         (O_RR n n₂ n_R) (O_RR n n₂ n_R)}) c_R
      (existT (ReflParam_matchR_Vec_pmtcty_RR0 C C₂ C_R n n₂ n_R vc vc₂)
         (fun _ : ReflParam_matchR_Vec_pmtcty_RR0 C C₂ C_R n n₂ n_R vc vc₂ =>
          ReflParam_matchR_Vec_pmtcty_RR0_indices C C₂ C_R (S n) 
            (S n₂) (O_RR n n₂ n_R) (O_RR n n₂ n_R)) vc_R
         (ReflParam_matchR_Vec_pmtcty_RR0_indicesc C C₂ C_R (S n) (S n₂) (O_RR n n₂ n_R)))))
(fun (C C₂ : Set) (C_R : C -> C₂ -> Prop) (m_R : nat_RR 0 0)
   (sigt_R : ReflParam_matchR_Vec_pmtcty_RR0_indices C C₂ C_R 0 0
               Coq_Init_Datatypes_nat_pmtcty_RR0_constr_0 m_R)
   (retTyp_R : forall m_R0 : nat_RR 0 0,
               ReflParam_matchR_Vec_pmtcty_RR0_indices C C₂ C_R 0 0
                 Coq_Init_Datatypes_nat_pmtcty_RR0_constr_0 m_R0 -> Set)
   (rett_R : retTyp_R Coq_Init_Datatypes_nat_pmtcty_RR0_constr_0
               (ReflParam_matchR_Vec_pmtcty_RR0_indicesc C C₂ C_R 0 0
                  Coq_Init_Datatypes_nat_pmtcty_RR0_constr_0)) =>
 (fun
    sigt_R0 : ReflParam_matchR_Vec_pmtcty_RR0_indices C C₂ C_R 0 0
                Coq_Init_Datatypes_nat_pmtcty_RR0_constr_0 m_R =>
  match
    sigt_R0 as sigt_R1 in (ReflParam_matchR_Vec_pmtcty_RR0_indices _ _ _ _ _ _ m_R0)
    return (retTyp_R m_R0 sigt_R1)
  with
  | ReflParam_matchR_Vec_pmtcty_RR0_indicesc _ _ _ _ _ _ => rett_R
  end) sigt_R)
(fun (C C₂ : Set) (C_R : C -> C₂ -> Prop) =>
 ReflParam_matchR_Vec_pmtcty_RR0_indicesc C C₂ C_R 0 0
   Coq_Init_Datatypes_nat_pmtcty_RR0_constr_0)
*)
Definition vapp :=
(let
   fix
   vAppend (C : Set) (n m : nat) (vl : Vec C n) (vr : Vec C m) {struct vl} :
     Vec C (n + m) :=
     match vl in (Vec _ n0) return (Vec C (n0 + m)) with
     | vnil _ => vr
     | vcons _ n' hl tl => vcons C (n' + m) hl (vAppend C n' m tl vr)
     end in
 let
   fix
   vAppend₂ (C₂ : Set) (n₂ m₂ : nat) (vl₂ : Vec C₂ n₂) 
            (vr₂ : Vec C₂ m₂) {struct vl₂} : Vec C₂ (n₂ + m₂) :=
     match vl₂ in (Vec _ n₂0) return (Vec C₂ (n₂0 + m₂)) with
     | vnil _ => vr₂
     | vcons _ n'₂ hl₂ tl₂ =>
         vcons C₂ (n'₂ + m₂) hl₂ (vAppend₂ C₂ n'₂ m₂ tl₂ vr₂)
     end in
 fun (C : Set) (n m : nat) (vl : Vec C n) (vr : Vec C m) =>
 match
   vl as vl0 in (Vec _ n0)
   return
     (match vl0 in (Vec _ n1) return (Vec C (n1 + m)) with
      | vnil _ => vr
      | vcons _ n' hl tl => vcons C (n' + m) hl (vAppend C n' m tl vr)
      end = vAppend C n0 m vl0 vr)
 with
 | vnil _ => eq_refl
 | vcons _ n0 c vc => eq_refl
 end).

Notation Vec_RR := ReflParam_matchR_Vec_pmtcty_RR0.

Definition vcons_RR  : forall (C₁ C₂ : Set) (C_R : C₁ -> C₂ -> Prop) (n₁ n₂ : nat) (n_R : nat_RR n₁ n₂)
  (H : C₁) (H0 : C₂) (c_R : C_R H H0) (H1 : Vec C₁ n₁) (H2 : Vec C₂ n₂)
  (v_R : Vec_RR C₁ C₂ C_R n₁ n₂ n_R H1 H2),
  Vec_RR C₁ C₂ C_R (S n₁) (S n₂) (S_RR n₁ n₂ n_R) 
         (vcons C₁ n₁ H H1) (vcons C₂ n₂ H0 H2):=
         ReflParam_matchR_Vec_pmtcty_RR0_constr_1.



Open Scope nat_scope.
Require Import SquiggleEq.UsefulTypes.
Fixpoint ReflParam_matchR_vAppend_pmtcty_RR (C₁ C₂ : Set) (C_R : C₁ -> C₂ -> Prop) (n₁ n₂ : nat) 
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
     (ReflParam_matchR_vAppend_pmtcty_RR _ _ _ _ _ _ _ _ _ _ _ tl_R  _ _ vr_R))
    in _
  end
end) n_R vl_R).
simpl vAppend. simpl add_RR.
destruct peq. exact old.
Defined.

Definition Vec_rect_type :=
forall (C : Set) (P : forall n : nat, Vec C n -> Set),
       P 0 (vnil C) ->
       (forall (n : nat) (c : C) (v : Vec C n), P n v -> P (S n) (vcons C n c v)) ->
       forall (n : nat) (v : Vec C n), P n v.


Require Import SquiggleEq.tactics.

Run TemplateProgram (genParam indTransEnv false true "vAppend").

(* Notation vAppend_RR := ReflParam_matchR_vAppend_pmtcty_RR. *)

Print sigT_rect.

Print indTransEnv.
Open Scope N_scope.
Run TemplateProgram (genParam indTransEnv false true "vAppend2").
 (* success!*)
Print vAppend2_RR.

(*
vAppend2_RR = 
fun (C C₂ : Set) (C_R : C -> C₂ -> Prop) (m m₂ : nat) (m_R : nat_RR m m₂) 
  (cdef : C) (cdef₂ : C₂) (cdef_R : C_R cdef cdef₂) (vr : Vec C m) 
  (vr₂ : Vec C₂ m₂) (vr_R : Vec_RR C C₂ C_R m m₂ m_R vr vr₂) =>
match
  vAppend vr vr as vapx in (Vec _ n)
  return
    ((fun (n0 n₂ : nat : Set) (vapx0 : Vec C n0 : Set) (vapx₂ : Vec C₂ n₂ : Set) =>
      forall n_R : nat_RR n0 n₂,
      Vec_RR C C₂ C_R n0 n₂ n_R vapx0 vapx₂ ->
      C_R match vapx0 with
          | vnil _ => cdef
          | vcons _ _ hl _ => hl
          end match vapx₂ with
              | vnil _ => cdef₂
              | vcons _ _ hl₂ _ => hl₂
              end) n (m₂ + m₂) vapx (vAppend vr₂ vr₂))
with
| vnil _ =>
    match
      vAppend vr₂ vr₂ as vapx₂ in (Vec _ n₂)
      return
        ((fun (n n₂0 : nat : Set) (vapx : Vec C n : Set) (vapx₂0 : Vec C₂ n₂0 : Set) =>
          forall n_R : nat_RR n n₂0,
          Vec_RR C C₂ C_R n n₂0 n_R vapx vapx₂0 ->
          C_R match vapx with
              | vnil _ => cdef
              | vcons _ _ hl _ => hl
              end match vapx₂0 with
                  | vnil _ => cdef₂
                  | vcons _ _ hl₂ _ => hl₂
                  end) 0 n₂ (vnil C) vapx₂)
    with
    | vnil _ =>
        fun (n_R : nat_RR 0 0) (vapx_R : Vec_RR C C₂ C_R 0 0 n_R (vnil C) (vnil C₂)) =>
        ReflParam_matchR_Vec_pmtcty_RR0_constr_0_inv C C₂ C_R n_R vapx_R
          (fun (n_R0 : nat_RR 0 0) (_ : Vec_RR C C₂ C_R 0 0 n_R0 (vnil C) (vnil C₂)) =>
           C_R match vnil C with
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
        ((fun (n n₂0 : nat : Set) (vapx : Vec C n : Set) (vapx₂0 : Vec C₂ n₂0 : Set) =>
          forall n_R : nat_RR n n₂0,
          Vec_RR C C₂ C_R n n₂0 n_R vapx vapx₂0 ->
          C_R match vapx with
              | vnil _ => cdef
              | vcons _ _ hl0 _ => hl0
              end match vapx₂0 with
                  | vnil _ => cdef₂
                  | vcons _ _ hl₂ _ => hl₂
                  end) (S n') n₂ (vcons C n' hl tl) vapx₂)
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
        ReflParam_matchR_Vec_pmtcty_RR0_constr_1_inv C C₂ C_R n' n'₂ hl hl₂ tl tl₂ n_R
          vapx_R
          (fun (n_R0 : nat_RR (S n') (S n'₂))
             (_ : Vec_RR C C₂ C_R (S n') (S n'₂) n_R0 (vcons C n' hl tl)
                    (vcons C₂ n'₂ hl₂ tl₂)) =>
           C_R match vcons C n' hl tl with
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
end (add_RR m m₂ m_R m m₂ m_R)
  (vAppend_RR C C₂ C_R m m₂ m_R m m₂ m_R vr vr₂ vr_R vr vr₂ vr_R)
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

