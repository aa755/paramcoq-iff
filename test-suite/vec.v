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
Run TemplateProgram (genParamInd [] true true "ReflParam.matchR.Vec").

(*
Arguments eq_refl : clear implicits.
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
 | vnil _ =>
     eq_refl (Vec C (0 + m))
       match vnil C in (Vec _ n0) return (Vec C (n0 + m)) with
       | vnil _ => vr
       | vcons _ n' hl tl => vcons C (n' + m) hl (vAppend C n' m tl vr)
       end
 | vcons _ n0 c vc =>
     eq_refl (Vec C ((S n0) + m))
       match vcons C n0 c vc in (Vec _ n1) return (Vec C (n1 + m)) with
       | vnil _ => vr
       | vcons _ n' hl tl => vcons C (n' + m) hl (vAppend C n' m tl vr)
       end
 end).
*)

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


Run TemplateProgram (genParam indTransEnv false true "vAppend").

Open Scope nat_scope.
Require Import SquiggleEq.UsefulTypes.
Definition ReflParam_matchR_vAppend_pmtcty_RR :
forall (C₁ C₂ : Set) (C_R : C₁ -> C₂ -> Prop) (n₁ n₂ : nat) 
   (n_R : nat_RR n₁ n₂) (m₁ m₂ : nat) (m_R : nat_RR m₁ m₂)
   (vl₁ : Vec C₁ n₁) (vl₂ : Vec C₂ n₂)
   (vl_R : Vec_RR C₁ C₂ C_R n₁ n₂ n_R vl₁ vl₂)
   (vr₁ : Vec C₁ m₁) (vr₂ : Vec C₂ m₂)
   (vr_R : Vec_RR C₁ C₂ C_R m₁ m₂ m_R vr₁ vr₂) ,
    Vec_RR C₁ C₂ C_R (n₁ + m₁) (n₂ + m₂) (add_RR n₁ n₂ n_R m₁ m₂ m_R)
         (vAppend vl₁ vr₁) (vAppend vl₂ vr₂)
:= vAppend_pmtcty_RR.

Lemma typesMatc :
forall (C₁ C₂ : Set) (C_R : C₁ -> C₂ -> Prop) (n₁ n₂ : nat) 
   (n_R : nat_RR n₁ n₂) (m₁ m₂ : nat) (m_R : nat_RR m₁ m₂)
   (vl₁ : Vec C₁ n₁) (vl₂ : Vec C₂ n₂)
   (vl_R : Vec_RR C₁ C₂ C_R n₁ n₂ n_R vl₁ vl₂)
   (vr₁ : Vec C₁ m₁) (vr₂ : Vec C₂ m₂)
   (vr_R : Vec_RR C₁ C₂ C_R m₁ m₂ m_R vr₁ vr₂) ,
   
    Vec_RR C₁ C₂ C_R (n₁ + m₁) (n₂ + m₂) (add_RR n₁ n₂ n_R m₁ m₂ m_R)
         (vAppend vl₁ vr₁) (vAppend vl₂ vr₂)
         =
       Vec_RR C₁ C₂ C_R (n₁ + m₁) (n₂ + m₂) (Coq_Init_Nat_add_pmtcty_RR n₁ n₂ n_R m₁ m₂ m_R)
         ((fix
           vAppend (C0 : Set) (n0 m0 : nat) (vl0 : Vec C0 n0) (vr0 : Vec C0 m0) {struct vl0} :
             Vec C0 (n0 + m0) :=
             match vl0 in (Vec _ n1) return (Vec C0 (n1 + m0)) with
             | vnil _ => vr0
             | vcons _ n' hl tl => vcons C0 (n' + m0) hl (vAppend C0 n' m0 tl vr0)
             end) C₁ n₁ m₁ vl₁ vr₁)
         ((fix
           vAppend₂ (C₂0 : Set) (n₂0 m₂0 : nat) (vl₂0 : Vec C₂0 n₂0) 
                    (vr₂0 : Vec C₂0 m₂0) {struct vl₂0} : Vec C₂0 (n₂0 + m₂0) :=
             match vl₂0 in (Vec _ n₂1) return (Vec C₂0 (n₂1 + m₂0)) with
             | vnil _ => vr₂0
             | vcons _ n'₂ hl₂ tl₂ =>
                 vcons C₂0 (n'₂ + m₂0) hl₂ (vAppend₂ C₂0 n'₂ m₂0 tl₂ vr₂0)
             end) C₂ n₂ m₂ vl₂ vr₂).
Proof.
  reflexivity.
Qed.             

Definition Vec_rect_type :=
forall (C : Set) (P : forall n : nat, Vec C n -> Set),
       P 0 (vnil C) ->
       (forall (n : nat) (c : C) (v : Vec C n), P n v -> P (S n) (vcons C n c v)) ->
       forall (n : nat) (v : Vec C n), P n v.


Require Import SquiggleEq.tactics.

Arguments eq_refl:clear implicits.



Print vAppend_RR.
(*
vAppend_RR = 
let
  fix vAppend (C : Set) (n m : nat) (vl : Vec C n) (vr : Vec C m) {struct vl} :
    Vec C (n + m) :=
    match vl in (Vec _ n0) return (Vec C (n0 + m)) with
    | vnil _ => vr
    | vcons _ n' hl tl => vcons C (n' + m) hl (vAppend C n' m tl vr)
    end in
let
  fix vAppend₂ (C₂ : Set) (n₂ m₂ : nat) (vl₂ : Vec C₂ n₂) (vr₂ : Vec C₂ m₂) {struct vl₂} :
    Vec C₂ (n₂ + m₂) :=
    match vl₂ in (Vec _ n₂0) return (Vec C₂ (n₂0 + m₂)) with
    | vnil _ => vr₂
    | vcons _ n'₂ hl₂ tl₂ => vcons C₂ (n'₂ + m₂) hl₂ (vAppend₂ C₂ n'₂ m₂ tl₂ vr₂)
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
| vnil _ =>
    eq_refl (Vec C (0 + m))
      match vnil C in (Vec _ n0) return (Vec C (n0 + m)) with
      | vnil _ => vr
      | vcons _ n' hl tl => vcons C (n' + m) hl (vAppend C n' m tl vr)
      end
| vcons _ n0 c vc =>
    eq_refl (Vec C (S n0 + m))
      match vcons C n0 c vc in (Vec _ n1) return (Vec C (n1 + m)) with
      | vnil _ => vr
      | vcons _ n' hl tl => vcons C (n' + m) hl (vAppend C n' m tl vr)
      end
end
     : forall (C : Set) (n m : nat) (vl : Vec C n) (vr : Vec C m),
       match vl in (Vec _ n0) return (Vec C (n0 + m)) with
       | vnil _ => vr
       | vcons _ n' hl tl =>
           vcons C (n' + m) hl
             ((fix
               vAppend (C0 : Set) (n0 m0 : nat) (vl0 : Vec C0 n0) 
                       (vr0 : Vec C0 m0) {struct vl0} : Vec C0 (n0 + m0) :=
                 match vl0 in (Vec _ n1) return (Vec C0 (n1 + m0)) with
                 | vnil _ => vr0
                 | vcons _ n'0 hl0 tl0 =>
                     vcons C0 (n'0 + m0) hl0 (vAppend C0 n'0 m0 tl0 vr0)
                 end) C n' m tl vr)
       end =
       (fix
        vAppend (C0 : Set) (n0 m0 : nat) (vl0 : Vec C0 n0) (vr0 : Vec C0 m0) {struct vl0} :
          Vec C0 (n0 + m0) :=
          match vl0 in (Vec _ n1) return (Vec C0 (n1 + m0)) with
          | vnil _ => vr0
          | vcons _ n' hl tl => vcons C0 (n' + m0) hl (vAppend C0 n' m0 tl vr0)
          end) C n m vl vr

Argument scopes are [type_scope nat_scope nat_scope _ _]

*)

(* Notation vAppend_RR := ReflParam_matchR_vAppend_pmtcty_RR. *)

Print sigT_rect.

Print indTransEnv.
Open Scope N_scope.
Run TemplateProgram (genParam indTransEnv false true "vAppend2").
 (* success!*)
(* Print vAppend2_RR. *)
