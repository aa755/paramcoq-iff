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

Inductive Vec (C : Set) : forall n:nat, Set :=
    vnil : Vec C 0 | vcons : forall (n:nat) (c:C) (v:Vec C n), Vec C (n+1).


Require Import Top.nat.
Run TemplateProgram (mkIndEnv "indTransEnv" ["Top.vecSRevAuto.Vec"]).
    

Definition one_RR : nat_RR 1 1.
apply S_RR. apply O_RR.
Defined.

Run TemplateProgram (genParamInd [] true true "Top.vecSRevAuto.Vec").

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
Notation Vec_RR := Top_vecSRevAuto_Vec_pmtcty_RR0.
Notation vcons_RR := Top_vecSRevAuto_Vec_pmtcty_RR0_constr_1.
Notation vnil_RR := Top_vecSRevAuto_Vec_pmtcty_RR0_constr_0.


Declare ML Module "paramcoq".
Parametricity Recursive Vec_rect.

Require Import SquiggleEq.tactics.

Require Import SquiggleEq.UsefulTypes.

Print Vec_rect.

Definition Vec_recs :=
fun (C : Set) (P : forall (nnnn : nat) (vvvv:Vec C nnnn), Set) (f : P 0 (vnil C))
  (ff : forall (nn : nat) (cc : C) 
  (vv : Vec C nn) (pr: P nn vv), P (nn + 1) (vcons C nn cc vv)) =>
fix F (n : nat) (v : Vec C n) {struct v} : P n v :=
  match v as v0 in (Vec _ n0) return (P n0 v0) with
  | vnil _ => f
  | vcons _ nnn ccc vvv => ff nnn ccc vvv (F nnn vvv)
  end.

Quote Definition Vec_recsSynt :=
(
fun (C : Set) (P : forall (nnnn : nat) (vvvv:Vec C nnnn), Set) (f : P 0 (vnil C))
  (ff : forall (nn : nat) (cc : C) 
  (vv : Vec C nn) (pr: P nn vv), P (nn + 1) (vcons C nn cc vv)) =>
fix F (n : nat) (v : Vec C n) {struct v} : P n v :=
  match v as v0 in (Vec _ n0) return (P n0 v0) with
  | vnil _ => f
  | vcons _ nnn ccc vvv => ff nnn ccc vvv (F nnn vvv)
  end
).


Open Scope N_scope.
Set Printing Depth 1000.


Run TemplateProgram (genParam indTransEnv false true "Vec_recs").

Lemma Vec_recsRRNilComputes 
(C C₂ : Set) (C_R : C -> C₂ -> Prop) (P : forall nnnn : nat, Vec C nnnn -> Set)
  (P₂ : forall nnnn₂ : nat, Vec C₂ nnnn₂ -> Set)
  (P_R : forall (nnnn nnnn₂ : nat) (nnnn_R : nat_RR nnnn nnnn₂),
         (fun (ff : Vec C nnnn -> Set) (ff₂ : Vec C₂ nnnn₂ -> Set) =>
          forall (vvvv : Vec C nnnn) (vvvv₂ : Vec C₂ nnnn₂),
          Vec_RR C C₂ C_R nnnn nnnn₂ nnnn_R vvvv vvvv₂ ->
          (fun H H0 : Set => H -> H0 -> Prop) (ff vvvv) (ff₂ vvvv₂)) 
           (P nnnn) (P₂ nnnn₂)) (f : P 0%nat (vnil C)) (f₂ : P₂ 0%nat (vnil C₂))
  (f_R : P_R 0%nat 0%nat O_RR (vnil C) (vnil C₂) (vnil_RR C C₂ C_R) f f₂)
  (ff : forall (nn : nat) (cc : C) (vv : Vec C nn), P nn vv -> P (nn + 1) (vcons C nn cc vv))
  (ff₂ : forall (nn₂ : nat) (cc₂ : C₂) (vv₂ : Vec C₂ nn₂),
         P₂ nn₂ vv₂ -> P₂ (nn₂ + 1) (vcons C₂ nn₂ cc₂ vv₂))
  (ff_R : forall (nn nn₂ : nat) (nn_R : nat_RR nn nn₂),
          (fun
             (ff0 : forall (cc : C) (vv : Vec C nn),
                    P nn vv -> P (nn + 1) (vcons C nn cc vv))
             (ff₂0 : forall (cc₂ : C₂) (vv₂ : Vec C₂ nn₂),
                     P₂ nn₂ vv₂ -> P₂ (nn₂ + 1) (vcons C₂ nn₂ cc₂ vv₂)) =>
           forall (cc : C) (cc₂ : C₂) (cc_R : C_R cc cc₂),
           (fun (ff1 : forall vv : Vec C nn, P nn vv -> P (nn + 1) (vcons C nn cc vv))
              (ff₂1 : forall vv₂ : Vec C₂ nn₂,
                      P₂ nn₂ vv₂ -> P₂ (nn₂ + 1) (vcons C₂ nn₂ cc₂ vv₂)) =>
            forall (vv : Vec C nn) (vv₂ : Vec C₂ nn₂)
              (vv_R : Vec_RR C C₂ C_R nn nn₂ nn_R vv vv₂),
            (fun (ff2 : P nn vv -> P (nn + 1) (vcons C nn cc vv))
               (ff₂2 : P₂ nn₂ vv₂ -> P₂ (nn₂ + 1) (vcons C₂ nn₂ cc₂ vv₂)) =>
             forall (pr : P nn vv) (pr₂ : P₂ nn₂ vv₂),
             P_R nn nn₂ nn_R vv vv₂ vv_R pr pr₂ ->
             P_R (nn + 1) (nn₂ + 1)
               (Coq_Init_Nat_add_pmtcty_RR nn nn₂ nn_R 1 1 (S_RR 0 0 O_RR))
               (vcons C nn cc vv) (vcons C₂ nn₂ cc₂ vv₂)
               (vcons_RR C C₂ C_R nn nn₂ nn_R cc cc₂ cc_R vv vv₂ vv_R) 
               (ff2 pr) (ff₂2 pr₂)) (ff1 vv) (ff₂1 vv₂)) (ff0 cc) 
             (ff₂0 cc₂)) (ff nn) (ff₂ nn₂)) :            
   Vec_recs_pmtcty_RR _ _ C_R _ _  P_R _ _ f_R _ _ ff_R 0 0 O_RR 
    (vnil C) (vnil C₂) (vnil_RR _ _ C_R)
   = f_R.
Proof.
  reflexivity.
Qed.


(*
(fun (C C₂ : Set) (C_R : C -> C₂ -> Prop) (P : forall nnnn : nat, Vec C nnnn -> Set)
   (P₂ : forall nnnn₂ : nat, Vec C₂ nnnn₂ -> Set)
   (P_R : forall (nnnn nnnn₂ : nat) (nnnn_R : nat_RR nnnn nnnn₂),
          (fun (ff : Vec C nnnn -> Set) (ff₂ : Vec C₂ nnnn₂ -> Set) =>
           forall (vvvv : Vec C nnnn) (vvvv₂ : Vec C₂ nnnn₂),
           Vec_RR C C₂ C_R nnnn nnnn₂ nnnn_R vvvv vvvv₂ ->
           (fun H H0 : Set => H -> H0 -> Prop) (ff vvvv) (ff₂ vvvv₂)) 
            (P nnnn) (P₂ nnnn₂)) (f : P 0%nat (vnil C)) (f₂ : P₂ 0%nat (vnil C₂))
   (f_R : P_R 0%nat 0%nat O_RR (vnil C) (vnil C₂) (vnil_RR C C₂ C_R) f f₂)
   (ff : forall (nn : nat) (cc : C) (vv : Vec C nn),
         P nn vv -> P (nn + 1) (vcons C nn cc vv))
   (ff₂ : forall (nn₂ : nat) (cc₂ : C₂) (vv₂ : Vec C₂ nn₂),
          P₂ nn₂ vv₂ -> P₂ (nn₂ + 1) (vcons C₂ nn₂ cc₂ vv₂))
   (ff_R : forall (nn nn₂ : nat) (nn_R : nat_RR nn nn₂),
           (fun
              (ff0 : forall (cc : C) (vv : Vec C nn),
                     P nn vv -> P (nn + 1) (vcons C nn cc vv))
              (ff₂0 : forall (cc₂ : C₂) (vv₂ : Vec C₂ nn₂),
                      P₂ nn₂ vv₂ -> P₂ (nn₂ + 1) (vcons C₂ nn₂ cc₂ vv₂)) =>
            forall (cc : C) (cc₂ : C₂) (cc_R : C_R cc cc₂),
            (fun (ff1 : forall vv : Vec C nn, P nn vv -> P (nn + 1) (vcons C nn cc vv))
               (ff₂1 : forall vv₂ : Vec C₂ nn₂,
                       P₂ nn₂ vv₂ -> P₂ (nn₂ + 1) (vcons C₂ nn₂ cc₂ vv₂)) =>
             forall (vv : Vec C nn) (vv₂ : Vec C₂ nn₂)
               (vv_R : Vec_RR C C₂ C_R nn nn₂ nn_R vv vv₂),
             (fun (ff2 : P nn vv -> P (nn + 1) (vcons C nn cc vv))
                (ff₂2 : P₂ nn₂ vv₂ -> P₂ (nn₂ + 1) (vcons C₂ nn₂ cc₂ vv₂)) =>
              forall (pr : P nn vv) (pr₂ : P₂ nn₂ vv₂),
              P_R nn nn₂ nn_R vv vv₂ vv_R pr pr₂ ->
              P_R (nn + 1) (nn₂ + 1) (add_RR nn nn₂ nn_R 1 1 (S_RR 0 0 O_RR))
                (vcons C nn cc vv) (vcons C₂ nn₂ cc₂ vv₂)
                (vcons_RR C C₂ C_R nn nn₂ nn_R cc cc₂ cc_R vv vv₂ vv_R) 
                (ff2 pr) (ff₂2 pr₂)) (ff1 vv) (ff₂1 vv₂)) (ff0 cc) 
              (ff₂0 cc₂)) (ff nn) (ff₂ nn₂)) =>
 let
   fix F (n : nat) (v : Vec C n) {struct v} : P n v :=
     match v as v0 in (Vec _ n0) return (P n0 v0) with
     | vnil _ => f
     | vcons _ nnn ccc vvv => ff nnn ccc vvv (F nnn vvv)
     end in
 let
   fix F₂ (n₂ : nat) (v₂ : Vec C₂ n₂) {struct v₂} : P₂ n₂ v₂ :=
     match v₂ as v0₂ in (Vec _ n0₂) return (P₂ n0₂ v0₂) with
     | vnil _ => f₂
     | vcons _ nnn₂ ccc₂ vvv₂ => ff₂ nnn₂ ccc₂ vvv₂ (F₂ nnn₂ vvv₂)
     end in
 fix
 F_R (n n₂ : nat) (n_R : nat_RR n n₂) (v : Vec C n) (v₂ : Vec C₂ n₂)
     (v_R : Vec_RR C C₂ C_R n n₂ n_R v v₂) {struct v} :
   P_R n n₂ n_R v v₂ v_R (F n v) (F₂ n₂ v₂) :=
   transport
     (fiat
        (match v as v0 in (Vec _ n0) return (P n0 v0) with
         | vnil _ => f
         | vcons _ nnn ccc vvv => ff nnn ccc vvv (F nnn vvv)
         end = F n v))
     (transport
        (fiat
           (match v₂ as v0₂ in (Vec _ n0₂) return (P₂ n0₂ v0₂) with
            | vnil _ => f₂
            | vcons _ nnn₂ ccc₂ vvv₂ => ff₂ nnn₂ ccc₂ vvv₂ (F₂ nnn₂ vvv₂)
            end = F₂ n₂ v₂))
        (match
           v as v0 in (Vec _ n0)
           return
             ((fun (n1 n0₂ : nat : Set) (v1 : Vec C n1 : Set) (v0₂ : Vec C₂ n0₂ : Set) =>
               forall (n0_R : nat_RR n1 n0₂) (v0_R : Vec_RR C C₂ C_R n1 n0₂ n0_R v1 v0₂),
               P_R n1 n0₂ n0_R v1 v0₂ v0_R
                 match v1 as v2 in (Vec _ n2) return (P n2 v2) with
                 | vnil _ => f
                 | vcons _ nnn ccc vvv => ff nnn ccc vvv (F nnn vvv)
                 end
                 match v0₂ as v0₂0 in (Vec _ n0₂0) return (P₂ n0₂0 v0₂0) with
                 | vnil _ => f₂
                 | vcons _ nnn₂ ccc₂ vvv₂ => ff₂ nnn₂ ccc₂ vvv₂ (F₂ nnn₂ vvv₂)
                 end) n0 n₂ v0 v₂)
         with
         | vnil _ =>
             match
               v₂ as v0₂ in (Vec _ n0₂)
               return
                 ((fun (n0 n0₂0 : nat : Set) (v0 : Vec C n0 : Set)
                     (v0₂0 : Vec C₂ n0₂0 : Set) =>
                   forall (n0_R : nat_RR n0 n0₂0)
                     (v0_R : Vec_RR C C₂ C_R n0 n0₂0 n0_R v0 v0₂0),
                   P_R n0 n0₂0 n0_R v0 v0₂0 v0_R
                     match v0 as v1 in (Vec _ n1) return (P n1 v1) with
                     | vnil _ => f
                     | vcons _ nnn ccc vvv => ff nnn ccc vvv (F nnn vvv)
                     end
                     match v0₂0 as v0₂1 in (Vec _ n0₂1) return (P₂ n0₂1 v0₂1) with
                     | vnil _ => f₂
                     | vcons _ nnn₂ ccc₂ vvv₂ => ff₂ nnn₂ ccc₂ vvv₂ (F₂ nnn₂ vvv₂)
                     end) 0%nat n0₂ (vnil C) v0₂)
             with
             | vnil _ =>
                 fun (n0_R : nat_RR 0 0)
                   (v0_R : Vec_RR C C₂ C_R 0 0 n0_R (vnil C) (vnil C₂)) =>
                 Top_vecSRevAuto_Vec_pmtcty_RR0_constr_0_inv C C₂ C_R n0_R v0_R
                   (fun (n0_R0 : nat_RR 0 0)
                      (v0_R0 : Vec_RR C C₂ C_R 0 0 n0_R0 (vnil C) (vnil C₂)) =>
                    P_R 0%nat 0%nat n0_R0 (vnil C) (vnil C₂) v0_R0
                      match vnil C as v0 in (Vec _ n0) return (P n0 v0) with
                      | vnil _ => f
                      | vcons _ nnn ccc vvv => ff nnn ccc vvv (F nnn vvv)
                      end
                      match vnil C₂ as v0₂ in (Vec _ n0₂) return (P₂ n0₂ v0₂) with
                      | vnil _ => f₂
                      | vcons _ nnn₂ ccc₂ vvv₂ => ff₂ nnn₂ ccc₂ vvv₂ (F₂ nnn₂ vvv₂)
                      end) f_R
             | vcons _ nnn₂ ccc₂ vvv₂ =>
                 fun (n0_R : nat_RR 0 (nnn₂ + 1))
                   (v0_R : Vec_RR C C₂ C_R 0 (nnn₂ + 1) n0_R (vnil C)
                             (vcons C₂ nnn₂ ccc₂ vvv₂)) =>
                 False_rectt
                   (P_R 0%nat (nnn₂ + 1) n0_R (vnil C) (vcons C₂ nnn₂ ccc₂ vvv₂) v0_R
                      match vnil C as v0 in (Vec _ n0) return (P n0 v0) with
                      | vnil _ => f
                      | vcons _ nnn ccc vvv => ff nnn ccc vvv (F nnn vvv)
                      end
                      match
                        vcons C₂ nnn₂ ccc₂ vvv₂ as v0₂ in (Vec _ n0₂) return (P₂ n0₂ v0₂)
                      with
                      | vnil _ => f₂
                      | vcons _ nnn₂0 ccc₂0 vvv₂0 => ff₂ nnn₂0 ccc₂0 vvv₂0 (F₂ nnn₂0 vvv₂0)
                      end) v0_R
             end
         | vcons _ nnn ccc vvv =>
             match
               v₂ as v0₂ in (Vec _ n0₂)
               return
                 ((fun (n0 n0₂0 : nat : Set) (v0 : Vec C n0 : Set)
                     (v0₂0 : Vec C₂ n0₂0 : Set) =>
                   forall (n0_R : nat_RR n0 n0₂0)
                     (v0_R : Vec_RR C C₂ C_R n0 n0₂0 n0_R v0 v0₂0),
                   P_R n0 n0₂0 n0_R v0 v0₂0 v0_R
                     match v0 as v1 in (Vec _ n1) return (P n1 v1) with
                     | vnil _ => f
                     | vcons _ nnn0 ccc0 vvv0 => ff nnn0 ccc0 vvv0 (F nnn0 vvv0)
                     end
                     match v0₂0 as v0₂1 in (Vec _ n0₂1) return (P₂ n0₂1 v0₂1) with
                     | vnil _ => f₂
                     | vcons _ nnn₂ ccc₂ vvv₂ => ff₂ nnn₂ ccc₂ vvv₂ (F₂ nnn₂ vvv₂)
                     end) (nnn + 1) n0₂ (vcons C nnn ccc vvv) v0₂)
             with
             | vnil _ =>
                 fun (n0_R : nat_RR (nnn + 1) 0)
                   (v0_R : Vec_RR C C₂ C_R (nnn + 1) 0 n0_R (vcons C nnn ccc vvv) (vnil C₂))
                 =>
                 False_rectt
                   (P_R (nnn + 1) 0%nat n0_R (vcons C nnn ccc vvv) 
                      (vnil C₂) v0_R
                      match vcons C nnn ccc vvv as v0 in (Vec _ n0) return (P n0 v0) with
                      | vnil _ => f
                      | vcons _ nnn0 ccc0 vvv0 => ff nnn0 ccc0 vvv0 (F nnn0 vvv0)
                      end
                      match vnil C₂ as v0₂ in (Vec _ n0₂) return (P₂ n0₂ v0₂) with
                      | vnil _ => f₂
                      | vcons _ nnn₂ ccc₂ vvv₂ => ff₂ nnn₂ ccc₂ vvv₂ (F₂ nnn₂ vvv₂)
                      end) v0_R
             | vcons _ nnn₂ ccc₂ vvv₂ =>
                 fun (n0_R : nat_RR (nnn + 1) (nnn₂ + 1))
                   (v0_R : Vec_RR C C₂ C_R (nnn + 1) (nnn₂ + 1) n0_R 
                             (vcons C nnn ccc vvv) (vcons C₂ nnn₂ ccc₂ vvv₂)) =>
                 Top_vecSRevAuto_Vec_pmtcty_RR0_constr_1_inv C C₂ C_R nnn nnn₂ ccc ccc₂ vvv
                   vvv₂ n0_R v0_R
                   (fun (n0_R0 : nat_RR (nnn + 1) (nnn₂ + 1))
                      (v0_R0 : Vec_RR C C₂ C_R (nnn + 1) (nnn₂ + 1) n0_R0
                                 (vcons C nnn ccc vvv) (vcons C₂ nnn₂ ccc₂ vvv₂)) =>
                    P_R (nnn + 1) (nnn₂ + 1) n0_R0 (vcons C nnn ccc vvv)
                      (vcons C₂ nnn₂ ccc₂ vvv₂) v0_R0
                      match vcons C nnn ccc vvv as v0 in (Vec _ n0) return (P n0 v0) with
                      | vnil _ => f
                      | vcons _ nnn0 ccc0 vvv0 => ff nnn0 ccc0 vvv0 (F nnn0 vvv0)
                      end
                      match
                        vcons C₂ nnn₂ ccc₂ vvv₂ as v0₂ in (Vec _ n0₂) return (P₂ n0₂ v0₂)
                      with
                      | vnil _ => f₂
                      | vcons _ nnn₂0 ccc₂0 vvv₂0 => ff₂ nnn₂0 ccc₂0 vvv₂0 (F₂ nnn₂0 vvv₂0)
                      end)
                   (fun (nnn_R : nat_RR nnn nnn₂) (ccc_R : C_R ccc ccc₂)
                      (vvv_R : Vec_RR C C₂ C_R nnn nnn₂ nnn_R vvv vvv₂) =>
                    ff_R nnn nnn₂ nnn_R ccc ccc₂ ccc_R vvv vvv₂ vvv_R 
                      (F nnn vvv) (F₂ nnn₂ vvv₂) (F_R nnn nnn₂ nnn_R vvv vvv₂ vvv_R))
             end
         end n_R v_R)))

*)
