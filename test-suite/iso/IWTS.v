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

Print Top_IWTS_LHS_pmtcty_RR.

Section IsoRelPreservesComp.

(** Just copied all the lambdas in front of Top_IWTS_LHS_pmtcty_RR *)
Variables (I I₂ : Set) (I_R : BestRel I I₂) (A A₂ : Set) (A_R : BestRel A A₂) 
  (B : A -> Set) (B₂ : A₂ -> Set)
  (B_R : forall (H : A) (H0 : A₂),
         BestR A_R H H0 -> (fun H1 H2 : Set => BestRel H1 H2) (B H) (B₂ H0)) 
  (AI : A -> I) (AI₂ : A₂ -> I₂)
  (AI_R : BestR
            (PiGoodSet A A₂ A_R (fun _ : A => I) (fun _ : A₂ => I₂)
               (fun (H : A) (H0 : A₂) (_ : BestR A_R H H0) => I_R)) AI AI₂)
  (BI : forall a : A, B a -> I) (BI₂ : forall a₂ : A₂, B₂ a₂ -> I₂)
  (BI_R : BestR
            (PiGoodSet A A₂ A_R (fun a : A => B a -> I) (fun a₂ : A₂ => B₂ a₂ -> I₂)
               (fun (a : A) (a₂ : A₂) (a_R : BestR A_R a a₂) =>
                PiGoodSet (B a) (B₂ a₂) (B_R a a₂ a_R) (fun _ : B a => I)
                  (fun _ : B₂ a₂ => I₂)
                  (fun (H : B a) (H0 : B₂ a₂) (_ : BestR (B_R a a₂ a_R) H H0) => I_R))) BI
            BI₂) (P : forall i : I, IWT I A B AI BI i -> Set)
  (P₂ : forall i₂ : I₂, IWT I₂ A₂ B₂ AI₂ BI₂ i₂ -> Set)
  (P_R : forall (i : I) (i₂ : I₂) (i_R : BestR I_R i i₂),
         (fun (ff : IWT I A B AI BI i -> Set) (ff₂ : IWT I₂ A₂ B₂ AI₂ BI₂ i₂ -> Set) =>
          forall (H : IWT I A B AI BI i) (H0 : IWT I₂ A₂ B₂ AI₂ BI₂ i₂),
          BestR
            (Top_IWTS_IWT_pmtcty_RR0_iso I I₂ I_R A A₂ A_R B B₂ B_R AI AI₂ AI_R BI BI₂ BI_R
               i i₂ i_R) H H0 -> (fun H1 H2 : Set => BestRel H1 H2) (ff H) (ff₂ H0)) 
           (P i) (P₂ i₂))
  (f : forall (a : A) (lim : forall b : B a, IWT I A B AI BI (BI a b)),
       (forall b : B a, P (BI a b) (lim b)) -> P (AI a) (iwt I A B AI BI a lim))
  (f₂ : forall (a₂ : A₂) (lim₂ : forall b₂ : B₂ a₂, IWT I₂ A₂ B₂ AI₂ BI₂ (BI₂ a₂ b₂)),
        (forall b₂ : B₂ a₂, P₂ (BI₂ a₂ b₂) (lim₂ b₂)) ->
        P₂ (AI₂ a₂) (iwt I₂ A₂ B₂ AI₂ BI₂ a₂ lim₂))
  (f_R : BestR
           (PiGoodSet A A₂ A_R
              (fun a : A =>
               forall lim : forall b : B a, IWT I A B AI BI (BI a b),
               (forall b : B a, P (BI a b) (lim b)) -> P (AI a) (iwt I A B AI BI a lim))
              (fun a₂ : A₂ =>
               forall lim₂ : forall b₂ : B₂ a₂, IWT I₂ A₂ B₂ AI₂ BI₂ (BI₂ a₂ b₂),
               (forall b₂ : B₂ a₂, P₂ (BI₂ a₂ b₂) (lim₂ b₂)) ->
               P₂ (AI₂ a₂) (iwt I₂ A₂ B₂ AI₂ BI₂ a₂ lim₂))
              (fun (a : A) (a₂ : A₂) (a_R : BestR A_R a a₂) =>
               PiGoodSet (forall b : B a, IWT I A B AI BI (BI a b))
                 (forall b₂ : B₂ a₂, IWT I₂ A₂ B₂ AI₂ BI₂ (BI₂ a₂ b₂))
                 (PiGoodSet (B a) (B₂ a₂) (B_R a a₂ a_R)
                    (fun b : B a => IWT I A B AI BI (BI a b))
                    (fun b₂ : B₂ a₂ => IWT I₂ A₂ B₂ AI₂ BI₂ (BI₂ a₂ b₂))
                    (fun (b : B a) (b₂ : B₂ a₂) (b_R : BestR (B_R a a₂ a_R) b b₂) =>
                     Top_IWTS_IWT_pmtcty_RR0_iso I I₂ I_R A A₂ A_R B B₂ B_R AI AI₂ AI_R BI
                       BI₂ BI_R (BI a b) (BI₂ a₂ b₂) (BI_R a a₂ a_R b b₂ b_R)))
                 (fun lim : forall b : B a, IWT I A B AI BI (BI a b) =>
                  (forall b : B a, P (BI a b) (lim b)) -> P (AI a) (iwt I A B AI BI a lim))
                 (fun lim₂ : forall b₂ : B₂ a₂, IWT I₂ A₂ B₂ AI₂ BI₂ (BI₂ a₂ b₂) =>
                  (forall b₂ : B₂ a₂, P₂ (BI₂ a₂ b₂) (lim₂ b₂)) ->
                  P₂ (AI₂ a₂) (iwt I₂ A₂ B₂ AI₂ BI₂ a₂ lim₂))
                 (fun (lim : forall b : B a, IWT I A B AI BI (BI a b))
                    (lim₂ : forall b₂ : B₂ a₂, IWT I₂ A₂ B₂ AI₂ BI₂ (BI₂ a₂ b₂))
                    (lim_R : BestR
                               (PiGoodSet (B a) (B₂ a₂) (B_R a a₂ a_R)
                                  (fun b : B a => IWT I A B AI BI (BI a b))
                                  (fun b₂ : B₂ a₂ => IWT I₂ A₂ B₂ AI₂ BI₂ (BI₂ a₂ b₂))
                                  (fun (b : B a) (b₂ : B₂ a₂)
                                     (b_R : BestR (B_R a a₂ a_R) b b₂) =>
                                   Top_IWTS_IWT_pmtcty_RR0_iso I I₂ I_R A A₂ A_R B B₂ B_R AI
                                     AI₂ AI_R BI BI₂ BI_R (BI a b) 
                                     (BI₂ a₂ b₂) (BI_R a a₂ a_R b b₂ b_R))) lim lim₂) =>
                  PiGoodSet (forall b : B a, P (BI a b) (lim b))
                    (forall b₂ : B₂ a₂, P₂ (BI₂ a₂ b₂) (lim₂ b₂))
                    (PiGoodSet (B a) (B₂ a₂) (B_R a a₂ a_R)
                       (fun b : B a => P (BI a b) (lim b))
                       (fun b₂ : B₂ a₂ => P₂ (BI₂ a₂ b₂) (lim₂ b₂))
                       (fun (b : B a) (b₂ : B₂ a₂) (b_R : BestR (B_R a a₂ a_R) b b₂) =>
                        P_R (BI a b) (BI₂ a₂ b₂) (BI_R a a₂ a_R b b₂ b_R) 
                          (lim b) (lim₂ b₂) (lim_R b b₂ b_R)))
                    (fun _ : forall b : B a, P (BI a b) (lim b) =>
                     P (AI a) (iwt I A B AI BI a lim))
                    (fun _ : forall b₂ : B₂ a₂, P₂ (BI₂ a₂ b₂) (lim₂ b₂) =>
                     P₂ (AI₂ a₂) (iwt I₂ A₂ B₂ AI₂ BI₂ a₂ lim₂))
                    (fun (H : forall b : B a, P (BI a b) (lim b))
                       (H0 : forall b₂ : B₂ a₂, P₂ (BI₂ a₂ b₂) (lim₂ b₂))
                       (_ : BestR
                              (PiGoodSet (B a) (B₂ a₂) (B_R a a₂ a_R)
                                 (fun b : B a => P (BI a b) (lim b))
                                 (fun b₂ : B₂ a₂ => P₂ (BI₂ a₂ b₂) (lim₂ b₂))
                                 (fun (b : B a) (b₂ : B₂ a₂)
                                    (b_R : BestR (B_R a a₂ a_R) b b₂) =>
                                  P_R (BI a b) (BI₂ a₂ b₂) (BI_R a a₂ a_R b b₂ b_R) 
                                    (lim b) (lim₂ b₂) (lim_R b b₂ b_R))) H H0) =>
                     P_R (AI a) (AI₂ a₂) (AI_R a a₂ a_R) (iwt I A B AI BI a lim)
                       (iwt I₂ A₂ B₂ AI₂ BI₂ a₂ lim₂)
                       (Top_IWTS_IWT_pmtcty_RR0_constr_0_iso I I₂ I_R A A₂ A_R B B₂ B_R AI
                          AI₂ AI_R BI BI₂ BI_R a a₂ a_R lim lim₂ lim_R))))) f f₂) 
  (a : A) (a₂ : A₂) (a_R : BestR A_R a a₂) (lim : forall b : B a, IWT I A B AI BI (BI a b))
  (lim₂ : forall b₂ : B₂ a₂, IWT I₂ A₂ B₂ AI₂ BI₂ (BI₂ a₂ b₂))
  (lim_R : BestR
             (PiGoodSet (B a) (B₂ a₂) (B_R a a₂ a_R)
                (fun b : B a => IWT I A B AI BI (BI a b))
                (fun b₂ : B₂ a₂ => IWT I₂ A₂ B₂ AI₂ BI₂ (BI₂ a₂ b₂))
                (fun (b : B a) (b₂ : B₂ a₂) (b_R : BestR (B_R a a₂ a_R) b b₂) =>
                 Top_IWTS_IWT_pmtcty_RR0_iso I I₂ I_R A A₂ A_R B B₂ B_R AI AI₂ AI_R BI BI₂
                   BI_R (BI a b) (BI₂ a₂ b₂) (BI_R a a₂ a_R b b₂ b_R))) lim lim₂).

Definition LHS_R :=
Top_IWTS_LHS_pmtcty_RR
I
I₂
I_R
A
A₂
A_R
B
B₂
B_R
AI
AI₂
AI_R
BI
BI₂
BI_R
P
P₂
P_R
f
f₂
f_R
a
a₂
a_R
lim
lim₂
lim_R.

Definition RHS_R :=
Top_IWTS_RHS_pmtcty_RR
I
I₂
I_R
A
A₂
A_R
B
B₂
B_R
AI
AI₂
AI_R
BI
BI₂
BI_R
P
P₂
P_R
f
f₂
f_R
a
a₂
a_R
lim
lim₂
lim_R.

Lemma IsoRelPreservesIotaDefinitionally:
LHS_R = RHS_R.
Proof.
reflexivity.
Qed.

End IsoRelPreservesComp.