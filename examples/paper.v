

Definition xx:=  forall (T:Type) (t1 t2:T), bool.


(* Print xx_R. *)

Definition xx_Rb :=
fun f₁ f₂ : forall T : Type, T -> T -> bool =>
forall (T₁ T₂ : Type) (T_R : T₁ -> T₂ -> Type) (t1₁ : T₁) (t1₂ : T₂),
T_R t1₁ t1₂ ->
forall (t2₁ : T₁) (t2₂ : T₂), T_R t2₁ t2₂ -> (f₁ T₁ t1₁ t2₁) = (f₂ T₂ t1₂ t2₂).



Definition xx1:=  forall (T:Type) (t:T), bool.

(*
Declare ML Module "paramcoq".
(* Print xx1_R. *)
Parametricity Recursive bool.

Definition xx1_Rb :=
fun f₁ f₂ : forall T : Type, T ->  bool =>
forall (T₁ T₂ : Type) (T_R : T₁ -> T₂ -> Prop) (t₁ : T₁) (t₂ : T₂),
T_R t₁ t₂ ->
bool_R (f₁ T₁ t₁) (f₂ T₂ t₂).
*)


Definition xxp:=  forall (T:Type) (t:T), Prop.


(** P is a proposition := P:Prop 
Props are treated just like types. Thus, it is not surprising that
their translatins are relations.
Props P1 and P2 are related if there is a relation between P1 and P2.
This makes sense if we treat P1 and P2 as types. But if we treat
them as logical propositions,the fact that there is a relation between P1
and P2 carries no useful information -- we can always cook up a relation between
any two props/types. 
Also, take a look at [Prop] and [bool]
 *)

Definition xxp_Rp :=
fun f1 f2 : forall T : Type, T -> Prop =>
forall (T₁ T₂ : Type) (T_R : T₁ -> T₂ -> Prop) (t₁ : T₁) (t₂ : T₂),
T_R t₁ t₂ -> f1 T₁ t₁ -> f2 T₂ t₂ -> Prop.
                
Definition xxp_Riff :=
fun f₁ f₂ : forall T : Type, T ->  Prop =>
forall (T₁ T₂ : Type) (T_R : T₁ -> T₂ -> Prop) (t₁ : T₁) (t₂ : T₂),
  T_R t₁ t₂ -> (f₁ T₁ t₁) <-> (f₂ T₂ t₂).

Definition PP:= Prop.

Definition Prop_R :=  fun P1 P2 : Prop => P1 -> P2 -> Prop.

Definition xxp_Rbad := fun (T:Type) (t:T) => forall (t2:T), t=t2.

(* only totality on T is needed in this example *)
Definition xxpb:=  forall (T:Type)  (f:T->bool), Prop.

Definition xxpbBad :=  fun  (T:Type) (f:T->bool) => forall (x:T), f x = true.

Definition goodP {P1 P2: Prop} (R : P1 -> P2 -> Prop) := P1 <-> P2 /\ (forall (x:P1) (y:P2), R x y).

Inductive nat : Set :=
| O : nat
| S : nat -> nat.

Definition pred (n:nat) : nat :=
  match n with
  | O  => O
  | S n => n
  end.

 (*
Locate well_founded.
Print Acc.
 seems to allow singletons 
*)

(*
Declare ML Module "paramcoq".
Parametricity Recursive True.
Parametricity Recursive False.
Print True_R.
Print False_R.
*)

Inductive True_R : True -> True -> Prop :=  True_R_I_R : True_R I I.
Inductive False_R : False -> False -> Prop := .

Definition isZero (n:nat) : Prop :=
  match n with
  | O  => True
  | S _ => False
  end.

(*
Parametricity Recursive xx.
Parametricity Recursive xx1.
(* Check (eq_refl : xx1_Rb = xx1_R). *)
Parametricity Recursive xxp.
Parametricity Recursive PP.

Parametricity Recursive nat.
Parametricity Recursive pred.
Parametricity Recursive largeElim.
 *)

Inductive nat_R : nat -> nat -> Set :=
| O_R : nat_R O O
| S_R : forall n n' : nat, nat_R n n' -> nat_R (S n) (S n').

Definition pred_R (n n' : nat) (n_R : nat_R n n') 
 : nat_R (pred n) (pred n') := 
match n_R with
| O_R => O_R
| S_R n n' n_R => n_R
end.

Definition isTrue_R (n n' : nat) (n_R : nat_R n n')
 : (isZero n) -> (isZero n') -> Prop :=
match n_R with
| O_R => True_R
| S_R _ _ _ => False_R
end.

(*
Require Import ReflParam.paramDirect.
*)

Require Import String.
Open Scope string_scope.

Require Import List.
Import ListNotations.

(*
Run TemplateProgram (genParamInd [] true true "Top.paper.nat").
*)

Module Ded.
Fixpoint nat_R (n n' : nat) : Prop :=
match n,n' with
| O, O => True
| S m, S m' => nat_R m m'
| _,_ => False
end.

Definition O_R : nat_R O O := I.

Definition S_R (n n' : nat) (n_R : nat_R n n') 
 : nat_R (S n) (S n') := n_R.

Require Import Coq.Unicode.Utf8.
Definition pred_R (n n' : nat) (n_R: nat_R n n')
 : nat_R (pred n) (pred n') :=
(match n, n' 
  return (nat_R n n') -> nat_R (pred n) (pred n')
  with
| O, O => λ (n_R: nat_R O O), O_R
| S m, S m' => λ (m_R: nat_R (S m) (S m')), m_R
| _, _ => λ n_R, False_rect _ n_R
end) n_R.

Definition isTrue_R (n n' : nat) (n_R : nat_R n n')
 : (isZero n) -> (isZero n') -> Prop  :=
(match n,n' 
  return forall (n_R:nat_R n n'), 
    (isZero n) -> (isZero n') -> Prop
  with
| O,O => fun _ => True_R
| S _, S _ => fun _ => False_R
| _,_ => fun n_R => False_rect _ n_R
end) n_R.

End Ded.


Inductive Vec (T: Set): forall (m: nat), Set :=
| nilV: Vec T O
| consV: forall (n: nat), T -> Vec T n -> Vec T (S n).

(*
Parametricity Recursive Vec.
Print Vec_R.
*)

Inductive Vec_R (T T' : Set) (T_R : T -> T' -> Prop)
  : forall (m m' : nat) (m_R : nat_R m m') (v : Vec T m) (v' : Vec T' m'), Prop :=
| nilV_R : Vec_R T T' T_R O O O_R (nilV T) (nilV T')
| consV_R : forall (n n' : nat) (n_R : nat_R n n') (t : T) (t' : T'),
  T_R t t' -> forall (vn : Vec T n) (vn' : Vec T' n'),
  Vec_R T T' T_R n n' n_R vn vn' ->
  Vec_R T T' T_R (S n) (S n') (S_R n n' n_R) (consV T n t vn) (consV T' n' t' vn').

Module DedV.
Arguments nilV {T}.
Arguments consV {T} n _ _.
Notation nat_R := Ded.nat_R.

Fixpoint Vec_R (T T' : Set) (T_R : T ->  T' -> Prop)
  (m m' : nat) (m_R : nat_R m m') (v : Vec T m) (v' : Vec T' m') : Prop :=
match v,v' with
| nilV, nilV => True
| consV n t vn, consV n' t' vn' =>
  {n_R : nat_R n n' | T_R t t' /\ Vec_R T T' T_R n n' n_R vn vn'}
| _, _ => False
end.

End DedV.

Require Import Coq.Unicode.Utf8.


Module DedVC.
Notation nat_R := Ded.nat_R.
Notation O_R := Ded.O_R.
Notation S_R := Ded.S_R.

Fixpoint Vec_R (T T' : Set) (T_R : T ->  T' -> Prop)
  (m m' : nat) (m_R : nat_R m m') (v : Vec T m) (v' : Vec T' m') : Prop :=
(match v,v' with
| nilV, nilV => λ m_R, m_R = O_R
| consV n t vn, consV n' t' vn' => λ m_R,
  {n_R : nat_R n n' & T_R t t' /\ Vec_R T T' T_R n n' n_R vn vn' /\ m_R = (S_R n n' n_R)}
| _, _ => λ _ , False
end) m_R.

End DedVC.


Print Vec_rect.

(*
Inductive depInd (A I : Set) (B: I-> Set) (f: A-> I) (g: forall i, B i): forall (i:I) (b:B i), Set :=
dind : forall (a:A), depInd A I B f g (f a) (g (f a)).
*)

Inductive depInd : forall (n:nat) (v:Vec nat n), Set :=
dind : forall (vv : Vec nat O), depInd O vv.

Definition depIndRec (P : ∀ (n : nat) (v : Vec nat n) (d: depInd n v), Set) 
(f : ∀ vv : Vec nat O, P O vv (dind vv)) (n : nat) (v : Vec nat n) (d : depInd n v) : P n v d:=
match d  with
| dind x => f x
end.

(*
Run TemplateProgram (genParamInd [] true true "Top.paper.Vec").
Run TemplateProgram (genParamInd [] true true "Top.paper.depInd").

Run TemplateProgram (mkIndEnv "indTransEnv" 
  ["Top.paper.Vec"; "Top.paper.nat"; "Top.paper.depInd"]).

Run TemplateProgram (genParam indTransEnv false true "depInd_recs").
*)

Module DedM.
(*
Notation nat_R := Top_paper_nat_pmtcty_RR0.
Notation Vec_R := Top_paper_Vec_pmtcty_RR0.
Notation depInd_R := Top_paper_depInd_pmtcty_RR0.
Notation depInd_indicesReq := Top_paper_depInd_pmtcty_RR0_indices.
Print Top_paper_depInd_pmtcty_RR0.
Print Top_paper_depInd_pmtcty_RR0_constr_0 .
Goal False.
set (f:= depInd_recs_pmtcty_RR).
unfold depInd_recs_pmtcty_RR in f.
unfold Top_paper_depInd_pmtcty_RR0_constr_0_inv in f.
Arguments existT {A} {P} x p.

Definition xx (P : ∀ (n : nat) (v : Vec nat n), depInd n v → Set)
     (P₂ : ∀ (n₂ : nat) (v₂ : Vec nat n₂), depInd n₂ v₂ → Set)
     (P_R : ∀ (n n₂ : nat) (n_R : nat_R n n₂) (v : Vec nat n) (v₂ : Vec nat n₂)
            (v_R : Vec_R nat nat nat_R n n₂ n_R v v₂) (H : depInd n v) 
            (H0 : depInd n₂ v₂), depInd_R n n₂ n_R v v₂ v_R H H0 → P n v H → P₂ n₂ v₂ H0 → Prop)
     (f : ∀ vv : Vec nat O, P O vv (dind vv)) (f₂ : ∀ vv₂ : Vec nat O, P₂ O vv₂ (dind vv₂))
     (f_R : ∀ (vv vv₂ : Vec nat O)
            (vv_R : Vec_R nat nat nat_R O O Top_paper_nat_pmtcty_RR0_constr_0 vv vv₂),
            P_R O O Top_paper_nat_pmtcty_RR0_constr_0 vv vv₂ vv_R (dind vv) 
              (dind vv₂) (Top_paper_depInd_pmtcty_RR0_constr_0 vv vv₂ vv_R) 
              (f vv) (f₂ vv₂)) (n n₂ : nat) (n_R : nat_R n n₂) (v : Vec nat n) 
     (v₂ : Vec nat n₂) (v_R : Vec_R nat nat nat_R n n₂ n_R v v₂) (d : depInd n v)
     (d₂ : depInd n₂ v₂) (d_R : depInd_R n n₂ n_R v v₂ v_R d d₂) :=
     match
       d as d0 in (depInd n0 v0)
       return
         (∀ (n0_R : nat_R n0 n₂) (v0_R : Vec_R nat nat nat_R n0 n₂ n0_R v0 v₂)
          (d0_R : depInd_R n0 n₂ n0_R v0 v₂ v0_R d0 d₂),
          P_R n0 n₂ n0_R v0 v₂ v0_R d0 d₂ d0_R
            match d0 as d1 in (depInd n1 v1) return (P n1 v1 d1) with
            | dind x => f x
            end
            match d₂ as d0₂ in (depInd n0₂ v0₂) return (P₂ n0₂ v0₂ d0₂) with
            | dind x₂ => f₂ x₂
            end)
     with
     | dind x =>
         match
           d₂ as d0₂ in (depInd n0₂ v0₂)
           return
             (∀ (n0_R : nat_R O n0₂) (v0_R : Vec_R nat nat nat_R O n0₂ n0_R x v0₂)
              (d0_R : depInd_R O n0₂ n0_R x v0₂ v0_R (dind x) d0₂),
              P_R O n0₂ n0_R x v0₂ v0_R (dind x) d0₂ d0_R (f x)
                match d0₂ as d0₂0 in (depInd n0₂0 v0₂0) return (P₂ n0₂0 v0₂0 d0₂0) with
                | dind x₂ => f₂ x₂
                end)
         with
         | dind x₂ =>
             λ (n0_R : nat_R O O) (v0_R : Vec_R nat nat nat_R O O n0_R x x₂)
             (d0_R : depInd_R O O n0_R x x₂ v0_R (dind x) (dind x₂)),
             let
               (vv_R, sigt_R) as sigt_R
                return (P_R O O n0_R x x₂ v0_R (dind x) (dind x₂) sigt_R (f x) (f₂ x₂)) :=
               d0_R in
             match
               sigt_R as sigt_R0 in (depInd_indicesReq _ _ _ _ _ _ n_R0 v_R0)
               return
                 (P_R O O n_R0 x x₂ v_R0 (dind x) (dind x₂) (existT vv_R sigt_R0) (f x) (f₂ x₂))
             with
             | Top_paper_depInd_pmtcty_RR0_indicesc _ _ _ _ _ _ => f_R x x₂ vv_R
             end
         end
     end n_R v_R d_R.

Abort.
*)
Notation nat_R := Ded.nat_R.
Notation Vec_R := DedV.Vec_R.
Notation O_R := Ded.O_R.

Inductive depInd_indicesReq (n n' : nat)  (n_R : nat_R n n') (v : Vec nat n) (v' : Vec nat n')
(v_R : Vec_R nat nat nat_R n n' n_R v v'): forall (n_Ri: nat_R n n') (v_Ri: Vec_R nat nat nat_R n n' n_Ri v v'), Prop :=
depInd_refl :  depInd_indicesReq n n' n_R v v' v_R n_R v_R.





Require Import SquiggleEq.UsefulTypes.

Arguments transport {T} {a} {b} P eq pa.

(*
Fixpoint depInd_R (n n' : nat) (n_R : nat_R n n') (v : Vec nat n) (v' : Vec nat n') 
  (b_R : Vec_R nat nat nat_R n n' n_R v v') (m : depInd n v) (m' : depInd n' v'): Prop :=
(match m,m' with
| dind vv, dind vv' => λ (n_R0 : nat_R O O) (v_R0 : Vec_R nat nat nat_R O O n_R0 vv vv'),
  {vv_R : Vec_R nat nat nat_R O O O_R vv vv' &
       {p: n_R0 = O_R & transport (fun (n_R2: nat_R O O) => Vec_R nat nat nat_R O O n_R2 vv vv') p v_R0 = vv_R}}
end) n_R b_R.
*)
Fixpoint depInd_R (n n' : nat) (n_R : nat_R n n') (v : Vec nat n) (v' : Vec nat n') 
(v_R : Vec_R nat nat nat_R n n' n_R v v') (m : depInd n v) (m' : depInd n' v'): Prop :=
(match m,m' with
| dind vv, dind vv' => λ (n_R : nat_R O O) (v_R : Vec_R nat nat nat_R O O n_R vv vv'),
  {vv_R : Vec_R nat nat nat_R O O O_R vv vv' & depInd_indicesReq O O O_R vv vv' vv_R n_R v_R}
end) n_R v_R.

Print depInd_rect.

Definition  dind_R  (vv vv₂ : Vec nat O) (vv_R : Vec_R nat nat nat_R O O O_R vv vv₂)
: depInd_R O O O_R vv vv₂ vv_R (dind vv) (dind vv₂) := existT _ vv_R (depInd_refl O O O_R vv vv₂ vv_R).

Arguments existT {A} {P} x p.

(* Notation " x , p |)" := (@existT _ _ x p) (at level 20). *)

Definition xxr (P : ∀ (n : nat) (v : Vec nat n), depInd n v → Set)
 (P' : ∀ (n' : nat) (v' : Vec nat n'), depInd n' v' → Set)
 (P_R : ∀ (n n' : nat) (n_R : nat_R n n') (v : Vec nat n) (v' : Vec nat n')
           (v_R : Vec_R nat nat nat_R n n' n_R v v') (d : depInd n v)
            (d' : depInd n' v') (d_R : depInd_R n n' n_R v v' v_R d d'), P n v d → P' n' v' d' → Prop)
 (f : ∀ vv : Vec nat O, P O vv (dind vv)) (f' : ∀ vv' : Vec nat O, P' O vv' (dind vv'))
 (f_R : ∀ (vv vv' : Vec nat O) (vv_R : Vec_R nat nat nat_R O O O_R vv vv'),
            P_R O O O_R vv vv' vv_R (dind vv) (dind vv') (dind_R vv vv' vv_R) (f vv) (f' vv')) 
 (n n' : nat) (n_R : nat_R n n') (v : Vec nat n) (v' : Vec nat n') 
 (v_R : Vec_R nat nat nat_R n n' n_R v v') (d : depInd n v)
 (d' : depInd n' v') (d_R : depInd_R n n' n_R v v' v_R d d') :
 P_R _ _ n_R _ _ v_R _ _ d_R (depIndRec _ f _ _  d) (depIndRec _ f' _ _  d') :=
match d 
       as d0 in (depInd n0 v0)
       return
         (∀ (n0_R : nat_R n0 n') (v0_R : Vec_R nat nat nat_R n0 n' n0_R v0 v')
          (d0_R : depInd_R n0 n' n0_R v0 v' v0_R d0 d'),
          P_R n0 n' n0_R v0 v' v0_R d0 d' d0_R
            match d0 as d1 in (depInd n1 v1) return (P n1 v1 d1) with
            | dind x => f x
            end
            match d' as d0' in (depInd n0' v0') return (P' n0' v0' d0') with
            | dind x' => f' x'
            end)

with
| dind x => 
  match d' 

 as d0' in (depInd n0' v0')
           return
             (∀ (n0_R : nat_R O n0') (v0_R : Vec_R nat nat nat_R O n0' n0_R x v0')
              (d0_R : depInd_R O n0' n0_R x v0' v0_R (dind x) d0'),
              P_R O n0' n0_R x v0' v0_R (dind x) d0' d0_R (f x)
                match d0' as d0'0 in (depInd n0'0 v0'0) return (P' n0'0 v0'0 d0'0) with
                | dind x' => f' x'
                end)

  with
  | dind x' =>
   λ (nn_R : nat_R O O) (vv_R : Vec_R nat nat nat_R O O nn_R x x')
    (dd_R : depInd_R O O nn_R x x' vv_R (dind x) (dind x')),
    match dd_R with
    | existT x_R pdeq => 

      (match pdeq as sigt_R0 in (depInd_indicesReq _ _ _ _ _ _ n_R0 v_R0)
       return (P_R O O n_R0 x x' v_R0 (dind x) (dind x') (existT x_R sigt_R0) (f x) (f' x'))

       with
       | depInd_refl _ _ _ _ _ _ => (f_R x x' x_R):
          (P_R O O O_R x x' x_R (dind x) (dind x') (dind_R x x' x_R) (f x) (f' x'))
       end):
       (P_R O O nn_R x x' vv_R (dind x) (dind x') (existT x_R pdeq) (f x) (f' x'))
    end
  end
end n_R v_R d_R.
End DedM.

(* not that this does not even mention the relation *)


Definition CompleteRel  {A A' : Prop} (R : A -> A' -> Prop) : Prop := (forall (a : A) (a' : A'), R a a').

Definition IffProps {A A' : Prop} (R : A -> A' -> Prop) : Prop := (A <-> A').

Definition TProp :=
 λ (A A': Prop), {R : A -> A' -> Prop & IffProps R /\ CompleteRel R}.

Definition OneToOne  {A B : Type} (R : A -> B -> Prop) : Prop :=
(forall (a:A) (b1 b2: B), R a b1 -> R a b2 ->  b1=b2) /\ (forall (b:B) (a1 a2: A), R a1 b -> R a2 b ->  a1=a2).

Definition Total {A B : Set} (R: A -> B -> Prop) : Type :=
(forall (a:A), {b:B & (R a b)}) * (forall (b:B), {a:A & (R a b)}).

Definition PNone := λ (T:Set) (f:T->nat) (a b :T) , (f a = f b).
Definition PTot := λ (T:Set) (f:T->nat), forall (t:T), f t = O.
Definition POne := λ (T:Set) (f:nat->T), f O = f (S O).
Module Proofs.
(* Parametricity Recursive PNone. *)
Axiom natRSimpl: forall n1 n2, nat_R n1 n2 -> n1=n2.
Lemma PNone (T₁ T₂ : Set) (T_R : T₁ → T₂ → Set) (f₁ : T₁ → nat) (f₂ : T₂ → nat)
(f_R : ∀ (H : T₁) (H0 : T₂), T_R H H0 → nat_R (f₁ H) (f₂ H0)) 
(a₁ : T₁) (a₂ : T₂) (a_R : T_R a₁ a₂) (b₁ : T₁) (b₂ : T₂) 
(b_R : T_R b₁ b₂):
(PNone T₁ f₁ a₁ b₁) <-> (PNone T₂ f₂ a₂ b₂).
Proof.
  unfold PNone. apply f_R in a_R. apply f_R in b_R.
  apply natRSimpl in a_R.
  apply natRSimpl in b_R.
  rewrite a_R, b_R. reflexivity.
Qed.
End Proofs.
Infix "×" := prod (at level 40).

Definition TSet : forall A A', Type :=
λ (A A': Set), {R : A -> A' -> Prop & Total R × OneToOne R}.

(*
Definition BRPi A A' A_R B B':=
  forall (a:A) (a':A'), A_R a a' -> BestRel (B a) (B' a').
*)

Definition irrelevant  {A A' : Set} (R : A -> A' -> Set)  := forall (a:A) (a':A') (p1 p2: R a a'), p1 = p2.

Print le.

Inductive le (n : nat) : nat -> Prop :=
|le_n : le n n 
|le_S : forall m : nat, le n m -> le n (S m).

Inductive IWP (I A : Set) (B : A -> Set) (AI : A -> I)  (BI : forall (a : A), B a -> I) : forall (i:I), Prop :=
iwp : forall (a : A) (node : forall b : B a, IWP I A B AI BI (BI a b)), IWP I A B AI BI (AI a).

(*
Parametricity Recursive IWP.
Print IWP_R.
*)

Inductive IWP_R (I₁ I₂ : Set) (I_R : I₁ → I₂ → Prop) (A₁ A₂ : Set) 
(A_R : A₁ → A₂ → Prop) (B₁ : A₁ → Set) (B₂ : A₂ → Set)
(B_R : ∀ (H : A₁) (H0 : A₂), A_R H H0 → B₁ H → B₂ H0 → Prop) 
(AI₁ : A₁ → I₁) (AI₂ : A₂ → I₂)
(AI_R : ∀ (H : A₁) (H0 : A₂), A_R H H0 → I_R (AI₁ H) (AI₂ H0))
(BI₁ : ∀ a : A₁, B₁ a → I₁) (BI₂ : ∀ a : A₂, B₂ a → I₂)
(BI_R : ∀ (a₁ : A₁) (a₂ : A₂) (a_R : A_R a₁ a₂) (H : B₁ a₁) 
        (H0 : B₂ a₂), B_R a₁ a₂ a_R H H0 → I_R (BI₁ a₁ H) (BI₂ a₂ H0))
  : ∀ (i₁ : I₁) (i₂ : I₂), I_R i₁ i₂ → IWP I₁ A₁ B₁ AI₁ BI₁ i₁ → IWP I₂ A₂ B₂ AI₂ BI₂ i₂ → Prop :=

|iwp_R : ∀ (a₁ : A₁) (a₂ : A₂) (a_R : A_R a₁ a₂)
                  (node₁ : ∀ b : B₁ a₁, IWP I₁ A₁ B₁ AI₁ BI₁ (BI₁ a₁ b))
                  (node₂ : ∀ b : B₂ a₂, IWP I₂ A₂ B₂ AI₂ BI₂ (BI₂ a₂ b)),
                  (∀ (b₁ : B₁ a₁) (b₂ : B₂ a₂) (b_R : B_R a₁ a₂ a_R b₁ b₂),
                   IWP_R I₁ I₂ I_R A₁ A₂ A_R B₁ B₂ B_R AI₁ AI₂ AI_R BI₁ BI₂ BI_R
                     (BI₁ a₁ b₁) (BI₂ a₂ b₂) (BI_R a₁ a₂ a_R b₁ b₂ b_R) 
                     (node₁ b₁) (node₂ b₂))
                  → IWP_R I₁ I₂ I_R A₁ A₂ A_R B₁ B₂ B_R AI₁ AI₂ AI_R BI₁ BI₂ BI_R
                      (AI₁ a₁) (AI₂ a₂) (AI_R a₁ a₂ a_R)
                      (iwp I₁ A₁ B₁ AI₁ BI₁ a₁ node₁)
                      (iwp I₂ A₂ B₂ AI₂ BI₂ a₂ node₂).

Scheme IRP_indd := Induction for IWP Sort Prop. 


Lemma IWP_R_complete_simpl
(I I' : Set) (I_R : I -> I' -> Prop) (A A' : Set) (A_R : A -> A' -> Prop)
(B : A -> Set) (B' : A' -> Set)
(B_R : forall (H : A) (H0 : A'), A_R H H0 -> B H -> B' H0 -> Prop)
(AI : A -> I) (AI' : A' -> I')
(AI_R : forall (H : A) (H0 : A'), A_R H H0 -> I_R (AI H) (AI' H0))
(BI : forall a : A, B a -> I) (BI' : forall a : A', B' a -> I')
(BI_R : forall (a : A) (a' : A') (a_R : A_R a a') (H : B a) (H0 : B' a'),
        B_R a a' a_R H H0 -> I_R (BI a H) (BI' a' H0))
 (i : I) (i' : I') (i_R : I_R i i')
(* extra*)
(I_R_iso : OneToOne I_R) (*total Hetero not needed*)
(A_R_tot : Total A_R) (* TotalHeteroRel implies TotalHeteroRelP *)
(B_R_tot : forall (a : A) (a' : A') (a_R : A_R a a'), Total (B_R _ _ a_R))
(x : IWP I A B AI BI i)
:
(IWP I' A' B' AI' BI' i') 
/\ (forall y : IWP I' A' B' AI' BI' i', IWP_R I I' I_R A A' A_R B B' B_R AI AI' AI_R BI BI' BI_R i i' i_R x y).
Proof.
  revert i_R.
  revert i'.
  induction x  as [a node Hb]  using IRP_indd.
  pose proof (fst A_R_tot a) as Haa.
  destruct Haa as [a' a_R].
  intros.
  pose proof (AI_R _ _ a_R) as ir2. (* similarly, iff wont be sufficient for A_R *)
  pose proof (proj1 I_R_iso _ _ _ i_R ir2) as Hir2.
  subst. clear ir2.
  evar ( c2 : IWP I' A' B' AI' BI' (AI' a')).
  Unshelve. Focus 2.
     constructor.
     intros b₂.
     pose proof (snd (B_R_tot _ _ a_R) b₂) as b1.
     destruct b1 as [b1 br].
     apply Hb with (b:=b1). apply BI_R with (a_R:=a_R). exact br.
  (* the above is the same as iff *)

  split;[exact c2|].
Check 
(
∀ y : IWP I' A' B' AI' BI' (AI' a'), IWP_R I I' I_R A A' A_R B B' B_R AI AI' AI_R BI BI' BI_R (AI a) (AI' a') i_R (iwp I A B AI BI a node) y
).
Abort.
(*
(* 

regexp replace

(([A-Za-z0-9_])*)\\_R

with

\\trel{$1}

*)
