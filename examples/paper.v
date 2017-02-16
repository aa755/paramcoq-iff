

Definition xx:=  forall (T:Type) (t1 t2:T), bool.


(* Print xx_R. *)

Definition xx_Rb :=
fun f₁ f₂ : forall T : Type, T -> T -> bool =>
forall (T₁ T₂ : Type) (T_R : T₁ -> T₂ -> Type) (t1₁ : T₁) (t1₂ : T₂),
T_R t1₁ t1₂ ->
forall (t2₁ : T₁) (t2₂ : T₂), T_R t2₁ t2₂ -> (f₁ T₁ t1₁ t2₁) = (f₂ T₂ t1₂ t2₂).



Definition xx1:=  forall (T:Type) (t:T), bool.

Declare ML Module "paramcoq".
(* Print xx1_R. *)
Parametricity Recursive bool.

Definition xx1_Rb :=
fun f₁ f₂ : forall T : Type, T ->  bool =>
forall (T₁ T₂ : Type) (T_R : T₁ -> T₂ -> Prop) (t₁ : T₁) (t₂ : T₂),
T_R t₁ t₂ ->
bool_R (f₁ T₁ t₁) (f₂ T₂ t₂).


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


Locate well_founded.
Print Acc. (* seems to allow singletons *)
Parametricity Recursive True.
Parametricity Recursive False.

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

Require Import ReflParam.paramDirect.

Require Import String.
Open Scope string_scope.

Require Import List.
Import ListNotations.

Run TemplateProgram (genParamInd [] true true "Top.paper.nat").

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

Definition depInd_recs (P : ∀ (n : nat) (v : Vec nat n), depInd n v → Set) 
(f : ∀ vv : Vec nat O, P O vv (dind vv)) (n : nat) (v : Vec nat n) (d : depInd n v)
: P n v d:=
match d as d0 in (depInd n0 v0) return (P n0 v0 d0) with
| dind x => f x
end.

Run TemplateProgram (genParamInd [] true true "Top.paper.Vec").
Run TemplateProgram (genParamInd [] true true "Top.paper.depInd").

Run TemplateProgram (mkIndEnv "indTransEnv" 
  ["Top.paper.Vec"; "Top.paper.nat"; "Top.paper.depInd"]).

Run TemplateProgram (genParam indTransEnv false true "depInd_recs").

Module DedM.
(*
Notation nat_R := Top_paper_nat_pmtcty_RR0.
Notation Vec_R := Top_paper_Vec_pmtcty_RR0.
Notation depInd_R := Top_paper_depInd_pmtcty_RR0.
Notation depInd_indicesReq := Top_paper_depInd_pmtcty_RR0_indices.
Print Top_paper_depInd_pmtcty_RR0.
Eval simpl in depInd_recs_pmtcty_RR.

Top_paper_depInd_pmtcty_RR0_indices.
*)
Notation nat_R := Ded.nat_R.
Notation Vec_R := DedV.Vec_R.
Notation O_R := Ded.O_R.

Inductive depInd_indicesReq (n n' : nat)  (n_R : nat_R n n') (v : Vec nat n) (v' : Vec nat n')
(v_R : Vec_R nat nat nat_R n n' n_R v v'): forall (n_Ri: nat_R n n') (v_Ri: Vec_R nat nat nat_R n n' n_Ri v v'), Prop :=
depInd_refl :  depInd_indicesReq n n' n_R v v' v_R n_R v_R.

Require Import SquiggleEq.UsefulTypes.

Arguments transport {T} {a} {b} P eq pa.

Fixpoint depInd_R (n n' : nat) (n_R : nat_R n n') (v : Vec nat n) (v' : Vec nat n') 
  (b_R : Vec_R nat nat nat_R n n' n_R v v') (m : depInd n v) (m' : depInd n' v'): Prop :=
(match m,m' with
| dind vv, dind vv' => λ (n_R0 : nat_R O O) (v_R0 : Vec_R nat nat nat_R O O n_R0 vv vv'),
  {vv_R : Vec_R nat nat nat_R O O O_R vv vv' &
       {p: n_R0 = O_R & transport (fun (n_R2: nat_R O O) => Vec_R nat nat nat_R O O n_R2 vv vv') p v_R0 = vv_R}}
end) n_R b_R.

Module Simple.
Fixpoint depInd_R (n n' : nat) (n_R : nat_R n n') (v : Vec nat n) (v' : Vec nat n') 
(v_R : Vec_R nat nat nat_R n n' n_R v v') (m : depInd n v) (m' : depInd n' v'): Prop :=
(match m,m' with
| dind vv, dind vv' => λ (n_R : nat_R O O) (v_R : Vec_R nat nat nat_R O O n_R vv vv'),
  {vv_R : Vec_R nat nat nat_R O O O_R vv vv' & depInd_indicesReq O O O_R vv vv' vv_R n_R v_R}
end) n_R v_R.
End Simple.

Print depInd_rect.


(*
Fixpoint depInd_R
 (n n₂ : nat) (n_R : nat_R n n') (b : Vec nat n) 
(b' : Vec nat n') (b_R : Vec_R nat nat nat_R n n' n_R b b')
(m : depInd n b) (m' : depInd n' b') {struct m} : Prop :=
  (match m,m'
  with
  | dind n0 v, dind n'0 v' =>
          fun (n_R0 : nat_R n0 n'0) (b_R0 : Vec_R nat nat nat_R n0 n'0 n_R0 v v') =>
          {n_R1 : nat_R n0 n'0 &
          {v_R : Vec_R nat nat nat_R n0 n'0 n_R1 v v' &
          depInd_indicesReq n0 n'0 n_R1 v v' v_R n_R0 b_R0}}
  end) n_R b_R.
*)
(*
fix
Top_paper_depInd_pmtcty_RR0 (n n' : nat) 
                             (n_R : nat_R n n')
                             (v : Vec nat n)
                             (v' : Vec nat n')
                             (v_R : Vec_R nat nat nat_R n n'
                                      n_R v v')
                             (H : depInd n v)
                             (H0 : depInd n' v') {struct H} :
  Prop :=
  match
    H in (depInd n0 v0)
    return
      (forall n_R0 : nat_R n0 n',
       Vec_R nat nat nat_R n0 n' n_R0 v0 v' -> Prop)
  with
  | dind nn vv =>
      match
        H0 in (depInd n'0 v'0)
        return
          (forall n_R0 : nat_R nn n'0,
           Vec_R nat nat nat_R nn n'0 n_R0 vv v'0 -> Prop)
      with
      | dind nn' vv' =>
          fun (n_R0 : nat_R nn nn')
            (v_R0 : Vec_R nat nat nat_R nn nn' n_R0 vv vv')
          =>
          {nn_R : nat_R nn nn' &
          {vv_R : Vec_R nat nat nat_R nn nn' nn_R vv vv' &
          depInd_indicesReq nn nn' nn_R vv vv' vv_R n_R0
            v_R0}}
*)
End DedM.
