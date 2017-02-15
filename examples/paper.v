

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

Print Vec_rect.

(*
Inductive multInd (A I : Set) (B: I-> Set) (f: A-> I) (g: forall i, B i): forall (i:I) (b:B i), Set :=
mind : forall (a:A), multInd A I B f g (f a) (g (f a)).
*)

Inductive multInd : forall (n:nat) (b:Vec nat n), Set :=
mind : multInd O nilV.


Run TemplateProgram (genParamInd [] true true "Top.paper.Vec").
Run TemplateProgram (genParamInd [] true true "Top.paper.multInd").

Print Top_paper_multInd_pmtcty_RR0_indices.




(*
Run TemplateProgram (mkIndEnv "indTransEnv" ["Top.paper.Vec"; "Top.paper.nat"]).
*)


Module DedM.
Notation nat_R := Top_paper_nat_pmtcty_RR0.
Notation Vec_R := Top_paper_Vec_pmtcty_RR0.
Notation multInd_R := Top_paper_multInd_pmtcty_RR0.
Notation multInd_indicesReq := Top_paper_multInd_pmtcty_RR0_indices.
Print Top_paper_multInd_pmtcty_RR0.
Top_paper_multInd_pmtcty_RR0_indices
Notation nat_R := Ded.nat_R.
Notation Vec_R := DedV.Vec_R.

Inductive multInd_indicesReq (n n₂ : nat) 
(n_R : nat_R n n₂) (b : Vec nat n)
(b₂ : Vec nat n₂)
(b_R : Vec_R nat nat nat_R n n₂ n_R b b₂)
  : forall (n_R : nat_R n n₂)
    (vr: Vec_R nat nat nat_R n n₂ n_R b b₂), Prop :=
multInd_refl :  multInd_indicesReq n n₂ n_R b b₂ b_R n_R b_R.

End DedM.
    


