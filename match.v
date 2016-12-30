Require Import Coq.Classes.DecidableClass.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import SquiggleEq.export.
Require Import SquiggleEq.UsefulTypes.
Require Import SquiggleEq.list.
Require Import SquiggleEq.LibTactics.
Require Import SquiggleEq.tactics.
Require Import SquiggleEq.AssociationList.
Require Import ExtLib.Structures.Monads.
Require Import common.
Require Import Trecord.

Fixpoint natElim (n  : nat) : Type:=
match n with
| 0 => bool
| S n => unit + (natElim n)
end.


Parametricity Recursive unit.
Parametricity Recursive sum.

Print nat_R.

(* Print nat_R
Changed Set to Prop
*)
Inductive nat_R : nat -> nat -> (* Set *) Prop :=
nat_R_O_R : nat_R 0 0 | nat_R_S_R : forall H H0 : nat, nat_R H H0 -> nat_R (S H) (S H0).

(*
Parametricity Recursive natElim.
Print natElim_R.
(* copied below *)
*)

(* Fails because nat_R is now in Prop
Definition natElim_R := 
let fix_natElim_1 :=
  fix natElim (n : nat) : Type :=
    match n with
    | 0 => bool
    | S n0 => (unit + natElim n0)%type
    end in
let fix_natElim_2 :=
  fix natElim (n : nat) : Type :=
    match n with
    | 0 => bool
    | S n0 => (unit + natElim n0)%type
    end in
fix natElim_R (n₁ n₂ : nat) (n_R : nat_R n₁ n₂) {struct n_R} :
  fix_natElim_1 n₁ -> fix_natElim_2 n₂ -> Type :=
  match n_R in (nat_R n₁0 n₂0) return (fix_natElim_1 n₁0 -> fix_natElim_2 n₂0 -> Type) with
  | nat_R_O_R => bool_R
  | nat_R_S_R n₁0 n₂0 n_R0 =>
      sum_R unit unit unit_R (fix_natElim_1 n₁0) (fix_natElim_2 n₂0)
        (natElim_R n₁0 n₂0 n_R0)
  end.
*)


Print list.


Inductive list (A : Set (* Type fails *)) 
  : Set :=  nil : list A | cons : A -> list A -> list A.

Fixpoint listElim (A:Set )(l  : list A) : Type:=
match l with
| nil _ => unit
| cons _ _ tl => @sum A (listElim A tl)
end.


Parametricity Recursive unit.
Parametricity Recursive sum.
(*Parametricity Recursive list.
 Parametricity Recursive listElim. 

Print listElim_R.
(* copied below *)
*)

Inductive list_R (A₁ A₂ : Set) (A_R : A₁ -> A₂ -> Set) : list A₁ -> list A₂ -> Prop :=
    list_R_nil_R : list_R A₁ A₂ A_R (nil A₁) (nil A₂)
  | list_R_cons_R : forall (H : A₁) (H0 : A₂),
                    A_R H H0 ->
                    forall (H1 : list A₁) (H2 : list A₂),
                    list_R A₁ A₂ A_R H1 H2 ->
                    list_R A₁ A₂ A_R (cons A₁ H H1) (cons A₂ H0 H2).

(* Fails because list_R is now in Prop
Definition listElim_R := 
let fix_listElim_1 :=
  fix listElim (A : Set) (l : list A) {struct l} : Type :=
    match l with
    | nil _ => unit
    | cons _ _ tl => (A + listElim A tl)%type
    end in
let fix_listElim_2 :=
  fix listElim (A : Set) (l : list A) {struct l} : Type :=
    match l with
    | nil _ => unit
    | cons _ _ tl => (A + listElim A tl)%type
    end in
fix
listElim_R (A₁ A₂ : Set) (A_R : A₁ -> A₂ -> Set) (l₁ : list A₁) 
           (l₂ : list A₂) (l_R : list_R A₁ A₂ A_R l₁ l₂) {struct l_R} :
  fix_listElim_1 A₁ l₁ -> fix_listElim_2 A₂ l₂ -> Type :=
  match
    l_R in (list_R _ _ _ l₁0 l₂0)
    return (fix_listElim_1 A₁ l₁0 -> fix_listElim_2 A₂ l₂0 -> Type)
  with
  | list_R_nil_R _ _ _ => unit_R
  | list_R_cons_R _ _ _ _ _ _ tl₁ tl₂ tl_R =>
      sum_R A₁ A₂ A_R (fix_listElim_1 A₁ tl₁) (fix_listElim_2 A₂ tl₂)
        (listElim_R A₁ A₂ A_R tl₁ tl₂ tl_R)
  end.
*)

Fixpoint list_RR (A₁ A₂ : Set) (A_R : A₁ -> A₂ -> Prop) (l1 : list A₁) (l2 : list A₂)
  {struct l1} : Prop :=
match (l1, l2) with
| (nil _, nil _) => True
| (cons _ h1 tl1, cons _ h2 tl2) => @sigT (A_R h1 h2) (fun _ => list_RR _ _ A_R tl1 tl2)
| ( _, _) => False
end.

(* because of template polymorphism, * for /\ works *)

Fixpoint listElim_RR  (A₁ A₂ : Set) (A_R : A₁ -> A₂ -> Prop) (l1 : list A₁) (l2 : list A₂)
  (l_R : list_RR A₁ A₂ A_R l1 l2) {struct l1} (* not l_R *)
 : (listElim A₁ l1) -> (listElim A₂ l2) -> Type :=
let reT := fun l1 l2 => list_RR A₁ A₂ A_R l1 l2 -> (listElim A₁ l1) -> (listElim A₂ l2) -> Type in
(match l1 return reT l1 l2 with
| nil _ => 
  match l2 return reT (nil _) l2 with
  | nil _ => fun l_R => unit_R
  | cons _ _ _ => fun l_R => False_rect _ l_R
  end
| cons _ h1 tl1 =>
  match l2 return reT (cons _ h1 tl1) l2 with
  | nil _ => fun l_R => False_rect _ l_R
  | cons _ h2 tl2 => fun l_R => 
      let tl_R := projT2 l_R in
      @sum_R _ _ A_R
      _ _ (listElim_RR _ _ A_R _ _ tl_R)
  end
end) l_R.

Require Import templateCoqMisc.
Require Import Template.Ast.

Print eq_R.
(* Should we have a set version as well? *)
(* The return type of eq is a Prop... So we can hust return fun _ _ .. => True *)

Definition eq_RR (A₁ A₂ : Type) (A_R : A₁ -> A₂ -> Type) (x₁ : A₁) (x₂ : A₂) 
(x_R : A_R x₁ x₂) : forall (y₁ : A₁) (y₂ : A₂), A_R y₁ y₂ -> x₁ = y₁ -> x₂ = y₂ -> Prop.
intros ? ?.
(*
rename H into y₁.
rename H0 into y₂. *)
intros ary H1eq H2eq.
destruct H1eq.
destruct H2eq.
exact True.
Defined.


Inductive Vec  (C:Set) : nat -> Type :=
| vnil : Vec C 0
| vcons : forall (n: nat), C -> Vec C n -> Vec C (S n).


Fixpoint nat_RR (n1 n2: nat) 
  {struct n1} : Prop :=
match (n1, n2) with
| (0, 0) => True
| (S h1, S h2) => nat_RR h1 h2
| ( _, _) => False
end.

(*
Definition transportRev {T : Type} {a b : T} {P : T -> Type}
   (p : a = b) (pb : P b) : P a
:= transport (eq_sym p) pb.
*)


Fixpoint vAppend  {C:Set} {n m : nat} 
  (vl : Vec C n) (vr : Vec C m): Vec C (n+m) :=
match vl in Vec _ n return Vec C (n + m) with
| vnil _ =>  vr
| vcons _ n' hl tl => 
    (vcons _ _ hl (vAppend tl vr))
end.

Run TemplateProgram (printTerm "vAppend").

Parametricity Recursive vAppend.

Print Vec_R.
Check vAppend_R.


Fixpoint Vec_RR (C1 C2 : Set) (C_R : C1 -> C2 -> Prop)
  (n1 n2 : nat) (n_R : nat_RR n1 n2)  (v1 : Vec C1 n1) (v2: Vec C2 n2) {struct v1} : Prop:= 
let reT := fun n1 n2 => nat_RR n1 n2 -> (* only the indices change. so only they appear here*) 
  Prop in 
(* for indexed inductives, in is needed before return to bring the index in scope *)
(match v1 in (Vec _ n1) return reT n1 n2 with
| vnil _ => 
  match v2 in (Vec _ n2) return reT 0 n2 with
  | vnil _ => fun _ => True
  | vcons _ _ _ _ => fun _ => False
  end
| vcons _ n1 h1 tl1 =>
  match v2 in (Vec _ n2) return reT (S n1) n2 with
  | vnil _ => fun _ => False
  | vcons _ n2 h2 tl2 => fun n_R =>
    let n_R := n_R (* no sig *) in
     (C_R h1 h2) /\ (Vec_RR _ _ C_R n1 n2 n_R tl1 tl2)
  end
end) n_R.

Print Nat.add.
Print Coq_o_Init_o_Nat_o_add_R.

Definition S_RR (n1 n2 : nat) 
  (n_R : nat_RR n1 n2) : nat_RR (S n1) (S n2) :=
n_R.


Fixpoint add_RR (n1 n2 : nat) (n_R : nat_RR n1 n2) (m1 m2 : nat) (m_R : nat_RR m1 m2):
nat_RR (n1 + m1) (n2 + m2) :=
let reT := fun n1 n2 => nat_RR n1 n2 -> nat_RR (n1 + m1) (n2 + m2) in
(match n1 return reT n1 n2 with
| 0 => 
  match n2 return reT 0 n2 with
  | 0 => fun _ => m_R
  | S _ => fun n_R => False_rect _ n_R
  end
| S p1 =>
  match n2 return reT (S p1) n2 with
  | 0 => fun n_R => False_rect _ n_R
  | S p2 => fun n_R => S_RR _ _ (add_RR p1 p2 n_R m1 m2 m_R)
  end
end) n_R.
Print Vec_R_vcons_R.

Definition vcons_RR {C₁ C₂ : Set} {C_R : C₁ -> C₂ -> Prop}
(n₁ n₂ : nat) (n_R : nat_RR n₁ n₂)
 (H : C₁) (H0 : C₂) (c_R: C_R H H0)
 (H1 : Vec C₁ n₁) (H2 : Vec C₂ n₂)
 (v_R : Vec_RR C₁ C₂ C_R n₁ n₂ n_R H1 H2):
  Vec_RR C₁ C₂ C_R (S n₁) (S n₂) (S_RR n₁ n₂ n_R)
  (vcons C₁ n₁ H H1) (vcons C₂ n₂ H0 H2).
Proof.
simpl. split; assumption.
Defined.

Fixpoint vAppend_RR {C₁ C₂ : Set} {C_R : C₁ -> C₂ -> Prop} (n₁ n₂ : nat) 
   (n_R : nat_RR n₁ n₂) (m₁ m₂ : nat) (m_R : nat_RR m₁ m₂)
   (vl₁ : Vec C₁ n₁) (vl₂ : Vec C₂ n₂)
   (vl_R : Vec_RR C₁ C₂ C_R n₁ n₂ n_R vl₁ vl₂)
   (vr₁ : Vec C₁ m₁) (vr₂ : Vec C₂ m₂)
   (vr_R : Vec_RR C₁ C₂ C_R m₁ m₂ m_R vr₁ vr₂) {struct vl₁ }:
    Vec_RR C₁ C₂ C_R (n₁ + m₁) (n₂ + m₂) (add_RR n₁ n₂ n_R m₁ m₂ m_R)
         (vAppend vl₁ vr₁) (vAppend vl₂ vr₂) :=
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
    let hl_R := proj1 v_R in
    let tl_R := proj2 v_R in
    (vcons_RR _ _ _ _ _ hl_R _ _ (vAppend_RR _ _ _ _ _ _ _ _  tl_R  _ _ vr_R))
  end
end) n_R vl_R.


Inductive IHaveUndecidalbeEq : Set :=
injFun : (nat->nat) -> IHaveUndecidalbeEq.

(*
Parametricity Recursive IHaveUndecidalbeEq.
Print IHaveUndecidalbeEq_R.
*)

Inductive IHaveUndecidalbeEq_R : IHaveUndecidalbeEq -> IHaveUndecidalbeEq -> Prop :=
 injFun_R : forall f1 f2 : nat -> nat,
   (forall n1 n2 : nat,
          n1 = n2 -> (f1 n1) = (f2 n2)) ->
             IHaveUndecidalbeEq_R (injFun f1) (injFun f2).


(* even after assuming function extensionality, is this provable? *)
Lemma UIP (f:IHaveUndecidalbeEq) (p1 p2 : IHaveUndecidalbeEq_R f f) :
p1=p2.
Proof using.
  Fail induction p1.
Abort.

Inductive IHaveUndecidalbeEq_R2 : IHaveUndecidalbeEq -> IHaveUndecidalbeEq -> Prop :=
 injFun_R2 : forall f1 f2 : nat -> nat, (f1= f2)
             -> IHaveUndecidalbeEq_R2 (injFun f1) (injFun f2).

Inductive IHaveUndecidalbeEq_R3  (f: IHaveUndecidalbeEq): IHaveUndecidalbeEq -> Prop :=
 injFun_R3 :  IHaveUndecidalbeEq_R3 f f.
 
Require Import Contractible.
 
Definition iso23 f1 f2 (p: IHaveUndecidalbeEq_R2 f1 f2) :   IHaveUndecidalbeEq_R3 f1 f2.
Proof using.
  destruct p. induction H.
  apply injFun_R3.
Defined.

Definition iso32 f1 f2 (p: IHaveUndecidalbeEq_R3 f1 f2) :   IHaveUndecidalbeEq_R2 f1 f2.
Proof using.
  destruct p.
  destruct f1.
  apply injFun_R2. reflexivity.
Defined.

Lemma iso232 f1 f2:
forall a : IHaveUndecidalbeEq_R3 f1 f2, iso23 f1 f2 (iso32 f1 f2 a) = a.
Proof using.
  intros ?. unfold iso32, iso23. simpl.
  destruct a. destruct f1. reflexivity.
Qed.

Lemma preserveContractible23 f (c1 : Contractible (IHaveUndecidalbeEq_R2 f f)):
  Contractible (IHaveUndecidalbeEq_R3 f f).
Proof using.
  revert c1.
  apply UP_iso with (AtoB := iso23 f f) (BtoA := iso32 f f).
  apply iso232.
Qed.

Section Iso12Feq.

Hypothesis feqNatNat : forall (f g : nat -> nat),
  (forall n, f n = g n) -> f=g.
  
Lemma feqNatNat2 : forall (f g : nat -> nat),
  (forall n1 n2, n1=n2 -> f n1 = g n2) -> f=g.
Proof.
  intros.
  apply feqNatNat. intros n.
  specialize (H n n eq_refl). assumption.
Qed.


Definition iso12 f1 f2 (p: IHaveUndecidalbeEq_R f1 f2) :   IHaveUndecidalbeEq_R2 f1 f2.
Proof.
  destruct p.
  apply feqNatNat2 in H.
  apply injFun_R2. assumption.
Defined.

Definition iso21 f1 f2 (p: IHaveUndecidalbeEq_R2 f1 f2) :   IHaveUndecidalbeEq_R f1 f2.
Proof using.
  destruct p.
  apply injFun_R.
  intros.  subst. reflexivity.
Defined.

Lemma iso121 f1 f2:
forall a : IHaveUndecidalbeEq_R2 f1 f2, iso12 f1 f2 (iso21 f1 f2 a) = a.
Proof using.
  intros ?. unfold iso21, iso12. simpl.
  destruct a. simpl.
  (* in Hott, this would be compute because function extensionality is not an axiom.
  If Contractible (IHaveUndecidalbeEq_R2 f1 f2) is not provable in 
  HoTT, a more powerful theory, it is not provable in Coq. *) 
  Fail induction e.
  (* destruct f1. reflexivity. *)
Abort.

(* Motivalte by explaining the problems caused by indexing, unprovability of UIP *)

(*
Lemma preserveContractible23 f (c1 : Contractible (IHaveUndecidalbeEq_R2 f f)):
  Contractible (IHaveUndecidalbeEq_R3 f f).
Proof using.
  revert c1.
  apply UP_iso with (AtoB := iso23 f f) (BtoA := iso32 f f).
  apply iso232.
Qed.
*)



