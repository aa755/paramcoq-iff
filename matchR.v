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

Definition isZero (n  : nat) : bool :=
negb(
match n with
| 0 => true
| S _ => false
end).


Parametricity Recursive isZero.
(* Print isZero_R. *)


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

Run TemplateProgram (printTerm "isZero").

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

Inductive Vec2  (C:Set) : nat -> Type :=
| vnil2 : Vec2 C 0
| vcons2 : forall (n: nat), C -> Vec2 C n -> Vec2 C (n+1) (* not struct on n*).

Open Scope nat_scope.

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


Definition vAppend2  {C:Set} {m : nat} (cdef: C)
   (vr : Vec C m):  C :=
match vAppend vr vr as vapx in Vec _ n return C with
| vnil _ =>  cdef
| vcons _ n' hl tl => hl
end.
(*
Parametricity Recursive vAppend2.
Print vAppend2_R.
vAppend2_R = 
fun (C₁ C₂ : Set) (C_R : C₁ -> C₂ -> Set) (m₁ m₂ : nat) (m_R : common.nat_R m₁ m₂)
  (cdef₁ : C₁) (cdef₂ : C₂) (cdef_R : C_R cdef₁ cdef₂) (vr₁ : Vec C₁ m₁) 
  (vr₂ : Vec C₂ m₂) (vr_R : Vec_R C₁ C₂ C_R m₁ m₂ m_R vr₁ vr₂) =>
match
  vAppend_R C₁ C₂ C_R m₁ m₂ m_R m₁ m₂ m_R vr₁ vr₂ vr_R vr₁ vr₂ vr_R in
  (Vec_R _ _ _ n₁ n₂ n_R x₁ x₂)
  return
    (C_R match x₁ with
         | vnil _ => cdef₁
         | vcons _ _ hl _ => hl
         end match x₂ with
             | vnil _ => cdef₂
             | vcons _ _ hl _ => hl
             end)
with
| Vec_R_vnil_R _ _ _ => cdef_R
| Vec_R_vcons_R _ _ _ _ _ _ _ _ hl_R _ _ _ => hl_R
end
     : forall (C₁ C₂ : Set) (C_R : C₁ -> C₂ -> Set) (m₁ m₂ : nat) 
         (m_R : common.nat_R m₁ m₂) (cdef₁ : C₁) (cdef₂ : C₂),
       C_R cdef₁ cdef₂ ->
       forall (vr₁ : Vec C₁ m₁) (vr₂ : Vec C₂ m₂),
       Vec_R C₁ C₂ C_R m₁ m₂ m_R vr₁ vr₂ -> C_R (vAppend2 cdef₁ vr₁) (vAppend2 cdef₂ vr₂)
*)
(*
Run TemplateProgram (printTerm "vAppend").
Run TemplateProgram (duplicateDefn "vAppend" "vAppendss").
Check (eq_refl: @vAppend=vAppendss).
*)

(*
Parametricity Recursive vAppend.

Print Vec_R.
Check vAppend_R.
*)

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


(* non n_R argument *)
Fixpoint Vec_RR2 (C1 C2 : Set) (C_R : C1 -> C2 -> Prop)
  (n1 n2 : nat)  (v1 : Vec C1 n1) (v2: Vec C2 n2) {struct v1} : Prop:= 
let reT :=  fun _ _ => Prop in 
(* for indexed inductives, in is needed before return to bring the index in scope *)
(match v1 in (Vec _ n1) return reT n1 n2 with
| vnil _ => 
  match v2 in (Vec _ n2) return reT 0 n2 with
  | vnil _ => True
  | vcons _ _ _ _ => False
  end
| vcons _ n1 h1 tl1 =>
  match v2 in (Vec _ n2) return reT (S n1) n2 with
  | vnil _ =>  False
  | vcons _ n2 h2 tl2 => 
     (C_R h1 h2) /\ (Vec_RR2 _ _ C_R n1 n2 tl1 tl2)
  end
end).

Definition Vec_RR3 := 
fix
ReflParam_matchR_Vec_RR0 (C C₂ : Set) (C_R : (fun H H0 : Set => H -> H0 -> Prop) C C₂)
                         (H H0 : nat) (_ (* unused *): nat_RR H H0) 
                         (H2 : Vec C H) (H3 : Vec C₂ H0) {struct H2} : Prop :=
  match H2 with
  | vnil _ => match H3 with
              | vnil _ => True
              | vcons _ _ _ _ => False
              end
  | vcons _ n x x0 =>
      match H3 with
      | vnil _ => False
      | vcons _ n₂ x1 x2 =>
          {n_R : nat_RR n n₂ &
          {_ : C_R x x1 & {_ : ReflParam_matchR_Vec_RR0 C C₂ C_R n n₂ n_R x0 x2 & True}}}
      end
  end.

(*
Print Nat.add.
Print Coq_o_Init_o_Nat_o_add_R.
*)

Definition S_RR (n1 n2 : nat) 
  (n_R : nat_RR n1 n2) : nat_RR (S n1) (S n2) :=
n_R.

Definition O_RR : nat_RR O O := I.


(* Parametricity Recursive Vec. *)
(* nat_R changed to nat_RR, Set changed to Prop *)
Inductive Vec_R (C₁ C₂ : Set) (C_R : C₁ -> C₂ -> Prop)
  : forall H H0 : nat, nat_RR H H0 -> Vec C₁ H -> Vec C₂ H0 -> Prop :=
  |  Vec_R_vnil_R : Vec_R C₁ C₂ C_R 0 0 O_RR (vnil C₁) (vnil C₂)
  | Vec_R_vcons_R : forall (n₁ n₂ : nat) (n_R : nat_RR n₁ n₂) (H : C₁) (H0 : C₂),
                    C_R H H0 ->
                    forall (H1 : Vec C₁ n₁) (H2 : Vec C₂ n₂),
                    Vec_R C₁ C₂ C_R n₁ n₂ n_R H1 H2 ->
                    Vec_R C₁ C₂ C_R (S n₁) (S n₂) (S_RR n₁ n₂ n_R)
                      (vcons C₁ n₁ H H1) (vcons C₂ n₂ H0 H2).

Definition fromNewV (C C₂ : Set) (C_R : C -> C₂ -> Prop)
(n1 n2: nat) (nr : nat_RR n1 n2) v1 v2
  (vr : Vec_RR3 _ _ C_R n1 n2 nr v1 v2) :
  Vec_R _ _ C_R n1 n2 nr v1 v2.
induction v1;induction v2; simpl in *.
- (* nr is arbitrary because it is an unused argument in Vec_RR *)
Abort.

Fixpoint Vec2_RR (C1 C2 : Set) (C_R : C1 -> C2 -> Prop)
  (n1 n2 : nat) (_ : nat_RR n1 n2)  (v1 : Vec2 C1 n1) (v2: Vec2 C2 n2) {struct v1} : Prop
   :=
(match v1 with
| vnil2 _ => 
  match v2 with
  | vnil2 _ => True
  | vcons2 _ _ _ _ => False
  end
| vcons2 _ n1 h1 tl1 =>
  match v2 with
  | vnil2 _ => False
  | vcons2 _ n2 h2 tl2 =>
     (C_R h1 h2) /\ (sig (fun nr => Vec2_RR _ _ C_R n1 n2 nr tl1 tl2))
  end
end).




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
(* Print Vec_R_vcons_R. *)

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

(* summary : need indices of:
  1) the type of the discriminee. put a cast around discriminee in template-coq?
  2) for each constructor, a way to get the indices of the return type 
    (or just the return type) from the arguments.
    take a list of types of constructors, in order of the constructors.
    convert the PIs to Lams in the type and then apply the arguments and maybe
    beta reduce. Beta reduction is not necessary though.
*)


Definition vAppend2_RR (C₁ C₂ : Set) (C_R : C₁ -> C₂ -> Prop) (m₁ m₂ : nat) 
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
      | vcons _ _ hl _ => fun _ vr =>
        let hl_R := proj1 vr in hl_R
      end

end (add_RR m₁ m₂ m_R m₁ m₂ m_R) 
  (vAppend_RR _ _ _ _ _ _ _ _ vr _ _ vr)
). 

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

End Iso12Feq.

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


(** the Set version of IWT *)
Section IWTS.

Variable A:Set.

Variable I:Set.

(* each member of B denotes one recursive occurrence in the constructor.
Only the cardinality matters *)
Variable B: A -> Set.

(* the index for the conclusion *)
Variable AI: A -> I.


(* the index for each recursive occurrence in B *)
Variable BI: forall a, B a -> I.


Inductive IWT : I ->Set :=
iwt : forall (a:A), (forall (b:B a), IWT (BI a b)) -> IWT (AI a).


Definition getA (i: I) (t : IWT i) : A :=
match t with
iwt a  _ => a
end.


End IWTS.
Check iwt.


(* Parametricity Recursive IWT. *)

Inductive IWT_R (A₁ A₂ : Set) (A_R : A₁ -> A₂ -> Set) (I₁ I₂ : Set) (I_R : I₁ -> I₂ -> Set)
(B₁ : A₁ -> Set) (B₂ : A₂ -> Set)
(B_R : forall (H : A₁) (H0 : A₂), A_R H H0 -> B₁ H -> B₂ H0 -> Set) 
(AI₁ : A₁ -> I₁) (AI₂ : A₂ -> I₂)
(AI_R : forall (H : A₁) (H0 : A₂), A_R H H0 -> I_R (AI₁ H) (AI₂ H0))
(BI₁ : forall a : A₁, B₁ a -> I₁) (BI₂ : forall a : A₂, B₂ a -> I₂)
(BI_R : forall (a₁ : A₁) (a₂ : A₂) (a_R : A_R a₁ a₂) (H : B₁ a₁) (H0 : B₂ a₂),
        B_R a₁ a₂ a_R H H0 -> I_R (BI₁ a₁ H) (BI₂ a₂ H0))
  : forall (H : I₁) (H0 : I₂),
    I_R H H0 -> IWT A₁ I₁ B₁ AI₁ BI₁ H -> IWT A₂ I₂ B₂ AI₂ BI₂ H0 -> Prop :=
    IWT_R_iwt_R : forall (a₁ : A₁) (a₂ : A₂) (a_R : A_R a₁ a₂)
                    (H : forall b : B₁ a₁, IWT A₁ I₁ B₁ AI₁ BI₁ (BI₁ a₁ b))
                    (H0 : forall b : B₂ a₂, IWT A₂ I₂ B₂ AI₂ BI₂ (BI₂ a₂ b)),
                  (forall (b₁ : B₁ a₁) (b₂ : B₂ a₂) (b_R : B_R a₁ a₂ a_R b₁ b₂),
                   IWT_R A₁ A₂ A_R I₁ I₂ I_R B₁ B₂ B_R AI₁ AI₂ AI_R BI₁ BI₂ BI_R 
                     (BI₁ a₁ b₁) (BI₂ a₂ b₂) (BI_R a₁ a₂ a_R b₁ b₂ b_R) 
                     (H b₁) (H0 b₂)) ->
                  IWT_R A₁ A₂ A_R I₁ I₂ I_R B₁ B₂ B_R AI₁ AI₂ AI_R BI₁ BI₂ BI_R 
                    (AI₁ a₁) (AI₂ a₂) (AI_R a₁ a₂ a_R) (iwt A₁ I₁ B₁ AI₁ BI₁ a₁ H)
                    (iwt A₂ I₂ B₂ AI₂ BI₂ a₂ H0).

Definition IWT_RC :=
      fix
       ReflParam_matchR_IWT_RR0 (A A₂ : Set) (A_R : A -> A₂ -> Prop) 
                                (I I₂ : Set) (I_R : I -> I₂ -> Prop) 
                                (B : A -> Set) (B₂ : A₂ -> Set)
                                (B_R : forall (a1 : A) (a2 : A₂),
                                       A_R a1 a2 -> B a1 -> B₂ a2 -> Prop) 
                                (AI : A -> I) (AI₂ : A₂ -> I₂)
                                (AI_R : forall (a1 : A) (a2 : A₂),
                                        A_R a1 a2 -> I_R (AI a1) (AI₂ a2))
                                (BI : forall a : A, B a -> I)
                                (BI₂ : forall a₂ : A₂, B₂ a₂ -> I₂)
                                (BI_R : forall (a1 : A) (a2 : A₂) 
                                          (p : A_R a1 a2) (a3 : B a1) 
                                          (a4 : B₂ a2),
                                        B_R a1 a2 p a3 a4 -> I_R (BI a1 a3) (BI₂ a2 a4))
                                (H : I) (H0 : I₂) (H1 : I_R H H0) 
                                (H2 : IWT A I B AI BI H) (H3 : IWT A₂ I₂ B₂ AI₂ BI₂ H0)
                                {struct H2} : Prop :=
          let reT i1 i2 := forall (ir : I_R i1 i2), Prop in
         (match H2 as iwt1 in IWT _ _ _ _ _ i1 return reT i1 H0 
         with
         | iwt _ _ _ _ _ a x =>
             match H3 as iwt2 in IWT _ _ _ _ _ i2 return reT (AI a) i2
             with
             | iwt _ _ _ _ _ a₂ x0 =>
              fun ir =>
                 {a_R : A_R a a₂ &
                 {_
                 : forall (a1 : B a) (a2 : B₂ a₂) (p : B_R a a₂ a_R a1 a2),
                   ReflParam_matchR_IWT_RR0 A A₂ A_R I I₂ I_R B B₂ B_R AI AI₂ AI_R BI BI₂
                     BI_R (BI a a1) (BI₂ a₂ a2) (BI_R a a₂ a_R a1 a2 p) 
                     (x a1) (x0 a2) & (ir=(AI_R a a₂ a_R))}}
             end
         end) H1.

Section ToFrom.

Variables (A₁ A₂ : Set) (A_R : A₁ -> A₂ -> Prop) (I₁ I₂ : Set) (I_R : I₁ -> I₂ -> Prop)
(B₁ : A₁ -> Set) (B₂ : A₂ -> Set)
(B_R : forall (H : A₁) (H0 : A₂), A_R H H0 -> B₁ H -> B₂ H0 -> Prop) 
(AI₁ : A₁ -> I₁) (AI₂ : A₂ -> I₂)
(AI_R : forall (H : A₁) (H0 : A₂), A_R H H0 -> I_R (AI₁ H) (AI₂ H0))
(BI₁ : forall a : A₁, B₁ a -> I₁) (BI₂ : forall a : A₂, B₂ a -> I₂)
(BI_R : forall (a₁ : A₁) (a₂ : A₂) (a_R : A_R a₁ a₂) (H : B₁ a₁) (H0 : B₂ a₂),
        B_R a₁ a₂ a_R H H0 -> I_R (BI₁ a₁ H) (BI₂ a₂ H0))
(i1 : I₁) (i2 : I₂) (ir : I_R i1 i2) 
(i1wt : IWT A₁ I₁ B₁ AI₁ BI₁ i1) (i2wt : IWT A₂ I₂ B₂ AI₂ BI₂ i2).

Definition toNew 
  (p: IWT_R _ _ A_R _ _ I_R _ _ B_R _ _ AI_R _ _ BI_R _ _ ir i1wt i2wt): 
  IWT_RC  _ _ A_R _ _ I_R _ _ B_R _ _ AI_R _ _ BI_R _ _ ir i1wt i2wt.
Proof using.
  induction p.
  simpl. eexists. eexists. apply H2. refl.
Defined.


Definition fromNew 
  (p: IWT_RC _ _ A_R _ _ I_R _ _ B_R _ _ AI_R _ _ BI_R _ _ ir i1wt i2wt): 
  IWT_R  _ _ A_R _ _ I_R _ _ B_R _ _ AI_R _ _ BI_R _ _ ir i1wt i2wt.
Proof using.
 rename i1wt into i1wtt. (* section vars don't go away even after destructing *)
 rename i2wt into i2wtt.
 revert p.
 revert i2wtt.
 revert ir.
 revert i2.
 induction i1wtt as [a1 f Hind].
 intros ? ? ?. destruct i2wtt. simpl in *.
 intros p. destruct p as [ar pp].
 destruct pp as [pp pp2].
 subst.
 apply IWT_R_iwt_R.
 Fail exact pp.
 intros.
 apply Hind.
 apply pp.
Defined.


Lemma fromNew_toNew_id : forall p, fromNew (toNew p) = p.
Proof using.
  intros p.
  Fail induction p.
(*
Abstracting over the terms "H", "H0", "ir", "H2" and "H3" leads to a term
fun (H1 : I₁) (H4 : I₂) (ir0 : I_R H1 H4) (H5 : IWT A₁ I₁ B₁ AI₁ BI₁ H1)
  (H6 : IWT A₂ I₂ B₂ AI₂ BI₂ H4) => fromNew (toNew p) = p
which is ill-typed.
*)
Abort.

End ToFrom.

Section Iso.

Lemma toNew_fromNew_id
(A₁ A₂ : Set) (A_R : A₁ -> A₂ -> Prop) (I₁ I₂ : Set) (I_R : I₁ -> I₂ -> Prop)
(B₁ : A₁ -> Set) (B₂ : A₂ -> Set)
(B_R : forall (H : A₁) (H0 : A₂), A_R H H0 -> B₁ H -> B₂ H0 -> Prop) 
(AI₁ : A₁ -> I₁) (AI₂ : A₂ -> I₂)
(AI_R : forall (H : A₁) (H0 : A₂), A_R H H0 -> I_R (AI₁ H) (AI₂ H0))
(BI₁ : forall a : A₁, B₁ a -> I₁) (BI₂ : forall a : A₂, B₂ a -> I₂)
(BI_R : forall (a₁ : A₁) (a₂ : A₂) (a_R : A_R a₁ a₂) (H : B₁ a₁) (H0 : B₂ a₂),
        B_R a₁ a₂ a_R H H0 -> I_R (BI₁ a₁ H) (BI₂ a₂ H0))
(i1 : I₁) (i2 : I₂) (ir : I_R i1 i2) 
(i1wt : IWT A₁ I₁ B₁ AI₁ BI₁ i1) (i2wt : IWT A₂ I₂ B₂ AI₂ BI₂ i2)
: forall (p: IWT_RC _ _ A_R _ _ I_R _ _ B_R _ _ AI_R _ _ BI_R _ _ ir i1wt i2wt), 
  toNew _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 
  (fromNew _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p) = p.
Proof using.
 revert i2wt.
 revert ir.
 revert i2.
 induction i1wt.
 simpl.
 intros ? ? ?. destruct i2wt. simpl in *.
 intros p. destruct p as [ar pp].
 destruct pp as [pp pp2].
 subst. simpl.
 progress f_equal.
 progress f_equal.
 Fail progress f_equal.
 simpl. simpl.
 apply FunctionalExtensionality.functional_extensionality_dep.
 intros.
 apply FunctionalExtensionality.functional_extensionality_dep.
 intros.
 apply FunctionalExtensionality.functional_extensionality_dep.
 intros ?.
 apply H.
Qed.

End Iso.

Print Assumptions fromNew.
(*
Closed under the global context
*)
Print Assumptions toNew.
(*
Closed under the global context
*)

Inductive tree (A : Set) : Set :=
| leaf : tree A 
| node : tlist A -> tree A
with
 tlist (A:Set) : Set :=  
| tnil : tlist A 
| tcons : tree A -> tlist A -> tlist A.

Module test.
Inductive slist (A : Set) : Set :=
snil : slist A 
| scons : A -> slist A -> slist A.

Inductive tree (A : Set) : Set :=
| leaf : tree A 
| node : slist (tree A) -> tree A.
End test.

Module test2.
Inductive slist (A : Set) : Set :=  
| snil : slist A 
| scons : (A -> A) -> slist A -> slist A.

(*
Inductive tree (A : Set) : Set :=
| leaf : tree A 
| node : slist (tree A) -> tree A.
*)

Inductive tree (A : Set) : Set :=
| leaf : tree A 
| node : forall n, Vec (tree A) n -> tree A.

End test2.

Fixpoint zero (T:Type) (e:T=T) :=
  let x := zero T e in 0.

(*
Fixpoint leee (n m :nat) (e: n + 1 =m ) (p:le n (n+1)) {struct p}: nat :=
(fix leee (n m : nat) (e : n + 1 = m) (p : n <= n + 1) {struct p} : nat :=
   (fun p0 : n <= m => ?Goal@{p:=p0}) (eq_ind (n + 1) (fun n0 : nat => n <= n0) p m e))
   
    
rewrite e in p.
Show Proof.
destruct n.
-  exact 0.
- specialize (leee n (n+1) eq_refl). apply leee.
Show Proof.
  inversion p.
  destruct p.
  rewrite <- e in p.
  inversion p. admit.
  subst.
  destruct p.

destruct p.
subst m.


Lemma leee0 n p : leee n p =0.
unfold leee.
destruct p.
*)
