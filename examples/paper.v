

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

Definition largeElim (n:nat) : Set :=
  match n with
  | O  => nat 
  | S _ => bool
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

Definition pred_R (n n' : nat) (n_R : nat_R n n') : nat_R (pred n) (pred n') := 
match n_R with
| O_R => O_R
| S_R n n' n_R => n_R
end.

Definition largeElim_R (n n' : nat) (n_R : nat_R n n') : (largeElim n) -> (largeElim n') -> Set  :=
match n_R with
| O_R => nat_R
| S_R _ _ _ => bool_R
end.
