
Declare ML Module "paramcoq".

Definition xx:=  forall (T:Type) (t1 t2:T), bool.

Parametricity Recursive xx.

(* Print xx_R. *)

Definition xx_Rb :=
fun f₁ f₂ : forall T : Type, T -> T -> bool =>
forall (T₁ T₂ : Type) (T_R : T₁ -> T₂ -> Type) (t1₁ : T₁) (t1₂ : T₂),
T_R t1₁ t1₂ ->
forall (t2₁ : T₁) (t2₂ : T₂), T_R t2₁ t2₂ -> (f₁ T₁ t1₁ t2₁) = (f₂ T₂ t1₂ t2₂).



Definition xx1:=  forall (T:Type) (t:T), bool.

Parametricity Recursive xx1.
(* Print xx1_R. *)

Definition xx1_Rb :=
fun f₁ f₂ : forall T : Type, T ->  bool =>
forall (T₁ T₂ : Type) (T_R : T₁ -> T₂ -> Prop) (t₁ : T₁) (t₂ : T₂),
T_R t₁ t₂ ->
bool_R (f₁ T₁ t₁) (f₂ T₂ t₂).

(* Check (eq_refl : xx1_Rb = xx1_R). *)

Definition xxp:=  forall (T:Type) (t:T), Prop.

Parametricity Recursive xxp.
Print xxp_R.

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
Parametricity Recursive PP.
Print PP_R.

Definition Prop_R :=  fun P1 P2 : Prop => P1 -> P2 -> Prop.

Definition xxp_Rbad := fun (T:Type) (t:T) => forall (t2:T), t=t2.

(* only totality on T is needed in this example *)
Definition xxpb:=  forall (T:Type)  (f:T->bool), Prop.

Definition xxpbBad :=  fun  (T:Type) (f:T->bool) => forall (x:T), f x = true.

Definition goodP {P1 P2: Prop} (R : P1 -> P2 -> Prop) := P1 <-> P2 /\ (forall (x:P1) (y:P2), R x y).
