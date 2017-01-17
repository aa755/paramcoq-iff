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

Print eq.

Inductive eqs (A : Set) (x : A) : forall a:A, Prop :=  eq_refls : eqs A x x.


Run TemplateProgram (genParamInd [] false true true true "Top.eqs.eqs").

(*
(fix
 Top_eqs_eqs_RR0 (A A₂ : Set) (A_R : A -> A₂ -> Prop) (x : A) (x₂ : A₂) 
                 (x_R : A_R x x₂) (H : A) (H0 : A₂) (H1 : A_R H H0) 
                 (H2 : eqs A x H) (H3 : eqs A₂ x₂ H0) {struct H2} : Prop :=
   match H2 with
   | eq_refls _ _ => match H3 with
                     | eq_refls _ _ => True
                     end
   end)
Top_eqs_eqs_RR0 is defined
(fun (A A₂ : Set) (A_R : A -> A₂ -> Prop) (x : A) (x₂ : A₂) (_ : A_R x x₂) => I)
Top_eqs_eqs_RR0_paramConstr_0 is defined
*)


Run TemplateProgram (mkIndEnv "indTransEnv" ["Top.eqs.eqs"]).

Arguments existT : clear implicits.


Definition eqs_recs := 
fun (A : Set) (x : A) (P : forall a:A, Set) (f : P x) (y : A) (e : eqs A x y) =>
match e as esss in (eqs _ _ yy)  return (P yy) with
| eq_refls _ _ => f
end.

Arguments sigT : clear implicits.

(*
Declare ML Module "paramcoq".
Parametricity Recursive eqs_recs.
*)
Notation eqs_R := Top_eqs_eqs_RR0.
Definition eqrecs_RR :
forall (A₁ A₂ : Set) (A_R : A₁ -> A₂ -> Prop) (x₁ : A₁) (x₂ : A₂) 
         (x_R : A_R x₁ x₂) (P₁ : A₁ -> Set) (P₂ : A₂ -> Set)
         (P_R : forall (a₁ : A₁) (a₂ : A₂), A_R a₁ a₂ -> P₁ a₁ -> P₂ a₂ -> Set) 
         (f₁ : P₁ x₁) (f₂ : P₂ x₂),
       P_R x₁ x₂ x_R f₁ f₂ ->
       forall (y₁ : A₁) (y₂ : A₂) (y_R : A_R y₁ y₂) (e₁ : eqs A₁ x₁ y₁) (e₂ : eqs A₂ x₂ y₂),
       eqs_R A₁ A₂ A_R x₁ x₂ x_R y₁ y₂ y_R e₁ e₂ ->
       P_R y₁ y₂ y_R (eqs_recs A₁ x₁ P₁ f₁ y₁ e₁) (eqs_recs A₂ x₂ P₂ f₂ y₂ e₂).
Abort.
       
Definition eq_recs_RR :=
(fun (A A₂ : Set) (A_R : A -> A₂ -> Prop) (x : A) 
   (x₂ : A₂) (x_R : A_R x x₂) (P : A -> Set) (P₂ : A₂ -> Set)
   (P_R : forall (a : A) (a₂ : A₂), A_R a a₂ -> P a -> P₂ a₂ -> Prop)
   (f : P x) (f₂ : P₂ x₂) (f_R : P_R x x₂ x_R f f₂) 
   (y : A) (y₂ : A₂) (y_R : A_R y y₂) (e : eqs A x y) 
   (e₂ : eqs A₂ x₂ y₂)
   (e_R : Top_eqs_eqs_RR0 A A₂ A_R x x₂ x_R y y₂ y_R e e₂) =>
 match
   e as esss in (eqs _ _ yy)
   return
     ((fun (yy0 : A : Set) (yy₂ : A₂ : Set) (esss0 : eqs A x yy0 : Prop)
         (esss₂ : eqs A₂ x₂ yy₂ : Prop) =>
       forall yy_R : A_R yy0 yy₂,
       Top_eqs_eqs_RR0 A A₂ A_R x x₂ x_R yy0 yy₂ yy_R esss0 esss₂ ->
       P_R yy0 yy₂ yy_R
         match esss0 in (eqs _ _ yy1) return (P yy1) with
         | eq_refls _ _ => f
         end
         match esss₂ in (eqs _ _ yy₂0) return (P₂ yy₂0) with
         | eq_refls _ _ => f₂
         end) yy y₂ esss e₂)
 with
 | eq_refls _ _ =>
     match
       e₂ as esss₂ in (eqs _ _ yy₂)
       return
         ((fun (yy : A : Set) (yy₂0 : A₂ : Set) (esss : eqs A x yy : Prop)
             (esss₂0 : eqs A₂ x₂ yy₂0 : Prop) =>
           forall yy_R : A_R yy yy₂0,
           Top_eqs_eqs_RR0 A A₂ A_R x x₂ x_R yy yy₂0 yy_R esss esss₂0 ->
           P_R yy yy₂0 yy_R
             match esss in (eqs _ _ yy0) return (P yy0) with
             | eq_refls _ _ => f
             end
             match esss₂0 in (eqs _ _ yy₂1) return (P₂ yy₂1) with
             | eq_refls _ _ => f₂
             end) x yy₂ (eq_refls A x) esss₂)
     with
     | eq_refls _ _ =>
         fun (yy_R : A_R x x₂)
           (esss_R : Top_eqs_eqs_RR0 A A₂ A_R x x₂ x_R x x₂ yy_R
                       (eq_refls A x) (eq_refls A₂ x₂)) =>
         Top_eqs_eqs_RR0_paramConstr_0_paramInv A A₂ A_R x x₂ x_R esss_R
           (P_R x x₂ yy_R
              match eq_refls A x in (eqs _ _ yy) return (P yy) with
              | eq_refls _ _ => f
              end
              match eq_refls A₂ x₂ in (eqs _ _ yy₂) return (P₂ yy₂) with
              | eq_refls _ _ => f₂
              end) f_R
     end
 end y_R e_R).


Run TemplateProgram (genParam indTransEnv false true "eqs_recs").

