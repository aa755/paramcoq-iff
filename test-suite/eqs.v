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

Run TemplateProgram (genParam indTransEnv false true "eqs_recs").

(*
Definition xxx :=
(fun (A A₂ : Set) (A_R : A -> A₂ -> Prop) (x : A) 
   (x₂ : A₂) (x_R : A_R x x₂) (P : A -> Set) (P₂ : A₂ -> Set)
   (P_R : forall (a : A) (a₂ : A₂), A_R a a₂ -> P a -> P₂ a₂ -> Prop)
   (f : P x) (f₂ : P₂ x₂) (f_R : P_R x x₂ x_R f f₂) 
   (y : A) (y₂ : A₂) (y_R : A_R y y₂) (e : eqs A x y) 
   (e₂ : eqs A₂ x₂ y₂)
   (e_R : Top_eqs_eqs_RR0 A A₂ A_R x x₂ x_R y y₂ y_R e e₂) =>
 match
   e as e0 in (eqs _ _ y0)
   return
     ((fun (y1 : A : Set) (y0₂ : A₂ : Set) (e1 : eqs A x y1 : Prop)
         (e₂0 : eqs A₂ x₂ y0₂ : Prop) =>
       forall y0_R : A_R y1 y0₂,
       Top_eqs_eqs_RR0 A A₂ A_R x x₂ x_R y1 y0₂ y0_R e1 e₂0 ->
       P_R y1 y0₂ y0_R
         match e1 in (eqs _ _ y2) return (P y2) with
         | eq_refls _ _ => f
         end
         match e₂0 in (eqs _ _ y0₂0) return (P₂ y0₂0) with
         | eq_refls _ _ => f₂
         end) y0 y₂ e0 e₂)
 with
 | eq_refls _ _ =>
     match
       e₂ as e₂0 in (eqs _ _ y0₂)
       return
         ((fun (y0 : A : Set) (y0₂0 : A₂ : Set) (e0 : eqs A x y0 : Prop)
             (e₂1 : eqs A₂ x₂ y0₂0 : Prop) =>
           forall y0_R : A_R y0 y0₂0,
           Top_eqs_eqs_RR0 A A₂ A_R x x₂ x_R y0 y0₂0 y0_R e0 e₂1 ->
           P_R y0 y0₂0 y0_R
             match e0 in (eqs _ _ y1) return (P y1) with
             | eq_refls _ _ => f
             end
             match e₂1 in (eqs _ _ y0₂1) return (P₂ y0₂1) with
             | eq_refls _ _ => f₂
             end) x y0₂ (eq_refls A x) e₂0)
     with
     | eq_refls _ _ =>
         fun (y0_R : A_R x x₂)
           (e_R0 : Top_eqs_eqs_RR0 A A₂ A_R x x₂ x_R x x₂ y0_R 
                     (eq_refls A x) (eq_refls A₂ x₂)) =>
         Top_eqs_eqs_RR0_paramConstr_0_paramInv A A₂ A_R x x₂ x_R e_R0
           (P_R x x₂ y0_R
              match eq_refls A x in (eqs _ _ y0) return (P y0) with
              | eq_refls _ _ => f
              end
              match eq_refls A₂ x₂ in (eqs _ _ y0₂) return (P₂ y0₂) with
              | eq_refls _ _ => f₂
              end) f_R
     end
 end y_R e_R).

*)
