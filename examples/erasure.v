Require Import Coq.Classes.DecidableClass.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import SquiggleEq.export.
Require Import SquiggleEq.UsefulTypes.
Require Import SquiggleEq.list.
Require Import SquiggleEq.LibTactics.
Require Import SquiggleEq.tactics.
Require Import SquiggleEq.AssociationList.
Require Import ReflParam.common.
Require Import ReflParam.templateCoqMisc.
Require Import ReflParam.paramDirect.


Locate prod.
Print prod.
Inductive prods (A B : Set) : Set :=  pair : A -> B -> prods A  B.

Run TemplateProgram (genParamInd [] false true true "Top.erasure.prods").
(*
(fix
 Top_erasure_prods_pmtcty_RR0 (A A₂ : Set) (A_R : A -> A₂ -> Prop) 
                              (B B₂ : Set) (B_R : B -> B₂ -> Prop) 
                              (H : prods A B) (H0 : prods A₂ B₂) {struct H} : Prop :=
   match H with
   | pair _ _ x x0 =>
       match H0 with
       | pair _ _ x1 x2 =>
           {_ : A_R x x1 &
           {_ : B_R x0 x2 & Top_erasure_prods_pmtcty_RR0_indices A A₂ A_R B B₂ B_R}}
       end
   end)
(fun (A A₂ : Set) (A_R : A -> A₂ -> Prop) (B B₂ : Set) (B_R : B -> B₂ -> Prop) 
   (H : A) (H0 : A₂) (H1 : B) (H2 : B₂)
   (sigt_R : {_ : A_R H H0 &
             {_ : B_R H1 H2 & Top_erasure_prods_pmtcty_RR0_indices A A₂ A_R B B₂ B_R}})
   (retTyp_R : {_ : A_R H H0 &
               {_ : B_R H1 H2 & Top_erasure_prods_pmtcty_RR0_indices A A₂ A_R B B₂ B_R}} ->
               Set)
   (rett_R : forall (H3 : A_R H H0) (H4 : B_R H1 H2),
             retTyp_R
               (existT
                  (fun _ : A_R H H0 =>
                   {_ : B_R H1 H2 & Top_erasure_prods_pmtcty_RR0_indices A A₂ A_R B B₂ B_R})
                  H3
                  (existT
                     (fun _ : B_R H1 H2 =>
                      Top_erasure_prods_pmtcty_RR0_indices A A₂ A_R B B₂ B_R) H4
                     (Top_erasure_prods_pmtcty_RR0_indicesc A A₂ A_R B B₂ B_R)))) =>
 sigT_rec
   (fun
      sigt_R0 : {_ : A_R H H0 &
                {_ : B_R H1 H2 & Top_erasure_prods_pmtcty_RR0_indices A A₂ A_R B B₂ B_R}} =>
    retTyp_R sigt_R0)
   (fun H3 : A_R H H0 =>
    sigT_rec
      (fun
         sigt_R0 : {_ : B_R H1 H2 & Top_erasure_prods_pmtcty_RR0_indices A A₂ A_R B B₂ B_R}
       =>
       retTyp_R
         (existT
            (fun _ : A_R H H0 =>
             {_ : B_R H1 H2 & Top_erasure_prods_pmtcty_RR0_indices A A₂ A_R B B₂ B_R}) H3
            sigt_R0))
      (fun (H4 : B_R H1 H2)
         (sigt_R0 : Top_erasure_prods_pmtcty_RR0_indices A A₂ A_R B B₂ B_R) =>
       match
         sigt_R0 as sigt_R1
         return
           (retTyp_R
              (existT
                 (fun _ : A_R H H0 =>
                  {_ : B_R H1 H2 & Top_erasure_prods_pmtcty_RR0_indices A A₂ A_R B B₂ B_R})
                 H3
                 (existT
                    (fun _ : B_R H1 H2 =>
                     Top_erasure_prods_pmtcty_RR0_indices A A₂ A_R B B₂ B_R) H4 sigt_R1)))
       with
       | Top_erasure_prods_pmtcty_RR0_indicesc _ _ _ _ _ _ => rett_R H3 H4
       end)) sigt_R)
(fun (A A₂ : Set) (A_R : A -> A₂ -> Prop) (B B₂ : Set) (B_R : B -> B₂ -> Prop) 
   (H : A) (H0 : A₂) (H1 : A_R H H0) (H2 : B) (H3 : B₂) (H4 : B_R H2 H3) =>
 existT
   (fun _ : A_R H H0 =>
    {_ : B_R H2 H3 & Top_erasure_prods_pmtcty_RR0_indices A A₂ A_R B B₂ B_R}) H1
   (existT (fun _ : B_R H2 H3 => Top_erasure_prods_pmtcty_RR0_indices A A₂ A_R B B₂ B_R) H4
      (Top_erasure_prods_pmtcty_RR0_indicesc A A₂ A_R B B₂ B_R)))

*)
Print Top_erasure_prods_pmtcty_RR0_indices.

Definition prod_recs := 
fun (A B : Set) (P : prods A B -> Set) (f : forall (a : A) (b : B), P (pair A B a b))
  (p : prods A B) => match p as p0 return (P p0) with
                     | pair _ _ x x0 => f x x0
                     end.

Run TemplateProgram (mkIndEnv "indTransEnv" ["Top.erasure.prods"]).

Run TemplateProgram (genParam indTransEnv false true "prod_recs"). (* success!*)

Print prod_recs_RR.

prod_recs_RR = 
fun (A A₂ : Set) (A_R : A -> A₂ -> Prop) (B B₂ : Set) (B_R : B -> B₂ -> Prop)
  (P : prods A B -> Set) (P₂ : prods A₂ B₂ -> Set)
  (P_R : forall (H : prods A B) (H0 : prods A₂ B₂),
         Top_erasure_prods_pmtcty_RR0 A A₂ A_R B B₂ B_R H H0 -> P H -> P₂ H0 -> Prop)
  (f : forall (a : A) (b : B), P (pair A B a b))
  (f₂ : forall (a₂ : A₂) (b₂ : B₂), P₂ (pair A₂ B₂ a₂ b₂))
  (f_R : forall (a : A) (a₂ : A₂) (a_R : A_R a a₂) (b : B) (b₂ : B₂) (b_R : B_R b b₂),
         P_R (pair A B a b) (pair A₂ B₂ a₂ b₂)
           (Top_erasure_prods_pmtcty_RR0_constr_0 A A₂ A_R B B₂ B_R a a₂ a_R b b₂ b_R)
           (f a b) (f₂ a₂ b₂)) (p : prods A B) (p₂ : prods A₂ B₂)
  (p_R : Top_erasure_prods_pmtcty_RR0 A A₂ A_R B B₂ B_R p p₂) =>
match
  p as p0
  return
    ((fun (p1 : prods A B : Set) (p0₂ : prods A₂ B₂ : Set) =>
      forall p0_R : Top_erasure_prods_pmtcty_RR0 A A₂ A_R B B₂ B_R p1 p0₂,
      P_R p1 p0₂ p0_R match p1 as p2 return (P p2) with
                      | pair _ _ x x0 => f x x0
                      end
        match p0₂ as p0₂0 return (P₂ p0₂0) with
        | pair _ _ x₂ x0₂ => f₂ x₂ x0₂
        end) p0 p₂)
with
| pair _ _ x x0 =>
    match
      p₂ as p0₂
      return
        ((fun (p0 : prods A B : Set) (p0₂0 : prods A₂ B₂ : Set) =>
          forall p0_R : Top_erasure_prods_pmtcty_RR0 A A₂ A_R B B₂ B_R p0 p0₂0,
          P_R p0 p0₂0 p0_R match p0 as p1 return (P p1) with
                           | pair _ _ x1 x2 => f x1 x2
                           end
            match p0₂0 as p0₂1 return (P₂ p0₂1) with
            | pair _ _ x₂ x0₂ => f₂ x₂ x0₂
            end) (pair A B x x0) p0₂)
    with
    | pair _ _ x₂ x0₂ =>
        fun
          p0_R : Top_erasure_prods_pmtcty_RR0 A A₂ A_R B B₂ B_R 
                   (pair A B x x0) (pair A₂ B₂ x₂ x0₂) =>
        Top_erasure_prods_pmtcty_RR0_constr_0_inv A A₂ A_R B B₂ B_R x x₂ x0 x0₂ p0_R
          (fun
             p0_R0 : Top_erasure_prods_pmtcty_RR0 A A₂ A_R B B₂ B_R 
                       (pair A B x x0) (pair A₂ B₂ x₂ x0₂) =>
           P_R (pair A B x x0) (pair A₂ B₂ x₂ x0₂) p0_R0
             match pair A B x x0 as p0 return (P p0) with
             | pair _ _ x1 x2 => f x1 x2
             end
             match pair A₂ B₂ x₂ x0₂ as p0₂ return (P₂ p0₂) with
             | pair _ _ x₂0 x0₂0 => f₂ x₂0 x0₂0
             end) (fun (x_R : A_R x x₂) (x0_R : B_R x0 x0₂) => f_R x x₂ x_R x0 x0₂ x0_R)
    end
end p_R
     : forall (A A₂ : Set) (A_R : A -> A₂ -> Prop) (B B₂ : Set) 
         (B_R : B -> B₂ -> Prop) (P : prods A B -> Set) (P₂ : prods A₂ B₂ -> Set)
         (P_R : forall (H : prods A B) (H0 : prods A₂ B₂),
                Top_erasure_prods_pmtcty_RR0 A A₂ A_R B B₂ B_R H H0 -> P H -> P₂ H0 -> Prop)
         (f : forall (a : A) (b : B), P (pair A B a b))
         (f₂ : forall (a₂ : A₂) (b₂ : B₂), P₂ (pair A₂ B₂ a₂ b₂)),
       (forall (a : A) (a₂ : A₂) (a_R : A_R a a₂) (b : B) (b₂ : B₂) (b_R : B_R b b₂),
        P_R (pair A B a b) (pair A₂ B₂ a₂ b₂)
          (Top_erasure_prods_pmtcty_RR0_constr_0 A A₂ A_R B B₂ B_R a a₂ a_R b b₂ b_R)
          (f a b) (f₂ a₂ b₂)) ->
       forall (p : prods A B) (p₂ : prods A₂ B₂)
         (p_R : Top_erasure_prods_pmtcty_RR0 A A₂ A_R B B₂ B_R p p₂),
       P_R p p₂ p_R match p as p0 return (P p0) with
                    | pair _ _ x x0 => f x x0
                    end
         match p₂ as p0₂ return (P₂ p0₂) with
         | pair _ _ x₂ x0₂ => f₂ x₂ x0₂
         end
