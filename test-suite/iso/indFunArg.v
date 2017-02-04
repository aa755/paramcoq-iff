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

(* translation of this fails because of clashes due to unnabed binders
Inductive NatLike (A B:Set) (C: (A->B) -> Set): Set := 
| SS : forall (f:A->B), C f -> NatLike A B C.
*)


Inductive NatLike (A:Set) (C: forall aa:A, Set): Set := 
(* | SS : forall (f:A->B) (c:C f)  (d:forall a:A, NatLike A B C)
     (e:forall (fi:A->B) (ci:C fi), NatLike A B C), NatLike A B C *) 
 | SS2 :  forall (ao:A) (cao: C ao) (d:forall (a:A) (ca: C a), NatLike A C),
       NatLike A C.

Run TemplateProgram (genParamInd [] true true "Top.indFunArg.NatLike").
Require Import ReflParam.Trecord.

Run TemplateProgram (genParamIndTot [] true true "Top.indFunArg.NatLike").

(*
(fix
 Top_indFunArg_NatLike_pmtcty_RR0_iso (A A₂ : Set) (A_R : BestRel A A₂) 
                                      (C : A -> Set) (C₂ : A₂ -> Set)
                                      (C_R : forall (aa : A) (aa₂ : A₂),
                                             BestR A_R aa aa₂ ->
                                             (fun H H0 : Set => BestRel H H0) 
                                               (C aa) (C₂ aa₂)) 
                                      (H : NatLike A C) {struct H} : 
 NatLike A₂ C₂ :=
   match H with
   | SS2 _ _ ao cao d =>
       let ao₂ := BestTot12 A_R ao in
       let ao_R := BestTot12R A_R ao in 
(* the body of cao₂ depends on ao_R above. So. the let bindings have to be 
scoped in order *)       
       let cao₂ := BestTot12 (C_R ao ao₂ ao_R) cao in
       let cao_R := BestTot12R (C_R ao ao₂ ao_R) cao in
       let d₂ :=
         fun (a₂ : A₂) (ca₂ : C₂ a₂) =>
         let a := BestTot21 A_R a₂ in
         let a_R := BestTot21R A_R a₂ in
         let ca := BestTot21 (C_R a a₂ a_R) ca₂ in
         let ca_R := BestTot21R (C_R a a₂ a_R) ca₂ in
         Top_indFunArg_NatLike_pmtcty_RR0_iso A A₂ A_R C C₂ C_R (d a ca) in
       SS2 A₂ C₂ ao₂ cao₂ d₂
   end)

*)