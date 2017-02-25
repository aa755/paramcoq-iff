(*
abhishek@brixpro:~/parametricity/reflective-paramcoq/test-suite$ ./coqid.sh indFunArg
*)

Require Import SquiggleEq.terms.


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

Require Import ReflParam.PIWNew.

Require Import Template.Template.

Inductive IWT (I A : Set) (B : A -> Set) (AI : A -> I) 
(BI : forall (a : A), B a -> I) : forall (i:I), Prop :=
iwt : forall (a : A) (lim: forall b : B a, IWT I A B AI BI (BI a b)),
     IWT I A B AI BI (AI a).

Inductive WT (A : Set) :  Prop :=
wt : forall (lim: WT A),
     WT A.

Require Import ReflParam.anyRelIndProp.
Run TemplateProgram (genParamIndProp [] false "Top.IWP.WT").
(*
Somehow, WT_R is being confused with A_R in variable bindings.
Error: Illegal application: 
The term "A_R" of type "A -> A₂ -> Prop"
cannot be applied to the term
 "A" : "Set"
This term has type "Set" which should be coercible to "A".
*)
Parametricity Recursive WT.
Print WT_R.
Run TemplateProgram (printTermSq "Top.IWP.WT_R").

Run TemplateProgram (genParamIndProp [] false "Top.IWP.IWT").

(*
This is correct. The bug seems to be in how squiggle rep. of inductives is converted
to templateCoq. it seems that the boundvars representing the inductives in the mutual block
are not put in scope when converting from named to DB.
exists worked.
WT_R got confused as A_R. A_R is the nearest boundvar.
named to DB conversion picks the index 0 when the var is not found

([nNamed "A"; nNamed "A"; nNamed "A"],
[("Top_IWP_WT_pmtcty_RR0",
 mkPiS (0, nNamed "A") (mkSort sSet) None
   (mkPiS (1, nNamed "A₂") (mkSort sSet) None
      (mkPiS (2, nNamed "A_R")
         (mkPiS (6, nAnon) (vterm (0, nNamed "A")) None (mkPiS (9, nAnon) (vterm (1, nNamed "A₂")) None (mkSort sProp) None) None) None
         (mkPiS (6, nAnon) (oterm (CApply 1) [bterm [] (mkConstInd (mkInd "Top.IWP.WT" 0)); bterm [] (vterm (0, nNamed "A"))]) None
            (mkPiS (9, nAnon) (oterm (CApply 1) [bterm [] (mkConstInd (mkInd "Top.IWP.WT" 0)); bterm [] (vterm (1, nNamed "A₂"))]) None
               (mkSort sProp) None) None) None) None) None,
 [("Top_IWP_WT_pmtcty_RR0_constr_0",
  bterm [(2, nNamed "WT_R"); (3, nNamed "A"); (4, nNamed "A₂"); (5, nNamed "A_R")]
    (mkPiS (6, nNamed "lim") (oterm (CApply 1) [bterm [] (vterm (0, nNamed "WT")); bterm [] (vterm (3, nNamed "A"))]) None
       (mkPiS (7, nNamed "lim₂") (oterm (CApply 1) [bterm [] (vterm (1, nNamed "WT₂")); bterm [] (vterm (4, nNamed "A₂"))]) None
          (mkPiS (8, nNamed "lim_R")
             (oterm (CApply 2)
                [bterm []
                   (oterm (CApply 3)
                      [bterm [] (vterm (2, nNamed "WT_R")); bterm [] (vterm (3, nNamed "A")); bterm [] (vterm (4, nNamed "A₂"));
                      bterm [] (vterm (5, nNamed "A_R"))]); bterm [] (vterm (6, nNamed "lim")); bterm [] (vterm (7, nNamed "lim₂"))]) None
             (oterm (CApply 2)
                [bterm []
                   (oterm (CApply 3)
                      [bterm [] (vterm (2, nNamed "WT_R")); bterm [] (vterm (3, nNamed "A")); bterm [] (vterm (4, nNamed "A₂"));
                      bterm [] (vterm (5, nNamed "A_R"))]);
                bterm []
                  (oterm (CApply 1)
                     [bterm [] (oterm (CApply 1) [bterm [] (mkConstr (mkInd "Top.IWP.WT" 0) 0); bterm [] (vterm (3, nNamed "A"))]);
                     bterm [] (vterm (6, nNamed "lim"))]);
                bterm []
                  (oterm (CApply 1)
                     [bterm [] (oterm (CApply 1) [bterm [] (mkConstr (mkInd "Top.IWP.WT" 0) 0); bterm [] (vterm (4, nNamed "A₂"))]);
                     bterm [] (vterm (7, nNamed "lim₂"))])]) None) None) None))])])
*)
