Require Import common.
Require Import templateCoqMisc.
Require Import String.
Require Import List.
Require Import Template.Ast.
Require Import SquiggleEq.terms.
Require Import paramDirect.
Require Import SquiggleEq.substitution.

Import ListNotations.

Open Scope string_scope.

Definition capture (T: nat -> Set) (x:nat) (x: T x) := x.

Parametricity Recursive capture.

Print capture_R .


Run TemplateProgram (printTermSq "capture").

Definition captureSyntax :=
(mkLamS (0, nNamed "T")
   (mkPiS (0, nAnon) (mkConstInd (mkInd "Coq.Init.Datatypes.nat" 0)) 
      (Some sSet) (mkSort sSet) None) None
   (mkLamS (3, nNamed "x") (mkConstInd (mkInd "Coq.Init.Datatypes.nat" 0)) 
      (Some sSet)
      (mkLamS (3, nNamed "x") (* changed 6 to 3*)
         (oterm (CApply 1)
            [bterm [] (vterm (0, nNamed "T")); bterm [] (vterm (3, nNamed "x"))])
         (Some sSet) (vterm (3, nNamed "x"))))).

Eval vm_compute in (translate false captureSyntax).

Definition captureTranslateSyntax
     := mkLamS (0, nNamed "T")
         (mkPiS (0, nAnon) (mkConstInd (mkInd "Coq.Init.Datatypes.nat" 0)) 
            (Some sSet) (mkSort sSet) None) None
         (mkLamS (1, nNamed "T₂")
            (mkPiS (1, nAnon) (mkConstInd (mkInd "Coq.Init.Datatypes.nat" 0)) 
               (Some sSet) (mkSort sSet) None) None
            (mkLamS (2, nNamed "T_R")
               (oterm (CApply 2)
                  [bterm []
                     (mkLamS (30, nNamed "ff")
                        (mkPiS (0, nAnon) (mkConstInd (mkInd "Coq.Init.Datatypes.nat" 0))
                           None
                           (oterm (CApply 1)
                              [bterm []
                                 (mkLamS (0, nAnon)
                                    (mkConstInd (mkInd "Coq.Init.Datatypes.nat" 0)) None
                                    (mkSort sSet)); bterm [] (vterm (0, nAnon))]) None) None
                        (mkLamS (31, nNamed "ff₂")
                           (mkPiS (1, nAnon) (mkConstInd (mkInd "Coq.Init.Datatypes.nat" 0))
                              None
                              (oterm (CApply 1)
                                 [bterm []
                                    (mkLamS (1, nAnon)
                                       (mkConstInd (mkInd "Coq.Init.Datatypes.nat" 0)) None
                                       (mkSort sSet)); bterm [] (vterm (1, nAnon))]) None)
                           None
                           (mkPiS (0, nAnon) (mkConstInd (mkInd "Coq.Init.Datatypes.nat" 0))
                              None
                              (mkPiS (1, nAnon)
                                 (mkConstInd (mkInd "Coq.Init.Datatypes.nat" 0)) None
                                 (mkPiS (2, nAnon)
                                    (oterm (CApply 2)
                                       [bterm [] (mkConst "Coq_Init_Datatypes_nat_RR0");
                                       bterm [] (vterm (0, nAnon));
                                       bterm [] (vterm (1, nAnon))]) None
                                    (oterm (CApply 2)
                                       [bterm []
                                          (oterm (CApply 3)
                                             [bterm []
                                                (mkLamS (0, nAnon)
                                                   (mkConstInd
                                                      (mkInd "Coq.Init.Datatypes.nat" 0))
                                                   None
                                                   (mkLamS (1, nAnon)
                                                      (mkConstInd
                                                         (mkInd "Coq.Init.Datatypes.nat" 0))
                                                      None
                                                      (mkLamS (2, nAnon)
                                                         (oterm 
                                                            (CApply 2)
                                                            [bterm []
                                                               (mkConst
                                                               "Coq_Init_Datatypes_nat_RR0");
                                                            bterm [] (vterm (0, nAnon));
                                                            bterm [] (vterm (1, nAnon))])
                                                         None
                                                         (mkLamS 
                                                            (0, nAnon) 
                                                            (mkSort sSet) None
                                                            (mkLamS 
                                                               (3, nAnon) 
                                                               (mkSort sSet) None
                                                               (mkPiS 
                                                               (6, nAnon) 
                                                               (vterm (0, nAnon)) None
                                                               (mkPiS 
                                                               (9, nAnon) 
                                                               (vterm (3, nAnon)) None
                                                               (mkSort sProp) None) None))))));
                                             bterm [] (vterm (0, nAnon));
                                             bterm [] (vterm (1, nAnon));
                                             bterm [] (vterm (2, nAnon))]);
                                       bterm []
                                         (oterm (CApply 1)
                                            [bterm [] (vterm (30, nNamed "ff"));
                                            bterm [] (vterm (0, nAnon))]);
                                       bterm []
                                         (oterm (CApply 1)
                                            [bterm [] (vterm (31, nNamed "ff₂"));
                                            bterm [] (vterm (1, nAnon))])]) None) None) None)));
                  bterm [] (vterm (0, nNamed "T")); bterm [] (vterm (1, nNamed "T₂"))]) None
               (mkLamS (3, nNamed "x") (mkConstInd (mkInd "Coq.Init.Datatypes.nat" 0)) None
                  (mkLamS (4, nNamed "x₂") (mkConstInd (mkInd "Coq.Init.Datatypes.nat" 0))
                     None
                     (mkLamS (5, nNamed "x_R")
                        (oterm (CApply 2)
                           [bterm [] (mkConst "Coq_Init_Datatypes_nat_RR0");
                           bterm [] (vterm (3, nNamed "x"));
                           bterm [] (vterm (4, nNamed "x₂"))]) None
                        (mkLamS (3, nNamed "x")
                           (oterm (CApply 1)
                              [bterm [] (vterm (0, nNamed "T"));
                              bterm [] (vterm (3, nNamed "x"))]) None
                           (mkLamS (4, nNamed "x₂")
                              (oterm (CApply 1)
                                 [bterm [] (vterm (1, nNamed "T₂"));
                                 bterm [] (vterm (4, nNamed "x₂"))]) None
                              (mkLamS (5, nNamed "x_R")
                                 (oterm (CApply 2)
                                    [bterm []
                                       (oterm (CApply 3)
                                          [bterm [] (vterm (2, nNamed "T_R"));
                                          bterm [] (vterm (3, nNamed "x"));
                                          bterm [] (vterm (4, nNamed "x₂")); (* capture *)
                                          bterm [] (vterm (5, nNamed "x_R"))]);
                                    bterm [] (vterm (3, nNamed "x"));
                                    bterm [] (vterm (4, nNamed "x₂"))]) None
                                 (vterm (5, nNamed "x_R")))))))))).

Run TemplateProgram (genParam false true "capture").
Print capture_RR.
Run TemplateProgram (tmMkDefinitionSq "captureFromSyn" captureSyntax).
Run TemplateProgram (tmMkDefinitionSq "captureTranslate" captureTranslateSyntax).
(*
In environment
T : nat -> Set
T₂ : nat -> Set
T_R : forall H H0 : nat, Coq_Init_Datatypes_nat_RR0 H H0 -> T H -> T₂ H0 -> Prop
x : nat
x₂ : nat
x_R : Coq_Init_Datatypes_nat_RR0 x x₂
x0 : T x
x₂0 : T₂ x₂
The term "x0" has type "T x" while it is expected to have type "nat".
*)







