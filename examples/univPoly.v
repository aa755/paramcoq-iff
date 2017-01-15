Definition pair@{i} (T:Type@{i}) (t:T): (T*T) := (t,t).

Print pair.

Check (pair True I).


Require Import Template.Template.
Quote Definition ps := pair nat 0.
Require Import String.
Require Import Ascii.
Open Scope string_scope.
Require Import List.
Import ListNotations.
Print ps.

Definition idT@{i} (T:Type@{i}) : Type@{i} := T.

Require Import Template.Ast.
Make Definition ps_from_syntax := 
(Ast.tApp (Ast.tConst "Top.pair")
  [Ast.tInd (Ast.mkInd "Coq.Init.Datatypes.nat" 0);
  Ast.tConstruct (Ast.mkInd "Coq.Init.Datatypes.nat" 0) 0]).
  
Print ps_from_syntax.

Make Definition idn_from_syntax := 
(Ast.tApp (Ast.tConst "Top.idT")
  [Ast.tInd (Ast.mkInd "Coq.Init.Datatypes.nat" 0)]).

Set Universe Minimization.

Print idn_from_syntax.


(*
Definition pair2@{i} (T:Type) (t:T): (T*T) := (t,t).
Top.6 is unbound.
*)

(*
Definition pair2@{i} (T:Type): Type@{i} := list T.
Error: Universe {Top.18} is unbound.
*)

(*
Definition pair2@{i} (T:Type@{i}): Type := list T.
Error: Universe {Top.22} is unbound.
Can't mix global and local universes?
*)

Definition pair2@{i j} (T:Type@{i}): Type@{j} :=  T.

Definition xx := (pair2 nat).
Print xx.
Unset Universe Minimization.
Definition xxx := (pair2 nat).
Print xxx.
(*
xx = pair2 nat
     : Type@{Top.30}
*)
Print xx.
(*
xx = pair2 nat
     : Type@{Top.30}
why same?
*)

Definition pair4@{i} (T:Type@{i}) (t:T) : (T*(Type@{i})) 
  := @Coq.Init.Datatypes.pair T (Type@{i}) t T.

Print Universes.

Check (pair2 nat).
