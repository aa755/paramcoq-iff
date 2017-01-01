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
Require Import templateCoqMisc.
Require Import Template.Template.
Require Import Template.Ast.


Require Import Program.
Open Scope program_scope.

Require Import Coq.Init.Nat.

(* can be Prop for set *)
Definition translateSort (s:sort) : sort := 
match s with
| sType _ => s
| _ => sProp
end.
(*
Definition mkTyRel (T1 T2 sort: term) : term :=
  T1 ↪ T2 ↪ sort.
Definition projTyRel (T1 T2 T_R: term) : term := T_R.
*)

Require Import NArith.
Require Import Trecord.
Require Import common.

Let V:Set := (N*name).


Open Scope N_scope.

Let vprime (v:V) : V := (1+(fst v), nameMap (fun x => String.append x "₂") (snd v)).
Let vrel (v:V) : V := (2+(fst v), nameMap (fun x => String.append x "_R") (snd v)).

Notation mkLam x A b :=
  (oterm CLambda [bterm [] A; bterm [x] b]).

Notation mkPi x A b :=
  (oterm CProd [bterm [] A; bterm [x] b]).

(* because of length, this cannot be used as a pattern *)
Definition mkApp (f: STerm) (args: list STerm) : STerm :=
  oterm (CApply (length args)) ((bterm [] f)::(map (bterm []) args)).

Notation mkConst s:=
  (oterm (CConst s) []).

Notation mkConstInd s:=
  (oterm (CInd s) []).

Notation mkSort s  :=
  (oterm (CSort s) []).

Notation mkCast t ck typ :=
  (oterm (CCast ck) [bterm [] t; bterm [] typ]).

Definition mkConstApp s l : STerm :=
mkApp  (mkConst s) l.

Definition mkIndApp (i:inductive) l : STerm :=
if (decide (length l=0))%nat then (mkConstInd i) else
mkApp (mkConstInd i) l.


(* inline it? *)
Definition mkTyRel (T1 T2 sort: STerm) : STerm :=
  mkConstApp "ReflParam.Trecord.BestRel" [T1; T2].

(* inline it? *)
Definition projTyRel (T1 T2 T_R: STerm) : STerm := 
mkConstApp "ReflParam.Trecord.BestR" [T1; T2; T_R].

Definition getSort (t:STerm) : option sort :=
match t with
| mkCast t _ (mkSort s) => Some s
| _ => None
end.

Definition hasSortSetOrProp (t:STerm) : bool :=
match t with
| mkCast t _ (mkSort sSet) => true
| mkCast t _ (mkSort sProp) => true
| _ => false
end.

Definition removeHeadCast (t:STerm) : STerm :=
match t with
| mkCast t  _ (mkSort _) => t
| _ => t
end.

Definition ids : forall A : Set, A -> A := fun (A : Set) (x : A) => x.
Definition idsT  := forall A : Set, A -> A.

Run TemplateProgram (printTerm "ids").
Run TemplateProgram (printTerm "idsT").

Fixpoint mkLamL (lb: list (V*STerm)) (b: STerm) 
  : STerm :=
match lb with
| nil => b
| a::tl =>  mkLam (fst a) (snd a )(mkLamL tl b)
end.

Fixpoint mkPiL (lb: list (V*STerm)) (b: STerm) 
  : STerm :=
match lb with
| nil => b
| a::tl =>  mkPi (fst a) (snd a )(mkPiL tl b)
end.

Require Import PiTypeR.

Definition mkPiR (A1 A2 A_R B1 B2 B_R : STerm) : STerm := 
mkApp (mkConst "ReflParam.PiTypeR.PiTSummary")
  [A1;A2;A_R;B1;B2;B_R].

(* can be used only find binding an mkPi whose body has NO free variables at all,
e.g. Set *)

(* Definition dummyVar : V := (0, nAnon). *)

(* collect the places where the extra type info is needed, and add those annotations
beforehand.
Alternatively, keep trying in order: Prop -> Set -> Type*)



Definition PiABType
  (A1 A2 :Type) (A_R: A1 -> A2 -> Type) 
  (B1: A1 -> Type) 
  (B2: A2 -> Type)
  (B_R: forall a1 a2,  A_R a1 a2 ->  (B1 a1) -> (B2 a2) -> Type)
  := (fun (f1 : forall a : A1, B1 a) (f2 : forall a : A2, B2 a) =>
forall (a1 : A1) (a2 : A2) (p : A_R a1 a2), B_R a1 a2 p (f1 a1) (f2 a2)).

Definition PiATypeBSet (* A higher. A's higher/lower is taken care of in [translate] *)
  (A1 A2 :Type) (A_R: A1 -> A2 -> Type) 
  (B1: A1 -> Set) 
  (B2: A2 -> Set)
  (B_R: forall a1 a2,  A_R a1 a2 -> BestRel (B1 a1) (B2 a2))
  := (fun (f1 : forall a : A1, B1 a) (f2 : forall a : A2, B2 a) =>
forall (a1 : A1) (a2 : A2) (p : A_R a1 a2), BestR (B_R a1 a2 p) (f1 a1) (f2 a2)).

(* Not Allowed
PiATypeBProp (* A higher. A's higher/lower is taken care of in [translate] *)
  (A1 A2 :Type) (A_R: A1 -> A2 -> Type) 
  (B1: A1 -> Set) 
  (B2: A2 -> Set)
  (B_R: forall a1 a2,  A_R a1 a2 -> BestRel (B1 a1) (B2 a2))
  := (fun (f1 : forall a : A1, B1 a) (f2 : forall a : A2, B2 a) =>
forall (a1 : A1) (a2 : A2) (p : A_R a1 a2), BestR (B_R a1 a2 p) (f1 a1) (f2 a2)).
*)

(* a special case of the above, which is allowed. a.k.a impredicative polymorphism
A= Prop:Type
B:Prop 
What if A = nat -> Prop?
Any predicate over sets should be allowed?
In Lasson's theory, A  would be in Set_1
*)
Definition PiAEqPropBProp
(*  let A1:Type := Prop in
  let A2:Type := Prop in
  let A_R := BestRelP in *)
  (B1: Prop -> Prop) 
  (B2: Prop -> Prop)
  (B_R: forall a1 a2,  BestRelP a1 a2 -> BestRelP (B1 a1) (B2 a2))
  : BestRelP (forall a : Prop, B1 a) (forall a : Prop, B2 a).
Proof.
  unfold BestRelP in *.
  split; intros.
- rewrite <- (B_R a);[eauto | reflexivity].
- rewrite (B_R a);[eauto | reflexivity].
Qed.

Lemma TotalBestp:
TotalHeteroRel (fun x x0 : Prop => BestRel x x0).
Proof.
split; intros t; exists t; unfold rInv; simpl; apply GoodPropAsSet; unfold BestRelP;
    reflexivity.
Qed.
Definition PiAEqPropBPropNoErasure
(*  let A1:Type := Prop in
  let A2:Type := Prop in
  let A_R := BestRelP in *)
  (B1: Prop -> Prop) 
  (B2: Prop -> Prop)
  (B_R: forall (a1 a2 : Prop),  BestRel a1 a2 -> BestRel (B1 a1) (B2 a2))
  : BestRel (forall a : Prop, B1 a) (forall a : Prop, B2 a).
Proof.
  exists
  (fun f1 f2 =>
  forall (a1 : Prop) (a2 : Prop) (p : BestRel a1 a2), BestR (B_R a1 a2 p) (f1 a1) (f2 a2));
  simpl.
- pose proof (totalPiHalfProp Prop Prop BestRel B1 B2) as Hp. simpl in Hp.
  specialize (Hp (fun a1 a2 ar => BestR (B_R a1 a2 ar))).
  simpl in Hp. apply Hp.
  + apply TotalBestp.
  + intros. destruct (B_R a1 a2 p). simpl in *. assumption.
- split; intros  ? ? ? ? ? ? ?; apply proof_irrelevance.
- intros  ? ? ? ?; apply proof_irrelevance.
Defined.


Definition PiASetBType
  (A1 A2 :Set) (A_R: BestRel A1 A2) 
  (B1: A1 -> Type) 
  (B2: A2 -> Type)
  (B_R: forall a1 a2,  BestR A_R a1 a2 -> (B1 a1) -> (B2 a2) -> Type)
  := (fun (f1 : forall a : A1, B1 a) (f2 : forall a : A2, B2 a) =>
forall (a1 : A1) (a2 : A2) (p : BestR A_R a1 a2), B_R a1 a2 p (f1 a1) (f2 a2)).

Definition PiASetBSet := ReflParam.PiTypeR.PiTSummary.

Definition PiASetBProp (A1 A2 : Set) 
  (A_R : BestRel A1 A2 (* just totality suffices *)) 
  (B1 : A1 -> Prop) (B2 : A2 -> Prop)
  (B_R : forall (a1 : A1) (a2 : A2), @BestR A1 A2 A_R a1 a2 -> BestRelP (B1 a1) (B2 a2))
   :  BestRelP (forall a : A1, B1 a) (forall a : A2, B2 a).
Proof using.
  destruct A_R. simpl in *.
  eapply propForalClosedP;[apply Rtot|].
  assumption.
Qed.

(* BestRelP can be problematic because it will force erasure *)

Section BestRelPForcesEraureOfLambda.
Variable A:Set.
Variable A_R : A->A-> Prop.
Let B: A -> Prop := fun  _ => True.
Let f : forall a, B a := fun _ => I.
Definition f_R : @BestRP (forall a, B a) (forall a, B a) (*Pi_R *) f f.
unfold BestRP.
(* f is a lambda. So f_R must be 3 lambdas *)
Fail exact (fun (a1:A) (a2:A) (arp: A_R a1 a2) => I).
simpl.
Abort.
End BestRelPForcesEraureOfLambda.

(* What is the translation of (A1 -> Prop) ? *)
Definition PiAEq2PropBProp
  (A1 A2 :Set) (A_R: BestRel A1 A2)
(*  let A1:Type := Prop in
  let A2:Type := Prop in
  let A_R := BestRelP in *)
  (B1: (A1 -> Prop) -> Prop) 
  (B2: (A2 -> Prop) -> Prop)
  (B_R: forall (a1: A1->Prop) (a2 : A2->Prop),
     R_Fun (BestR A_R) BestRel a1 a2 -> BestRel (B1 a1) (B2 a2))
  : BestRel (forall a, B1 a) (forall a, B2 a).
Proof using.
  exists
  (fun f1 f2 =>
  forall (a1: A1->Prop) (a2 : A2->Prop) (p : R_Fun (BestR A_R) BestRel a1 a2), 
    BestR (B_R a1 a2 p) (f1 a1) (f2 a2));
  simpl.
- pose proof (totalPiHalfProp (A1 -> Prop) (A2 -> Prop) 
    (R_Fun (BestR A_R) BestRel) B1 B2) as Hp. simpl in Hp.
  specialize (Hp (fun a1 a2 ar => BestR (B_R a1 a2 ar))).
  simpl in Hp. apply Hp.
  + pose proof (@totalFun A1 A2 (BestR A_R) Prop Prop BestRel).
    simpl in *.
    replace ((fun x x0 : Prop => BestRel x x0)) with (BestRel:(Prop->Prop->Type)) in X;
      [| reflexivity].
    unfold R_Fun in *. simpl in *. unfold R_Pi in *.
    destruct A_R; simpl in *.
    apply X; auto.
    apply TotalBestp.
  + intros. destruct (B_R a1 a2 p). simpl in *. assumption.
- split; intros  ? ? ? ? ? ? ?; apply proof_irrelevance.
- intros  ? ? ? ?; apply proof_irrelevance.
Defined.

Definition PiAPropBType 
  (A1 A2 :Prop) (A_R: BestRelP A1 A2) 
  (B1: A1 -> Type) 
  (B2: A2 -> Type)
  (B_R: forall a1 a2,  BestRP a1 a2 -> (B1 a1) -> (B2 a2) -> Type)
  := (fun (f1 : forall a : A1, B1 a) (f2 : forall a : A2, B2 a) =>
forall (a1 : A1) (a2 : A2) (p : BestRP a1 a2), B_R a1 a2 p (f1 a1) (f2 a2)).

Definition PiAPropBSet
 (A1 A2 : Prop) 
  (A_R : BestRelP A1 A2) 
  (B1 : A1 -> Set) (B2 : A2 -> Set)
  (B_R : forall (a1 : A1) (a2 : A2), (@BestRP A1 A2) a1 a2 -> BestRel (B1 a1) (B2 a2))
   :  BestRel (forall a : A1, B1 a) (forall a : A2, B2 a).
Proof.
  eapply ReflParam.PiTypeR.PiTSummary with (A_R:= GoodPropAsSet A_R).
  simpl. exact B_R.
Defined.

Definition PiAPropBProp
 (A1 A2 : Prop) 
  (A_R : BestRelP A1 A2) 
  (B1 : A1 -> Prop) (B2 : A2 -> Prop)
  (B_R : forall (a1 : A1) (a2 : A2), (@BestRP A1 A2) a1 a2 -> BestRelP (B1 a1) (B2 a2))
   :  BestRelP (forall a : A1, B1 a) (forall a : A2, B2 a).
Proof.
  unfold BestRelP, BestRP in *.
  firstorder;
  eauto.
Qed.


Let xx :=
(PiATypeBSet Set Set (fun H H0 : Set => BestRel H H0)
   (fun A : Set => (A) -> A)
   (fun A₂ : Set => (A₂) -> A₂)
   (fun (A A₂ : Set) (A_R : BestRel A A₂) =>
    (PiTSummary A A₂ A_R (fun _ : A => A) (fun _ : A₂ => A₂)
      (fun (H : A) (H0 : A₂) (_ : BestR A_R H H0) => A_R)))).


Definition getPiConst (Asp Bsp : bool) := 
match (Asp, Bsp) with
(* true means lower universe (sp stands for Set or Prop) *)
| (false, false) => "PiABType"
| (false, true) => "PiATypeBSet"
| (true, false) => "PiASetBType"
| (true, true) => "ReflParam.PiTypeR.PiTSummary"
end.

(*
Definition mkPiRHigher2 (A1 A2 A_R B1 B2 B_R : STerm) : STerm := 
  mkLamL ()
*)

Definition appArgTranslate translate (b:@BTerm (N*name) CoqOpid) : list STerm :=
  let t := get_nt b in
  let t2 := tvmap vprime t in
  let tR := translate t in
  [t; t2; tR].

Definition mkTyRelOld T1 T2 TS := 
  let v1 := (6, nAnon) in (* safe to use 0,3 ? *)
  let v2 := (9, nAnon) in
  mkPiL [(v1,T1); (v2,T2)] TS. 


Fixpoint getHeadPIs (s: STerm) : STerm * list (V*STerm) :=
match s with
| mkPi nm A B => let (t,l):=(getHeadPIs B) in (t,(nm,A)::l)
| _ => (s,[])
end.


Require Import SquiggleEq.varInterface.
Import STermVarInstances.
Require Import SquiggleEq.varImplDummyPair.

(*
Definition t12  := (@free_vars, @free_vars_bterm).

Run TemplateProgram (printTerm "t12").
Inductives are always referred to as the first one in the mutual block, index.
The names of the second inductive never apear?
Run TemplateProgram (printTermSq "t12").
*)

Definition zeroSq : STerm := (mkConstInd (mkInd "Coq.Init.Logic.True" 0)). 


Section trans.
Variable piff:bool.
Let removeHeadCast := if piff then removeHeadCast else id.
Let hasSortSetOrProp := if piff then hasSortSetOrProp else (fun _ => false).
Let projTyRel := if piff then projTyRel else (fun _ _ t=> t).
Let mkTyRel := if piff then mkTyRel else mkTyRelOld.

Definition transLam translate  (nma : V*STerm) b :=
  let (nm,A) := nma in
  let A1 := (removeHeadCast A) in
  let A2 := tvmap vprime A1 in
  let f := if (hasSortSetOrProp A) then 
           (fun t => projTyRel A1 A2 t)
      else id in
  mkLamL [(nm, A1);
            (vprime nm, A2);
            (vrel nm, mkApp (f (translate A)) [vterm nm; vterm (vprime nm)])]
         b.

Definition constTransName (n:ident) : ident :=
  String.append (mapDots "_" n) "_RR".

Require Import ExtLib.Data.String.
Definition indTransName (n:inductive) : ident :=
match n with
| mkInd s n => String.append (constTransName s) (nat2string10 n)
end.

Fixpoint translate (t:STerm) : STerm :=
match t with
| vterm n => vterm (vrel n)
| mkSort s =>
  let v1 := (0, nAnon) in
  let v2 := (3, nAnon) in
(* because the body of the lambda is closed, no capture possibility*)
      mkLamL
        [(v1 (* Coq picks some name like H *), t);
         (v2, t)]
         (mkTyRel (vterm v1) (vterm v2) (mkSort (translateSort s)))
| mkCast tc _ _ => translate tc
| mkConst c => mkConst (constTransName c)
| mkConstInd s => mkConst (indTransName s)
| mkLam nm A b => transLam (translate ) (nm,A) (translate b)
| mkPi nm A B =>
  let A1 := (removeHeadCast A) in
  let A2 := tvmap vprime A1 in
  let B1 := (mkLam nm A1 (removeHeadCast B)) in
  let B2 := tvmap vprime B1 in
  let B_R := transLam translate (nm,A) (translate (removeHeadCast B)) in
  let Asp := (hasSortSetOrProp A) in
  let Bsp := (hasSortSetOrProp B) in
  mkApp (mkConst (getPiConst Asp Bsp)) [A1; A2; (translate A); B1; B2; B_R]
(* the translation of a lambda always is a lambda with 3 bindings. So no
projection of LHS should be required *)
| oterm (CApply _) (fb::argsb) =>
    mkApp (translate (get_nt fb)) (flat_map (appArgTranslate translate) argsb)
(* Const C needs to be translated to Const C_R, where C_R is the registered translation
  of C. Until we figure out how to make such databases, we can assuming that C_R =
    f C, where f is a function from strings to strings that also discards all the
    module prefixes *)
| _ => t
end.

Definition translateIndMatchBranch (argsB: STerm * list (V * STerm)) : STerm :=
  let (ret,args) := argsB in
  mkLamL args ret.


Definition boolNthTrue (len n:nat) : list bool:=
map (fun m => if decide(n=m) then true else false )(List.seq 0 len).

Definition translateIndInnerMatchBody o (cargs: list (list (V * STerm)))
   v mTyInfo (lb: (list bool)*(list (V * STerm))) :=
  let ret (b:bool) : STerm := if b then mkConstInd (mkInd "Coq.Init.Logic.True" 0)
             else mkConstInd (mkInd "Coq.Init.Logic.False" 0) in
  let cargs := map (map (fun p => (vprime (fst p), tvmap vprime (snd p)))) cargs in
  let lnt : list STerm := [tvmap vprime mTyInfo; vterm (vprime v)]
      ++(map translateIndMatchBranch (combine (map ret (fst lb)) cargs)) in
    translateIndMatchBranch (oterm  o (map (bterm []) lnt), snd lb).


Definition translateIndMatchBody (numParams:nat) (allInds: list inductive) 
  tind (cs: list (ident * SBTerm)) v (srt: STerm) ctyLams lp : STerm :=
  let indsT : list STerm := (map (fun t => mkConstInd t) allInds)++lp in
  let ctypes := map ((fun b: SBTerm => apply_bterm b indsT)∘snd) cs in
  let cargs : list (list (V * STerm)) := map (snd∘getHeadPIs) ctypes in
  let cargsL : list nat := (map (@length (V * STerm)) cargs) in
  let o := (CCase (tind, numParams) cargsL) in
  let mTyInfo := mkLamL ctyLams (mkSort sProp) (*fix*) in
  let numConstrs : nat := length cargs in
  let lb : list (list bool):= map (boolNthTrue numConstrs) (List.seq 0 numConstrs) in
  let lnt : list STerm := [mTyInfo; vterm v]
      ++(map (translateIndInnerMatchBody o cargs v mTyInfo) (combine lb cargs)) in
    oterm o (map (bterm []) lnt).



(** tind is a constant denoting the inductive being processed *)
Definition translateInd (numParams:nat) (allInds: list inductive) 
  (tind : inductive*(simple_one_ind STerm SBTerm)) :=
  let (tind,smi) := tind in
  let (nmT, cs) := smi in
  let (nm, t) := nmT in
  let (srt, bs) := getHeadPIs t in
  let srt := 
    match srt with 
    | mkSort s => mkSort (translateSort s) 
    | _ => srt (* should never happen *)
    end in
  let vars : list V := map fst bs in
  let t1 : STerm := (mkIndApp tind (map vterm vars)) in
  let t2 : STerm := (mkIndApp tind (map (vterm∘vprime) vars)) in
  (* local section variables could be a problem. Other constants are not a problem*)
  let v : V := fresh_var vars in
  let caseTyLams := skipn numParams (snoc bs (v,t1)) in
  let lParams := firstn numParams bs in
  let mb := translateIndMatchBody numParams allInds  tind cs v srt caseTyLams 
    (map (vterm∘fst) lParams) in
  let lamB : STerm := mkLamL [(v,t1); (vprime v, t2)] mb in
  fold_right (transLam translate) lamB bs.


End trans.


Import MonadNotation.
Open Scope monad_scope.


Require Import matchR. (* shadows Coq.Init.Datatypes.list *)
Require Import List. 

Run TemplateProgram (printTermSq "Vec").

Definition vBool  (C:Set) (n : nat)
  (vl : Vec C n) : bool :=
match vl return bool with
| vnil _ =>  false
| vcons _ n' hl tl =>  true
end.

Run TemplateProgram (printTermSq "vBool").
Run TemplateProgram (printTermSq "Vec").

(*
Inductive t1 : Set :=
with t2 : Set :=.

Definition t12 : Set := (t1*t2).

Run TemplateProgram (printTermSq "t12").
*)

(*
Fixpoint convertHeadPiToLam (s: STerm) : (STerm -> STerm) * (list V) :=
match s with
| mkPi nm A B => let (r,l) := (convertHeadPiToLam B) in ((fun t=> mkLam nm A (r t)), nm::l)
| _ => (id,[])
end.
*)





Definition genParam (piff: bool) (b:bool) (id: ident) : TemplateMonad unit :=
  id_s <- tmQuoteSq id true;;
(*  _ <- tmPrint id_s;; *)
  match id_s with
  Some (inl t) => 
    let t_R := (translate piff t) in
    trr <- tmReduce Ast.all t_R;;
    tmPrint trr  ;;
    trrt <- tmReduce Ast.all (fromSqNamed t_R);;
    tmPrint trrt  ;;
     if b then (@tmMkDefinitionSq (String.append id "_RR")  t_R) else (tmReturn tt)
  | _ => ret tt
  end.

Definition genParamInd (piff: bool) (b:bool) (id: ident) : TemplateMonad unit :=
  id_s <- tmQuoteSq id true;;
(*  _ <- tmPrint id_s;; *)
  match id_s with
  Some (inl t) => ret tt
  | Some (inr t) =>
    let (np,ones) := (t: simple_mutual_ind STerm SBTerm) in
    let is := seq 0 (length ones) in
    let inds := map (fun n => mkInd id n) is in
      let tr: list STerm := map (translateInd false (length np) inds) (combine inds ones) in
      match tr with
      h::_ =>
      if b then (tmMkDefinitionSq (indTransName (mkInd id 0)) h) else
        (trr <- tmReduce Ast.all tr;; tmPrint trr)
      | [] => ret tt
      end
  | _ => ret tt
  end.

(*
    match snd t with
    | h::_ => let tr: STerm := translateInd false 0%nat (mkInd id 0) (snd h) in
(*      if b then (tmMkDefinitionSq (indTransName (mkInd id 0)) tr) else *)
        (trr <- tmReduce Ast.all tr;; tmPrint trr)
    | [] => ret tt
    end
*)
Locate Vec.

Declare ML Module "paramcoq".

Parametricity Recursive ids.

Definition appTest  := fun (A : Set) (B: forall A, Set) (f: (forall a:A, B a)) (a:A)=>
 f a.

Let mode := false.

(*
Definition xxx (n:nat) :Prop :=
match n with
| O => True
| S _ => True
end.

*)

Run TemplateProgram (genParamInd mode true "Coq.Init.Datatypes.nat").
(* Run TemplateProgram (genParamInd mode true "nat"). Fails *)
Eval compute in Coq_Init_Datatypes_nat_RR0.
(*
     = fun H _ : nat => match H with
                        | 0%nat => True
                        | S _ => True
                        end
     : nat -> nat -> Prop
*)

Run TemplateProgram (printTermSq "ReflParam.matchR.vAppend").

Run TemplateProgram (genParamInd mode true "ReflParam.matchR.Vec").
Run TemplateProgram (printTermSq "ReflParam.matchR.Vec").
Print ReflParam_matchR_Vec_RR0.
(*
ReflParam_matchR_Vec_RR0 = 
fun (C C₂ : Set) (_ : (fun H H0 : Set => H -> H0 -> Prop) C C₂) 
  (H H0 : nat) (_ : Coq_Init_Datatypes_nat_RR0 H H0) (H1 : Vec C H) 
  (_ : Vec C₂ H0) => match H1 with
                     | vnil _ => True
                     | vcons _ _ _ _ => True
                     end
     : forall C C₂ : Set,
       (fun H H0 : Set => H -> H0 -> Prop) C C₂ ->
       forall H H0 : nat, Coq_Init_Datatypes_nat_RR0 H H0 -> Vec C H -> Vec C₂ H0 -> Prop
*)

Run TemplateProgram (genParam mode true "appTest").

Eval compute in appTest_RR.
(* how does the type of f_R have BestR? Template-coq quotes the type in a lambda,
even if the type is a mkPi, whose sort can be easily computed from its subterms
that are guaranteed to be tagged. *)
Definition ids_RN : forall (A₁ A₂ : Set) (A_R : BestRel A₁ A₂ ) (x₁ : A₁) (x₂ : A₂),
       R A_R x₁ x₂ -> R A_R x₁ x₂
:= 
fun (A₁ A₂ : Set) (A_R :BestRel A₁ A₂) (x₁ : A₁) (x₂ : A₂) 
  (x_R : BestR A_R x₁ x₂) => x_R.

Run TemplateProgram (printTerm "ids").

Run TemplateProgram (printTerm "ids_RN").



Run TemplateProgram (genParam mode true "idsT").
Eval compute in idsT_RR.

Print idsT.

Parametricity idsT.

(* Given f: some Pi Type, prove that the new theorem implies the old *)
Eval vm_compute in idsT_RR.


Run TemplateProgram (genParam mode true "ids").
Eval compute in ids_RR.

Definition idsTT  := fun A : Set => forall a:A, A.

Parametricity Recursive idsTT.

Run TemplateProgram (genParam mode true "idsTT").
Eval compute in idsTT_RR.

Print idsTT_RR.

Definition s := Set.
Run TemplateProgram (genParam mode  true "s").

Eval compute in s_RR.

Definition propIff : Type := forall A:Set, Prop.

Run TemplateProgram (genParam mode true "propIff").

Eval compute in propIff_RR.

Definition propIff2 : Prop := forall A:Prop, A.

Run TemplateProgram (genParam mode  true "propIff2").

Run TemplateProgram (printTerm "propIff2").

Eval compute in propIff2_RR.

Goal propIff2_RR = fun _ _ => True.
unfold propIff2_RR.
Print PiTSummary.
unfold PiATypeBSet. simpl.
Print PiATypeBSet.
Abort.

Definition p := Prop.
Run TemplateProgram (genParam mode  true "p").

Eval compute in p_RR.

Section Impred.
Variable A1 : Prop.
Variable B1 : Prop->Prop.
Variable A2: Prop.
Variable B2 : forall _:Prop, Prop.

Let PiTP1 := forall (A1 : Prop), B1 A1.
Let PiTP2 := forall (A2 : Prop), B2 A2.

Variable A_R: BestRelP A1 A2.
 
Check (eq_refl: let idp: Prop->Prop := id in propIff2 = forall A:Prop, idp A).

Lemma PiTP_R : BestRelP PiTP1 PiTP2.
compute in A_R.
Abort.

Check PiTSummary.

Parametricity Recursive propIff2.

Eval compute in propIff2_R. (* In Prop *)



Definition propIff2Ideal : BestRelP propIff2 propIff2.
unfold propIff2. unfold BestRelP. tauto.
Defined.


Eval compute in (@p_RR propIff2 propIff2).
Section Temp.
Variable A:Type.
Variable B:A->Prop.
Variable C:Set->Prop.
Variable D:Type->Prop.
Check ((forall (a:A), B a):Prop).
Check ((forall (a:Set), C a):Prop).
(* we will not be able to handle the case below because the relations for type 
dont have goodness props *)
Check ((forall (a:Type), D a):Prop).
End Temp.
Fail Check (propIff2_RR : @p_RR propIff2 propIff2).

(*
Fails because the parametricity plugin chooses different names when compiling interactively
and when compiling via coqc
Print idsTT_R.
Check (eq_refl : ids_RR=ids_RN).
Print idsT_R.
*)


(*
The type of forall also depends on the type of B

Variable A:Type.
Variable B:A->Set.
Check (forall a:A, B a):Type.
Fail Check (forall a:A, B a):Set.
*)

(*
Quote Definition nt := (nat:Type (*this is reified as cast*)).
Print nt.
*)