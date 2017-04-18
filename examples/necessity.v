Definition ExistsB (b:bool) (T:Type) (p: T -> bool):=  exists t:T, p t = b.
  
Definition fType := forall (T:Set) (p: T -> bool), ExistsB true T p * ExistsB false T p.


(* This is logicall equivalent to the AnyRel translation of ExistsTrue. We
have simplified it a bit, just for better readability.*)
Inductive ExistsBR (b:bool) {T1 T2: Set} (R: T1 -> T2 -> Prop)
          {p1: T1-> bool} {p2: T2-> bool} (pR : forall t1 t2, R t1 t2 -> p1 t1 = p2 t2)
  : forall (dp1 : ExistsB b T1 p1) (dp2 : ExistsB b T2 p2), Prop :=
| exTrueR : forall (t1: T1) (t2: T2) dp1 dp2,
    R t1 t2 ->
    ExistsBR b R pR (ex_intro _ t1 dp1) (ex_intro _ t2 dp2).

(*
Definition IffProps {A B : Prop} (_: A -> B -> Prop)  := (A <-> B).
 *)

Definition TotalHeteroRelHalf {T1 T2 : Type} (R: T1 -> T2 -> Prop) : Type :=
  (forall (t1:T1), ex (R t1)).

Definition ExistsTrueRIso (b:bool) {T1 T2: Set} (R: T1 -> T2 -> Prop)
           {p1: T1-> bool} {p2: T2-> bool} (pR : forall t1 t2, R t1 t2 -> p1 t1 = p2 t2)
           (dp1 : ExistsB b T1 p1) (dp2 : ExistsB b T2 p2)
  :=
  ExistsBR b R pR dp1 dp2 /\ (ExistsB b T1 p1 <->  ExistsB b T2 p2).

Section TotalityNec.
  Variable f:fType.
  
(* In the syle of reverse mathematics (https://en.wikipedia.org/wiki/Reverse_mathematics), 
we assume the result and prove the assumptions that are
supposed to be necessary. This is the reverse direction of what we did in Sec 3.
of the paper. *)
  Hypothesis fR: forall  {T1 T2: Set} (R: T1 -> T2 -> Prop)
                    {p1: T1-> bool} {p2: T2-> bool} (pR : forall t1 t2, R t1 t2 -> p1 t1 = p2 t2)
    , ExistsTrueRIso true R pR (fst (f T1 p1)) (fst (f T2 p2))
  /\ ExistsTrueRIso false R pR (snd (f T1 p1)) (snd (f T2 p2)).

  (* we only show one side of the proof. *)
  Lemma totalAssumptionNecessary (T1 T2: Set) (R: T1 -> T2 -> Prop) 
     {p1: T1-> bool} {p2: T2-> bool} (pR : forall t1 t2, R t1 t2 -> p1 t1 = p2 t2) :
    TotalHeteroRelHalf R.
  Proof using.
    intros ?. specialize (fR T1 T2 R _ _ pR ).
    apply proj1 in fR.
    remember (p1 t1) as pt1. symmetry in Heqpt1. destruct pt1.
-    destruct fR as [fRa fRIff]. clear fR.
     apply proj1 in fRIff.
     specialize (fRIff (ex_intro _ t1 Heqpt1)).
     destruct fRIff. exists x. inversion fRa.
  Abort.
    
