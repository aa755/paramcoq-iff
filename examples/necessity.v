Definition ExistsTrue (T:Type) :=  exists t:T, True.
  
Definition fType := forall (T:Set), ExistsTrue T.


(* This is logicall equivalent to the AnyRel translation of ExistsTrue. We
have simplified it a bit, just for better readability.*)
Inductive ExistsTrueR {T1 T2: Set} (R: T1 -> T2 -> Prop)
  : forall (p1 : ExistsTrue T1) (p2 : ExistsTrue T2), Prop :=
| exTrueR : forall (t1: T1) (t2: T2) p1 p2,
  R t1 t2 ->  ExistsTrueR R (ex_intro _ t1 p1) (ex_intro _ t2 p2).

(*
Definition IffProps {A B : Prop} (_: A -> B -> Prop)  := (A <-> B).
 *)

Definition TotalHeteroRelHalf {T1 T2 : Type} (R: T1 -> T2 -> Prop) : Type :=
  (forall (t1:T1), ex (R t1)).

Definition ExistsTrueRIso {T1 T2: Set} (R: T1 -> T2 -> Prop)
           (p1 : ExistsTrue T1) (p2 : ExistsTrue T2) :=
  ExistsTrueR R p1 p2 /\ (ExistsTrue T1 <->  ExistsTrue T2).

Section TotalityNec.
  Variable f:fType.
  
(* In the syle of reverse mathematics (https://en.wikipedia.org/wiki/Reverse_mathematics), 
we assume the result and prove the assumptions that are
supposed to be necessary. This is the reverse direction of what we did in Sec 3.
of the paper. *)
  Hypothesis fR: forall (T1 T2: Set) (R: T1 -> T2 -> Prop), ExistsTrueRIso R (f T1) (f T2).

  (* we only show one side of the proof. *)
  Lemma totalAssumptionNecessary (T1 T2: Set) (R: T1 -> T2 -> Prop) :
    TotalHeteroRelHalf R.
  Proof using.
    intros ?. specialize (fR T1 T2 R). destruct fR as [fRa fRIff]. clear fR.
    apply proj1 in fRIff. specialize (fRIff (ex_intro _ t1 I)).
    destruct fRIff. exists x. destruct fRa.
  Abort.
    
