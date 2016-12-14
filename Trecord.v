Require Import SquiggleEq.list.
Require Import SquiggleEq.UsefulTypes.
Require Import common.

Module TyRel.
(*Prop is also considered a type here.*)
Inductive Props := Total | OneToOne | Irrel.

Global Instance deq : Deq Props.
Proof using.
  apply @deqAsSumbool.
  unfold DeqSumbool. intros. unfold DecidableSumbool.
  repeat decide equality.
Defined.

Arguments memberb {_} {_} x l.


Record GoodRel (T₁ T₂:Type) (select: list Props) :=
{
  R : T₁ -> T₂ -> Type;
  Rtot : if (memberb Total select) then TotalHeteroRel R else True;
  Rone : if (memberb OneToOne select) then oneToOne R else True;
  Rirrel : if (memberb Irrel select) then rellIrrUptoEq R else True;
}.

