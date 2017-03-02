Lemma iffInvert (A B B2: Prop): ((A/\B) <-> (A/\B2))  -> (B<->B2).
Proof.
intros.
Fail tauto.
Abort.


Lemma iffInvert (A B B2: Prop): ((A/\B) <-> (A/\B2))  -> (A->(B<->B2)).
Proof.
intros. tauto.
Qed.
