Theorem example_1: forall P Q: Prop,
       ~(P \/ Q) -> ~P /\ ~Q.
    Proof.
        unfold not.
        intros.
        split.
        intros H1.
        apply H.
        left.
        apply H1.
        intros H1.
        apply H.
        right.
        apply H1.
    Qed.