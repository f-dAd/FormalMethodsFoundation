Variables A: Set.
Variables P Q: A -> Prop.
Theorem example5 :
        (exists x: A, ~P x) -> ~(forall x: A, P x).
    Proof.
        unfold not.
        intros.
        destruct H as [a p].
        apply p.
        apply H0.
    Qed.
