Variables A: Set.
Variables P Q R: A -> Prop.
Theorem example5 :
        (exists x: A, (P x /\ Q x)) /\ (forall x: A, (P x -> R x)) -> (exists x: A, R x /\ Q x).
    Proof.
        intros.
        destruct H as [H1 H2].
        destruct H1 as [a p].
        exists a.
        destruct p as [p1 p2].
        apply H2 in p1. 
        split.
        apply p1.
        apply p2.
    Qed.
