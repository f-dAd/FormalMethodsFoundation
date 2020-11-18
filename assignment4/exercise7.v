Variables A: Set.
Variables P Q: A -> Prop.
Theorem example5 :
        (exists x: A, (~P x /\ Q x)) -> (exists x: A, (~P x /\ Q x)).
    Proof.
        unfold not.
        intros.
        destruct H as [a p].
        exists a.
        destruct p as [p1 p2]. 
        split.
        apply p1.
        apply p2.
    Qed.
