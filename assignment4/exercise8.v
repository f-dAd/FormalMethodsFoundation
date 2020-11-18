Variables A: Set.
Variables P Q: A -> Prop.
Theorem example5 :
        (exists x: A, (P x \/ Q x)) <-> (exists x: A, P x) \/ (exists x: A, Q x).
    Proof.
        split.
        intros.
        destruct H as [a p].
        destruct p as [p1 | p2]. 
        left.
        exists a.
        apply p1.
        right.
        exists a.
        apply p2.
        intros.
        destruct H as [H1 | H2].
        destruct H1 as [a p].
        exists a.
        left.
        apply p.
        destruct H2 as [a p].
        exists a.
        right.
        apply p.
    Qed.
