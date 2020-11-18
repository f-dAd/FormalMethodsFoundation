Variables A B: Set.
Variables P: A -> B -> Prop.
Theorem example5 :
        (exists x: A, exists y: B, (P x y)) -> (exists y: B, exists x: A, P x y).
    Proof.
        intros.
        destruct H as [a p].
        destruct p as [b p].
        exists b.
        exists a.
        apply p.
    Qed.
