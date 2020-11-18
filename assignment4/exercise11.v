Variables A: Set.
Variables P Q: A -> Prop.
Theorem example5 :
        (forall x: A, (P x -> Q x)) /\ (exists x: A, P x) -> (exists x: A, Q x).
    Proof.
        intros.
        destruct H as [H1 H2].
        destruct H2 as [a p].
        exists a.
        apply H1 in p. 
        apply p.
    Qed.
