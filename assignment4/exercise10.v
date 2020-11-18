Variables A: Set.
Variables P Q: A -> Prop.
Theorem example5 :
        (forall x: A, (P x -> ~Q x)) -> ~(exists x: A, (P x /\ Q x)).
    Proof.
        unfold not.
        intros.
        destruct H0 as [a p].
        destruct p as [p1 p2].
        apply H in p1. 
        apply p1.
        apply p2.
    Qed.
