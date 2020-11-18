Variables A: Set.
Variables P Q: A -> Prop.
Theorem example5 :
        (exists x: A, (~P x \/ Q x)) -> (exists x: A, (~P x /\ ~ Q x)).
    Proof.
        unfold not.
        intros.
        destruct H as [a p].
        exists a.
        split.
        intros.
        destruct p as [p1 | p2].  
        apply p1 in H.
        apply H.
intros.
        apply H.

     
        
        apply p2.
    Qed.
