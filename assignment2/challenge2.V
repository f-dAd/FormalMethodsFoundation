Theorem exercise1: forall P Q R:Prop,
       (P -> Q) -> (~Q -> ~P).
Proof.
    unfold not.
    intros.
    apply H in H1.
    apply H0.
    apply H1.
Qed.