Theorem exercise1: forall P Q R:Prop,
      (P -> Q /\ R) -> ((P -> Q) /\ (P -> R)).
Proof.
    intros.
    split.
    intros.
    apply H in H0.
    inversion H0.
    apply H1.
    intros.
    apply H in H0.
    inversion H0.
    apply H2.
Qed.