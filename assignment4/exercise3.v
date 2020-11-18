Variables A: Set.
Variables P Q: A -> Prop.
Theorem example_4:
    (forall x: A, ~P x  /\ Q x) -> (forall x: A, P x -> Q x).
Proof.
    intros H1 a H2.
    apply H1.
Qed.