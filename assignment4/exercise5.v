Variables A: Set.
Variables P Q: A -> Prop.
Theorem exercise5:
    (forall x, (P x /\ Q x)) <-> ((forall x, P x) /\ (forall x, Q x)).
Proof.
    split. 
    intros.
    split.
    apply H.
    apply H.
    intros.
    destruct H as [Ha  Hb].
    split.
    apply Ha.
    apply Hb.
Qed.
