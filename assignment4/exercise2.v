Theorem example_3: forall P Q R:Prop,
       P /\ (Q \/ R) <-> (P /\ Q) \/ (P /\ R).
Proof.
    intros.
    split.
    intros.
    destruct H as [Ha  Hb].
    destruct Hb as [Hp | Hq].
    left.
    split.
    apply Ha.
    apply Hp.
    right.
    split.
    apply Ha.
    apply Hq.
    intros.
    destruct H as [Hp | Hq].
    destruct Hp as [Ha  Hb].
    split.
    apply Ha.
    left.
    apply Hb.
    destruct Hq as [Ha  Hb].
    split.
    apply Ha.
    right.
    apply Hb.
Qed.