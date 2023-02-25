Theorem excluded_middle_irrefutable: forall (P:Prop),
  ~ ~ (P \/ ~ P).
Proof.
  unfold not. intros P H.
  assert (H2 : P -> False).
  { intros p. apply (fun x => H (or_introl x)) in p. apply p. }
  apply H. apply or_intror. apply H2.
Qed.

