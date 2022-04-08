(* Exercise: 2 stars, standard (and_exercise) *)

Example and_exercise: forall n m: nat, 
  n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros. induction n.
  - simpl in H. split. 
    + reflexivity.
    + apply H.
  - split. discriminate. discriminate.
Qed.

(* Exercise: 1 star, standard, optional (proj2) *)

Lemma proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  intros. destruct H. apply H0.
Qed.