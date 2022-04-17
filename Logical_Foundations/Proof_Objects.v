Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".

Module And.

Inductive and (P Q : Prop) : Prop :=
  | conj : P -> Q -> and P Q.

Arguments conj [P] [Q].

Notation "P /\ Q" := (and P Q) : type_scope.

Theorem proj1 : forall P Q,
  P /\ Q -> P.
Proof.
  intros P Q HPQ. destruct HPQ as [HP HQ]. apply HP.
  Show Proof.
Qed.

Theorem proj2 : forall P Q,
  P /\ Q -> Q.
Proof.
  intros P Q HPQ. destruct HPQ as [HP HQ]. apply HQ.
  Show Proof.
Qed.


Definition conj_fact : forall P Q R, 
  P /\ Q -> Q /\ R -> P /\ R.

End And.


Module Or.

Inductive or (P Q : Prop) : Prop :=
  | or_introl : P -> or P Q
  | or_intror : Q -> or P Q.

Arguments or_introl [P] [Q].
Arguments or_intror [P] [Q].

Notation "P \/ Q" := (or P Q) : type_scope.

End Or.