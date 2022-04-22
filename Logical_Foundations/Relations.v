Definition relation (X: Type) := X -> X -> Prop.

Definition partial_function {X: Type} (R: relation X) :=
  forall x y1 y2: X, R x y1 -> R x y2 -> y1 = y2.

Inductive next_nat : nat -> nat -> Prop :=
  | nn n : next_nat n (S n).

Theorem next_nat_partial_function:
  partial_function next_nat.
Proof.
  unfold partial_function. intros.
  inversion H. inversion H0.
  reflexivity.
Qed.

Theorem le_not_a_partial_function:
  not (partial_function le).
Proof.