Definition relation (X: Type) := X -> X -> Prop.

Definition partial_function {X: Type} (R: relation X) :=
  forall x y1 y2: X, R x y1 -> R x y2 -> y1 = y2.

Theorem next_nat_partial_function :
  partial_function next_nat.