Module ScratchPad.

Inductive sumbool (A B : Prop) : Set :=
  | left : A -> sumbool A B
  | right : B -> sumbool A B.

Definition t1 := sumbool (3 < 7) (3 > 2).




End ScratchPad.

