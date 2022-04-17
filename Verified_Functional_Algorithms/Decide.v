Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".

From Coq Require Import Lia.

Module ScratchPad.

Inductive sumbool (A B : Prop) : Set :=
  | left : A -> sumbool A B
  | right : B -> sumbool A B.

Definition t1 := sumbool (3 < 7) (3 > 2).

Lemma less37: 3<7. 
Proof. lia. Qed.

Lemma greater23: 3>2. 
Proof. lia. Qed.

Definition v1a: t1 := left (3<7) (3>2) less37.

Notation "{ A } + { B }" := (sumbool A B) : type_scope.

End ScratchPad.

