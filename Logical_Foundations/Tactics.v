From Coq Require Import List. Import ListNotations.

(* Exercise: 3 stars, standard, optional (trans_eq_exercise) *)

Definition minustwo (n : nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S ns) => ns
  end.

Example trans_eq_exercise: forall (n m o p : nat),
  m = (minustwo o) -> (n + p) = m -> (n + p) = (minustwo o).
Proof.
  intros. transitivity m. apply H0. apply H.
Qed.

(* Exercise: 3 stars, standard (injection_ex3) *)

Example injection_ex3 : forall (X: Type) (x y z : X) (l j: list X),
  x :: y :: l = z :: j -> j = z :: l -> x = y.
Proof.
  intros. injection H. intros. rewrite H0 in H1. injection H1.
  intros. rewrite H2. rewrite H3. reflexivity.
Qed.

(* Exercise: 1 star, standard (discriminate_ex3) *)

Example discriminate_ex3: forall (X: Type) (x y z: X) (l j: list X),
  x :: y :: l = [] -> x = z.
Proof.
  intros. discriminate H.
Qed.

(* Exercise: 3 stars, standard, especially useful (plus_n_n_injective) *)

Theorem plus_n_n_injective: forall n m,
  n + n = m + m -> n = m.
Proof.
  intros. Admitted.


Theorem combine_split : forall X Y (l: list (X * Y)) l1 l2,
  split l = (l1, l2) -> combine l1 l2 = l.
Proof.
  intros. Admitted.