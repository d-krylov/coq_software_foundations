Require Import Arith.

Module EvenPlayground.

Inductive even : nat -> Prop :=
  | even_0 : even 0
  | even_SS (n : nat) (H : even n) : even (S (S n)).


(* Exercise: 1 star, standard (even_double) *)

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n_ => S (S (double n_))
end.

Theorem even_double : forall n,
  even (double n).
Proof.
  intros. induction n as [ | n IHn ].
  - apply even_0.
  - simpl. apply even_SS. apply IHn.
Qed. 

(* Exercise: 1 star, standard (inversion_practice) *)

Theorem SSSSev__even : forall n,
  even (S (S (S (S n)))) -> even n.
Proof.
  intros n H. 
  inversion H  as [ | n1 H1 ].
  inversion H1 as [ | n2 H2 ].
  apply H2.
Qed.

(* Exercise: 1 star, standard (ev5_nonsense) *)

Theorem ev5_nonsense :
  even 5 -> 2 + 2 = 9.
Proof.
  intros. inversion H as [ | n1 H1 ].
  inversion H1 as [ | n2 H2 ].
  inversion H2.
Qed.

(* Exercise: 2 stars, standard (even_sum) *)

Theorem even_sum : forall n m, 
  even n -> even m -> even (n + m).
Proof.
  intros. induction H as [ | n E IHH ].
  - apply H0.
  - simpl. apply even_SS. apply IHH.
Qed.

(* Exercise: 4 stars, advanced, optional (even_even_new) *)

Inductive even_new: nat -> Prop :=
  | even_new_0 : even_new 0
  | even_new_2 : even_new 2
  | even_new_add n m (Hn: even_new n) (Hm: even_new m) : even_new (n + m).

Theorem even_even_new: forall n, 
  even n <-> even_new n.
Proof.
  split.
  - intros. induction H.
    + apply even_new_0.
    + apply even_new_add with (n := 2) (m := n).
      * apply even_new_2.
      * apply IHeven.
  - intros. induction H.
    + apply even_0.
    + apply even_SS. apply even_0.
    + Admitted.


(* Exercise: 3 stars, advanced, especially useful (ev_ev__ev) *)

Theorem ev_plus_plus : forall n m p,
  even (n + m) -> even (n + p) -> even (m + p).
Proof.
  intros. 
  Admitted.
 
End EvenPlayground.