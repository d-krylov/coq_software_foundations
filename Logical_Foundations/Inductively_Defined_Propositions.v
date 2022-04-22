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
    + apply even_sum. apply IHeven_new1. apply IHeven_new2.
Qed. 

(* Exercise: 3 stars, advanced, especially useful (ev_ev__ev) *)

Theorem ev_plus_plus : forall n m p,
  even (n + m) -> even (n + p) -> even (m + p).
Proof.
  intros. 
  Admitted.
 
End EvenPlayground.


Module LessPlayground.

Inductive Less : nat -> nat -> Prop :=
  | Less_n (n : nat) : Less n n
  | Less_S (n m : nat) (H : Less n m) : Less n (S m).

Notation "n <= m" := (Less n m).

Lemma le_trans: forall m n o,
  m <= n -> n <= o -> m <= o.
Proof.
  intros. induction H0.
  - apply H.
  - apply Less_S. apply IHLess. apply H.
Qed.

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  intros. induction n.
  - apply Less_n.
  - apply Less_S. apply IHn.
Qed.

Theorem n_le_m__Sn_le_Sm: forall n m,
  n <= m -> S n <= S m.
Proof.
  intros. induction H.
  - apply Less_n.
  - apply Less_S. apply IHLess.
Qed.

Theorem Sn_le_Sm__n_le_m: forall n m,
  S n <= S m -> n <= m.
Proof.
  intros. Admitted.

Theorem lt_ge_cases: forall n m,
  n < m \/ n >= m.
Proof.
  intros. induction m. Admitted.

Theorem le_plus_l: forall a b,
  a <= a + b.
Proof.
  intros. induction b.
  - rewrite Nat.add_0_r. apply Less_n.
  - rewrite <- plus_n_Sm. apply Less_S. apply IHb.
Qed.

Theorem plus_le: forall n1 n2 m,
  n1 + n2 <= m -> n1 <= m /\ n2 <= m.
Proof.
  intros. split.
  - apply le_trans with (n1 + n2). apply le_plus_l. apply H.
  - apply le_trans with (n2 + n1). apply le_plus_l. rewrite Nat.add_comm. apply H.
Qed.

Theorem add_le_cases: forall n m p q,
  n + m <= p + q -> n <= p \/ m <= q.
Proof.
  intros. induction n.
  - left. apply O_le_n.
  - simpl in H. apply plus_le with (1) (n + m) (p + q) in H. destruct H.
    Admitted.


Theorem plus_le_compat_l: forall n m p,
  n <= m -> p + n <= p + m.
Proof.
  intros. induction n.
  - rewrite Nat.add_0_r. apply le_plus_l.
  - rewrite <- plus_n_Sm. 
Admitted.

Theorem plus_le_compat_r: forall n m p,
  n <= m -> n + p <= m + p.
Proof.
  Admitted.

Theorem le_plus_trans: forall n m p,
  n <= m -> n <= m + p.
Proof.
   Admitted.

Theorem n_lt_m__n_le_m: forall n m,
  n < m -> n <= m.
Proof.
  Admitted.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m -> n1 < m /\ n2 < m.
Proof.
 Admitted.

Theorem leb_complete : forall n m,
  n <=? m = true -> n <= m.
Proof.
 Admitted.

Theorem leb_correct : forall n m,
  n <= m -> n <=? m = true.
Proof.
  Admitted.

Theorem leb_true_trans : forall n m o,
  n <=? m = true -> m <=? o = true -> n <=? o = true.
Proof.
 Admitted.
 

End LessPlayground.



