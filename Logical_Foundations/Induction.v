From LF Require Export Basics.

Theorem add_0_r : forall n: nat, 
  n + 0 = n.
Proof.
  induction n.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

(* Exercise: 2 stars, standard, especially useful (basic_induction) *)

Theorem mul_0_r: forall n: nat,
  n * 0 = 0.
Proof.
  intros. induction n.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros. induction n.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros. induction n.
  - rewrite add_0_r. reflexivity.
  - simpl. rewrite IHn. rewrite plus_n_Sm. reflexivity.
Qed.

Theorem add_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros. induction n.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

(* Exercise: 2 stars, standard (double_plus) *)

Fixpoint double (n: nat) :=
  match n with
  | O => O
  | S ns => S (S (double ns))
end.

Lemma double_plus: forall n, 
  double n = n + n.
Proof.
  intros. induction n.
  - reflexivity.
  - simpl. rewrite IHn. rewrite plus_n_Sm. reflexivity.
Qed.

(* Exercise: 2 stars, standard, optional (even_S) *)

Fixpoint even (n:nat): bool :=
  match n with
  | O => true
  | S O => false
  | S (S ns) => even ns
end.

Theorem even_S : forall n: nat,
  even (S n) = negb (even n).
Proof.
  intros. induction n.
  - reflexivity.
  - rewrite IHn. rewrite negb_involutive. reflexivity.
Qed.

(* Exercise: 3 stars, standard, especially useful (mul_comm) *)

Theorem add_shuffle3: forall n m p: nat,
  n + (m + p) = m + (n + p).
Proof.
  intros. rewrite add_assoc. rewrite add_assoc. 
  assert (H: n + m = m + n). 
  {
    rewrite add_comm. reflexivity.
  }
  rewrite H. reflexivity. 
Qed.

Lemma mul_n_Sm: forall n k,
  n * (S k) = n + n * k.
Proof.
  intros. induction n.
  - reflexivity. 
  - simpl. rewrite IHn. rewrite add_shuffle3. reflexivity.
Qed.

Theorem mul_comm: forall m n: nat,
  m * n = n * m.
Proof.
  intros. induction m.
  - rewrite mul_0_r. reflexivity.
  - simpl. rewrite mul_n_Sm. rewrite IHm. reflexivity.
Qed.

(* Exercise: 3 stars, standard, optional (more_exercises) *)

Fixpoint leb (n m: nat): bool :=
  match n with
  | O => true
  | S ns =>
    match m with
    | O => false
    | S ms => leb ns ms
    end
end.

Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.

Theorem leb_refl : forall n:nat,
  (n <=? n) = true.
Proof.
  intros. induction n.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Theorem zero_neqb_S: forall n: nat,
  0 =? (S n) = false.
Proof.
  intros. reflexivity.
Qed.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros. induction n.
  - reflexivity.
  - simpl. rewrite IHn. rewrite add_assoc. reflexivity.
Qed.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  intros. induction n. 
  - reflexivity.
  - simpl. rewrite mult_plus_distr_r. rewrite IHn. reflexivity.
Qed.
  
