Module BoolPlayground.

Inductive bool_ : Type :=
  | true
  | false.

Definition negb (b:bool_) : bool_ :=
  match b with
  | true => false
  | false => true
end.

Definition andb (b1: bool_) (b2: bool_) : bool_ :=
  match b1 with
  | true => b2
  | false => false
end.

Definition orb (b1: bool_) (b2: bool_): bool_ :=
  match b1 with
  | true => true
  | false => b2
end.

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

(* Exercise: 1 star, standard (nandb) *)

Definition nandb (b1: bool_) (b2: bool_) : bool_ :=
  match b1 with
  | true => negb b2
  | false => true
end.

Example test_nandb1: (nandb true false) = true.
Proof. reflexivity. Qed.

Example test_nandb2: (nandb false false) = true.
Proof. reflexivity. Qed.

Example test_nandb3: (nandb false true) = true.
Proof. reflexivity. Qed.

Example test_nandb4: (nandb true true) = false.
Proof. reflexivity. Qed.

(* Exercise: 1 star, standard (andb3) *)

Definition andb3 (b1: bool_) (b2: bool_) (b3: bool_): bool_ :=
  match b1 with
  | true => andb b2 b3
  | false => false
end.

Example test_andb31: (andb3 true true true) = true.
Proof. reflexivity. Qed.

Example test_andb32: (andb3 false true true) = false.
Proof. reflexivity. Qed.

Example test_andb33: (andb3 true false true) = false.
Proof. reflexivity. Qed.

Example test_andb34: (andb3 true true false) = false.
Proof. reflexivity. Qed.

End BoolPlayground.

Module NatPlayground.

Inductive nat_ : Type :=
  | O
  | S (n : nat_).

Fixpoint plus (n m: nat_): nat_ :=
  match n with
  | O => m
  | S n_ => S (plus n_ m)
end.

Fixpoint mult (n m : nat_) : nat_ :=
  match n with
  | O => O
  | S n_ => plus m (mult n_ m)
end.

Fixpoint minus (n m: nat_) : nat_ :=
  match n, m with
  | O , _ => O
  | S _ , O => n
  | S n_, S m_ => minus n_ m_
end.

End NatPlayground.

(* Exercise: 1 star, standard (factorial) *)

Fixpoint factorial (n: nat): nat :=
  match n with
  | O => 1
  | S n_ => mult (S n_) (factorial n_)
end.

Example test_factorial1: (factorial 3) = 6.
Proof. reflexivity. Qed.

Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. reflexivity. Qed.


Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m_ => false
         end
  | S n_ => match m with
            | O => false
            | S m_ => eqb n_ m_
            end
end.

Notation "x =? y" := (eqb x y) (at level 70): nat_scope.

(* Exercise: 1 star, standard (plus_id_exercise) *)

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o H1 H2. rewrite H1. rewrite H2.
  reflexivity.
Qed.

(* Exercise: 1 star, standard (mult_n_1) *)

Check mult_n_O.
Check mult_n_Sm.

Theorem mult_n_1 : forall p : nat,
  p * 1 = p.
Proof.
  intros. 
  rewrite <- mult_n_Sm.
  rewrite <- mult_n_O.
  reflexivity.
Qed.

Theorem negb_involutive: forall b: bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b eqn:E.
  - reflexivity.
  - reflexivity. Qed.


 