From Coq Require Import List. Import ListNotations.
From Coq Require Import Sorting.Permutation.
From Coq Require Import Arith.

Fixpoint product_one {X Y: Type} (x : X) (l : list Y) : list (X * Y) :=
  match l with
  | nil => nil
  | r :: rs => (x, r) :: product_one x rs
end.

Fixpoint product {X Y: Type} (l1 : list X) (l2 : list Y) : list (X * Y) :=
  match l1 with 
  | nil => nil
  | x :: ls => (product_one x l2) ++ (product ls l2)
end.

Example product_example2: length (product [1;2;3] [true;false]) = 6.
Proof. reflexivity. Qed.

Lemma product_one_length: forall X Y (x: X) (l: list Y),
  length (product_one x l) = length l.
Proof.
  intros. induction l.
  - reflexivity.
  - simpl. rewrite IHl. reflexivity.
Qed.

Lemma product_times : forall X Y (l1 : list X) (l2 : list Y),
  length (product l1 l2) = length l1 * length l2.
Proof. 
  intros. induction l1.
  - reflexivity.
  - simpl. rewrite app_length. rewrite IHl1. 
    rewrite product_one_length.
    reflexivity.
Qed.

Fixpoint factorial (n: nat): nat :=
  match n with
  | 0 => 1
  | S ns => n * factorial ns
end.

Fixpoint everywhere {A: Type} (a: A) (ls: list A): list (list A) :=
  match ls with
  | [] => [[a]] 
  | h :: t => (a :: ls) :: (map (fun ts => h :: ts) (everywhere a t))
end.

Fixpoint concat_map {A B: Type} (f: A -> list B) (l: list A): list B :=
  match l with
  | [] => []
  | a :: ls => f a ++ concat_map f ls
end.

Fixpoint permutations {A: Type} (ls: list A): list (list A) :=
  match ls with
  | [] => [[]] 
  | h :: t => concat_map (everywhere h) (permutations t)
end.

Lemma In_concat_map: forall (A B: Type) (f: A -> list B) (l : list A) (y : B),
  In y (concat_map f l) -> (exists x : A, In y (f x) /\ In x l).
Proof.
  intros. induction l.
  - simpl in H. inversion H.
  - simpl in H. apply in_app_or in H. destruct H eqn:Eq.
    + exists a. split. apply i. simpl. left. reflexivity.
    + destruct IHl. apply i. destruct H0. exists x. split.
      apply H0. simpl. right. apply H1.
Qed.
 
Print Permutation.    

Lemma everywhere_perm : forall A (l1 l2 : list A) (x : A),
  In l2 (everywhere x l1) -> Permutation (x :: l1) l2.
Proof.
  intros. induction l2.
  - intros. give_up.
  - 

Theorem permutations_complete : forall A (l1 l2 : list A),
  In l1 (permutations l2) -> Permutation l1 l2.
Proof.
  intros. Admitted.

Lemma In_everywhere_length: forall A (a: A) (l perm: list A),
  In perm (everywhere a l) -> length perm = S (length l).
Proof.
  intros. Admitted.


Lemma length_concat_map: forall A B (f: A -> list B) (l: list A) n,
  (forall y, In y l -> length (f y) = n) -> length (concat_map f l) = n * length l.
Proof.
Admitted.

Lemma length_permutation: forall A n (l: list A),
  length l = n -> forall y, In y (permutations l) -> length y = n.
Proof.
  Admitted.

Lemma permutation_length: forall A (l1 l2: list A) (a: A),
  In l2 (permutations l1) -> length (everywhere a l2) = S (length l1).
Proof.
  Admitted.

Lemma permutations_length: forall A (l: list A) n,
  length l = n -> length (permutations l) = factorial n.
Proof.
  Admitted.


Fixpoint choose (n m : nat) : nat :=
  match n, m with
  | _, O => 1
  | O, S ms => 0
  | S ns, S ms => choose ns (S ms) + choose ns ms
end.

Lemma choose_n_0: forall n : nat,
  choose n 0 = 1.
Proof.
  intros. induction n. reflexivity. reflexivity.
Qed.

Lemma choose_n_lt_m: forall n m : nat,
  n < m -> choose n m = 0.
Proof.
  Admitted.

Lemma choose_n_n: forall n: nat, 
  choose n n = 1.
Proof.
  induction n. reflexivity. simpl. rewrite IHn. rewrite choose_n_lt_m.
  reflexivity. apply Nat.lt_succ_diag_r. 
Qed.

Lemma choose_fact : forall m n: nat,
  choose (n + m) n * (factorial n * factorial m) = factorial (n + m).
Proof.
  intros. induction n. 
  - simpl. rewrite Nat.add_0_r. rewrite choose_n_0. rewrite Nat.mul_1_l. reflexivity.
  - simpl. 