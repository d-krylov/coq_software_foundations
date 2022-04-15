From Coq Require Import Sorting.Permutation.
From Coq Require Import List. Import ListNotations.

(* Exercise: 1 star (Permutation_refl) *)

Theorem Permutation_refl : forall A (l: list A),
  Permutation l l.
Proof.
  intros. induction l.
  - reflexivity.
  - apply perm_skip. apply IHl.
Qed.

(* Exercise: 1 star (Permutation_length) *)

Theorem Permutation_length : forall A (l1 l2: list A),
  Permutation l1 l2 -> length l1 = length l2.
Proof.
  intros. induction H.
  - reflexivity.
  - simpl. rewrite IHPermutation. reflexivity.
  - simpl. reflexivity.
  - rewrite IHPermutation1. rewrite IHPermutation2. reflexivity.
Qed.
  
(* Exercise: 1 star (Permutation_sym) *)

Lemma Permutation_sym : forall A (l1 l2: list A),
  Permutation l1 l2 -> Permutation l2 l1.
Proof.
  intros. induction H.
  - reflexivity.
  - apply perm_skip. apply IHPermutation.
  - apply perm_swap.
  - apply perm_trans with (l'). apply IHPermutation2. apply IHPermutation1.
Qed.

Inductive Forall {A : Type} (P : A -> Prop): list A -> Prop :=
  | Forall_nil: Forall P []
  | Forall_cons : forall (x: A) (l: list A), P x -> Forall P l -> Forall P (x :: l).

Theorem Forall_perm: forall {A} (f: A -> Prop) al bl,
  Permutation al bl -> Forall f al -> Forall f bl.
Proof.
  intros. induction H.
  - apply H0.
  - apply Forall_cons. inversion H0. apply H3. inversion H0. apply IHPermutation. apply H4.
  - apply Forall_cons. inversion H0. inversion H3. apply H6.
    apply Forall_cons. inversion H0. apply H2. inversion H0. inversion H3.
    apply H7.
  - Admitted.


