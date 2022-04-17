From Coq Require Import List.
From Coq Require Import Permutation.

Theorem Forall_perm: forall {A} (f: A -> Prop) al bl,
  Permutation al bl -> Forall f al -> Forall f bl.
Proof.
  intros. induction H.
  - apply H0.
  - apply Forall_cons. inversion H0. apply H3. apply IHPermutation.
    inversion H0. apply H4.
  - repeat apply Forall_cons. inversion H0. inversion H3. apply H6.
    inversion H0. apply H2. inversion H0. inversion H3.  apply H7.
  - apply IHPermutation2. apply IHPermutation1. apply H0.
Qed.

