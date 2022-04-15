From Coq Require Import List. Import ListNotations.
From Coq Require Import Arith.
From Coq Require Import Permutation.

Fixpoint insert (i: nat) (l: list nat) :=
  match l with
  | [] => [i]
  | h :: t => if i <=? h then i :: h :: t else h :: insert i t
end.

Fixpoint sort (l: list nat): list nat :=
  match l with
  | [] => []
  | h :: t => insert h (sort t)
end.

Inductive sorted : list nat -> Prop :=
  | sorted_nil: sorted []
  | sorted_1 : forall x, sorted [x]
  | sorted_cons : forall x y l,
    x <= y -> sorted (y :: l) -> sorted (x :: y :: l).

Definition is_a_sorting_algorithm (f: list nat -> list nat) := forall al,
  Permutation al (f al) /\ sorted (f al).
 
Search (_ <= _ ).

(* Exercise: 3 stars, standard (insert_sorted) *)

Lemma insert_sorted: forall a l, 
  sorted l -> sorted (insert a l).
Proof.
  intros a l S. induction S; simpl.
  - apply sorted_1.
  - destruct (a <=? x) eqn:Eq.
    + apply sorted_cons. apply leb_complete in Eq. apply Eq.
      apply sorted_1.
    + apply leb_complete_conv in Eq. apply sorted_cons. apply Nat.lt_le_incl in Eq. apply Eq.
      apply sorted_1.
  - destruct (a <=? x) eqn:Eq.
    + apply sorted_cons. apply leb_complete in Eq. apply Eq.
      apply sorted_cons. apply H. apply S.
    + destruct (a <=? y) eqn:R.
      apply sorted_cons. apply leb_complete_conv in Eq. apply Nat.lt_le_incl in Eq. apply Eq.
      apply sorted_cons. apply leb_complete in R. apply R. apply S.
      apply sorted_cons. apply H. simpl in IHS. destruct (a <=? y) eqn:M.
      inversion R. apply IHS.
Qed.

Theorem sort_sorted: forall l, 
  sorted (sort l).
Proof.
  intros. induction l.
  - apply sorted_nil.
  - simpl. apply insert_sorted. apply IHl.
Qed.
  
Lemma insert_perm: forall x l,
  Permutation (x :: l) (insert x l).
Proof. 
  intros. induction l.
  - reflexivity.
  - simpl. destruct (x <=? a).
    + reflexivity.
    + apply perm_trans with (a :: x :: l).
      * apply perm_swap.
      * apply perm_skip. apply IHl.
Qed.

Theorem sort_perm: forall l, Permutation l (sort l).
Proof.
  intros. induction l.
  - apply perm_nil.
  - simpl. apply perm_trans with (a :: sort l).
    + apply perm_skip. apply IHl.
    + apply insert_perm.
Qed.

Theorem insertion_sort_correct:
    is_a_sorting_algorithm sort.
Proof.
  unfold is_a_sorting_algorithm. intros. split.
  - apply sort_perm.
  - apply sort_sorted.
Qed.