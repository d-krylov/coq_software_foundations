From Coq Require Import List. Import ListNotations.
From Coq Require Import Arith.
From Coq Require Import Permutation.

Fixpoint select (x: nat) (l: list nat) : nat * list nat :=
  match l with
  | [] => (x, [])
  | h :: t => if x <=? h
              then let (j, ls) := select x t in (j, h :: ls)
              else let (j, ls) := select h t in (j, x :: ls)
end.

Fixpoint selsort (l : list nat) (n : nat) : list nat :=
  match l, n with
  | _ , O => [] 
  | [], _ => []
  | x :: r, S ns => let (y, rs) := select x r
                    in y :: selsort rs ns
end.

Example extra_fuel: selsort [3;1;4;1;5] 10 = [1;1;3;4;5].
Proof.
  simpl. reflexivity.
Qed.

Inductive sorted: list nat -> Prop :=
  | sorted_nil: sorted []
  | sorted_1: forall i, sorted [i]
  | sorted_cons: forall i j l, i <= j -> sorted (j :: l) -> sorted (i :: j :: l).

Definition is_a_sorting_algorithm (f: list nat -> list nat) := forall al,
  Permutation al (f al) /\ sorted (f al).

Lemma select_perm: forall x l y r,
  (y, r) = select x l -> Permutation (x :: l) (y :: r).
Proof.
  intros. induction l.
  - injection H. intros ->. intros ->. apply perm_skip. apply perm_nil.
  - inversion H. clear H. Admitted.

Lemma selsort_perm: forall n l,
  length l = n -> Permutation l (selsort l n).
Proof.

Lemma selection_sort_perm: forall l,
  Permutation l (selection_sort l).
Proof.

Lemma select_rest_length : forall x l y r,
  select x l = (y, r) -> length l = length r.
Proof.

Lemma select_fst_leq: forall al bl x y,
  select x al = (y, bl) -> y <= x.
Proof.