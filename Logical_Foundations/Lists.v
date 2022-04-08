Require Import Arith.

Module NatProdPlayground.

Inductive natprod : Type :=
  | pair (n1 n2 : nat).

Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
end.

Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
end.

Notation "( x , y )" := (pair x y).

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x, y) => (y, x)
end.

(* Exercise: 1 star, standard (snd_fst_is_swap) *)

Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  intros. destruct p. reflexivity.
Qed.

(* Exercise: 1 star, standard, optional (fst_swap_is_snd) *)

Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
  intros. destruct p. reflexivity.
Qed.

End NatProdPlayground.

Module NatListPlayground.

Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h :: t => h :: (app t l2)
end.

Notation "x ++ y" := (app x y) (right associativity, at level 60).

(* Fixpoint nonzeros (l: natlist) : natlist *)

Fixpoint nonzeros (l: natlist) : natlist :=
  match l with
  | nil => nil
  | x :: ls  => if (x =? 0) then nonzeros ls
                else x :: nonzeros ls
end.

Example test_nonzeros: nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. reflexivity. Qed.

(* Exercise: 3 stars, advanced (alternate) *)

Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1, l2 with
  | nil, _ => l2
  | _, nil => l1
  | f :: ll, s :: rr => f :: s :: (alternate ll rr)
end.

Example test_alternate1: alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6]. 
Proof. reflexivity. Qed.

Example test_alternate2: alternate [1] [4;5;6] = [1;4;5;6].
Proof. reflexivity. Qed.

Example test_alternate3: alternate [1;2;3] [4] = [1;4;2;3].
Proof. reflexivity. Qed.

Example test_alternate4: alternate [] [20;30] = [20;30].  
Proof. reflexivity. Qed.

(* Exercise: 3 stars, standard, especially useful (bag_functions) *)

Definition bag := natlist.

Fixpoint count (v : nat) (s : bag) : nat :=
  match s with 
  | nil => 0
  | x :: ls => if (x =? v) then 1 + count v ls
               else count v ls
end.

Example test_count1: count 1 [1;2;3;1;4;1] = 3.
Proof. reflexivity. Qed.

Example test_count2: count 6 [1;2;3;1;4;1] = 0.
Proof. reflexivity. Qed.

Definition add (v : nat) (s : bag) : bag := v :: s.

(* Exercise: 3 stars, standard, optional (bag_more_functions) *)

Fixpoint remove_one (v : nat) (s : bag) : bag :=
  match s with
  | nil => nil
  | x :: ls => if (x =? v) then ls
               else x :: remove_one v ls
end.

Example test_remove_one1: count 5 ( remove_one 5 [2;1;5;4;1] ) = 0.
Proof. reflexivity. Qed.

Example test_remove_one2: count 5 ( remove_one 5 [2;1;4;1] ) = 0.
Proof. reflexivity. Qed.

Example test_remove_one3: count 4 ( remove_one 5 [2;1;4;5;1;4] ) = 2.
Proof. reflexivity. Qed.

Example test_remove_one4: count 5 ( remove_one 5 [2;1;5;4;5;1;4] ) = 1.
Proof. reflexivity. Qed.

Fixpoint remove_all (v: nat) (s: bag) : bag :=
  match s with
  | nil => nil
  | x :: ls => if (x =? v) then remove_all v ls
               else x :: remove_all v ls
end.

Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.

Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.

Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.

Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof. reflexivity. Qed.

(* Exercise: 2 stars, standard, especially useful (add_inc_count) *)

Theorem bag_theorem: forall (v: nat) (s: bag),
  count v (add v s) = count v s + 1.
Proof.
  intros. Admitted.

Theorem app_assoc : forall l1 l2 l3: natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros. induction l1.
  - reflexivity.
  - simpl. rewrite IHl1. reflexivity.
Qed.

Fixpoint rev (l: natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => rev t ++ [h]
end.

(* Exercise: 3 stars, standard (list_exercises) *)

Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.
Proof.
  intros. induction l.
  - reflexivity.
  - simpl. rewrite IHl. reflexivity.
Qed.

Theorem rev_app_distr: forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros. induction l1.
  - simpl. rewrite app_nil_r. reflexivity.
  - simpl. rewrite IHl1. rewrite app_assoc. reflexivity.
Qed.

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  intros. induction l.
  - reflexivity.
  - simpl. rewrite rev_app_distr. rewrite IHl. reflexivity.
Qed.

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  Admitted.

Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros. induction l1.
  - reflexivity.
  - simpl. destruct (n =? 0).
    + rewrite IHl1. reflexivity.
    + simpl. rewrite IHl1. reflexivity.
Qed.

(* Exercise: 2 stars, standard (eqblist) *)

Fixpoint eqblist (l1 l2 : natlist) : bool :=
  match l1, l2 with 
  | nil, nil => true
  | nil, x :: ls => false
  | x :: ls, nil => false
  | x :: ll, y :: rr => if (x =? y) then eqblist ll rr
                        else false
end.

Example test_eqblist1: (eqblist nil nil = true).
Proof. reflexivity. Qed.

Example test_eqblist2: eqblist [1;2;3] [1;2;3] = true.
Proof. reflexivity. Qed.

Example test_eqblist3: eqblist [1;2;3] [1;2;4] = false.
Proof. reflexivity. Qed.

Theorem eqblist_refl: forall l: natlist,
  true = eqblist l l.
Proof.
  intros. induction l.
  - reflexivity.
  - simpl. rewrite Nat.eqb_refl. apply IHl.
Qed.

(* Exercise: 1 star, standard (count_member_nonzero) *)

Theorem count_member_nonzero : forall (s : bag),
  1 <=? (count 1 (1 :: s)) = true.
Proof.
  intros. reflexivity.
Qed.

(* Exercise: 3 stars, advanced (remove_does_not_increase_count) *)

Theorem remove_does_not_increase_count: forall (s : bag),
  (count 0 (remove_one 0 s)) <=? (count 0 s) = true.
Proof.
  intros. induction s.
  - reflexivity.
  - simpl. destruct (n =? 0).
    + Admitted.

End NatListPlayground.