Theorem nat_ind: forall P : nat -> Prop,
  P 0 -> (forall n: nat, P n -> P (S n)) -> forall n: nat, P n.
Proof.
  intros P H0 Hrec n. cut (P n).
  - tauto.
  - elim n. apply H0. apply Hrec.
Qed.

Theorem plus_one_r : forall n: nat,
  n + 1 = S n.
Proof.
  apply nat_ind.
  - reflexivity.
  - intros. simpl. rewrite H. reflexivity.
Qed.

Inductive booltree : Type :=
  | bt_empty
  | bt_leaf (b : bool)
  | bt_branch (b : bool) (t1 t2 : booltree).

Check booltree_ind: forall (P: booltree -> Prop),
  P bt_empty -> (forall b: bool, P (bt_leaf b)) ->
  (forall (b: bool) (t1: booltree), P t1 -> 
    forall t2: booltree, P t2 -> P (bt_branch b t1 t2)) ->
  forall t: booltree, P t.

Inductive tree (X: Type): Type :=
  | leaf (x : X)
  | node (t1 t2 : tree X).

Check tree_ind: forall (X: Type) (P: tree X -> Prop),
  (forall x: X, P (leaf X x)) -> (forall t1: tree X, P t1 -> 
    forall t2: tree X, P t2 -> P (node X t1 t2)) ->
  forall t: tree X, P t.


Inductive le2 (n: nat) : nat -> Prop :=
  | le2_n : le2 n n
  | le2_S m (H: le2 n m): le2 n (S m).

Check le2_ind: forall (n: nat) (P: nat -> Prop),
  P n ->
  (forall m: nat, le2 n m -> P m -> P (S m)) ->
    forall n0: nat, le2 n n0 -> P n0.

Definition nat_ind2: forall (P: nat -> Prop),
  P 0 -> P 1 -> (forall n: nat, P n -> P (S (S n))) ->
  forall n: nat, P n :=
    fun P => fun P0 => fun P1 => fun PSS =>
      fix f (n: nat) := match n with
                       | 0 => P0
                       | 1 => P1
                       | S (S ns) => PSS ns (f ns)
                       end.

Lemma even_ev: forall n, 
  even n = true -> ev n.
Proof.
  intros.
  induction n as [ | | ns ] using nat_ind2.
  - apply ev_0.
  - simpl in H.
    inversion H.
  - simpl in H.
    apply ev_SS.
    apply IHn'.
    apply H.
Qed.