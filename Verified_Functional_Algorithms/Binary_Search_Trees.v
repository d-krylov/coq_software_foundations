Require Import Arith.

Definition key := nat.

Inductive tree (V: Type): Type :=
  | E
  | T (l : tree V) (k : key) (v : V) (r : tree V).

Arguments E {V}.
Arguments T {V}.

Definition empty_tree {V: Type}: tree V := E.

Fixpoint insert {V: Type} (x: key) (v: V) (t: tree V): tree V :=
  match t with
  | E => T E x v E
  | T l y vs r => if x <? y then T (insert x v l) y vs r
                  else if y <? x then T l y vs (insert x v r)
                  else T l x v r
end.

Fixpoint ForallT {V : Type} (P: key -> V -> Prop) (t: tree V): Prop :=
  match t with
  | E => True
  | T l k v r => P k v /\ ForallT P l /\ ForallT P r
end.

Inductive BST {V: Type}: tree V -> Prop :=
  | BST_E : BST E
  | BST_T : forall l x v r,
      ForallT (fun y _ => y < x) l ->
      ForallT (fun y _ => y > x) r ->
      BST l ->
      BST r ->
      BST (T l x v r).

Search (_ <? _).  

Lemma ForallT_insert : forall (V: Type) (P: key -> V -> Prop) (t: tree V),
  ForallT P t -> forall (k : key) (v : V), P k v -> ForallT P (insert k v t).
Proof.
  intros. induction t.
  - simpl. split. apply H0. split. reflexivity. reflexivity.
  - simpl. destruct (k <? k0) eqn:Eq.
    + simpl. split. destruct H. apply H. destruct H. 
      split. apply IHt1. destruct H1. apply H1. destruct H1. apply H2.
    + destruct (k0 <? k) eqn:R.
      simpl. simpl in H. destruct H. split. apply H. destruct H1.
      split. apply H1. apply IHt2. apply H2. simpl. repeat split.
      apply H0. simpl in H. destruct H. destruct H1. apply H1.
      simpl in H. destruct H. destruct H1. apply H2.
Qed.

Theorem insert_BST : forall (V: Type) (k: key) (v: V) (t: tree V),
  BST t -> BST (insert k v t).
Proof.
  intros. induction H.
  - simpl. apply BST_T. reflexivity. reflexivity. apply BST_E. apply BST_E.
  - simpl. destruct (k <? x) eqn:Eq. 
    + apply BST_T. apply ForallT_insert. apply H. apply Nat.ltb_lt in Eq. apply Eq.
      apply H0. apply IHBST1. apply H2.
    + destruct (x <? k) eqn:B. apply BST_T. apply H. apply ForallT_insert.
      apply H0. apply Nat.ltb_lt in B. apply B. apply H1. apply IHBST2. apply BST_T.
       
    