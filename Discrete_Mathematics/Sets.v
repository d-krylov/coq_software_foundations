Module AxiomaticSets.

Parameter set : Type -> Type.

Parameter Empty: forall {X: Type}, set X.

Parameter Universe: forall {X: Type}, set X.

Parameter Spec : forall {X: Type}, (X -> Prop) -> set X.

Parameter Member : forall {X: Type}, X -> set X -> Prop.

Axiom extensionality : forall X (S1 S2: set X),
  (forall x, Member x S1 <-> Member x S2) <-> S1 = S2.

Axiom inclusion_exclusion : forall {X} (S: set X) x,
  Member x S \/ not (Member x S).

Axiom member_empty : forall X (x: X),
  not (Member x Empty).

Axiom member_universe: forall X (x: X),
  Member x Universe.

Axiom member_spec_P : forall X (P : X -> Prop),
  forall x, Member x (Spec P) -> P x.

Axiom P_member_spec : forall X (P : X -> Prop),
  forall x, P x -> Member x (Spec P).

Definition Singleton {X: Type} (x: X): set X := Spec (fun y => x = y).

Definition Union {X: Type} (S1 S2: set X): set X :=
  Spec (fun x => Member x S1 \/ Member x S2).

Definition Intersection {X: Type} (S1 S2: set X): set X :=
  Spec (fun x => Member x S1 /\ Member x S2).

Definition Difference {X: Type} (S1 S2: set X): set X :=
  Spec (fun x => Member x S1 /\ not (Member x S2)).

Definition Complement {X: Type} (S: set X): set X :=
  Spec (fun x => not (Member x S)).

Lemma member_singleton: forall X (x y: X),
  Member x (Singleton y) <-> x = y.
Proof.
  intros. split.
  - intros. apply member_spec_P in H. rewrite H. reflexivity.
  - intros. apply P_member_spec. rewrite H. reflexivity.
Qed.

Lemma member_union: forall X (S1 S2: set X) (x : X),
  Member x (Union S1 S2) <-> Member x S1 \/ Member x S2.
Proof.
  intros. split.
  - intros. apply member_spec_P in H. apply H.
  - intros. apply P_member_spec. apply H.
Qed.

Lemma member_intersection : forall X (S1 S2: set X) (x: X),
  Member x (Intersection S1 S2) <-> Member x S1 /\ Member x S2.
Proof.
  intros. split.
  - intros. apply member_spec_P in H. apply H.
  - intros. apply P_member_spec. apply H.
Qed.

Lemma member_difference: forall X (S1 S2 : set X) (x : X),
  Member x (Difference S1 S2) <-> Member x S1 /\ not (Member x S2).
Proof.
  intros. split.
  - intros. apply member_spec_P in H. apply H.
  - intros. apply P_member_spec. apply H.
Qed.

Definition subset {X : Type} (S1 S2 : set X): Prop :=
  forall x, Member x S1 -> Member x S2.

Lemma empty_subset: forall X (S: set X),
  subset Empty S.
Proof.
  unfold subset. intros. Admitted.

Definition injective {A B : Type} (f: A -> B): Prop :=
  forall x y: A, f x = f y -> x = y.

Definition surjective {A B: Type} (f: A -> B): Prop :=
  forall y, exists x, f x = y.

Definition bijective {A B : Type} (f: A -> B): Prop :=
  injective f /\ surjective f.

Definition same_cardinality (X Y: Type): Prop :=
  exists f: X -> Y, bijective f.
Admitted.

Lemma bool_nat_cardinality: not (same_cardinality bool nat).
Proof.
  unfold not. intros [f [Hi Hs]].
  Admitted.


Definition countable (X: Type): Prop :=
  (exists f: X -> nat, injective f) \/
  (exists f: nat -> X, surjective f).
