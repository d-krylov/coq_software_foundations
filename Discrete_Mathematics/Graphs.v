From Coq Require Import List. Import ListNotations.

Fixpoint sum (ns: list nat): nat :=
  match ns with
  | [] => 0
  | n::ns => n + sum ns
end.

Fixpoint sum_map {X: Type} (f: X -> nat) (xs: list X) : nat :=
  match xs with
  | [] => 0
  | x::xs => f x + sum_map f xs
end.

Fixpoint remove_first {X : Type} (eq_dec : forall (x y: X), {x = y} + {x <> y}) 
                      (y: X) (xs: list X): list X :=
  match xs with
  | [] => []
  | (x::xs) => if eq_dec y x then xs else x::remove_first eq_dec y xs
end.

Inductive setlike {X: Type}: list X -> Prop :=
  | setlike_nil: setlike []
  | setlike_cons: forall (v: X) (vs: list X), 
      setlike vs -> not (In v vs) -> setlike (v::vs).

Module ExplicitType.

  Parameter X : Type.
  Axiom eq_dec_V : forall (x y : X), {x = y} + {x <> y}.

Inductive graph: list X -> list (X * X) -> Type :=
  | g_empty: graph [] []
  | g_vertex:
      forall (V: list X) (E: list (X * X)) (g: graph V E) (v: X),
        not (In v V) -> graph (v::V) E
  | g_arc:
      forall (V: list X) (E: list (X * X)) (g: graph V E) (src tgt: X),
      In src V ->
      In tgt V ->
      not (In (src, tgt) E) -> graph V ((src,tgt)::E).

Lemma vertex_setlike: forall {V: list X} {E: list (X * X)} (g: graph V E), 
  setlike V.
Proof.
  intros. induction g.
  - apply setlike_nil.
  - apply setlike_cons. apply IHg. apply n.
  - apply IHg.
Qed.

Fixpoint in_degree {V : list X} {E : list (X * X)} (v: X) (g: graph V E): nat :=
  match g with
  | g_empty => 0
  | g_vertex V_ E_ g_ _ _ => in_degree v g_
  | g_arc V_ E_ g_ _ tgt _ _ _ => if eq_dec_V v tgt
                                  then 1 + in_degree v g_
                                  else in_degree v g_
end.

Fixpoint out_degree {V: list X} {E: list (X * X)} (v: X) (g: graph V E): nat :=
  match g with
  | g_empty => 0
  | g_vertex V_ E_ g_ _ _ => out_degree v g_
  | g_arc V_ E_ g_ src _ _ _ _ => if eq_dec_V v src
                                  then 1 + out_degree v g_
                                  else out_degree v g_
end.

Lemma eq_dec_E: forall (e1 e2: X * X), 
  {e1 = e2} + {e1 <> e2}.
Proof.
  intros. destruct e1 as [L1 R1]. destruct e2 as [L2 R2].
  destruct (eq_dec_V L1 L2) as [ EL1 | EL2 ];  
  destruct (eq_dec_V R1 R2) as [ ER1 | ER2 ].
  - left. rewrite EL1. rewrite ER1. reflexivity.
  - right. intros contra. inversion contra. contradiction.
  - right. intros contra. inversion contra. contradiction. 
  - right. intros contra. inversion contra. contradiction. 
Qed.

End ExplicitType.