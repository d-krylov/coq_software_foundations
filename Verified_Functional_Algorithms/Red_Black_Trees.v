From Coq Require Import List. Import ListNotations.

Section ValueType.
  
Variable V : Type.
Variable default : V.

Parameter int: Type.
Parameter ltb: int -> int -> bool.

Definition key := int.

Inductive color := Red | Black.

Inductive tree : Type :=  
  | E : tree
  | T : color -> tree -> key -> V -> tree -> tree.

Definition empty_tree : tree := E.

Fixpoint lookup (x: key) (t: tree) : V :=
  match t with
  | E => default
  | T _ tl k v tr => if ltb x k then lookup x tl
                     else if ltb k x then lookup x tr
                     else v
end.

Definition balance (rb : color) (t1 : tree) (k : key) (vk : V) (t2 : tree) : tree :=
  match rb with
  | Red => T Red t1 k vk t2
  | _ => match t1 with
        | T Red (T Red a x vx b) y vy c => T Red (T Black a x vx b) y vy (T Black c k vk t2)
        | T Red a x vx (T Red b y vy c) => T Red (T Black a x vx b) y vy (T Black c k vk t2)
        | _ => match t2 with
                | T Red (T Red b y vy c) z vz d => T Red (T Black t1 k vk b) y vy (T Black c z vz d)
                | T Red b y vy (T Red c z vz d) => T Red (T Black t1 k vk b) y vy (T Black c z vz d)
                | _ => T Black t1 k vk t2
                end
        end
end.

Fixpoint ins (x : key) (vx : V) (t : tree) : tree :=
  match t with
  | E => T Red E x vx E
  | T c a y vy b => if ltb x y then balance c (ins x vx a) y vy b
                    else if ltb y x then balance c a y vy (ins x vx b)
                    else T c a x vx b
end.

Definition make_black (t : tree) : tree :=
  match t with
  | E => E
  | T _ a x vx b => T Black a x vx b
end.

Definition insert (x : key) (vx : V) (t : tree) := make_black (ins x vx t).

Fixpoint elements_tr (t : tree) (acc: list (key * V)): list (key * V) :=
  match t with
  | E => acc
  | T _ l k v r => elements_tr l ((k, v) :: elements_tr r acc)
end.

Definition elements (t : tree) : list (key * V) := elements_tr t [].

Fixpoint ForallT (P: int -> V -> Prop) (t: tree) : Prop :=
  match t with
  | E => True
  | T c l k v r => P k v /\ ForallT P l /\ ForallT P r
end.

Inductive BST : tree -> Prop :=
  | ST_E : BST E
  | ST_T : forall (c : color) (l : tree) (k : key) (v : V) (r : tree),
    ForallT (fun ks _ => (Abs ks) < (Abs k)) l ->
    ForallT (fun ks _ => (Abs ks) > (Abs k)) r ->
    BST l -> BST r -> BST (T c l k v r).