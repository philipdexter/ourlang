
From Coq Require Import Lists.List.
Import ListNotations.

Definition append (A:Type) (l1 : list A) (l2 : list A) := concat [l1; l2].
Notation "a ++ b" := (append a b).

Notation key := nat.
Notation payload := nat.
Notation label := nat.
Notation keyset := (list key).

Inductive node : Type :=
| N : key -> payload -> node.

Inductive operation : Type :=
| inc : keyset -> operation.

Definition target op :=
match op with
| inc ks => ks
end.

Definition final op : payload :=
match op with
| inc ks => 0
end.

Inductive labeled_operation : Type :=
| lo : label -> operation -> labeled_operation.

Notation "l ->> o" := (lo l o) (at level 40).

Notation result := payload.

Inductive labeled_result : Type :=
| lr : label -> result -> labeled_result.

Notation "l ->>> r" := (lr l r) (at level 40).

Notation ostream := (list labeled_operation).
Notation rstream := (list labeled_result).

Inductive station : Type :=
| S : node -> ostream -> station.

Notation "<< n ; os >>" := (S n os).

Notation backend := (list station).

Inductive config : Type :=
| C : backend -> ostream -> rstream -> config.

Definition getKey (n : node) :=
match n with
  | N k _ => k
end.

Definition getPayload (n : node) :=
match n with
  | N _ p => p
end.

Reserved Notation "c1 '-->' c2" (at level 40).

Inductive step : config -> config -> Prop :=
| S_Empty : forall c os rs os' o l op,
    c = C [] os rs ->
    os = o :: os' ->
    o = l ->> op ->
    c --> C [] os' (l ->>> final op :: rs)
| S_First : forall c b os rs o os' b' n1 os1,
    c = C b os rs ->
    os = o :: os' ->
    b = (<<n1; os1>>)::b' ->
    c --> C ((S n1 (os1 ++ [o]))::b') os' rs
where "c1 --> c2" := (step c1 c2).
