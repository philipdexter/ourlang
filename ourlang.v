
Require Import CpdtTactics.
From Coq Require Import Lists.List.
From Coq Require Import Arith.PeanoNat.
From Coq Require Import Arith.Peano_dec.
Import ListNotations.

Set Implicit Arguments.

Definition append (A:Type) (l1 : list A) (l2 : list A) := concat [l1; l2].
Notation "a ++ b" := (append a b).

Notation key := nat.
Notation payload := nat.
Notation label := nat.
Notation keyset := (list key).

Inductive node : Type :=
| N : key -> payload -> node.
Hint Constructors node.

Inductive operation : Type :=
| inc : keyset -> operation
| add : key -> payload -> operation.
Hint Constructors operation.

Definition target op :=
match op with
| inc ks => ks
| add _ _ => []
end.

Definition final op : payload :=
match op with
| inc ks => 0
| add k _ => k
end.

Inductive labeled_operation : Type :=
| lo : label -> operation -> labeled_operation.
Hint Constructors labeled_operation.

Notation "l ->> o" := (lo l o) (at level 40).

Notation result := nat.

Inductive labeled_result : Type :=
| lr : label -> result -> labeled_result.
Hint Constructors labeled_result.

Notation "l ->>> r" := (lr l r) (at level 40).

Notation ostream := (list labeled_operation).
Notation rstream := (list labeled_result).

Inductive station : Type :=
| S : node -> ostream -> station.
Hint Constructors station.

Notation "<< n ; os >>" := (S n os).

Notation backend := (list station).

Inductive config : Type :=
| C : backend -> ostream -> rstream -> config.
Hint Constructors config.

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
    c --> C (<<n1; (os1 ++ [o])>>::b') os' rs
| S_Add : forall c b os rs os' l k v o,
    c = C b os rs ->
    os = o :: os' ->
    o = l ->> add k v ->
    c --> C (<<(N k v); []>> :: b) os' (l ->>> final (add k v) :: rs)
| S_Inc : forall c b os rs b1 s1 s1' os1 os1' os1'' b2 k v ks l,
    c = C b os rs ->
    b = b1 ++ s1 :: b2 ->
    s1 = <<(N k v); os1>> ->
    os1 = l ->> inc ks :: os1'' ->
    os1' = l ->> inc (remove Nat.eq_dec k ks) :: os1'' ->
    s1' = <<(N k (v + 1)); os1'>> ->
    In k ks ->
    c --> C (b1 ++ s1' :: b2) os rs
| S_Complete : forall c b os rs l n1 os1 os1' op b1 k,
    c = C b os rs ->
    b = b1 ++ [<<n1; os1>>] ->
    os1 = l ->> op :: os1' ->
    k = getKey n1 ->
    not (In k (target op)) ->
    c --> C (b1 ++ [<<n1; os1'>>]) os (l ->>> final op :: rs)
(* S_Last *)
where "c1 --> c2" := (step c1 c2).
Hint Constructors step.
Definition relation (X : Type) := X -> X -> Prop.
Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.
Hint Constructors multi.

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).


Example step_empty : (C [] [1 ->> inc []] []) --> (C [] [] [1 ->>> 0]).
Proof using.
  assert (0 = final (inc [])) by crush.
  rewrite -> H.
  apply S_Empty with (c := (C [] [1 ->> inc []] [])) (os := [1 ->> inc []]) (o := 1 ->> inc []); crush.
Qed.

Example step_first : (C [<<(N 1 1); []>>] [1 ->> inc []] []) --> (C [<<(N 1 1); [1 ->> inc []]>>] [] []).
Proof using.
  eapply S_First with (c := (C [<<(N 1 1); []>>] [1 ->> inc []] [])) (n1 := (N 1 1)) (o := 1 ->> inc []) (os1 := []); crush.
Qed.

Example step_add : (C [] [1 ->> add 1 0] []) --> (C [<<(N 1 0); []>>] [] [1 ->>> 1]).
Proof using.
  eapply S_Add; crush.
Qed.

Example step_addinc1 : (C [] [1 ->> add 1 0; 2 ->> inc [1]] []) --> (C [<<(N 1 0); []>>] [2 ->> inc [1]] [1 ->>> 1]).
Proof using.
  eapply S_Add; crush.
Qed.

Example step_addinc2 : (C [<<(N 1 0); []>>] [2 ->> inc [1]] [1 ->>> 1]) --> (C [<<(N 1 0); [2 ->> inc [1]]>>] [] [1 ->>> 1]).
Proof using.
  eapply S_First with (c := (C [<<(N 1 0); []>>] [2 ->> inc [1]] [1 ->>> 1])) (n1 := (N 1 0)) (o := 2 ->> inc [1]) (os1 := []); crush.
Qed.

Example step_addinc3 : (C [<<(N 1 0); [2 ->> inc [1]]>>] [] [1 ->>> 1]) --> (C [<<(N 1 1); [2 ->> inc []]>>] [] [1 ->>> 1]).
Proof using.
  eapply S_Inc with (c := (C [<<(N 1 0); [2 ->> inc [1]]>>] [] [1 ->>> 1])) (s1' := <<(N 1 1); [2 ->> inc []]>>) (b1 := []); crush.
Qed.

Example step_addinc4 : (C [<<(N 1 1); [2 ->> inc []]>>] [] [1 ->>> 1]) --> (C [<<(N 1 1); []>>] [] [2 ->>> 0; 1 ->>> 1]).
Proof using.
  assert (0 = final (inc [])) by crush.
  rewrite -> H.
  eapply S_Complete with (c := (C [<<(N 1 1); [2 ->> inc []]>>] [] [1 ->>> 1])) (n1 := (N 1 1)) (os1 := [2 ->> inc []]) (b1 := []); crush.
Qed.

Example step_addinc : (C [] [1 ->> add 1 0; 2 ->> inc [1]] []) -->* (C [<<(N 1 1); []>>] [] [2 ->>> 0; 1 ->>> 1]).
Proof.
  eapply multi_step.
  apply step_addinc1.
  eapply multi_step.
  apply step_addinc2.
  eapply multi_step.
  apply step_addinc3.
  eapply multi_step.
  apply step_addinc4.
  eapply multi_refl.
Qed.
