
Require Import CpdtTactics.
From Coq Require Import Lists.List.
From Coq Require Import Sorting.Permutation.
From Coq Require Import Arith.PeanoNat.
From Coq Require Import Arith.Peano_dec.
From Coq Require Import Classes.Equivalence.
Import ListNotations.

From Coq Require Import Relations.Relations.
From Coq Require Import Relations.Relation_Definitions.
Hint Constructors clos_refl_trans_1n.

Hint Constructors Permutation.Permutation.

Set Implicit Arguments.

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

Definition not_add op : Prop :=
match op with
| inc _ => True
| add _ _ => False
end.
Hint Unfold not_add.

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
| St : node -> ostream -> station.
Hint Constructors station.
Notation "<< n ; os >>" := (St n os).

Notation backend := (list station).

Inductive config : Type :=
| C : backend -> ostream -> rstream -> config.
Hint Constructors config.

Definition getNode (s : station) :=
match s with
| <<n; _>> => n
end.

Definition getOstream (s : station) :=
match s with
| <<_; os>> => os
end.

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
(* to-graph *)
| S_Empty : forall c os rs os' o l op,
    c = C [] os rs ->
    os = o :: os' ->
    o = l ->> op ->
    not_add op ->
    c --> C [] os' (l ->>> final op :: rs)
| S_First : forall c b os rs o os' b' n1 os1 op l,
    c = C b os rs ->
    os = o :: os' ->
    b = (<<n1; os1>>)::b' ->
    o = l ->> op ->
    not_add op ->
    c --> C (<<n1; (os1 ++ [o])>>::b') os' rs
| S_Add : forall c b os rs os' l k v o,
    c = C b os rs ->
    os = o :: os' ->
    o = l ->> add k v ->
    c --> C (<<(N k v); []>> :: b) os' (l ->>> final (add k v) :: rs)
(* task *)
| S_Inc : forall c b os rs b1 s1 s1' os1 os1' os1'' b2 k v ks l,
    c = C b os rs ->
    b = b1 ++ s1 :: b2 ->
    s1 = <<(N k v); os1>> ->
    os1 = l ->> inc ks :: os1'' ->
    os1' = l ->> inc (remove Nat.eq_dec k ks) :: os1'' ->
    s1' = <<(N k (v + 1)); os1'>> ->
    In k ks ->
    c --> C (b1 ++ s1' :: b2) os rs
| S_Last : forall c b os rs l n1 os1 os1' op b1 k,
    c = C b os rs ->
    b = b1 ++ [<<n1; os1>>] ->
    os1 = l ->> op :: os1' ->
    k = getKey n1 ->
    not (In k (target op)) ->
    c --> C (b1 ++ [<<n1; os1'>>]) os (l ->>> final op :: rs)
(* S_Complete *)
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
  eapply S_Last with (c := (C [<<(N 1 1); [2 ->> inc []]>>] [] [1 ->>> 1])) (n1 := (N 1 1)) (os1 := [2 ->> inc []]) (b1 := []); crush.
Qed.

Example step_addinc : (C [] [1 ->> add 1 0; 2 ->> inc [1]] []) -->* (C [<<(N 1 1); []>>] [] [2 ->>> 0; 1 ->>> 1]).
Proof using.
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

Definition backend_keys (b : backend) :=
map (fun s => getKey (getNode s)) b.
Hint Unfold backend_keys.

Definition ostream_keys (os : ostream) :=
concat (map (fun o => match o with
             | l ->> add k _ => [k]
             | _ => []
           end) os).
Hint Unfold ostream_keys.

Definition config_keys (c : config) :=
match c with
| C b os rs => concat [backend_keys b; ostream_keys os]
end.
Hint Unfold config_keys.

Definition ostream_labels (os : ostream) :=
map (fun o => match o with l ->> _ => l end) os.
Hint Unfold ostream_labels.

Lemma ostream_labels_dist :
  forall os1 os2,
  ostream_labels (os1 ++ os2) = ostream_labels os1 ++ ostream_labels os2.
Proof using.
 induction os1; intros; crush.
Qed.
Hint Rewrite ostream_labels_dist.

Lemma backend_keys_dist :
  forall b1 b2,
  backend_keys (b1 ++ b2) = backend_keys b1 ++ backend_keys b2.
Proof using.
 induction b1; intros; crush.
Qed.
Hint Rewrite backend_keys_dist.

Definition rstream_labels (rs : rstream) :=
map (fun r => match r with l ->>> _ => l end) rs.
Hint Unfold rstream_labels.

Definition backend_labels (b : backend) :=
concat (map (fun s => ostream_labels (getOstream s)) b).
Hint Unfold backend_labels.

Lemma backend_labels_dist :
  forall b1 b2,
  backend_labels (b1 ++ b2) = backend_labels b1 ++ backend_labels b2.
Proof using.
  induction b1; intros; intuition.
  simpl.
  unfold backend_labels in *.
  simpl.
  crush.
Qed.
Hint Rewrite backend_labels_dist.

Definition config_labels (c : config) :=
match c with
| C b os rs => concat [backend_labels b; ostream_labels os; rstream_labels rs]
end.
Hint Unfold config_labels.

Inductive distinct (A : Type) : list A -> Prop :=
| distinct_empty : distinct []
| distinct_one : forall x, distinct [x]
| distinct_many : forall xs x xs', xs = x :: xs' -> not (In x xs') -> distinct xs' -> distinct xs.
Hint Constructors distinct.

Lemma distinct_remove :
  forall A (x : A) xs,
  distinct (x :: xs) ->
  distinct xs /\ not (In x xs).
Proof using.
  intros.
  inversion H; crush.
Qed.
Hint Rewrite distinct_remove.

Lemma not_in_app_comm :
  forall A (x : A) xs ys,
  ~ In x (xs ++ ys) ->
  ~ In x (ys ++ xs).
Proof using.
  unfold not in *.
  intros.
  apply List.in_app_or in H0.
  inversion H0; crush.
Qed.

Lemma not_in_remove :
  forall A (x : A) y xs,
  ~ In x (y :: xs) ->
  ~ In x xs /\ x <> y.
Proof using.
  induction xs; crush.
Qed.
Hint Rewrite not_in_remove.

Lemma distinct_rotate :
  forall A (x : A) xs ys,
  distinct (x :: xs ++ ys) ->
  distinct (xs ++ x :: ys).
Proof using.
  induction xs; intros; crush.
  apply distinct_remove in H; destruct H.
  apply distinct_remove in H; destruct H.
  crush.
  assert (distinct (x :: xs ++ ys)).
  eapply distinct_many; crush.
  apply IHxs in H0.
  apply distinct_many with (x := a) (xs' := xs ++ x :: ys); crush.
  apply List.in_app_or in H4; destruct H4; crush.
Qed.
Hint Rewrite distinct_rotate.

Lemma distinct_rotate_rev :
  forall A (x : A) xs ys,
  distinct (xs ++ x :: ys) ->
  distinct (x :: xs ++ ys).
Proof using.
  induction xs; intros; crush.
  apply distinct_remove in H; destruct H.
  apply IHxs in H.
  apply distinct_remove in H; destruct H.
  assert (distinct (a :: xs ++ ys)).
  eapply distinct_many; crush.
  apply List.in_app_or in H2; destruct H2; crush.
  apply distinct_many with (x := x) (xs' := a :: xs ++ ys); crush.
Qed.
Hint Rewrite distinct_rotate.

Lemma distinct_app_comm :
  forall A (xs : list A) ys,
  distinct (xs ++ ys) ->
  distinct (ys ++ xs).
Proof using.
  induction xs; intros ys Ih.
  - rewrite List.app_nil_r; assumption.
  - simpl in Ih.
    apply distinct_remove in Ih.
    destruct Ih.
    apply IHxs in H.
    apply not_in_app_comm in H0.
    apply distinct_rotate.
    eapply distinct_many; crush.
Qed.

Lemma distinct_remove_middle :
  forall A (x : A) xs ys,
  distinct (xs ++ [x] ++ ys) ->
  distinct (xs ++ ys).
Proof using.
  intros.
  assert ([x] ++ ys = x :: ys) by crush.
  rewrite H0 in H.
  apply distinct_rotate_rev in H.
  apply distinct_remove in H.
  crush.
Qed.
Hint Rewrite distinct_remove_middle.

Lemma in_empty :
  forall A (x : A),
  In x [] -> False.
Proof using.
  intros A.
  unfold In.
  auto.
Qed.

Lemma distinct_concat :
  forall A (xs : list A) ys,
  distinct (xs ++ ys) ->
  distinct xs /\ distinct ys.
Proof using.
  intros A xs.
  induction xs; intros.
  - simpl in H. split; crush.
  - split. simpl in H. eapply distinct_many. crush.
    inversion H.
    * intuition.
      assert (xs = []).
      destruct xs.
      + reflexivity.
      + inversion H2.
      + rewrite H3 in H0. apply in_empty with (A := A) (x := a). auto.
    * assert (a = x) by crush.
      crush.
    * apply distinct_remove in H.
      destruct H.
      eapply IHxs in H.
      inversion H.
      assumption.
    * simpl in H.
      apply distinct_remove in H.
      destruct H.
      eapply IHxs in H.
      inversion H.
      assumption.
Qed.

Inductive well_typed : config -> Prop :=
| WT : forall c,
    distinct (config_keys c) ->
    distinct (config_labels c) ->
    well_typed c.
Hint Constructors well_typed.

Example wt : well_typed (C [<<(N 1 2); [5 ->> inc []]>>; <<(N 2 3); [4 ->> inc []]>>] [2 ->> inc []; 3 ->> inc []] [1 ->>> 2]).
Proof using.
  eapply WT; repeat crush; repeat (eapply distinct_many; crush).
Qed.

Lemma cons_to_app :
  forall A (x : A) xs,
  x :: xs = [x] ++ xs.
Proof using.
  intros.
  crush.
Qed.

Lemma well_typed_preservation :
  forall c1 c2,
  well_typed c1 ->
  c1 --> c2 ->
  well_typed c2.
Proof using.
  intros.
  inversion H0; inversion H; eapply WT; crush.
  (* S_Empty *)
  - destruct op; crush.
  - apply distinct_rotate.
    assumption.
  (* S_First *)
  - unfold ostream_keys in H8.
    destruct op; crush.
  - rewrite List.app_nil_r in *.
    unfold backend_labels. simpl.
    unfold backend_labels in H9. simpl in H9.
    destruct op; crush.
    apply distinct_rotate.
    remember (ostream_labels os' ++ rstream_labels rs) as y.
    assert (ostream_labels os1 ++ concat (map (fun s : station => ostream_labels (getOstream s)) b') ++ y =
            (ostream_labels os1 ++ concat (map (fun s : station => ostream_labels (getOstream s)) b')) ++ y) by crush.
    rewrite H1.
    rewrite List.app_assoc in H9.
    apply distinct_rotate_rev with (x:=l) in H9.
    crush.
  (* S_Add *)
  - apply distinct_rotate_rev. crush.
  - unfold backend_labels. simpl.
    rewrite List.app_nil_r. rewrite List.app_nil_r in H7.
    apply distinct_rotate_rev in H7.
    rewrite List.app_assoc.
    apply distinct_rotate.
    crush.
  (* S_Inc *)
  - crush.
  - apply distinct_rotate_rev in H9.
    rewrite List.app_assoc.
    rewrite List.app_assoc.
    apply distinct_rotate.
    unfold backend_labels at 2.
    crush.
Qed.

(* change this to the exists notation *)
(*
Reserved Notation "c1 '-v' c2" (at level 40).
Inductive goes_to : config -> config -> Prop :=
| goes_to_refl: forall cx cy, cx = cy -> cx -v cy
| goes_to_steps: forall cx cy cu cv, cx -->* cu -> cy -->* cv -> cu = cv -> cx -v cy
where "cx -v cy" := (goes_to cx cy).
Hint Constructors goes_to.
*)

Reserved Notation "c1 '==' c2" (at level 40).
Inductive cequiv : config -> config -> Prop :=
| cequiv_refl : forall c, c == c
| cequiv_permutation : forall b os rs rs', Permutation.Permutation rs rs' -> C b os rs == C b os rs'
where "c1 == c2" := (cequiv c1 c2).
Hint Constructors cequiv.

Lemma cequiv_trans :
  forall c1 c2 c3,
  c1 == c2 ->
  c2 == c3 ->
  c1 == c3.
Proof using.
  intros.
  inversion H; inversion H0; crush.
  inversion H5.
  apply cequiv_permutation.
  crush.
Qed.

Lemma cequiv_symmetric :
  forall c1 c2,
  c1 == c2 ->
  c2 == c1.
Proof using.
  intros.
  inversion H; crush.
Qed.
Hint Rewrite cequiv_symmetric.

Notation "cx -v cy" := (cx == cy \/ exists cu cv, cx --> cu /\ cy --> cv /\ cu == cv) (at level 40).
Definition goes_to (c1 : config) (c2 : config) : Prop := c1 -v c2.

Lemma goes_to_symmetric :
  forall c1 c2,
  c1 -v c2 ->
  c2 -v c1.
Proof using.
  intros.
  destruct H.
  - left. apply cequiv_symmetric. assumption.
  - inversion H.
    destruct H0.
    right.
    eapply ex_intro.
    eapply ex_intro.
    split ; try split.
    instantiate (1 := x0).
    crush.
    instantiate (1 := x).
    crush.
    apply cequiv_symmetric.
    crush.
Qed.
Hint Resolve goes_to_symmetric.

Lemma goes_to_refl :
  forall c,
  c -v c.
Proof using.
  intros.
  left.
  crush.
Qed.
Hint Rewrite goes_to_refl.

Lemma local_confluence_p1 :
  forall cx cy cz,
  (* well_typed cx -> *)
  cx --> cy ->
  cx --> cz ->
  (cy -v cz).
(* change this to single step if we don't need multi *)
Proof.
  (* intros cx cy cz WTcx cxcy cxcz. *)
  intros cx cy cz cxcy cxcz.
  inversion cxcy.
  (* S_Empty *)
  - inversion cxcz.
    (* S_Empty *)
    + crush.
      inversion H5.
      apply goes_to_refl.
    (* S_First *)
    + crush.
    (* S_Add *)
    + crush. destruct op; crush.
    (* S_Inc *)
    + rewrite H in H5. rewrite H6 in H5.
      inversion H5.
      destruct b1; crush.
    (* S_Last *)
    + rewrite H in H5. rewrite H6 in H5.
      inversion H5.
      destruct b1; crush.
  (* S_First *)
  - inversion cxcz.
    (* S_Empty *)
    + crush.
    (* S_First *)
    + crush.
      inversion H6.
      apply goes_to_refl.
    (* S_Add *)
    + crush.
      assert (Hop : op = add k v) by crush; rewrite Hop in *.
      crush.
    (* S_Inc *)
    + crush.
      {
      destruct b1; right; eapply ex_intro; eapply ex_intro; intros.
      (* b1 = [] *)
      - split; try split.
        + instantiate (1 := C (<< N k (v + 1); l0 ->> inc (remove Nat.eq_dec k ks) :: os1'' ++ [l ->> op] >> :: b') os' rs).
          inversion H6.
          simpl.
          eapply S_Inc with (b1 := []); crush.
        + instantiate (1 := C (<< N k (v + 1); l0 ->> inc (remove Nat.eq_dec k ks) :: os1'' ++ [l ->> op] >> :: b') os' rs).
          inversion H6.
          simpl.
          eapply S_First with (os1 := l0 ->> inc (remove Nat.eq_dec k ks) :: os1''); crush.
        + crush.
      (* b1 != [] *)
      - split; try split.
        + instantiate (1 := C (<< n1; os1 ++ [l ->> op] >> :: b1 ++ << N k (v + 1); l0 ->> inc (remove Nat.eq_dec k ks) :: os1'' >> :: b2) os' rs).
          inversion H6.
          eapply S_Inc with (b1 := << n1; os1 ++ [l ->> op] >> :: b1); crush.
        + instantiate (1 := C (<< n1; os1 ++ [l ->> op] >> :: b1 ++ << N k (v + 1); l0 ->> inc (remove Nat.eq_dec k ks) :: os1'' >> :: b2) os' rs).
          inversion H6.
          eapply S_First; crush.
        + crush.
      }
    (* S_Last *)
    + crush.
      {
      destruct b1; right; eapply ex_intro; eapply ex_intro; intros.
      (* b1 = [] *)
      - split; try split.
        + simpl in *. instantiate (1 := C [<< n1; os1' ++ [l ->> op]>>] os' (l0 ->>> final op0 :: rs0)).
          inversion H6.
          eapply S_Last with (b1 := []); crush.
        + simpl in *. instantiate (1 := C [<< n1; os1' ++ [l ->> op]>>] os' (l0 ->>> final op0 :: rs0)).
          inversion H6.
          eapply S_First; crush.
        + crush.
      (* b1 != [] *)
      - split; try split.
        + instantiate (1 := C (<< n1; os1 ++ [l ->> op] >> :: b1 ++ [<< n0; os1' >>]) os' (l0 ->>> final op0 :: rs)).
          inversion H6.
          eapply S_Last with (b1 := << n1; os1 ++ [l ->> op] >> :: b1); crush.
        + instantiate (1 := C (<< n1; os1 ++ [l ->> op] >> :: b1 ++ [<< n0; os1' >>]) os' (l0 ->>> final op0 :: rs)).
          inversion H6.
          eapply S_First; crush.
        + crush.
      }
  (* S_Add *)
  - inversion cxcz.
    (* S_Empty *)
    + crush. inversion H4. crush.
    (* S_First *)
    + crush. inversion H4. crush.
    (* S_Add *)
    + crush. inversion H4. crush.
    (* S_Inc *)
    + crush.
      {
      destruct b1; right; eapply ex_intro; eapply ex_intro; intros.
      (* b1 = [] *)
      - split; try split.
        + simpl in *. instantiate (1 := C (<< N k v; [] >> :: << N k0 (v0 + 1); l0 ->> inc (remove Nat.eq_dec k0 ks) :: os1'' >> :: b2) os' (l ->>> k :: rs)).
          inversion H4.
          eapply S_Inc with (b1 := [<< N k v; [] >>]); crush.
        + simpl in *. instantiate (1 := C (<< N k v; [] >> :: << N k0 (v0 + 1); l0 ->> inc (remove Nat.eq_dec k0 ks) :: os1'' >> :: b2) os' (l ->>> k :: rs)).
          inversion H4.
          eapply S_Add; crush.
        + crush.
      (* b1 != [] *)
      - split; try split.
        + simpl in *. instantiate (1 := C (<< N k v; [] >> :: s :: b1 ++ << N k0 (v0 + 1); l0 ->> inc (remove Nat.eq_dec k0 ks) :: os1'' >> :: b2) os' (l ->>> k :: rs)).
          inversion H4.
          eapply S_Inc with (b1 := << N k v; [] >> :: s :: b1); crush.
        + simpl in *. instantiate (1 := C (<< N k v; [] >> :: s :: b1 ++ << N k0 (v0 + 1); l0 ->> inc (remove Nat.eq_dec k0 ks) :: os1'' >> :: b2) os' (l ->>> k :: rs)).
          inversion H4.
          eapply S_Add; crush.
        + crush.
      }
    (* S_Last *)
    + crush.
      {
      destruct b1; right; eapply ex_intro; eapply ex_intro; intros.
      (* b1 = [] *)
      - split; try split.
        + simpl in *. instantiate (1 := C (<< N k v; [] >> :: [<< n1; os1' >>]) os' (l0 ->>> final op :: l ->>> k :: rs)).
          inversion H4.
          eapply S_Last with (b1 := [<<N k v; []>>]); crush.
        + simpl in *. instantiate (1 := C (<< N k v; [] >> :: [<< n1; os1' >>]) os' (l ->>> k :: l0 ->>> final op :: rs)).
          inversion H4.
          eapply S_Add; crush.
        + crush.
      (* b1 != [] *)
      - split; try split.
        + 
Admitted.
(*           * simpl in *. instantiate (1 := ...) *)

(*             inversion H4. *)
(*   C (s :: b1 ++ [<< n1; os1' >>]) os0 (l0 ->>> final op :: rs0) *)
(*   C (<< N k v; [] >> :: b) os' (l ->>> k :: rs) *)

(*       } *)


(* Qed. *)

(* try to add a simple frontend with just an emit *)



(*************)
(* change to multi step *)
Definition diamond_property_modulo {A : Type}
           (R1 R2 : A -> A -> Prop) (sim : A -> A -> Prop) :=
forall x y z,
    R1 x y ->
    R2 x z ->
    sim y z \/ exists u v, R2 y u /\ R1 z v /\ sim u v.

Lemma diamond_symmetric : forall {A : Type} (R1 R2 : A -> A -> Prop) (sim : A -> A -> Prop),
  (equiv A sim) ->
  diamond_property_modulo R1 R2 sim -> diamond_property_modulo R2 R1 sim.
Proof.
  intros A R1 R2 sim Hequivsim H.
  unfold diamond_property_modulo in *.
  intros x y z xy xz.
  apply H with (x:=x) (y:=z) in xy; try assumption.
  destruct xy.
  - left.
    destruct Hequivsim.
    crush.
  - right.
    destruct H0; destruct H0; destruct H0; destruct H1.
    repeat (eapply ex_intro).
    split; try split.
    instantiate (1 := x1).
    assumption.
    instantiate (1 := x0).
    assumption.
    destruct Hequivsim.
    crush.
Qed.
Hint Resolve diamond_symmetric.

Inductive star {A : Type} (R : A -> A -> Prop) : nat -> A -> A -> Prop :=
| Zero : forall x, star R 0 x x
| Step : forall x y, R x y -> forall n z, star R n y z -> star R (S n) x z.
Hint Constructors star.

Lemma clos_refl_multi :
  forall {A} R x y,
  clos_refl_trans_1n A R x y <-> exists n, star R n x y.
Proof.
Admitted.
Hint Resolve clos_refl_multi.

Lemma on_the_left :
  forall {A : Type} (R1 R2 : A -> A -> Prop) (sim : A -> A -> Prop),
  diamond_property_modulo R1 R2 sim -> forall n, diamond_property_modulo (star R1 n) R2 sim.
Proof.
Admitted.
Hint Resolve on_the_left.

Lemma on_the_right :
  forall {A : Type} (R1 R2 : A -> A -> Prop) (sim : A -> A -> Prop),
  diamond_property_modulo R1 R2 sim -> forall n, diamond_property_modulo R1 (star R2 n) sim.
Proof.
Admitted.
Hint Resolve on_the_right.

Lemma diamond_property_implies_mn_confluence :
  forall {A : Type} (R : A -> A -> Prop) (sim : A -> A -> Prop),
  diamond_property_modulo R R sim -> forall m n, diamond_property_modulo (star R m) (star R n) sim.
Proof.
Admitted.
Hint Resolve diamond_property_implies_mn_confluence.

Theorem diamond_property_implies_confluence :
  forall {A : Type} (R : A -> A -> Prop) (sim : A -> A -> Prop),
  equiv A sim ->
  diamond_property_modulo R R sim -> diamond_property_modulo (clos_refl_trans_1n A R) (clos_refl_trans_1n A R) sim.
Proof using.
  unfold diamond_property_modulo in *.
  intros A R sim simequiv local_diamond x y z xy xz.
  apply clos_refl_multi in xy.
  apply clos_refl_multi in xz.
  destruct xy as [n xy].
  destruct xz as [m xz].
  eapply diamond_property_implies_mn_confluence with (m0:=n) (n0:=m) in local_diamond.
  unfold diamond_property_modulo in *.
  eapply local_diamond with (z := z) in xy.
  - destruct xy as [xy|xy].
    + crush.
    + right.
      destruct xy as [u xy]. destruct xy as [v].
      repeat (eapply ex_intro).
      split ; try split.
      * apply clos_refl_multi.
        eapply ex_intro.
        instantiate (1 := u).
        instantiate (1 := m).
        crush.
      * apply clos_refl_multi.
        eapply ex_intro.
        instantiate (1 := v).
        instantiate (1 := n).
        crush.
      * crush.
  - crush.
Qed.
(*************)

(* define the relation over well-typed configurations *)

Lemma ourlang_local_confluence :
  diamond_property_modulo step step cequiv.
Proof using.
  unfold diamond_property_modulo.
  intros.
  eapply local_confluence_p1 with (cx:=x) (cy:=y) (cz:=z); crush.
Qed.

Instance cequiv_reflective : Reflexive cequiv := cequiv_refl.
Instance cequiv_sym : Symmetric cequiv := cequiv_symmetric.
Instance cequiv_transitive : Transitive cequiv := cequiv_trans.
Program Instance cequiv_equivalence : Equivalence cequiv.

Theorem ourlang_confluence :
  diamond_property_modulo (clos_refl_trans_1n config step) (clos_refl_trans_1n config step) cequiv.
Proof using.
  eapply diamond_property_implies_confluence.
  unfold equiv.
  split.
  apply cequiv_reflective.
  split.
  apply cequiv_transitive.
  apply cequiv_sym.
  apply ourlang_local_confluence.
Qed.
