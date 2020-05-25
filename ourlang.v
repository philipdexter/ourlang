
Require Import CpdtTactics.
From Coq Require Import Lists.List.
From Coq Require Import Sorting.Permutation.
From Coq Require Import Arith.PeanoNat.
From Coq Require Import Arith.Peano_dec.
From Coq Require Import Classes.Equivalence.
From Coq Require Import Strings.String.
Import ListNotations.

From Coq Require Import Relations.Relations.
From Coq Require Import Relations.Relation_Definitions.
Hint Constructors clos_refl_trans_1n.

Hint Constructors Permutation.Permutation.

Ltac inv H := inversion H; subst; clear H.

Set Implicit Arguments.

Notation key := nat.
Notation payload := nat.
Notation label := nat.
Notation keyset := (list key).

Inductive node : Type :=
| N : key -> payload -> node.
Hint Constructors node.

Inductive operation : Type :=
| inc : nat -> keyset -> operation
| add : key -> payload -> operation.
Hint Constructors operation.

Definition target op :=
match op with
| inc _ ks => ks
| add _ _ => []
end.
Hint Unfold target.

Definition not_add op : Prop :=
match op with
| inc _ _ => True
| add _ _ => False
end.
Hint Unfold not_add.

Definition final op : payload :=
match op with
| inc _ ks => 0
| add k _ => k
end.
Hint Unfold final.

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

(* ***********************frontend *)

Inductive type : Type :=
| Label : type.
Hint Constructors type.

Inductive term : Type :=
| t_var : string -> term
| t_app : term -> term -> term
| t_abs : string -> type -> term -> term
| t_emit : labeled_operation -> term
| t_result : result -> term.
Hint Constructors term.

Inductive value : term -> Prop :=
| v_abs : forall x T t,
          value (t_abs x T t)
| v_label : forall label,
            value label
| v_result : forall result,
             value (t_result result).
Hint Constructors value.
Definition noop : term := t_result 0.

Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.

Reserved Notation "'#[' x ':=' s ']' t" (at level 20).

Fixpoint e_subst (x : string) (s : term) (t : term) : term :=
  match t with
  | t_var x' =>
      if eqb_string x x' then s else t
  | t_abs x' T t1 =>
      t_abs x' T (if eqb_string x x' then t1 else (#[x:=s] t1))
  | t_app t1 t2 =>
      t_app (#[x:=s] t1) (#[x:=s] t2)
  | t_emit lop =>
      t_emit lop
  | t_result r =>
      t_result r
  end
where "'#[' x ':=' s ']' t" := (e_subst x s t).

Reserved Notation "t1 '==>' t2" (at level 40).

(* put these into the other reduction rule, not its own, because needs config to do emit *)
Inductive e_step : term -> term -> Prop :=
| E_App : forall x T t12 v2,
          value v2 ->
          (t_app (t_abs x T t12) v2) ==> #[x:=v2]t12
| E_App1 : forall t1 t1' t2,
           t1 ==> t1' ->
           t_app t1 t2 ==> t_app t1' t2
| E_App2 : forall v1 t2 t2',
           value v1 ->
           t2 ==> t2' ->
           t_app v1 t2 ==> t_app v1  t2'
| E_Emit : forall lop,
           t_emit lop ==> t_emit lop (* TODO fix this *)
where "t1 '==>' t2" := (e_step t1 t2).
Hint Constructors e_step.

(* ***********************end frontend *)

Notation backend := (list station).

Inductive config : Type :=
| C : backend -> ostream -> rstream -> term -> config.
Hint Constructors config.

Definition get_node (s : station) :=
match s with
| <<n; _>> => n
end.
Hint Unfold get_node.

Definition get_ostream (s : station) :=
match s with
| <<_; os>> => os
end.
Hint Unfold get_ostream.

Definition getKey (n : node) :=
match n with
  | N k _ => k
end.
Hint Unfold getKey.

Definition get_payload (n : node) :=
match n with
  | N _ p => p
end.
Hint Unfold get_payload.

Reserved Notation "c1 '-->' c2" (at level 40).

Inductive step : config -> config -> Prop :=
(* frontend *)
| S_Emit : forall c b os rs t_lop l op,
    c = C b os rs t_lop ->
    t_lop = t_emit (l ->> op) ->
    c --> C b (os ++ [l ->> op]) rs (t_result l)
| S_App : forall c b os rs x T t12 v2,
    c = C b os rs (t_app (t_abs x T t12) v2) ->
    value v2 ->
    c --> C b os rs (#[x:=v2]t12)
| S_App1 : forall c b os rs t1 t1' t2,
    c = C b os rs (t_app t1 t2) ->
    C [] [] rs t1 --> C [] [] rs t1' ->
    c --> C b os rs (t_app t1' t2)
(* to-graph *)
| S_Empty : forall c os rs os' o l op term,
    c = C [] os rs term ->
    os = o :: os' ->
    o = l ->> op ->
    not_add op ->
    c --> C [] os' (l ->>> final op :: rs) term
| S_First : forall c b os rs o os' b' n1 os1 op l term,
    c = C b os rs term ->
    os = o :: os' ->
    b = (<<n1; os1>>)::b' ->
    o = l ->> op ->
    not_add op ->
    c --> C (<<n1; (os1 ++ [o])>> :: b') os' rs term
| S_Add : forall c b os rs os' l k v o term,
    c = C b os rs term ->
    os = o :: os' ->
    o = l ->> add k v ->
    c --> C (<<(N k v); []>> :: b) os' (l ->>> final (add k v) :: rs) term
(* task *)
| S_Inc : forall c b os rs b1 s1 s1' os1 os1' os1'' b2 k v ks l term incby,
    c = C b os rs term ->
    b = b1 ++ s1 :: b2 ->
    s1 = <<(N k v); os1>> ->
    os1 = l ->> inc incby ks :: os1'' ->
    os1' = l ->> inc incby (remove Nat.eq_dec k ks) :: os1'' ->
    s1' = <<(N k (v + incby)); os1'>> ->
    In k ks ->
    c --> C (b1 ++ s1' :: b2) os rs term
| S_Last : forall c b os rs l n1 os1 os1' op b1 k term,
    c = C b os rs term ->
    b = b1 ++ [<<n1; os1>>] ->
    os1 = l ->> op :: os1' ->
    k = getKey n1 ->
    not (In k (target op)) ->
    c --> C (b1 ++ [<<n1; os1'>>]) os (l ->>> final op :: rs) term
| S_FuseInc : forall c b n b1 b2 os os1 os2 rs term incby incby' ks l l',
    c = C b os rs term ->
    b = b1 ++ <<n; os1 ++ l ->> inc incby ks :: l' ->> inc incby' ks :: os2>> :: b2 ->
    c --> C (b1 ++ <<n; os1 ++ l ->> inc (incby + incby') ks :: os2>> :: b2) os (l' ->>> final (inc incby' ks) :: rs) term
(* S_Complete *)
where "c1 --> c2" := (step c1 c2).
Hint Constructors step.

Inductive star {A : Type} (R : A -> A -> Prop) : nat -> A -> A -> Prop :=
| Zero : forall x, star R 0 x x
| Step : forall x y, R x y -> forall n z, star R n y z -> star R (S n) x z.
Hint Constructors star.

Notation "c1 '-->*[' n ']' c2" := (star step n c1 c2) (at level 40).

Example step_empty : (C [] [1 ->> inc 1 []] [] noop) --> (C [] [] [1 ->>> 0] noop).
Proof using.
  assert (0 = final (inc 1 [])) by crush.
  rewrite -> H.
  apply S_Empty with (c := (C [] [1 ->> inc 1 []] [] noop)) (os := [1 ->> inc 1 []]) (o := 1 ->> inc 1 []); crush.
Qed.

Example step_first : (C [<<(N 1 1); []>>] [1 ->> inc 1 []] [] noop) --> (C [<<(N 1 1); [1 ->> inc 1 []]>>] [] [] noop).
Proof using.
  eapply S_First with (c := (C [<<(N 1 1); []>>] [1 ->> inc 1 []] [] noop)) (n1 := (N 1 1)) (o := 1 ->> inc 1 []) (os1 := []); crush.
Qed.

Example step_add : (C [] [1 ->> add 1 0] [] noop) --> (C [<<(N 1 0); []>>] [] [1 ->>> 1] noop).
Proof using.
  eapply S_Add; crush.
Qed.

Example step_addinc1 : (C [] [1 ->> add 1 0; 2 ->> inc 1 [1]] [] noop) --> (C [<<(N 1 0); []>>] [2 ->> inc 1 [1]] [1 ->>> 1] noop).
Proof using.
  eapply S_Add; crush.
Qed.

Example step_addinc2 : (C [<<(N 1 0); []>>] [2 ->> inc 1 [1]] [1 ->>> 1] noop) --> (C [<<(N 1 0); [2 ->> inc 1 [1]]>>] [] [1 ->>> 1] noop).
Proof using.
  eapply S_First with (c := (C [<<(N 1 0); []>>] [2 ->> inc 1 [1]] [1 ->>> 1] noop)) (n1 := (N 1 0)) (o := 2 ->> inc 1 [1]) (os1 := []); crush.
Qed.

Example step_addinc3 : (C [<<(N 1 0); [2 ->> inc 1 [1]]>>] [] [1 ->>> 1] noop) --> (C [<<(N 1 1); [2 ->> inc 1 []]>>] [] [1 ->>> 1] noop).
Proof using.
  eapply S_Inc with (c := (C [<<(N 1 0); [2 ->> inc 1 [1]]>>] [] [1 ->>> 1] noop)) (s1' := <<(N 1 1); [2 ->> inc 1 []]>>) (b1 := []); crush.
Qed.

Example step_addinc4 : (C [<<(N 1 1); [2 ->> inc 1 []]>>] [] [1 ->>> 1] noop) --> (C [<<(N 1 1); []>>] [] [2 ->>> 0; 1 ->>> 1] noop).
Proof using.
  assert (0 = final (inc 1 [])) by crush.
  rewrite -> H.
  eapply S_Last with (c := (C [<<(N 1 1); [2 ->> inc 1 []]>>] [] [1 ->>> 1] noop)) (n1 := (N 1 1)) (os1 := [2 ->> inc 1 []]) (b1 := []); crush.
Qed.

Example step_addinc : (C [] [1 ->> add 1 0; 2 ->> inc 1 [1]] [] noop) -->*[4] (C [<<(N 1 1); []>>] [] [2 ->>> 0; 1 ->>> 1] noop).
Proof using.
  eapply Step.
  apply step_addinc1.
  eapply Step.
  apply step_addinc2.
  eapply Step.
  apply step_addinc3.
  eapply Step.
  apply step_addinc4.
  eapply Zero.
Qed.

Definition backend_keys (b : backend) :=
map (fun s => getKey (get_node s)) b.
Hint Unfold backend_keys.

Definition ostream_keys (os : ostream) :=
List.concat (map (fun o => match o with
             | l ->> add k _ => [k]
             | _ => []
           end) os).
Hint Unfold ostream_keys.

Fixpoint term_keys (t : term) :=
match t with
| t_var _ => []
| t_app t1 t2 => List.concat [term_keys t1; term_keys t2]
| t_abs _ _ t => term_keys t
| t_emit (_ ->> add k v) => [k]
| t_emit (_ ->> inc _ _) => []
| t_result _ => []
end.
Hint Unfold term_keys.

Definition config_keys (c : config) :=
match c with
| C b os rs term => List.concat [backend_keys b; ostream_keys os]
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

Lemma cons_equal :
  forall {A: Type} (x : A) y xs ys,
  x = y ->
  xs = ys ->
  x :: xs = y :: ys.
Proof using.
  crush.
Qed.

Lemma ostream_keys_dist :
  forall os1 os2,
  ostream_keys (os1 ++ os2) = ostream_keys os1 ++ ostream_keys os2.
Proof using.
  induction os1; intros.
  - crush.
  - simpl.
    destruct a; destruct o.
    + unfold ostream_keys.
      simpl.
      apply IHos1.
    + unfold ostream_keys.
      simpl.
      apply cons_equal; crush.
      apply IHos1.
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
List.concat (map (fun s => ostream_labels (get_ostream s)) b).
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

Fixpoint term_labels (t : term) :=
match t with
| t_var _ => []
| t_app t1 t2 => List.concat [term_labels t1; term_labels t2]
| t_abs _ _ t => term_labels t
| t_emit (l ->> op) => [l]
| t_result _ => []
end.

Definition config_labels (c : config) :=
match c with
| C b os rs term => List.concat [backend_labels b; ostream_labels os; rstream_labels rs]
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
Hint Resolve distinct_remove.

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
Hint Resolve not_in_app_comm.

Lemma not_in_remove :
  forall A (x : A) y xs,
  ~ In x (y :: xs) ->
  ~ In x xs /\ x <> y.
Proof using.
  induction xs; crush.
Qed.
Hint Resolve not_in_remove.

Lemma distinct_rotate_back_one :
  forall A (x : A) xs,
  distinct (x :: xs) ->
  distinct (xs ++ [x]).
Proof using.
  induction xs; intros; crush.
  apply distinct_remove in H.
  destruct H.
  eapply distinct_many.
  instantiate (1:=xs ++ [x]).
  instantiate (1:=a).
  crush.
  crush.
  apply List.in_app_iff in H1.
  destruct H1.
  - inv H; crush.
  - inv H0; crush.
  - apply IHxs.
    apply List.not_in_cons in H0.
    destruct H0.
    inv H; crush.
    eapply distinct_many.
    instantiate (1:=xs').
    instantiate (1:=x).
    crush.
    crush.
    crush.
Qed.

Lemma distinct_rotate_back :
  forall A (x : A) xs ys,
  distinct (xs ++ x :: ys) ->
  distinct (xs ++ ys ++ [x]).
Proof using.
  induction xs; intros.
  - simpl.
    apply distinct_rotate_back_one.
    crush.
  - simpl in *.
    apply distinct_remove in H.
    eapply distinct_many.
    instantiate (1:=(xs ++ ys ++ [x])).
    instantiate (1:=a).
    crush.
    destruct H.
    crush.
    assert (In a (xs ++ x :: ys)).
    apply List.in_app_iff in H1.
    destruct H1.
    crush.
    apply List.in_app_iff in H1.
    destruct H1.
    crush.
    crush.
    crush.
    apply IHxs.
    crush.
Qed.

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
Hint Resolve distinct_rotate.

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
Hint Resolve distinct_rotate.

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
Hint Resolve distinct_app_comm.

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
Hint Resolve distinct_remove_middle.

Lemma in_empty :
  forall A (x : A),
  In x [] -> False.
Proof using.
  intros A.
  unfold In.
  auto.
Qed.
Hint Immediate in_empty.

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
      + crush.
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
Hint Resolve distinct_concat.

Inductive well_typed : config -> Prop :=
| WT : forall c,
    distinct (config_keys c) ->
    distinct (config_labels c) ->
    well_typed c.
Hint Constructors well_typed.

Example wt : well_typed (C [<<(N 1 2); [5 ->> inc 1 []]>>; <<(N 2 3); [4 ->> inc 1 []]>>] [2 ->> inc 1 []; 3 ->> inc 1 []] [1 ->>> 2] noop).
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

Hint Rewrite List.app_assoc.
Hint Rewrite List.app_nil_r.

Axiom fresh :
  forall c b os rs l op,
  c = C b os rs (t_emit (l ->> op)) ->
  well_typed c ->
  well_typed (C b (os ++ [l ->> op]) rs (t_result l)).

Lemma well_typed_preservation :
  forall c1 c2,
  well_typed c1 ->
  c1 --> c2 ->
  well_typed c2.
Proof using.
  intros.
  inversion H0; inversion H; eapply WT; crush.
  (* S_Emit *)
  - apply fresh with (b:=b) (os:=os) (rs:=rs) (l:=l) (op:=op) in H; inv H; crush.
  - apply fresh with (b:=b) (os:=os) (rs:=rs) (l:=l) (op:=op) in H; inv H; crush.
  (* S_App auto handled *)
  (* S_App1 auto handled *)
  (* S_Empty *)
  - destruct op; crush.
  (* S_First *)
  - unfold ostream_keys in H8.
    destruct op; crush.
  - unfold backend_labels. simpl.
    unfold backend_labels in H9. simpl in H9.
    destruct op; crush.
    apply distinct_rotate.
    remember (ostream_labels os' ++ rstream_labels rs) as y.
    assert (ostream_labels os1 ++ List.concat (map (fun s : station => ostream_labels (get_ostream s)) b') ++ y =
            (ostream_labels os1 ++ List.concat (map (fun s : station => ostream_labels (get_ostream s)) b')) ++ y) by crush.
    rewrite H1.
    rewrite List.app_assoc in H9.
    apply distinct_rotate_rev with (x:=l) in H9.
    crush.
  (* S_Add *)
  - apply distinct_rotate_rev. crush.
  - unfold backend_labels. simpl.
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
  (* S_FuseInc *)
  - admit.
Admitted.
(* Qed. *)

Reserved Notation "c1 '==' c2" (at level 40).
Inductive cequiv : config -> config -> Prop :=
| cequiv_refl : forall c, c == c
| cequiv_permutation : forall b os rs rs' term, Permutation.Permutation rs rs' -> C b os rs term == C b os rs' term
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

(* put multi step here instead of the == case *)
(* TODO change this to use star *)

Notation "cx -v cy" := (exists cu cv, (exists n, cx -->*[n] cu) /\ (exists m, cy -->*[m] cv) /\ cu == cv) (at level 40).
Definition goes_to (c1 : config) (c2 : config) : Prop := c1 -v c2.

Lemma goes_to_symmetric :
  forall c1 c2,
  c1 -v c2 ->
  c2 -v c1.
Proof using.
  intros.
  inversion H.
  destruct H0.
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

Lemma star_zero :
  forall {A : Type} (R : A -> A -> Prop) x y,
  star R 0 x y ->
  x = y.
Proof using.
  intros.
  inversion H; subst; clear H; crush.
Qed.
Hint Immediate star_zero.

Lemma one_star :
  forall {A : Type} R (x:A) y,
  star R 1 x y <->
  R x y.
Proof using.
  split; intros.
  - inv H.
    apply star_zero in H2; subst.
    assumption.
  - eapply Step.
    instantiate (1:=y).
    assumption.
    apply Zero.
Qed.
Hint Immediate one_star.

Lemma star_zero_exists :
  forall {A : Type} (R : A -> A -> Prop) x,
  exists m, star R m x x.
Proof using.
  intros.
  apply ex_intro with (0).
  crush.
Qed.
Hint Immediate star_zero_exists.

Lemma goes_to_refl :
  forall c,
  c -v c.
Proof using.
  intros.
  apply ex_intro with (c).
  eapply ex_intro with (c).
  crush.
Qed.
Hint Immediate goes_to_refl.

Lemma target_same_or_different :
  forall b b1 b2 b3 b4 k v k' v' os os',
  b = b1 ++ <<N k v; os>> :: b2 ->
  b = b3 ++ <<N k' v'; os'>> :: b4 ->
  (b1 = b3 /\ b2 = b4 /\ k = k' /\ v = v' /\ os = os') \/
  (exists (b' : backend) b'' b''', b = b' ++ <<N k v; os>> :: b'' ++ <<N k' v'; os'>> :: b''') \/
  (exists (b' : backend) b'' b''', b = b' ++ <<N k' v'; os'>> :: b'' ++ <<N k v; os>> :: b''').
Proof.
Admitted.

Lemma target_unique :
  forall b b' b1 b2 b3 b4 k v os os0 rs0 t0,
  well_typed (C b os0 rs0 t0) ->
  b = b' ->
  b = b1 ++ [<<N k v; os>>] ++ b2 ->
  b' = b3 ++ [<<N k v; os>>] ++ b4 ->
  (b1 = b3 /\ b2 = b4).
Proof.
Admitted.
Hint Resolve target_unique.

Ltac ssame := subst; match goal with
                     | [ H : C _ _ _ _ = C _ _ _ _ |- _ ] => inversion H
                     end; subst.
Ltac got := eapply ex_intro; eapply ex_intro; split; try split.
Ltac one_step := apply ex_intro with (1); apply one_star.
Ltac gotw X := got; try instantiate (1:=X); try one_step.

Lemma list_apps :
  forall {A : Type} (xs : list A),
  exists x y, xs = x ++ y.
Proof using.
  intros.
  induction xs.
  - eapply ex_intro.
    eapply ex_intro.
    instantiate (1:=[]).
    instantiate (1:=[]).
    crush.
  - destruct IHxs.
    destruct H.
    eapply ex_intro.
    eapply ex_intro.
    instantiate (1:=x0).
    instantiate (1:=a::x).
    crush.
Qed.

Lemma list_snoc :
  forall {A : Type} xs' (x : A) xs,
  xs = x :: xs' ->
  exists y ys,
  xs = ys ++ [y].
Proof using.
  intros A xs'.
  induction xs'; intros.
  - eapply ex_intro; eapply ex_intro.
    instantiate (1:=x).
    instantiate (1:=[]).
    crush.
  - remember (a :: xs') as xxs.
    apply IHxs' with (xs:=xxs) (x:=a) in Heqxxs.
    destruct Heqxxs.
    destruct H0.
    eapply ex_intro.
    eapply ex_intro.
    instantiate (1:=x0).
    instantiate (1:=x::x1).
    crush.
Qed.

Lemma well_typed_backend_key_find :
  forall c b os rs t b1 b2 b3 b4 v1 v2 os1 os2 k,
  well_typed c ->
  c = C b os rs t ->
  b = b1 ++ <<N k v1; os1>> :: b2 ->
  b = b3 ++ <<N k v2; os2>>:: b4 ->
  b1 = b3 /\ b2 = b4 /\ v1 = v2 /\ os1 = os2.
Proof.
Admitted.

Lemma frontend_rstream_extension :
  forall rs t t' lr,
  C [] [] rs t --> C [] [] rs t' ->
  C [] [] (lr :: rs) t --> C [] [] (lr :: rs) t'.
Proof.
  intros rs t t' lr H.
  inversion H; ssame.
  - destruct os.
    + inversion H1.
    + inversion H1.
Admitted.
Hint Resolve frontend_rstream_extension.

Lemma frontend_no_value :
  forall rs t t' s ty te,
  C [] [] rs t --> C [] [] rs t' ->
  ~ (t =  t_abs s ty te).
Proof using.
  intros rs t t' s ty te H.
  inversion H; ssame.
  - crush.
  - crush.
  - crush.
  - destruct b1; crush.
  - destruct b1; crush.
  - destruct b1; crush.
Qed.
Hint Resolve frontend_no_value.

Lemma frontend_deterministic :
  forall rs t t' t'',
  C [] [] rs t --> C [] [] rs t' ->
  C [] [] rs t --> C [] [] rs t'' ->
  t' = t''.
Proof.
  intros rs t t' t'' H1 H2.
  inversion H1; inversion H2; subst.
  - destruct os.
    + inversion H0.
    + inversion H0.
Admitted.
Hint Resolve frontend_deterministic.

Lemma local_confluence_p1 :
  forall cx cy cz,
  well_typed cx ->
  cx --> cy ->
  cx --> cz ->
  (cy -v cz).
Proof using.
  (* intros cx cy cz WTcx cxcy cxcz. *)
  intros cx cy cz WT cxcy cxcz.
  (* generalize dependent cxcz. *)
  (* induction cxcy; intros cxcz. *)
  inversion cxcy.
  (* S_Emit *)
  - inversion cxcz; ssame.
    (* S_Emit *)
    + crush.
    (* S_App auto handled *)
    (* S_App1 auto handled *)
    (* S_Empty *)
    + gotw (C [] (os' ++ [l ->> op]) (l0 ->>> final op0 :: rs0) (t_result l)).
      * eapply S_Empty; crush.
      * eapply S_Emit; crush.
      * crush.
    (* S_First *)
    + gotw (C (<< n1; os1 ++ [l0 ->> op0] >> :: b') (os' ++ [l ->> op]) rs0 (t_result l)).
      * eapply S_First; crush.
      * eapply S_Emit; crush.
      * crush.
    (* S_Add *)
    + gotw (C (<< N k v; [] >> :: b0) ( os' ++ [l ->> op]) (l0 ->>> final (add k v) :: rs0) (t_result l)).
      * eapply S_Add; crush.
      * eapply S_Emit; crush.
      * crush.
    (* S_Inc *)
    + gotw (C (b1 ++ << N k (v + incby); l0 ->> inc incby (remove Nat.eq_dec k ks) :: os1'' >> :: b2) (os0 ++ [l ->> op]) rs0 (t_result l)).
      * eapply S_Inc; crush.
      * eapply S_Emit; crush.
      * crush.
    (* S_Last *)
    + gotw (C (b1 ++ [<< n1; os1' >>]) (os0 ++ [l ->> op]) (l0 ->>> final op0 :: rs0) (t_result l)).
      * eapply S_Last; crush.
      * eapply S_Emit; crush.
      * crush.
    (* S_FuseInc *)
    + gotw (C (b1 ++ << n; os1 ++ l0 ->> inc (incby + incby') ks :: os2 >> :: b2) (os0 ++ [l ->> op]) (l' ->>> final (inc incby' ks) :: rs0) (t_result l)).
      * eapply S_FuseInc; crush.
      * eapply S_Emit; crush.
      * crush.
  (* S_App *)
  - inversion cxcz; ssame.
    (* S_Emit auto handled *)
    (* S_App *)
    + crush.
    (* S_App1 *)
    + apply frontend_no_value with (s:=x) (ty:=T) (te:=t12) in H4; crush.
    (* S_Empty *)
    + gotw (C [] os' (l ->>> final op :: rs0) (#[ x := v2] t12)).
      * eapply S_Empty; crush.
      * eapply S_App; crush.
      * crush.
    (* S_First *)
    + gotw (C (<< n1; os1 ++ [l ->> op] >> :: b') os' rs0 (#[ x := v2] t12)).
      * eapply S_First; crush.
      * eapply S_App; crush.
      * crush.
    (* S_Add *)
    + gotw (C (<< N k v; [] >> :: b0) os' (l ->>> final (add k v) :: rs0) (#[ x := v2] t12)).
      * eapply S_Add; crush.
      * eapply S_App; crush.
      * crush.
    (* S_Inc *)
    + gotw (C (b1 ++ << N k (v + incby); l ->> inc incby (remove Nat.eq_dec k ks) :: os1'' >> :: b2) os0 rs0 (#[ x := v2] t12)).
      * eapply S_Inc; crush.
      * eapply S_App; crush.
      * crush.
    (* S_Last *)
    + gotw (C (b1 ++ [<< n1; os1' >>]) os0 (l ->>> final op :: rs0) (#[ x := v2] t12)).
      * eapply S_Last; crush.
      * eapply S_App; crush.
      * crush.
    (* S_FuseInc *)
    + admit.
  (* S_App1 *)
  - inversion cxcz; ssame.
    (* S_Emit auto handled *)
    (* S_App *)
    + apply frontend_no_value with (s:=x) (ty:=T) (te:=t12) in H0; crush.
    (* S_App1 *)
    + apply frontend_deterministic with (t':=t1'0) in H0; crush.
    (* S_Empty *)
    + gotw (C [] os' (l ->>> final op :: rs0) (t_app t1' t2)).
      * eapply S_Empty; crush.
      * eapply S_App1; crush.
      * crush.
    (* S_First *)
    + gotw (C (<< n1; os1 ++ [l ->> op] >> :: b') os' rs0 (t_app t1' t2)).
      * eapply S_First; crush.
      * eapply S_App1; crush.
      * crush.
    (* S_Add *)
    + gotw (C (<< N k v; [] >> :: b0) os' (l ->>> final (add k v) :: rs0) (t_app t1' t2)).
      * eapply S_Add; crush.
      * eapply S_App1; crush.
      * crush.
    (* S_Inc *)
    + gotw (C (b1 ++ << N k (v + incby); l ->> inc incby (remove Nat.eq_dec k ks) :: os1'' >> :: b2) os0 rs0 (t_app t1' t2)).
      * eapply S_Inc; crush.
      * eapply S_App1; crush.
      * crush.
    (* S_Last *)
    + gotw (C (b1 ++ [<< n1; os1' >>]) os0 (l ->>> final op :: rs0) (t_app t1' t2)).
      * eapply S_Last; crush.
      * eapply S_App1; crush.
      * crush.
    (* S_FuseInc *)
    + admit.
  (* S_Empty *)
  - inversion cxcz; ssame.
    (* S_Emit *)
    + gotw (C [] (os' ++ [l0 ->> op0]) (l ->>> final op :: rs0) (t_result l0)).
      * eapply S_Emit; crush.
      * eapply S_Empty; crush.
      * crush.
    (* S_App *)
    + gotw (C [] os' (l ->>> final op :: rs0) (#[ x := v2] t12)).
      * eapply S_App; crush.
      * eapply S_Empty; crush.
      * crush.
    (* S_App1 *)
    + gotw (C [] os' (l ->>> final op :: rs0) (t_app t1' t2)).
      * eapply S_App1; crush.
      * eapply S_Empty; crush.
      * crush.
    (* S_Empty *)
    + crush.
    (* S_First auto handled *)
    (* S_Add *)
    + crush.
    (* S_Inc *)
    + destruct b1; crush.
    (* S_Last *)
    + destruct b1; crush.
    (* S_FuseInc *)
    + admit.
  (* S_First *)
  - inversion cxcz; ssame.
    (* S_Emit *)
    + gotw (C (<< n1; os1 ++ [l ->> op] >> :: b') (os' ++ [l0 ->> op0]) rs0 (t_result l0)).
      * eapply S_Emit; crush.
      * eapply S_First; crush.
      * crush.
    (* S_App *)
    + gotw (C (<< n1; os1 ++ [l ->> op] >> :: b') os' rs0 (#[ x := v2] t12)).
      * eapply S_App; crush.
      * eapply S_First; crush.
      * crush.
    (* S_App1 *)
    + gotw (C (<< n1; os1 ++ [l ->> op] >> :: b') os' rs0 (t_app t1' t2)).
      * eapply S_App1; crush.
      * eapply S_First; crush.
      * crush.
    (* S_Empty *)
    + crush.
    + crush.
    (* S_Add auto handled *)
    (* S_Inc *)
    + destruct b1; simpl in *.
      * gotw (C (<< N k (v + incby); l0 ->> inc incby (remove Nat.eq_dec k ks) :: os1'' ++ [l ->> op] >> :: b2)  os' rs0 term1).
        { inv H0; eapply S_Inc with (b1:=[]); crush. }
        { inv H0; eapply S_First with (os1:=l0 ->> inc incby (remove Nat.eq_dec k ks) :: os1''); crush. }
        { crush. }
      * gotw (C (<< n1; os1 ++ [l ->> op] >> :: b1 ++ << N k (v + incby); l0 ->> inc incby (remove Nat.eq_dec k ks) :: os1'' >> :: b2) os' rs0 term1).
        { inv H0. eapply S_Inc with (b1:=<< n1; os1 ++ [l ->> op] >> :: b1); crush. }
        { inv H0. eapply S_First; crush. }
        { crush. }
    (* S_Last *)
    + crush.
      {
      destruct b1; eapply ex_intro; eapply ex_intro; intros.
      (* b1 = [] *)
      - split; try split.
        + simpl in *. instantiate (1 := C [<< n1; os1' ++ [l ->> op]>>] os' (l0 ->>> final op0 :: rs0) term1).
          inversion H6.
          one_step; eapply S_Last with (b1 := []); crush.
        + simpl in *. instantiate (1 := C [<< n1; os1' ++ [l ->> op]>>] os' (l0 ->>> final op0 :: rs0) term1).
          inversion H6.
          one_step; eapply S_First; crush.
        + crush.
      (* b1 != [] *)
      - split; try split.
        + instantiate (1 := C (<< n1; os1 ++ [l ->> op] >> :: b1 ++ [<< n0; os1' >>]) os' (l0 ->>> final op0 :: rs0) term1).
          inversion H6.
          one_step; eapply S_Last with (b1 := << n1; os1 ++ [l ->> op] >> :: b1); crush.
        + instantiate (1 := C (<< n1; os1 ++ [l ->> op] >> :: b1 ++ [<< n0; os1' >>]) os' (l0 ->>> final op0 :: rs0) term1).
          inversion H6.
          one_step; eapply S_First; crush.
        + crush.
      }
    (* S_FuseInc *)
    + admit.
  (* S_Add *)
  - inversion cxcz.
    (* S_Emit *)
    + ssame. gotw (C (<< N k v; [] >> :: b0) (os' ++ [l0 ->> op]) (l ->>> final (add k v) :: rs0) (t_result l0)).
      * eapply S_Emit; crush.
      * eapply S_Add; crush.
      * crush.
    (* S_App *)
    + ssame. gotw (C (<< N k v; [] >> :: b0) os' (l ->>> final (add k v) :: rs0) (#[ x := v2] t12)).
      * eapply S_App; crush.
      * eapply S_Add; crush.
      * crush.
    (* S_App1 *)
    + ssame. gotw (C (<< N k v; [] >> :: b0) os' (l ->>> final (add k v) :: rs0) (t_app t1' t2)).
      * eapply S_App1; crush.
      * eapply S_Add; crush.
      * crush.
    (* S_Empty *)
    + crush. inversion H4. crush.
    (* S_First *)
    + crush. inversion H4. crush.
    (* S_Add *)
    + crush. inversion H4. crush.
    (* S_Inc *)
    + crush.
      {
      destruct b1; eapply ex_intro; eapply ex_intro; intros.
      (* b1 = [] *)
      - split; try split.
        + simpl in *. instantiate (1 := C (<< N k v; [] >> :: << N k0 (v0 + incby); l0 ->> inc incby (remove Nat.eq_dec k0 ks) :: os1'' >> :: b2) os' (l ->>> k :: rs) term0).
          inversion H4.
          one_step; eapply S_Inc with (b1 := [<< N k v; [] >>]); crush.
        + simpl in *. instantiate (1 := C (<< N k v; [] >> :: << N k0 (v0 + incby); l0 ->> inc incby (remove Nat.eq_dec k0 ks) :: os1'' >> :: b2) os' (l ->>> k :: rs) term0).
          inversion H4.
          one_step; eapply S_Add; crush.
        + crush.
      (* b1 != [] *)
      - split; try split.
        + simpl in *. instantiate (1 := C (<< N k v; [] >> :: s :: b1 ++ << N k0 (v0 + incby); l0 ->> inc incby (remove Nat.eq_dec k0 ks) :: os1'' >> :: b2) os' (l ->>> k :: rs) term0).
          inversion H4.
          one_step; eapply S_Inc with (b1 := << N k v; [] >> :: s :: b1); crush.
        + simpl in *. instantiate (1 := C (<< N k v; [] >> :: s :: b1 ++ << N k0 (v0 + incby); l0 ->> inc incby (remove Nat.eq_dec k0 ks) :: os1'' >> :: b2) os' (l ->>> k :: rs) term0).
          inversion H4.
          one_step; eapply S_Add; crush.
        + crush.
      }
    (* S_Last *)
    + crush.
      {
      destruct b1; eapply ex_intro; eapply ex_intro; intros.
      (* b1 = [] *)
      - split; try split.
        + simpl in *. instantiate (1 := C (<< N k v; [] >> :: [<< n1; os1' >>]) os' (l0 ->>> final op :: l ->>> k :: rs) term0).
          inversion H4.
          one_step; eapply S_Last with (b1 := [<<N k v; []>>]); crush.
        + simpl in *. instantiate (1 := C (<< N k v; [] >> :: [<< n1; os1' >>]) os' (l ->>> k :: l0 ->>> final op :: rs) term0).
          inversion H4.
          one_step; eapply S_Add; crush.
        + crush.
      (* b1 != [] *)
      - split; try split.
        + simpl in *. instantiate (1:=C (<< N k v; [] >> :: s :: b1 ++ [<< n1; os1' >>]) os' (l0 ->>> final op :: l ->>> k :: rs0) term0).
          inv H4.
          one_step; eapply S_Last with (b1 := << N k v; [] >> :: s :: b1); crush.
        + simpl in *. instantiate (1:=C (<< N k v; [] >> :: s :: b1 ++ [<< n1; os1' >>]) os' (l ->>> k :: l0 ->>> final op :: rs0) term0).
          inv H4.
          one_step; eapply S_Add; crush.
        + crush.
      }
    (* S_FuseInc *)
    + admit.
  (* S_Inc *)
  - inversion cxcz.
    (* S_Emit *)
    + ssame. gotw (C (b1 ++ << N k (v + incby); l ->> inc incby (remove Nat.eq_dec k ks) :: os1'' >> :: b2) (os0 ++ [l0 ->> op]) rs0 (t_result l0)).
      * eapply S_Emit; crush.
      * eapply S_Inc; crush.
      * crush.
    (* S_App *)
    + ssame. gotw (C (b1 ++ << N k (v + incby); l ->> inc incby (remove Nat.eq_dec k ks) :: os1'' >> :: b2) os0 rs0 (#[ x := v2] t12)).
      * eapply S_App; crush.
      * eapply S_Inc; crush.
      * crush.
    (* S_App1 *)
    + ssame. gotw (C (b1 ++ << N k (v + incby); l ->> inc incby (remove Nat.eq_dec k ks) :: os1'' >> :: b2) os0 rs0 (t_app t1' t2)).
      * eapply S_App1; crush.
      * eapply S_Inc; crush.
      * crush.
    (* S_Empty *)
    + crush. destruct b1; crush.
    (* S_First *)
    + crush.
      {
      destruct b1; eapply ex_intro; eapply ex_intro; intros.
      (* b1 = [] *)
      - split; try split.
        + simpl in *. instantiate (1:=C (<< N k (v + incby); l ->> inc incby (remove Nat.eq_dec k ks) :: os1'' ++ [l0 ->> op] >> :: b2) os' rs term0).
          inv H8.
          one_step; eapply S_First with (os1:=l ->> inc incby (remove Nat.eq_dec k ks) :: os1''); crush.
        + simpl in *. instantiate (1:=C (<< N k (v + incby); l ->> inc incby (remove Nat.eq_dec k ks) :: os1'' ++ [l0 ->> op] >> :: b2) os' rs term0).
          inv H8.
          one_step; eapply S_Inc with (b1:=[]); crush.
        + crush.
      (* b1 != [] *)
      - split; try split.
        + simpl in *. instantiate (1:=C (<< n1; os2 ++ [l0 ->> op] >> :: b1 ++ << N k (v + incby); l ->> inc incby (remove Nat.eq_dec k ks) :: os1'' >> :: b2) os' rs term0).
          inv H8.
          one_step; eapply S_First; crush.
        + simpl in *. instantiate (1:=C (<< n1; os2 ++ [l0 ->> op] >> :: b1 ++ << N k (v + incby); l ->> inc incby (remove Nat.eq_dec k ks) :: os1'' >> :: b2) os' rs term0).
          inv H8.
          one_step; eapply S_Inc with (b1:=<< n1; os2 ++ [l0 ->> op] >> :: b1); crush.
        + crush.
      }
    (* S_Add *)
    + crush.
      {
      destruct b1; eapply ex_intro; eapply ex_intro; intros.
      (* b1 = [] *)
      - split; try split.
        + simpl in *. instantiate (1:=C (<< N k0 v0; [] >> :: << N k (v + incby); l ->> inc incby (remove Nat.eq_dec k ks) :: os1'' >> :: b2) os' (l0 ->>> k0 :: rs) term0).
          inv H8.
          one_step; eapply S_Add with (b:=<< N k (v + incby); l ->> inc incby (remove Nat.eq_dec k ks) :: os1'' >> :: b2); crush.
        + simpl in *. instantiate (1:=C (<< N k0 v0; [] >> :: << N k (v + incby); l ->> inc incby (remove Nat.eq_dec k ks) :: os1'' >> :: b2) os' (l0 ->>> k0 :: rs) term0).
          inv H8.
          one_step; eapply S_Inc with (b1:=[<< N k0 v0; [] >>]); crush.
        + crush.
      (* b1 != [] *)
      - split; try split.
        + simpl in *. instantiate (1:=C (<< N k0 v0; [] >> :: s :: b1 ++ << N k (v + incby); l ->> inc incby (remove Nat.eq_dec k ks) :: os1'' >> :: b2) os' (l0 ->>> k0 :: rs) term0).
          inv H8.
          one_step; eapply S_Add with (b:=s :: b1 ++ << N k (v + incby); l ->> inc incby (remove Nat.eq_dec k ks) :: os1'' >> :: b2); crush.
        + simpl in *. instantiate (1:=C (<< N k0 v0; [] >> :: s :: b1 ++ << N k (v + incby); l ->> inc incby (remove Nat.eq_dec k ks) :: os1'' >> :: b2) os' (l0 ->>> k0 :: rs) term0).
          inv H8.
          one_step; eapply S_Inc with (b1:=<< N k0 v0; [] >> :: s :: b1); crush.
        + crush.
      }
    (* S_Inc *)
    + ssame.
      {
      apply target_same_or_different with (b1:=b1) (b2:=b2) (b3:=b3) (b4:=b4) (k:=k) (v:=v) (k':=k0) (v':=v0) (os:=l ->> inc incby ks :: os1'') in H0.
      - destruct H0; try destruct H.
        (* Same target *)
        + destruct H0; destruct H1; destruct H2; subst. inversion H3. subst. crush.
        (* First first *)
        + destruct H; destruct H; destruct H.
          assert (b1 = x).
          {
            apply target_unique with (b1:=b1) (b2:=b2) (b3:=x) (b4:=x0 ++ << N k0 v0; l0 ->> inc incby0 ks0 :: os1''0 >> :: x1) (os0:=os0) (rs0:=rs0) (t0:=term1) (b:=b1 ++ << N k v; l ->> inc incby ks :: os1'' >> :: b2) in H; crush.
          }
          rewrite H0 in *.
          apply List.app_inv_head in H.
          inversion H.
          rewrite H2 in *.
          assert (b3 = x ++ << N k v; l ->> inc incby ks :: os1'' >> :: x0).
          {
            inversion H8.
            apply target_unique with (b1:=x ++ << N k v; l ->> inc incby ks :: os1'' >> :: x0) (b2:=x1) (b3:=b3) (b4:=b4) (os0:=os0) (rs0:=rs0) (t0:=term1) (b:=b1 ++ << N k v; l ->> inc incby ks :: os1'' >> :: b2) in H3; crush.
          }
          rewrite H1 in *.
          assert (b4 = x1).
          {
            inversion H8.
            apply target_unique with (b1:=x ++ << N k v; l ->> inc incby ks :: os1'' >> :: x0) (b2:=x1) (b3:=x ++ << N k v; l ->> inc incby ks :: os1'' >> :: x0) (b4:=b4) (os0:=os0) (rs0:=rs0) (t0:=term1) (b:=b1 ++ << N k v; l ->> inc incby ks :: os1'' >> :: b2) in H4; crush.
          }
          got.
          * instantiate (1:=C ((x ++ << N k (v + incby); l ->> inc incby (remove Nat.eq_dec k ks) :: os1'' >> :: x0) ++ << N k0 (v0 + incby0); l0 ->> inc incby0 (remove Nat.eq_dec k0 ks0) :: os1''0 >> :: x1) os0 rs0 term1).
            one_step; eapply S_Inc with (b1:=x ++ << N k (v + incby); l ->> inc incby (remove Nat.eq_dec k ks) :: os1'' >> :: x0); crush.
          * instantiate (1:=C (x ++ << N k (v + incby); l ->> inc incby (remove Nat.eq_dec k ks) :: os1'' >> :: x0 ++ << N k0 (v0 + incby0); l0 ->> inc incby0 (remove Nat.eq_dec k0 ks0) :: os1''0 >> :: x1) os0 rs0 term1).
            one_step; eapply S_Inc with (b1:=x); crush.
          * crush.
        (* First second *)
        + destruct H; destruct H; destruct H.
          apply target_unique with (os:=l ->> inc incby ks :: os1'') (k:=k) (v:=v) (b1:=b1) (b2:=b2) (b3:=x ++ << N k0 v0; l0 ->> inc incby0 ks0 :: os1''0 >> :: x0) (b4:=x1) (os0:=os0) (rs0:=rs0) (t0:=term1) (b:=b1 ++ << N k v; l ->> inc incby ks :: os1'' >> :: b2) in H; crush.
          got.
          * instantiate (1:= C (x ++ << N k0 (v0 + incby0); l0 ->> inc incby0 (remove Nat.eq_dec k0 ks0) :: os1''0 >> :: x0 ++ << N k (v + incby); l ->> inc incby (remove Nat.eq_dec k ks) :: os1'' >> :: x1) os0 rs0 term1).
            one_step; eapply S_Inc; crush.
          * instantiate (1:= C ((b3 ++ << N k0 (v0 + incby0); l0 ->> inc incby0 (remove Nat.eq_dec k0 ks0) :: os1''0 >> :: x0) ++ << N k (v + incby); l ->> inc incby (remove Nat.eq_dec k ks) :: os1'' >> :: x1) os0 rs0 term1).
            one_step; eapply S_Inc; crush.
            inversion H8.
            apply target_unique with (b1:=x) (b2:=x0 ++ << N k v; l ->> inc incby ks :: os1'' >> :: x1) (b3:=b3) (b4:=b4) (os0:=os0) (rs0:=rs0) (t0:=term1) (b:=x ++ << N k0 v0; l0 ->> inc incby0 ks0 :: os1''0 >> :: x0 ++ << N k v; l ->> inc incby ks :: os1'' >> :: x1) in H0; crush.
          * inversion H8.
            apply target_unique with (b1:=x) (b2:=x0 ++ << N k v; l ->> inc incby ks :: os1'' >> :: x1) (b3:=b3) (b4:=b4) (os0:=os0) (rs0:=rs0) (t0:=term1) (b:=x ++ << N k0 v0; l0 ->> inc incby0 ks0 :: os1''0 >> :: x0 ++ << N k v; l ->> inc incby ks :: os1'' >> :: x1) in H0; crush.
      - crush.
      }
    (* S_Last *)
    + crush.
      {
      destruct b2.
      (* b2 = [] *)
      - ssame.
        apply List.app_inj_tail in H0.
        destruct H0.
        inversion H0.
        crush.
      (* b2 != [] *)
      - ssame.
        remember (s :: b2) as bend.
        assert (exists y ys, bend = ys ++ [y]) by (apply list_snoc with (xs:=bend) (x:=s) (xs':=b2); crush).
        destruct H; destruct H.
        inv H.
        rewrite H1 in *.
        assert (b1 ++ << N k v; l ->> inc incby ks :: os1'' >> :: x0 ++ [x]=(b1 ++ << N k v; l ->> inc incby ks :: os1'' >> :: x0) ++ [x]) by crush.
        rewrite H in H0.
        apply List.app_inj_tail in H0.
        destruct H0.
        rewrite H2 in *.
        eapply ex_intro; eapply ex_intro; split; try split.
        + instantiate (1:=C ((b1 ++ << N k (v + incby); l ->> inc incby (remove Nat.eq_dec k ks) :: os1'' >> :: x0) ++ [<< n1;  os1'0 >>]) os0 (l0 ->>> final op :: rs0) term1).
          one_step; eapply S_Last; crush.
        + instantiate (1:=C (b1 ++ << N k (v + incby); l ->> inc incby (remove Nat.eq_dec k ks) :: os1'' >> :: x0 ++ [<< n1;  os1'0 >>]) os0 (l0 ->>> final op :: rs0) term1).
          one_step; eapply S_Inc; crush.
        + crush.
      }
    (* S_FuseInc *)
    + admit.
  (* S_Last *)
  - inversion cxcz.
    (* S_Emit *)
    + ssame. gotw (C (b1 ++ [<< n1; os1' >>]) (os0 ++ [l0 ->> op0]) (l ->>> final op :: rs0) (t_result l0)).
      * eapply S_Emit; crush.
      * eapply S_Last; crush.
      * crush.
    (* S_App *)
    + ssame. gotw (C (b1 ++ [<< n1; os1' >>]) os0 (l ->>> final op :: rs0) (#[ x := v2] t12)).
      * eapply S_App; crush.
      * eapply S_Last; crush.
      * crush.
    (* S_App1 *)
    + ssame. gotw (C (b1 ++ [<< n1; os1' >>]) os0 (l ->>> final op :: rs0) (t_app t1' t2)).
      * eapply S_App1; crush.
      * eapply S_Last; crush.
      * crush.
    (* S_Empty *)
    + crush. destruct b1; crush.
    (* S_First *)
    + subst.
      {
      destruct b1.
      (* b1 = [] *)
      - simpl in *. inv H6. eapply ex_intro. eapply ex_intro.
        split; try split.
        + instantiate (1:=C [<< n0; os1' ++ [l0 ->> op0] >>] os' (l ->>> final op :: rs0) term1).
          one_step; eapply S_First; crush.
        + instantiate (1:=C [<< n0; os1' ++ [l0 ->> op0] >>] os' (l ->>> final op :: rs0) term1).
          simpl in *.
          one_step; eapply S_Last with (b1:=[]) (os1':=os1' ++ [l0 ->> op0]); crush.
        + crush.
      (* b1 != [] *)
      - simpl in *. inv H6. eapply ex_intro. eapply ex_intro.
        split; try split.
        + instantiate (1:=C (<< n0; os2 ++ [l0 ->> op0] >> :: b1 ++ [<< n1; os1' >>])  os' (l ->>> final op :: rs0) term1).
          one_step; eapply S_First; crush.
        + instantiate (1:=C (<< n0; os2 ++ [l0 ->> op0] >> :: b1 ++ [<< n1; os1' >>])  os' (l ->>> final op :: rs0) term1).
          one_step; eapply S_Last with (b1:=<< n0; os2 ++ [l0 ->> op0] >> :: b1); crush.
        + crush.
      }
    (* S_Add *)
    + subst.
      {
      destruct b1.
      (* b1 = [] *)
      - simpl in *. inv H6. eapply ex_intro. eapply ex_intro.
        split; try split.
        + instantiate (1:=C [<< N k0 v; [] >>; << n1; os1' >>] os' (l0 ->>> k0 :: l ->>> final op :: rs0) term1).
          one_step; eapply S_Add with (b:=[<< n1; os1' >>]); crush.
        + instantiate (1:=C [<< N k0 v; [] >>; << n1; os1' >>] os' (l ->>> final op :: l0 ->>> k0 :: rs0) term1).
          one_step; eapply S_Last with (b1:=[<< N k0 v; [] >>]); crush.
        + crush.
      (* b1 != [] *)
      - simpl in *. inv H6. eapply ex_intro. eapply ex_intro.
        split; try split.
        + instantiate (1:=C (<< N k0 v; [] >> :: s :: b1 ++ [<< n1; os1' >>]) os' (l0 ->>> k0 :: l ->>> final op :: rs0) term1).
          one_step; eapply S_Add; crush.
        + instantiate (1:=C (<< N k0 v; [] >> :: s :: b1 ++ [<< n1; os1' >>]) os' (l ->>> final op :: l0 ->>> k0 :: rs0) term1).
          one_step; eapply S_Last with (b1:=<< N k0 v; [] >> :: s :: b1); crush.
        + crush.
      }
    (* S_Inc *)
    + ssame.
      {
      destruct b3.
      (* b3 = [] *)
      - apply List.app_inj_tail in H0.
        inv H0.
        inv H1.
        crush.
      (* b3 != [] *)
      - remember (s :: b3) as bend.
        assert (exists y ys, bend = ys ++ [y]) by (apply list_snoc with (xs:=bend) (x:=s) (xs':=b3); crush).
        destruct H; destruct H.
        inv H0.
        eapply ex_intro; eapply ex_intro; split; try split.
        + instantiate (1:=C (b2 ++ << N k0 (v + incby); l0 ->> inc incby (remove Nat.eq_dec k0 ks) :: os1'' >> :: x0 ++ [<< n1; os1' >>]) os0 (l ->>> final op :: rs0) term1).
          one_step; eapply S_Inc; crush. inv H6. rewrite H in H2.
          assert (b2 ++ << N k0 v; l0 ->> inc incby ks :: os1'' >> :: x0 ++ [x] = (b2 ++ << N k0 v; l0 ->> inc incby ks :: os1'' >> :: x0) ++ [x]) by crush.
          rewrite H0 in H2.
          apply List.app_inj_tail in H2.
          crush.
        + instantiate (1:=C ((b2 ++ << N k0 (v + incby); l0 ->> inc incby (remove Nat.eq_dec k0 ks) :: os1'' >> :: x0) ++ [<< n1; os1' >>]) os0 (l ->>> final op :: rs0) term1).
          inv H6.
          rewrite H in *.
          assert (b2 ++ << N k0 v; l0 ->> inc incby ks :: os1'' >> :: x0 ++ [x] = (b2 ++ << N k0 v; l0 ->> inc incby ks :: os1'' >> :: x0) ++ [x]) by crush.
          rewrite H0 in H2.
          apply List.app_inj_tail in H2.
          destruct H2.
          rewrite <- H4 in *.
          one_step; eapply S_Last with (b1:=b2 ++ << N k0 (v + incby); l0 ->> inc incby (remove Nat.eq_dec k0 ks) :: os1'' >> :: x0); crush.
        + crush.
      }
    (* S_Last *)
    + ssame. apply List.app_inj_tail in H0. inv H0. inv H1. crush.
    (* S_FuseInc *)
    + admit.
  (* S_FuseInc *)
  - admit.
Admitted.
(* Qed. *)

Lemma local_confluence_p2 :
  forall cx cy cz,
  (* well_typed cx -> *)
  cx == cy ->
  cx --> cz ->
  cz -v cy.
Proof.
  intros cx cy cz equiv_cxcy cxcz.
  inversion cxcz; admit.
Admitted.

(* TODO need to start x and x' as sim, not x and x as equal *)
(* if we do that, then remove multi step (enhance equivalence a bit)
   then we have a chance of matching the paper version *)
Definition diamond_property_modulo {A : Type} (R1 R2 sim : A -> A -> Prop) :=
    forall x y z,
    R1 x y ->
    R2 x z ->
    exists u v, (exists n, star R2 n y u) /\ (exists m, star R1 m z v) /\ sim u v.

Lemma diamond_modulo_symmetric : forall {A : Type} (R1 R2 : A -> A -> Prop) (sim : A -> A -> Prop),
  (equiv A sim) ->
  diamond_property_modulo R1 R2 sim -> diamond_property_modulo R2 R1 sim.
Proof using.
  intros A R1 R2 sim Hequivsim H.
  unfold diamond_property_modulo in *.
  intros x y z xy xz.
  apply H with (x:=x) (y:=z) in xy; try assumption.
  destruct xy.
  destruct H0.
  destruct H0.
  destruct H1.
  repeat (eapply ex_intro).
  split; try split.
  instantiate (1 := x1).
  assumption.
  instantiate (1 := x0).
  assumption.
  destruct Hequivsim.
  crush.
Qed.

Lemma clos_refl_star : forall {A} R x y, clos_refl_trans_1n A R x y <-> exists n, star R n x y.
Proof using.
  split; intros.
  - induction H.
    + eapply ex_intro. crush.
    + destruct IHclos_refl_trans_1n.
      eapply ex_intro.
      eapply Step.
      instantiate (1 := y).
      assumption.
      instantiate (1 := x0).
      assumption.
  - destruct H.
    induction H.
    + crush.
    + constructor 2 with (y := y); crush.
Qed.
Hint Resolve clos_refl_star.

Lemma star_zero_in :
  forall {A : Type} (R : A -> A -> Prop) n x y,
  star (star R 0) n x y ->
  x = y.
Proof using.
  intros A R.
  induction n; intros.
  apply star_zero in H; auto.
  inv H.
  apply IHn in H2; subst.
  apply star_zero in H1; auto.
Qed.

Lemma star_zero_in_add :
  forall {A : Type} (R : A -> A -> Prop) n x y,
  x = y ->
  star (star R 0) n x y.
Proof using.
  intros A R.
  induction n; intros.
  - crush.
  - apply IHn in H.
    eapply Step.
    instantiate (1:=x).
    apply Zero.
    assumption.
Qed.

Lemma star_trans :
  forall {A : Type} (R : A -> A -> Prop) x y z m n,
  star R m x y ->
  star R n y z ->
  star R (m+n) x z.
Proof using.
  intros.
  generalize dependent z.
  generalize dependent x.
  generalize dependent y.
  generalize dependent n.
  induction m; induction n; intros.
  - crush.
    apply star_zero in H; subst; crush.
  - simpl.
    apply star_zero in H; subst; crush.
  - apply star_zero in H0; subst.
    assert (S m = S m + 0) by crush.
    rewrite H0 in H.
    crush.
  - simpl in *.
    inversion H; subst; clear H.
    inversion H0; subst; clear H0.
    eapply Step.
    instantiate (1:=y0).
    assumption.
    eapply IHm.
    instantiate (1:=y).
    assumption.
    eapply Step.
    instantiate (1:=y1).
    assumption.
    assumption.
Qed.

Lemma star_prod_reverse :
  forall {A : Type} (R : A -> A -> Prop) m n x y,
  star R (n*m) x y ->
  star (star R m) n x y.
Admitted.

Lemma star_prod :
  forall {A : Type} (R : A -> A -> Prop) m n x y,
  star (star R m) n x y ->
  star R (n*m) x y.
Proof using.
  intros A R.
  induction m; induction n; intros; simpl in *.
  - apply star_zero in H.
    rewrite H.
    apply Zero.
  - assert (n * 0 = 0) by crush.
    rewrite H0.
    apply star_zero_in in H.
    crush.
  - apply star_zero in H; crush.
  - inv H.
    apply IHn in H2.
    assert (S (m + n * S m) = (S m) + n * S m) by crush.
    rewrite H.
    eapply star_trans with (y1:=y0); crush.
Qed.

Lemma clos_refl_trans_trans :
  forall {A : Type} R x y z,
  clos_refl_trans_1n A R x y ->
  clos_refl_trans_1n A R y z ->
  clos_refl_trans_1n A R x z.
Proof using.
  intros A R x y z xy.
  induction xy; intros xz.
  - assumption.
  - crush.
    constructor 2 with (y:=y); crush.
Qed.

Lemma double_clos_remove :
  forall {A : Type} R x y,
  clos_refl_trans_1n A (clos_refl_trans_1n A R) x y ->
  clos_refl_trans_1n A R x y.
Proof using.
  intros A R x y xy.
  induction xy.
  - crush.
  - apply clos_refl_trans_trans with (y0:=y); crush.
Qed.

Lemma double_clos :
  forall {A : Type} R x y,
  clos_refl_trans_1n A R x y ->
  clos_refl_trans_1n A (clos_refl_trans_1n A R) x y.
Proof using.
  intros A R x y xy.
  induction xy.
  - crush.
  - constructor 2 with (y:=y).
    constructor 2 with (y:=y); crush.
    crush.
Qed.

Lemma star_comm :
  forall {A : Type} R n m (x : A) y,
  star (star R m) n x y ->
  star (star R n) m x y.
Proof using.
Admitted.

(* proof structure for diamond property confluence taken from
   https://coq.discourse.group/t/diamond-property-implies-confluence/620
   but adapted for multi step and equiv relation. *)
(* An out-of-coq proof can be found in the technical report, with inspiration from
   Huet, Gérard. "Confluent reductions: Abstract properties and applications
   to term rewriting systems: Abstract properties and applications to term
   rewriting systems." Journal of the ACM (JACM) 27.4 (1980): 797-821.
*)

Lemma on_the_left'_modulo :
  forall {A : Type} (R1 R2 sim : A -> A -> Prop),
  equiv A sim ->
  diamond_property_modulo R1 R2 sim -> forall n, diamond_property_modulo (star R1 n) R2 sim.
Admitted.

Lemma on_the_right'_modulo :
  forall {A : Type} (R1 R2 sim : A -> A -> Prop),
  equiv A sim ->
  diamond_property_modulo R1 R2 sim -> forall n, diamond_property_modulo R1 (star R2 n) sim.
Admitted.

Lemma diamond_property_modulo_implies_mn_confluence :
  forall {A : Type} (R sim : A -> A -> Prop),
  equiv A sim ->
  diamond_property_modulo R R sim -> forall m n, diamond_property_modulo (star R m) (star R n) sim.
Proof using.
  intros A R sim simequiv diamond.
  intros m n.
  apply on_the_left'_modulo with (n0:=m) in diamond.
  apply on_the_right'_modulo with (n0:=n) in diamond.
  assumption.
  assumption.
  assumption.
Qed.

Theorem diamond_property_modulo_implies_confluence :
  forall {A : Type} (R sim : A -> A -> Prop),
  equiv A sim ->
  diamond_property_modulo R R sim -> diamond_property_modulo (clos_refl_trans_1n A R) (clos_refl_trans_1n A R) sim.
Proof using.
  unfold diamond_property_modulo in *.
  intros A R sim equivsim local_diamond x y z xy xz.
  apply clos_refl_star in xy.
  apply clos_refl_star in xz.
  destruct xy as [n xy].
  destruct xz as [m xz].
  eapply diamond_property_modulo_implies_mn_confluence with (m0:=n) (n0:=m) in local_diamond.
  unfold diamond_property_modulo in *.
  eapply local_diamond with (z := z) in xy.
  destruct xy as [u].
  destruct H as [v].
  destruct H.
  destruct H as [n' yv].
  destruct H0.
  destruct H as [m' zv].
  eapply ex_intro.
  eapply ex_intro.
  split.
  apply clos_refl_star.
  apply double_clos.
  apply clos_refl_star.
  eapply ex_intro.
  instantiate (1:=u).
  instantiate (1:=n'*m).
  apply star_prod.
  assumption.
  split.
  apply clos_refl_star.
  apply double_clos.
  apply clos_refl_star.
  eapply ex_intro.
  instantiate (1:=v).
  instantiate (1:=m'*n).
  apply star_prod.
  assumption.
  assumption.
  assumption.
  assumption.
Qed.

(*********************)

Instance cequiv_reflective : Reflexive cequiv := cequiv_refl.
Instance cequiv_sym : Symmetric cequiv := cequiv_symmetric.
Instance cequiv_transitive : Transitive cequiv := cequiv_trans.
Program Instance cequiv_equivalence : Equivalence cequiv.

Axiom start_at_well_typed :
  forall c, well_typed c.

Lemma dgcalc_local_confluence :
  diamond_property_modulo step step cequiv.
Proof using.
  unfold diamond_property_modulo.
  intros.
  eapply local_confluence_p1 with (cx:=x) (cy:=y) (cz:=z); crush.
  apply start_at_well_typed.
Qed.

Theorem dgcalc_confluence :
  diamond_property_modulo (clos_refl_trans_1n config step) (clos_refl_trans_1n config step) cequiv.
Proof using.
  eapply diamond_property_modulo_implies_confluence.
  unfold equiv.
  split.
  apply cequiv_reflective.
  split.
  apply cequiv_transitive.
  apply cequiv_sym.
  apply dgcalc_local_confluence.
Qed.

(*********************)
(*********************)
(*********************)

Inductive clos_refl_trans {A : Type} (R : A -> A -> Prop) : A -> A -> Prop :=
| CRTZero : forall x, clos_refl_trans R x x
| CRTStep : forall x y, clos_refl_trans R x y -> forall z, R y z -> clos_refl_trans R x z.
Hint Constructors clos_refl_trans.

Lemma snoc_clos_refl_trans_1n {A : Type} (R : A -> A -> Prop) :
  forall x y, clos_refl_trans_1n A R x y -> forall z, R y z -> clos_refl_trans_1n A R x z.
Admitted.

Lemma cons_clos_refl_trans {A : Type} (R : A -> A -> Prop) :
  forall y z, clos_refl_trans R y z -> forall x, R x y -> clos_refl_trans R x z.
Admitted.

Lemma clos_refl_trans_equiv {A : Type} R :
  forall x y, clos_refl_trans R x y <-> clos_refl_trans_1n A R x y.
Admitted.

Definition diamond_property {A : Type} (R1 R2 : A -> A -> Prop) :=
    forall x y z,
    R1 x y ->
    R2 x z ->
    exists w, clos_refl_trans R2 y w /\ clos_refl_trans R1 z w.

Lemma on_the_left' :
  forall {A : Type} (R : A -> A -> Prop),
  (forall x y z,
   R x y ->
   R x z ->
   exists w, clos_refl_trans R y w /\ clos_refl_trans R z w) ->
  forall x y z,
  clos_refl_trans R x y ->
  clos_refl_trans R x z ->
  exists w, clos_refl_trans R y w /\ clos_refl_trans R z w.
Proof.
  intros A R Hdiamond x y z Hxy Hxz.

Lemma on_the_left' :
  forall {A : Type} (R : A -> A -> Prop),
  (forall x y z,
   R x y ->
   R x z ->
   exists w, clos_refl_trans R y w /\ clos_refl_trans R z w) ->
  forall x y z,
  clos_refl_trans R x y ->
  R x z ->
  exists w, clos_refl_trans R y w /\ clos_refl_trans R z w.
Proof.
  intros A R Hdiamond x y z Hxy Hxz.
  induction Hxy.
  - apply ex_intro with (z); split.
    apply CRTStep with (x); crush.
    crush.
  - apply IHHxy in Hxz.
    destruct Hxz.
    destruct H0.
apply clos_refl_trans_equiv in H.
    inv H.
    + admit.
    +


apply cons_clos_refl_trans with (z0:=y0) in H.

    crush.
Qed.

Lemma on_the_left :
  forall {A : Type} (R1 R2 : A -> A -> Prop),
  diamond_property R1 R2 -> diamond_property (clos_refl_trans R1) R2.
Proof.
  intros A R1 R2 local_diamond.

(*
could try proving this new style without the star, and with that diff definition of clos_trans_refl
*)

(* NEW IDEA
try to prove the paper version, by introducing normal forms
*)

(*
but first try to prove current version on pen/paper

long term we might not need multi step if we can have some smarter form of equivalence,
then maybe we could get rid of admits since i think we can prove
1) single step
2) single step sim (??)
but not
3) multi step
4) multi step sim
*)

Definition diamond_property' {A : Type} (R1 R2 : A -> A -> Prop) :=
    forall x y z,
    R1 x y ->
    R2 x z ->
    exists w, (exists n, star R2 n y w) /\ (exists m, star R1 m z w).

(* TODO might need normal form lemma, then we can say they meet up at the normal form *)
Lemma on_the_left' :
  forall {A : Type} (R : A -> A -> Prop),
  (forall x y z, R x y -> R x z -> exists w, (exists n, star R n y w) /\ (exists m, star R m z w)) ->
  forall o,
  (forall x y z, star R o x y -> R x z -> exists w, (exists n, star R n y w) /\ (exists m, star R m z w)).
Proof using.
  intros A R H o.
  induction o; intros x y z xy xz.
  - apply star_zero in xy; subst.
    apply ex_intro with (z).
    split.
    apply ex_intro with (1).
    apply one_star.
    assumption.
    apply ex_intro with (0).
    crush.
  - inv xy.
    rename y0 into x'.
    rename H1 into xx'.
    rename H2 into x'y.


    inv xy.
    assert ({y0 = z} + {y0 <> z}) by admit.
    + destruct H0; subst.
      * apply ex_intro with (y).
        split.
        apply ex_intro with (0); crush.
        apply ex_intro with (o); crush.
      * remember xz as xz'. clear Heqxz'.
        apply H with (y:=y0) in xz.
        destruct xz.
        destruct H0.
        destruct H0.
        destruct H3.
        {
          destruct x1.
          - apply star_zero in H0; subst.
        }

apply IHo with (z:=z) in H2.

    remember xz. clear Heqr.
    apply H with (z:=y0) in xz.
    destruct xz.
    destruct H0.
    destruct H0.
    destruct H3.
    apply IHo with () in H2.

    apply IHo with (z:=z) in H2.

    apply ex_intro with ().

  diamond_property' R1 R2 -> forall n, diamond_property' (star R1 n) R2 sim.
