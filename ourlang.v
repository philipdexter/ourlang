
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
| add : key -> payload -> operation
| getpay : key -> operation.
Hint Constructors operation.

Definition target op :=
match op with
| inc _ ks => ks
| add _ _ => []
| getpay k => [k]
end.
Hint Unfold target.

Definition not_add op : Prop :=
match op with
| inc _ _ => True
| add _ _ => False
| getpay _ => True
end.
Hint Unfold not_add.

Definition final op : payload :=
match op with
| inc _ ks => 0
| add k _ => k
| getpay _ => 0
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

(* TODO need S_Claim *)
(* TODO s_app1 and s_app2 need to allow emit (don't use [] for result of ostream) *)
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
| S_App2 : forall c b os rs v1 t2' t2,
    c = C b os rs (t_app v1 t2) ->
    value v1 ->
    C [] [] rs t2 --> C [] [] rs t2' ->
    c --> C b os rs (t_app v1 t2')
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
| S_GetPay : forall c b os rs b1 s1 s1' os1 os1' b2 k v ks l term,
    c = C b os rs term ->
    b = b1 ++ s1 :: b2 ->
    s1 = <<(N k v); os1>> ->
    os1 = l ->> getpay k :: os1' ->
    s1' = <<(N k v); os1'>> ->
    In k ks ->
    c --> C (b1 ++ s1' :: b2) os (l ->>> v :: rs) term
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
| S_Prop : forall c b os rs n1 n2 os1 os2 b1 b2 l op term,
    c = C b os rs term ->
    ~ (In (getKey n1) (target op)) ->
    b = b1 ++ <<n1; l ->> op :: os1>> :: <<n2; os2>> :: b2 ->
    c --> C (b1 ++ <<n1; os1>> :: <<n2; os2 ++ [l ->> op]>> :: b2) os rs term
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
| t_emit (_ ->> getpay _) => []
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
    + unfold ostream_keys.
      simpl.
      eauto.
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

Lemma distinct_rotate_front :
  forall A (x : A) y xs,
  distinct (x :: y :: xs) ->
  distinct (y :: x :: xs).
Proof using.
  intros.
  assert (x :: y :: xs = [x] ++ y :: xs) by crush.
  rewrite H0 in H.
  clear H0.
  apply distinct_rotate_rev in H.
  crush.
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
Hint Rewrite List.app_comm_cons.

Axiom fresh :
  forall c b os rs l op,
  c = C b os rs (t_emit (l ->> op)) ->
  well_typed c ->
  well_typed (C b (os ++ [l ->> op]) rs (t_result l)).

Lemma cons_app :
  forall {A: Type} (x : A) xs,
  x :: xs = [x] ++ xs.
Proof using.
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
  (* S_Emit *)
  - apply fresh with (b:=b) (os:=os) (rs:=rs) (l:=l) (op:=op) in H; inv H; crush.
  - apply fresh with (b:=b) (os:=os) (rs:=rs) (l:=l) (op:=op) in H; inv H; crush.
  (* S_App auto handled *)
  (* S_App1 auto handled *)
  (* S_App2 auto handled *)
  (* S_Empty *)
  - destruct op; crush.
  (* S_First *)
  - unfold ostream_keys in H8.
    destruct op; crush.
  - unfold backend_labels. simpl.
    unfold backend_labels in H9. simpl in H9.
    destruct op; crush.
    + apply distinct_rotate.
      remember (ostream_labels os' ++ rstream_labels rs) as y.
      assert (ostream_labels os1 ++ List.concat (map (fun s : station => ostream_labels (get_ostream s)) b') ++ y =
              (ostream_labels os1 ++ List.concat (map (fun s : station => ostream_labels (get_ostream s)) b')) ++ y) by crush.
      rewrite H1.
      rewrite List.app_assoc in H9.
      apply distinct_rotate_rev with (x:=l) in H9.
      crush.
    + apply distinct_rotate.
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
  (* S_GetPay *)
  - unfold backend_labels at 2.
    simpl.
    assert (backend_labels b1 ++
                           (ostream_labels os1' ++ List.concat (map (fun s : station => ostream_labels (get_ostream s)) b2))
                           ++ ostream_labels os ++ l :: rstream_labels rs =
    (backend_labels b1 ++
                    (ostream_labels os1' ++ List.concat (map (fun s : station => ostream_labels (get_ostream s)) b2))
                    ++ ostream_labels os) ++ l :: rstream_labels rs) by crush.
    rewrite H1. clear H1.
    apply distinct_rotate.
    apply distinct_rotate_rev in H10.
    crush.
  (* S_Last *)
  - apply distinct_rotate_rev in H9.
    rewrite List.app_assoc.
    rewrite List.app_assoc.
    apply distinct_rotate.
    unfold backend_labels at 2.
    crush.
  (* S_FuseInc *)
  - assert (<< n; os1 ++ l ->> inc incby ks :: l' ->> inc incby' ks :: os2 >> :: b2 = [<< n; os1 ++ l ->> inc incby ks :: l' ->> inc incby' ks :: os2 >>] ++ b2) by crush.
    rewrite H1 in H6.
    rewrite backend_labels_dist in H6.
    unfold backend_labels at 2 in H6.
    simpl in H6.
    rewrite ostream_labels_dist in H6.
    simpl in H6.
    assert (<< n; os1 ++ l ->> inc (incby + incby') ks :: os2 >> :: b2 = [<< n; os1 ++ l ->> inc (incby + incby') ks :: os2 >>] ++ b2) by crush.
    rewrite H2.
    clear H1; clear H2.
    rewrite backend_labels_dist.
    unfold backend_labels at 2.
    simpl.
    rewrite ostream_labels_dist.
    simpl.
    repeat (rewrite <- List.app_assoc).
    repeat (rewrite <- List.app_assoc in H6).
    remember (backend_labels b1 ++ ostream_labels os1) as y.
    rewrite -> List.app_assoc.
    rewrite -> List.app_assoc in H6.
    rewrite <- Heqy in *.
    simpl in *.
    rewrite -> cons_app.
    assert (l' :: rstream_labels rs = [l'] ++ rstream_labels rs) by crush.
    rewrite H1.
    clear H1.
    rewrite -> cons_app in H6.
    apply distinct_app_comm.
    simpl.
    apply distinct_app_comm in H6.
    simpl in H6.
    rewrite -> cons_app.
    assert ([l] ++ (ostream_labels os2 ++ backend_labels b2 ++ ostream_labels os ++ l' :: rstream_labels rs) ++ y = ([l] ++ ostream_labels os2 ++ backend_labels b2 ++ ostream_labels os) ++ (l' :: rstream_labels rs ++ y)) by crush.
    rewrite H1.
    clear H1.
    apply distinct_rotate.
    simpl.
    apply distinct_rotate_front.
    crush.
  (* S_Prop *)
  - rewrite cons_app.
    rewrite backend_labels_dist.
    unfold backend_labels at 3.
    simpl.
    rewrite ostream_labels_dist.
    unfold ostream_labels at 2.
    simpl.
    remember (List.concat (map (fun s : station => ostream_labels (get_ostream s)) b2)) as y.
    remember (ostream_labels os ++ rstream_labels rs) as x.
    unfold backend_labels at 2.
    simpl.
    rewrite List.app_nil_r.
    repeat (rewrite <- List.app_assoc).
    repeat (rewrite <- List.app_assoc in H7).
    apply distinct_app_comm in H7.
    rewrite <- cons_app.
    assert (backend_labels b1 ++ ostream_labels os1 ++ ostream_labels os2 ++ l :: y ++ x = (backend_labels b1 ++ ostream_labels os1 ++ ostream_labels os2) ++ l :: y ++ x) by crush.
    rewrite H1; clear H1.
    apply distinct_rotate.
    apply distinct_rotate in H7.
    apply distinct_app_comm in H7.
    crush.
Qed.

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

Lemma distinct_center :
  forall {A : Type} (xs : list A) x ys xs' ys' l l',
  distinct l ->
  l = l' ->
  l = xs ++ x :: ys ->
  l = xs' ++ x :: ys' ->
  xs = xs' /\ ys = ys'.
Proof using.
  induction xs; intros.
  - simpl in *.
    subst.
    destruct xs'.
    + crush.
    + inv H2.
      rewrite List.app_comm_cons in H.
      apply distinct_rotate_rev in H.
      inversion H; subst.
      inv H0.
      crush.
  - simpl in *.
    subst.
    destruct xs'.
    + simpl in H2.
      rewrite List.app_comm_cons in H.
      apply distinct_rotate_rev in H.
      inv H2.
      inversion H; subst.
      inv H0.
      crush.
    + simpl in *.
      inv H2.
      eapply IHxs in H3; eauto.
      * destruct H3; split; eauto; crush.
      * inversion H; crush.
Qed.

Lemma distinct_nodes :
  forall b os0 rs0 term0,
  well_typed (C b os0 rs0 term0) ->
  distinct b.
Proof using.
  induction b; intros; eauto.
  assert (well_typed (C b os0 rs0 term0)).
  {
  inv H.
  unfold config_keys in H0.
  unfold backend_keys in H0.
  simpl in H0.
  rewrite cons_app in H0.
  apply distinct_concat in H0.
  unfold config_labels in H1.
  unfold backend_labels in H1.
  simpl in H1.
  rewrite <- List.app_assoc in H1.
  apply distinct_concat in H1.
  destruct H0.
  destruct H1.
  split.
  - unfold config_keys.
    crush.
  - unfold config_labels.
    crush.
  }
  apply IHb in H0.
  eapply distinct_many.
  - instantiate (1:=b).
    instantiate (1:=a).
    reflexivity.
  - intro.
    inv H.
    unfold config_keys in H2.
    apply distinct_concat in H2.
    destruct H2.
    clear H2 H3.
    apply List.in_split in H1.
    destruct H1. destruct H1.
    subst.
    rewrite List.app_comm_cons in H.
    rewrite backend_keys_dist in H.
    crush.
    rewrite cons_app in H.
    rewrite List.app_assoc in H.
    apply distinct_rotate_rev in H.
    simpl in H.
    inversion H; subst.
    crush.
  - assumption.
Qed.

Lemma distinct_ops :
  forall b1 b2 n os os0 rs0 term0,
  well_typed (C (b1 ++ <<n; os>> :: b2) os0 rs0 term0) ->
  distinct os.
Proof using.
  induction os; intros; eauto.
  assert (well_typed (C (b1 ++ << n; os >> :: b2) os0 rs0 term0)).
  {
    inv H.
    split.
    - crush.
    - unfold config_labels in H1.
      rewrite backend_labels_dist in H1.
      simpl in H1.
      unfold backend_labels at 2 in H1.
      destruct a.
      simpl in H1.
      rewrite <- List.app_assoc in H1.
      apply distinct_rotate_rev in H1.
      rewrite cons_app in H1.
      apply distinct_concat in H1.
      destruct H1.
      crush.
      unfold backend_labels at 2.
      simpl.
      crush.
  }
  apply IHos in H0.
  eapply distinct_many.
  - instantiate (1:=os).
    instantiate (1:=a).
    reflexivity.
  - intro.
    inv H.
    unfold config_labels in H3.
    apply distinct_concat in H3.
    destruct H3.
    apply List.in_split in H1.
    destruct H1. destruct H1.
    subst.
    rewrite List.app_comm_cons in H.
    rewrite backend_labels_dist in H.
    apply distinct_concat in H.
    destruct H.
    unfold backend_labels in H1.
    simpl in H1.
    destruct a.
    rewrite ostream_labels_dist in H1.
    simpl in H1.
    assert (n0 :: (ostream_labels x ++ n0 :: ostream_labels x0) ++ List.concat (map (fun s : station => ostream_labels (get_ostream s)) b2) = (n0 :: ostream_labels x) ++ n0 :: ostream_labels x0 ++ List.concat (map (fun s : station => ostream_labels (get_ostream s)) b2)) by crush.
    rewrite H4 in H1; clear H4.
    apply distinct_rotate_rev in H1.
    simpl in H1.
    inversion H1.
    crush.
  - assumption.
Qed.

Lemma target_unique :
  forall b b' b1 b2 b3 b4 k v os os0 rs0 t0,
  well_typed (C b os0 rs0 t0) ->
  b = b' ->
  b = b1 ++ [<<N k v; os>>] ++ b2 ->
  b' = b3 ++ [<<N k v; os>>] ++ b4 ->
  (b1 = b3 /\ b2 = b4).
Proof using.
  intros.
  eapply distinct_center with (l:=b).
  eapply distinct_nodes; eauto.
  instantiate (1:=b').
  assumption.
  instantiate (1:=<<N k v; os>>).
  assumption.
  crush.
Qed.
Hint Resolve target_unique.

Lemma op_unique :
  forall b n b1 b2 lop os os' os1 os2 os3 os4 os0 rs0 t0,
  well_typed (C b os0 rs0 t0) ->
  b = b1 ++ <<n; os>> :: b2 ->
  os = os' ->
  os = os1 ++ lop :: os2 ->
  os' = os3 ++ lop :: os4 ->
  (os1 = os3 /\ os2 = os4).
Proof using.
  intros.
  apply distinct_center with (l:=os) (l':=os') (x:=lop); eauto; crush.
  apply distinct_ops with (term0:=t0) (rs0:=rs0) (os0:=os0) (b1:=b1) (b2:=b2) (n:=n).
  crush.
Qed.
Hint Resolve op_unique.

Axiom unique_lop :
  forall os l op op' n b1 b2 os0 rs0 term0,
  well_typed (C (b1 ++ <<n; os>> :: b2) os0 rs0 term0) ->
  In (l ->> op) os ->
  In (l ->> op') os ->
  op = op'.

Lemma op_unique' :
  forall b n b1 b2 op l op' os os' os1 os2 os3 os4 os0 rs0 t0,
  well_typed (C b os0 rs0 t0) ->
  b = b1 ++ <<n; os>> :: b2 ->
  os = os' ->
  os = os1 ++ l ->> op :: os2 ->
  os' = os3 ++ l ->> op' :: os4 ->
  (os1 = os3 /\ os2 = os4 /\ op = op').
Proof using.
  intros.
  assert (op = op') by (eapply unique_lop with (b1:=b1) (b2:=b2) (l:=l) (op:=op) (op':=op'); subst; eauto; crush).
  split; try split; try assumption; try reflexivity; subst.
  eapply op_unique with (os1:=os1) (os2:=os2) (os3:=os3) (os4:=os4); eauto.
  eapply op_unique with (os1:=os1) (os2:=os2) (os3:=os3) (os4:=os4); eauto.
Qed.

Axiom unique_key :
  forall k v os v' os' b os0 rs0 term0,
  well_typed (C b os0 rs0 term0) ->
  In <<N k v; os>> b ->
  In <<N k v'; os'>> b ->
  v = v' /\ os = os'.

Lemma target_unique' :
  forall b b' b1 b2 b3 b4 k v v' os' os os0 rs0 t0,
  well_typed (C b os0 rs0 t0) ->
  b = b' ->
  b = b1 ++ [<<N k v; os>>] ++ b2 ->
  b' = b3 ++ [<<N k v'; os'>>] ++ b4 ->
  (b1 = b3 /\ b2 = b4 /\ v = v' /\ os = os').
Proof using.
  intros.
  assert (v = v') by (eapply unique_key with (k:=k) (v:=v) (v':=v') (os:=os) (os':=os'); eauto; subst; crush).
  assert (os = os') by (eapply unique_key with (k:=k) (v:=v) (v':=v') (os:=os) (os':=os'); eauto; subst; crush).
  subst.
  split; try split; try split; try assumption; try reflexivity.
  eapply target_unique with (b1:=b1) (b2:=b2) (b3:=b3) (b4:=b4); eauto.
  eapply target_unique with (b1:=b1) (b2:=b2) (b3:=b3) (b4:=b4); eauto.
Qed.
Hint Resolve target_unique.

Lemma target_same_or_different :
  forall b b1 b2 b3 b4 k v k' v' os os' os0 rs0 term0,
  well_typed (C b os0 rs0 term0) ->
  b = b1 ++ <<N k v; os>> :: b2 ->
  b = b3 ++ <<N k' v'; os'>> :: b4 ->
  (b1 = b3 /\ b2 = b4 /\ k = k' /\ v = v' /\ os = os') \/
  (exists (b' : backend) b'' b''', b = b' ++ <<N k v; os>> :: b'' ++ <<N k' v'; os'>> :: b''') \/
  (exists (b' : backend) b'' b''', b = b' ++ <<N k' v'; os'>> :: b'' ++ <<N k v; os>> :: b''').
Proof using.
  intros.
  destruct (Nat.eq_dec k k') as [keq|kneq].
  - rewrite keq in *. clear keq.
    assert (v = v') by (eapply target_unique'; eauto; crush).
    assert (os = os') by (eapply target_unique'; eauto; crush).
    assert (b1 = b3 /\ b2 = b4) by (eapply target_unique with (b:=b) (b1:=b1) (b2:=b2) (b3:=b3) (b4:=b4); eauto; crush).
    left.
    crush.
  - subst.
    assert (In << N k' v'; os' >> (b1 ++ << N k v; os >> :: b2)) by crush.
    apply List.in_app_or in H0.
    destruct H0.
    * right.
      right.
      apply List.in_split in H0.
      destruct H0.
      destruct H0.
      subst.
      assert ((x ++ << N k' v'; os' >> :: x0) ++ << N k v; os >> :: b2 = x ++ << N k' v'; os' >> :: x0 ++ << N k v; os >> :: b2) by crush.
      eauto.
    * right.
      left.
      apply List.in_split in H0.
      destruct H0.
      destruct H0.
      {
      destruct x.
      - crush.
      - inversion H0.
        eauto.
      }
Qed.

Lemma op_same_or_different :
  forall b1 b2 n os0 rs0 term0 os os1 os2 os3 os4 lop lop',
  well_typed (C (b1 ++ <<n;os>> :: b2) os0 rs0 term0) ->
  os = os1 ++ lop :: os2 ->
  os = os3 ++ lop' :: os4 ->
  (os1 = os3 /\ os2 = os4 /\ lop = lop') \/
  (exists (os' : ostream) os'' os''', os = os' ++ lop :: os'' ++ lop' :: os''') \/
  (exists (os' : ostream) os'' os''', os = os' ++ lop' :: os'' ++ lop :: os''').
Proof.
  intros.
  destruct lop as [l op].
  destruct lop' as [l' op'].
  destruct (Nat.eq_dec l l') as [leq|lneq].
  - subst.
    left.
    eapply op_unique' with (os1:=os1) (os2:=os2) in H1; eauto.
    split; try split; crush.
  - assert (In (l' ->> op') (os1 ++ l ->> op :: os2)) by crush.
    apply List.in_app_or in H2.
    destruct H2.
    + right.
      right.
      apply List.in_split in H2.
      destruct H2.
      destruct H2.
      subst.
      assert ((x ++ l' ->> op' :: x0) ++ l ->> op :: os2 = x ++ l' ->> op' :: x0 ++ l ->> op :: os2) by crush.
      eauto.
    + right.
      left.
      apply List.in_split in H2.
      destruct H2.
      destruct H2.
      {
      destruct x.
      - crush.
      - inversion H2.
        crush.
        eauto.
      }
Qed.


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
  - crush.
  - destruct b1; crush.
  - destruct b1; crush.
  - destruct b1; crush.
  - destruct b1; crush.
  - destruct b1; crush.
Qed.
Hint Resolve frontend_no_value.

Lemma frontend_no_value' :
  forall rs t t',
  C [] [] rs t --> C [] [] rs t' ->
  ~ (value t).
Proof using.
  intros rs t t' H.
  inversion H; ssame.
  - destruct os; crush.
  - unfold not; intros. inversion H0.
  - unfold not; intros. inversion H0.
  - unfold not; intros. inversion H0.
  - destruct b1; crush.
  - destruct b1; crush.
  - destruct b1; crush.
  - destruct b1; crush.
  - destruct b1; crush.
Qed.
Hint Resolve frontend_no_value'.

Lemma frontend_rstream_extension :
  forall rs t t' lr,
  C [] [] rs t --> C [] [] rs t' ->
  C [] [] (lr :: rs) t --> C [] [] (lr :: rs) t'.
Proof.
  induction t; intros.
  inversion H; subst; try (destruct os; crush); try (destruct b1; crush); try (inv H3); try (inv H4).
  - admit.
  - apply frontend_no_value' in H; crush.
  - inv H; try (destruct os; crush); try (destruct b1; crush); try (inv H3); try (inv H4).
  - apply frontend_no_value' in H; crush.
Admitted.
Hint Resolve frontend_rstream_extension.

Axiom app_reduce :
  forall rs t t' t'',
  C [] [] rs (t_app t t') --> C [] [] rs (t_app t'' t') ->
  C [] [] rs t --> C [] [] rs t''.

Lemma frontend_deterministic :
  forall t rs t',
  C [] [] rs t --> C [] [] rs t' ->
  forall t'',
  C [] [] rs t --> C [] [] rs t'' ->
  t' = t''.
Proof using.
(* TODO uncomment, takes too long so temp commenting *)
(*   induction t; intros. *)
(*   inversion H; inversion H0; try (inv H5; eapply frontend_no_value in H15; crush); try (inv H5; eapply frontend_no_value in H16; crush); try (destruct b1; crush); try (destruct os; crush). *)
(*   - inversion H; inversion H0; try (destruct os; crush); try (inv H11; inv H4; eapply frontend_no_value' in H14; crush); try (inv H12; inv H4; eapply frontend_no_value' in H15; crush); try (destruct b1; crush). *)
(*     + eapply frontend_no_value' in H7. assert (value (t_abs x T t12)) by constructor. crush. *)
(*     + assert (C [] [] rs t0 --> C [] [] rs t1'0) by (apply app_reduce with (t':=t3); assumption). *)
(*       apply IHt1 with (t':=t1'0) in H7; crush. *)
(*     + eapply frontend_no_value' in H7; crush. *)
(*     + inv H12. inv H5. eapply frontend_no_value' in H8; crush. *)
(*     + inv H12. inv H5. eapply frontend_no_value' in H15; crush. *)
(*     + inv H13. inv H5. apply IHt2 with (t':=t2'0) in H8; crush. *)
(*     Unshelve. *)
(*     auto. *)
(*     auto. *)
(*     auto. *)
(*     auto. *)
(*     auto. *)
(*     auto. *)
(*     auto. *)
(*     auto. *)
(*     auto. *)
(*     auto. *)
(*   - inversion H; inversion H0; try (destruct os; crush); try (inv H11; inv H4; eapply frontend_no_value' in H14; crush); try (inv H12; inv H4; eapply frontend_no_value' in H15; crush); try (destruct b1; crush). *)
(*   - inv H; try (destruct os; crush); try (inv H4); try (inv H5); try (destruct b1; crush). *)
(*   - inv H; try (destruct os; crush); try (inv H4); try (inv H5); try (destruct b1; crush). *)
(* Qed. *)
Admitted.
Hint Resolve frontend_deterministic.

Lemma lc_getpay :
  forall cx cy cz os rs term k v l os1 b1 b2,
  well_typed cx ->
  cx = C (b1 ++ <<N k v; l ->> getpay k :: os1>> :: b2) os rs term ->
  cy = C (b1 ++ <<N k v; os1>> :: b2) os (l ->>> v :: rs) term ->
  cx --> cy ->
  cx --> cz ->
  cy -v cz.
Proof using.
Admitted.
Hint Resolve lc_getpay.

Lemma lc_prop :
  forall cx cy cz os rs term n1 n2 l op os1 os2 b1 b2,
  well_typed cx ->
  cx = C (b1 ++ <<n1; l ->> op :: os1>> :: <<n2; os2>> :: b2) os rs term ->
  cy = C (b1 ++ <<n1; os1>> :: <<n2; os2 ++ [l ->> op]>> :: b2) os rs term ->
  cx --> cy ->
  cx --> cz ->
  ~ (In (getKey n1) (target op)) ->
  cy -v cz.
Proof using.
  intros cx cy cz os rs term n1 n2 l op os1 os2 b1 b2.
  intros WT Heqcx Heqcy cxcy cxcz.
  intros notin.
  inversion cxcz; ssame.
  (* S_Emit *)
  - gotw (C (b1 ++ << n1; os1 >> :: << n2; os2 ++ [l ->> op] >> :: b2) (os0 ++ [l0 ->> op0]) rs0 (t_result l0)); eauto.
  (* S_App *)
  - gotw (C (b1 ++ << n1; os1 >> :: << n2; os2 ++ [l ->> op] >> :: b2) os0 rs0 (#[ x := v2] t12)); eauto.
  (* S_App1 *)
  - gotw (C (b1 ++ << n1; os1 >> :: << n2; os2 ++ [l ->> op] >> :: b2) os0 rs0 (t_app t1' t2)); eauto.
  (* S_App2 *)
  - gotw (C (b1 ++ << n1; os1 >> :: << n2; os2 ++ [l ->> op] >> :: b2) os0 rs0 (t_app v1 t2')); eauto.
  (* S_Empty *)
  - destruct b1; crush.
  (* S_First *)
  - destruct b1; simpl in *.
    + inv H1.
      gotw (C (<< n0; os1 ++ [l0 ->> op0] >> :: << n2; os2 ++ [l ->> op] >> :: b2) os' rs0 term0); eauto.
      apply S_Prop with (b1:=[]) (b:=<< n0; l ->> op :: os1 ++ [l0 ->> op0] >> :: << n2; os2 >> :: b2); crush.
    + inv H1.
      gotw (C (<< n0; os3 ++ [l0 ->> op0] >> :: b1 ++ << n1;  os1 >> :: << n2; os2 ++ [l ->> op] >> :: b2) os' rs0 term0); eauto.
      repeat (rewrite List.app_comm_cons).
      eauto.
  (* S_Add *)
  - gotw (C (<< N k v; [] >> :: b1 ++ << n1; os1 >> :: << n2; os2 ++ [l ->> op] >> :: b2) os' (l0 ->>> final (add k v) :: rs0) term0); eauto.
    repeat (rewrite List.app_comm_cons).
    eauto.
  (* S_Inc *)
  - destruct n1.
    eapply target_same_or_different with (b1:=b1) (b2:=<< n2; os2 >> :: b2) (b3:=b0) (b4:=b3) (k:=n) (v:=n0) (k':=k) (v':=v) in H1; eauto.
    destruct H1; try destruct H0.
    (* Same target *)
    + destruct H1. destruct H2. destruct H3. subst.
      inv H4.
      crush.
    (* First first *)
    + destruct H0. destruct H0. destruct H0.
      eapply target_unique with (b1:=b1) (b2:=<< n2; os2 >> :: b2) (b3:=x) (b4:=x0 ++ << N k v; l0 ->> inc incby ks :: os1'' >> :: x1) in H0; crush.
      rewrite H2 in *.
      destruct x0.
      * inv H.
        simpl in *.
        eapply target_unique with (b1:=x ++ [<< N n n0; l ->> op :: os1 >>]) (b2:=x1) (b3:=b0) (b4:=b3) in H1; eauto; crush.
        inv H2.
        {
          got.
          - instantiate (1:=C ((x ++ [<< N n n0; os1 >>]) ++ << N k (v + incby); l0 ->> inc incby (remove Nat.eq_dec k ks) :: os1'' ++ [l ->> op] >> :: b3) os0 rs0 term0).
            one_step. eapply S_Inc; crush.
          - instantiate (1:=C (x ++ << N n n0; os1 >> :: << N k (v + incby); (l0 ->> inc incby (remove Nat.eq_dec k ks) :: os1'') ++ [l ->> op] >> :: b3) os0 rs0 term0).
            one_step. eapply S_Prop; crush.
          - crush.
        }
      * inv H2.
        inv H.
        eapply target_unique with (b1:=x ++ << N n n0; l ->> op :: os1 >> :: << n2; os2 >> :: x0) (b2:=x1) (b3:=b0) (b4:=b3) in H1; eauto; crush.
        {
          got.
          - instantiate (1:=C ((x ++ << N n n0; os1 >> :: << n2; os2 ++ [l ->> op] >> :: x0) ++ << N k (v + incby); l0 ->> inc incby (remove Nat.eq_dec k ks) :: os1'' >> :: b3) os0 rs0 term0).
            one_step. eapply S_Inc; crush.
          - instantiate (1:=C (x ++ << N n n0; os1 >> :: << n2; os2 ++ [l ->> op] >> :: x0 ++ << N k (v + incby); l0 ->> inc incby (remove Nat.eq_dec k ks) :: os1'' >> :: b3) os0 rs0 term0).
            one_step. eapply S_Prop; crush.
          - crush.
        }
    (* First second *)
    + destruct H0. destruct H0. destruct H0.
      eapply target_unique with (b1:=b1) (b2:=<< n2; os2 >> :: b2) (b3:=x ++ << N k v; l0 ->> inc incby ks :: os1'' >> :: x0) (b4:=x1) in H0; eauto; crush.
      inv H.
      eapply target_unique with (b1:=x) (b2:=x0 ++ << N n n0; l ->> op :: os1 >> :: << n2; os2 >> :: b2) (b3:=b0) (b4:=b3) in H1; eauto; crush.
      got.
      * instantiate (1:= C (b0 ++ << N k (v + incby); l0 ->> inc incby (remove Nat.eq_dec k ks) :: os1'' >> :: x0 ++ << N n n0; os1 >> :: << n2; os2 ++ [l ->> op] >> :: b2) os0 rs0 term0).
        one_step. eapply S_Inc; crush.
      * instantiate (1:= C ((b0 ++ << N k (v + incby); l0 ->> inc incby (remove Nat.eq_dec k ks) :: os1'' >> :: x0) ++ << N n n0; os1 >> :: << n2; os2 ++ [l ->> op] >> :: b2) os0 rs0 term0).
        one_step. eapply S_Prop; crush.
      * crush.
  (* S_GetPay *)
  - eauto.
  (* S_Last *)
  - destruct b2.
    + assert (b1 ++ [<< n1; l ->> op :: os1 >>; << n2; os2 >>] = b1 ++ [<< n1; l ->> op :: os1 >>] ++ [<< n2; os2 >>]) by crush.
      rewrite H0 in H1; clear H0.
      rewrite List.app_assoc in H1.
      apply List.app_inj_tail in H1.
      destruct H1.
      subst.
      inv H1.
      got.
      * instantiate (1:=C ((b1 ++ [<< n1; os1 >>]) ++ [<< n0; os1' ++ [l ->> op] >>]) os0 (l0 ->>> final op0 :: rs0) term0).
        one_step. eapply S_Last with (b1:=b1 ++ [<< n1; os1 >>]) (os1:=(l0 ->> op0 :: os1') ++ [l ->> op]); eauto.
        simpl.
        rewrite List.app_comm_cons.
        crush.
      * instantiate (1:=C (b1 ++ << n1; os1 >> :: [<< n0; os1' ++ [l ->> op] >>]) os0 (l0 ->>> final op0 :: rs0) term0).
        one_step. eapply S_Prop; eauto.
        crush.
      * crush.
    + remember (s :: b2) as bend.
      assert (exists y ys, bend = ys ++ [y]) by (apply list_snoc with (xs:=bend) (x:=s) (xs':=b2); crush).
      destruct H0; destruct H0.
      inv H0.
      rewrite H2 in *. clear H2.
      assert (b1 ++ << n1; l ->> op :: os1 >> :: << n2; os2 >> :: x0 ++ [x] = (b1 ++ << n1; l ->> op :: os1 >> :: << n2; os2 >> :: x0) ++ [x]) by crush.
      rewrite H0 in H1. clear H0.
      apply List.app_inj_tail in H1.
      destruct H1.
      subst.
      gotw (C (b1 ++ << n1; os1 >> :: << n2; os2 ++ [l ->> op] >> :: x0 ++ [<< n0;  os1' >>]) os0 (l0 ->>> final op0 :: rs0) term0); eauto.
      * assert (forall x, b1 ++ << n1; os1 >> :: << n2; os2 ++ [l ->> op] >> :: x0 ++ x = (b1 ++ << n1; os1 >> :: << n2; os2 ++ [l ->> op] >> :: x0) ++ x) by crush.
        repeat (rewrite H0). clear H0.
        eauto.
      * rewrite <- List.app_assoc.
        eauto.
  (* S_FuseInc *)
  - destruct n1 as [k v].
    destruct n as [k' v'].
    eapply target_same_or_different with (b1:=b1) (b2:=<< n2; os2 >> :: b2) (b3:=b0) (b4:=b3) (k:=k) (v:=v) (k':=k') (v':=v') in H1; eauto.
    destruct H1; try destruct H0.
    (* Same target *)
    + destruct H1. destruct H2. destruct H3. subst.
      destruct os3.
      * simpl in *.
        inv H4.
        {
        got.
        - instantiate (1:=C (b0 ++ << N k' v'; os4 >> :: << n2; os2 ++ [l0 ->> inc (incby + incby') ks] >> :: b2) os0 (l' ->>> final (inc incby' ks) :: rs0) term0).
          apply ex_intro with 2.
          eapply Step.
          instantiate (1:=C (b0 ++ << N k' v'; os4 >> :: << n2; (os2 ++ [l0 ->> inc incby ks]) ++ [l' ->> inc incby' ks] >> :: b2) os0 rs0 term0).
          eapply S_Prop; crush.
          apply one_star.
          assert ((os2 ++ [l0 ->> inc incby ks]) ++ [l' ->> inc incby' ks] = os2 ++ [l0 ->> inc incby ks] ++ [l' ->> inc incby' ks]) by crush.
          rewrite H0. clear H0.
          assert (forall x, b0 ++ << N k' v'; os4 >> :: x = (b0 ++ [<< N k' v'; os4 >>]) ++ x) by crush.
          rewrite H0. clear H0.
          assert (b0 ++ << N k' v'; os4 >> :: << n2; os2 ++ [l0 ->> inc (incby + incby') ks] >> :: b2 = (b0 ++ [<< N k' v'; os4 >>]) ++ << n2; os2 ++ [l0 ->> inc (incby + incby') ks] >> :: b2) by crush.
          rewrite H0. clear H0.
          eapply S_FuseInc; crush.
        - instantiate (1:=C (b0 ++ << N k' v'; os4 >> :: << n2; os2 ++ [l0 ->> inc (incby + incby') ks] >> :: b2) os0 (l' ->>> final (inc incby' ks) :: rs0) term0).
          one_step. eapply S_Prop; crush.
        - crush.
        }
      * simpl in *.
        inv H4.
        {
        got.
        - instantiate (1:=C (b0 ++ << N k' v'; os3 ++ l0 ->> inc (incby + incby') ks :: os4 >> :: << n2; os2 ++ [l ->> op] >> :: b2) os0 (l' ->>> 0 :: rs0) term0).
          one_step. eapply S_FuseInc; crush.
        - instantiate (1:=C (b0 ++ << N k' v'; os3 ++ l0 ->> inc (incby + incby') ks :: os4 >> :: << n2; os2 ++ [l ->> op] >> :: b2) os0 (l' ->>> 0 :: rs0) term0).
          one_step. eapply S_Prop; crush.
        - crush.
        }
    (* First first *)
    + destruct H0. destruct H0. destruct H0.
      destruct x0; simpl in *.
      * eapply target_unique with (b1:=b1) (b2:=<< n2; os2 >> :: b2) (b3:=x) (b4:=<< N k' v'; os3 ++ l0 ->> inc incby ks :: l' ->> inc incby' ks :: os4 >> :: x1) in H0; eauto; crush.
        inv H2.
        inv H.
        eapply target_unique with (b1:=x ++ [<< N k v; l ->> op :: os1 >>]) (b2:=x1) (b3:=b0) (b4:=b3) in H1; eauto; crush.
        {
        got.
        - instantiate (1:=C ((x ++ [<< N k v; os1 >>]) ++ << N k' v'; os3 ++ l0 ->> inc (incby + incby') ks :: os4 ++ [l ->> op] >> :: b3) os0 (l' ->>> 0 :: rs0) term0).
          one_step. eapply S_FuseInc; crush.
        - instantiate (1:=C (x ++ << N k v; os1 >> :: << N k' v'; (os3 ++ l0 ->> inc (incby + incby') ks :: os4) ++ [l ->> op] >> :: b3) os0 (l' ->>> 0 :: rs0) term0).
          one_step. eapply S_Prop; crush.
        - crush.
        }
      * eapply target_unique with (b1:=b1) (b2:=<< n2; os2 >> :: b2) (b3:=x) (b4:=s :: x0 ++ << N k' v'; os3 ++ l0 ->> inc incby ks :: l' ->> inc incby' ks :: os4 >> :: x1) in H0; eauto; crush.
        inv H.
        eapply target_unique with (b1:=x ++ << N k v; l ->> op :: os1 >> :: << n2; os2 >> :: x0) (b2:=x1) (b3:=b0) (b4:=b3) in H1; eauto; crush.
        {
        got.
        - instantiate (1:=C ((x ++ << N k v; os1 >> :: << n2; os2 ++ [l ->> op] >> :: x0) ++ << N k' v'; os3 ++ l0 ->> inc (incby + incby') ks :: os4 >> :: b3) os0 (l' ->>> 0 :: rs0) term0).
          one_step. eapply S_FuseInc; crush.
        - instantiate (1:=C (x ++ << N k v; os1 >> :: << n2; os2 ++ [l ->> op] >> :: x0 ++ << N k' v'; os3 ++ l0 ->> inc (incby + incby') ks :: os4 >> :: b3) os0 (l' ->>> 0 :: rs0) term0).
          one_step. eapply S_Prop; crush.
        - crush.
        }
    (* First second *)
    + destruct H0. destruct H0. destruct H0.
      eapply target_unique with (b1:=b1) (b2:=<< n2; os2 >> :: b2) (b3:=x ++ << N k' v'; os3 ++ l0 ->> inc incby ks :: l' ->> inc incby' ks :: os4 >> :: x0) (b4:=x1) in H0; eauto; crush.
      inv H.
      eapply target_unique with (b1:=x) (b2:=x0 ++ << N k v; l ->> op :: os1 >> :: << n2; os2 >> :: b2) (b3:=b0) (b4:=b3) in H1; eauto; crush.
      got.
      * instantiate (1:=C (b0 ++ << N k' v'; os3 ++ l0 ->> inc (incby + incby') ks :: os4 >> :: x0 ++ << N k v; os1 >> :: << n2; os2 ++ [l ->> op] >> :: b2) os0 (l' ->>> 0 :: rs0) term0).
        one_step. eapply S_FuseInc; crush.
      * instantiate (1:=C ((b0 ++ << N k' v'; os3 ++ l0 ->> inc (incby + incby') ks :: os4 >> :: x0) ++ << N k v; os1 >> :: << n2; os2 ++ [l ->> op] >> :: b2) os0 (l' ->>> 0 :: rs0) term0).
        one_step. eapply S_Prop; crush.
      * crush.
  (* S_Prop *)
  - destruct n1 as [k v].
    destruct n0 as [k' v'].
    eapply target_same_or_different with (b1:=b1) (b2:=<< n2; os2 >> :: b2) (b3:=b0) (b4:=<< n3; os4 >> :: b3) (k:=k) (v:=v) (k':=k') (v':=v') in H2; eauto.
    destruct H2; try destruct H1.
    (* Same target *)
    + inv H2.
      destruct H4. destruct H2. inv H4. inv H3. crush.
    (* First first *)
    + destruct H1. destruct H1. destruct H1.
      destruct x0.
      * simpl in *.
        eapply target_unique with (b1:=b1) (b2:=<< n2; os2 >> :: b2) (b3:=x) (b4:=<< N k' v'; l0 ->> op0 :: os3 >> :: x1) in H1; eauto; crush.
        inv H3.
        inv H.
        eapply target_unique with (b1:=x ++ [<< N k v; l ->> op :: os1 >>]) (b2:=x1) (b3:=b0) (b4:=<< n3; os4 >> :: b3) in H2; eauto; crush.
        {
        got.
        - instantiate (1:=C ((x ++ [<< N k v; os1 >>]) ++ << N k' v'; os3 ++ [l ->> op] >> :: << n3; os4 ++ [l0 ->> op0] >> :: b3) os0 rs0 term0).
          one_step. eapply S_Prop; crush.
        - instantiate (1:=C (x ++ << N k v; os1 >> :: << N k' v'; os3 ++ [l ->> op] >> :: << n3; os4 ++ [l0 ->> op0] >> :: b3) os0 rs0 term0).
          one_step. eapply S_Prop; crush.
        - crush.
        }
      * simpl in *.
        eapply target_unique with (b1:=b1) (b2:=<< n2; os2 >> :: b2) (b3:=x) (b4:=s :: x0 ++ << N k' v'; l0 ->> op0 :: os3 >> :: x1) in H1; eauto; crush.
        inv H.
        eapply target_unique with (b1:=x ++ << N k v; l ->> op :: os1 >> :: << n2; os2 >> :: x0) (b2:=x1) (b3:=b0) (b4:=<< n3; os4 >> :: b3) in H2; eauto; crush.
        {
        got.
        - instantiate (1:=C ((x ++ << N k v; os1 >> :: << n2; os2 ++ [l ->> op] >> :: x0) ++ << N k' v'; os3 >> :: << n3; os4 ++ [l0 ->> op0] >> :: b3) os0 rs0 term0).
          one_step. eapply S_Prop; crush.
        - instantiate (1:=C (x ++ << N k v; os1 >> :: << n2; os2 ++ [l ->> op] >> :: x0 ++ << N k' v'; os3 >> :: << n3; os4 ++ [l0 ->> op0] >> :: b3) os0 rs0 term0).
          one_step. eapply S_Prop; crush.
        - crush.
        }
    (* First second *)
    + destruct H1. destruct H1. destruct H1.
      destruct x0.
      * simpl in *.
        eapply target_unique with (b1:=b1) (b2:=<< n2; os2 >> :: b2) (b3:=x ++ [<< N k' v'; l0 ->> op0 :: os3 >>]) (b4:=x1) in H1; eauto; crush.
        inv H.
        eapply target_unique with (b1:=x) (b2:=<< N k v; l ->> op :: os1 >> :: << n2; os2 >> :: b2) (b3:=b0) (b4:=<< n3; os4 >> :: b3) in H2; eauto; crush.
        inv H1.
        {
        got.
        - instantiate (1:=C (b0 ++ << N k' v'; os3 >> :: << N k v; os1 ++ [l0 ->> op0] >> :: << n2; os2 ++ [l ->> op] >> :: b2) os0 rs0 term0).
          one_step. eapply S_Prop; crush.
        - instantiate (1:=C ((b0 ++ [<< N k' v'; os3 >>]) ++ << N k v; os1 ++ [l0 ->> op0] >> :: << n2; os2 ++ [l ->> op] >> :: b2) os0 rs0 term0).
          one_step. eapply S_Prop; crush.
        - crush.
        }
      * simpl in *.
        eapply target_unique with (b1:=b1) (b2:=<< n2; os2 >> :: b2) (b3:=x ++ << N k' v'; l0 ->> op0 :: os3 >> :: s :: x0) (b4:=x1) in H1; eauto; crush.
        inv H.
        eapply target_unique with (b1:=x) (b2:=s :: x0 ++ << N k v; l ->> op :: os1 >> :: << n2; os2 >> :: b2) (b3:=b0) (b4:=<< n3; os4 >> :: b3) in H2; eauto; crush.
        {
        got.
        - instantiate (1:=C (b0 ++ << N k' v'; os3 >> :: << n3; os4 ++ [l0 ->> op0] >> :: x0 ++ << N k v; os1 >> :: << n2; os2 ++ [l ->> op] >> :: b2) os0 rs0 term0).
          one_step. eapply S_Prop; crush.
        - instantiate (1:=C ((b0 ++ << N k' v'; os3 >> :: << n3; os4 ++ [l0 ->> op0] >> :: x0) ++ << N k v; os1 >> :: << n2; os2 ++ [l ->> op] >> :: b2) os0 rs0 term0).
          one_step. eapply S_Prop; crush.
        - crush.
        }
Qed.
Hint Resolve lc_prop.

Lemma lc_app2 :
  forall cx cy cz b os rs v1 t2 t2',
  well_typed cx ->
  cx = C b os rs (t_app v1 t2) ->
  cy = C b os rs (t_app v1 t2') ->
  cx --> cy ->
  cx --> cz ->
  value v1 ->
  C [] [] rs t2 --> C [] [] rs t2' ->
  cy -v cz.
Proof using.
  intros cx cy cz b os rs v1 t2 t2' WT Heqcx Heqcy cxcy cxcz.
  intros Vv1 t2t2'.
  inversion cxcz; ssame.
  (* S_Emit auto handled *)
  (* S_App *)
  + apply frontend_no_value' in t2t2'; crush.
  (* S_App1 *)
  + apply frontend_no_value' in H0; crush.
  (* S_App2 *)
  + apply frontend_deterministic with (t':=t2'0) in t2t2'; crush.
  (* S_Empty *)
  + gotw (C [] os' (l ->>> final op :: rs0) (t_app v1 t2')).
    * eapply S_Empty; crush.
    * eapply S_App2; crush.
    * crush.
  (* S_First *)
  + gotw (C (<< n1; os1 ++ [l ->> op] >> :: b') os' rs0 (t_app v1 t2')).
    * eapply S_First; crush.
    * eapply S_App2; crush.
    * crush.
  (* S_Add *)
  + gotw (C (<< N k v; [] >> :: b0) os' (l ->>> final (add k v) :: rs0) (t_app v1 t2')).
    * eapply S_Add; crush.
    * eapply S_App2; crush.
    * crush.
  (* S_Inc *)
  + gotw (C (b1 ++ << N k (v + incby); l ->> inc incby (remove Nat.eq_dec k ks) :: os1'' >> :: b2) os0 rs0 (t_app v1 t2')).
    * eapply S_Inc; crush.
    * eapply S_App2; crush.
    * crush.
  (* S_GetPay *)
  + eauto.
  (* S_Last *)
  + gotw (C (b1 ++ [<< n1; os1' >>]) os0 (l ->>> final op :: rs0) (t_app v1 t2')).
    * eapply S_Last; crush.
    * eapply S_App2; crush.
    * crush.
  (* S_FuseInc *)
  + gotw (C (b1 ++ << n; os1 ++ l ->> inc (incby + incby') ks :: os2 >> :: b2) os0 (l' ->>> final (inc incby' ks) :: rs0) (t_app v1 t2')).
    * eapply S_FuseInc; crush.
    * eapply S_App2; crush.
    * crush.
  (* S_Prop *)
  + eauto.
Qed.
Hint Resolve lc_app2.

Lemma lc_app :
  forall cx cy cz b os rs x T t12 v2,
  well_typed cx ->
  cx = C b os rs (t_app (t_abs x T t12) v2) ->
  cy = C b os rs (#[ x := v2] t12) ->
  value v2 ->
  cx --> cy ->
  cx --> cz ->
  cy -v cz.
Proof using.
  intros cx cy cz b os rs x T t12 v2 WT Heqcx Heqcy Vv2 cxcy cxcz.
  inversion cxcz; ssame.
  (* S_Emit auto handled *)
  (* S_App *)
  + crush.
  (* S_App1 *)
  + apply frontend_no_value with (s:=x) (ty:=T) (te:=t12) in H0; crush.
  (* S_App2 *)
  + eauto.
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
  (* S_GetPay *)
  + eauto.
  (* S_Last *)
  + gotw (C (b1 ++ [<< n1; os1' >>]) os0 (l ->>> final op :: rs0) (#[ x := v2] t12)).
    * eapply S_Last; crush.
    * eapply S_App; crush.
    * crush.
  (* S_FuseInc *)
  + gotw (C (b1 ++ << n; os1 ++ l ->> inc (incby + incby') ks :: os2 >> :: b2) os0 (l' ->>> final (inc incby' ks) :: rs0) (#[ x := v2] t12)).
    * eapply S_FuseInc; crush.
    * eapply S_App; crush.
    * crush.
  (* S_Prop *)
  + eauto.
Qed.
Hint Resolve lc_app.

Lemma lc_emit :
  forall cx cy cz b os rs l op,
  well_typed cx ->
  cx = C b os rs (t_emit (l ->> op)) ->
  cy = C b (os ++ [l ->> op]) rs (t_result l) ->
  cx --> cy ->
  cx --> cz ->
  cy -v cz.
Proof using.
  intros cx cy cz b os rs l op WT Heqcx Heqcy cxcy cxcz.
  inversion cxcz; ssame.
  (* S_Emit *)
  + crush.
  (* S_App auto handled *)
  (* S_App1 auto handled *)
  (* S_App2 auto handled *)
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
  (* S_GetPay *)
  + eauto.
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
  (* S_Prop *)
  + eauto.
Qed.
Hint Resolve lc_emit.

Lemma lc_app1 :
  forall cx cy cz b os rs t1 t2 t1',
  well_typed cx ->
  cx = C b os rs (t_app t1 t2) ->
  cy = C b os rs (t_app t1' t2) ->
  cx --> cy ->
  cx --> cz ->
  C [] [] rs t1 --> C [] [] rs t1' ->
  cy -v cz.
Proof using.
  intros cx cy cz b os rs t1 t2 t1' WT Heqcx Heqcy cxcy cxcz.
  intros t1t1'.
  inversion cxcz; ssame.
  (* S_Emit auto handled *)
  (* S_App *)
  + eauto.
  (* S_App1 *)
  + apply frontend_deterministic with (t':=t1'0) in t1t1'; crush.
  (* S_App2 *)
  + eauto.
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
  (* S_GetPay *)
  + eauto.
  (* S_Last *)
  + gotw (C (b1 ++ [<< n1; os1' >>]) os0 (l ->>> final op :: rs0) (t_app t1' t2)).
    * eapply S_Last; crush.
    * eapply S_App1; crush.
    * crush.
  (* S_FuseInc *)
  + gotw (C (b1 ++ << n; os1 ++ l ->> inc (incby + incby') ks :: os2 >> :: b2) os0 (l' ->>> final (inc incby' ks) :: rs0) (t_app t1' t2)).
    * eapply S_FuseInc; crush.
    * eapply S_App1; crush.
    * crush.
  (* S_Prop *)
  + eauto.
Qed.
Hint Resolve lc_app1.

Lemma lc_first :
  forall cx cy cz rs l op term n1 os1 b' os',
  well_typed cx ->
  cx = C (<< n1; os1 >> :: b') (l ->> op :: os') rs term ->
  cy = C (<< n1; os1 ++ [l ->> op] >> :: b') os' rs term ->
  not_add op ->
  cx --> cy ->
  cx --> cz ->
  cy -v cz.
Proof using.
  intros cx cy cz rs l op term0 n1 os1 b' os' WT Heqcx Heqcy Hnotnotadd cxcy cxcz.
  inversion cxcz; ssame.
  (* S_Emit *)
  + eauto.
  (* S_App *)
  + eauto.
  (* S_App1 *)
  + eauto.
  (* S_App2 *)
  + eauto.
  (* S_Empty *)
  + crush.
  (* S_First *)
  + crush.
  (* S_Add auto handled *)
  (* S_Inc *)
  + destruct b1; simpl in *.
    * gotw (C (<< N k (v + incby); l0 ->> inc incby (remove Nat.eq_dec k ks) :: os1'' ++ [l ->> op] >> :: b2)  os' rs0 term1).
      { inv H1; eapply S_Inc with (b1:=[]); crush. }
      { inv H1; eapply S_First with (os1:=l0 ->> inc incby (remove Nat.eq_dec k ks) :: os1''); crush. }
      { crush. }
    * gotw (C (<< n1; os1 ++ [l ->> op] >> :: b1 ++ << N k (v + incby); l0 ->> inc incby (remove Nat.eq_dec k ks) :: os1'' >> :: b2) os' rs0 term1).
      { inv H1. eapply S_Inc with (b1:=<< n1; os1 ++ [l ->> op] >> :: b1); crush. }
      { inv H1. eapply S_First; crush. }
      { crush. }
  (* S_GetPay *)
  + eauto.
  (* S_Last *)
  + crush.
    {
    destruct b1; eapply ex_intro; eapply ex_intro; intros.
    (* b1 = [] *)
    - split; try split.
      + simpl in *. instantiate (1 := C [<< n1; os1' ++ [l ->> op]>>] os' (l0 ->>> final op0 :: rs0) term1).
        inversion H1.
        one_step; eapply S_Last with (b1 := []); crush.
      + simpl in *. instantiate (1 := C [<< n1; os1' ++ [l ->> op]>>] os' (l0 ->>> final op0 :: rs0) term1).
        inversion H1.
        one_step; eapply S_First; crush.
      + crush.
    (* b1 != [] *)
    - split; try split.
      + instantiate (1 := C (<< n1; os1 ++ [l ->> op] >> :: b1 ++ [<< n0; os1' >>]) os' (l0 ->>> final op0 :: rs0) term1).
        inversion H1.
        one_step; eapply S_Last with (b1 := << n1; os1 ++ [l ->> op] >> :: b1); crush.
      + instantiate (1 := C (<< n1; os1 ++ [l ->> op] >> :: b1 ++ [<< n0; os1' >>]) os' (l0 ->>> final op0 :: rs0) term1).
        inversion H1.
        one_step; eapply S_First; crush.
      + crush.
    }
  (* S_FuseInc *)
  + destruct b1; simpl in *.
    (* b1 = [] *)
    * gotw (C (<< n; os0 ++ l0 ->> inc (incby + incby') ks :: os2 ++ [l ->> op] >> :: b2) os' (l' ->>> 0 :: rs0) term1).
      { inv H1. eapply S_FuseInc with (b1:=[]); crush. }
      { inv H1. assert (os0 ++ l0 ->> inc (incby + incby') ks :: os2 ++ [l ->> op] = (os0 ++ l0 ->> inc (incby + incby') ks :: os2) ++ [l ->> op]) by crush. rewrite H0. eapply S_First; crush. }
      { crush. }
    (* b1 != [] *)
    * gotw (C (<< n1; os1 ++ [l ->> op] >> :: b1 ++ << n; os0 ++ l0 ->> inc (incby + incby') ks :: os2 >> :: b2) os' (l' ->>> 0 :: rs0) term1).
      { inv H1. eapply S_FuseInc with (b1:=<< n1; os1 ++ [l ->> op] >> :: b1); crush. }
      { inv H1. eapply S_First; crush. }
      { crush. }
  (* S_Prop *)
  + eauto.
Qed.
Hint Resolve lc_first.

Lemma lc_inc :
  forall cx cy cz rs term0 l incby ks os1'' b1 b2 k os v,
  well_typed cx ->
  cx = C (b1 ++ << N k v; l ->> inc incby ks :: os1'' >> :: b2) os rs term0 ->
  cy = C (b1 ++ << N k (v + incby); l ->> inc incby (remove Nat.eq_dec k ks) :: os1'' >> :: b2) os rs term0 ->
  In k ks ->
  cx --> cy ->
  cx --> cz ->
  cy -v cz.
Proof using.
  intros cx cy cz rs term0 l incby ks os1'' b1 b2 k os v WT Heqcx Heqcy HIn cxcy cxcz.
  inversion cxcz; ssame.
  (* S_Emit *)
  + eauto.
  (* S_App *)
  + eauto.
  (* S_App1 *)
  + eauto.
  (* S_App2 *)
  + eauto.
  (* S_Empty *)
  + crush. destruct b1; crush.
  (* S_First *)
  + subst; eauto.
  (* S_Add *)
  + gotw (C (<< N k0 v0; [] >> :: b1 ++ << N k (v + incby); l ->> inc incby (remove Nat.eq_dec k ks) :: os1'' >> :: b2) os' (l0 ->>> final (add k0 v0) :: rs0) term1).
    * eapply S_Add; crush.
    * eapply S_Inc with (b1:=<< N k0 v0; [] >> :: b1); crush.
    * crush.
  (* S_Inc *)
  + rename H1 into H0.
    rename b3 into b4.
    rename b0 into b3.
    {
    eapply target_same_or_different with (b1:=b1) (b2:=b2) (b3:=b3) (b4:=b4) (k:=k) (v:=v) (k':=k0) (v':=v0) in H0; eauto.
    - destruct H0; try destruct H0.
      (* Same target *)
      + destruct H0; destruct H1; destruct H1; destruct H2; subst. inversion H3. subst. crush.
      (* First first *)
      + destruct H0; destruct H0; destruct H0.
        apply target_unique with (os:=l ->> inc incby ks :: os1'') (k:=k) (v:=v) (b1:=b1) (b2:=b2) (b3:=x) (b4:=x0 ++ << N k0 v0; l0 ->> inc incby0 ks0 :: os1''0 >> :: x1) (os0:=os0) (rs0:=rs0) (t0:=term1) (b:=b1 ++ << N k v; l ->> inc incby ks :: os1'' >> :: b2) in H0; crush.
        inv H.
        apply target_unique with (os:=l0 ->> inc incby0 ks0 :: os1''0) (k:=k0) (v:=v0) (b1:=x ++ << N k v; l ->> inc incby ks :: os1'' >> :: x0) (b2:=x1) (b3:=b3) (b4:=b4) (os0:=os0) (rs0:=rs0) (t0:=term1) (b:=x ++ << N k v; l ->> inc incby ks :: os1'' >> :: x0 ++ << N k0 v0; l0 ->> inc incby0 ks0 :: os1''0 >> :: x1) in H1; crush.
        got.
        * instantiate (1:=C ((x ++ << N k (v + incby); l ->> inc incby (remove Nat.eq_dec k ks) :: os1'' >> :: x0) ++ << N k0 (v0 + incby0); l0 ->> inc incby0 (remove Nat.eq_dec k0 ks0) :: os1''0 >> :: b4) os0 rs0 term1).
          one_step. eapply S_Inc; crush.
        * instantiate (1:=C (x ++ << N k (v + incby); l ->> inc incby (remove Nat.eq_dec k ks) :: os1'' >> :: x0 ++ << N k0 (v0 + incby0); l0 ->> inc incby0 (remove Nat.eq_dec k0 ks0) :: os1''0 >> :: b4) os0 rs0 term1).
          one_step. eapply S_Inc; crush.
        * crush.
      (* First second *)
      + destruct H0; destruct H0; destruct H0.
        apply target_unique with (os:=l ->> inc incby ks :: os1'') (k:=k) (v:=v) (b1:=b1) (b2:=b2) (b3:=x ++ << N k0 v0; l0 ->> inc incby0 ks0 :: os1''0 >> :: x0) (b4:=x1) (os0:=os0) (rs0:=rs0) (t0:=term1) (b:=b1 ++ << N k v; l ->> inc incby ks :: os1'' >> :: b2) in H0; crush.
        inv H.
        eapply target_unique with (os:=l0 ->> inc incby0 ks0 :: os1''0) (k:=k0) (v:=v0) (b1:=x) (b2:=x0 ++ << N k v; l ->> inc incby ks :: os1'' >> :: x1) (b3:=b3) (b4:=b4) (os0:=os0) (rs0:=rs0) (t0:=term1) in H1; eauto.
        got.
        * instantiate (1:=C (b3 ++ << N k0 (v0 + incby0); l0 ->> inc incby0 (remove Nat.eq_dec k0 ks0) :: os1''0 >> :: x0 ++ << N k (v + incby); l ->> inc incby (remove Nat.eq_dec k ks) :: os1'' >> :: x1) os0 rs0 term1).
          one_step. eapply S_Inc; crush.
        * instantiate (1:=C ((b3 ++ << N k0 (v0 + incby0); l0 ->> inc incby0 (remove Nat.eq_dec k0 ks0) :: os1''0 >> :: x0) ++ << N k (v + incby); l ->> inc incby (remove Nat.eq_dec k ks) :: os1'' >> :: x1) os0 rs0 term1).
          one_step. eapply S_Inc; crush.
        * crush.
    }
  (* S_GetPay *)
  + eauto.
  (* S_Last *)
  +
    {
    destruct b2.
    (* b2 = [] *)
    - apply List.app_inj_tail in H1.
      destruct H1.
      inversion H1.
      crush.
    (* b2 != [] *)
    - remember (s :: b2) as bend.
      assert (exists y ys, bend = ys ++ [y]) by (apply list_snoc with (xs:=bend) (x:=s) (xs':=b2); crush).
      destruct H0; destruct H0.
      inv H0.
      rewrite H2 in *.
      assert (b1 ++ << N k v; l ->> inc incby ks :: os1'' >> :: x0 ++ [x]=(b1 ++ << N k v; l ->> inc incby ks :: os1'' >> :: x0) ++ [x]) by crush.
      rewrite H0 in H1.
      apply List.app_inj_tail in H1.
      destruct H1.
      rewrite H4 in *.
      subst.
      got.
      + instantiate (1:=C ((b1 ++ << N k (v + incby); l ->> inc incby (remove Nat.eq_dec k ks) :: os1'' >> :: x0) ++ [<< n1; os1' >>]) os0 (l0 ->>> final op :: rs0) term1).
        one_step. eapply S_Last; crush.
      + instantiate (1:=C (b1 ++ << N k (v + incby); l ->> inc incby (remove Nat.eq_dec k ks) :: os1'' >> :: x0 ++ [<< n1; os1' >>]) os0 (l0 ->>> final op :: rs0) term1).
        one_step. eapply S_Inc; crush.
      + crush.
    }
  (* S_FuseInc *)
  + destruct n.
    eapply target_same_or_different with (b1:=b1) (b2:=b2) (b3:=b0) (b4:=b3) (k:=k) (v:=v) (k':=n) (v':=n0) in H1; eauto.
    destruct H1; try destruct H0.
    (* Same target *)
    - destruct H1. destruct H2. destruct H3. subst.
      destruct os1.
      * simpl in *.
        inv H4.
        {
        destruct b3.
        - got.
          + instantiate (1:=C (b0 ++ [<< N n (n0 + incby0 + incby'); os2 >>]) os0 (l' ->>> final (inc incby' (remove Nat.eq_dec n ks0)) :: l0 ->>> 0 :: rs0) term1).
            apply ex_intro with 3.
            eapply Step.
            instantiate (1:=C (b0 ++ [<< N n (n0 + incby0); l' ->> inc incby' ks0 :: os2 >>]) os0 (l0 ->>> final (inc incby0 (remove Nat.eq_dec n ks0)) :: rs0) term1).
            eapply S_Last; crush.
            apply List.remove_In in H0. assumption.
            eapply Step.
            instantiate (1:=C (b0 ++ [<< N n ((n0 + incby0) + incby'); l' ->> inc incby' (remove Nat.eq_dec n ks0) :: os2 >>]) os0 (l0 ->>> final (inc incby0 (remove Nat.eq_dec n ks0)) :: rs0) term1).
            eapply S_Inc; crush.
            apply one_star.
            eapply S_Last; crush.
            apply List.remove_In in H0. assumption.
          + instantiate (1:=C (b0 ++ [<< N n (n0 + incby0 + incby'); os2 >>]) os0 (l0 ->>> final (inc (incby0 + incby') (remove Nat.eq_dec n ks0)) :: l' ->>> 0 :: rs0) term1).
            apply ex_intro with 2.
            eapply Step.
            eapply S_Inc; crush.
            apply one_star.
            eapply S_Last; crush.
            rewrite PeanoNat.Nat.add_assoc. crush.
            apply List.remove_In in H0. assumption.
          + crush.
        - destruct s.
          got.
          + instantiate (1:=C (b0 ++ << N n (n0 + incby0 + incby'); os2 >> :: << n1; l ++ [l0 ->> inc (incby0 + incby') (remove Nat.eq_dec n ks0)] >> :: b3) os0 (l' ->>> final (inc incby' (remove Nat.eq_dec n ks0)) :: rs0) term1).
            apply ex_intro with 4.
            eapply Step.
            instantiate (1:=C (b0 ++ << N n (n0 + incby0); l' ->> inc incby' ks0 :: os2 >> :: << n1; l ++ [l0 ->> inc incby0 (remove Nat.eq_dec n ks0)] >> :: b3) os0 rs0 term1).
            eapply S_Prop; crush.
            apply List.remove_In in H0. assumption.
            eapply Step.
            instantiate (1:=C (b0 ++ << N n ((n0 + incby0) + incby'); l' ->> inc incby' (remove Nat.eq_dec n ks0) :: os2 >> :: << n1; l ++ [l0 ->> inc incby0 (remove Nat.eq_dec n ks0)] >> :: b3) os0 rs0 term1).
            eapply S_Inc; crush.
            eapply Step.
            instantiate (1:=C (b0 ++ << N n (n0 + incby0 + incby'); os2 >> :: << n1; (l ++ [l0 ->> inc incby0 (remove Nat.eq_dec n ks0)]) ++ [l' ->> inc incby' (remove Nat.eq_dec n ks0)] >> :: b3) os0 rs0 term1).
            eapply S_Prop; crush.
            apply List.remove_In in H0. assumption.
            apply one_star.
            assert (b0 ++ << N n (n0 + incby0 + incby'); os2 >> :: << n1; (l ++ [l0 ->> inc incby0 (remove Nat.eq_dec n ks0)]) ++ [l' ->> inc incby' (remove Nat.eq_dec n ks0)] >> :: b3 = (b0 ++ [<< N n (n0 + incby0 + incby'); os2 >>]) ++ << n1; l ++ l0 ->> inc incby0 (remove Nat.eq_dec n ks0) :: l' ->> inc incby' (remove Nat.eq_dec n ks0) :: [] >> :: b3) by crush.
            rewrite H0.
            assert (b0 ++ << N n (n0 + incby0 + incby'); os2 >> :: << n1; l ++ [l0 ->> inc (incby0 + incby') (remove Nat.eq_dec n ks0)] >> :: b3 = (b0 ++ [<< N n (n0 + incby0 + incby'); os2 >>]) ++ << n1; l ++ [l0 ->> inc (incby0 + incby') (remove Nat.eq_dec n ks0)] >> :: b3) by crush.
            rewrite H1.
            eapply S_FuseInc; crush.
          + instantiate (1:=C (b0 ++ << N n (n0 + incby0 + incby'); os2 >> :: << n1; l ++ [l0 ->> inc (incby0 + incby') (remove Nat.eq_dec n ks0)] >> :: b3) os0 (l' ->>> 0 :: rs0) term1).
            apply ex_intro with 2.
            eapply Step.
            instantiate (1:=C (b0 ++ << N n (n0 + (incby0 + incby')); l0 ->> inc (incby0 + incby') (remove Nat.eq_dec n ks0) :: os2 >> :: << n1; l >> :: b3) os0 (l' ->>> 0 :: rs0) term1).
            eapply S_Inc; crush.
            apply one_star.
            eapply S_Prop; crush.
            apply List.remove_In in H0. assumption.
            rewrite PeanoNat.Nat.add_assoc. crush.
          + crush.
        }
      * inv H4.
        {
          got.
          * instantiate (1:= C (b0 ++ << N n (n0 + incby); (l ->> inc incby (remove Nat.eq_dec n ks) :: os1) ++ l0 ->> inc (incby0 + incby') ks0 :: os2 >> :: b3) os0 (l' ->>> final (inc incby' ks0) :: rs0) term1).
            one_step. eapply S_FuseInc; crush.
          * instantiate (1:= C (b0 ++ << N n (n0 + incby); l ->> inc incby (remove Nat.eq_dec n ks) :: os1 ++ l0 ->> inc (incby0 + incby') ks0 :: os2 >> :: b3) os0 (l' ->>> final (inc incby' ks0) :: rs0) term1).
            one_step. eapply S_Inc; crush.
          * crush.
        }
    (* First first *)
    - destruct H0. destruct H0. destruct H0.
      eapply target_unique with (b1:=b1) (b2:=b2) (b3:=x) (b4:=x0 ++ << N n n0; os1 ++ l0 ->> inc incby0 ks0 :: l' ->> inc incby' ks0 :: os2 >> :: x1) in H0; crush.
      inv H.
      eapply target_unique with (b1:=x ++ << N k v; l ->> inc incby ks :: os1'' >> :: x0) (b2:=x1) (b3:=b0) (b4:=b3) in H1; eauto; crush.
      got.
      * instantiate (1:=C ((x ++ << N k (v + incby); l ->> inc incby (remove Nat.eq_dec k ks) :: os1'' >> :: x0) ++ << N n n0; os1 ++ l0 ->> inc (incby0 + incby') ks0 :: os2 >> :: b3) os0 (l' ->>> 0 :: rs0) term1).
        one_step. eapply S_FuseInc; crush.
      * instantiate (1:=C (x ++ << N k (v + incby); l ->> inc incby (remove Nat.eq_dec k ks) :: os1'' >> :: x0 ++ << N n n0; os1 ++ l0 ->> inc (incby0 + incby') ks0 :: os2 >> :: b3) os0 (l' ->>> 0 :: rs0) term1).
        one_step. eapply S_Inc; crush.
      * crush.
    (* First second *)
    - destruct H0. destruct H0. destruct H0.
      eapply target_unique with (b1:=b1) (b2:=b2) (b3:=x ++ << N n n0; os1 ++ l0 ->> inc incby0 ks0 :: l' ->> inc incby' ks0 :: os2 >> :: x0) (b4:=x1) in H0; eauto; crush.
      inv H.
      eapply target_unique with (b1:=x) (b2:=x0 ++ << N k v; l ->> inc incby ks :: os1'' >> :: x1) (b3:=b0) (b4:=b3) in H1; eauto; crush.
      got.
      * instantiate (1:=C (b0 ++ << N n n0; os1 ++ l0 ->> inc (incby0 + incby') ks0 :: os2 >> :: x0 ++ << N k (v + incby); l ->> inc incby (remove Nat.eq_dec k ks) :: os1'' >> :: x1) os0 (l' ->>> 0 :: rs0) term1).
        one_step. eapply S_FuseInc; crush.
      * instantiate (1:=C ((b0 ++ << N n n0; os1 ++ l0 ->> inc (incby0 + incby') ks0 :: os2 >> :: x0) ++ << N k (v + incby); l ->> inc incby (remove Nat.eq_dec k ks) :: os1'' >> :: x1) os0 (l' ->>> 0 :: rs0) term1).
        one_step. eapply S_Inc; crush.
      * crush.
  (* S_Prop *)
  + eauto.
Qed.
Hint Resolve lc_inc.

Lemma lc_fuseinc :
  forall cx cy cz n b1 b2 os os1 os2 rs term0 incby incby' ks l l',
  well_typed cx ->
  cx = C (b1 ++ << n; os1 ++ l ->> inc incby ks :: l' ->> inc incby' ks :: os2 >> :: b2) os rs term0 ->
  cy = C (b1 ++ << n; os1 ++ l ->> inc (incby + incby') ks :: os2 >> :: b2) os (l' ->>> final (inc incby' ks) :: rs) term0 ->
  cx --> cy ->
  cx --> cz ->
  cy -v cz.
Proof using.
  intros cx cy cz n b1 b2 os os1 os2 rs term0 incby incby' ks l l' WT Heqcx Heqcy cxcy cxcz.
  remember (b1 ++ << n; os1 ++ l ->> inc incby ks :: l' ->> inc incby' ks :: os2 >> :: b2) as b.
  rename Heqb into H0.
  assert (H : cx = C b os rs term0) by assumption.
  remember cx as c.
  rename Heqc into H1.
  assert (H2 : C (b1 ++ << n; os1 ++ l ->> inc (incby + incby') ks :: os2 >> :: b2) os (l' ->>> final (inc incby' ks) :: rs) term0 = cy) by auto.
  inversion cxcz; ssame.
  (* S_Emit *)
  + eauto.
  (* S_App *)
  + eauto.
  (* S_App1 *)
  + eauto.
  (* S_App2 *)
  + eauto.
  (* S_Empty *)
  + destruct b1; crush.
  (* S_First *)
  + eauto.
  (* S_Add *)
  + ssame.
    got.
    * instantiate (1:=C (<< N k v; [] >> :: b1 ++ << n; os1 ++ l ->> inc (incby + incby') ks :: os2 >> :: b2) os' (l0 ->>> final (add k v) :: l' ->>> final (inc incby' ks) :: rs0) term1).
      one_step. eapply S_Add; crush.
    * instantiate (1:=C (<< N k v; [] >> :: b1 ++ << n; os1 ++ l ->> inc (incby + incby') ks :: os2 >> :: b2) os' (l' ->>> final (inc incby' ks) :: l0 ->>> final (add k v) :: rs0) term1).
      one_step. apply S_FuseInc with (b:=<< N k v; [] >> :: b1 ++ << n; os1 ++ l ->> inc incby ks :: l' ->> inc incby' ks :: os2 >> :: b2) (b1:=<< N k v; [] >> :: b1); crush.
    * crush.
  (* S_Inc *)
  + eauto.
  (* S_GetPay *)
  + eauto.
  (* S_Last *)
  +
    {
    rename b1 into btmp.
    rename b3 into b1.
    rename b2 into b3.
    rename btmp into b2.
    rename os2 into os3.
    rename os1 into os2.
    destruct b3.
    (* b3 = [] *)
    - apply List.app_inj_tail in H1. destruct H1. inv H1.
      destruct os2.
      (* os2 = [] *)
      + simpl in *.
        inv H6.
        got.
        * instantiate (1:=C (b1 ++ [<< n1; os3 >>]) os0 (l0 ->>> final (inc (incby + incby') ks) :: l' ->>> 0 :: rs0) term1).
          one_step. eapply S_Last; crush.
        * instantiate (1:=C (b1 ++ [<< n1; os3 >>]) os0 (l' ->>> final (inc incby' ks) :: l0 ->>> 0 :: rs0) term1).
          one_step. eapply S_Last; crush.
        * crush.
      (* os2 != [] *)
      + inv H6.
        got.
        * instantiate (1:=C (b1 ++ [<< n1; os2 ++ l ->> inc (incby + incby') ks :: os3 >>]) os0 (l0 ->>> final op :: l' ->>> final (inc incby' ks) :: rs0) term1).
          one_step. eapply S_Last; crush.
        * instantiate (1:=C (b1 ++ [<< n1; os2 ++ l ->> inc (incby + incby') ks :: os3 >>]) os0 (l' ->>> final (inc incby' ks) :: l0 ->>> final op :: rs0) term1).
          one_step. eapply S_FuseInc; crush.
        * crush.
    (* b3 != [] *)
    - remember (s :: b3) as bend.
      assert (exists y ys, bend = ys ++ [y]) by (apply list_snoc with (xs:=bend) (x:=s) (xs':=b3); crush).
      destruct H0; destruct H0.
      inv H0.
      rewrite H4 in *.
      assert (b2 ++ << n; os2 ++ l ->> inc incby ks :: l' ->> inc incby' ks :: os3 >> :: x0 ++ [x] = (b2 ++ << n; os2 ++ l ->> inc incby ks :: l' ->> inc incby' ks :: os3 >> :: x0) ++ [x]) by crush.
      rewrite H0 in H1; clear H0.
      apply List.app_inj_tail in H1.
      destruct H1.
      rewrite -> H1 in *.
      clear H1.
      clear x.
      rewrite <- H0 in *.
      clear H0.
      clear b1.
      got.
      + instantiate (1:=C ((b2 ++ << n; os2 ++ l ->> inc (incby + incby') ks :: os3 >> :: x0) ++ [<< n1; os1' >>]) os0 (l0 ->>> final op :: l' ->>> final (inc incby' ks) :: rs0) term1).
        one_step. eapply S_Last; crush.
      + instantiate (1:=C (b2 ++ << n; os2 ++ l ->> inc (incby + incby') ks :: os3 >> :: x0 ++ [<< n1; os1' >>]) os0 (l' ->>> final (inc incby' ks) :: l0 ->>> final op :: rs0) term1).
        assert (forall y, (b2 ++ << n; os2 ++ l ->> inc incby ks :: l' ->> inc incby' ks :: os3 >> :: x0) ++ y = b2 ++ << n; os2 ++ l ->> inc incby ks :: l' ->> inc incby' ks :: os3 >> :: x0 ++ y) by crush. rewrite H0.
        one_step. eapply S_FuseInc; crush.
      + crush.
    }
  (* S_FuseInc *)
  + destruct n as [k v].
    destruct n0 as [k' v'].
    {
    eapply target_same_or_different with (b1:=b1) (b2:=b2) (b3:=b3) (b4:=b4) (k:=k) (v:=v) (k':=k') (v':=v') in H1; eauto.
    - destruct H1; try destruct H0.
      (* Same target *)
      + destruct H1; destruct H4; destruct H5; subst.
        {
        eapply op_same_or_different with (os1:=os1) (os2:=l' ->> inc incby' ks :: os2) (lop:=l ->> inc incby ks) (os3:=os3) (os4:=l'0 ->> inc incby'0 ks0 :: os4) (lop':=l0 ->> inc incby0 ks0) in H6; eauto.
        - destruct H6; destruct H0; try destruct H1.
          (* Same first lop *)
          + inv H1. inv H4. crush.
          (* First first *)
          + destruct H0; destruct H0; destruct H0.
            destruct x0.
            (* First's second is second's first *)
            * simpl in *.
              apply op_unique with (n:=N k' v') (os1:=os1) (os2:=l' ->> inc incby' ks :: os2) (os3:=x) (os4:=l0 ->> inc incby0 ks0 :: x1) (os0:=os0) (rs0:=rs0) (t0:=term1) (b:=b3 ++ << N k' v'; os1 ++ l ->> inc incby ks :: l' ->> inc incby' ks :: os2 >> :: b4) (b1:=b3) (b2:=b4) (os:=os1 ++ l ->> inc incby ks :: l' ->> inc incby' ks :: os2) in H0; crush.
              inv H4.
              inv H3.
              apply List.app_inv_head in H1.
              inv H1.
              apply op_unique with (n:=N k' v') (os1:=x ++ [l ->> inc incby ks0]) (os2:=x1) (os3:=os3) (os4:=l'0 ->> inc incby'0 ks0 :: os4) (os0:=os0) (rs0:=rs0) (t0:=term1) (b:=b3 ++ << N k' v'; x ++ l ->> inc incby ks0 :: l0 ->> inc incby0 ks0 :: x1 >> :: b4) (b1:=b3) (b2:=b4) (os:=x ++ l ->> inc incby ks0 :: l0 ->> inc incby0 ks0 :: x1) in H3; crush.
              {
              got.
              - instantiate (1:=C (b3 ++ << N k' v'; x ++ l ->> inc (incby + incby0 + incby'0) ks0 :: os4 >> :: b4) os0 (l'0 ->>> final (inc incby'0 ks0) :: l0 ->>> 0 :: rs0) term1).
                one_step. eapply S_FuseInc; crush.
              - instantiate (1:=C (b3 ++ << N k' v'; x ++ l ->> inc (incby + (incby0 + incby'0)) ks0 :: os4 >> :: b4) os0 (l0 ->>> final (inc (incby0 + incby'0) ks0) :: l'0 ->>> 0 :: rs0) term1).
                one_step. eapply S_FuseInc; crush.
              - rewrite PeanoNat.Nat.add_assoc. crush.
              }
            (* No overlap *)
            * simpl in *.
              apply op_unique with (n:=N k' v') (os1:=os1) (os2:=l' ->> inc incby' ks :: os2) (os3:=x) (os4:=l1 :: x0 ++ l0 ->> inc incby0 ks0 :: x1) (os0:=os0) (rs0:=rs0) (t0:=term1) (b:=b3 ++ << N k' v'; os1 ++ l ->> inc incby ks :: l' ->> inc incby' ks :: os2 >> :: b4) (b1:=b3) (b2:=b4) (os:=os1 ++ l ->> inc incby ks :: l' ->> inc incby' ks :: os2) in H0; crush.
              inv H3.
              apply List.app_inv_head in H1.
              inv H1.
              apply op_unique with (n:=N k' v') (os1:=x ++ l ->> inc incby ks :: l' ->> inc incby' ks :: x0) (os2:=x1) (os3:=os3) (os4:=l'0 ->> inc incby'0 ks0 :: os4) (os0:=os0) (rs0:=rs0) (t0:=term1) (b:=b3 ++ << N k' v'; x ++ l ->> inc incby ks :: l' ->> inc incby' ks :: x0 ++ l0 ->> inc incby0 ks0 :: x1 >> :: b4) (b1:=b3) (b2:=b4) (os:=x ++ l ->> inc incby ks :: l' ->> inc incby' ks :: x0 ++ l0 ->> inc incby0 ks0 :: x1) in H3; crush.
              {
              got.
              - instantiate (1:=C (b3 ++ << N k' v'; (x ++ l ->> inc (incby + incby') ks :: x0) ++ l0 ->> inc (incby0 + incby'0) ks0 :: os4 >> :: b4) os0 (l'0 ->>> final (inc incby'0 ks0) :: l' ->>> 0 :: rs0) term1).
                one_step. eapply S_FuseInc; crush.
              - instantiate (1:=C (b3 ++ << N k' v'; x ++ l ->> inc (incby + incby') ks :: x0 ++ l0 ->> inc (incby0 + incby'0) ks0 :: os4 >> :: b4) os0 (l' ->>> final (inc incby' ks) :: l'0 ->>> 0 :: rs0) term1).
                one_step. eapply S_FuseInc; crush.
              - crush.
              }
          (* First second *)
          + destruct H0; destruct H0; destruct H0.
            destruct x0.
            (* First's second is second's first *)
            * simpl in *.
              eapply op_unique with (n:=N k' v') (os1:=os1) (os2:=l' ->> inc incby' ks :: os2) (os3:=x ++ [l0 ->> inc incby0 ks0]) (os4:=x1) (os0:=os0) (rs0:=rs0) (t0:=term1) (b:=b3 ++ << N k' v'; os1 ++ l ->> inc incby ks :: l' ->> inc incby' ks :: os2 >> :: b4) (b1:=b3) (b2:=b4) (os:=os1 ++ l ->> inc incby ks :: l' ->> inc incby' ks :: os2) in H0; crush.
              inv H3.
              apply List.app_inv_head in H1.
              inv H1.
              apply op_unique with (n:=N k' v') (os1:=x) (os2:=l ->> inc incby ks :: l' ->> inc incby' ks :: os2) (os3:=os3) (os4:=l'0 ->> inc incby'0 ks0 :: os4) (os0:=os0) (rs0:=rs0) (t0:=term1) (b:=b3 ++ << N k' v'; x ++ l0 ->> inc incby0 ks0 :: l ->> inc incby ks :: l' ->> inc incby' ks :: os2 >> :: b4) (b1:=b3) (b2:=b4) (os:=x ++ l0 ->> inc incby0 ks0 :: l ->> inc incby ks :: l' ->> inc incby' ks :: os2) in H3; crush.
              inv H1.
              {
              got.
              - instantiate (1:=C (b3 ++ << N k' v'; os3 ++ l0 ->> inc (incby0 + (incby'0 + incby')) ks0 :: os2 >> :: b4) os0 (l'0 ->>> final (inc (incby'0 + incby') ks0) :: l' ->>> 0 :: rs0) term1).
                one_step. eapply S_FuseInc; crush.
              - instantiate (1:=C (b3 ++ << N k' v'; os3 ++ l0 ->> inc (incby0 + incby'0 + incby') ks0 :: os2 >> :: b4) os0 (l' ->>> final (inc incby' ks0) :: l'0 ->>> 0 :: rs0) term1).
                one_step. eapply S_FuseInc; crush.
              - rewrite PeanoNat.Nat.add_assoc. crush.
              }
            (* No overlap *)
            * simpl in *.
              eapply op_unique with (n:=N k' v') (os1:=os1) (os2:=l' ->> inc incby' ks :: os2) (os3:=x ++ l0 ->> inc incby0 ks0 :: l1 :: x0) (os4:=x1) (os0:=os0) (rs0:=rs0) (t0:=term1) (b:=b3 ++ << N k' v'; os1 ++ l ->> inc incby ks :: l' ->> inc incby' ks :: os2 >> :: b4) (b1:=b3) (b2:=b4) (os:=os1 ++ l ->> inc incby ks :: l' ->> inc incby' ks :: os2) in H0; crush.
              inv H3.
              apply List.app_inv_head in H1.
              inv H1.
              apply op_unique with (n:=N k' v') (os1:=x) (os2:=l1 :: x0 ++ l ->> inc incby ks :: l' ->> inc incby' ks :: os2) (os3:=os3) (os4:=l'0 ->> inc incby'0 ks0 :: os4) (os0:=os0) (rs0:=rs0) (t0:=term1) (b:=b3 ++ << N k' v'; x ++ l0 ->> inc incby0 ks0 :: l1 :: x0 ++ l ->> inc incby ks :: l' ->> inc incby' ks :: os2 >> :: b4) (b1:=b3) (b2:=b4) (os:=x ++ l0 ->> inc incby0 ks0 :: l1 :: x0 ++ l ->> inc incby ks :: l' ->> inc incby' ks :: os2) in H3; crush.
              {
              got.
              - instantiate (1:=C (b3 ++ << N k' v'; os3 ++ l0 ->> inc (incby0 + incby'0) ks0 :: x0 ++ l ->> inc (incby + incby') ks :: os2 >> :: b4) os0 (l'0 ->>> final (inc incby'0 ks0) :: l' ->>> 0 :: rs0) term1).
                one_step. eapply S_FuseInc; crush.
              - instantiate (1:=C (b3 ++ << N k' v'; (os3 ++ l0 ->> inc (incby0 + incby'0) ks0 :: x0) ++ l ->> inc (incby + incby') ks :: os2 >> :: b4) os0 (l' ->>> final (inc incby' ks) :: l'0 ->>> 0 :: rs0) term1).
                one_step. eapply S_FuseInc; crush.
              - crush.
              }
        }
      (* First first *)
      + destruct H0; destruct H0; destruct H0.
        apply target_unique with (os:=os1 ++ l ->> inc incby ks :: l' ->> inc incby' ks :: os2) (k:=k) (v:=v) (b1:=b1) (b2:=b2) (b3:=x) (b4:=x0 ++ << N k' v'; os3 ++ l0 ->> inc incby0 ks0 :: l'0 ->> inc incby'0 ks0 :: os4 >> :: x1) (os0:=os0) (rs0:=rs0) (t0:=term1) (b:=b1 ++ << N k v; os1 ++ l ->> inc incby ks :: l' ->> inc incby' ks :: os2 >> :: b2) in H0; crush.
        inv H3.
        apply target_unique with (os:=os3 ++ l0 ->> inc incby0 ks0 :: l'0 ->> inc incby'0 ks0 :: os4) (k:=k') (v:=v') (b1:=x ++ << N k v; os1 ++ l ->> inc incby ks :: l' ->> inc incby' ks :: os2 >> :: x0) (b2:=x1) (b3:=b3) (b4:=b4) (os0:=os0) (rs0:=rs0) (t0:=term1) (b:=x ++ << N k v; os1 ++ l ->> inc incby ks :: l' ->> inc incby' ks :: os2 >> :: x0 ++ << N k' v'; os3 ++ l0 ->> inc incby0 ks0 :: l'0 ->> inc incby'0 ks0 :: os4 >> :: x1) in H1; crush.
        got.
        * instantiate (1:=C ((x ++ << N k v; os1 ++ l ->> inc (incby + incby') ks :: os2 >> :: x0) ++ << N k' v'; os3 ++ l0 ->> inc (incby0 + incby'0) ks0 :: os4 >> :: b4) os0 (l'0 ->>> 0 :: l' ->>> 0 :: rs0) term1).
          one_step. eapply S_FuseInc; crush.
        * instantiate (1:=C (x ++ << N k v; os1 ++ l ->> inc (incby + incby') ks :: os2 >> :: x0 ++ << N k' v'; os3 ++ l0 ->> inc (incby0 + incby'0) ks0 :: os4 >> :: b4) os0 (l' ->>> 0 :: l'0 ->>> 0 :: rs0) term1).
          one_step. eapply S_FuseInc; crush.
        * crush.
      (* First second *)
      + destruct H0; destruct H0; destruct H0.
        apply target_unique with (os:=os1 ++ l ->> inc incby ks :: l' ->> inc incby' ks :: os2) (k:=k) (v:=v) (b1:=b1) (b2:=b2) (b3:=x ++ << N k' v'; os3 ++ l0 ->> inc incby0 ks0 :: l'0 ->> inc incby'0 ks0 :: os4 >> :: x0) (b4:=x1) (os0:=os0) (rs0:=rs0) (t0:=term1) (b:=b1 ++ << N k v; os1 ++ l ->> inc incby ks :: l' ->> inc incby' ks :: os2 >> :: b2) in H0; crush.
        inv H3.
        apply target_unique with (os:=os3 ++ l0 ->> inc incby0 ks0 :: l'0 ->> inc incby'0 ks0 :: os4) (k:=k') (v:=v') (b1:=x) (b2:=x0 ++ << N k v; os1 ++ l ->> inc incby ks :: l' ->> inc incby' ks :: os2 >> :: x1) (b3:=b3) (b4:=b4) (os0:=os0) (rs0:=rs0) (t0:=term1) (b:=x ++ << N k' v'; os3 ++ l0 ->> inc incby0 ks0 :: l'0 ->> inc incby'0 ks0 :: os4 >> :: x0 ++ << N k v; os1 ++ l ->> inc incby ks :: l' ->> inc incby' ks :: os2 >> :: x1) in H1; crush.
        got.
        * instantiate (1:=C (b3 ++ << N k' v'; os3 ++ l0 ->> inc (incby0 + incby'0) ks0 :: os4 >> :: x0 ++ << N k v; os1 ++ l ->> inc (incby + incby') ks :: os2 >> :: x1) os0 (l'0 ->>> 0 :: l' ->>> 0 :: rs0) term1).
          one_step. eapply S_FuseInc; crush.
        * instantiate (1:=C ((b3 ++ << N k' v'; os3 ++ l0 ->> inc (incby0 + incby'0) ks0 :: os4 >> :: x0) ++ << N k v; os1 ++ l ->> inc (incby + incby') ks :: os2 >> :: x1) os0 (l' ->>> 0 :: l'0 ->>> 0 :: rs0) term1).
          one_step. eapply S_FuseInc; crush.
        * crush.
    }
  (* S_Prop *)
  + eauto.
Qed.
Hint Resolve lc_fuseinc.

Lemma lc_last :
  forall cx cy cz b1 n1 os rs term0 os1' l op,
  well_typed cx ->
  cx = C (b1 ++ [<< n1; l ->> op :: os1' >>]) os rs term0 ->
  cy = C (b1 ++ [<< n1; os1' >>]) os (l ->>> final op :: rs) term0 ->
  ~ In (getKey n1) (target op) ->
  cx --> cy ->
  cx --> cz ->
  cy -v cz.
Proof using.
  intros cx cy cz b1 n1 os rs term0 os1' l op WT Heqcx Heqcy H3 cxcy cxcz.
  remember (getKey n1) as k.
  rename Heqk into H2.
  remember (l ->> op :: os1') as os1.
  rename Heqos1 into H1.
  remember (b1 ++ [<<n1; os1>>]) as b.
  rename Heqb into H0.
  rename Heqcx into H.
  remember cx as c.
  rename Heqc into H4.
  rename Heqcy into H5.
  inversion cxcz.
  (* S_Emit *)
  + subst; eauto.
  (* S_App *)
  + eauto.
  (* S_App1 *)
  + eauto.
  (* S_App2 *)
  + eauto.
  (* S_Empty *)
  + crush. destruct b1; crush.
  (* S_First *)
  + subst; eauto.
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
  + subst; eauto.
  (* S_GetPay *)
  + subst; eauto.
  (* S_Last *)
  + ssame. apply List.app_inj_tail in H0. inv H0. inv H1. crush.
  (* S_FuseInc *)
  + subst; eauto.
  (* S_Prop *)
  + subst; eauto.
Qed.
Hint Resolve lc_last.

Lemma lc_empty :
  forall cx cy cz l op os' rs term0,
  well_typed cx ->
  cx = C [] (l ->> op :: os') rs term0 ->
  cy = C [] os' (l ->>> final op :: rs) term0 ->
  not_add op ->
  cx --> cy ->
  cx --> cz ->
  cy -v cz.
Proof using.
  intros cx cy cz l op os' rs term0 WT Heqcx Heqcy Hnotadd cxcy cxcz.
  inversion cxcz; ssame; eauto; crush.
Qed.
Hint Resolve lc_empty.

Lemma lc_add :
  forall cx cy cz b l k v os' rs term0,
  well_typed cx ->
  cx = C b (l ->> add k v :: os') rs term0 ->
  cy = C (<< N k v; [] >> :: b) os' (l ->>> final (add k v) :: rs) term0 ->
  cx --> cy ->
  cx --> cz ->
  cy -v cz.
Proof using.
  intros cx cy cz b l k v os' rs term0 WT Heqcx Heqcy cxcy cxcz.
  inversion cxcz; ssame; eauto; crush.
Qed.
Hint Resolve lc_add.

Lemma local_confluence :
  forall cx cy cz,
  well_typed cx ->
  cx --> cy ->
  cx --> cz ->
  (cy -v cz).
Proof using.
  intros cx cy cz WT cxcy cxcz.
  inversion cxcy; subst; eauto.
Qed.

Axiom noe_indo :
  forall cx cy,
  cx == cy ->
  forall cx' cy' n m,
  cx -->*[n] cx' ->
  cy -->*[m] cy' ->
  (cx' -v cy').
(* TODO don't need this after fix normal form below *)
(* or rather, need it but need some different form where if as input we say that they are in normal form *)
(* then need axiom on getting to normal form *)
Axiom noe_indo_norm :
  forall cx cy,
  cx == cy ->
  forall cx' cy' n m,
  cx -->*[n] cx' ->
  cy -->*[m] cy' ->
  cx' == cy'.

(*****************)
(*****************)
(*****************)

Theorem confluence :
  forall cx cy cz,
  well_typed cx ->
  (exists n, cx -->*[n] cy) ->
  (exists m, cx -->*[m] cz) ->
  (cy -v cz).
Proof using.
  intros cx cy cz WT XY XZ.
  destruct XY as [n XY].
  destruct XZ as [m XZ].
  destruct m; destruct n.
  (* n = 0, m = 0 *)
  - apply star_zero in XY.
    apply star_zero in XZ.
    crush.
  (* n = 0, m > 0 *)
  - inv XY.
    apply star_zero in XZ; subst.
    eapply ex_intro.
    eapply ex_intro.
    split; try split.
    + instantiate (1:=cy).
      crush.
    + instantiate (1:=cy).
      apply ex_intro with (S n).
      apply Step with (y).
      assumption.
      assumption.
    + crush.
  (* n > 0, m = 0 *)
  - inv XZ.
    apply star_zero in XY; subst.
    eapply ex_intro.
    eapply ex_intro.
    split; try split.
    + instantiate (1:=cz).
      apply ex_intro with (S m).
      apply Step with (y).
      assumption.
      assumption.
    + instantiate (1:=cz).
      crush.
    + crush.
  (* n > 0, m > 0 *)
  - inv XY.
    rename y into cy'.
    inv XZ.
    rename y into cz'.
    destruct (local_confluence WT H0 H2).
    destruct H. destruct H. destruct H4. destruct H. destruct H4.
    rename x into cy''.
    rename x0 into cz''.
    assert (Hsimcy' : cy' == cy') by crush.
    destruct (noe_indo Hsimcy' H1 H).
    destruct H6. destruct H6. destruct H7. destruct H6. destruct H7.
    rename x into cw.
    rename x0 into cw'.
    assert (Hsimcz' : cz' == cz') by crush.
    destruct (noe_indo Hsimcz' H4 H3).
    destruct H9. destruct H9. destruct H9. destruct H10. destruct H10.
    rename x into cv.
    rename x0 into cv'.
    (* cw' and cv are normal form, so noe_indo can get cy'' and cz'' to reduce to cw' and cv and multi step but there are no multi steps since they're already at normal form, so the multi step is 0, so no steps are taken and they are equivalent *)
    (* so need version of noe_indo which can go all the way to normal form *)
    assert (cw' == cv) by (apply (noe_indo_norm H5 H7 H9)).
    apply ex_intro with cw.
    apply ex_intro with cv'.
    split; try split.
    + eauto.
    + eauto.
    + apply cequiv_trans with cw'; auto.
      apply cequiv_trans with cv; auto.
Qed.
