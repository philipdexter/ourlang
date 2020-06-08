
Require Import CpdtTactics.
From Coq Require Import Lists.List.
From Coq Require Import Sorting.Permutation.
From Coq Require Import Arith.PeanoNat.
From Coq Require Import Arith.Peano_dec.
From Coq Require Import Classes.Equivalence.
From Coq Require Import Strings.String.
Require Import Maps.
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
| Result : type
| Keyset : type
| Label : type -> type
| Arrow : type -> type -> type.
Hint Constructors type.

Inductive term : Type :=
| t_var : string -> term
| t_app : term -> term -> term
| t_abs : string -> type -> term -> term
| t_emit : labeled_operation -> term
| t_label : label -> term
| t_result : result -> term
| t_ks_nil : term
| t_ks_cons : term -> term -> term
| t_downarrow : term -> term
| t_emit_ot_getpay : label -> term -> term
| t_emit_ot_inc : label -> term -> term -> term.
Hint Constructors term.

Inductive value : term -> Prop :=
| v_abs : forall x T t,
          value (t_abs x T t)
| v_result : forall result,
             value (t_result result)
| v_label : forall label,
             value (t_label label)
| v_keyset_nil : value (t_ks_nil)
| v_keyset_cons : forall k ks,
                  value k ->
                  value ks ->
                  value (t_ks_cons k ks).
Hint Constructors value.
Definition noop : term := t_result 0.

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
  | t_label l =>
      t_label l
  | t_result r =>
      t_result r
  | t_ks_nil => t_ks_nil
  | t_ks_cons k ks =>
      t_ks_cons (#[x:=s] k) (#[x:=s] ks)
  | t_downarrow t =>
      t_downarrow (#[x:=s] t)
  | t_emit_ot_getpay l t =>
      t_emit_ot_getpay l (#[x:=s] t)
  | t_emit_ot_inc l t1 t2 =>
      t_emit_ot_inc l (#[x:=s] t1) (#[x:=s] t2)
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

(* ****** typing *)
Definition context := partial_map type.

Inductive has_type : context -> term -> type -> Prop :=
| T_Var : forall Gamma x T,
    Gamma x = Some T ->
    has_type Gamma (t_var x) T
| T_Abs : forall Gamma x T11 T12 t12,
    has_type (x |-> T11 ; Gamma) t12 T12 ->
    has_type Gamma (t_abs x T11 t12) (Arrow T11 T12)
| T_App : forall T11 T12 Gamma t1 t2,
    has_type Gamma t1 (Arrow T11 T12) ->
    has_type Gamma t2 T11 ->
    has_type Gamma (t_app t1 t2) T12
| T_Result : forall r Gamma,
    has_type Gamma (t_result r) Result
| T_KS_Nil : forall Gamma,
    has_type Gamma t_ks_nil Keyset
| T_KS_Cons : forall k ks Gamma,
    has_type Gamma k Result ->
    has_type Gamma ks Keyset ->
    has_type Gamma (t_ks_cons k ks) Keyset
| T_Downarrow : forall ft t Gamma,
    has_type Gamma t (Label ft) ->
    has_type Gamma (t_downarrow t) ft
| T_Label : forall l Gamma,
    has_type Gamma (t_label l) (Label Result)
| T_Emit : forall l op Gamma,
    has_type Gamma (t_emit (l ->> op)) (Label Result)
| T_Emit_OT_GetPay : forall l t Gamma,
    has_type Gamma t Result ->
    has_type Gamma (t_emit_ot_getpay l t) (Label Result)
| T_Emit_OT_Inc : forall l t1 t2 Gamma,
    has_type Gamma t1 Result ->
    has_type Gamma t2 Keyset ->
    has_type Gamma (t_emit_ot_inc l t1 t2) (Label Result).
Hint Constructors has_type.

(* ****** end typing *)

Fixpoint keyset_to_keyset (t : term) :=
match t with
| t_ks_nil => []
| t_ks_cons (t_result k) ks => k :: keyset_to_keyset ks
| _ => []
end.

Reserved Notation "c1 '-->' c2" (at level 40).

Inductive step : config -> config -> Prop :=
(* frontend *)
| S_Emit : forall c b os rs t_lop l op,
    c = C b os rs t_lop ->
    t_lop = t_emit (l ->> op) ->
    c --> C b (os ++ [l ->> op]) rs (t_label l)
| S_Emit_OT_GetPay : forall c b os rs l k,
    c = C b os rs (t_emit_ot_getpay l (t_result k)) ->
    c --> C b (os ++ [l ->> getpay k]) rs (t_label l)
| S_Emit_OT_Inc : forall c b os rs l incby ks ks',
    c = C b os rs (t_emit_ot_inc l (t_result incby) ks) ->
    value ks ->
    ks' = keyset_to_keyset ks ->
    c --> C b (os ++ [l ->> inc incby ks']) rs (t_label l)
| S_Claim : forall c b os rs l v,
    c = C b os rs (t_downarrow (t_label l)) ->
    In (l ->>> v) rs ->
    c --> C b os rs (t_result v)
| S_Ctx_Downarrow : forall c b os os' rs t t',
    c = C b os rs (t_downarrow t) ->
    C [] [] rs t --> C [] os' rs t' ->
    c --> C b (os ++ os') rs (t_downarrow t')
| S_Ctx_Emit_OT_GetPay : forall c b os os' rs l t t',
    c = C b os rs (t_emit_ot_getpay l t) ->
    C [] [] rs t --> C [] os' rs t' ->
    c --> C b (os ++ os') rs (t_emit_ot_getpay l t')
| S_Ctx_Emit_OT_Inc1 : forall c b os os' rs l t1 t1' t2,
    c = C b os rs (t_emit_ot_inc l t1 t2) ->
    C [] [] rs t1 --> C [] os' rs t1' ->
    c --> C b (os ++ os') rs (t_emit_ot_inc l t1' t2)
| S_Ctx_Emit_OT_Inc2 : forall c b os os' rs l t1 t2 t2',
    c = C b os rs (t_emit_ot_inc l t1 t2) ->
    value t1 ->
    C [] [] rs t2 --> C [] os' rs t2' ->
    c --> C b (os ++ os') rs (t_emit_ot_inc l t1 t2')
| S_App : forall c b os rs x T t12 v2,
    c = C b os rs (t_app (t_abs x T t12) v2) ->
    value v2 ->
    c --> C b os rs (#[x:=v2]t12)
| S_App1 : forall c b os os' rs t1 t1' t2,
    c = C b os rs (t_app t1 t2) ->
    C [] [] rs t1 --> C [] os' rs t1' ->
    c --> C b (os ++ os') rs (t_app t1' t2)
| S_App2 : forall c b os os' rs v1 t2' t2,
    c = C b os rs (t_app v1 t2) ->
    value v1 ->
    C [] [] rs t2 --> C [] os' rs t2' ->
    c --> C b (os ++ os') rs (t_app v1 t2')
| S_KS1 : forall c b os os' rs k ks k',
    c = C b os rs (t_ks_cons k ks) ->
    C [] [] rs k --> C [] os' rs k' ->
    c --> C b (os ++ os') rs (t_ks_cons k' ks)
| S_KS2 : forall c b os os' rs k ks ks',
    c = C b os rs (t_ks_cons k ks) ->
    value k ->
    C [] [] rs ks --> C [] os' rs ks' ->
    c --> C b (os ++ os') rs (t_ks_cons k ks')
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
| S_GetPay : forall c b os rs b1 s1 s1' os1 os1' b2 k v l term,
    c = C b os rs term ->
    b = b1 ++ s1 :: b2 ->
    s1 = <<(N k v); os1>> ->
    os1 = l ->> getpay k :: os1' ->
    s1' = <<(N k v); os1'>> ->
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
| t_label _ => []
| t_result _ => []
| t_ks_nil => []
| t_ks_cons k ks => List.concat [term_keys k; term_keys ks]
| t_downarrow t => term_keys t
| t_emit_ot_getpay _ t => term_keys t
| t_emit_ot_inc _ t1 t2 => List.concat [term_keys t1; term_keys t2]
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

Lemma rstream_labels_dist :
  forall rs1 rs2,
  rstream_labels (rs1 ++ rs2) = rstream_labels rs1 ++ rstream_labels rs2.
Proof using.
 induction rs1; intros; crush.
Qed.
Hint Rewrite rstream_labels_dist.


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
| t_label _ => []
| t_result _ => []
| t_ks_nil => []
| t_ks_cons k ks => List.concat [term_labels k; term_labels ks]
| t_downarrow t => term_labels t
| t_emit_ot_getpay _ t => term_labels t
| t_emit_ot_inc _ t1 t2 => List.concat [term_labels t1; term_labels t2]
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

Definition config_has_type (c : config) (T : type) :=
match c with
| C b os rs t => has_type empty t T
end.

Inductive well_typed : config -> Prop :=
| WT : forall c,
    distinct (config_keys c) ->
    distinct (config_labels c) ->
    (exists T, config_has_type c T) ->
    well_typed c.
Hint Constructors well_typed.

Example wt : well_typed (C [<<(N 1 2); [5 ->> inc 1 []]>>; <<(N 2 3); [4 ->> inc 1 []]>>] [2 ->> inc 1 []; 3 ->> inc 1 []] [1 ->>> 2] noop).
Proof using.
  eapply WT; repeat crush; repeat (eapply distinct_many; crush).
  unfold noop; eauto.
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

Definition get_config_rstream (c : config) :=
match c with
| C _ _ rs _ => rs
end.
Definition get_config_backend (c : config) :=
match c with
| C b _ _ _ => b
end.
Axiom all_labels :
  forall c,
  well_typed c ->
  forall l,
  (exists v, In (l ->>> v) (get_config_rstream c)) \/ (exists op b1 s b2, get_config_backend c = b1 ++ s :: b2 /\ In (l ->> op) (get_ostream s)).

Axiom fresh :
  forall c b os rs l op,
  c = C b os rs (t_emit (l ->> op)) ->
  well_typed c ->
  well_typed (C b (os ++ [l ->> op]) rs (t_label l)).
Axiom fresh' :
  forall c b os os' rs t1 t2 t',
  c = C b os rs (t_app t1 t2) ->
  well_typed c ->
  well_typed (C b (os ++ os') rs t').
Axiom fresh'' :
  forall c b os os' rs t t',
  c = C b os rs (t_downarrow t) ->
  well_typed c ->
  well_typed (C b (os ++ os') rs t').
Axiom fresh''' :
  forall c b os rs l t os' t',
  c = C b os rs (t_emit_ot_getpay l t) ->
  well_typed c ->
  well_typed (C b (os ++ os') rs t').
Axiom fresh'''' :
  forall c b os rs l t1 t2 os' t',
  c = C b os rs (t_emit_ot_inc l t1 t2) ->
  well_typed c ->
  well_typed (C b (os ++ os') rs t').
Axiom fresh''''' :
  forall c b os os' rs t1 t2 t',
  c = C b os rs (t_ks_cons t1 t2) ->
  well_typed c ->
  well_typed (C b (os ++ os') rs t').

Lemma cons_app :
  forall {A: Type} (x : A) xs,
  x :: xs = [x] ++ xs.
Proof using.
  crush.
Qed.

Ltac ssame := subst; match goal with
                     | [ H : C _ _ _ _ = C _ _ _ _ |- _ ] => inversion H
                     end; subst.

Lemma frontend_no_value :
  forall rs os t t' s ty te,
  C [] [] rs t --> C [] os rs t' ->
  ~ (t =  t_abs s ty te).
Proof using.
  intros rs os t t' s ty te H.
  inversion H; ssame.
  - crush.
  - crush.
  - crush.
  - crush.
  - crush.
  - crush.
  - crush.
  - crush.
  - crush.
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
  forall rs rs' os t t',
  C [] [] rs t --> C [] os rs' t' ->
  ~ (value t).
Proof using.
  intros rs rs' os t.
  generalize dependent rs.
  generalize dependent rs'.
  generalize dependent os.
  induction t; intros; intro; try solve [inversion H0].
  - inversion H; ssame; eauto; try solve [destruct b1; crush].
  - inversion H; ssame; eauto; try solve [destruct b1; crush].
  - inversion H; ssame; eauto; try solve [destruct b1; crush].
  - inversion H; ssame; eauto; try solve [destruct b1; crush].
  - inversion H; ssame; eauto; try solve [destruct b1; crush].
    + apply IHt1 in H7. inv H0. eauto.
    + apply IHt2 in H8. inv H0. eauto.
Qed.
Hint Resolve frontend_no_value'.

(* ****** typing *)
Lemma canonical_forms_fun : forall t T1 T2,
  has_type empty t (Arrow T1 T2) ->
  value t ->
  exists x u, t = t_abs x T1 u.
Proof using.
  intros t T1 T2 HT HVal.
  inversion HVal; intros; subst; try inversion HT; subst; auto.
  exists x, t0. auto.
Qed.

Lemma canonical_forms_emit_ot_inc : forall t l t1 t2,
  t = t_emit_ot_inc l t1 t2 ->
  has_type empty t1 Result ->
  has_type empty t2 Keyset ->
  value t1 ->
  value t2 ->
  exists incby ks, (ks = t_ks_nil \/ (exists k' ks', ks = t_ks_cons k' ks' /\ value k' /\ value ks')) /\ t = t_emit_ot_inc l (t_result incby) ks.
Proof using.
  intros t l t1 t2 Hteq HT1 HT2 HV1 HV2.
  inversion HV1; intros; subst; try inversion HT1; subst; auto.
  inversion HV2; intros; subst; try inversion HT2; subst; auto.
  - exists result, t_ks_nil; eauto.
  - exists result, (t_ks_cons k ks); eauto.
    split.
    + right. eauto.
    + eauto.
Qed.

Inductive frontend_reduction : config -> config -> Prop :=
| FR_Emit : forall c b os rs t_lop l op,
    c = C b os rs t_lop ->
    t_lop = t_emit (l ->> op) ->
    frontend_reduction c (C b (os ++ [l ->> op]) rs (t_label l))
| FR_Claim : forall c b os rs l v,
    c = C b os rs (t_downarrow (t_label l)) ->
    In (l ->>> v) rs ->
    frontend_reduction c (C b os rs (t_result v))
| FR_Ctx_Downarrow : forall c b os os' rs t t',
    c = C b os rs (t_downarrow t) ->
    C [] [] rs t --> C [] os' rs t' ->
    frontend_reduction c (C b (os ++ os') rs (t_downarrow t'))
| FR_App : forall c b os rs x T t12 v2,
    c = C b os rs (t_app (t_abs x T t12) v2) ->
    value v2 ->
    frontend_reduction c (C b os rs (#[x:=v2]t12))
| FR_App1 : forall c b os os' rs t1 t1' t2,
    c = C b os rs (t_app t1 t2) ->
    C [] [] rs t1 --> C [] os' rs t1' ->
    frontend_reduction c (C b (os ++ os') rs (t_app t1' t2))
| FR_App2 : forall c b os os' rs v1 t2' t2,
    c = C b os rs (t_app v1 t2) ->
    value v1 ->
    C [] [] rs t2 --> C [] os' rs t2' ->
    frontend_reduction c (C b (os ++ os') rs (t_app v1 t2')).
Hint Constructors frontend_reduction.

Ltac destructor := repeat (match goal with
                           | [H : exists _, _ |- _] => destruct H
                           | [H : _ /\ _ |- _] => destruct H
                           end).

Lemma frontend_reduction_to_step :
  forall c c',
  frontend_reduction c c' ->
  c --> c'.
Proof using.
  intros c c' H.
  inversion H; eauto.
Qed.
Hint Resolve frontend_reduction_to_step.

Lemma step_to_frontend_reduction :
  forall c c',
    ((exists b os rs t_lop l op,
      c = C b os rs t_lop /\
      c' = C b (os ++ [l ->> op]) rs (t_label l) /\
      t_lop = t_emit (l ->> op)) \/
     (exists b os rs l v,
      c = C b os rs (t_downarrow (t_label l)) /\
      c' = C b os rs (t_result v) /\
      In (l ->>> v) rs) \/
     (exists b os rs t os' t',
      c = C b os rs (t_downarrow t) /\
      c' = C b (os ++ os') rs (t_downarrow t') /\
      C [] [] rs t --> C [] os' rs t') \/
     (exists b os rs x T t12 v2,
      c = C b os rs (t_app (t_abs x T t12) v2) /\
      c' = C b os rs (#[x:=v2]t12) /\
      value v2) \/
     (exists b os rs t1 t2 os' t1',
      c = C b os rs (t_app t1 t2) /\
      c' = C b (os ++ os') rs (t_app t1' t2) /\
      C [] [] rs t1 --> C [] os' rs t1') \/
     (exists b os rs v1 t2 os' t2',
      c = C b os rs (t_app v1 t2) /\
      c' = C b (os ++ os') rs (t_app v1 t2') /\
      value v1 /\
      C [] [] rs t2 --> C [] os' rs t2')) ->
  frontend_reduction c c'.
Proof using.
  intros c c' H.
  destruct H; destructor; subst; eauto.
  destruct H; destructor; subst; eauto.
  destruct H; destructor; subst; eauto.
  destruct H; destructor; subst; eauto.
  destruct H; destructor; subst; eauto.
Qed.
Hint Resolve step_to_frontend_reduction.

Lemma frontend_backend_agnostic :
  forall b os rs t os' t',
  frontend_reduction (C b os rs t) (C b (os ++ os') rs t') ->
  forall b' os'',
  frontend_reduction (C b' os'' rs t) (C b' (os'' ++ os') rs t').
Proof using.
  intros b os rs t os' t' FR.
  inversion FR; ssame; intros.
  - apply List.app_inv_head in H0; subst; eauto.
  - assert (os' = []).
    {
    induction os.
    + crush.
    + rewrite <- List.app_nil_r in H0 at 1. apply List.app_inv_head in H0. auto.
    }
    subst.
    apply FR_Claim with l; crush.
  - apply List.app_inv_head in H0; subst; eauto.
  - assert (os' = []).
    {
    induction os.
    + crush.
    + rewrite <- List.app_nil_r in H0 at 1. apply List.app_inv_head in H0. auto.
    }
    subst.
    apply FR_App with (T:=T); crush.
  - apply List.app_inv_head in H0; subst; eauto.
  - apply List.app_inv_head in H0; subst; eauto.
Qed.
Hint Resolve frontend_backend_agnostic.

Lemma frontend_agnostic :
  forall os rs t t',
  C [] [] rs t --> C [] os rs t' ->
  forall b os',
  C b os' rs t --> C b (os' ++ os) rs t'.
Proof using.
  intros os rs t t' H.
  inversion H; subst; intros; try solve [inv H3; simpl in *; eauto]; try solve [inv H2; simpl in *; eauto]; try solve [destruct b1; crush].
  - inv H4; simpl in *; eauto.
  - inv H3; simpl in *; eauto.
    apply S_Claim with (l:=l).
    + crush.
    + assumption.
  - inv H4. eauto.
  - inv H3. apply S_App with (T:=T); crush.
  - inv H4. eauto.
  - inv H4; eauto.
Unshelve.
auto.
auto.
auto.
auto.
auto.
auto.
auto.
auto.
auto.
auto.
auto.
auto.
auto.
auto.
auto.
auto.
Qed.

Inductive dry_backend : backend -> Prop :=
| dry_backend_empty : dry_backend []
| dry_backend_cons : forall s b, dry_backend b -> get_ostream s = [] -> dry_backend (s::b).
Hint Constructors dry_backend.
Inductive dry : config -> Prop :=
| dry_ : forall b rs v, dry_backend b -> value v -> dry (C b [] rs v).
Hint Constructors dry.

Lemma dry_no_in : forall b s n os,
  dry_backend b ->
  In s b ->
  s = <<n; os>> ->
  os = [].
Proof using.
  induction b; intros.
  - crush.
  - crush.
    + inv H. auto.
    + inv H. eauto.
Qed.

Lemma value_dec : forall t, value t \/ ~ value t.
Proof using.
  induction t; try solve [right; intro; inv H1]; try solve [right; intro; inv H]; try solve [left; eauto].
  destruct IHt1; destruct IHt2.
  - eauto.
  - right; intro; inv H1; eauto.
  - right; intro; inv H1; eauto.
  - right; intro; inv H1; eauto.
Qed.

Theorem progress : forall b os rs t T,
  well_typed (C b os rs t) ->
  has_type empty t T ->
  value t \/ exists c', (C b os rs t) --> c'.
Proof with eauto.
  intros b os rs t T WT ET.
  remember (@empty type) as Gamma.
  induction ET; subst Gamma...
  - inversion H.
  - right. destruct IHET1...
    + inversion WT. split; crush; eauto.
    + destruct IHET2...
      * inversion WT. split; crush; eauto.
      * assert (exists x0 t0, t1 = t_abs x0 T11 t0).
        {
          apply canonical_forms_fun in ET1.
          destruct ET1.
          destruct H1.
          exists x.
          exists x0...
          assumption.
        }
        destruct H1.
        destruct H1.
        exists (C b os rs (#[x:=t2]x0))...
        apply S_App with (T11).
        subst.
        reflexivity.
        assumption.
      * destruct H0.
        inversion H0; ssame; eauto.
    + destruct H.
      inversion H; ssame; eauto.
  - destruct IHET1...
    + inversion WT. split; crush; eauto.
    + destruct IHET2...
      * inversion WT. split; crush; eauto.
      * right; destruct H0.
        inversion H0; ssame; eauto.
    + right; destruct H.
      inversion H; ssame; eauto.
  - destruct IHET...
    + inversion WT. split; crush; eauto.
    + right.
      inversion H; subst; try solve [inv ET].
      * apply all_labels with (l:=label) in WT.
        {
        destruct WT.
        - destruct H0.
          eauto.
        - destruct H0. destruct H0. destruct H0. destruct H0. destruct H0.
          unfold get_config_backend in H0.
          destruct x1.
          apply List.in_split in H1.
          destruct H1. destruct H1.
          unfold get_ostream in H1.
          destruct x1.
          + simpl in *.
            rename x into op.
            destruct op; destruct n.
            * {
              destruct (List.in_dec Nat.eq_dec n l0).
              - subst; eapply ex_intro; eapply S_Inc; eauto.
              - subst.
                destruct x2.
                + eapply ex_intro; eapply S_Last; eauto.
                + destruct s; eapply ex_intro; eapply S_Prop; eauto.
                  crush.
              }
            * {
              subst; destruct x2.
              - eapply ex_intro; eapply S_Last; eauto.
              - destruct s; eapply ex_intro; eapply S_Prop; eauto.
                crush.
              }
            * {
              destruct (Nat.eq_dec n n0).
              - subst; eapply ex_intro; eapply S_GetPay; eauto.
              - subst.
                destruct x2.
                + eapply ex_intro; eapply S_Last; eauto. crush.
                + destruct s; eapply ex_intro; eapply S_Prop; eauto.
                  crush.
              }
          + destruct l0.
            destruct o; destruct n; simpl in *.
            * {
              destruct (List.in_dec Nat.eq_dec n l0).
              - subst; eapply ex_intro; eapply S_Inc; eauto.
              - subst.
                destruct x2.
                + eapply ex_intro; eapply S_Last; eauto.
                + destruct s; eapply ex_intro; eapply S_Prop; eauto.
                  crush.
              }
            * {
              subst; destruct x2.
              - eapply ex_intro; eapply S_Last; eauto.
              - destruct s; eapply ex_intro; eapply S_Prop; eauto.
                crush.
              }
            * {
              destruct (Nat.eq_dec n n1).
              - subst; eapply ex_intro; eapply S_GetPay; eauto.
              - subst.
                destruct x2.
                + eapply ex_intro; eapply S_Last; eauto. crush.
                + destruct s; eapply ex_intro; eapply S_Prop; eauto.
                  crush.
              }
        }
    + right.
      destruct H.
      destruct x.
      inversion H; ssame; eauto.
  - destruct IHET...
    + inversion WT. split; crush; eauto.
    + right.
      inversion H; subst; try solve [inv ET].
      * eapply ex_intro. eapply S_Emit_OT_GetPay; eauto.
    + right.
      destruct H.
      destruct x.
      inversion H; ssame; eauto.
  - right. destruct IHET1...
    + inversion WT. split; crush; eauto.
    + destruct IHET2...
      * inversion WT. split; crush; eauto.
      * remember (t_emit_ot_inc l t1 t2) as t.
        apply canonical_forms_emit_ot_inc in Heqt; eauto.
        destruct Heqt. destruct H1.
        destruct H1.
        {
        destruct H1; subst.
        - eapply ex_intro; eapply S_Emit_OT_Inc; eauto.
        - destruct H1; destruct H1. destruct H1; destruct H2; subst; eapply ex_intro; eapply S_Emit_OT_Inc; eauto.
        }
      * destruct H0. inversion H0; ssame; eauto.
    + destruct H.
      inversion H; ssame; eauto.
Qed.

Theorem progress' : forall b os rs t T,
  well_typed (C b os rs t) ->
  has_type empty t T ->
  dry (C b os rs t) \/ exists c', (C b os rs t) --> c'.
Proof using.
  intros b os rs t T WT ET.
  remember ET. clear Heqh. apply progress with (b:=b) (os:=os) (rs:=rs) in h; eauto.
  destruct h.
  - destruct os.
    * {
      induction b.
      - crush.
      - assert (dry (C b [] rs t) \/ (exists c' : config, C b [] rs t --> c')).
        {
          apply IHb.
          inversion WT.
          split; try split; crush.
          - inv H0; eauto; inv H3; eauto.
          - rewrite cons_app in H1.
            rewrite backend_labels_dist in H1.
            rewrite <- List.app_assoc in H1.
            apply distinct_concat in H1.
            crush.
        }
        destruct a as [n os].
        + destruct os.
          * {
            destruct H0.
            - left.
              constructor; eauto.
              constructor; eauto.
              inv H0; eauto.
            - right.
              destruct H0.
              inversion H0; ssame; try solve [match goal with | [H : value _ |- _] => inv H end].
              + eapply ex_intro; eauto.
              + eapply ex_intro; eauto.
              + eapply ex_intro; eapply S_App; eauto.
              + eapply ex_intro; eapply S_App2; eauto.
              + eapply ex_intro; eauto.
              + eapply ex_intro; eauto.
              + eapply ex_intro; eapply S_Inc; eauto; crush.
              + eapply ex_intro; eapply S_GetPay; eauto; crush.
              + eapply ex_intro; eapply S_Last; eauto; crush.
              + eapply ex_intro; eapply S_FuseInc; eauto; crush.
              + eapply ex_intro; eapply S_Prop; eauto; crush.
            }
          * right.
            destruct l as [l op].
            {
            destruct op.
              - destruct b; destruct n.
                + destruct (List.in_dec Nat.eq_dec n l0).
                  * eapply ex_intro; eapply S_Inc with (b1:=[]); eauto; crush.
                  * eapply ex_intro; eapply S_Last with (b1:=[]); eauto; crush.
                + destruct s. destruct (List.in_dec Nat.eq_dec n l0).
                  * eapply ex_intro; eapply S_Inc with (b1:=[]); eauto; crush.
                  * eapply ex_intro; eapply S_Prop with (b1:=[]) (n1:=N n n1) (op:=inc n0 l0); eauto; crush.
              - destruct b; destruct n.
                + eapply ex_intro; eapply S_Last with (b1:=[]); eauto; crush.
                + destruct s. eapply ex_intro; eapply S_Prop with (b1:=[]) (l:=l) (n1:=N n n2) (op:=add n0 n1); eauto; crush.
              - destruct b; destruct n.
                + destruct (Nat.eq_dec n n0).
                  * eapply ex_intro; eapply S_GetPay with (b1:=[]); eauto; crush.
                  * eapply ex_intro; eapply S_Last with (b1:=[]); eauto; crush.
                + destruct s. destruct (Nat.eq_dec n n0).
                  * eapply ex_intro; eapply S_GetPay with (b1:=[]); eauto; crush.
                  * eapply ex_intro; eapply S_Prop with (b1:=[]) (n1:=N n n1) (op:=getpay n0); eauto; crush.
            }
          }
      * destruct l as [l op].
        right.
        {
        destruct op.
        - destruct b.
          + eapply ex_intro; eapply S_Empty; eauto.
          + destruct s; eapply ex_intro; eapply S_First; eauto; crush.
        - eapply ex_intro; eapply S_Add; eauto.
        - destruct b.
          + eapply ex_intro; eapply S_Empty; eauto.
          + destruct s; eapply ex_intro; eapply S_First; eauto; crush.
        }
  - right. assumption.
Qed.

Inductive appears_free_in : string -> term -> Prop :=
| afi_var : forall x,
    appears_free_in x (t_var x)
| afi_app1 : forall x t1 t2,
    appears_free_in x t1 ->
    appears_free_in x (t_app t1 t2)
| afi_app2 : forall x t1 t2,
    appears_free_in x t2 ->
    appears_free_in x (t_app t1 t2)
| afi_abs : forall x y T11 t12,
    y <> x  ->
    appears_free_in x t12 ->
    appears_free_in x (t_abs y T11 t12)
| afi_ks1 : forall x k ks,
    appears_free_in x k ->
    appears_free_in x (t_ks_cons k ks)
| afi_ks2 : forall x k ks,
    appears_free_in x ks ->
    appears_free_in x (t_ks_cons k ks)
| afi_downarrow : forall x t,
    appears_free_in x t ->
    appears_free_in x (t_downarrow t)
| afi_emit_ot_getpay : forall x l t,
    appears_free_in x t ->
    appears_free_in x (t_emit_ot_getpay l t)
| afi_emit_ot_inc1 : forall x l t1 t2,
    appears_free_in x t1 ->
    appears_free_in x (t_emit_ot_inc l t1 t2)
| afi_emit_ot_inc2 : forall x l t1 t2,
    appears_free_in x t2 ->
    appears_free_in x (t_emit_ot_inc l t1 t2)
| afi_emit_ot_add1 : forall x l t1 t2,
    appears_free_in x t1 ->
    appears_free_in x (t_emit_ot_add l t1 t2)
| afi_emit_ot_add2 : forall x l t1 t2,
    appears_free_in x t2 ->
    appears_free_in x (t_emit_ot_add l t1 t2).
Hint Constructors appears_free_in.

Definition closed (t:term) :=
  forall x, ~ appears_free_in x t.

Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   has_type Gamma t T ->
   exists T', Gamma x = Some T'.
Proof using.
  intros x t T Gamma H H0. generalize dependent Gamma.
  generalize dependent T.
  induction H;
         intros; try solve [inversion H0; eauto].
  - (* afi_abs *)
    inversion H1; subst.
    apply IHappears_free_in in H7.
    rewrite update_neq in H7; assumption.
Qed.

Corollary typable_empty__closed : forall t T,
    has_type empty t T ->
    closed t.
Proof using.
  unfold closed. intros. intro.
  eapply free_in_context with (Gamma:=empty) in H0.
  destruct H0.
  inv H0.
  eauto.
Qed.

Lemma context_invariance : forall Gamma Gamma' t T,
     has_type Gamma t T  ->
     (forall x, appears_free_in x t -> Gamma x = Gamma' x) ->
     has_type Gamma' t T.
Proof with eauto.
  intros.
  generalize dependent Gamma'.
  induction H; intros; auto.
  - (* T_Var *)
    apply T_Var. rewrite <- H0...
  - (* T_Abs *)
    apply T_Abs.
    apply IHhas_type. intros x1 Hafi.
    (* the only tricky step... the [Gamma'] we use to
       instantiate is [x|->T11;Gamma] *)
    unfold update. unfold t_update. destruct (eqb_string x x1) eqn: Hx0x1...
    rewrite eqb_string_false_iff in Hx0x1. auto.
  - (* T_App *)
    apply T_App with T11...
Qed.

Lemma substitution_preserves_typing : forall Gamma x U t v T,
  has_type (x |-> U ; Gamma) t T ->
  has_type empty v U   ->
  has_type Gamma (#[x:=v]t) T.
Proof with eauto.
  intros Gamma x U t v T Ht Ht'.
  generalize dependent Gamma. generalize dependent T.
  induction t; intros T Gamma H;
    (* in each case, we'll want to get at the derivation of H *)
    inversion H; subst; simpl...
  - (* var *)
    rename s into y. destruct (eqb_stringP x y) as [Hxy|Hxy].
    + (* x=y *)
      subst.
      rewrite update_eq in H2.
      inversion H2; subst.
      eapply context_invariance. eassumption.
      apply typable_empty__closed in Ht'. unfold closed in Ht'.
      intros.  apply (Ht' x) in H0. inversion H0.
    + (* x<>y *)
      apply T_Var. rewrite update_neq in H2...
  - (* abs *)
    rename s into y. rename t into T. apply T_Abs.
    destruct (eqb_stringP x y) as [Hxy | Hxy].
    + (* x=y *)
      subst. rewrite update_shadow in H5. apply H5.
    + (* x<>y *)
      apply IHt. eapply context_invariance...
      intros z Hafi. unfold update, t_update.
      destruct (eqb_stringP y z) as [Hyz | Hyz]; subst; trivial.
      rewrite <- eqb_string_false_iff in Hxy.
      rewrite Hxy...
Qed.

Theorem preservation : forall c c' T,
  config_has_type c T  ->
  c --> c'  ->
  config_has_type c' T.
Proof with eauto.
  unfold config_has_type. intros t t'.
  remember (@empty type) as Gamma.
  intros T HT. generalize dependent t'.
  remember t as c.
  destruct c as [b os rs term].
  subst t.
  induction HT;
       intros t' HE; subst Gamma; subst;
       try solve [inversion HE; subst; ssame; crush];
       try solve [inversion H].
  - inversion HE; subst; ssame; crush; try solve [eauto].
    + apply substitution_preserves_typing with T11; eauto.
      inversion HT1; crush.
    + eapply T_App.
      assert (C b0 os0 rs0 t0 --> C b0 (os0 ++ os') rs0 t1') by (eapply frontend_agnostic in H0; eauto).
      apply H1 in H3.
      eauto.
      eauto.
    + assert (C b0 os0 rs0 t0 --> C b0 (os0 ++ os') rs0 t2') by (eapply frontend_agnostic in H1; eauto).
      eapply T_App.
      apply H3 in H4.
      eauto.
      apply H3 in H4.
      eauto.
  - inversion HE; subst; ssame; crush.
    + assert (C b0 os0 rs0 k0 --> C b0 (os0 ++ os') rs0 k') by (eapply frontend_agnostic in H0; eauto).
      apply H1 in H3. eauto.
    + assert (C b0 os0 rs0 ks0 --> C b0 (os0 ++ os') rs0 ks') by (eapply frontend_agnostic in H1; eauto).
      apply H3 in H4. eauto.
  - inversion HE; subst; ssame; crush.
    + inv HT. eauto.
    + assert (C b0 os0 rs0 t0 --> C b0 (os0 ++ os') rs0 t'0) by (eapply frontend_agnostic in H0; eauto).
      apply H1 in H2.
      eauto.
  - inversion HE; subst; ssame; crush.
    assert (C b0 os0 rs0 t0 --> C b0 (os0 ++ os') rs0 t'0) by (eapply frontend_agnostic in H0; eauto).
    apply H1 in H2.
    eauto.
  - inversion HE; subst; ssame; crush.
    + assert (C b0 os0 rs0 t0 --> C b0 (os0 ++ os') rs0 t1') by (eapply frontend_agnostic in H0; eauto).
      apply H1 in H3. eauto.
    + assert (C b0 os0 rs0 t3 --> C b0 (os0 ++ os') rs0 t2') by (eapply frontend_agnostic in H1; eauto).
      apply H3 in H4. eauto.
Qed.

Definition normal_form (c : config) : Prop :=
  ~ exists c', c --> c'.

Lemma dry_normal_form : forall c b os rs t,
    well_typed c ->
    c = C b os rs t ->
    (dry c <-> normal_form c).
Proof using.
  intros c b os rs t WT Heq.
  split; intros.
  - inversion H.
    intro.
    destruct H3.
    inversion H3; inversion H4; try solve [subst; inv H1]; try solve [inv H5]; try solve [subst; match goal with | [H : [] = _ |- _] => inv H end].
    + subst. inv H0; inv H1; exfalso; eapply frontend_no_value'; eauto.
    + subst. inv H0; inv H1; exfalso; eapply frontend_no_value'; eauto.
    + subst. inv H0.
      * destruct b2; crush.
      * {
          destruct b2.
          - inv H5. crush.
          - inv H5.
            apply dry_no_in with (n:=N k v0) (s:=<< N k v0; l ->> inc incby ks :: os1'' >>) (os:=l ->> inc incby ks :: os1'') in H6; crush.
        }
    + subst. inv H0.
      * destruct b2; crush.
      * {
          destruct b2.
          - inv H5; crush.
          - inv H5.
            apply dry_no_in with (n:=N k v0) (s:=<< N k v0; l ->> getpay k :: os1' >>) (os:=l ->> getpay k :: os1') in H6; crush.
        }
    + subst. inv H0.
      * destruct b2; crush.
      * {
          destruct b2.
          - inv H5; crush.
          - inv H5.
            eapply dry_no_in with (n:=n1) in H6; eauto; crush. inv H6.
        }
    + subst. inv H0.
      * destruct b2; crush.
      * {
          destruct b2.
          - inv H5; crush.
            destruct os1; crush.
          - inv H5.
            eapply dry_no_in with (n:=n) in H6; eauto; crush. destruct os1; crush.
        }
    + subst. inv H0.
      * destruct b2; crush.
      * {
          destruct b2.
          - inv H6; crush.
          - inv H6.
            eapply dry_no_in with (n:=n1) in H7; eauto; crush. inv H7.
        }
  - unfold normal_form in H.
    remember WT.
    inversion WT.
    destruct H2.
    unfold config_has_type in H2.
    destruct c; subst.
    inv Heq.
    apply progress with (os:=os) (rs:=rs) (b:=b) in H2; eauto.
    destruct H2.
    + destruct os.
      * {
        induction b.
        - crush.
        - destruct a as [n os].
          + destruct os.
            * constructor.
              assert (dry (C b [] rs t)).
              {
                apply IHb.
                - inversion WT.
                  split; try split; eauto.
                  crush.
                  inversion H3; eauto.
                  subst.
                  inv H6.
                  crush.
                - intro.
                  destruct H3.
                  unfold not in H.
                  inversion H3; ssame; try solve [match goal with | [H : value _ |- _] => inv H end]; try solve [exfalso; apply H; eauto].
                  + exfalso; apply H. eapply ex_intro; eapply S_Inc; eauto; crush.
                  + exfalso; apply H. eapply ex_intro; eapply S_GetPay; eauto; crush.
                  + exfalso; apply H. eapply ex_intro; eapply S_Last; eauto; crush.
                  + exfalso; apply H. eapply ex_intro; eapply S_FuseInc; eauto; crush.
                  + exfalso; apply H. eapply ex_intro; eapply S_Prop; eauto; crush.
                - crush.
                  inv H0; eauto.
                  inv H3; eauto.
                - crush.
              }
              inv H3.
              crush.
              assumption.
            * destruct l as [l op].
              {
              destruct op.
              - exfalso; apply H; destruct n as [k v].
                destruct (List.in_dec Nat.eq_dec k l0).
                + eapply ex_intro; eapply S_Inc with (b1:=[]); eauto; crush.
                + destruct b.
                  * eapply ex_intro; eapply S_Last with (b1:=[]); eauto; crush.
                  * destruct s. eapply ex_intro; apply S_Prop with (b1:=[]) (os1:=os) (n1:=N k v) (b:=(<< N k v; l ->> inc n0 l0 :: os >> :: << n1; l1>> :: b)) (op:=inc n0 l0); eauto; crush.
              - exfalso; apply H. destruct b.
                + eapply ex_intro; eapply S_Last with (b1:=[]); eauto; crush.
                + destruct s. eapply ex_intro; apply S_Prop with (b1:=[]) (os1:=os) (n1:=n) (b:=(<< n; l ->> add n0 n1 :: os >> :: << n2; l0>> :: b)) (op:=add n0 n1); eauto; crush.
              - exfalso; apply H; destruct n as [k v].
                destruct (Nat.eq_dec k n0).
                + eapply ex_intro; eapply S_GetPay with (b1:=[]); eauto; crush.
                + destruct b.
                  * eapply ex_intro; eapply S_Last with (b1:=[]); eauto; crush.
                  * destruct s. eapply ex_intro; apply S_Prop with (b1:=[]) (os1:=os) (n1:=N k v) (b:=(<< N k v; l ->> getpay n0 :: os >> :: << n1; l0>> :: b)) (op:=getpay n0); eauto; crush.
              }
        }
      * exfalso. apply H.
        destruct l as [l op].
        {
        destruct op.
        - destruct b.
          eapply ex_intro; eapply S_Empty; eauto.
          destruct s.
          eapply ex_intro; eapply S_First; eauto.
        - eapply ex_intro; eapply S_Add; eauto.
        - destruct b.
          eapply ex_intro; eapply S_Empty; eauto.
          destruct s.
          eapply ex_intro; eapply S_First; eauto.
        }
    + crush.
Qed.

Definition stuck c : Prop := normal_form c /\ ~ dry c.

(* ****** end typing *)

Ltac apply_preservation :=
  match goal with
  | [H: C _ _ _ _ --> C _ _ _ _ |- _] => eapply preservation in H; eauto
  end.

Lemma well_typed_preservation :
  forall c1 c2,
  well_typed c1 ->
  c1 --> c2 ->
  well_typed c2.
Proof using.
  intros.
  inversion H0; inversion H; eapply WT; crush; try solve apply_preservation.
  (* S_Emit *)
  - apply fresh with (b:=b) (os:=os) (rs:=rs) (l:=l) (op:=op) in H; inv H; crush.
  - apply fresh with (b:=b) (os:=os) (rs:=rs) (l:=l) (op:=op) in H; inv H; crush.
  (* S_Emit_OT_GetPay *)
  - apply fresh''' with (b:=b) (os:=os) (rs:=rs) (l:=l) (t:=t_result k) (os':=[l ->> getpay k]) (t':=t_label l) in H; inv H; crush.
  - apply fresh''' with (b:=b) (os:=os) (rs:=rs) (l:=l) (t:=t_result k) (os':=[l ->> getpay k]) (t':=t_label l) in H; inv H; crush.
  (* S_Emit_OT_Inc *)
  - eapply fresh'''' with (b:=b) (os:=os) (rs:=rs) (l:=l) (t1:=t_result incby) (os':=[l ->> inc incby (keyset_to_keyset ks)]) (t':=t_label l) in H; inv H; crush.
  - eapply fresh'''' with (b:=b) (os:=os) (rs:=rs) (l:=l) (t1:=t_result incby) (os':=[l ->> inc incby (keyset_to_keyset ks)]) (t':=t_label l) in H; inv H; crush.
  (* S_Claim auto handled *)
  (* S_Ctx_Downarrow *)
  - apply fresh'' with (b:=b) (os:=os) (rs:=rs) (os':=os') (t:=t) (t':=t') in H; inv H; crush.
  - apply fresh'' with (b:=b) (os:=os) (rs:=rs) (os':=os') (t:=t) (t':=t') in H; inv H; crush.
  - inv H1. apply_preservation.
  (* S_Ctx_Emit_OT_GetPay *)
  - apply fresh''' with (b:=b) (os:=os) (rs:=rs) (l:=l) (t:=t) (os':=os') (t':=t_emit_ot_getpay l t') in H; inv H; crush.
  - apply fresh''' with (b:=b) (os:=os) (rs:=rs) (l:=l) (t:=t) (os':=os') (t':=t_emit_ot_getpay l t') in H; inv H; crush.
  - inv H1. apply_preservation.
  (* S_Ctx_Emit_OT_Inc1 *)
  - eapply fresh'''' with (b:=b) (os:=os) (rs:=rs) (l:=l) (t1:=t1) (os':=os') (t':=t_label l) in H; inv H; crush.
  - eapply fresh'''' with (b:=b) (os:=os) (rs:=rs) (l:=l) (t1:=t1) (os':=os') (t':=t_label l) in H; inv H; crush.
  - inv H1. apply_preservation.
  (* S_Ctx_Emit_OT_Inc2 *)
  - eapply fresh'''' with (b:=b) (os:=os) (rs:=rs) (l:=l) (t1:=t1) (os':=os') (t':=t_label l) in H; inv H; crush.
  - eapply fresh'''' with (b:=b) (os:=os) (rs:=rs) (l:=l) (t1:=t1) (os':=os') (t':=t_label l) in H; inv H; crush.
  - inv H1. apply_preservation.
  (* S_App auto handled *)
  (* S_App1 *)
  - apply fresh' with (b:=b) (os:=os) (rs:=rs) (os':=os') (t1:=t1) (t2:=t2) (t':=t_app t1' t2) in H; inv H; crush.
  - apply fresh' with (b:=b) (os:=os) (rs:=rs) (os':=os') (t1:=t1) (t2:=t2) (t':=t_app t1' t2) in H; inv H; crush.
  - inv H1. apply_preservation.
  (* S_App2 *)
  - apply fresh' with (b:=b) (os:=os) (rs:=rs) (os':=os') (t1:=v1) (t2:=t2) (t':=t_app v1 t2') in H; inv H; crush.
  - apply fresh' with (b:=b) (os:=os) (rs:=rs) (os':=os') (t1:=v1) (t2:=t2) (t':=t_app v1 t2') in H; inv H; crush.
  - inv H1. apply_preservation.
  (* S_KS1 *)
  - apply fresh''''' with (b:=b) (os:=os) (rs:=rs) (os':=os') (t1:=k) (t2:=ks) (t':=t_ks_cons k' ks) in H; inv H; crush.
  - apply fresh''''' with (b:=b) (os:=os) (rs:=rs) (os':=os') (t1:=k) (t2:=ks) (t':=t_ks_cons k' ks) in H; inv H; crush.
  - inv H1. apply_preservation.
  (* S_KS2 *)
  - apply fresh''''' with (b:=b) (os:=os) (rs:=rs) (os':=os') (t1:=k) (t2:=ks) (t':=t_ks_cons k ks') in H; inv H; crush.
  - apply fresh''''' with (b:=b) (os:=os) (rs:=rs) (os':=os') (t1:=k) (t2:=ks) (t':=t_ks_cons k ks') in H; inv H; crush.
  - inv H1. apply_preservation.
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
      rewrite H2.
      rewrite List.app_assoc in H9.
      apply distinct_rotate_rev with (x:=l) in H9.
      crush.
    + apply distinct_rotate.
      remember (ostream_labels os' ++ rstream_labels rs) as y.
      assert (ostream_labels os1 ++ List.concat (map (fun s : station => ostream_labels (get_ostream s)) b') ++ y =
              (ostream_labels os1 ++ List.concat (map (fun s : station => ostream_labels (get_ostream s)) b')) ++ y) by crush.
      rewrite H2.
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
    rewrite H2. clear H2.
    apply distinct_rotate.
    apply distinct_rotate_rev in H9.
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
    rewrite H2 in H6.
    rewrite backend_labels_dist in H6.
    unfold backend_labels at 2 in H6.
    simpl in H6.
    rewrite ostream_labels_dist in H6.
    simpl in H6.
    assert (<< n; os1 ++ l ->> inc (incby + incby') ks :: os2 >> :: b2 = [<< n; os1 ++ l ->> inc (incby + incby') ks :: os2 >>] ++ b2) by crush.
    rewrite H3.
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
    remember (ostream_labels os ++ rstream_labels rs) as x1.
    unfold backend_labels at 2.
    simpl.
    rewrite List.app_nil_r.
    repeat (rewrite <- List.app_assoc).
    repeat (rewrite <- List.app_assoc in H7).
    apply distinct_app_comm in H7.
    rewrite <- cons_app.
    assert (backend_labels b1 ++ ostream_labels os1 ++ ostream_labels os2 ++ l :: y ++ x1 = (backend_labels b1 ++ ostream_labels os1 ++ ostream_labels os2) ++ l :: y ++ x1) by crush.
    rewrite H3; clear H3.
    apply distinct_rotate.
    apply distinct_rotate in H7.
    apply distinct_app_comm in H7.
    crush.
Qed.

(* ****** typing *)

Corollary soundness : forall c c',
  well_typed c ->
  (exists n, c -->*[n] c') ->
  ~(stuck c').
Proof using.
  intros c c' WT.
  inversion WT.
  destruct H1.
  rename H1 into Hhas_type.
  intros Hmulti.
  unfold stuck.
  destruct Hmulti as [n Hmulti]. subst.
  induction Hmulti.
  - unfold config_has_type in Hhas_type.
    subst.
    destruct x0 as [b os rs t].
    intros [Hnf Hnv].
    eapply progress' with (b:=b) (os:=os) (rs:=rs) in Hhas_type; try assumption.
    destruct Hhas_type; eauto.
  - assert (well_typed y) by (apply well_typed_preservation in H1; crush).
    apply preservation with (T:=x) in H1.
    + apply IHHmulti in H1; eauto.
      inversion H2.
      assumption.
      inversion H2.
      assumption.
    + assumption.
Qed.

Theorem unique_types : forall Gamma t T T',
  has_type Gamma t T ->
  has_type Gamma t T' ->
  T = T'.
Proof using.
  intros Gamma t.
  generalize dependent Gamma.
  induction t; intros Gamma T T' HT HT'.
  - inv HT; inv HT'; crush.
  - inv HT; inv HT'.
    apply IHt1 with (T':=Arrow T0 T') in H2; eauto.
    apply IHt2 with (T':=T0) in H4; eauto.
    subst.
    inv H2.
    reflexivity.
  - inv HT; inv HT'.
    apply IHt with (T':=T0) in H4; eauto.
    crush.
  - inv HT; inv HT'; eauto.
  - inv HT; inv HT'; eauto.
  - inv HT; inv HT'; eauto.
  - inv HT; inv HT'; eauto.
  - inv HT; inv HT'; eauto.
  - inv HT; inv HT'.
    eapply IHt in H1; eauto.
    inv H1; eauto.
  - inv HT; inv HT'; eauto.
  - inv HT; inv HT'; eauto.
Qed.

(* ****** end typing *)

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
Hint Resolve star_trans.

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
  - eauto.
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
    - eauto.
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
    rewrite H5 in H1; clear H5.
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

Lemma unique_lop :
  forall os l op op' n b1 b2 os0 rs0 term0,
  well_typed (C (b1 ++ <<n; os>> :: b2) os0 rs0 term0) ->
  In (l ->> op) os ->
  In (l ->> op') os ->
  op = op'.
Proof using.
  intros os l op op' n b1 b2 os0 rs0 term0 WT Inop Inop'.
  apply List.in_split in Inop.
  destruct Inop.
  destruct H.
  subst.
  apply List.in_app_or in Inop'.
  destruct Inop'.
  - apply List.in_split in H.
    destruct H.
    destruct H.
    subst.
    exfalso.
    inversion WT.
    unfold config_labels in H0.
    simpl in *.
    rewrite backend_labels_dist in H0.
    unfold backend_labels at 2 in H0.
    simpl in H0.
    rewrite ostream_labels_dist in H0.
    simpl in H0.
    repeat (rewrite <- List.app_assoc in H0).
    apply distinct_concat in H0.
    destruct H0.
    apply distinct_rotate_rev in H3.
    rewrite ostream_labels_dist in H3.
    unfold ostream_labels at 2 in H3.
    simpl in H3.
    clear H1 H H0.
    rewrite -> List.app_comm_cons in H3.
    apply distinct_concat in H3.
    destruct H3.
    clear H0.
    apply distinct_rotate in H.
    apply distinct_concat in H.
    destruct H.
    inv H0.
    crush.
  - apply List.in_inv in H.
    destruct H.
    + crush.
    + exfalso.
      apply List.in_split in H.
      destruct H.
      destruct H.
      subst.
      inversion WT.
      clear H1 H WT.
      unfold config_labels in H0.
      simpl in H0.
      rewrite backend_labels_dist in H0.
      apply distinct_concat in H0.
      destruct H0.
      apply distinct_concat in H.
      destruct H.
      unfold backend_labels in H1.
      simpl in H1.
      rewrite ostream_labels_dist in H1.
      clear H0.
      rewrite List.app_comm_cons in H1.
      rewrite ostream_labels_dist in H1.
      apply distinct_concat in H1.
      destruct H1.
      apply distinct_concat in H0.
      destruct H0.
      clear H H0 H1.
      simpl in H2.
      apply distinct_rotate in H3.
      apply distinct_concat in H3.
      destruct H3.
      inv H0.
      crush.
Qed.

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

Lemma unique_key :
  forall k v os v' os' b os0 rs0 term0,
  well_typed (C b os0 rs0 term0) ->
  In <<N k v; os>> b ->
  In <<N k v'; os'>> b ->
  v = v' /\ os = os'.
Proof using.
  intros k v os v' os' b os0 rs0 term0 WT Inb Inb'.
  apply List.in_split in Inb'.
  destruct Inb'.
  destruct H.
  subst.
  inversion WT.
  clear H0 H1 WT.
  apply List.in_app_or in Inb.
  destruct Inb.
  - apply List.in_split in H0.
    destruct H0.
    destruct H0.
    subst.
    unfold config_keys in H.
    simpl in H.
    apply distinct_concat in H.
    destruct H.
    clear H0.
    rewrite backend_keys_dist in H.
    rewrite backend_keys_dist in H.
    simpl in H.
    apply distinct_rotate_rev in H.
    rewrite List.app_comm_cons in H.
    apply distinct_concat in H.
    destruct H.
    clear H0.
    apply distinct_rotate in H.
    apply distinct_concat in H.
    destruct H.
    clear H.
    inv H0.
    crush.
  - apply List.in_inv in H0.
    + destruct H0.
      * crush.
      * exfalso.
        apply List.in_split in H0.
        destruct H0.
        destruct H0.
        subst.
        unfold config_keys in H.
        simpl in H.
        apply distinct_concat in H.
        destruct H.
        clear H0.
        rewrite backend_keys_dist in H.
        apply distinct_concat in H.
        destruct H.
        clear H.
        simpl in H0.
        rewrite backend_keys_dist in H0.
        simpl in H0.
        apply distinct_rotate in H0.
        apply distinct_concat in H0.
        destruct H0.
        inv H0.
        crush.
Qed.

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
Proof using.
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

Lemma list_not_self :
  forall {A : Type} (x: A) xs,
  not (x :: xs = xs).
Proof using.
  induction xs; crush.
Qed.

Lemma list_not_self' :
  forall {A : Type} (x: A) xs,
  not (xs ++ [x] = xs).
Proof using.
  induction xs; crush.
Qed.

Lemma app_reduce_choice :
  forall b os os'' rs t t' t1 t2,
  t = t_app t1 t2 ->
  C b os rs t --> C b os'' rs t' ->
  (exists os' t1', (C [] [] rs t1 --> C [] os' rs t1' /\ C b os rs t --> C b (os ++ os') rs (t_app t1' t2))) \/
  (value t1 /\ (exists os' t2', C [] [] rs t2 --> C [] os' rs t2' /\ C b os rs t --> C b (os ++ os') rs (t_app t1 t2'))) \/
  (value t2 /\ (exists x T t12, t1 = (t_abs x T t12) /\ C b os rs t --> C b os rs (#[x:=t2]t12))).
Proof using.
  intros.
  inversion H0; subst.
  - inversion H4.
  - inversion H3.
  - inversion H5.
  - subst. right. right.
    split; crush.
  - inversion H4.
  - inversion H4.
  - inversion H4.
  - inversion H5.
  - inv H4.
    right.
    right.
    split; eauto.
  - inv H4.
    left.
    apply ex_intro with os'.
    apply ex_intro with t1'.
    crush.
  - inv H5.
    right. left.
    split.
    + assumption.
    + apply ex_intro with os'.
      apply ex_intro with t2'.
      crush.
  - inversion H4.
  - inversion H5.
  - inv H6.
    exfalso.
    eapply list_not_self.
    eauto.
  - inv H5.
    exfalso.
    eapply list_not_self'.
    eauto.
  - inv H5.
    exfalso.
    eapply list_not_self.
    eauto.
  - inv H5.
    exfalso.
    apply List.app_inv_head in H1.
    inv H1.
    rewrite <- H3 in H12.
    apply List.remove_In in H12.
    assumption.
  - inv H5.
    apply List.app_inv_head in H1.
    exfalso.
    inv H1.
    eapply list_not_self.
    eauto.
  - inv H5.
    exfalso.
    eapply list_not_self.
    eauto.
  - inv H4.
    exfalso.
    eapply list_not_self.
    eauto.
  - inv H5.
    apply List.app_inv_head in H1.
    inv H1.
    exfalso.
    eapply list_not_self.
    eauto.
Qed.

Lemma frontend_rstream_extension :
  forall rs os t t' lr,
  C [] [] rs t --> C [] os rs t' ->
  C [] [] (lr :: rs) t --> C [] os (lr :: rs) t'.
Proof using.
  intros rs os t.
  generalize dependent rs.
  generalize dependent os.
  induction t; intros os rs t' lr Hstep.
  - inversion Hstep; ssame; try solve [destruct b1; crush].
  - inversion Hstep; ssame; try solve [destruct b1; crush].
    + eapply S_App; eauto.
    + eapply S_App1; eauto.
    + eapply S_App2; eauto.
  - exfalso; apply frontend_no_value' in Hstep; eauto.
  - inversion Hstep; ssame; try solve [destruct b1; crush].
    + eapply S_Emit; eauto.
  - inversion Hstep; ssame; try solve [destruct b1; crush].
  - inversion Hstep; ssame; try solve [destruct b1; crush].
  - inversion Hstep; ssame; try solve [destruct b1; crush].
  - inversion Hstep; ssame; try solve [destruct b1; crush].
    + eauto; crush.
    + eauto; crush.
  - inversion Hstep; ssame; try solve [destruct b1; crush].
    + eapply S_Claim; eauto. crush.
    + eapply S_Ctx_Downarrow; eauto.
  - inversion Hstep; ssame; try solve [destruct b1; crush]; eauto.
  - inversion Hstep; ssame; try solve [destruct b1; crush]; eauto.
Qed.
Hint Resolve frontend_rstream_extension.

Lemma unique_result :
  forall b os rs t l r r',
  well_typed (C b os rs t) ->
  In (l ->>> r) rs ->
  In (l ->>> r') rs ->
  r = r'.
Proof using.
  intros b os rs t l r r' WT In1 In2.
  inversion WT as [c H H0 TT H1].
  apply List.in_split in In1.
  destruct In1. destruct H2.
  subst.
  apply List.in_app_or in In2.
  destruct In2.
  - apply List.in_split in H1.
    destruct H1.
    destruct H1.
    subst.
    simpl in H0.
    apply distinct_concat in H0.
    destruct H0.
    apply distinct_concat in H1.
    destruct H1.
    rewrite List.app_nil_r in H2.
    rewrite rstream_labels_dist in H2.
    rewrite rstream_labels_dist in H2.
    unfold rstream_labels at 2 in H2.
    simpl in H2.
    apply distinct_rotate_rev in H2.
    rewrite List.app_comm_cons in H2.
    rewrite List.app_comm_cons in H2.
    rewrite <- List.app_assoc in H2.
    simpl in H2.
    apply distinct_rotate in H2.
    apply distinct_concat in H2.
    destruct H2.
    inv H3.
    crush.
  - apply List.in_split in H1.
    destruct H1.
    destruct H1.
    destruct x1; crush.
    apply distinct_concat in H0.
    destruct H0.
    apply distinct_concat in H1.
    destruct H1.
    apply distinct_rotate_rev in H3.
    rewrite List.app_comm_cons in H3.
    rewrite List.app_assoc in H3.
    apply distinct_rotate_rev in H3.
    simpl in H3.
    inversion H3.
    crush.
Qed.

Lemma frontend_deterministic :
  forall t rs os t',
  well_typed (C [] [] rs t) ->
  C [] [] rs t --> C [] os rs t' ->
  forall t'' os',
  C [] [] rs t --> C [] os' rs t'' ->
  t' = t'' /\ os = os'.
Proof using.
  induction t; intros rs os0 t' WT; intros.
  - inv H; try solve [inv H3]; try solve [inv H4]; try solve [inv H5]; try solve [match goal with | [H : ?b ++ _ = [] |- _] => destruct b; inv H end].
  - inversion H; subst; try solve [inv H3]; try solve [inv H4]; try solve [inv H5]; try solve [match goal with | [H : ?b ++ _ = [] |- _] => destruct b; inv H end].
    + inversion H0; subst; try solve [inv H6]; try solve [inv H3]; try solve [inv H5]; try solve [match goal with | [H : ?b ++ _ = [] |- _] => destruct b; inv H end].
      * inv H4; inv H5. eauto.
      * inv H4; inv H5. apply frontend_no_value' in H9. exfalso. eauto.
      * inv H4; inv H6. apply frontend_no_value' in H10. exfalso. eauto.
    + inversion H0; subst; try solve [inv H6]; try solve [inv H3]; try solve [inv H5]; try solve [match goal with | [H : ?b ++ _ = [] |- _] => destruct b; inv H end].
      * inv H4; inv H5. apply frontend_no_value' in H7. exfalso. eauto.
      * inv H4; inv H5. eapply IHt1 in H7; eauto. destruct H7. subst; split; eauto.
        inversion WT.
        split; try split; eauto.
        destruct H3.
        inv H3.
        eauto.
      * inv H4; inv H6. apply frontend_no_value' in H7. exfalso. eauto.
    + inversion H0; subst; try solve [inv H6]; try solve [inv H3]; try solve [inv H4; inv H5]; try solve [inv H5]; try solve [match goal with | [H : ?b ++ _ = [] |- _] => destruct b; inv H end].
      * inv H4; inv H5. apply frontend_no_value' in H8. exfalso. eauto.
      * inv H4; inv H5. apply frontend_no_value' in H10. exfalso. eauto.
      * inv H5; inv H6. eapply IHt2 in H8; eauto. destruct H8. subst; split; eauto.
        inversion WT.
        split; try split; eauto.
        destruct H3.
        inv H3.
        eauto.
  - apply frontend_no_value' in H; exfalso; eauto.
  - inversion H; subst; try solve [inv H3]; try solve [inv H4]; try solve [inv H5]; try solve [match goal with | [H : ?b ++ _ = [] |- _] => destruct b; inv H end].
    inv H4.
    inversion H0; subst; try solve [inv H3]; try solve [inv H4; inv H5]; try solve [inv H5]; try solve [match goal with | [H : ?b ++ _ = [] |- _] => destruct b; inv H end].
    ssame. split; eauto.
  - inversion H; subst; try solve [inv H3]; try solve [inv H4]; try solve [inv H5]; try solve [match goal with | [H : ?b ++ _ = [] |- _] => destruct b; inv H end].
  - inversion H; subst; try solve [inv H3]; try solve [inv H4]; try solve [inv H5]; try solve [match goal with | [H : ?b ++ _ = [] |- _] => destruct b; inv H end].
  - inversion H; subst; try solve [inv H3]; try solve [inv H4]; try solve [inv H5]; try solve [match goal with | [H : ?b ++ _ = [] |- _] => destruct b; inv H end].
  - inversion H; subst; try solve [inv H3]; try solve [inv H4]; try solve [inv H5]; try solve [match goal with | [H : ?b ++ _ = [] |- _] => destruct b; inv H end].
    + inversion H0; subst; try solve [inv H6]; try solve [inv H3]; try solve [inv H5]; try solve [match goal with | [H : ?b ++ _ = [] |- _] => destruct b; inv H end].
      * inv H4; inv H5. apply IHt1 with (t'':=k'0) (os':=os'1) in H7. crush.
        inv WT.
        destruct H3.
        split; try split; eauto; inv H3; eauto.
        assumption.
      * inv H4; inv H6. exfalso; eapply frontend_no_value' in H7; eauto.
    + inversion H0; subst; try solve [inv H4]; try solve [inv H6]; try solve [inv H3]; try solve [inv H5]; try solve [match goal with | [H : ?b ++ _ = [] |- _] => destruct b; inv H end].
      * inv H4; inv H5. exfalso; eapply frontend_no_value' in H10; eauto.
      * inv H5; inv H6. apply IHt2 with (t'':=ks'0) (os':=os'1) in H8. crush.
        inv WT.
        destruct H3.
        split; try split; eauto; inv H3; eauto.
        assumption.
  - inversion H; subst; try solve [inv H3]; try solve [inv H4]; try solve [inv H5]; try solve [match goal with | [H : ?b ++ _ = [] |- _] => destruct b; inv H end].
    + inversion H0; subst; try solve [inv H6]; try solve [inv H3]; try solve [inv H5]; try solve [match goal with | [H : ?b ++ _ = [] |- _] => destruct b; inv H end].
      * inv H4; inv H5.
        eapply unique_result with (r':=v0) in H7; eauto.
      * inv H4; inv H5. apply frontend_no_value' in H9. exfalso. eauto.
    + inversion H0; subst; try solve [inv H6]; try solve [inv H3]; try solve [inv H5]; try solve [match goal with | [H : ?b ++ _ = [] |- _] => destruct b; inv H end].
      * inv H4; inv H5. apply frontend_no_value' in H7; exfalso; eauto.
      * inv H4; inv H5. apply IHt with (os:=os'0) (t':=t'0) in H9; eauto. destruct H9. subst. split; eauto.
        inversion WT; split; try split; eauto.
        destruct H3.
        inv H3.
        eauto.
  - inversion H; subst; try solve [inv H6]; try solve [inv H3]; try solve [inv H4]; try solve [inv H5]; try solve [match goal with | [H : ?b ++ _ = [] |- _] => destruct b; inv H end].
    + inversion H0; subst; try solve [inv H3]; try solve [inv H6]; try solve [inv H5]; try solve [match goal with | [H : ?b ++ _ = [] |- _] => destruct b; inv H end].
      * inv H3; inv H4.
        split; crush.
      * inv H3; inv H5. apply frontend_no_value' in H8; exfalso; eauto.
    + inversion H0; subst; try solve [inv H6]; try solve [inv H3]; try solve [inv H6]; try solve [inv H5]; try solve [match goal with | [H : ?b ++ _ = [] |- _] => destruct b; inv H end].
      * inv H4; inv H3. apply frontend_no_value' in H7; exfalso; eauto.
      * inv H5; inv H4. apply IHt with (os:=os'1) (t':=t') in H7. crush.
        inv WT.
        destruct H3.
        split; try split; eauto; inv H3; eauto.
        assumption.
  - inversion H; subst; try solve [inv H6]; try solve [inv H3]; try solve [inv H4]; try solve [inv H5]; try solve [match goal with | [H : ?b ++ _ = [] |- _] => destruct b; inv H end].
    + inversion H0; subst; try solve [inv H4]; try solve [inv H3]; try solve [inv H6]; try solve [inv H5]; try solve [match goal with | [H : ?b ++ _ = [] |- _] => destruct b; inv H end].
      * inv H5; inv H6. eauto.
      * inv H4; inv H5. exfalso; eapply frontend_no_value'; eauto.
      * inv H5; inv H6. exfalso; eapply frontend_no_value'; eauto.
    + inversion H0; subst; try solve [inv H6]; try solve [inv H3]; try solve [inv H6]; try solve [inv H5]; try solve [match goal with | [H : ?b ++ _ = [] |- _] => destruct b; inv H end].
      * inv H4; inv H6. exfalso; eapply frontend_no_value' in H7; eauto.
      * inv H5; inv H4. apply IHt1 with (os:=os'1) (t':=t1'0) in H7. crush.
        inv WT.
        destruct H3.
        split; try split; eauto; inv H3; eauto.
        assumption.
      * inv H4; inv H6. exfalso; eapply frontend_no_value' in H7; eauto.
    + inversion H0; subst; try solve [inv H4]; try solve [inv H6]; try solve [inv H3]; try solve [inv H6]; try solve [inv H5]; try solve [match goal with | [H : ?b ++ _ = [] |- _] => destruct b; inv H end].
      * inv H5; inv H6. exfalso; eapply frontend_no_value' in H8; eauto.
      * inv H4; inv H5. exfalso; eapply frontend_no_value' in H7; eauto.
      * inv H5; inv H6. apply IHt2 with (os:=os'1) (t':=t2'0) in H8. crush.
        inv WT.
        destruct H3.
        split; try split; eauto; inv H3; eauto.
        assumption.
Qed.
Hint Resolve frontend_deterministic.

Ltac fnv := match goal with
            | [H : C [] [] ?rs ?t --> C [] ?os ?rs ?t' |- _] => apply frontend_no_value' in H; crush
            end.

Ltac trouble_makers := try solve [eapply S_Add; eauto]; try solve [eapply S_FuseInc; eauto].

Ltac match_ks1 :=
  match goal with
  | [H : _ --> C ?b ?os ?rs (t_ks_cons ?t1 ?t2) |- _] =>
    match goal with
    | [H': C [] [] ?rs' ?t --> C [] ?os' ?rs' ?t' |- _] => gotw (C b (os ++ os') rs (t_ks_cons t' t2)); simpl; eauto; trouble_makers
    end
  end.

Lemma lc_ks1 :
  forall cx cy cz b os os0 rs t1 t2 t1',
  well_typed cx ->
  cx = C b os rs (t_ks_cons t1 t2) ->
  cy = C b (os ++ os0) rs (t_ks_cons t1' t2) ->
  cx --> cy ->
  cx --> cz ->
  C [] [] rs t1 --> C [] os0 rs t1' ->
  cy -v cz.
Proof using.
  intros cx cy cz b os os' rs t1 t2 t1'.
  intros WT Heqcx Heqcy cxcy cxcz.
  intros t1t1'.
  inversion cxcz; ssame; try solve match_ks1.
  (* S_KS1 *)
  - apply frontend_deterministic with (t'':=k') (os':=os'0) in t1t1'; eauto. crush.
    inv WT. split; try split; eauto; crush.
    apply distinct_concat in H2.
    destruct H2.
    apply distinct_concat in H4.
    crush.
    inv H3; eauto.
  (* S_Ctx_Emit_OT_GetPay *)
  - apply frontend_no_value' in t1t1'; exfalso; eauto.
Qed.
Hint Resolve lc_ks1.

Ltac match_ks2 :=
  match goal with
  | [H : _ --> C ?b ?os ?rs (t_ks_cons ?t1 ?t2) |- _] =>
    match goal with
    | [H': C [] [] ?rs' ?t --> C [] ?os' ?rs' ?t' |- _] => gotw (C b (os ++ os') rs (t_ks_cons t1 t')); simpl; eauto; trouble_makers
    end
  end.

Lemma lc_ks2 :
  forall cx cy cz b os os0 rs t1 t2 t2',
  well_typed cx ->
  cx = C b os rs (t_ks_cons t1 t2) ->
  cy = C b (os ++ os0) rs (t_ks_cons t1 t2') ->
  cx --> cy ->
  cx --> cz ->
  value t1 ->
  C [] [] rs t2 --> C [] os0 rs t2' ->
  cy -v cz.
Proof using.
  intros cx cy cz b os os' rs t1 t2 t1'.
  intros WT Heqcx Heqcy cxcy cxcz.
  intros HV t2t2'.
  inversion cxcz; ssame; try solve match_ks2.
  (* S_KS1 *)
  - fnv.
  (* S_KS2 *)
  - apply frontend_deterministic with (t'':=ks') (os':=os'0) in t2t2'; eauto. crush.
    inv WT. split; try split; eauto; crush.
    apply distinct_concat in H3.
    destruct H3.
    apply distinct_concat in H5.
    crush.
    inv H4; eauto.
Qed.
Hint Resolve lc_ks2.

Ltac match_emit_ot_inc :=
  match goal with
  | [H : _ --> C ?b ?os ?rs ?t |- _] => match goal with
                                      | [H': _ --> C ?b' (?os' ++ ?os'') ?rs' ?t' |- _] => gotw (C b (os ++ os'') rs t'); simpl; eauto; trouble_makers
                                      end
  end.

Lemma lc_emit_ot_inc :
  forall cx cy cz b os rs l incby ks,
  well_typed cx ->
  cx = C b os rs (t_emit_ot_inc l (t_result incby) ks) ->
  cy = C b (os ++ [l ->> inc incby (keyset_to_keyset ks)]) rs (t_label l) ->
  cx --> cy ->
  cx --> cz ->
  value ks ->
  cy -v cz.
Proof using.
  intros cx cy cz b os rs l incby ks.
  intros WT Heqcx Heqcy cxcy cxcz.
  intros HV.
  inversion cxcz; ssame; try solve match_emit_ot_inc.
  (* S_Emit_OT_Inc *)
  - crush.
  (* S_Ctx_Emit_OT_Inc1 *)
  - apply frontend_no_value' in H0; exfalso; eauto.
  (* S_Ctx_Emit_OT_Inc2 *)
  - apply frontend_no_value' in H1; exfalso; eauto.
Qed.
Hint Resolve lc_emit_ot_inc.

Ltac match_ctx_emit_ot_inc1 :=
  match goal with
  | [H : _ --> C ?b ?os ?rs (t_emit_ot_inc ?l ?t1 ?t2) |- _] =>
    match goal with
    | [H': C [] [] ?rs' ?t --> C [] ?os' ?rs' ?t' |- _] => gotw (C b (os ++ os') rs (t_emit_ot_inc l t' t2)); simpl; eauto; trouble_makers
    end
  end.

Lemma lc_ctx_emit_ot_inc1 :
  forall cx cy cz b os os' rs t1 t2 t1' l,
  well_typed cx ->
  cx = C b os rs (t_emit_ot_inc l t1 t2) ->
  cy = C b (os ++ os') rs (t_emit_ot_inc l t1' t2) ->
  cx --> cy ->
  cx --> cz ->
  C [] [] rs t1 --> C [] os' rs t1' ->
  cy -v cz.
Proof using.
  intros cx cy cz b os os' rs t1 t2 t1' l.
  intros WT Heqcx Heqcy cxcy cxcz.
  intros t1t1'.
  inversion cxcz; ssame; try solve match_ctx_emit_ot_inc1.
  (* S_Emit_OT_Inc *)
  - fnv.
  (* S_Ctx_Emit_OT_Inc1 *)
  - apply frontend_deterministic with (t'':=t1'0) (os':=os'0) in t1t1'; eauto. crush.
    inv WT. split; try split; eauto; crush.
    apply distinct_concat in H2.
    destruct H2.
    apply distinct_concat in H4.
    crush.
    inv H3; eauto.
  (* S_Ctx_Emit_OT_Inc2 *)
  - apply frontend_no_value' in t1t1'; exfalso; eauto.
Qed.
Hint Resolve lc_ctx_emit_ot_inc1.

Ltac match_ctx_emit_ot_inc2 :=
  match goal with
  | [H : _ --> C ?b ?os ?rs (t_emit_ot_inc ?l ?t1 ?t2) |- _] =>
    match goal with
    | [H': C [] [] ?rs' ?t --> C [] ?os' ?rs' ?t' |- _] => gotw (C b (os ++ os') rs (t_emit_ot_inc l t1 t')); simpl; eauto; trouble_makers
    end
  end.
Lemma lc_ctx_emit_ot_inc2 :
  forall cx cy cz b os os' rs t1 t2 t2' l,
  well_typed cx ->
  cx = C b os rs (t_emit_ot_inc l t1 t2) ->
  cy = C b (os ++ os') rs (t_emit_ot_inc l t1 t2') ->
  cx --> cy ->
  cx --> cz ->
  value t1 ->
  C [] [] rs t2 --> C [] os' rs t2' ->
  cy -v cz.
Proof using.
  intros cx cy cz b os os' rs t1 t2 t2' l.
  intros WT Heqcx Heqcy cxcy cxcz.
  intros HV t1t1'.
  inversion cxcz; ssame; try solve match_ctx_emit_ot_inc2.
  (* S_Emit_OT_Inc *)
  - fnv.
  (* S_Ctx_Emit_OT_Inc1 *)
  - apply frontend_no_value' in H0; exfalso; eauto.
  (* S_Ctx_Emit_OT_Inc2 *)
  - apply frontend_deterministic with (t'':=t2'0) (os':=os'0) in t1t1'; eauto. crush.
    inv WT. split; try split; eauto; crush.
    apply distinct_concat in H3.
    destruct H3.
    apply distinct_concat in H5.
    crush.
    inv H4; eauto.
Qed.
Hint Resolve lc_ctx_emit_ot_inc2.

Ltac match_ctx_emit_ot_getpay :=
  match goal with
  | [H : _ --> C ?b ?os ?rs (t_emit_ot_getpay ?l ?t) |- _] =>
    match goal with
    | [H': C [] [] ?rs' ?t --> C [] ?os' ?rs' ?t' |- _] => gotw (C b (os ++ os') rs (t_emit_ot_getpay l t')); simpl; eauto
    end
  end.

Lemma lc_ctx_emit_ot_getpay :
  forall cx cy cz b os os' rs t t' l,
  well_typed cx ->
  cx = C b os rs (t_emit_ot_getpay l t) ->
  cy = C b (os ++ os') rs (t_emit_ot_getpay l t') ->
  cx --> cy ->
  cx --> cz ->
  C [] [] rs t --> C [] os' rs t' ->
  cy -v cz.
Proof using.
  intros cx cy cz b os os' rs t t' l.
  intros WT Heqcx Heqcy cxcy cxcz.
  intros tt'.
  inversion cxcz; ssame; try solve match_ctx_emit_ot_getpay.
  (* S_Emit_OT_GetPay *)
  - fnv.
  (* S_Ctx_Emit_OT_GetPay *)
  - apply frontend_deterministic with (t':=t'0) (os:=os'0) in tt'. crush.
    inv WT. split; try split; eauto; crush.
    apply distinct_concat in H2.
    destruct H2.
    apply distinct_concat in H4.
    crush.
    inv H3; eauto.
    assumption.
  (* S_Add *)
  - match_ctx_emit_ot_getpay.
    eapply S_Add; eauto.
  - match_ctx_emit_ot_getpay.
    eapply S_FuseInc; eauto.
Qed.
Hint Resolve lc_ctx_emit_ot_getpay.

Ltac match_emit_ot_getpay :=
  match goal with
  | [H : _ --> C ?b ?os ?rs ?t |- _] => match goal with
                                      | [H': _ --> C ?b' (?os' ++ ?os'') ?rs' ?t' |- _] => gotw (C b (os ++ os'') rs t'); simpl; eauto
                                      end
  end.

Lemma lc_emit_ot_getpay :
  forall cx cy cz b os rs l k,
  well_typed cx ->
  cx = C b os rs (t_emit_ot_getpay l (t_result k)) ->
  cy = C b (os ++ [l ->> getpay k]) rs (t_label l) ->
  cx --> cy ->
  cx --> cz ->
  cy -v cz.
Proof using.
  intros cx cy cz b os rs l k WT Heqcx Heqcy cxcy cxcz.
  inversion cxcz; ssame; try solve match_emit_ot_getpay.
  (* S_Emit_OT_GetPay *)
  - crush.
  (* S_Ctx_Emit_OT_GetPay *)
  - apply frontend_no_value' in H0; exfalso; eauto.
  (* S_Add *)
  - match_emit_ot_getpay.
    eapply S_Add with (os:=l0 ->> add k0 v :: os' ++ [l ->> getpay k]); eauto.
  (* S_FuseInc *)
  - match_emit_ot_getpay.
    eapply S_FuseInc; eauto.
Qed.
Hint Resolve lc_emit_ot_getpay.

Ltac match_ctx_downarrow :=
  match goal with
  | [H : _ --> C ?b ?os ?rs ?t |- _] => match goal with
                                      | [H': _ --> C [] ?os' ?rs' ?t' |- _] => gotw (C b (os ++ os') rs (t_downarrow t')); simpl; eauto
                                      end
  end.

Lemma lc_ctx_downarrow :
  forall cx cy cz b os os' rs t t',
  well_typed cx ->
  cx = C b os rs (t_downarrow t) ->
  cy = C b (os ++ os') rs (t_downarrow t') ->
  cx --> cy ->
  cx --> cz ->
  C [] [] rs t --> C [] os' rs t' ->
  cy -v cz.
Proof using.
  intros cx cy cz b os os' rs t t'.
  intros WT Heqcx Heqcy cxcy cxcz.
  intros tt'.
  inversion cxcz; ssame; try solve match_ctx_downarrow.
  (* S_Claim *)
  - fnv.
  (* S_Ctx_Downarrow *)
  - assert (t' = t'0 /\ os' = os'0).
    {
    apply frontend_deterministic with (rs:=rs0) (t:=t0).
    - inversion WT as [c H1 H2 TT].
      split.
      + crush.
      + apply distinct_concat in H2.
        destruct H2.
        apply distinct_concat in H4.
        crush.
      + destruct TT as [T TT]; inv TT; eauto.
    - assumption.
    - assumption.
    }
    crush.
  (* S_Empty *)
  - gotw (C [] (os'0 ++ os') (l ->>> final op :: rs0) (t_downarrow t')).
    + eapply S_Empty; eauto. crush.
    + eapply S_Ctx_Downarrow; eauto.
    + crush.
  (* S_Add *)
  - match_ctx_downarrow.
    + eapply S_Add; eauto.
  (* S_FuseInc *)
  - match_ctx_downarrow.
    eapply S_FuseInc; eauto.
Unshelve.
auto.
auto.
auto.
auto.
auto.
auto.
auto.
auto.
auto.
auto.
auto.
auto.
auto.
auto.
Qed.
Hint Resolve lc_ctx_downarrow.

Ltac match_claim :=
  match goal with
  | [H : _ --> C ?b ?os ?rs ?t |- _] => match goal with
                                      | [H': C ?b' ?os' ?rs' ?t'' --> C ?b' ?os' ?rs' ?t' |- _] => gotw (C b os rs t'); simpl; eauto; eapply S_Claim; eauto; crush
                                      end
  end.

Lemma lc_claim :
  forall cx cy cz b os rs l v,
  well_typed cx ->
  cx = C b os rs (t_downarrow (t_label l)) ->
  cy = C b os rs (t_result v) ->
  cx --> cy ->
  cx --> cz ->
  In (l ->>> v) rs ->
  cy -v cz.
Proof using.
  intros cx cy cz b os rs l v.
  intros WT Heqcx Heqcy cxcy cxcz.
  intros RIn.
  inversion cxcz; ssame; try solve [subst; eauto]; try solve match_claim.
  (* S_Claim *)
  - assert (v = v0) by (eapply unique_result; eauto).
    crush.
  (* S_Add *)
  - gotw (C (<< N k v0; [] >> :: b0) os' (l0 ->>> final (add k v0) :: rs0) (t_result v)); eauto.
    eapply S_Claim; eauto; crush.
  (* S_FuseInc *)
  - gotw (C (b1 ++ << n; os1 ++ l0 ->> inc (incby + incby') ks :: os2 >> :: b2) os0 (l' ->>> final (inc incby' ks) :: rs0) (t_result v)); eauto.
    eapply S_Claim; eauto; crush.
Qed.
Hint Resolve lc_claim.

Lemma lc_getpay :
  forall cx cy cz os rs term k v l os1 b1 b2,
  well_typed cx ->
  cx = C (b1 ++ <<N k v; l ->> getpay k :: os1>> :: b2) os rs term ->
  cy = C (b1 ++ <<N k v; os1>> :: b2) os (l ->>> v :: rs) term ->
  cx --> cy ->
  cx --> cz ->
  cy -v cz.
Proof using.
  intros cx cy cz os rs term k v l os1 b1 b2.
  intros WT Heqcx Heqcy cxcy cxcz.
  inversion cxcz; ssame; try solve [subst; eauto].
  (* S_Emit *)
  - gotw (C (b1 ++ << N k v; os1 >> :: b2) (os0 ++ [l0 ->> op]) (l ->>> v :: rs0) (t_label l0)); eauto.
  (* S_App *)
  - gotw (C (b1 ++ << N k v; os1 >> :: b2) os0 (l ->>> v :: rs0) (#[ x := v2] t12)); eauto.
  (* S_App1 *)
  - gotw (C (b1 ++ << N k v; os1 >> :: b2) (os0 ++ os') (l ->>> v :: rs0) (t_app t1' t2)); eauto.
  (* S_App2 *)
  - gotw (C (b1 ++ << N k v; os1 >> :: b2) (os0 ++ os') (l ->>> v :: rs0) (t_app v1 t2')); eauto.
  (* S_Empty *)
  - destruct b1; crush.
  (* S_First *)
  - destruct b1; simpl in *.
    + inv H1.
      gotw (C (<< N k v; os1 ++ [l0 ->> op] >> :: b') os' (l ->>> v :: rs0) term0); eauto.
      * rewrite <- List.app_comm_cons.
        eapply S_GetPay with (b1:=[]); crush.
    + inv H1.
      gotw (C (<< n1; os2 ++ [l0 ->> op] >> :: b1 ++ << N k v; os1 >> :: b2) os' (l ->>> v :: rs0) term0); eauto.
      * rewrite List.app_comm_cons.
        eapply S_GetPay with (b1:=(<< n1; os2 ++ [l0 ->> op] >> :: b1)); crush.
  (* S_Add *)
  - got.
    * instantiate (1:=C (<< N k0 v0; [] >> :: b1 ++ << N k v; os1 >> :: b2) os' (l0 ->>> final (add k0 v0) :: l ->>> v :: rs0) term0); eauto.
    * instantiate (1:=C (<< N k0 v0; [] >> :: b1 ++ << N k v; os1 >> :: b2) os' (l ->>> v :: l0 ->>> final (add k0 v0) :: rs0) term0).
      rewrite List.app_comm_cons; eauto.
    * crush.
  (* S_Inc *)
  - eapply target_same_or_different with (b1:=b1) (b2:=b2) (b3:=b0) (b4:=b3) (k:=k) (v:=v) (k':=k0) (v':=v0) in H1; eauto.
    destruct H1; try destruct H0.
    (* Same target *)
    + crush.
    (* First first *)
    + destruct H0. destruct H0. destruct H0.
      eapply target_unique with (b1:=b1) (b2:=b2) (b3:=x) (b4:=x0 ++ << N k0 v0; l0 ->> inc incby ks :: os1'' >> :: x1) in H0; crush.
      inv H.
      eapply target_unique with (b1:=x ++ << N k v; l ->> getpay k :: os1 >> :: x0) (b2:=x1) (b3:=b0) (b4:=b3) in H1; eauto; crush.
      got.
      * instantiate (1:=C ((x ++ << N k v; os1 >> :: x0) ++ << N k0 (v0 + incby); l0 ->> inc incby (remove Nat.eq_dec k0 ks) :: os1'' >> :: b3) os0 (l ->>> v :: rs0) term0).
        one_step. eapply S_Inc; crush.
      * instantiate (1:=C (x ++ << N k v; os1 >> :: x0 ++ << N k0 (v0 + incby); l0 ->> inc incby (remove Nat.eq_dec k0 ks) :: os1'' >> :: b3) os0 (l ->>> v :: rs0) term0).
        eauto.
      * crush.
    (* First secon *)
    + destruct H0. destruct H0. destruct H0.
      eapply target_unique with (b1:=b1) (b2:=b2) (b3:=x ++ << N k0 v0; l0 ->> inc incby ks :: os1'' >> :: x0) (b4:=x1) in H0; eauto; crush.
      inv H.
      eapply target_unique with (b1:=x) (b2:=x0 ++ << N k v; l ->> getpay k :: os1 >> :: x1) (b3:=b0) (b4:=b3) in H1; eauto; crush.
      got.
      * instantiate (1:=C (b0 ++ << N k0 (v0 + incby); l0 ->> inc incby (remove Nat.eq_dec k0 ks) :: os1'' >> :: x0 ++ << N k v; os1 >> :: x1) os0 (l ->>> v :: rs0) term0).
        eauto.
      * instantiate (1:=C ((b0 ++ << N k0 (v0 + incby); l0 ->> inc incby (remove Nat.eq_dec k0 ks) :: os1'' >> :: x0) ++ << N k v; os1 >> :: x1) os0 (l ->>> v :: rs0) term0).
        one_step. eapply S_GetPay; crush.
      * crush.
  (* S_GetPay *)
  - eapply target_same_or_different with (b1:=b1) (b2:=b2) (b3:=b0) (b4:=b3) (k:=k) (v:=v) (k':=k0) (v':=v0) in H1; eauto.
    destruct H1; try destruct H0.
    (* Same target *)
    + crush. inv H5. crush.
    (* First first *)
    + destruct H0. destruct H0. destruct H0.
      eapply target_unique with (b1:=b1) (b2:=b2) (b3:=x) (b4:=x0 ++ << N k0 v0; l0 ->> getpay k0 :: os1' >> :: x1) in H0; eauto; crush.
      inv H.
      eapply target_unique with (b1:=x ++ << N k v; l ->> getpay k :: os1 >> :: x0) (b2:=x1) (b3:=b0) (b4:=b3) in H1; eauto; crush.
      got.
      * instantiate (1:=C ((x ++ << N k v; os1 >> :: x0) ++ << N k0 v0; os1' >> :: b3) os0 (l0 ->>> v0 :: l ->>> v :: rs0) term0).
        one_step. eapply S_GetPay; crush.
      * instantiate (1:=C (x ++ << N k v; os1 >> :: x0 ++ << N k0 v0; os1' >> :: b3) os0 (l ->>> v :: l0 ->>> v0 :: rs0) term0).
        eauto.
      * crush.
    (* First second *)
    + destruct H0. destruct H0. destruct H0.
      eapply target_unique with (b1:=b1) (b2:=b2) (b3:=x ++ << N k0 v0; l0 ->> getpay k0 :: os1' >> :: x0) (b4:=x1) in H0; eauto; crush.
      inv H.
      eapply target_unique with (b1:=x) (b2:=x0 ++ << N k v; l ->> getpay k :: os1 >> :: x1) (b3:=b0) (b4:=b3) in H1; eauto; crush.
      got.
      * instantiate (1:=C (b0 ++ << N k0 v0; os1' >> :: x0 ++ << N k v; os1 >> :: x1) os0 (l0 ->>> v0 :: l ->>> v :: rs0) term0).
        eauto.
      * instantiate (1:=C ((b0 ++ << N k0 v0; os1' >> :: x0) ++ << N k v; os1 >> :: x1) os0 (l ->>> v :: l0 ->>> v0 :: rs0) term0).
        one_step. eapply S_GetPay; crush.
      * crush.
  (* S_Last *)
  - destruct b2.
    + apply List.app_inj_tail in H1.
      destruct H1.
      inv H1.
      crush.
    + remember (s :: b2) as bend.
      assert (exists y ys, bend = ys ++ [y]) by (apply list_snoc with (xs:=bend) (x:=s) (xs':=b2); crush).
      destruct H0; destruct H0.
      inv H0.
      rewrite H2 in *. clear H2.
      assert (b1 ++ << N k v; l ->> getpay k :: os1 >> :: x0 ++ [x] = (b1 ++ << N k v; l ->> getpay k :: os1 >> :: x0) ++ [x]) by crush.
      rewrite H0 in H1; clear H0.
      apply List.app_inj_tail in H1.
      destruct H1.
      subst.
      got.
      * instantiate (1:=C ((b1 ++ << N k v; os1 >> :: x0) ++ [<< n1; os1' >>]) os0 (l0 ->>> final op :: l ->>> v :: rs0) term0).
        one_step. eapply S_Last; crush.
      * instantiate (1:=C (b1 ++ << N k v; os1 >> :: x0 ++ [<< n1; os1' >>]) os0 (l ->>> v :: l0 ->>> final op :: rs0) term0).
        one_step. eapply S_GetPay; crush.
      * crush.
  (* S_FuseInc *)
  - destruct n as [k' v'].
    eapply target_same_or_different with (b1:=b1) (b2:=b2) (b3:=b0) (b4:=b3) (k:=k) (v:=v) (k':=k') (v':=v') in H1; eauto.
    destruct H1; try destruct H0.
    (* Same target *)
    + destruct H1. destruct H2. destruct H3.
      destruct os2.
      * crush.
      * inv H4.
      {
      got.
      - instantiate (1:=C (b0 ++ << N k' v'; os2 ++ l0 ->> inc (incby + incby') ks :: os3 >> :: b3) os0 (l' ->>> final (inc incby' ks) :: l ->>> v' :: rs0) term0).
        one_step. eapply S_FuseInc; crush.
      - instantiate (1:=C (b0 ++ << N k' v'; os2 ++ l0 ->> inc (incby + incby') ks :: os3 >> :: b3) os0 (l ->>> v' :: l' ->>> final (inc incby' ks) :: rs0) term0).
        one_step. eapply S_GetPay; crush.
      - crush.
      }
    (* First first *)
    + destruct H0. destruct H0. destruct H0.
      eapply target_unique with (b1:=b1) (b2:=b2) (b3:=x) (b4:=x0 ++ << N k' v'; os2 ++ l0 ->> inc incby ks :: l' ->> inc incby' ks :: os3 >> :: x1) in H0; eauto; crush.
      inv H.
      eapply target_unique with (b1:=x ++ << N k v; l ->> getpay k :: os1 >> :: x0) (b2:=x1) (b3:=b0) (b4:=b3) in H1; eauto; crush.
      got.
      * instantiate (1:=C ((x ++ << N k v; os1 >> :: x0) ++ << N k' v'; os2 ++ l0 ->> inc (incby + incby') ks :: os3 >> :: b3) os0 (l' ->>> 0 :: l ->>> v :: rs0) term0).
        one_step. eapply S_FuseInc; crush.
      * instantiate (1:=C (x ++ << N k v; os1 >> :: x0 ++ << N k' v'; os2 ++ l0 ->> inc (incby + incby') ks :: os3 >> :: b3) os0 (l ->>> v :: l' ->>> 0 :: rs0) term0).
        one_step. eapply S_GetPay; crush.
      * crush.
    (* First second *)
    + destruct H0. destruct H0. destruct H0.
      eapply target_unique with (b1:=b1) (b2:=b2) (b3:=x ++ << N k' v'; os2 ++ l0 ->> inc incby ks :: l' ->> inc incby' ks :: os3 >> :: x0) (b4:=x1) in H0; eauto; crush.
      inv H.
      eapply target_unique with (b1:=x) (b2:=x0 ++ << N k v; l ->> getpay k :: os1 >> :: x1) (b3:=b0) (b4:=b3) in H1; eauto; crush.
      got.
      * instantiate (1:=C (b0 ++ << N k' v'; os2 ++ l0 ->> inc (incby + incby') ks :: os3 >> :: x0 ++ << N k v; os1 >> :: x1) os0 (l' ->>> 0 :: l ->>> v :: rs0) term0).
        one_step. eapply S_FuseInc; crush.
      * instantiate (1:=C ((b0 ++ << N k' v'; os2 ++ l0 ->> inc (incby + incby') ks :: os3 >> :: x0) ++ << N k v; os1 >> :: x1) os0 (l ->>> v :: l' ->>> 0 :: rs0) term0).
        one_step. eapply S_GetPay; crush.
      * crush.
  (* S_Inc *)
  - destruct n1 as [k' v'].
    eapply target_same_or_different with (b1:=b1) (b2:=b2) (b3:=b0) (b4:=<< n2; os3 >> :: b3) (k:=k) (v:=v) (k':=k') (v':=v') in H2; eauto.
    destruct H2; try destruct H1.
    (* Same target *)
    + destruct H2. destruct H3. destruct H4. subst.
      inv H5.
      crush.
    (* First first *)
    + destruct H1. destruct H1. destruct H1.
      eapply target_unique with (b1:=b1) (b2:=b2) (b3:=x) (b4:=x0 ++ << N k' v'; l0 ->> op :: os2 >> :: x1) in H1; crush.
      inv H.
      eapply target_unique with (b1:=x ++ << N k v; l ->> getpay k :: os1 >> :: x0) (b2:=x1) (b3:=b0) (b4:=<< n2; os3 >> :: b3) in H2; eauto; crush.
      got.
      * instantiate (1:=C ((x ++ << N k v; os1 >> :: x0) ++ << N k' v'; os2 >> :: << n2; os3 ++ [l0 ->> op] >> :: b3) os0 (l ->>> v :: rs0) term0).
        one_step. eapply S_Prop; crush.
      * instantiate (1:=C (x ++ << N k v; os1 >> :: x0 ++ << N k' v'; os2 >> :: << n2; os3 ++ [l0 ->> op] >> :: b3) os0 (l ->>> v :: rs0) term0).
        one_step. eapply S_GetPay; crush.
      * crush.
    (* First second *)
    + destruct H1. destruct H1. destruct H1.
      eapply target_unique with (b1:=b1) (b2:=b2) (b3:=x ++ << N k' v'; l0 ->> op :: os2 >> :: x0) (b4:=x1) in H1; eauto; crush.
      destruct x0.
      * inv H.
        simpl in *.
        eapply target_unique with (b1:=x) (b2:=<< N k v; l ->> getpay k :: os1 >> :: x1) (b3:=b0) (b4:=<< n2; os3 >> :: b3) in H2; eauto; crush.
        inv H1.
        {
        got.
        - instantiate (1:=C (b0 ++ << N k' v'; os2 >> :: << N k v; os1 ++ [l0 ->> op] >> :: b3) os0 (l ->>> v :: rs0) term0).
          one_step. eapply S_Prop; crush.
        - instantiate (1:=C ((b0 ++ [<< N k' v'; os2 >>]) ++ << N k v; os1 ++ [l0 ->> op] >> :: b3) os0 (l ->>> v :: rs0) term0).
          one_step. eapply S_GetPay; crush.
        - crush.
        }
      * inv H.
        simpl in *.
        eapply target_unique with (b1:=x) (b2:=s :: x0 ++ << N k v; l ->> getpay k :: os1 >> :: x1) (b3:=b0) (b4:=<< n2; os3 >> :: b3) in H2; eauto; crush.
        {
        got.
        - instantiate (1:=C (b0 ++ << N k' v'; os2 >> :: << n2; os3 ++ [l0 ->> op] >> :: x0 ++ << N k v; os1 >> :: x1) os0 (l ->>> v :: rs0) term0).
          one_step. eapply S_Prop; crush.
        - instantiate (1:=C ((b0 ++ << N k' v'; os2 >> :: << n2; os3 ++ [l0 ->> op] >> :: x0) ++ << N k v; os1 >> :: x1) os0 (l ->>> v :: rs0) term0).
          one_step. eapply S_GetPay; crush.
        - crush.
        }
Unshelve.
auto.
auto.
auto.
auto.
auto.
auto.
auto.
auto.
Qed.
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
  inversion cxcz; ssame; try solve [subst; eauto].
  (* S_Emit *)
  - gotw (C (b1 ++ << n1; os1 >> :: << n2; os2 ++ [l ->> op] >> :: b2) (os0 ++ [l0 ->> op0]) rs0 (t_label l0)); eauto.
  (* S_App *)
  - gotw (C (b1 ++ << n1; os1 >> :: << n2; os2 ++ [l ->> op] >> :: b2) os0 rs0 (#[ x := v2] t12)); eauto.
  (* S_App1 *)
  - gotw (C (b1 ++ << n1; os1 >> :: << n2; os2 ++ [l ->> op] >> :: b2) (os0 ++ os') rs0 (t_app t1' t2)); eauto.
  (* S_App2 *)
  - gotw (C (b1 ++ << n1; os1 >> :: << n2; os2 ++ [l ->> op] >> :: b2) (os0 ++ os') rs0 (t_app v1 t2')); eauto.
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
Unshelve.
auto.
auto.
auto.
auto.
auto.
auto.
Qed.
Hint Resolve lc_prop.

Ltac match_app2 :=
  match goal with
  | [H : _ --> C ?b ?os ?rs (t_app ?t1 ?t2) |- _] => match goal with
                                      | [H': C [] [] ?rs' ?t'' --> C [] ?os' ?rs' ?t' |- _] => gotw (C b (os ++ os') rs (t_app t1 t')); simpl; crush
                                      end
  end.

Lemma lc_app2 :
  forall cx cy cz b os os0 rs v1 t2 t2',
  well_typed cx ->
  cx = C b os rs (t_app v1 t2) ->
  cy = C b (os ++ os0) rs (t_app v1 t2') ->
  cx --> cy ->
  cx --> cz ->
  value v1 ->
  C [] [] rs t2 --> C [] os0 rs t2' ->
  cy -v cz.
Proof using.
  intros cx cy cz b os os'' rs v1 t2 t2' WT Heqcx Heqcy cxcy cxcz.
  intros Vv1 t2t2'.
  inversion cxcz; ssame; try solve [subst; eauto].
  (* S_App *)
  + fnv.
  (* S_App1 *)
  + fnv.
  (* S_App2 *)
  + apply frontend_deterministic with (os:=os') (t':=t2'0) in t2t2'; crush.
    inversion WT.
    clear cxcy cxcz H0 H1 Vv1.
    split.
    * crush.
    * crush.
      apply distinct_concat in H3.
      destruct H3.
      apply distinct_concat in H3.
      crush.
    * destruct H4. inv H0. eauto.
  (* S_Empty *)
  + match_app2.
    * eapply S_Empty; eauto.
    * eapply S_App2; eauto.
  (* S_First *)
  + match_app2.
    * eapply S_First; crush.
    * eapply S_App2; crush.
  (* S_Add *)
  + match_app2.
    * eapply S_Add; crush.
    * eapply S_App2; crush.
  (* S_Inc *)
  + match_app2.
    * eapply S_Inc; crush.
    * eapply S_App2; crush.
  (* S_Last *)
  + match_app2.
    * eapply S_Last; crush.
    * eapply S_App2; crush.
  (* S_FuseInc *)
  + match_app2.
    * eapply S_FuseInc; crush.
    * eapply S_App2; crush.
Qed.
Hint Resolve lc_app2.

Ltac match_app :=
  match goal with
  | [H : _ --> C ?b ?os ?rs (t_app ?t1 ?t2) |- _] => match goal with
                                      | [H': C ?b' ?os' ?rs' ?t'' --> C ?b' ?os' ?rs' ?t' |- _] => gotw (C b os rs t'); simpl; eauto
                                      end
  end.

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
  inversion cxcz; ssame; try solve [subst; eauto]; try solve match_app.
  (* S_App1 *)
  + fnv.
  (* S_Add *)
  + match_app.
    * eapply S_Add; eauto.
  (* S_FuseInc *)
  + match_app.
    * eapply S_FuseInc; eauto.
Qed.
Hint Resolve lc_app.

Ltac match_emit :=
  match goal with
  | [H : _ --> C ?b ?os ?rs ?t |- _] => match goal with
                                      | [H': C ?b' ?os' ?rs' ?t'' --> C ?b' (?os' ++ ?os'') ?rs' ?t' |- _] => gotw (C b (os ++ os'') rs t'); simpl; crush
                                      end
  end.

Lemma lc_emit :
  forall cx cy cz b os rs l op,
  well_typed cx ->
  cx = C b os rs (t_emit (l ->> op)) ->
  cy = C b (os ++ [l ->> op]) rs (t_label l) ->
  cx --> cy ->
  cx --> cz ->
  cy -v cz.
Proof using.
  intros cx cy cz b os rs l op WT Heqcx Heqcy cxcy cxcz.
  inversion cxcz; ssame; try solve [subst; eauto].
  (* S_Empty *)
  + match_emit.
    * eapply S_Empty; eauto.
    * eapply S_Emit; eauto.
  (* S_First *)
  + match_emit.
    * eapply S_First; eauto.
    * eapply S_Emit; eauto.
  (* S_Add *)
  + match_emit.
    * eapply S_Add; eauto.
    * eapply S_Emit; eauto.
  (* S_Inc *)
  + match_emit.
    * eapply S_Inc; eauto.
    * eapply S_Emit; eauto.
  (* S_Last *)
  + match_emit.
    * eapply S_Last; eauto.
    * eapply S_Emit; eauto.
  (* S_FuseInc *)
  + match_emit.
    * eapply S_FuseInc; eauto.
    * eapply S_Emit; eauto.
Qed.
Hint Resolve lc_emit.

Ltac match_app1 :=
  match goal with
  | [H : _ --> C ?b ?os ?rs (t_app ?t1 ?t2) |- _] => match goal with
                                      | [H': C [] [] ?rs' ?t'' --> C [] ?os' ?rs' ?t' |- _] => gotw (C b (os ++ os') rs (t_app t' t2)); simpl; crush
                                      end
  end.

Lemma lc_app1 :
  forall cx cy cz b os os'' rs t1 t2 t1',
  well_typed cx ->
  cx = C b os rs (t_app t1 t2) ->
  cy = C b (os ++ os'') rs (t_app t1' t2) ->
  cx --> cy ->
  cx --> cz ->
  C [] [] rs t1 --> C [] os'' rs t1' ->
  cy -v cz.
Proof using.
  intros cx cy cz b os os'' rs t1 t2 t1' WT Heqcx Heqcy cxcy cxcz.
  intros t1t1'.
  inversion cxcz; ssame; try solve [subst; eauto].
  (* S_App1 *)
  + apply frontend_deterministic with (os:=os') (t':=t1'0) in t1t1'; crush.
    inversion WT.
    clear cxcy cxcz H0 H1.
    split.
    * crush.
    * crush.
      apply distinct_concat in H2.
      destruct H2.
      apply distinct_concat in H2.
      crush.
    * destruct H3. inv H0. eauto.
  (* S_Empty *)
  + match_app1.
    * eapply S_Empty; eauto.
    * eapply S_App1; eauto.
  (* S_First *)
  + match_app1.
    * eapply S_First; eauto.
    * eapply S_App1; eauto.
  (* S_Add *)
  + match_app1.
    * eapply S_Add; eauto.
    * eapply S_App1; eauto.
  (* S_Inc *)
  + match_app1.
    * eapply S_Inc; eauto.
    * eapply S_App1; eauto.
  (* S_Last *)
  + match_app1.
    * eapply S_Last; eauto.
    * eapply S_App1; eauto.
  (* S_FuseInc *)
  + match_app1.
    * eapply S_FuseInc; eauto.
    * eapply S_App1; eauto.
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
  inversion cxcz; ssame; try solve [subst; eauto].
  (* S_Add *)
  - crush.
  (* S_Inc *)
  - destruct b1; simpl in *.
    * gotw (C (<< N k (v + incby); l0 ->> inc incby (remove Nat.eq_dec k ks) :: os1'' ++ [l ->> op] >> :: b2)  os' rs0 term1).
      { inv H1; eapply S_Inc with (b1:=[]); crush. }
      { inv H1; eapply S_First with (os1:=l0 ->> inc incby (remove Nat.eq_dec k ks) :: os1''); crush. }
      { crush. }
    * gotw (C (<< n1; os1 ++ [l ->> op] >> :: b1 ++ << N k (v + incby); l0 ->> inc incby (remove Nat.eq_dec k ks) :: os1'' >> :: b2) os' rs0 term1).
      { inv H1. eapply S_Inc with (b1:=<< n1; os1 ++ [l ->> op] >> :: b1); crush. }
      { inv H1. eapply S_First; crush. }
      { crush. }
  (* S_Last *)
  - crush.
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
  - destruct b1; simpl in *.
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
  inversion cxcz; ssame; try solve [subst; eauto].
  (* S_Empty *)
  - destruct b1; crush.
  (* S_Add *)
  - gotw (C (<< N k0 v0; [] >> :: b1 ++ << N k (v + incby); l ->> inc incby (remove Nat.eq_dec k ks) :: os1'' >> :: b2) os' (l0 ->>> final (add k0 v0) :: rs0) term1).
    * eapply S_Add; eauto.
    * eapply S_Inc with (b1:=<< N k0 v0; [] >> :: b1); crush.
    * crush.
  (* S_Inc *)
  - rename H1 into H0.
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
  (* S_Last *)
  -
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
  - destruct n.
    eapply target_same_or_different with (b1:=b1) (b2:=b2) (b3:=b0) (b4:=b3) (k:=k) (v:=v) (k':=n) (v':=n0) in H1; eauto.
    destruct H1; try destruct H0.
    (* Same target *)
    + destruct H1. destruct H2. destruct H3. subst.
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
    + destruct H0. destruct H0. destruct H0.
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
    + destruct H0. destruct H0. destruct H0.
      eapply target_unique with (b1:=b1) (b2:=b2) (b3:=x ++ << N n n0; os1 ++ l0 ->> inc incby0 ks0 :: l' ->> inc incby' ks0 :: os2 >> :: x0) (b4:=x1) in H0; eauto; crush.
      inv H.
      eapply target_unique with (b1:=x) (b2:=x0 ++ << N k v; l ->> inc incby ks :: os1'' >> :: x1) (b3:=b0) (b4:=b3) in H1; eauto; crush.
      got.
      * instantiate (1:=C (b0 ++ << N n n0; os1 ++ l0 ->> inc (incby0 + incby') ks0 :: os2 >> :: x0 ++ << N k (v + incby); l ->> inc incby (remove Nat.eq_dec k ks) :: os1'' >> :: x1) os0 (l' ->>> 0 :: rs0) term1).
        one_step. eapply S_FuseInc; crush.
      * instantiate (1:=C ((b0 ++ << N n n0; os1 ++ l0 ->> inc (incby0 + incby') ks0 :: os2 >> :: x0) ++ << N k (v + incby); l ->> inc incby (remove Nat.eq_dec k ks) :: os1'' >> :: x1) os0 (l' ->>> 0 :: rs0) term1).
        one_step. eapply S_Inc; crush.
      * crush.
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
  inversion cxcz; ssame; try solve [subst; eauto].
  (* S_Empty *)
  - destruct b1; crush.
  (* S_Add *)
  - ssame.
    got.
    * instantiate (1:=C (<< N k v; [] >> :: b1 ++ << n; os1 ++ l ->> inc (incby + incby') ks :: os2 >> :: b2) os' (l0 ->>> final (add k v) :: l' ->>> final (inc incby' ks) :: rs0) term1).
      one_step. eapply S_Add; crush.
    * instantiate (1:=C (<< N k v; [] >> :: b1 ++ << n; os1 ++ l ->> inc (incby + incby') ks :: os2 >> :: b2) os' (l' ->>> final (inc incby' ks) :: l0 ->>> final (add k v) :: rs0) term1).
      one_step. apply S_FuseInc with (b:=<< N k v; [] >> :: b1 ++ << n; os1 ++ l ->> inc incby ks :: l' ->> inc incby' ks :: os2 >> :: b2) (b1:=<< N k v; [] >> :: b1); crush.
    * crush.
  (* S_Last *)
  -
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
  - destruct n as [k v].
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
  inversion cxcz; try solve [subst; eauto].
  (* S_Empty *)
  - crush. destruct b1; crush.
  (* S_Add *)
  - subst.
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
  (* S_Last *)
  - ssame. apply List.app_inj_tail in H0. inv H0. inv H1. crush.
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

Axiom noe_indo' :
  forall c c',
  c --> c' ->
  exists n c'', c' -->*[n] c'' /\ normal_form c''.

Lemma wt_to_nf : forall c,
  well_typed c ->
  exists n c', c -->*[n] c' /\ normal_form c'.
Proof using.
  intros c WT.
  remember WT.
  inversion WT.
  destruct H1.
  unfold config_has_type in H1.
  destruct c as [b os rs t]; subst.
  apply progress' with (b:=b) (os:=os) (rs:=rs) in H1; eauto.
  destruct H1.
  - exists 0. exists (C b os rs t). remember (C b os rs t) as c. assert (normal_form c) by (eapply dry_normal_form; eauto). split; eauto.
  - destruct H1. remember H1 as Hc. clear HeqHc. apply noe_indo' in H1. destruct H1. destruct H1. destruct H1.
    exists (S x1). exists x2. split; eauto.
Qed.

Axiom noe_indo :
  forall cx cy,
  cx == cy ->
  forall cx' cy' n m,
  cx -->*[n] cx' ->
  cy -->*[m] cy' ->
  (cx' -v cy').

Lemma well_typed_preservation' : forall c n c',
  well_typed c ->
  c -->*[n] c' ->
  well_typed c'.
Proof using.
  intros c n c' WT Hmulti.
  induction Hmulti; subst; eauto.
  assert (well_typed y) by (eapply well_typed_preservation; eauto).
  eauto.
Qed.

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
    assert (exists n cw, cy -->*[n] cw /\ normal_form cw).
    {
    apply wt_to_nf.
    apply well_typed_preservation' in H1; eauto.
    apply well_typed_preservation in H0; eauto.
    }
    destruct H6 as [n' H']. destruct H' as [cw cycw]. destruct cycw as [cycw nfcw].
    assert (exists n cw', cy'' -->*[n] cw' /\ normal_form cw').
    {
    apply wt_to_nf.
    apply well_typed_preservation' in H; eauto.
    apply well_typed_preservation in H0; eauto.
    }
    destruct H6 as [n'' H']. destruct H' as [cw' cycw']. destruct cycw' as [cycw' nfcw'].
    assert (exists n cv, cz'' -->*[n] cv /\ normal_form cv).
    {
    apply wt_to_nf.
    apply well_typed_preservation' in H4; eauto.
    apply well_typed_preservation in H2; eauto.
    }
    destruct H6 as [n''' H']. destruct H' as [cv cycv]. destruct cycv as [cycv nfcv].
    assert (exists n cv', cz -->*[n] cv' /\ normal_form cv').
    {
    apply wt_to_nf.
    apply well_typed_preservation' in H3; eauto.
    apply well_typed_preservation in H2; eauto.
    }
    destruct H6 as [n'''' H']. destruct H' as [cv' cycv']. destruct cycv' as [cycv' nfcv'].
    assert (Hsimcy' : cy' == cy') by crush.
    assert (cw == cw').
    {
      eapply noe_indo with (cx':=cw) (cy':=cw') in Hsimcy'.
      - destruct Hsimcy'.
        destruct H6.
        destruct H6.
        destruct H6.
        destruct H7.
        destruct H7.
        assert (x = cw).
        {
          destruct x3.
          - apply star_zero in H6; eauto.
          - inversion H6. subst. exfalso. unfold normal_form in nfcw. apply nfcw. eauto.
        }
        subst.
        assert (x0 = cw').
        {
          destruct x4.
          - apply star_zero in H7; eauto.
          - inversion H7. subst. exfalso. unfold normal_form in nfcw'. apply nfcw'. eauto.
        }
        subst. assumption.
      - instantiate (1:=n+n'). eauto.
      - instantiate (1:=x1+n''). eauto.
    }
    assert (Hsimcz' : cz' == cz') by crush.
    assert (cv == cv').
    {
      eapply noe_indo with (cx':=cv) (cy':=cv') in Hsimcz'.
      - destruct Hsimcz'.
        destruct H7.
        destruct H7.
        destruct H7.
        destruct H8.
        destruct H8.
        assert (x = cv).
        {
          destruct x3.
          - apply star_zero in H7; eauto.
          - inversion H7. subst. exfalso. unfold normal_form in nfcv. apply nfcv. eauto.
        }
        subst.
        assert (x0 = cv').
        {
          destruct x4.
          - apply star_zero in H8; eauto.
          - inversion H8. subst. exfalso. unfold normal_form in nfcv'. apply nfcv'. eauto.
        }
        subst. assumption.
      - instantiate (1:=x2+n'''). eauto.
      - instantiate (1:=m+n''''). eauto.
    }
    assert (cw' == cv).
    {
      eapply noe_indo with (cx':=cw') (cy':=cv) in H5.
      - destruct H5.
        destruct H5.
        destruct H5.
        destruct H5.
        destruct H8.
        destruct H8.
        assert (x = cw').
        {
          destruct x3.
          - apply star_zero in H5; eauto.
          - inversion H5. subst. exfalso. unfold normal_form in nfcw'. apply nfcw'. eauto.
        }
        subst.
        assert (x0 = cv).
        {
          destruct x4.
          - apply star_zero in H8; eauto.
          - inversion H8. subst. exfalso. unfold normal_form in nfcv. apply nfcv. eauto.
        }
        subst. assumption.
      - eauto.
      - eauto.
    }
    apply ex_intro with cw.
    apply ex_intro with cv'.
    split; try split.
    + eauto.
    + eauto.
    + apply cequiv_trans with cw'; auto.
      apply cequiv_trans with cv; auto.
Qed.
