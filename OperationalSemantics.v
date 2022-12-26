
Require Import CpdtTactics.
From Coq Require Import Arith.PeanoNat.
From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
Import ListNotations.

Require Import SyntaxRuntime.

Local Set Warnings "-implicit-core-hint-db".

Set Implicit Arguments.

Ltac inv H := inversion H; subst; clear H.

Fixpoint keyset_to_keyset (t : term) :=
match t with
| t_ks_nil => []
| t_ks_cons (t_result k) ks => k :: keyset_to_keyset ks
| _ => []
end.

Inductive frff : Type :=
| FRf : term -> rstream -> frff.
Hint Constructors frff.
Inductive frtt : Type :=
| FRt : term -> ostream -> frtt.
Hint Constructors frtt.
Reserved Notation "frff '==>' frtt" (at level 40).

Inductive fstep : frff -> frtt -> Prop :=
| F_Emit_PFold : forall rs l f t ks,
    value f ->
    value t ->
    value ks ->
    FRf (t_emit_pfold l f t ks) rs ==> FRt (t_label l) [l ->> pfold f t (keyset_to_keyset ks)]
| F_Emit_PMap : forall c b os rs l f ks,
    c = C b os rs (t_emit_pmap l f ks) ->
    value f ->
    value ks ->
    FRf (t_emit_pmap l f ks) rs ==> FRt (t_label l) [l ->> pmap f (keyset_to_keyset ks)]
| F_Emit_Add : forall rs l k v,
    FRf (t_emit_add l (t_result k) (t_result v)) rs ==> FRt (t_label l) [l ->> add k (t_result v)]
| F_Claim : forall rs l v,
    In (l ->>> v) rs ->
    FRf (t_downarrow (t_label l)) rs ==> FRt (t_result v) []
| F_Ctx_Downarrow : forall os rs t t',
    FRf t rs ==> FRt t' os ->
    FRf (t_downarrow t) rs ==> FRt (t_downarrow t') os
| F_Ctx_Emit_PFold1 : forall os rs l t1 t2 t3 t1',
    FRf t1 rs ==> FRt t1' os ->
    FRf (t_emit_pfold l t1 t2 t3) rs ==> FRt (t_emit_pfold l t1' t2 t3) os
| F_Ctx_Emit_PFold2 : forall os rs l t1 t2 t3 t2',
    value t1 ->
    FRf t2 rs ==> FRt t2' os ->
    FRf (t_emit_pfold l t1 t2 t3) rs ==> FRt (t_emit_pfold l t1 t2' t3) os
| F_Ctx_Emit_PFold3 : forall os rs l t1 t2 t3 t3',
    value t1 ->
    value t2 ->
    FRf t3 rs ==> FRt t3' os ->
    FRf (t_emit_pfold l t1 t2 t3) rs ==> FRt (t_emit_pfold l t1 t2 t3') os
| F_Ctx_Emit_PMap1 : forall os rs l t1 t2 t1',
    FRf t1 rs ==> FRt t1' os ->
    FRf (t_emit_pmap l t1 t2) rs ==> FRt (t_emit_pmap l t1' t2) os
| F_Ctx_Emit_PMap2 : forall os rs l t1 t2 t2',
    value t1 ->
    FRf t2 rs ==> FRt t2' os ->
    FRf (t_emit_pmap l t1 t2) rs ==> FRt (t_emit_pmap l t1 t2') os
| F_Ctx_Emit_Add1 : forall os rs l t1 t2 t1',
    FRf t1 rs ==> FRt t1' os ->
    FRf (t_emit_add l t1 t2) rs ==> FRt (t_emit_add l t1' t2) os
| F_Ctx_Emit_Add2 : forall os rs l t1 t2 t2',
    value t1 ->
    FRf t2 rs ==> FRt t2' os ->
    FRf (t_emit_add l t1 t2) rs ==> FRt (t_emit_add l t1 t2') os
| F_App : forall rs x T t12 v2,
    value v2 ->
    FRf (t_app (t_abs x T t12) v2) rs ==> FRt (#[x:=v2]t12) []
| F_App1 : forall os rs t1 t2 t1',
    FRf t1 rs ==> FRt t1' os ->
    FRf (t_app t1 t2) rs ==> FRt (t_app t1' t2) os
| F_App2 : forall os rs t1 t2 t2',
    value t1 ->
    FRf t2 rs ==> FRt t2' os ->
    FRf (t_app t1 t2) rs ==> FRt (t_app t1 t2') os
| F_Ctx_KS1 : forall os rs k ks k',
    FRf k rs ==> FRt k' os ->
    FRf (t_ks_cons k ks) rs ==> FRt (t_ks_cons k' ks) os
| F_Ctx_KS2 : forall os rs k ks ks',
    value k ->
    FRf ks rs ==> FRt ks' os ->
    FRf (t_ks_cons k ks) rs ==> FRt (t_ks_cons k ks') os
| F_Ctx_Node1 : forall os rs k p es k',
    FRf k rs ==> FRt k' os ->
    FRf (t_node k p es) rs ==> FRt (t_node k' p es) os
| F_Ctx_Node2 : forall os rs k p es p',
    value k ->
    FRf p rs ==> FRt p' os ->
    FRf (t_node k p es) rs ==> FRt (t_node k p' es) os
| F_Ctx_Node3 : forall os rs k p es es',
    value k ->
    value p ->
    FRf es rs ==> FRt es' os ->
    FRf (t_node k p es) rs ==> FRt (t_node k p es') os
| F_Fix : forall rs t T,
    value t ->
    FRf (t_fix T t) rs ==> FRt (t_abs "x" T (t_app (t_app t (t_fix T t)) (t_var "x"))) []
| F_Ctx_Na1 : forall os rs t t',
    FRf t rs ==> FRt t' os ->
    FRf (t_na1 t) rs ==> FRt (t_na1 t') os
| F_Ctx_Na2 : forall os rs t t',
    FRf t rs ==> FRt t' os ->
    FRf (t_na2 t) rs ==> FRt (t_na2 t') os
| F_Ctx_Na3 : forall os rs t t',
    FRf t rs ==> FRt t' os ->
    FRf (t_na3 t) rs ==> FRt (t_na3 t') os
| F_Na1 : forall rs t1 t2 t3,
    value t1 ->
    value t2 ->
    value t3 ->
    FRf (t_na1 (t_node t1 t2 t3)) rs ==> FRt t1 []
| F_Na2 : forall rs t1 t2 t3,
    value t1 ->
    value t2 ->
    value t3 ->
    FRf (t_na2 (t_node t1 t2 t3)) rs ==> FRt t2 []
| F_Na3 : forall rs t1 t2 t3,
    value t1 ->
    value t2 ->
    value t3 ->
    FRf (t_na3 (t_node t1 t2 t3)) rs ==> FRt t3 []
| F_Ctx_Fix : forall os rs t t' T,
    FRf t rs ==> FRt t' os ->
    FRf (t_fix T t) rs ==> FRt (t_fix T t') os
where "frff ==> frtt" := (fstep frff frtt).
Hint Constructors fstep.

Inductive lappears_free_in : label -> term -> Prop :=
| lafi_label : forall l,
    lappears_free_in l (t_label l)
| lafi_app1 : forall x t1 t2,
    lappears_free_in x t1 ->
    lappears_free_in x (t_app t1 t2)
| lafi_app2 : forall x t1 t2,
    lappears_free_in x t2 ->
    lappears_free_in x (t_app t1 t2)
| lafi_abs : forall x y T11 t12,
    lappears_free_in x t12 ->
    lappears_free_in x (t_abs y T11 t12)
| lafi_ks1 : forall x k ks,
    lappears_free_in x k ->
    lappears_free_in x (t_ks_cons k ks)
| lafi_ks2 : forall x k ks,
    lappears_free_in x ks ->
    lappears_free_in x (t_ks_cons k ks)
| lafi_node1 : forall x k p es,
    lappears_free_in x k ->
    lappears_free_in x (t_node k p es)
| lafi_node2 : forall x k p es,
    lappears_free_in x p ->
    lappears_free_in x (t_node k p es)
| lafi_node3 : forall x k p es,
    lappears_free_in x es ->
    lappears_free_in x (t_node k p es)
| lafi_downarrow : forall x t,
    lappears_free_in x t ->
    lappears_free_in x (t_downarrow t)
| lafi_emit_getpay1 : forall x l t1 t2 t3,
    lappears_free_in x t1 ->
    lappears_free_in x (t_emit_pfold l t1 t2 t3)
| lafi_emit_getpay2 : forall x l t1 t2 t3,
    lappears_free_in x t2 ->
    lappears_free_in x (t_emit_pfold l t1 t2 t3)
| lafi_emit_getpay3 : forall x l t1 t2 t3,
    lappears_free_in x t3 ->
    lappears_free_in x (t_emit_pfold l t1 t2 t3)
| lafi_emit_pmap1 : forall x l t1 t2,
    lappears_free_in x t1 ->
    lappears_free_in x (t_emit_pmap l t1 t2)
| lafi_emit_pmap2 : forall x l t1 t2,
    lappears_free_in x t2 ->
    lappears_free_in x (t_emit_pmap l t1 t2)
| lafi_emit_add1 : forall x l t1 t2,
    lappears_free_in x t1 ->
    lappears_free_in x (t_emit_add l t1 t2)
| lafi_emit_add2 : forall x l t1 t2,
    lappears_free_in x t2 ->
    lappears_free_in x (t_emit_add l t1 t2)
| lafi_na1 : forall x t,
    lappears_free_in x t ->
    lappears_free_in x (t_na1 t)
| lafi_na2 : forall x t,
    lappears_free_in x t ->
    lappears_free_in x (t_na2 t)
| lafi_na3 : forall x t,
    lappears_free_in x t ->
    lappears_free_in x (t_na3 t)
| lafi_fix : forall x t T,
    lappears_free_in x t ->
    lappears_free_in x (t_fix T t).
Hint Constructors lappears_free_in.


Definition pmap_compose f f' :=
t_abs "x" Result (t_app f (t_app f' (t_var "x"))).

Reserved Notation "c1 '-->' c2" (at level 40).

(* Fig 11: Operational Semantics *)

Inductive step : config -> config -> Prop :=
(* frontend *)
| S_Frontend : forall c b os rs t os' t',
    c = C b os rs t ->
    FRf t rs ==> FRt t' os' ->
    c --> C b (os ++ os') rs t'
(* to-graph *)
| S_Empty : forall c os rs os' o l op term H,
    c = C [] os rs term ->
    os = o :: os' ->
    o = l ->> op ->
    not_add op ->
    c --> C [] os' (l ->>> (@final op) H :: rs) term
| S_First : forall c b os rs o os' b' n1 os1 op l term,
    c = C b os rs term ->
    os = o :: os' ->
    b = (<<n1; os1>>)::b' ->
    o = l ->> op ->
    not_add op ->
    c --> C (<<n1; (os1 ++ [o])>> :: b') os' rs term
| S_Add : forall c b os rs os' l k v o term H,
    c = C b os rs term ->
    os = o :: os' ->
    o = l ->> add k v ->
    c --> C (<<(N k v t_ks_nil); []>> :: b) os' (l ->>> (@final (add k v)) H :: rs) term
(* task *)
| S_PMap : forall c b os rs b1 s1 s1' os1 os1' os1'' b2 k v es ks l term f,
    c = C b os rs term ->
    b = b1 ++ s1 :: b2 ->
    s1 = <<N k v es; os1>> ->
    os1 = l ->> pmap f ks :: os1'' ->
    os1' = l ->> pmap f (remove Nat.eq_dec k ks) :: os1'' ->
    s1' = <<N k (t_app f v) es; os1'>> ->
    In k ks ->
    c --> C (b1 ++ s1' :: b2) os rs term
| S_PFold : forall c b os rs b1 s1 s1' os1 os1' os1'' b2 k t es f t' ks l term,
    c = C b os rs term ->
    b = b1 ++ s1 :: b2 ->
    s1 = <<N k t es; os1>> ->
    os1 = l ->> pfold f t' ks :: os1'' ->
    os1' = l ->> pfold f (t_app (t_app f t) t') (remove Nat.eq_dec k ks) :: os1'' ->
    s1' = <<N k t es; os1'>> ->
    In k ks ->
    c --> C (b1 ++ s1' :: b2) os rs term
| S_Last : forall c b os rs l n1 os1 os1' op b1 k term H,
    c = C b os rs term ->
    b = b1 ++ [<<n1; os1>>] ->
    os1 = l ->> op :: os1' ->
    k = getKey n1 ->
    not (In k (target op)) ->
    c --> C (b1 ++ [<<n1; os1'>>]) os (l ->>> (@final op) H :: rs) term
(* Fig 12: Temporal Locality Optimization *)
| S_FusePMap : forall c b n b1 b2 os os1 os2 rs term f f' ks l l' H,
    c = C b os rs term ->
    b = b1 ++ <<n; os1 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os2>> :: b2 ->
    c --> C (b1 ++ <<n; os1 ++ l' ->> pmap (pmap_compose f' f) ks :: os2>> :: b2) os (l ->>> (@final (pmap f ks)) H :: rs) term
| S_SwapReads : forall c b n b1 b2 os os1 os2 rs term l l' f f' ks ks' t t',
    c = C b os rs term ->
    b = b1 ++ <<n; os1 ++ l ->> pfold f t ks :: l' ->> pfold f' t' ks' :: os2>> :: b2 ->
    not (lappears_free_in l f') ->
    not (lappears_free_in l t') ->
    c --> (C (b1 ++ <<n; os1 ++ l' ->> pfold f' t' ks' :: l ->> pfold f t ks :: os2>> :: b2) os rs term)
| S_Prop : forall c b os rs n1 n2 os1 os2 b1 b2 l op term,
    c = C b os rs term ->
    ~ (In (getKey n1) (target op)) ->
    b = b1 ++ <<n1; l ->> op :: os1>> :: <<n2; os2>> :: b2 ->
    c --> C (b1 ++ <<n1; os1>> :: <<n2; os2 ++ [l ->> op]>> :: b2) os rs term
(* task *)
| S_Load : forall c b os0 rs0 term0 b1 b2 k t es t' os,
   c = C b os0 rs0 term0 ->
   b = b1 ++ <<N k t es; os>> :: b2 ->
   FRf t rs0 ==> FRt t' [] ->
   c --> C (b1 ++ <<N k t' es; os>> :: b2) os0 rs0 term0
| S_LoadPFold : forall c b b' os0 rs0 term0 l b1 b2 k t es f t1 t1' ks os os',
   c = C b os0 rs0 term0 ->
   b = b1 ++ <<N k t es; os ++ l ->> pfold f t1 ks :: os'>> :: b2 ->
   FRf t1 rs0 ==> FRt t1' [] ->
   b' = b1 ++ <<N k t es; os ++ l ->> pfold f t1' ks :: os'>> :: b2 ->
   c --> C b' os0 rs0 term0
where "c1 --> c2" := (step c1 c2).
Hint Constructors step.

Inductive star {A : Type} (R : A -> A -> Prop) : nat -> A -> A -> Prop :=
| Zero : forall x, star R 0 x x
| Step : forall x y, R x y -> forall n z, star R n y z -> star R (S n) x z.
Hint Constructors star.

Notation "c1 '-->*[' n ']' c2" := (star step n c1 c2) (at level 40).

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

Definition backend_keys (b : backend) :=
map (fun s => getKey (get_node s)) b.
Hint Unfold backend_keys.

Definition ostream_keys (os : ostream) :=
List.concat (map (fun o => match o with
             | l ->> add k _ => [k]
             | _ => []
           end) os).
Hint Unfold ostream_keys.

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
