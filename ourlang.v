(* TODO GRAPH TYPING *)
(* EMITTABILITY *)

Require Import CpdtTactics.
From Coq Require Import Lists.List.
From Coq Require Import Bool.Bool.
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
Notation label := nat.
Notation keyset := (list key).
Notation result := nat.

(* ***********************frontend *)

Inductive type : Type :=
| Result : type
| Keyset : type
| Label : type -> type
| Arrow : type -> type -> bool -> type.
Hint Constructors type.

Inductive term : Type :=
| t_var : string -> term
| t_app : term -> term -> term
| t_abs : string -> type -> term -> term
| t_label : label -> term
| t_result : result -> term
| t_ks_nil : term
| t_ks_cons : term -> term -> term
| t_downarrow : term -> term
| t_emit_ot_pfold : label -> term -> term -> term -> term
| t_emit_ot_pmap : label -> term -> term -> term
| t_emit_ot_add : label -> term -> term -> term.
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
  | t_label l =>
      t_label l
  | t_result r =>
      t_result r
  | t_ks_nil => t_ks_nil
  | t_ks_cons k ks =>
      t_ks_cons (#[x:=s] k) (#[x:=s] ks)
  | t_downarrow t =>
      t_downarrow (#[x:=s] t)
  | t_emit_ot_pfold l t1 t2 t3 =>
      t_emit_ot_pfold l (#[x:=s] t1) (#[x:=s] t2) (#[x:=s] t3)
  | t_emit_ot_pmap l t1 t2 =>
      t_emit_ot_pmap l (#[x:=s] t1) (#[x:=s] t2)
  | t_emit_ot_add l t1 t2 =>
      t_emit_ot_add l (#[x:=s] t1) (#[x:=s] t2)
  end
where "'#[' x ':=' s ']' t" := (e_subst x s t).

(* ***********************end frontend *)

Notation payload := term.

Inductive node : Type :=
| N : key -> payload -> node.
Hint Constructors node.

Inductive operation : Type :=
| pmap : term -> keyset -> operation
| add : key -> payload -> operation
| pfold : term -> term -> keyset -> operation.
Hint Constructors operation.

Definition target op :=
match op with
| pmap _ ks => ks
| add _ _ => []
| pfold _ _ ks => ks
end.
Hint Unfold target.

Definition not_add op : Prop :=
match op with
| pmap _ _ => True
| add _ _ => False
| pfold _ _ _ => True
end.
Hint Unfold not_add.

Definition is_fold op : Prop :=
match op with
| pmap _ _ => False
| add _ _ => False
| pfold _ _ _ => True
end.

Definition not_fold_or_done op := (not (is_fold op)) \/ (exists t1 v t2, op = pfold t1 (t_result v) t2).
Hint Unfold not_fold_or_done.

Definition final : forall (op : operation), not_fold_or_done op -> result.
refine (fun op:operation =>
        match op return not_fold_or_done op -> result with
        | pmap _ ks => fun _ => 0
        | add k _ => fun _ => k
        | pfold _ (t_result v) _ => fun _ => v
        | _ => _
        end).
intros. exact 1.
intros. exact 1.
intros. exact 1.
intros. exact 1.
intros. exact 1.
intros. exact 1.
intros. exact 1.
intros. exact 1.
intros. exact 1.
intros. exact 1.
Defined.
Hint Unfold final.

Inductive labeled_operation : Type :=
| lo : label -> operation -> labeled_operation.
Hint Constructors labeled_operation.

Notation "l ->> o" := (lo l o) (at level 40).

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

Inductive has_type : context -> term -> type -> bool -> Prop :=
| T_Var : forall Gamma x T,
    Gamma x = Some T ->
    has_type Gamma (t_var x) T false
| T_Abs : forall Gamma x T11 T12 t12 E,
    has_type (x |-> T11 ; Gamma) t12 T12 E ->
    has_type Gamma (t_abs x T11 t12) (Arrow T11 T12 E) false
| T_App : forall T11 T12 Gamma t1 t2 E1 E2 E3,
    has_type Gamma t1 (Arrow T11 T12 E1) E2 ->
    has_type Gamma t2 T11 E3 ->
    has_type Gamma (t_app t1 t2) T12 (E1 || E2 || E3)
| T_Result : forall r Gamma,
    has_type Gamma (t_result r) Result false
| T_KS_Nil : forall Gamma,
    has_type Gamma t_ks_nil Keyset false
| T_KS_Cons : forall k ks Gamma E1 E2,
    has_type Gamma k Result E1 ->
    has_type Gamma ks Keyset E2 ->
    has_type Gamma (t_ks_cons k ks) Keyset (E1 || E2)
| T_Downarrow : forall ft t Gamma E,
    has_type Gamma t (Label ft) E ->
    has_type Gamma (t_downarrow t) ft E
| T_Label : forall l Gamma,
    has_type Gamma (t_label l) (Label Result) false
| T_Emit_OT_PFold : forall l t1 t2 t3 Gamma E1 E2 E3,
    has_type Gamma t1 (Arrow Result (Arrow Result Result false) false) E1 ->
    has_type Gamma t2 Result E2 ->
    has_type Gamma t3 Keyset E3 ->
    has_type Gamma (t_emit_ot_pfold l t1 t2 t3) (Label Result) true
| T_Emit_OT_PMap : forall l t1 t2 Gamma E1 E2,
    has_type Gamma t1 (Arrow Result Result false) E1 ->
    has_type Gamma t2 Keyset E2 ->
    has_type Gamma (t_emit_ot_pmap l t1 t2) (Label Result) true
| T_Emit_OT_Add : forall l t1 t2 Gamma E1 E2,
    has_type Gamma t1 Result E1 ->
    has_type Gamma t2 Result E2 ->
    has_type Gamma (t_emit_ot_add l t1 t2) (Label Result) true.
Hint Constructors has_type.

Inductive well_typed_operation : operation -> Prop :=
| WTO_PFold : forall t1 t2 ks,
    value t1 ->
    has_type empty t1 (Arrow Result (Arrow Result Result false) false) false ->
    has_type empty t2 Result false ->
    well_typed_operation (pfold t1 t2 ks)
| WTO_PMap : forall t ks,
    value t ->
    has_type empty t (Arrow Result Result false) false ->
    well_typed_operation (pmap t ks)
| WTO_Add : forall k t,
    has_type empty t Result false ->
    well_typed_operation (add k t).
Hint Constructors well_typed_operation.

Inductive well_typed_top_ostream : ostream -> Prop :=
| WTTO_nil :
    well_typed_top_ostream []
| WTTO_cons : forall l op os,
    (match op with
     | pfold _ t _ => exists r, t = t_result r
     | _ => True
     end) ->
    well_typed_top_ostream os ->
    well_typed_operation op ->
    well_typed_top_ostream (l ->> op :: os).
Hint Constructors well_typed_top_ostream.

Inductive well_typed_ostream : ostream -> Prop :=
| WTO_nil :
    well_typed_ostream []
| WTO_cons : forall l op os,
    well_typed_ostream os ->
    well_typed_operation op ->
    well_typed_ostream (l ->> op :: os).
Hint Constructors well_typed_ostream.

Inductive well_typed_backend : backend -> Prop :=
| WTB_nil :
    well_typed_backend []
| WTB_cons : forall k t os b,
    has_type empty t Result false ->
    well_typed_ostream os ->
    well_typed_backend b ->
    well_typed_backend (<<N k t; os>> :: b).
Hint Constructors well_typed_backend.

Inductive config_has_type : config -> type -> bool -> Prop :=
| CT : forall b os rs t T E,
    well_typed_backend b ->
    well_typed_top_ostream os ->
    has_type empty t T E ->
    config_has_type (C b os rs t) T E.
Hint Constructors config_has_type.

Axiom graph_typing : forall n k t,
    n = N k t ->
    has_type empty t Result false.
Axiom graph_typing' : forall op f t ks,
    op = pfold f t ks ->
    has_type empty t Result false.
Axiom graph_typing'' : forall op f t ks,
    op = pfold f t ks ->
    has_type empty f (Arrow Result (Arrow Result Result false) false) false.

(* ****** end typing *)

Fixpoint keyset_to_keyset (t : term) :=
match t with
| t_ks_nil => []
| t_ks_cons (t_result k) ks => k :: keyset_to_keyset ks
| _ => []
end.

Definition pmap_compose f f' :=
t_abs "x" Result (t_app f (t_app f' (t_var "x"))).

Reserved Notation "c1 '-->' c2" (at level 40).

Inductive step : config -> config -> Prop :=
(* frontend *)
| S_Emit_OT_PFold : forall c b os rs l f t ks,
    c = C b os rs (t_emit_ot_pfold l f t ks) ->
    value f ->
    value t ->
    value ks ->
    c --> C b (os ++ [l ->> pfold f t (keyset_to_keyset ks)]) rs (t_label l)
| S_Emit_OT_PMap : forall c b os rs l f ks,
    c = C b os rs (t_emit_ot_pmap l f ks) ->
    value f ->
    value ks ->
    c --> C b (os ++ [l ->> pmap f (keyset_to_keyset ks)]) rs (t_label l)
| S_Emit_OT_Add : forall c b os rs l k v,
    c = C b os rs (t_emit_ot_add l (t_result k) (t_result v)) ->
    c --> C b (os ++ [l ->> add k (t_result v)]) rs (t_label l)
| S_Claim : forall c b os rs l v,
    c = C b os rs (t_downarrow (t_label l)) ->
    In (l ->>> v) rs ->
    c --> C b os rs (t_result v)
| S_Ctx_Downarrow : forall c b os os' rs t t',
    c = C b os rs (t_downarrow t) ->
    C [] [] rs t --> C [] os' rs t' ->
    c --> C b (os ++ os') rs (t_downarrow t')
| S_Ctx_Emit_OT_PFold1 : forall c b os os' rs l t1 t2 t3 t',
    c = C b os rs (t_emit_ot_pfold l t1 t2 t3) ->
    C [] [] rs t1 --> C [] os' rs t' ->
    c --> C b (os ++ os') rs (t_emit_ot_pfold l t' t2 t3)
| S_Ctx_Emit_OT_PFold2 : forall c b os os' rs l t1 t2 t3 t',
    c = C b os rs (t_emit_ot_pfold l t1 t2 t3) ->
    value t1 ->
    C [] [] rs t2 --> C [] os' rs t' ->
    c --> C b (os ++ os') rs (t_emit_ot_pfold l t1 t' t3)
| S_Ctx_Emit_OT_PFold3 : forall c b os os' rs l t1 t2 t3 t',
    c = C b os rs (t_emit_ot_pfold l t1 t2 t3) ->
    value t1 ->
    value t2 ->
    C [] [] rs t3 --> C [] os' rs t' ->
    c --> C b (os ++ os') rs (t_emit_ot_pfold l t1 t2 t')
| S_Ctx_Emit_OT_PMap1 : forall c b os os' rs l t1 t1' t2,
    c = C b os rs (t_emit_ot_pmap l t1 t2) ->
    C [] [] rs t1 --> C [] os' rs t1' ->
    c --> C b (os ++ os') rs (t_emit_ot_pmap l t1' t2)
| S_Ctx_Emit_OT_PMap2 : forall c b os os' rs l t1 t2 t2',
    c = C b os rs (t_emit_ot_pmap l t1 t2) ->
    value t1 ->
    C [] [] rs t2 --> C [] os' rs t2' ->
    c --> C b (os ++ os') rs (t_emit_ot_pmap l t1 t2')
| S_Ctx_Emit_OT_Add1 : forall c b os os' rs l t1 t1' t2,
    c = C b os rs (t_emit_ot_add l t1 t2) ->
    C [] [] rs t1 --> C [] os' rs t1' ->
    c --> C b (os ++ os') rs (t_emit_ot_add l t1' t2)
| S_Ctx_Emit_OT_Add2 : forall c b os os' rs l t1 t2 t2',
    c = C b os rs (t_emit_ot_add l t1 t2) ->
    value t1 ->
    C [] [] rs t2 --> C [] os' rs t2' ->
    c --> C b (os ++ os') rs (t_emit_ot_add l t1 t2')
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
    c --> C (<<(N k v); []>> :: b) os' (l ->>> (@final (add k v)) H :: rs) term
(* task *)
| S_PMap : forall c b os rs b1 s1 s1' os1 os1' os1'' b2 k v ks l term f,
    c = C b os rs term ->
    b = b1 ++ s1 :: b2 ->
    s1 = <<N k v; os1>> ->
    os1 = l ->> pmap f ks :: os1'' ->
    os1' = l ->> pmap f (remove Nat.eq_dec k ks) :: os1'' ->
    s1' = <<N k (t_app f v); os1'>> ->
    In k ks ->
    c --> C (b1 ++ s1' :: b2) os rs term
| S_PFold : forall c b os rs b1 s1 s1' os1 os1' os1'' b2 k t f t' ks l term,
    c = C b os rs term ->
    b = b1 ++ s1 :: b2 ->
    s1 = <<N k t; os1>> ->
    os1 = l ->> pfold f t' ks :: os1'' ->
    os1' = l ->> pfold f (t_app (t_app f t) t') (remove Nat.eq_dec k ks) :: os1'' ->
    s1' = <<N k t; os1'>> ->
    In k ks ->
    c --> C (b1 ++ s1' :: b2) os rs term
| S_Last : forall c b os rs l n1 os1 os1' op b1 k term H,
    c = C b os rs term ->
    b = b1 ++ [<<n1; os1>>] ->
    os1 = l ->> op :: os1' ->
    k = getKey n1 ->
    not (In k (target op)) ->
    c --> C (b1 ++ [<<n1; os1'>>]) os (l ->>> (@final op) H :: rs) term
| S_FusePMap : forall c b n b1 b2 os os1 os2 rs term f f' ks l l' H,
    c = C b os rs term ->
    b = b1 ++ <<n; os1 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os2>> :: b2 ->
    c --> C (b1 ++ <<n; os1 ++ l ->> pmap (pmap_compose f' f) ks :: os2>> :: b2) os (l' ->>> (@final (pmap f' ks)) H :: rs) term
| S_Prop : forall c b os rs n1 n2 os1 os2 b1 b2 l op term,
    c = C b os rs term ->
    ~ (In (getKey n1) (target op)) ->
    b = b1 ++ <<n1; l ->> op :: os1>> :: <<n2; os2>> :: b2 ->
    c --> C (b1 ++ <<n1; os1>> :: <<n2; os2 ++ [l ->> op]>> :: b2) os rs term
(* task *)
| S_Load : forall c b os0 rs0 term0 b1 b2 k t t' os,
   c = C b os0 rs0 term0 ->
   b = b1 ++ <<N k t; os>> :: b2 ->
   C [] [] rs0 t --> C [] [] rs0 t' ->
   c --> C (b1 ++ <<N k t'; os>> :: b2) os0 rs0 term0
| S_LoadPFold : forall c b b' os0 rs0 term0 l b1 b2 k t f t1 t1' ks os os',
   c = C b os0 rs0 term0 ->
   b = b1 ++ <<N k t; os ++ l ->> pfold f t1 ks :: os'>> :: b2 ->
   C [] [] rs0 t1 --> C [] [] rs0 t1' ->
   b' = b1 ++ <<N k t; os ++ l ->> pfold f t1' ks :: os'>> :: b2 ->
   c --> C b' os0 rs0 term0
(* S_Complete *)
where "c1 --> c2" := (step c1 c2).
Hint Constructors step.

Inductive star {A : Type} (R : A -> A -> Prop) : nat -> A -> A -> Prop :=
| Zero : forall x, star R 0 x x
| Step : forall x y, R x y -> forall n z, star R n y z -> star R (S n) x z.
Hint Constructors star.

Notation "c1 '-->*[' n ']' c2" := (star step n c1 c2) (at level 40).

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

Inductive well_typed : config -> Prop :=
| WT : forall c,
    distinct (config_keys c) ->
    distinct (config_labels c) ->
    (exists T b, config_has_type c T b) ->
    well_typed c.
Hint Constructors well_typed.

Example wt : well_typed (C [<<(N 1 (t_result 2)); [5 ->> pmap (t_abs "x" Result (t_var "x")) []]>>; <<(N 2 (t_result 3)); [4 ->> pmap (t_abs "x" Result (t_var "x")) []]>>] [2 ->> pmap (t_abs "x" Result (t_var "x")) []; 3 ->> pmap (t_abs "x" Result (t_var "x")) []] [1 ->>> 2] noop).
Proof using.
  eapply WT; repeat crush; repeat (eapply distinct_many; crush).
  unfold noop; eauto.
  exists Result, false.
  constructor; eauto.
  constructor; eauto.
  constructor; eauto.
  constructor; eauto.
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
  forall c b os rs l os' t' t1 t2 t3,
  c = C b os rs (t_emit_ot_pfold l t1 t2 t3) ->
  well_typed c ->
  well_typed (C b (os ++ os') rs t').
Axiom fresh'''' :
  forall c b os rs l t1 t2 os' t',
  c = C b os rs (t_emit_ot_pmap l t1 t2) ->
  well_typed c ->
  well_typed (C b (os ++ os') rs t').
Axiom fresh''''' :
  forall c b os os' rs t1 t2 t',
  c = C b os rs (t_ks_cons t1 t2) ->
  well_typed c ->
  well_typed (C b (os ++ os') rs t').
Axiom fresh'''''' :
  forall c b os rs l t1 t2 os' t',
  c = C b os rs (t_emit_ot_add l t1 t2) ->
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
  inversion H; ssame; try solve [destruct b1; crush]; try solve [crush].
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

Ltac narrow_terms := try (match goal with
                          | [H : value _ |- _] => inv H
                          end);
                     try (match goal with
                          | [H : empty _ = Some _ |- _] => inv H
                          end);
                     try solve [match goal with
                                | [H : has_type _ _ _ _ |- _] => inv H
                                end].

(* ****** typing *)
Lemma canonical_forms_fun : forall t T1 T2 E1 E2,
  has_type empty t (Arrow T1 T2 E1) E2 ->
  value t ->
  exists x u, t = t_abs x T1 u.
Proof using.
  intros t T1 T2 HT HVal.
  inversion HVal; intros; subst; try inversion HT; subst; auto; inv H; narrow_terms; eauto.
Qed.

Lemma canonical_forms_emit_ot_pmap : forall t l t1 t2 E1 E2 E3,
  t = t_emit_ot_pmap l t1 t2 ->
  has_type empty t1 (Arrow Result Result E1) E2 ->
  has_type empty t2 Keyset E3 ->
  value t1 ->
  value t2 ->
  exists x u ks, (ks = t_ks_nil \/ (exists k' ks', ks = t_ks_cons k' ks' /\ value k' /\ value ks')) /\ t = t_emit_ot_pmap l (t_abs x Result u) ks.
Proof using.
  intros t l t1 t2 Hteq HT1 HT2 HV1 HV2.
  inversion HV1; intros; subst; try inversion HT1; subst; auto; narrow_terms.
  inversion HV2; intros; subst; try inversion HT2; subst; auto; narrow_terms; try solve [exists x, t12, t_ks_nil; eauto].
  - apply canonical_forms_fun in HV2. destruct HV2 as [x [u]]; subst. exists x, u, (t_ks_cons k ks); eauto. split.
    right. exists k, ks. eauto. eauto. eauto.
  - apply canonical_forms_fun in HV2. destruct HV2 as [x [u]]; subst. exists x, u, t_ks_nil; eauto. assumption.
  - apply canonical_forms_fun in HV2. destruct HV2 as [x [u]]; subst. exists x, u, (t_ks_cons k ks); eauto. split.
    right. exists k, ks. eauto. eauto. eauto.
Qed.

Lemma frontend_agnostic :
  forall os rs t t',
  C [] [] rs t --> C [] os rs t' ->
  forall b os',
  C b os' rs t --> C b (os' ++ os) rs t'.
Proof using.
  intros os rs t t' H.
  inversion H; subst; intros; try solve [inv H3; simpl in *; eauto]; try solve [inv H2; simpl in *; eauto]; try solve [destruct b1; crush].
  - inv H5; simpl in *; eauto.
  - inv H4; simpl in *; eauto.
  - inv H3; simpl in *; eauto.
    apply S_Claim with (l:=l).
    + crush.
    + assumption.
  - inv H4. eauto.
  - inv H5. eauto.
  - inv H4. eauto.
  - inv H4. eauto.
  - inv H3. apply S_App with (T:=T); crush.
  - inv H4. eauto.
  - inv H4; eauto.
  - inv H4; eauto.
Qed.

Inductive dry_backend : backend -> Prop :=
| dry_backend_empty : dry_backend []
| dry_backend_cons : forall s b, dry_backend b -> value (get_payload (get_node s)) -> get_ostream s = [] -> dry_backend (s::b).
Hint Constructors dry_backend.
Inductive dry : config -> Prop :=
| dry_ : forall b rs v, dry_backend b -> value v -> dry (C b [] rs v).
Hint Constructors dry.

Lemma dry_backend_dist : forall b b1 b2,
  b = b1 ++ b2 ->
  dry_backend b ->
  dry_backend b1 /\ dry_backend b2.
Proof using.
  induction b; intros.
  - assert (b1 = []). destruct b1. destruct b2. eauto. inv H. inv H.
    assert (b2 = []). destruct b1. destruct b2. eauto. inv H. inv H.
    crush.
  - destruct b1; destruct b2; inv H.
    + split; eauto.
    + split; eauto.
      constructor; inv H0; crush.
    + split.
      constructor; inv H0; crush.
      * apply IHb with (b3:=b1) (b4:=s0::b2) in H2; eauto; crush.
      * inv H0. apply IHb with (b3:=b1) (b4:=s0::b2) in H2; eauto; crush.
Qed.

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

Axiom pfold_value : forall op f t ks,
  op = pfold f t ks ->
  value f.

Lemma frontend_into_load : forall t t' k os c b1 b2 os0 rs0 term0,
  C [] [] rs0 t --> C [] [] rs0 t' ->
  well_typed c ->
  c = C (b1 ++ <<N k t; os>>:: b2) os0 rs0 term0 ->
  exists c', c --> c'.
Proof using.
  induction t; intros; inversion H; subst; try solve [destruct os1; match goal with | [H : _ = [] |- _] => inv H end]; try solve [match goal with | [H : [] = _ |- _] => inv H end]; try solve [eapply ex_intro; eapply S_Load; eauto].
Qed.

Lemma frontend_into_loadpfold : forall t t1 t2 t3 t' l k os os' c b1 b2 os0 rs0 term0,
  C [] [] rs0 t2 --> C [] [] rs0 t' ->
  well_typed c ->
  c = C (b1 ++ <<N k t; os ++ l ->> pfold t1 t2 t3 :: os'>>:: b2) os0 rs0 term0 ->
  exists c', c --> c'.
Proof using.
  induction t; intros; inversion H; subst; try solve [destruct os1; match goal with | [H : _ = [] |- _] => inv H end]; try solve [match goal with | [H : [] = _ |- _] => inv H end]; try solve [eapply ex_intro; eapply S_LoadPFold; eauto].
Qed.

Inductive next_reduction : term -> term -> Prop :=
| nr_app1 : forall t1 t2 t1', not (value t1) -> next_reduction t1 t1' -> next_reduction (t_app t1 t2) t1'
| nr_app2 : forall t1 t2 t2', value t1 -> not (value t2) -> next_reduction t2 t2' -> next_reduction (t_app t1 t2) t2'
| nr_app : forall t1 t2, value t1 -> value t2 -> next_reduction (t_app t1 t2) (t_app t1 t2)
| nr_var : forall x, next_reduction (t_var x) (t_var x)
| nr_ks_cons1 : forall t1 t2 t1', not (value t1) -> next_reduction t1 t1' -> next_reduction (t_ks_cons t1 t2) t1'
| nr_ks_cons2 : forall t1 t2 t2', value t1 -> not (value t2) -> next_reduction t2 t2' -> next_reduction (t_ks_cons t1 t2) t2'
| nr_downarrow : forall t t', not (value t) -> next_reduction t t' -> next_reduction (t_downarrow t) t'
| nr_downarrow_claim : forall t, value t -> next_reduction (t_downarrow t) (t_downarrow t)
| nr_emit_ot_pfold1 : forall l t1 t2 t3 t', not (value t1) -> next_reduction t1 t' -> next_reduction (t_emit_ot_pfold l t1 t2 t3) t'
| nr_emit_ot_pfold2 : forall l t1 t2 t3 t', value t1 -> not (value t2) -> next_reduction t2 t' -> next_reduction (t_emit_ot_pfold l t1 t2 t3) t'
| nr_emit_ot_pfold3 : forall l t1 t2 t3 t', value t1 -> value t2 -> not (value t3) -> next_reduction t3 t' -> next_reduction (t_emit_ot_pfold l t1 t2 t3) t'
| nr_emit_ot_pfold : forall l t1 t2 t3, value t1 -> value t2 -> value t3 -> next_reduction (t_emit_ot_pfold l t1 t2 t3) (t_emit_ot_pfold l t1 t2 t3)
| nr_emit_ot_pmap1 : forall l t1 t2 t', not (value t1) -> next_reduction t1 t' -> next_reduction (t_emit_ot_pmap l t1 t2) t'
| nr_emit_ot_pmap2 : forall l t1 t2 t', value t1 -> not (value t2) -> next_reduction t2 t' -> next_reduction (t_emit_ot_pmap l t1 t2) t'
| nr_emit_ot_pmap : forall l t1 t2, value t1 -> value t2 -> next_reduction (t_emit_ot_pmap l t1 t2) (t_emit_ot_pmap l t1 t2)
| nr_emit_ot_add1 : forall l t1 t2 t', not (value t1) -> next_reduction t1 t' -> next_reduction (t_emit_ot_add l t1 t2) t'
| nr_emit_ot_add2 : forall l t1 t2 t', value t1 -> not (value t2) -> next_reduction t2 t' -> next_reduction (t_emit_ot_add l t1 t2) t'
| nr_emit_ot_add : forall l t1 t2, value t1 -> value t2 -> next_reduction (t_emit_ot_add l t1 t2) (t_emit_ot_add l t1 t2).
Hint Constructors next_reduction.

Lemma result_in_dec : forall rs l, (exists v, In (l ->>> v) rs) \/ (not (exists v, In (l ->>> v) rs)).
Proof using.
  induction rs; intros.
  - right; crush.
  - destruct IHrs with (l:=l).
    + left. destruct H. exists x. crush.
    + destruct a.
      destruct (Nat.eq_dec n l).
      * subst. left. exists n0. crush.
      * right. intro.
        destruct H0.
        apply List.in_inv in H0.
        {
        destruct H0.
        - crush.
        - apply H. exists x. crush.
        }
Qed.

Ltac find_type := match goal with
                 | [H : has_type _ _ _ _ |- _] => inv H; eauto
                 | [H : config_has_type _ _ _ |- _] => inv H; find_type
                 end.
Ltac easy_wt := inversion WT; split; try split; crush; find_type.

Lemma next_reduction_to_reduction :
  forall t t' rs0,
  well_typed (C [] [] rs0 t) ->
  next_reduction t t' ->
  (exists t'' os, C [] [] rs0 t --> C [] os rs0 t'') \/ (exists l, t' = t_downarrow (t_label l) /\ not (exists v, In (l ->>> v) rs0)).
Proof using.
  intros t t' rs0 WT NR.
  induction NR; subst.
  - destruct IHNR; [| left; destruct H0 as [t''[os]] | destruct H0 as [l]; destruct H0; right; eauto].
    + easy_wt.
    + eapply ex_intro; eapply ex_intro; eapply S_App1; eauto.
  - destruct IHNR as [HH|HH]; [| left; destruct HH as [t''[os]] | destruct HH as [l HH]; destruct HH; right; eauto].
    + easy_wt.
    + eapply ex_intro; eapply ex_intro; eapply S_App2; eauto; find_type.
  - inversion WT. destruct H3 as [T [b]]. inv H3. inv H13.
    apply canonical_forms_fun in H6. destruct H6. destruct H3. subst.
    left. eapply ex_intro; eapply ex_intro; eapply S_App; eauto. assumption.
  - inversion WT. destruct H1 as [T [b]]. find_type; narrow_terms.
  - destruct IHNR as [HH|HH]; [| left; destruct HH as [t''[os]] | destruct HH as [l HH]; destruct HH; right; eauto].
    + easy_wt.
    + eapply ex_intro; eapply ex_intro; eapply S_KS1; eauto.
  - destruct IHNR as [HH|HH]; [| left; destruct HH as [t''[os]] | destruct HH as [l HH]; destruct HH; right; eauto].
    + easy_wt.
    + eapply ex_intro; eapply ex_intro; eapply S_KS2; eauto.
  - destruct IHNR as [HH|HH]; [| left; destruct HH as [t''[os]] | destruct HH as [l HH]; destruct HH; right; eauto].
    + easy_wt.
    + eapply ex_intro; eapply ex_intro; eapply S_Ctx_Downarrow; eauto.
  - inversion WT. destruct H2 as [T [b]]. inv H2. inv H12. destruct t; try solve [inv H]; try solve [inv H4].
    rename n into l.
    destruct (result_in_dec rs0 l).
    + destruct H2. eauto.
    + right. eauto.
  - destruct IHNR as [HH|HH]; [| left; destruct HH as [t''[os]] | destruct HH as [l' HH]; destruct HH; right; eauto].
    + inversion WT; split; try split; crush. inversion H2; eauto; find_type.
    + eapply ex_intro; eapply ex_intro; eapply S_Ctx_Emit_OT_PFold1; eauto.
  - destruct IHNR as [HH|HH]; [| left; destruct HH as [t''[os]] | destruct HH as [l' HH]; destruct HH; right; eauto].
    + inversion WT; split; try split; crush. inversion H3; eauto; find_type.
    + eapply ex_intro; eapply ex_intro; eapply S_Ctx_Emit_OT_PFold2; eauto.
  - destruct IHNR as [HH|HH]; [| left; destruct HH as [t''[os]] | destruct HH as [l' HH]; destruct HH; right; eauto].
    + inversion WT; split; try split; crush. inversion H4; eauto; find_type.
    + eapply ex_intro; eapply ex_intro; eapply S_Ctx_Emit_OT_PFold3; eauto.
  - eauto.
  - destruct IHNR as [HH|HH]; [| left; destruct HH as [t''[os]] | destruct HH as [l' HH]; destruct HH; right; eauto].
    + inversion WT; split; try split; crush. inversion H2; eauto; find_type.
    + eapply ex_intro; eapply ex_intro; eapply S_Ctx_Emit_OT_PMap1; eauto.
  - destruct IHNR as [HH|HH]; [| left; destruct HH as [t''[os]] | destruct HH as [l' HH]; destruct HH; right; eauto].
    + inversion WT; split; try split; crush. inversion H3; eauto; find_type.
    + eapply ex_intro; eapply ex_intro; eapply S_Ctx_Emit_OT_PMap2; eauto.
  - eauto.
  - destruct IHNR as [HH|HH]; [| left; destruct HH as [t''[os]] | destruct HH as [l' HH]; destruct HH; right; eauto].
    + inversion WT; split; try split; crush. inversion H2; eauto; find_type.
    + eapply ex_intro; eapply ex_intro; eapply S_Ctx_Emit_OT_Add1; eauto.
  - destruct IHNR as [HH|HH]; [| left; destruct HH as [t''[os]] | destruct HH as [l' HH]; destruct HH; right; eauto].
    + inversion WT; split; try split; crush. inversion H3; eauto; find_type.
    + eapply ex_intro; eapply ex_intro; eapply S_Ctx_Emit_OT_Add2; eauto.
  - inversion WT.
    destruct H3 as [T [b]]. find_type; narrow_terms.
    destruct t1; find_type; narrow_terms.
Qed.

Lemma term_to_next_reduction :
  forall t, well_typed (C [] [] [] t) -> not (value t) -> exists t', next_reduction t t'.
Proof using.
  induction t; intros WT; intros; eauto.
  - destruct (value_dec t1); destruct (value_dec t2); eauto.
    + remember H1. clear Heqn. apply IHt2 in H1. destruct H1. eauto. easy_wt.
    + remember H0. clear Heqn. apply IHt1 in H0. destruct H0. eauto. easy_wt.
    + remember H0. clear Heqn. apply IHt1 in H0. destruct H0. eauto. easy_wt.
  - crush.
  - crush.
  - crush.
  - crush.
  - destruct (value_dec t1); destruct (value_dec t2).
    + assert (value (t_ks_cons t1 t2)) by eauto; crush.
    + remember H1. clear Heqn. apply IHt2 in H1. destruct H1. eauto. easy_wt.
    + remember H0. clear Heqn. apply IHt1 in H0. destruct H0. eauto. easy_wt.
    + remember H0. clear Heqn. apply IHt1 in H0. destruct H0. eauto. easy_wt.
  - destruct (value_dec t).
    + assert (exists l, t = t_label l).
      {
        inversion WT.
        destruct H3 as [T [b]]. find_type; narrow_terms.
        eauto.
      }
      destruct H1. eauto.
    + remember H0. clear Heqn. apply IHt in H0. destruct H0. eauto. easy_wt.
  - destruct (value_dec t1).
    + destruct (value_dec t2).
      * {
        destruct (value_dec t3).
        - eauto.
        - remember H2. clear Heqn0. apply IHt3 in H2. destruct H2. eauto. easy_wt.
        }
      * remember H1. clear Heqn0. apply IHt2 in H1. destruct H1. eauto. easy_wt.
    + remember H0. clear Heqn0. apply IHt1 in H0. destruct H0. eauto. easy_wt.
  - destruct (value_dec t1).
    + destruct (value_dec t2).
      * eauto.
      * remember H1. clear Heqn0. apply IHt2 in H1. destruct H1. eauto. easy_wt.
    + remember H0. clear Heqn0. apply IHt1 in H0. destruct H0. eauto. easy_wt.
  - destruct (value_dec t1).
    + destruct (value_dec t2).
      * eauto.
      * remember H1. clear Heqn0. apply IHt2 in H1. destruct H1. eauto. easy_wt.
    + remember H0. clear Heqn0. apply IHt1 in H0. destruct H0. eauto. easy_wt.
Qed.

(* TODO require that t is found inside the graph *)
Axiom emittability : forall t t' os' rs0,
  C [] [] rs0 t --> C [] os' rs0 t' ->
  os' = [].

Axiom dependent_loadpfold_after : forall l' l c b1 b2 t1 t2 t3 n os os' os0 rs0 term0,
  c = C (b1 ++ <<n; os ++ l' ->> pfold t1 t2 t3 :: os'>> :: b2) os0 rs0 term0 ->
  next_reduction t2 (t_downarrow (t_label l)) ->
  well_typed c ->
  (exists v, In (l ->>> v) rs0) \/ (exists n' op b2' b2'' os'', b2 = b2' ++ <<n'; os''>> :: b2'' /\ In (l ->> op) os).

Lemma op_reduction_exists : forall c b b1 b2 rs0 os0 term0 k t os l op,
  well_typed c ->
  c = C b os0 rs0 term0 ->
  b = b1 ++ <<N k t; l ->> op :: os>> :: b2 ->
  exists c', C b os0 rs0 term0 --> c'.
Proof using.
  intros c b b1 b2 rs0 os0 term0 k t os l op WT Hceq Hbeq.
  destruct op; subst.
  - destruct (List.in_dec Nat.eq_dec k l0).
    + eapply ex_intro; eapply S_PMap; eauto.
    + destruct b2.
      * eapply ex_intro; eapply S_Last; eauto.
      * destruct s. eapply ex_intro; eapply S_Prop; eauto; crush.
  - destruct b2.
    + eapply ex_intro; eapply S_Last; eauto.
    + destruct s. eapply ex_intro; eapply S_Prop; eauto; crush.
  - destruct (List.in_dec Nat.eq_dec k l0).
    + eapply ex_intro; eapply S_PFold; eauto.
      Unshelve.
      auto.
      auto.
    + destruct b2.
      * {
        destruct (value_dec t1).
        - assert (has_type empty t1 Result false) by (eapply graph_typing'; eauto).
          destruct t1; try solve [inv H]; try solve [inv H0].
          eapply ex_intro; eapply S_Last; eauto.
          - rename H into HNV. apply term_to_next_reduction in HNV.
            + destruct HNV. remember H. clear Heqn0. rename n0 into NR. apply next_reduction_to_reduction with (rs0:=rs0) in H.
              * {
                destruct H.
                - destruct H as [t''[os']].
                  assert (os'=[]) by (eapply emittability; eauto). subst.
                  eapply frontend_into_loadpfold with (t1:=t0) (t':=t'') (rs0:=rs0) (b2:=[]) (os:=[]); simpl; eauto.
                  Unshelve.
                  auto.
                  auto.
                  right; eauto.
                - destruct H as [l']. destruct H. subst.
                  destruct all_labels with (c:=C (b1 ++ [<< N k t; l ->> pfold t0 t1 l0 :: os >>]) os0 rs0 term0) (l:=l').
                  + eauto.
                  + exfalso; eauto.
                  + destruct H as [op [b2 [s [b3]]]]. simpl in *. destruct H.
                    edestruct dependent_loadpfold_after with (c:=C (b1 ++ [<< N k t; l ->> pfold t0 t1 l0 :: os >>]) os0 rs0 term0).
                    * instantiate (4:=[]).
                      instantiate (9:=[]).
                      simpl; eauto.
                    * instantiate (1:=l'). assumption.
                    * assumption.
                    * exfalso; eauto.
                    * destruct H2 as [n' [op' [b2' [b2'' [os'']]]]].
                      destruct H2.
                      exfalso; eauto.
                }
              * inversion WT; split; try split; crush.
                apply distinct_concat in H1.
                destruct H1.
                inv H3.
                assert (ostream_labels os = []) by (destruct os; crush). rewrite H3 in *. simpl in *.
                assert (ostream_labels os0 = []) by (destruct os0; crush). rewrite H4 in *. simpl in *.
                rewrite <- H6. eauto.
                inv H4.
                apply distinct_concat in H6.
                destruct H6.
                apply distinct_concat in H4.
                crush.
                assert (has_type empty t1 Result false) by (eapply graph_typing'; eauto).
                eauto.
            + inversion WT; split; try split; crush.
              assert (has_type empty t1 Result false) by (eapply graph_typing'; eauto).
              eauto.
        }
      * destruct s. eapply ex_intro; eapply S_Prop; eauto; crush.
Unshelve.
auto.
auto.
auto.
auto.
Qed.

Lemma load_exists : forall c b b1 b2 rs0 os0 term0 k t os,
  well_typed c ->
  c = C b os0 rs0 term0 ->
  b = b1 ++ <<N k t; os>> :: b2 ->
  not (value t) ->
  exists c', C b os0 rs0 term0 --> c'.
Proof using.
  intros c b b1 b2 rs0 os0 term0 k t os WT Hceq Hbeq HNV.
  assert (has_type empty t Result false) by (eapply graph_typing; eauto).
  destruct t; try solve [inv H; inv H2].
  - apply term_to_next_reduction in HNV.
    + destruct HNV. remember H0. clear Heqn. rename n into NR. apply next_reduction_to_reduction with (rs0:=rs0) in H0.
      * {
        destruct H0.
        - destruct H0 as [t''[os']].
          assert (os'=[]) by (eapply emittability; eauto). subst.
          eapply frontend_into_load with (t:=(t_app t1 t2)) (t':=t'') (rs0:=rs0); eauto.
        - destruct H0 as [l]. destruct H0. subst.
          destruct all_labels with (c:=C (b1 ++ << N k (t_app t1 t2); os >> :: b2) os0 rs0 term0) (l:=l); eauto.
          + destruct H0. simpl in *. exfalso. apply H1. eauto.
          + destruct H0 as [op [b3 [s [b4]]]]. destruct H0. destruct s. simpl in *.
            apply List.in_split in H2. destruct H2. destruct H2. subst.
            destruct x; simpl in *.
            * destruct n. eapply op_reduction_exists; eauto.
            * destruct l0. rewrite H0. destruct n. eapply op_reduction_exists; eauto.
              crush.
        }
      * inversion WT; split; try split; crush; eauto.
        apply distinct_concat in H2.
        destruct H2.
        apply distinct_concat in H4.
        destruct H4.
        apply distinct_concat in H5.
        crush.
    + inversion WT; split; try split; crush; eauto.
  - assert (value (t_result n)) by crush.
    exfalso; apply HNV; eauto.
  - apply term_to_next_reduction in HNV.
    + destruct HNV. remember H0. clear Heqn. rename n into NR. apply next_reduction_to_reduction with (rs0:=rs0) in H0.
      * {
        destruct H0.
        - destruct H0 as [t''[os']].
          assert (os'=[]) by (eapply emittability; eauto). subst.
          eapply frontend_into_load with (t:=t_downarrow t) (t':=t'') (rs0:=rs0); eauto.
        - destruct H0 as [l]. destruct H0. subst.
          destruct all_labels with (c:=C (b1 ++ << N k (t_downarrow t); os >> :: b2) os0 rs0 term0) (l:=l); eauto.
          + destruct H0. simpl in *. exfalso. apply H1. eauto.
          + destruct H0 as [op [b3 [s [b4]]]]. destruct H0. destruct s. simpl in *.
            apply List.in_split in H2. destruct H2. destruct H2. subst.
            destruct x; simpl in *.
            * destruct n. eapply op_reduction_exists; eauto.
            * destruct l0. rewrite H0. destruct n. eapply op_reduction_exists; eauto.
              crush.
        }
      * inversion WT; split; try split; crush; eauto.
        apply distinct_concat in H2.
        destruct H2.
        apply distinct_concat in H4.
        destruct H4.
        apply distinct_concat in H5.
        crush.
    + inversion WT; split; try split; crush; eauto.
Unshelve.
auto.
Qed.

Lemma cht_app1 : forall b os rs t1 t2 T E,
  config_has_type (C b os rs (t_app t1 t2)) T E ->
  exists T' E', config_has_type (C b os rs t1) T' E'.
Proof using.
  intros. inv H. inv H8. eauto.
Qed.
Hint Resolve cht_app1.

Lemma cht_app2 : forall b os rs t1 t2 T E,
  config_has_type (C b os rs (t_app t1 t2)) T E ->
  exists T' E', config_has_type (C b os rs t2) T' E'.
Proof using.
  intros. inv H. inv H8. eauto.
Qed.
Hint Resolve cht_app2.

Lemma cht_ks1 : forall b os rs t1 t2 T E,
  config_has_type (C b os rs (t_ks_cons t1 t2)) T E ->
  exists T' E', config_has_type (C b os rs t1) T' E'.
Proof using.
  intros. inv H. inv H8. eauto.
Qed.
Hint Resolve cht_ks1.

Lemma cht_ks2 : forall b os rs t1 t2 T E,
  config_has_type (C b os rs (t_ks_cons t1 t2)) T E ->
  exists T' E', config_has_type (C b os rs t2) T' E'.
Proof using.
  intros. inv H. inv H8. eauto.
Qed.
Hint Resolve cht_ks2.

Lemma cht_downarrow : forall b os rs t T E,
  config_has_type (C b os rs (t_downarrow t)) T E ->
  exists T' E', config_has_type (C b os rs t) T' E'.
Proof using.
  intros. inv H. inv H8. eauto.
Qed.
Hint Resolve cht_downarrow.

Lemma cht_pfold1 : forall b os rs l t1 t2 t3 T E,
  config_has_type (C b os rs (t_emit_ot_pfold l t1 t2 t3)) T E ->
  exists T' E', config_has_type (C b os rs t1) T' E'.
Proof using.
  intros. inv H. inv H8. eauto.
Qed.
Hint Resolve cht_pfold1.

Lemma cht_pfold2 : forall b os rs l t1 t2 t3 T E,
  config_has_type (C b os rs (t_emit_ot_pfold l t1 t2 t3)) T E ->
  exists T' E', config_has_type (C b os rs t2) T' E'.
Proof using.
  intros. inv H. inv H8. eauto.
Qed.
Hint Resolve cht_pfold2.

Lemma cht_pfold3 : forall b os rs l t1 t2 t3 T E,
  config_has_type (C b os rs (t_emit_ot_pfold l t1 t2 t3)) T E ->
  exists T' E', config_has_type (C b os rs t3) T' E'.
Proof using.
  intros. inv H. inv H8. eauto.
Qed.
Hint Resolve cht_pfold3.

Lemma cht_pmap1 : forall b os rs l t1 t2 T E,
  config_has_type (C b os rs (t_emit_ot_pmap l t1 t2)) T E ->
  exists T' E', config_has_type (C b os rs t1) T' E'.
Proof using.
  intros. inv H. inv H8. eauto.
Qed.
Hint Resolve cht_pmap1.

Lemma cht_pmap2 : forall b os rs l t1 t2 T E,
  config_has_type (C b os rs (t_emit_ot_pmap l t1 t2)) T E ->
  exists T' E', config_has_type (C b os rs t2) T' E'.
Proof using.
  intros. inv H. inv H8. eauto.
Qed.
Hint Resolve cht_pmap2.

Lemma cht_add1 : forall b os rs l t1 t2 T E,
  config_has_type (C b os rs (t_emit_ot_add l t1 t2)) T E ->
  exists T' E', config_has_type (C b os rs t1) T' E'.
Proof using.
  intros. inv H. inv H8. eauto.
Qed.
Hint Resolve cht_add1.

Lemma cht_add2 : forall b os rs l t1 t2 T E,
  config_has_type (C b os rs (t_emit_ot_add l t1 t2)) T E ->
  exists T' E', config_has_type (C b os rs t2) T' E'.
Proof using.
  intros. inv H. inv H8. eauto.
Qed.
Hint Resolve cht_add2.

Theorem progress : forall b os rs t,
  well_typed (C b os rs t) ->
  value t \/ exists c', (C b os rs t) --> c'.
Proof with eauto.
  intros b os rs t WT.
  inversion WT. destruct H1 as [T [E]]. rename H1 into ET. rename H into Hdk. rename H0 into Hdl. subst c. inv ET. clear H5 H6. rename H7 into ET.
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
      * remember WT as WT'.
        clear HeqWT'.
        apply all_labels with (l:=label) in WT.
        {
        destruct WT.
        - destruct H0.
          eauto.
        - destruct H0. destruct H0. destruct H0. destruct H0. destruct H0.
          simpl in *.
          destruct x1.
          simpl in *.
          destruct l.
          + crush.
          + destruct l.
            destruct n.
            eapply op_reduction_exists with (b1:=x0) (b2:=x2); eauto.
        }
    + right.
      destruct H.
      destruct x.
      inversion H; ssame; eauto.
  - right. destruct IHET1...
    + inversion WT. split; crush; eauto.
    + destruct IHET2...
      * inversion WT. split; crush; eauto.
      * {
        destruct IHET3...
        - inversion WT. split; crush; eauto.
        - destruct H1. inversion H1; ssame; eauto.
        }
      * destruct H0. inversion H0; ssame; eauto.
    + destruct H. inversion H; ssame; eauto.
  - right. destruct IHET1...
    + inversion WT. split; crush; eauto.
    + destruct IHET2...
      * inversion WT. split; crush; eauto.
      * destruct H0. inversion H0; ssame; eauto.
    + destruct H.
      inversion H; ssame; eauto.
  - right. destruct IHET1...
    + inversion WT. split; crush; eauto.
    + destruct IHET2...
      * inversion WT. split; crush; eauto.
      * destruct t1; try solve [inv ET1; inv H3]; try solve [inv H].
        destruct t2; try solve [inv ET2; inv H3]; try solve [inv H0].
        eauto.
      * destruct H0. inversion H0; ssame; eauto.
    + destruct H.
      inversion H; ssame; eauto.
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

Axiom waiting_fold_value : forall c b os os' rs l t t1 t2 t3,
  c = C b os rs t ->
  well_typed c ->
  os = l ->> pfold t1 t2 t3 :: os' ->
  value t2.

Lemma cht_tail : forall a b os rs t T E,
  config_has_type (C (a :: b) os rs t) T E ->
  exists T' E', config_has_type (C b os rs t) T' E'.
Proof using.
  intros. inv H. exists T, E. constructor; eauto.
  inv H6; eauto.
Qed.
Hint Resolve cht_tail.

Lemma app_empty :
  forall {A : Type} (xs : list A) ys,
  [] = xs ++ ys -> xs = [] /\ ys = [].
Proof using.
  induction xs; crush.
Qed.

Lemma app_empty' :
  forall {A : Type} (xs : list A) ys,
  xs ++ ys = [] -> xs = [] /\ ys = [].
Proof using.
  induction xs; crush.
Qed.

Lemma wt_cons : forall b a,
  well_typed_backend (a :: b) ->
  well_typed_backend b.
Proof using.
  intros.
  inv H.
  assumption.
Qed.
Hint Resolve wt_cons.

Lemma dck_cons : forall a b os rs t,
  distinct (config_keys (C (a :: b) os rs t)) ->
  distinct (config_keys (C b os rs t)).
Proof using.
  intros.
  unfold config_keys in *.
  simpl in H.
  rewrite cons_app in H.
  apply distinct_concat in H.
  crush.
Qed.
Hint Resolve dck_cons.

Lemma dcl_cons : forall a b os rs t,
  distinct (config_labels (C (a :: b) os rs t)) ->
  distinct (config_labels (C b os rs t)).
Proof using.
  intros.
  unfold config_labels in *.
  simpl in H.
  unfold backend_labels in H.
  simpl in H.
  rewrite <- List.app_assoc in H.
  apply distinct_concat in H.
  crush.
Qed.
Hint Resolve dcl_cons.

Theorem progress' : forall b os rs t,
  well_typed (C b os rs t) ->
  dry (C b os rs t) \/ exists c', (C b os rs t) --> c'.
Proof using.
  intros b os rs t WT.
  inversion WT. subst c. destruct H1 as [T [E]]. rename H into Hdk; rename H0 into Hdl. inv H1. rename H6 into Hwtb. rename H7 into Hwtto. rename H8 into ET.
  remember WT as WT'. clear HeqWT'. apply progress with (b:=b) (os:=os) (rs:=rs) in WT'.
  destruct WT'.
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
          - find_type.
          - eapply dck_cons; eauto.
          - eapply dcl_cons; eauto.
          - inv Hwtb; eauto.
        }
        destruct a as [n os].
        + destruct os.
          * {
            destruct H0.
            - destruct n.
              destruct (value_dec t0).
              + left.
                constructor; eauto.
                constructor; eauto.
                inv H0; eauto.
              + right.
                remember WT. clear Heqw.
                eapply load_exists with (os:=[]) (b1:=[]) (b2:=b) (k:=n) (rs0:=rs) (t:=t0) in w; eauto.
            - right.
              destruct H0.
              inversion H0; ssame; try solve [match goal with | [H : value _ |- _] => inv H end].
              + eapply ex_intro; eauto.
              + eapply ex_intro; eauto.
              + eapply ex_intro; eauto.
              + eapply ex_intro; eauto.
              + eapply ex_intro; eauto.
              + eapply ex_intro; eauto.
              + eapply ex_intro; eauto.
              + eapply ex_intro; eauto.
              + eapply ex_intro; eauto.
              + eapply ex_intro; eauto.
              + eapply ex_intro; eapply S_PMap; eauto; crush.
              + eapply ex_intro; eapply S_PFold; eauto; crush.
              + eapply ex_intro; eapply S_Last; eauto; crush.
                Unshelve.
                auto.
              + eapply ex_intro; eapply S_FusePMap; eauto; crush.
                Unshelve.
                auto.
              + eapply ex_intro; eapply S_Prop; eauto; crush.
              + eapply ex_intro; eapply S_Load; eauto; crush.
              + eapply ex_intro; eapply S_LoadPFold; eauto; crush.
            }
          * right.
            destruct l as [l op].
            destruct n.
            eapply op_reduction_exists with (b1:=[]); eauto.
            crush.
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
            Unshelve.
            auto.
            auto.
            assert (value t1) by (eapply waiting_fold_value; eauto).
            assert (has_type empty t1 Result false) by (eapply graph_typing'; eauto).
            destruct t1; try solve [inv H; inv H4]; try solve [inv H0]; try solve [inv H1].
            right. eauto.
          + destruct s; eapply ex_intro; eapply S_First; eauto; crush.
        }
  - right. assumption.
Unshelve.
auto.
auto.
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
| afi_emit_ot_getpay1 : forall x l t1 t2 t3,
    appears_free_in x t1 ->
    appears_free_in x (t_emit_ot_pfold l t1 t2 t3)
| afi_emit_ot_getpay2 : forall x l t1 t2 t3,
    appears_free_in x t2 ->
    appears_free_in x (t_emit_ot_pfold l t1 t2 t3)
| afi_emit_ot_getpay3 : forall x l t1 t2 t3,
    appears_free_in x t3 ->
    appears_free_in x (t_emit_ot_pfold l t1 t2 t3)
| afi_emit_ot_pmap1 : forall x l t1 t2,
    appears_free_in x t1 ->
    appears_free_in x (t_emit_ot_pmap l t1 t2)
| afi_emit_ot_pmap2 : forall x l t1 t2,
    appears_free_in x t2 ->
    appears_free_in x (t_emit_ot_pmap l t1 t2)
| afi_emit_ot_add1 : forall x l t1 t2,
    appears_free_in x t1 ->
    appears_free_in x (t_emit_ot_add l t1 t2)
| afi_emit_ot_add2 : forall x l t1 t2,
    appears_free_in x t2 ->
    appears_free_in x (t_emit_ot_add l t1 t2).
Hint Constructors appears_free_in.

Definition closed (t:term) :=
  forall x, ~ appears_free_in x t.

Lemma free_in_context : forall x t T E Gamma,
   appears_free_in x t ->
   has_type Gamma t T E ->
   exists T', Gamma x = Some T'.
Proof using.
  intros x t T E Gamma H H0. generalize dependent Gamma.
  generalize dependent T.
  generalize dependent E.
  induction H;
         intros; try solve [inversion H0; eauto].
  - (* afi_abs *)
    inversion H1; subst.
    apply IHappears_free_in in H8.
    rewrite update_neq in H8; assumption.
Qed.

Corollary typable_empty__closed : forall t T E,
    has_type empty t T E ->
    closed t.
Proof using.
  unfold closed. intros. intro.
  eapply free_in_context with (Gamma:=empty) in H0.
  destruct H0.
  inv H0.
  eauto.
Qed.

Lemma context_invariance : forall Gamma Gamma' t T E,
     has_type Gamma t T E ->
     (forall x, appears_free_in x t -> Gamma x = Gamma' x) ->
     has_type Gamma' t T E.
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
  - eapply T_Emit_OT_PFold; eauto.
  - eapply T_Emit_OT_PMap; eauto.
  - eapply T_Emit_OT_Add; eauto.
Qed.

Lemma value_no_emit : forall v Gamma T E,
  has_type Gamma v T E ->
  value v ->
  E = false.
Proof using.
  induction v; intros; try solve [inv H0]; try solve [inv H; eauto]; eauto.
  inv H0. inv H. apply IHv1 in H5; auto. apply IHv2 in H8; auto. subst. auto.
Qed.

Lemma substitution_preserves_typing : forall Gamma x U t v T E1,
  has_type (x |-> U ; Gamma) t T E1 ->
  has_type empty v U false ->
  has_type Gamma (#[x:=v]t) T E1.
Proof with eauto.
  intros Gamma x U t v T E1 Ht Ht'.
  generalize dependent Gamma. generalize dependent T. generalize dependent E1. generalize dependent Ht'.
  induction t; intros Ht' E1 T Gamma H;
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
      subst. rewrite update_shadow in H6. apply H6.
    + (* x<>y *)
      apply IHt. assumption. eapply context_invariance...
      intros z Hafi. unfold update, t_update.
      destruct (eqb_stringP y z) as [Hyz | Hyz]; subst; trivial.
      rewrite <- eqb_string_false_iff in Hxy.
      rewrite Hxy...
Qed.

Lemma wtto_cons : forall lop os,
  well_typed_top_ostream (lop :: os) ->
  well_typed_top_ostream os.
Proof using.
  intros. inv H. eauto.
Qed.
Hint Resolve wtto_cons.

Lemma well_typed_backend_dist' : forall b b',
  well_typed_backend (b ++ b') ->
  well_typed_backend b /\ well_typed_backend b'.
Proof using.
  induction b; intros.
  - crush.
  - simpl in *. inv H. apply IHb in H4. destruct H4. crush.
Qed.
Hint Resolve well_typed_backend_dist'.

Lemma well_typed_backend_dist : forall b b',
  well_typed_backend b ->
  well_typed_backend b' ->
  well_typed_backend (b ++ b').
Proof using.
  induction b; intros.
  - eauto.
  - simpl; destruct a. destruct n; constructor; inv H; eauto.
Unshelve.
auto.
Qed.
Hint Resolve well_typed_backend_dist.

Lemma well_typed_top_ostream_dist : forall os os',
  well_typed_top_ostream os ->
  well_typed_top_ostream os' ->
  well_typed_top_ostream (os ++ os').
Proof using.
  induction os; intros.
  - eauto.
  - simpl; destruct a; destruct o; constructor; inv H; eauto.
Qed.
Hint Resolve well_typed_top_ostream_dist.

Lemma well_typed_ostream_dist' : forall os os',
  well_typed_ostream (os ++ os') ->
  well_typed_ostream os /\ well_typed_ostream os'.
Proof using.
  induction os; intros.
  - eauto.
  - simpl in *; destruct a; destruct o; constructor; inv H; eauto;
    try solve [constructor; eauto; apply IHos in H2; crush];
    try solve [apply IHos in H2; crush].
Qed.
Hint Resolve well_typed_ostream_dist'.

Lemma well_typed_ostream_dist : forall os os',
  well_typed_ostream os ->
  well_typed_ostream os' ->
  well_typed_ostream (os ++ os').
Proof using.
  induction os; intros.
  - eauto.
  - simpl; destruct a; destruct o; constructor; inv H; eauto.
Qed.
Hint Resolve well_typed_ostream_dist.

Lemma emit_well_typed_top_ostream : forall t os rs t' T E,
  config_has_type (C [] [] rs t) T E ->
  C [] [] rs t --> C [] os rs t' ->
  well_typed_top_ostream os.
Proof using.
  induction t; intros;
  rename H into HT;
  inversion HT; subst;
  inv H8.
  - inv H2.
  - inversion H0; ssame; try solve [eauto].
  - exfalso; eapply frontend_no_value'; eauto.
  - exfalso; eapply frontend_no_value'; eauto.
  - exfalso; eapply frontend_no_value'; eauto.
  - exfalso; eapply frontend_no_value'; eauto.
  - inversion H0; ssame; try solve [eauto].
  - inversion H0; ssame; try solve [eauto].
  - inversion H0; ssame; try solve [eauto].
    + constructor. destruct t; try solve [inv H11]; try solve [inv H9].
      * eauto.
      * eauto.
      * assert (E1 = false) by (eapply value_no_emit; eauto); subst.
        assert (E2 = false) by (eapply value_no_emit; eauto); subst.
        eauto.
  - inversion H0; ssame; try solve [eauto].
    + assert (E1 = false) by (eapply value_no_emit; eauto); subst.
      constructor; eauto.
  - inversion H0; ssame; try solve [eauto].
Qed.
Hint Resolve emit_well_typed_top_ostream.

Lemma wt_btop_cons : forall n os os0 op b l,
  well_typed_backend (<<n; os>> :: b) ->
  well_typed_top_ostream (l ->> op :: os0) ->
  well_typed_backend (<<n; os ++ [l ->> op]>> :: b).
Proof using.
  intros.
  inv H.
  inv H0.
  destruct op; eauto.
Qed.
Hint Resolve wt_btop_cons.

Lemma wt_top_to_ht1 : forall l k v os,
  well_typed_top_ostream (l ->> add k v :: os) ->
  has_type empty v Result false.
Proof using.
  intros. inv H. inv H5. auto.
Qed.
Hint Resolve wt_top_to_ht1.

Lemma wt_to_wt1 : forall b1 k v l f ks os b2,
  well_typed_backend (b1 ++ << N k v; l ->> pmap f ks :: os >> :: b2) ->
  well_typed_backend (b1 ++ << N k (t_app f v); l ->> pmap f (remove Nat.eq_dec k ks) :: os >> :: b2).
Proof using.
  intros.
  apply well_typed_backend_dist' in H.
  destruct H.
  apply well_typed_backend_dist; eauto.
  inv H0.
  inv H6.
  inv H5.
  constructor; eauto.
  - remember H6. clear Heqh. apply canonical_forms_fun in H6; eauto. destruct H6 as [x[u]]; subst.
    assert (false = false || false || false)%bool by crush.
    rewrite H0.
    eapply T_App with Result.
    constructor.
    inv h.
    auto.
    auto.
Qed.
Hint Resolve wt_to_wt1.

Lemma wt_to_wt2 : forall b1 k t l f t' ks os b2,
  well_typed_backend (b1 ++ << N k t; l ->> pfold f t' ks :: os >> :: b2) ->
  well_typed_backend (b1 ++ << N k t; l ->> pfold f (t_app (t_app f t) t') (remove Nat.eq_dec k ks) :: os >> :: b2).
Proof using.
  intros.
  apply well_typed_backend_dist' in H.
  destruct H.
  apply well_typed_backend_dist; eauto.
  inv H0.
  inv H6.
  inv H5.
  constructor; eauto.
  - remember H8. clear Heqh. apply canonical_forms_fun in H8; eauto. destruct H8 as [x[u]]; subst.
    constructor; eauto.
    constructor; eauto.
    assert (false = false || false || false)%bool by crush.
    rewrite H0.
    eapply T_App with Result.
    rewrite H0.
    eapply T_App with Result.
    constructor.
    inv h.
    auto.
    auto.
    auto.
Qed.
Hint Resolve wt_to_wt2.

Lemma wt_to_wt3 : forall b n l op os,
  well_typed_backend (b ++ [<< n; l ->> op :: os >>]) ->
  well_typed_backend (b ++ [<< n; os >>]).
Proof using.
  intros.
  apply well_typed_backend_dist' in H.
  destruct H.
  apply well_typed_backend_dist; eauto.
  inv H0.
  inv H6.
  inv H5.
  constructor; eauto.
Qed.
Hint Resolve wt_to_wt3.

Lemma wt_to_wt4 : forall b1 n os l f l' f' ks os' b2,
  well_typed_backend (b1 ++ << n; os ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os' >> :: b2) ->
  well_typed_backend (b1 ++ << n; os ++ l ->> pmap (pmap_compose f' f) ks :: os' >> :: b2).
Proof using.
  intros; apply well_typed_backend_dist' in H; destruct H; apply well_typed_backend_dist; eauto.
  inv H0.
  eapply well_typed_ostream_dist' in H5. destruct H5.
  constructor; eauto.
  apply well_typed_ostream_dist; eauto.
  constructor; eauto. inv H1. inv H5. auto.
  inv H1.
  inv H8.
  inv H5.
  inv H10.
  remember H7. clear Heqh. apply canonical_forms_fun in H7; auto. destruct H7 as [x[u]]; subst.
  remember h as h''. clear Heqh''.
  inv h.
  constructor; eauto.
  unfold pmap_compose; auto.
  unfold pmap_compose.
  constructor.
  assert (false = false || false || false)%bool by crush.
  rewrite H1 at 9.
  eapply T_App with Result.
  rewrite H1 at 6.
  remember H9. clear Heqh. apply canonical_forms_fun in H9. destruct H9 as [x'[u']]. subst.
  apply context_invariance with empty; eauto.
  intros.
  apply typable_empty__closed in h.
  unfold closed in h.
  destruct h with x0.
  auto.
  auto.
  rewrite H1 at 9.
  eapply T_App with Result.
  apply context_invariance with empty; eauto.
  intros.
  apply typable_empty__closed in h''.
  unfold closed in h''.
  destruct h'' with x0.
  assumption.
  auto.
Qed.
Hint Resolve wt_to_wt4.

Lemma wt_to_wt5 : forall b1 n l op os n' os' b2,
  well_typed_backend (b1 ++ << n; l ->> op :: os >> :: << n'; os' >> :: b2) ->
  well_typed_backend (b1 ++ << n; os >> :: << n'; os' ++ [l ->> op] >> :: b2).
Proof using.
  intros; apply well_typed_backend_dist' in H; destruct H; apply well_typed_backend_dist; eauto.
  inv H0. inv H5. inv H6.
  constructor; eauto.
Qed.
Hint Resolve wt_to_wt5.

Lemma cht_to_ht : forall b os rs t T E,
  config_has_type (C b os rs t) T E ->
  has_type empty t T E.
Proof using. intros. inv H. assumption. Qed.
Hint Resolve cht_to_ht.

Lemma cht_cons : forall b lop os rs t T E,
  config_has_type (C b (lop :: os) rs t) T E ->
  config_has_type (C b os rs t) T E.
Proof using. intros. constructor; eauto; inv H; auto. inv H7. auto. Qed.
Hint Resolve cht_cons.

Lemma cht_to_wtop_cons : forall b lop os rs t T E,
  config_has_type (C b (lop :: os) rs t) T E ->
  well_typed_top_ostream os.
Proof using. intros; inv H; inv H7; auto. Qed.
Hint Resolve cht_to_wtop_cons.

Theorem preservation : forall c c' T E,
  config_has_type c T E ->
  c --> c'  ->
  exists E', config_has_type c' T E' /\ (match E with
                                    | false => E' = false
                                    | _ => True
                                    end).
Proof with eauto.
  intros c c' T E Hht Hstep.
  generalize dependent T.
  generalize dependent E.
  induction Hstep; intros; subst c.
  - inv Hht.
    inv H10.
    exists false.
    split; [constructor; eauto|eauto].
    + assert (E1 = false) by (eapply value_no_emit; eauto); subst.
      assert (E2 = false) by (eapply value_no_emit; eauto); subst.
      assert (E3 = false) by (eapply value_no_emit; eauto); subst.
      eapply well_typed_top_ostream_dist; eauto.
      constructor; eauto. destruct t; try solve [inv H13; inv 4]; try solve [inv H1]. eauto.
  - inv Hht.
    inv H9.
    exists false.
    split; [constructor; eauto|eauto].
    + assert (E1 = false) by (eapply value_no_emit; eauto); subst.
      assert (E2 = false) by (eapply value_no_emit; eauto); subst.
      eapply well_typed_top_ostream_dist; eauto.
  - inv Hht.
    inv H7.
    exists false.
    split; [constructor; eauto|eauto].
  - exists E. inv Hht. split; [constructor; eauto|eauto].
    inv H8.
    inv H2.
    auto.
    destruct E; auto.
  - inv Hht. inv H7.
    assert (config_has_type (C [] [] rs t) (Label T) E) by crush.
    apply IHHstep in H. destruct H. destruct H.
    inv H.
    exists x. crush.
  - inv Hht. inv H7.
    assert (config_has_type (C [] [] rs t1) (Arrow Result (Arrow Result Result false) false) E1) by crush.
    apply IHHstep in H; destruct H; destruct H.
    inv H.
    exists true. split; [constructor; eauto|eauto].
  - inv Hht. inv H8.
    assert (config_has_type (C [] [] rs t2) Result E2) by crush.
    apply IHHstep in H; destruct H; destruct H.
    inv H.
    exists true. split; [constructor; eauto|eauto].
  - inv Hht. inv H9.
    assert (config_has_type (C [] [] rs t3) Keyset E3) by crush.
    apply IHHstep in H; destruct H; destruct H.
    inv H.
    exists true. split; [constructor; eauto|eauto].
  - inv Hht. inv H7.
    assert (config_has_type (C [] [] rs t1) (Arrow Result Result false) E1) by crush.
    apply IHHstep in H; destruct H; destruct H.
    inv H.
    exists true. split; [constructor; eauto|eauto].
  - inv Hht. inv H8.
    assert (config_has_type (C [] [] rs t2) Keyset E2) by crush.
    apply IHHstep in H; destruct H; destruct H.
    inv H.
    exists true. split; [constructor; eauto|eauto].
  - inv Hht. inv H7.
    assert (config_has_type (C [] [] rs t1) Result E1) by crush.
    apply IHHstep in H; destruct H; destruct H.
    inv H.
    exists true. split; [constructor; eauto|eauto].
  - inv Hht. inv H8.
    assert (config_has_type (C [] [] rs t2) Result E2) by crush.
    apply IHHstep in H; destruct H; destruct H.
    inv H.
    exists true. split; [constructor; eauto|eauto].
  - inv Hht. remember E. inv H8.
    assert (E2 = false) by (eapply value_no_emit; eauto); subst.
    assert (E3 = false) by (eapply value_no_emit; eauto); subst.
    exists (E1 || false || false). split; [constructor; eauto|eauto].
    inv H3.
    apply substitution_preserves_typing with T11; eauto.
    repeat (rewrite Bool.orb_false_r); auto.
    destruct E1; auto.
    crush.
    crush.
  - inv Hht. inv H7.
    assert (config_has_type (C [] [] rs t1) (Arrow T11 T E1) E2) by crush.
    apply IHHstep in H; destruct H; destruct H.
    inv H.
    exists (E1 || x || E3). split; [constructor; eauto|eauto].
    destruct E1; destruct E2; destruct E3; auto; crush.
  - inv Hht. inv H8.
    assert (config_has_type (C [] [] rs t2) T11 E3) by crush.
    apply IHHstep in H; destruct H; destruct H.
    inv H.
    exists (E1 || E2 || x). split; [constructor; eauto|eauto].
    destruct E1; destruct E2; destruct E3; auto; crush.
  - inv Hht. inv H7.
    assert (config_has_type (C [] [] rs k) Result E1) by crush.
    apply IHHstep in H; destruct H; destruct H.
    inv H.
    exists (x || E2). split; [constructor; eauto|eauto].
    destruct E1; destruct E2; auto; crush.
  - inv Hht. inv H8.
    assert (config_has_type (C [] [] rs ks) Keyset E2) by crush.
    apply IHHstep in H; destruct H; destruct H.
    inv H.
    exists (E1 || x). split; [constructor; eauto|eauto].
    destruct E1; destruct E2; auto; crush.
  - subst. exists E; split; [constructor; eauto|auto]; destruct E; auto.
  - subst. exists E; split; [constructor; eauto|auto]; destruct E; auto; inv Hht; eauto.
  - subst. exists E; split; [constructor; eauto|auto]; destruct E; auto; inv Hht; eauto.
  - subst. exists E; split; [constructor; eauto|auto]; destruct E; auto; inv Hht; eauto.
  - subst. exists E; split; [constructor; eauto|auto]; destruct E; auto; inv Hht; eauto.
  - subst. exists E; split; [constructor; eauto|auto]; destruct E; auto; inv Hht; eauto.
  - subst. exists E; split; [constructor; eauto|auto]; destruct E; auto; inv Hht; eauto.
  - subst. exists E; split; [constructor; eauto|auto]; destruct E; auto; inv Hht; eauto.
  - subst. exists E; split; [constructor; eauto|auto]; destruct E; auto.
    + assert (config_has_type (C [] [] rs0 t) Result false).
      {
        inv Hht.
        apply well_typed_backend_dist' in H5; destruct H5.
        inv H0. crush.
      }
      apply IHHstep in H; destruct H; destruct H; subst.
      inv Hht.
      apply well_typed_backend_dist' in H6; destruct H6.
      apply well_typed_backend_dist; eauto.
      constructor; eauto.
      inv H1; auto.
    + assert (config_has_type (C [] [] rs0 t) Result false).
      {
        inv Hht.
        apply well_typed_backend_dist' in H5; destruct H5.
        inv H0. crush.
      }
      apply IHHstep in H; destruct H; destruct H; subst.
      inv Hht.
      apply well_typed_backend_dist' in H6; destruct H6.
      apply well_typed_backend_dist; eauto.
      constructor; eauto.
      inv H1; auto.
    + inv Hht; eauto.
    + inv Hht; eauto.
  - subst. exists E; split; [constructor; eauto|auto]; destruct E; auto.
    + inv Hht.
      apply well_typed_backend_dist' in H5; destruct H5.
      apply well_typed_backend_dist; eauto.
      inv H0.
      apply well_typed_ostream_dist' in H8; destruct H8. inv H1.
      assert (config_has_type (C [] [] rs0 t1) Result false).
      {
        inv H10.
        constructor; eauto.
      }
      constructor; eauto; apply well_typed_ostream_dist; eauto.
      constructor; eauto.
      eapply IHHstep in H1; destruct H1; destruct H1; subst.
      inv H1.
      inv H10.
      constructor; eauto.
    + inv Hht.
      apply well_typed_backend_dist' in H5; destruct H5.
      apply well_typed_backend_dist; eauto.
      inv H0.
      apply well_typed_ostream_dist' in H8; destruct H8. inv H1.
      assert (config_has_type (C [] [] rs0 t1) Result false).
      {
        inv H10.
        constructor; eauto.
      }
      constructor; eauto; apply well_typed_ostream_dist; eauto.
      constructor; eauto.
      eapply IHHstep in H1; destruct H1; destruct H1; subst.
      inv H1.
      inv H10.
      constructor; eauto.
    + inv Hht; eauto.
    + inv Hht; eauto.
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
auto.
auto.
auto.
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
    + subst. inv H5.
    + subst. inv H5.
    + subst. inv H5.
    + subst. inv H5.
    + subst. inv H0.
      * destruct b2; crush.
      * {
          destruct b2.
          - inv H5. crush.
          - inv H5.
            apply dry_no_in with (n:=N k v0) (s:=<< N k v0; l ->> pmap f ks :: os1'' >>) (os:=l ->> pmap f ks :: os1'') in H6; crush.
        }
    + subst. inv H0.
      * destruct b2; crush.
      * {
          destruct b2.
          - inv H5; crush.
          - inv H5.
            apply dry_no_in with (n:=N k t0) (s:=<< N k t0; l ->> pfold f t' ks :: os1'' >>) (os:=l ->> pfold f t' ks :: os1'') in H6; crush.
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
      * inv H2. inv H5.
        {
          destruct b2.
          - inv H6; crush.
          - inv H2.
            eapply dry_no_in with (n:=n) in H6; eauto; crush.
        }
    + subst. inv H0.
      * destruct b2; crush.
      * {
          destruct b2.
          - inv H6; crush.
          - inv H6.
            eapply dry_no_in with (n:=n1) in H7; eauto; crush. inv H7.
        }
    + subst. inv H2. inv H4.
      apply dry_backend_dist with (b1:=b2) (b2:=<< N k t0; os1 >> :: b3) in H0; eauto.
      destruct H0.
      inv H2.
      simpl in H8.
      apply frontend_no_value' in H6. apply H6. eauto.
    + subst. inv H2. inv H4.
      apply dry_backend_dist with (b1:=b2) (b2:=<< N k t0; os1 ++ l ->> pfold f t1 ks :: os' >> :: b3) in H0; eauto.
      destruct H0.
      inv H2.
      simpl in H9.
      destruct os1; crush.
  - unfold normal_form in H.
    remember WT. clear Heqw.
    subst c; apply progress in w; eauto.
    destruct w.
    + destruct os.
      * {
        induction b.
        - crush.
        - destruct a as [n os].
          + destruct os.
            * constructor; eauto.
              assert (dry (C b [] rs t)).
              {
                apply IHb.
                - inversion WT.
                  split; try split; eauto.
                  crush.
                  inversion H3; eauto.
                - intro.
                  destruct H1.
                  unfold not in H.
                  inversion H1; ssame; try solve [match goal with | [H : value _ |- _] => inv H end]; try solve [exfalso; apply H; eauto].
                  + exfalso; apply H. eapply ex_intro; eapply S_PMap; eauto; crush.
                  + exfalso; apply H. eapply ex_intro; eapply S_PFold; eauto; crush.
                  + exfalso; apply H. eapply ex_intro; eapply S_Last; eauto; crush.
                  + exfalso; apply H. eapply ex_intro; eapply S_FusePMap; eauto; crush.
                  + exfalso; apply H. eapply ex_intro; eapply S_Prop; eauto; crush.
                  + exfalso; apply H. eapply ex_intro; eapply S_Load; eauto; crush.
                  + exfalso; apply H. eapply ex_intro; eapply S_LoadPFold; eauto; crush.
              }
              inv H1.
              destruct n.
              destruct (value_dec t0); eauto.
              eapply load_exists with (k:=n) (os:=[]) (b1:=[]) (b2:=b) in WT; eauto.
              destruct WT.
              unfold not in H. exfalso; apply H. exists x. assumption. crush.
            * destruct l as [l op].
              exfalso.
              apply H.
              destruct n; eapply op_reduction_exists with (b1:=[]) (b2:=b); eauto; crush.
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
          Unshelve.
          auto.
          auto.
          auto.
          auto.
          assert (value t1) by (eapply waiting_fold_value; eauto).
          assert (has_type empty t1 Result false) by (eapply graph_typing'; eauto).
          destruct t1; try solve [inv H; inv H4]; try solve [inv H1]; try solve [inv H2].
          right. eauto.
        }
    + crush.
Unshelve.
auto.
auto.
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
  inversion H0; inversion H; eapply WT; crush; try solve [apply_preservation]; try solve [inv H1; apply_preservation];
  try solve [
  match goal with
  | [ H : config_has_type _ _ |- _] => inv H
  end;
  match goal with
  | [ H : has_type _ _ _ |- _] => inv H
  end;
  apply_preservation;
  match goal with
  | [ H : config_has_type _ _ |- _] => inv H
  end;
  eauto].
  (* S_Emit_OT_PFold *)
  - eapply fresh''' with (b:=b) (os:=os) (rs:=rs) (l:=l) (os':=[l ->> pfold f t (keyset_to_keyset ks)]) (t':=t_label l) in H; inv H; crush.
  - eapply fresh''' with (b:=b) (os:=os) (rs:=rs) (l:=l) (os':=[l ->> pfold f t (keyset_to_keyset ks)]) (t':=t_label l) in H; inv H; crush.
  - eapply fresh''' with (b:=b) (os:=os) (rs:=rs) (l:=l) (os':=[l ->> pfold f t (keyset_to_keyset ks)]) (t':=t_label l) in H; inv H; crush.
  (* S_Emit_OT_PMap *)
  - eapply fresh'''' with (b:=b) (os:=os) (rs:=rs) (l:=l) (t1:=f) (os':=[l ->> pmap f (keyset_to_keyset ks)]) (t':=t_label l) in H; inv H; crush.
  - eapply fresh'''' with (b:=b) (os:=os) (rs:=rs) (l:=l) (t1:=f) (os':=[l ->> pmap f (keyset_to_keyset ks)]) (t':=t_label l) in H; inv H; crush.
  - eapply fresh'''' with (b:=b) (os:=os) (rs:=rs) (l:=l) (t1:=f) (os':=[l ->> pmap f (keyset_to_keyset ks)]) (t':=t_label l) in H; inv H; crush.
  (* S_Emit_OT_Add *)
  - eapply fresh'''''' with (b:=b) (os:=os) (rs:=rs) (l:=l) (t1:=t_result k) (os':=[l ->> add k (t_result v)]) (t':=t_label l) in H; inv H; crush.
  - eapply fresh'''''' with (b:=b) (os:=os) (rs:=rs) (l:=l) (t1:=t_result k) (os':=[l ->> add k (t_result v)]) (t':=t_label l) in H; inv H; crush.
  - eapply fresh'''''' with (b:=b) (os:=os) (rs:=rs) (l:=l) (t1:=t_result k) (os':=[l ->> add k (t_result v)]) (t':=t_label l) in H; inv H; crush.
  (* S_Claim auto handled *)
  (* S_Ctx_Downarrow *)
  - apply fresh'' with (b:=b) (os:=os) (rs:=rs) (os':=os') (t:=t) (t':=t') in H; inv H; crush.
  - apply fresh'' with (b:=b) (os:=os) (rs:=rs) (os':=os') (t:=t) (t':=t') in H; inv H; crush.
  - apply fresh'' with (b:=b) (os:=os) (rs:=rs) (os':=os') (t:=t) (t':=(t_downarrow t')) in H; inv H; crush.
  (* S_Ctx_Emit_OT_PFold1 *)
  - eapply fresh''' with (b:=b) (os:=os) (rs:=rs) (l:=l)  (os':=os') (t':=t_emit_ot_pfold l t' t2 t3) in H; inv H; crush.
  - eapply fresh''' with (b:=b) (os:=os) (rs:=rs) (l:=l)  (os':=os') (t':=t_emit_ot_pfold l t' t2 t3) in H; inv H; crush.
  - eapply fresh''' with (b:=b) (os:=os) (rs:=rs) (l:=l)  (os':=os') (t':=t_emit_ot_pfold l t' t2 t3) in H; inv H; crush.
  (* S_Ctx_Emit_OT_PFold2 *)
  - eapply fresh''' with (b:=b) (os:=os) (rs:=rs) (l:=l)  (os':=os') (t':=t_emit_ot_pfold l t1 t' t3) in H; inv H; crush.
  - eapply fresh''' with (b:=b) (os:=os) (rs:=rs) (l:=l)  (os':=os') (t':=t_emit_ot_pfold l t1 t' t3) in H; inv H; crush.
  - eapply fresh''' with (b:=b) (os:=os) (rs:=rs) (l:=l)  (os':=os') (t':=t_emit_ot_pfold l t1 t' t3) in H; inv H; crush.
  (* S_Ctx_Emit_OT_PFold3 *)
  - eapply fresh''' with (b:=b) (os:=os) (rs:=rs) (l:=l)  (os':=os') (t':=t_emit_ot_pfold l t1 t2 t') in H; inv H; crush.
  - eapply fresh''' with (b:=b) (os:=os) (rs:=rs) (l:=l)  (os':=os') (t':=t_emit_ot_pfold l t1 t2 t') in H; inv H; crush.
  - eapply fresh''' with (b:=b) (os:=os) (rs:=rs) (l:=l)  (os':=os') (t':=t_emit_ot_pfold l t1 t2 t') in H; inv H; crush.
  (* S_Ctx_Emit_OT_PMap1 *)
  - eapply fresh'''' with (b:=b) (os:=os) (rs:=rs) (l:=l) (t1:=t1) (os':=os') (t':=t_emit_ot_pmap l t1' t2) in H; inv H; crush.
  - eapply fresh'''' with (b:=b) (os:=os) (rs:=rs) (l:=l) (t1:=t1) (os':=os') (t':=t_emit_ot_pmap l t1' t2) in H; inv H; crush.
  - eapply fresh'''' with (b:=b) (os:=os) (rs:=rs) (l:=l) (t1:=t1) (os':=os') (t':=t_emit_ot_pmap l t1' t2) in H; inv H; crush.
  (* S_Ctx_Emit_OT_PMap2 *)
  - eapply fresh'''' with (b:=b) (os:=os) (rs:=rs) (l:=l) (t1:=t1) (os':=os') (t':=t_emit_ot_pmap l t1 t2') in H; inv H; crush.
  - eapply fresh'''' with (b:=b) (os:=os) (rs:=rs) (l:=l) (t1:=t1) (os':=os') (t':=t_emit_ot_pmap l t1 t2') in H; inv H; crush.
  - eapply fresh'''' with (b:=b) (os:=os) (rs:=rs) (l:=l) (t1:=t1) (os':=os') (t':=t_emit_ot_pmap l t1 t2') in H; inv H; crush.
  (* S_Ctx_Emit_OT_Add1 *)
  - eapply fresh'''''' with (b:=b) (os:=os) (rs:=rs) (l:=l) (t1:=t1) (t':=t_emit_ot_add l t1' t2) (t2:=t2) (os':=os') in H; inv H; crush.
  - eapply fresh'''''' with (b:=b) (os:=os) (rs:=rs) (l:=l) (t1:=t1) (t':=t_emit_ot_add l t1' t2) (t2:=t2) (os':=os') in H; inv H; crush.
  - eapply fresh'''''' with (b:=b) (os:=os) (rs:=rs) (l:=l) (t1:=t1) (t':=t_emit_ot_add l t1' t2) (t2:=t2) (os':=os') in H; inv H; crush.
  (* S_Ctx_Emit_OT_Add2 *)
  - eapply fresh'''''' with (b:=b) (os:=os) (rs:=rs) (l:=l) (t1:=t1) (t':=t_emit_ot_add l t1 t2') (t2:=t2) (os':=os') in H; inv H; crush.
  - eapply fresh'''''' with (b:=b) (os:=os) (rs:=rs) (l:=l) (t1:=t1) (t':=t_emit_ot_add l t1 t2') (t2:=t2) (os':=os') in H; inv H; crush.
  - eapply fresh'''''' with (b:=b) (os:=os) (rs:=rs) (l:=l) (t1:=t1) (t':=t_emit_ot_add l t1 t2') (t2:=t2) (os':=os') in H; inv H; crush.
  (* S_App  *)
  - apply_preservation. destruct H0. destruct H0. exists x0, x2. assumption.
  (* S_App1 *)
  - apply fresh' with (b:=b) (os:=os) (rs:=rs) (os':=os') (t1:=t1) (t2:=t2) (t':=t_app t1' t2) in H; inv H; crush.
  - apply fresh' with (b:=b) (os:=os) (rs:=rs) (os':=os') (t1:=t1) (t2:=t2) (t':=t_app t1' t2) in H; inv H; crush.
  - apply fresh' with (b:=b) (os:=os) (rs:=rs) (os':=os') (t1:=t1) (t2:=t2) (t':=t_app t1' t2) in H; inv H; crush.
  (* S_App2 *)
  - apply fresh' with (b:=b) (os:=os) (rs:=rs) (os':=os') (t1:=v1) (t2:=t2) (t':=t_app v1 t2') in H; inv H; crush.
  - apply fresh' with (b:=b) (os:=os) (rs:=rs) (os':=os') (t1:=v1) (t2:=t2) (t':=t_app v1 t2') in H; inv H; crush.
  - apply fresh' with (b:=b) (os:=os) (rs:=rs) (os':=os') (t1:=v1) (t2:=t2) (t':=t_app v1 t2') in H; inv H; crush.
  (* S_KS1 *)
  - apply fresh''''' with (b:=b) (os:=os) (rs:=rs) (os':=os') (t1:=k) (t2:=ks) (t':=t_ks_cons k' ks) in H; inv H; crush.
  - apply fresh''''' with (b:=b) (os:=os) (rs:=rs) (os':=os') (t1:=k) (t2:=ks) (t':=t_ks_cons k' ks) in H; inv H; crush.
  - apply fresh''''' with (b:=b) (os:=os) (rs:=rs) (os':=os') (t1:=k) (t2:=ks) (t':=t_ks_cons k' ks) in H; inv H; crush.
  (* S_KS2 *)
  - apply fresh''''' with (b:=b) (os:=os) (rs:=rs) (os':=os') (t1:=k) (t2:=ks) (t':=t_ks_cons k ks') in H; inv H; crush.
  - apply fresh''''' with (b:=b) (os:=os) (rs:=rs) (os':=os') (t1:=k) (t2:=ks) (t':=t_ks_cons k ks') in H; inv H; crush.
  - apply fresh''''' with (b:=b) (os:=os) (rs:=rs) (os':=os') (t1:=k) (t2:=ks) (t':=t_ks_cons k ks') in H; inv H; crush.
  (* S_Empty *)
  - destruct op; crush.
  (* S_First *)
  - unfold ostream_keys in H8.
    exists x, x0.
    destruct op; inv H2; constructor; eauto.
  - destruct op; crush.
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
  - exists x, x0. inv H1; constructor; eauto.
  - apply distinct_rotate_rev. crush.
  - unfold backend_labels. simpl.
    apply distinct_rotate_rev in H8.
    rewrite List.app_assoc.
    apply distinct_rotate.
    crush.
  (* S_PMap *)
  - exists x, x0. inv H2; constructor; eauto.
  - crush.
  - crush.
  (* S_PFold *)
  - unfold backend_labels at 2.
    simpl.
    assert (backend_labels b1 ++ l :: (ostream_labels os1' ++ []) ++ ostream_labels os ++ rstream_labels rs = backend_labels b1 ++ l :: (ostream_labels os1' ++ [] ++ ostream_labels os ++ rstream_labels rs)) by crush.
    rewrite H3 in H10; clear H3.
    apply distinct_rotate_rev in H10.
    assert (backend_labels b1 ++ (ostream_labels os1' ++ []) ++ ostream_labels os ++ l :: rstream_labels rs = (backend_labels b1 ++ (ostream_labels os1' ++ []) ++ ostream_labels os) ++ l :: rstream_labels rs) by crush.
    rewrite H3; clear H3.
    apply distinct_rotate.
    crush.
  (* S_FusePMap *)
  - exists x, x0. inv H2; constructor; eauto.
  - assert (<< n; os1 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os2 >> :: b2 = [<< n; os1 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os2 >>] ++ b2) by crush.
    rewrite H3 in H7.
    rewrite backend_labels_dist in H7.
    unfold backend_labels at 2 in H7.
    simpl in H7.
    rewrite ostream_labels_dist in H7.
    simpl in H7.
    assert (<< n; os1 ++ l ->> pmap (pmap_compose f' f) ks :: os2 >> :: b2 = [<< n; os1 ++ l ->> pmap (pmap_compose f' f) ks :: os2 >>] ++ b2) by crush.
    rewrite H4.
    clear H1; clear H2.
    rewrite backend_labels_dist.
    unfold backend_labels at 2.
    simpl.
    rewrite ostream_labels_dist.
    simpl.
    repeat (rewrite <- List.app_assoc).
    repeat (rewrite <- List.app_assoc in H7).
    remember (backend_labels b1 ++ ostream_labels os1) as y.
    rewrite -> List.app_assoc.
    rewrite -> List.app_assoc in H7.
    rewrite <- Heqy in *.
    simpl in *.
    rewrite -> cons_app.
    assert (l' :: rstream_labels rs = [l'] ++ rstream_labels rs) by crush.
    rewrite H1.
    clear H1.
    rewrite -> cons_app in H6.
    apply distinct_app_comm.
    simpl.
    apply distinct_app_comm in H7.
    simpl in H7.
    rewrite -> cons_app.
    assert ([l] ++ (ostream_labels os2 ++ backend_labels b2 ++ ostream_labels os ++ l' :: rstream_labels rs) ++ y = ([l] ++ ostream_labels os2 ++ backend_labels b2 ++ ostream_labels os) ++ (l' :: rstream_labels rs ++ y)) by crush.
    rewrite H1.
    clear H1.
    apply distinct_rotate.
    simpl.
    apply distinct_rotate_front.
    crush.
  (* S_Prop *)
  - exists x, x0. inv H2; constructor; eauto.
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
  (* S_Load *)
  - exists x, x0. inv H1. apply well_typed_backend_dist' in H11. destruct H11.
    inv H2.
    apply_preservation. destruct H3. destruct H2. constructor; eauto.
    inv H2.
    apply well_typed_backend_dist; eauto.
  (* S_LoadPFold *)
  - unfold backend_labels at 2 in H8; simpl in H8.
    rewrite ostream_labels_dist in H8.
    unfold backend_labels at 2; simpl.
    rewrite ostream_labels_dist.
    assumption.
  - exists x, x0. inv H1. apply well_typed_backend_dist' in H11. destruct H11.
    inv H2.
    apply well_typed_ostream_dist' in H11; destruct H11.
    inv H4.
    constructor; eauto.
    apply well_typed_backend_dist; eauto.
    constructor; eauto.
    apply well_typed_ostream_dist; eauto.
    constructor; eauto.
    inv H15.
    apply_preservation. destruct H3. destruct H3. inv H3. constructor; eauto.
Unshelve.
auto.
auto.
auto.
auto.
auto.
auto.
auto.
Qed.

(* ****** typing *)

Corollary soundness : forall c c',
  well_typed c ->
  (exists n, c -->*[n] c') ->
  ~(stuck c').
Proof using.
  intros c c' WT.
  intros Hmulti.
  unfold stuck.
  destruct Hmulti as [n Hmulti].
  induction Hmulti.
  - destruct x as [b os rs t].
    eapply progress' in WT; eauto.
    crush.
  - assert (well_typed y) by (apply well_typed_preservation in H; crush).
    crush.
Qed.

Theorem unique_types : forall Gamma t T T' E E',
  has_type Gamma t T E ->
  has_type Gamma t T' E' ->
  T = T' /\ E = E'.
Proof using.
  intros Gamma t.
  generalize dependent Gamma.
  induction t; intros Gamma T T' E E' HT HT'.
  - inv HT; inv HT'; crush.
  - inv HT; inv HT'.
    eapply IHt1 in H2; eauto.
    eapply IHt2 in H5; eauto.
    crush.
  - inv HT; inv HT'.
    eapply IHt in H5; eauto.
    crush.
  - inv HT; inv HT'; eauto.
  - inv HT; inv HT'; eauto.
  - inv HT; inv HT'; eauto.
  - inv HT; inv HT'.
    eapply IHt1 with (T':=Result) (E':=E0) in H2; eauto.
    eapply IHt2 with (T':=Keyset) (E':= E3) in H5; eauto.
    crush.
  - inv HT; inv HT'.
    eapply IHt in H1; eauto.
    crush.
  - inv HT; inv HT'; eauto.
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
  - destruct H2. inv H2. eauto.
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
    - destruct H2.
      inv H.
      exists x, x0. inv H2. apply well_typed_backend_dist' in H8; destruct H8; inv H2. inv H7.
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

Lemma frontend_rstream_extension :
  forall rs os t t' lr,
  C [] [] rs t --> C [] os rs t' ->
  C [] [] (lr :: rs) t --> C [] os (lr :: rs) t'.
Proof using.
  intros rs os t.
  generalize dependent rs.
  generalize dependent os.
  induction t; intros os rs t' lr Hstep; try solve [inversion Hstep; ssame; try solve [destruct b1; crush]; eauto].
  - inversion Hstep; ssame; try solve [destruct b1; crush].
    + eapply S_Claim; eauto. crush.
    + eapply S_Ctx_Downarrow; eauto.
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

Ltac fdet :=
  try solve [match goal with
             | [H : ?b ++ _ = [] |- _] => destruct b; inv H
             | [H : [] = ?b ++ _ |- _] => destruct b; inv H
             end];
  try solve [ssame];
  try solve [repeat (match goal with
                     | [H : C _ _ _ _ = C _ _ _ _ |- _] => inv H
                     end); try solve [split; crush]; try solve [exfalso; eapply frontend_no_value'; eauto]].

Lemma frontend_deterministic :
  forall t rs os t',
  well_typed (C [] [] rs t) ->
  C [] [] rs t --> C [] os rs t' ->
  forall t'' os',
  C [] [] rs t --> C [] os' rs t'' ->
  t' = t'' /\ os = os'.
Proof using.
  induction t; intros rs os0 t' WT; intros.
  - inv H; fdet.
  - inversion H; subst; fdet.
    + inversion H0; subst; fdet.
    + inversion H0; subst; fdet.
      * inv H4; inv H5. eapply IHt1 in H7; eauto. destruct H7. subst; split; eauto.
        inversion WT.
        split; try split; eauto.
        destruct H3.
        inv H3.
        find_type.
      * inv H4; inv H6. apply frontend_no_value' in H7. exfalso. eauto.
    + inversion H0; subst; fdet.
      * inv H5; inv H6. eapply IHt2 in H8; eauto. destruct H8. subst; split; eauto.
        inversion WT.
        split; try split; eauto.
        destruct H3.
        inv H3.
        find_type.
  - apply frontend_no_value' in H; exfalso; eauto.
  - inversion H; subst; fdet.
  - inversion H; subst; fdet.
  - inversion H; subst; fdet.
  - inversion H; subst; fdet.
    + inversion H0; subst; fdet.
      * inv H4; inv H5. apply IHt1 with (t'':=k'0) (os':=os'1) in H7. crush.
        easy_wt.
        assumption.
      * inv H4; inv H6. exfalso; eapply frontend_no_value' in H7; eauto.
    + inversion H0; subst; fdet.
      * inv H5; inv H6. apply IHt2 with (t'':=ks'0) (os':=os'1) in H8. crush.
        easy_wt.
        assumption.
  - inversion H; subst; fdet.
    + inversion H0; subst; fdet.
      * inv H4; inv H5.
        eapply unique_result with (r':=v0) in H7; eauto.
    + inversion H0; subst; fdet.
      * inv H4; inv H5. apply IHt with (os:=os'0) (t':=t'0) in H9; eauto. destruct H9. subst. split; eauto.
        easy_wt.
  - inversion H; subst; fdet.
    + inversion H0; subst; fdet.
    + inversion H0; subst; fdet.
      * inv H4; inv H5.
        eapply IHt1 with (t':=t') (os:=os'1) in H7; eauto.
        destruct H7. crush.
        easy_wt.
      * inv H4; inv H6.
        exfalso; eapply frontend_no_value' in H7; eauto.
      * inv H4; inv H8.
        exfalso; eapply frontend_no_value' in H7; eauto.
    + inversion H0; subst; fdet.
      * inv H5; inv H6.
        eapply IHt2 with (t':=t') (os:=os'1) in H8; eauto.
        destruct H8. crush.
        easy_wt.
      * inv H5; inv H9.
        exfalso; eapply frontend_no_value' in H8; eauto.
    + inversion H0; subst; fdet.
      * inv H6; inv H10.
        eapply IHt3 with (t':=t') (os:=os'1) in H9; eauto.
        destruct H9. crush.
        easy_wt.
  - inversion H; subst; fdet.
    + inversion H0; subst; fdet.
    + inversion H0; subst; fdet.
      * inv H5; inv H4. apply IHt1 with (os:=os'1) (t':=t1'0) in H7. crush.
        easy_wt.
        assumption.
      * inv H4; inv H6.
        exfalso; eapply frontend_no_value' in H7; eauto.
    + inversion H0; subst; fdet.
      * inv H5; inv H6.
        apply IHt2 with (os:=os'0) (t':=t2') in H11; eauto. crush.
        easy_wt.
  - inversion H; subst; fdet.
    + inversion H0; subst; fdet.
      * inv H3; inv H5. exfalso; eapply frontend_no_value'; eauto.
      * inv H3; inv H6. exfalso; eapply frontend_no_value'; eauto.
    + inversion H0; subst; fdet.
      * inv H5; inv H4. apply IHt1 with (os:=os'1) (t':=t1'0) in H7. crush.
        easy_wt.
        assumption.
      * inv H4; inv H6. exfalso; eapply frontend_no_value' in H7; eauto.
    + inversion H0; subst; fdet.
      * inv H5; inv H6. apply IHt2 with (os:=os'1) (t':=t2'0) in H8. crush.
        easy_wt.
        assumption.
Qed.
Hint Resolve frontend_deterministic.

Ltac fnv := match goal with
            | [H : C [] [] ?rs ?t --> C [] ?os ?rs ?t' |- _] => apply frontend_no_value' in H; crush
            end.

Ltac trouble_makers := try solve [eapply S_Add; eauto]; try solve [eapply S_FusePMap; eauto].

Ltac match_ctx_emit_ot_pfold1 :=
  match goal with
  | [H : _ --> C ?b ?os ?rs (t_emit_ot_pfold ?l ?t1 ?t2 ?t3) |- _] =>
    match goal with
    | [H': C [] [] ?rs' ?t --> C [] ?os' ?rs' ?t' |- _] => gotw (C b (os ++ os') rs (t_emit_ot_pfold l t' t2 t3)); simpl; eauto; trouble_makers
    end
  end.

Lemma lc_ctx_emit_ot_pfold1 :
  forall cx cy cz b os os' rs t1 t2 t3 t' l,
  well_typed cx ->
  cx = C b os rs (t_emit_ot_pfold l t1 t2 t3) ->
  cy = C b (os ++ os') rs (t_emit_ot_pfold l t' t2 t3) ->
  cx --> cy ->
  cx --> cz ->
  C [] [] rs t1 --> C [] os' rs t' ->
  cy -v cz.
Proof using.
  intros cx cy cz b os os' rs t1 t2 t3 t' l.
  intros WT Heqcx Heqcy cxcy cxcz.
  intros tt'.
  inversion cxcz; ssame; try solve match_ctx_emit_ot_pfold1.
  (* S_Emit_OT_Pfold *)
  - fnv.
  (* S_Ctx_Emit_OT_Pfold1 *)
  - apply frontend_deterministic with (t'':=t'0) (os':=os'0) in tt'; eauto. crush.
    inv WT. split; try split; eauto; crush.
    apply distinct_concat in H2.
    destruct H2.
    apply distinct_concat in H4.
    crush.
    find_type.
  (* S_Ctx_Emit_OT_Pfold2 *)
  - apply frontend_no_value' in tt'; exfalso; eauto.
  (* S_Ctx_Emit_OT_Pfold3 *)
  - apply frontend_no_value' in tt'; exfalso; eauto.
  (* S_Load *)
  - gotw (C (b1 ++ << N k t'0; os1 >> :: b2) (os0 ++ os') rs0 (t_emit_ot_pfold l t' t2 t3)); eauto.
  (* S_LoadPFold *)
  - gotw (C (b1 ++ << N k t; os1 ++ l0 ->> pfold f t1' ks :: os'0 >> :: b2) (os0 ++ os') rs0 (t_emit_ot_pfold l t' t2 t3)); eauto.
Unshelve.
auto.
auto.
Qed.
Hint Resolve lc_ctx_emit_ot_pfold1.

Ltac match_ctx_emit_ot_pfold2 :=
  match goal with
  | [H : _ --> C ?b ?os ?rs (t_emit_ot_pfold ?l ?t1 ?t2 ?t3) |- _] =>
    match goal with
    | [H': C [] [] ?rs' ?t --> C [] ?os' ?rs' ?t' |- _] => gotw (C b (os ++ os') rs (t_emit_ot_pfold l t1 t' t3)); simpl; eauto; trouble_makers
    end
  end.

Lemma lc_ctx_emit_ot_pfold2 :
  forall cx cy cz b os os' rs t1 t2 t3 t' l,
  well_typed cx ->
  cx = C b os rs (t_emit_ot_pfold l t1 t2 t3) ->
  cy = C b (os ++ os') rs (t_emit_ot_pfold l t1 t' t3) ->
  cx --> cy ->
  cx --> cz ->
  value t1 ->
  C [] [] rs t2 --> C [] os' rs t' ->
  cy -v cz.
Proof using.
  intros cx cy cz b os os' rs t1 t2 t3 t' l.
  intros WT Heqcx Heqcy cxcy cxcz.
  intros HV tt'.
  inversion cxcz; ssame; try solve match_ctx_emit_ot_pfold2.
  (* S_Emit_OT_Pfold *)
  - fnv.
  (* S_Ctx_Emit_OT_Pfold1 *)
  - apply frontend_no_value' in H0; exfalso; eauto.
  (* S_Ctx_Emit_OT_Pfold2 *)
  - apply frontend_deterministic with (t'':=t'0) (os':=os'0) in tt'; eauto. crush.
    inv WT. split; try split; eauto; crush.
    apply distinct_concat in H2.
    destruct H2.
    apply distinct_concat in H3.
    destruct H3. apply distinct_concat in H6.
    crush.
    find_type.
  (* S_Ctx_Emit_OT_Pfold3 *)
  - apply frontend_no_value' in tt'; exfalso; eauto.
  (* S_Load *)
  - gotw (C (b1 ++ << N k t'0; os1 >> :: b2) (os0 ++ os') rs0 (t_emit_ot_pfold l t1 t' t3)); eauto.
  (* S_LoadPFold *)
  - gotw (C (b1 ++ << N k t; os1 ++ l0 ->> pfold f t1' ks :: os'0 >> :: b2) (os0 ++ os') rs0 (t_emit_ot_pfold l t1 t' t3)); eauto.
Unshelve.
auto.
auto.
Qed.
Hint Resolve lc_ctx_emit_ot_pfold2.

Ltac match_ctx_emit_ot_pfold3 :=
  match goal with
  | [H : _ --> C ?b ?os ?rs (t_emit_ot_pfold ?l ?t1 ?t2 ?t3) |- _] =>
    match goal with
    | [H': C [] [] ?rs' ?t --> C [] ?os' ?rs' ?t' |- _] => gotw (C b (os ++ os') rs (t_emit_ot_pfold l t1 t2 t')); simpl; eauto; trouble_makers
    end
  end.

Lemma lc_ctx_emit_ot_pfold3 :
  forall cx cy cz b os os' rs t1 t2 t3 t' l,
  well_typed cx ->
  cx = C b os rs (t_emit_ot_pfold l t1 t2 t3) ->
  cy = C b (os ++ os') rs (t_emit_ot_pfold l t1 t2 t') ->
  cx --> cy ->
  cx --> cz ->
  value t1 ->
  value t2 ->
  C [] [] rs t3 --> C [] os' rs t' ->
  cy -v cz.
Proof using.
  intros cx cy cz b os os' rs t1 t2 t3 t' l.
  intros WT Heqcx Heqcy cxcy cxcz.
  intros HV HV' tt'.
  inversion cxcz; ssame; try solve match_ctx_emit_ot_pfold3.
  (* S_Emit_OT_Pfold *)
  - fnv.
  (* S_Ctx_Emit_OT_Pfold1 *)
  - fnv.
  (* S_Ctx_Emit_OT_Pfold2 *)
  - fnv.
  (* S_Ctx_Emit_OT_Pfold3 *)
  - apply frontend_deterministic with (t'':=t'0) (os':=os'0) in tt'; eauto. crush.
    inv WT. split; try split; eauto; crush.
    apply distinct_concat in H4.
    destruct H4.
    apply distinct_concat in H6.
    destruct H6.
    crush.
    find_type.
  (* S_Load *)
  - gotw (C (b1 ++ << N k t'0; os1 >> :: b2) (os0 ++ os') rs0 (t_emit_ot_pfold l t1 t2 t')); eauto.
  (* S_LoadPFold *)
  - gotw (C (b1 ++ << N k t; os1 ++ l0 ->> pfold f t1' ks :: os'0 >> :: b2) (os0 ++ os') rs0 (t_emit_ot_pfold l t1 t2 t')); eauto.
Unshelve.
auto.
auto.
Qed.
Hint Resolve lc_ctx_emit_ot_pfold3.

Ltac match_emit_ot_add :=
  match goal with
  | [H : _ --> C ?b ?os ?rs ?t |- _] => match goal with
                                      | [H': _ --> C ?b' (?os' ++ ?os'') ?rs' ?t' |- _] => gotw (C b (os ++ os'') rs t'); simpl; eauto; trouble_makers
                                      end
  end.

Lemma lc_emit_ot_add :
  forall cx cy cz b os rs l k v,
  well_typed cx ->
  cx = C b os rs (t_emit_ot_add l (t_result k) (t_result v)) ->
  cy = C b (os ++ [l ->> add k (t_result v)]) rs (t_label l) ->
  cx --> cy ->
  cx --> cz ->
  cy -v cz.
Proof using.
  intros cx cy cz b os rs l incby ks.
  intros WT Heqcx Heqcy cxcy cxcz.
  inversion cxcz; ssame; try solve match_emit_ot_add.
  (* S_Emit_OT_Add *)
  - crush.
  (* S_Ctx_Emit_OT_Add1 *)
  - apply frontend_no_value' in H0; exfalso; eauto.
  (* S_Ctx_Emit_OT_Add2 *)
  - apply frontend_no_value' in H1; exfalso; eauto.
  (* S_Load *)
  - gotw (C (b1 ++ << N k t'; os1 >> :: b2) (os0 ++ [l ->> add incby (t_result ks)]) rs0 (t_label l)); eauto.
  (* S_LoadPFold *)
  - gotw (C (b1 ++ << N k t; os1 ++ l0 ->> pfold f t1' ks0 :: os' >> :: b2) (os0 ++ [l ->> add incby (t_result ks)]) rs0 (t_label l)); eauto.
Unshelve.
auto.
auto.
Qed.
Hint Resolve lc_emit_ot_add.

Ltac match_ctx_emit_ot_add1 :=
  match goal with
  | [H : _ --> C ?b ?os ?rs (t_emit_ot_add ?l ?t1 ?t2) |- _] =>
    match goal with
    | [H': C [] [] ?rs' ?t --> C [] ?os' ?rs' ?t' |- _] => gotw (C b (os ++ os') rs (t_emit_ot_add l t' t2)); simpl; eauto; trouble_makers
    end
  end.

Lemma lc_ctx_emit_ot_add1 :
  forall cx cy cz b os os' rs t1 t2 t1' l,
  well_typed cx ->
  cx = C b os rs (t_emit_ot_add l t1 t2) ->
  cy = C b (os ++ os') rs (t_emit_ot_add l t1' t2) ->
  cx --> cy ->
  cx --> cz ->
  C [] [] rs t1 --> C [] os' rs t1' ->
  cy -v cz.
Proof using.
  intros cx cy cz b os os' rs t1 t2 t1' l.
  intros WT Heqcx Heqcy cxcy cxcz.
  intros t1t1'.
  inversion cxcz; ssame; try solve match_ctx_emit_ot_add1.
  (* S_Emit_OT_Add *)
  - fnv.
  (* S_Ctx_Emit_OT_Add1 *)
  - apply frontend_deterministic with (t'':=t1'0) (os':=os'0) in t1t1'; eauto. crush.
    inv WT. split; try split; eauto; crush.
    apply distinct_concat in H2.
    destruct H2.
    apply distinct_concat in H4.
    crush.
    find_type.
  (* S_Ctx_Emit_OT_Add2 *)
  - apply frontend_no_value' in t1t1'; exfalso; eauto.
  (* S_Load *)
  - gotw (C (b1 ++ << N k t'; os1 >> :: b2) (os0 ++ os') rs0 (t_emit_ot_add l t1' t2)); eauto.
  (* S_LoadPFold *)
  - gotw (C (b1 ++ << N k t; os1 ++ l0 ->> pfold f t1'0 ks :: os'0 >> :: b2) (os0 ++ os') rs0 (t_emit_ot_add l t1' t2)); eauto.
Unshelve.
auto.
auto.
Qed.
Hint Resolve lc_ctx_emit_ot_add1.

Ltac match_ctx_emit_ot_add2 :=
  match goal with
  | [H : _ --> C ?b ?os ?rs (t_emit_ot_add ?l ?t1 ?t2) |- _] =>
    match goal with
    | [H': C [] [] ?rs' ?t --> C [] ?os' ?rs' ?t' |- _] => gotw (C b (os ++ os') rs (t_emit_ot_add l t1 t')); simpl; eauto; trouble_makers
    end
  end.

Lemma lc_ctx_emit_ot_add2 :
  forall cx cy cz b os os' rs t1 t2 t2' l,
  well_typed cx ->
  cx = C b os rs (t_emit_ot_add l t1 t2) ->
  cy = C b (os ++ os') rs (t_emit_ot_add l t1 t2') ->
  cx --> cy ->
  cx --> cz ->
  value t1 ->
  C [] [] rs t2 --> C [] os' rs t2' ->
  cy -v cz.
Proof using.
  intros cx cy cz b os os' rs t1 t2 t2' l.
  intros WT Heqcx Heqcy cxcy cxcz.
  intros HV t1t1'.
  inversion cxcz; ssame; try solve match_ctx_emit_ot_add2.
  (* S_Emit_OT_Add *)
  - fnv.
  (* S_Ctx_Emit_OT_Add1 *)
  - apply frontend_no_value' in H0; exfalso; eauto.
  (* S_Ctx_Emit_OT_Add2 *)
  - apply frontend_deterministic with (t'':=t2'0) (os':=os'0) in t1t1'; eauto. crush.
    inv WT. split; try split; eauto; crush.
    apply distinct_concat in H3.
    destruct H3.
    apply distinct_concat in H5.
    crush.
    find_type.
  (* S_Load *)
  - gotw (C (b1 ++ << N k t'; os1 >> :: b2) (os0 ++ os') rs0 (t_emit_ot_add l t1 t2')); eauto.
  (* S_LoadPFold *)
  - gotw (C (b1 ++ << N k t; os1 ++ l0 ->> pfold f t1' ks :: os'0 >> :: b2) (os0 ++ os') rs0 (t_emit_ot_add l t1 t2')); eauto.
Unshelve.
auto.
auto.
Qed.
Hint Resolve lc_ctx_emit_ot_add2.

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
    find_type.
  (* S_Ctx_Emit_OT_GetPay *)
  - apply frontend_no_value' in t1t1'; exfalso; eauto.
  (* S_Load *)
  - gotw (C (b1 ++ << N k t'; os1 >> :: b2) (os0 ++ os') rs0 (t_ks_cons t1' t2)); eauto.
  (* S_LoadPFold *)
  - gotw (C (b1 ++ << N k t; os1 ++ l ->> pfold f t1'0 ks :: os'0 >> :: b2) (os0 ++ os') rs0 (t_ks_cons t1' t2)); eauto.
Unshelve.
auto.
auto.
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
    find_type.
  (* S_Load *)
  - gotw (C (b1 ++ << N k t'; os1 >> :: b2) (os0 ++ os') rs0 (t_ks_cons t1 t1')); eauto.
  (* S_LoadPFold *)
  - gotw (C (b1 ++ << N k t; os1 ++ l ->> pfold f t1'0 ks :: os'0 >> :: b2) (os0 ++ os') rs0 (t_ks_cons t1 t1')); eauto.
Unshelve.
auto.
auto.
Qed.
Hint Resolve lc_ks2.

Ltac match_emit_ot_pmap :=
  match goal with
  | [H : _ --> C ?b ?os ?rs ?t |- _] => match goal with
                                      | [H': _ --> C ?b' (?os' ++ ?os'') ?rs' ?t' |- _] => gotw (C b (os ++ os'') rs t'); simpl; eauto; trouble_makers
                                      end
  end.

Lemma lc_emit_ot_pmap :
  forall cx cy cz b os rs l f ks,
  well_typed cx ->
  cx = C b os rs (t_emit_ot_pmap l f ks) ->
  cy = C b (os ++ [l ->> pmap f (keyset_to_keyset ks)]) rs (t_label l) ->
  cx --> cy ->
  cx --> cz ->
  value f ->
  value ks ->
  cy -v cz.
Proof using.
  intros cx cy cz b os rs l incby ks.
  intros WT Heqcx Heqcy cxcy cxcz.
  intros HV1 HV2.
  inversion cxcz; ssame; try solve match_emit_ot_pmap.
  (* S_Emit_OT_PMap *)
  - crush.
  (* S_Ctx_Emit_OT_PMap1 *)
  - apply frontend_no_value' in H0; exfalso; eauto.
  (* S_Ctx_Emit_OT_PMap2 *)
  - apply frontend_no_value' in H1; exfalso; eauto.
  (* S_Load *)
  - gotw (C (b1 ++ << N k t'; os1 >> :: b2) (os0 ++ [l ->> pmap incby (keyset_to_keyset ks)]) rs0 (t_label l)); eauto.
  (* S_LoadPFold *)
  - gotw (C (b1 ++ << N k t; os1 ++ l0 ->> pfold f t1' ks0 :: os' >> :: b2) (os0 ++ [l ->> pmap incby (keyset_to_keyset ks)]) rs0 (t_label l)); eauto.
Unshelve.
auto.
auto.
Qed.
Hint Resolve lc_emit_ot_pmap.

Ltac match_ctx_emit_ot_pmap1 :=
  match goal with
  | [H : _ --> C ?b ?os ?rs (t_emit_ot_pmap ?l ?t1 ?t2) |- _] =>
    match goal with
    | [H': C [] [] ?rs' ?t --> C [] ?os' ?rs' ?t' |- _] => gotw (C b (os ++ os') rs (t_emit_ot_pmap l t' t2)); simpl; eauto; trouble_makers
    end
  end.

Lemma lc_ctx_emit_ot_pmap1 :
  forall cx cy cz b os os' rs t1 t2 t1' l,
  well_typed cx ->
  cx = C b os rs (t_emit_ot_pmap l t1 t2) ->
  cy = C b (os ++ os') rs (t_emit_ot_pmap l t1' t2) ->
  cx --> cy ->
  cx --> cz ->
  C [] [] rs t1 --> C [] os' rs t1' ->
  cy -v cz.
Proof using.
  intros cx cy cz b os os' rs t1 t2 t1' l.
  intros WT Heqcx Heqcy cxcy cxcz.
  intros t1t1'.
  inversion cxcz; ssame; try solve match_ctx_emit_ot_pmap1.
  (* S_Emit_OT_Pmap *)
  - fnv.
  (* S_Ctx_Emit_OT_Pmap1 *)
  - apply frontend_deterministic with (t'':=t1'0) (os':=os'0) in t1t1'; eauto. crush.
    inv WT. split; try split; eauto; crush.
    apply distinct_concat in H2.
    destruct H2.
    apply distinct_concat in H4.
    crush.
    find_type.
  (* S_Ctx_Emit_OT_Pmap2 *)
  - apply frontend_no_value' in t1t1'; exfalso; eauto.
  (* S_Load *)
  - gotw (C (b1 ++ << N k t'; os1 >> :: b2) (os0 ++ os') rs0 (t_emit_ot_pmap l t1' t2)); eauto.
  (* S_LoadPFold *)
  - gotw (C (b1 ++ << N k t; os1 ++ l0 ->> pfold f t1'0 ks :: os'0 >> :: b2) (os0 ++ os') rs0 (t_emit_ot_pmap l t1' t2)); eauto.
Unshelve.
auto.
auto.
Qed.
Hint Resolve lc_ctx_emit_ot_pmap1.

Ltac match_ctx_emit_ot_pmap2 :=
  match goal with
  | [H : _ --> C ?b ?os ?rs (t_emit_ot_pmap ?l ?t1 ?t2) |- _] =>
    match goal with
    | [H': C [] [] ?rs' ?t --> C [] ?os' ?rs' ?t' |- _] => gotw (C b (os ++ os') rs (t_emit_ot_pmap l t1 t')); simpl; eauto; trouble_makers
    end
  end.

Lemma lc_ctx_emit_ot_pmap2 :
  forall cx cy cz b os os' rs t1 t2 t2' l,
  well_typed cx ->
  cx = C b os rs (t_emit_ot_pmap l t1 t2) ->
  cy = C b (os ++ os') rs (t_emit_ot_pmap l t1 t2') ->
  cx --> cy ->
  cx --> cz ->
  value t1 ->
  C [] [] rs t2 --> C [] os' rs t2' ->
  cy -v cz.
Proof using.
  intros cx cy cz b os os' rs t1 t2 t2' l.
  intros WT Heqcx Heqcy cxcy cxcz.
  intros HV t1t1'.
  inversion cxcz; ssame; try solve match_ctx_emit_ot_pmap2.
  (* S_Emit_OT_Pmap *)
  - fnv.
  (* S_Ctx_Emit_OT_Pmap1 *)
  - apply frontend_no_value' in H0; exfalso; eauto.
  (* S_Ctx_Emit_OT_Pmap2 *)
  - apply frontend_deterministic with (t'':=t2'0) (os':=os'0) in t1t1'; eauto. crush.
    inv WT. split; try split; eauto; crush.
    apply distinct_concat in H3.
    destruct H3.
    apply distinct_concat in H5.
    crush.
    find_type.
  (* S_Load *)
  - gotw (C (b1 ++ << N k t'; os1 >> :: b2) (os0 ++ os') rs0 (t_emit_ot_pmap l t1 t2')); eauto.
  (* S_LoadPFold *)
  - gotw (C (b1 ++ << N k t; os1 ++ l0 ->> pfold f t1' ks :: os'0 >> :: b2) (os0 ++ os') rs0 (t_emit_ot_pmap l t1 t2')); eauto.
Unshelve.
auto.
auto.
Qed.
Hint Resolve lc_ctx_emit_ot_pmap2.

Ltac match_emit_ot_pfold :=
  match goal with
  | [H : _ --> C ?b ?os ?rs ?t |- _] => match goal with
                                      | [H': _ --> C ?b' (?os' ++ ?os'') ?rs' ?t' |- _] => gotw (C b (os ++ os'') rs t'); simpl; eauto; trouble_makers
                                      end
  end.

Lemma lc_emit_ot_pfold :
  forall cx cy cz b os rs l f t ks,
  well_typed cx ->
  cx = C b os rs (t_emit_ot_pfold l f t ks) ->
  cy = C b (os ++ [l ->> pfold f t (keyset_to_keyset ks)]) rs (t_label l) ->
  cx --> cy ->
  cx --> cz ->
  value f ->
  value t ->
  value ks ->
  cy -v cz.
Proof using.
  intros cx cy cz b os rs l f t ks WT Heqcx Heqcy cxcy cxcz.
  intros Hvf Hvt Hvks.
  inversion cxcz; ssame; try solve match_emit_ot_pfold; try solve [fnv].
  (* S_Emit_OT_PFold *)
  - crush.
  (* S_Load *)
  - gotw (C (b1 ++ << N k t'; os1 >> :: b2) (os0 ++ [l ->> pfold f t (keyset_to_keyset ks)]) rs0 (t_label l)); eauto.
  (* S_LoadPFold *)
  - gotw (C (b1 ++ << N k t0; os1 ++ l0 ->> pfold f0 t1' ks0 :: os' >> :: b2) (os0 ++ [l ->> pfold f t (keyset_to_keyset ks)]) rs0 (t_label l)); eauto.
Unshelve.
auto.
auto.
Qed.
Hint Resolve lc_emit_ot_pfold.

Ltac match_ctx_downarrow :=
  match goal with
  | [H : _ --> C ?b ?os ?rs ?t |- _] => match goal with
                                      | [H': _ --> C [] ?os' ?rs' ?t' |- _] => gotw (C b (os ++ os') rs (t_downarrow t')); simpl; eauto; trouble_makers
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
  - gotw (C [] (os'0 ++ os') (l ->>> final H :: rs0) (t_downarrow t')).
    + eapply S_Empty; eauto. crush.
    + eapply S_Ctx_Downarrow; eauto.
    + crush.
  (* S_Load *)
  - gotw (C (b1 ++ << N k t'0; os1 >> :: b2) (os0 ++ os') rs0 (t_downarrow t')); eauto.
  (* S_LoadPFold *)
  - gotw (C (b1 ++ << N k t0; os1 ++ l ->> pfold f t1' ks :: os'0 >> :: b2) (os0 ++ os') rs0 (t_downarrow t')); eauto.
Unshelve.
auto.
auto.
Qed.
Hint Resolve lc_ctx_downarrow.

Ltac match_claim :=
  match goal with
  | [H : _ --> C ?b ?os ?rs ?t |- _] => match goal with
                                      | [H': C ?b' ?os' ?rs' ?t'' --> C ?b' ?os' ?rs' ?t' |- _] => gotw (C b os rs t'); simpl; eauto; trouble_makers; eapply S_Claim; eauto; crush
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
  (* S_Load *)
  - gotw (C (b1 ++ << N k t'; os1 >> :: b2) os0 rs0 (t_result v)); eauto.
  (* S_LoadPFold *)
  - gotw (C (b1 ++ << N k t; os1 ++ l0 ->> pfold f t1' ks :: os' >> :: b2) os0 rs0 (t_result v)); eauto.
Unshelve.
auto.
auto.
Qed.
Hint Resolve lc_claim.

Ltac tsod := match goal with
             | [H : ?b1 ++ <<N ?k ?t; ?os>> :: ?b2 = ?b3 ++ <<N ?k' ?t'; ?os'>> :: ?b4 |- _] =>
                 eapply (@target_same_or_different _ b1 b2 b3 b4 k t k' t') in H; eauto; destruct H as [Hsame|Hwhich]; try destruct Hwhich as [Hfirst|Hsecond];
                 try (destruct Hsame as [Hsame1 Hsame2]; destruct Hsame2 as [Hsame2 Hsame3]; destruct Hsame3 as [Hsame3 Hsame4]; destruct Hsame4 as [Hsame4 Hsame5]; subst)
             end.

Ltac tsod' := match goal with
              | [H : ?b1 ++ <<N ?k ?t; ?os>> :: ?b2 = ?b3 ++ <<N ?k' ?t'; ?os' ++ ?os''>> :: ?b4 |- _] =>
                  eapply (@target_same_or_different _ b1 b2 b3 b4 k t k' t' os (os' ++ os'')) in H; eauto; destruct H as [Hsame|Hwhich]; try destruct Hwhich as [Hfirst|Hsecond];
                  try (destruct Hsame as [Hsame1 Hsame2]; destruct Hsame2 as [Hsame2 Hsame3]; destruct Hsame3 as [Hsame3 Hsame4]; destruct Hsame4 as [Hsame4 Hsame5]; subst)
              end.

Ltac tsod'' := match goal with
              | [H : ?b1 ++ <<N ?k ?t; ?os ++ ?os'''>> :: ?b2 = ?b3 ++ <<N ?k' ?t'; ?os' ++ ?os''>> :: ?b4 |- _] =>
                  eapply (@target_same_or_different _ b1 b2 b3 b4 k t k' t' (os ++ os''') (os' ++ os'')) in H; eauto; destruct H as [Hsame|Hwhich]; try destruct Hwhich as [Hfirst|Hsecond];
                  try (destruct Hsame as [Hsame1 Hsame2]; destruct Hsame2 as [Hsame2 Hsame3]; destruct Hsame3 as [Hsame3 Hsame4]; destruct Hsame4 as [Hsame4 Hsame5]; subst)
              end.

Ltac tu1 := match goal with
            | [H : ?b1 ++ <<N ?k ?t; ?os>> :: ?b2 = ?b3 ++ <<N ?k ?t; ?os>> :: ?b' ++ <<N ?k' ?t'; ?os'>> :: ?b4 |- _] =>
            eapply (@target_unique _ _ b1 b2 b3 _) in H; crush
            end;
            match goal with
            | [H : C _ _ _ _ = C _ _ _ _ |- _] => inv H
            end;
            match goal with
            | [H : ?b1 ++ <<N ?k' ?t'; ?os'>> :: ?b' ++ <<N ?k ?t; ?os>> :: ?b2 = ?b3 ++ <<N ?k ?t; ?os>> :: ?b4 |- _] =>
              eapply (@target_unique _ _ (b1 ++ <<N k' t'; os'>> :: b') b2 b3 b4) in H; eauto; crush
            end.

Ltac tu2 := match goal with
            | [H : ?b1 ++ <<N ?k ?t; ?os>> :: ?b2 = ?b3 ++ <<N ?k' ?t'; ?os'>> :: ?b' ++ <<N ?k ?t; ?os>> :: ?b4 |- _] =>
              eapply (@target_unique _ _ b1 b2 (b3 ++ <<N k' t'; os'>> :: b') b4) in H; eauto; crush
            end;
            match goal with
            | [H : C _ _ _ _ = C _ _ _ _ |- _] => inv H
            end;
            match goal with
            | [H : ?b1 ++ <<N ?k ?t; ?os>> :: ?b' ++ <<N ?k' ?t'; ?os'>> :: ?b2 = ?b3 ++ <<N ?k ?t; ?os>> :: ?b4 |- _] =>
              eapply (@target_unique _ _ b1 (b' ++ <<N k' t'; os'>> :: b2) b3 b4) in H; eauto; crush
            end.

Axiom pmap_value : forall op f ks,
  op = pmap f ks ->
  value f.

Lemma lc_load :
  forall cx cy cz b1 b2 k os t t' term0 os0 rs0,
  well_typed cx ->
  cx = C (b1 ++ <<N k t; os>> :: b2) os0 rs0 term0 ->
  cy = C (b1 ++ <<N k t'; os>> :: b2) os0 rs0 term0 ->
  cx --> cy ->
  cx --> cz ->
  C [] [] rs0 t --> C [] [] rs0 t' ->
  cy -v cz.
Proof using.
  intros cx cy cz b1 b2 k os t t' term0 os0 rs0.
  intros WT Heqcx Heqcy cxcy cxcz.
  intros tt'.
  inversion cxcz; ssame; try solve [subst; eauto].
  (* S_App *)
  - gotw (C (b1 ++ << N k t'; os >> :: b2) os1 rs (#[ x := v2] t12)); eauto.
  (* S_App1 *)
  - gotw (C (b1 ++ << N k t'; os >> :: b2) (os1 ++ os') rs (t_app t1' t2)); eauto.
  (* S_App2 *)
  - gotw (C (b1 ++ << N k t'; os >> :: b2) (os1 ++ os') rs (t_app v1 t2')); eauto.
  (* S_Empty *)
  - destruct b1; crush.
  (* S_First *)
  - destruct b1; simpl in *.
    + inv H1.
      gotw (C (<< N k t'; os2 ++ [l ->> op] >> :: b') os' rs term1); eauto.
      eapply S_Load with (b1:=[]); eauto; crush.
    + inv H1.
      gotw (C (<< n1; os2 ++ [l ->> op] >> :: b1 ++ << N k t'; os >> :: b2) os' rs term1); eauto.
      eapply S_Load with (b1:=<< n1; os2 ++ [l ->> op] >> :: b1); eauto; crush.
  (* S_Add *)
  - gotw (C (<< N k0 v; [] >> :: b1 ++ << N k t'; os >> :: b2) os' (l ->>> final H :: rs) term1); eauto.
    eapply S_Load with (b1:=<< N k0 v; [] >> :: b1); eauto; crush.
  (* S_PMap *)
  - tsod.
    + inv H.
      got.
      * one_step. instantiate (1:=C (b0 ++ << N k0 (t_app f t'); l ->> pmap f (remove Nat.eq_dec k0 ks) :: os1'' >> :: b3) os1 rs term1).
        eapply S_PMap; eauto.
      * one_step. instantiate (1:=C (b0 ++ << N k0 (t_app f t'); l ->> pmap f (remove Nat.eq_dec k0 ks) :: os1'' >> :: b3) os1 rs term1).
        eapply S_Load; eauto.
        eapply S_App2 with (os:=[]); eauto.
        remember (pmap f ks) as op; eapply pmap_value; eauto.
      * crush.
    + destruct Hfirst as [b' [b'' [b''']]].
      tu1.
      got.
      * one_step. instantiate (1:=C ((b' ++ << N k t'; os >> :: b'') ++ << N k0 (t_app f v); l ->> pmap f (remove Nat.eq_dec k0 ks) :: os1'' >> :: b3) os1 rs term1).
        eapply S_PMap; eauto; crush.
      * one_step. instantiate (1:=C (b' ++ << N k t'; os >> :: b'' ++ << N k0 (t_app f v); l ->> pmap f (remove Nat.eq_dec k0 ks) :: os1'' >> :: b3) os1 rs term1).
        eapply S_Load; eauto; crush.
      * crush.
    + destruct Hsecond as [b' [b'' [b''']]].
      tu2.
      got.
      * instantiate (1:=C (b0 ++ << N k0 (t_app f v); l ->> pmap f (remove Nat.eq_dec k0 ks) :: os1'' >> :: b'' ++ << N k t'; os >> :: b''') os1 rs term1).
        one_step; eapply S_PMap; eauto.
      * instantiate (1:=C ((b0 ++ << N k0 (t_app f v); l ->> pmap f (remove Nat.eq_dec k0 ks) :: os1'' >> :: b'') ++ << N k t'; os >> :: b''') os1 rs term1).
        one_step; eapply S_Load; eauto; crush.
      * crush.
  (* S_PFold *)
  - tsod.
    + got.
      * instantiate (1:=C (b0 ++ << N k0 t'; l ->> pfold f (t_app (t_app f t') t'0) (remove Nat.eq_dec k0 ks) :: os1'' >> :: b3) os1 rs term1).
        one_step. eapply S_PFold; eauto.
      * instantiate (1:=C (b0 ++ << N k0 t'; l ->> pfold f (t_app (t_app f t') t'0) (remove Nat.eq_dec k0 ks) :: os1'' >> :: b3) os1 rs term1).
        exists 2.
        eapply Step.
        instantiate (1:=C (b0 ++ << N k0 t'; l ->> pfold f (t_app (t_app f t0) t'0) (remove Nat.eq_dec k0 ks) :: os1'' >> :: b3) os1 rs term1).
        eapply S_Load; eauto.
        apply one_star.
        {
        eapply S_LoadPFold with (os:=[]).
        - instantiate (1:=(b0 ++ << N k0 t'; l ->> pfold f (t_app (t_app f t0) t'0) (remove Nat.eq_dec k0 ks) :: os1'' >> :: b3)).
          reflexivity.
        - simpl. eauto.
        - instantiate (1:=(t_app (t_app f t') t'0)).
          eapply S_App1 with (os:=[]).
          instantiate (1:=(t_app f t0)).
          reflexivity.
          eapply S_App2 with (os:=[]).
          instantiate (1:=t0).
          reflexivity.
          eapply pfold_value; eauto.
          assumption.
        - crush.
        }
      * crush.
    + destruct Hfirst as [b' [b'' [b''']]].
      tu1.
      got.
      * instantiate (1:=C ((b' ++ << N k t'; os >> :: b'') ++ << N k0 t0; l ->> pfold f (t_app (t_app f t0) t'0) (remove Nat.eq_dec k0 ks) :: os1'' >> :: b3) os1 rs term1).
        one_step; eapply S_PFold; eauto; crush.
      * instantiate (1:=C (b' ++ << N k t'; os >> :: b'' ++ << N k0 t0; l ->> pfold f (t_app (t_app f t0) t'0) (remove Nat.eq_dec k0 ks) :: os1'' >> :: b3) os1 rs term1).
        one_step; eapply S_Load; eauto.
      * crush.
    + destruct Hsecond as [b' [b'' [b''']]].
      tu2.
      got.
      * instantiate (1:=C (b0 ++ << N k0 t0; l ->> pfold f (t_app (t_app f t0) t'0) (remove Nat.eq_dec k0 ks) :: os1'' >> :: b'' ++ << N k t'; os >> :: b''') os1 rs term1).
        one_step; eapply S_PFold; eauto; crush.
      * instantiate (1:=C ((b0 ++ << N k0 t0; l ->> pfold f (t_app (t_app f t0) t'0) (remove Nat.eq_dec k0 ks) :: os1'' >> :: b'') ++ << N k t'; os >> :: b''') os1 rs term1).
        one_step; eapply S_Load; eauto; crush.
      * crush.
  (* S_Last *)
  - destruct b2.
    + apply List.app_inj_tail in H2. destruct H2. inv H2.
      gotw (C (b0 ++ [<< N k t'; os1' >>]) os1 (l ->>> final H :: rs) term1); eauto.
    + remember (s :: b2) as bend.
      assert (exists y ys, bend = ys ++ [y]) by (apply list_snoc with (xs:=bend) (x:=s) (xs':=b2); crush).
      destruct H1; destruct H1.
      inv H1.
      rewrite H3 in *. clear H3.
      assert (b1 ++ << N k t; os >> :: x0 ++ [x] = (b1 ++ << N k t; os >> :: x0) ++ [x]) by crush.
      rewrite H1 in H2; clear H1.
      apply List.app_inj_tail in H2.
      destruct H2.
      subst.
      got.
      * instantiate (1:=C ((b1 ++ << N k t'; os >> :: x0) ++ [<< n1; os1' >>]) os1 (l ->>> final H :: rs) term1).
        one_step; eapply S_Last; eauto; crush.
      * instantiate (1:=C (b1 ++ << N k t'; os >> :: x0 ++ [<< n1; os1' >>]) os1 (l ->>> final H :: rs) term1).
        one_step; eapply S_Load; eauto; crush.
      * crush.
  (* S_FusePMap *)
  - destruct n. tsod'.
    + gotw (C (b0 ++ << N n t'; os2 ++ l ->> pmap (pmap_compose f' f) ks :: os3 >> :: b3) os1 (l' ->>> final H :: rs) term1); eauto.
    + destruct Hfirst as [b' [b'' [b''']]].
      tu1.
      got.
      * instantiate (1:=C ((b' ++ << N k t'; os >> :: b'') ++ << N n t0; os2 ++ l ->> pmap (pmap_compose f' f) ks :: os3 >> :: b3) os1 (l' ->>> 0 :: rs) term1).
        one_step; eapply S_FusePMap; eauto; crush.
      * instantiate (1:=C (b' ++ << N k t'; os >> :: b'' ++ << N n t0; os2 ++ l ->> pmap (pmap_compose f' f) ks :: os3 >> :: b3) os1 (l' ->>> 0 :: rs) term1).
        one_step; eapply S_Load; eauto; crush.
      * crush.
    + destruct Hsecond as [b' [b'' [b''']]].
      tu2.
      got.
      * instantiate (1:=C (b0 ++ << N n t0; os2 ++ l ->> pmap (pmap_compose f' f) ks :: os3 >> :: b'' ++ << N k t'; os >> :: b''') os1 (l' ->>> 0 :: rs) term1).
        one_step; eapply S_FusePMap; eauto; crush.
      * instantiate (1:=C ((b0 ++ << N n t0; os2 ++ l ->> pmap (pmap_compose f' f) ks :: os3 >> :: b'') ++ << N k t'; os >> :: b''') os1 (l' ->>> 0 :: rs) term1).
        one_step; eapply S_Load; eauto; crush.
      * crush.
  (* S_Prop *)
  - destruct n1. tsod.
    + inv H.
      gotw (C (b0 ++ << N n t'; os2 >> :: << n2; os3 ++ [l ->> op] >> :: b3) os1 rs term1); eauto.
    + destruct Hfirst as [b' [b'' [b''']]].
      tu1.
      got.
      * instantiate (1:=C ((b' ++ << N k t'; os >> :: b'') ++ << N n t0; os2 >> :: << n2; os3 ++ [l ->> op] >> :: b3) os1 rs term1); eauto.
        one_step; eapply S_Prop; eauto; crush.
      * instantiate (1:=C (b' ++ << N k t'; os >> :: b'' ++ << N n t0; os2 >> :: << n2; os3 ++ [l ->> op] >> :: b3) os1 rs term1); eauto.
      * crush.
    + destruct Hsecond as [b' [b'' [b''']]].
      tu2.
      {
      destruct b''; simpl in *.
      - inv H1.
        got.
        + instantiate (1:=C (b0 ++ << N n t0; os2 >> :: << N k t'; os3 ++ [l ->> op] >> :: b3) os1 rs term1); eauto.
          one_step; eapply S_Prop; eauto; crush.
        + instantiate (1:=C ((b0 ++ [<< N n t0; os2 >>]) ++ << N k t'; os3 ++ [l ->> op] >> :: b3) os1 rs term1); eauto.
          one_step; eapply S_Load; eauto; crush.
        + crush.
      - inv H1.
        got.
        + instantiate (1:=C (b0 ++ << N n t0; os2 >> :: << n2; os3 ++ [l ->> op] >> :: b'' ++ << N k t'; os >> :: b''') os1 rs term1); eauto.
          one_step; eapply S_Prop; eauto; crush.
        + instantiate (1:=C ((b0 ++ << N n t0; os2 >> :: << n2; os3 ++ [l ->> op] >> :: b'') ++ << N k t'; os >> :: b''') os1 rs term1); eauto.
          one_step; eapply S_Load; eauto; crush.
        + crush.
      }
  (* S_Load *)
  - tsod.
    + eapply frontend_deterministic with (os:=[]) (t':=t'0) in tt'; eauto. destruct tt'.
      crush.
      split; crush.
      inv WT. crush. apply distinct_concat in H2. destruct H2. apply distinct_concat in H4. destruct H4. apply distinct_concat in H5.
      crush.
      remember (N k0 t0) as n.
      exists Result, false.
      constructor; eauto. eapply graph_typing; eauto.
    + destruct Hfirst as [b' [b'' [b''']]].
      tu1.
      got.
      * instantiate (1:=C ((b' ++ << N k t'; os >> :: b'') ++ << N k0 t'0; os2 >> :: b3) os1 rs1 term1); eauto.
        one_step; eapply S_Load; eauto; crush.
      * instantiate (1:=C (b' ++ << N k t'; os >> :: b'' ++ << N k0 t'0; os2 >> :: b3) os1 rs1 term1); eauto.
      * crush.
    + destruct Hsecond as [b' [b'' [b''']]].
      tu2.
      got.
      * instantiate (1:=C (b0 ++ << N k0 t'0; os2 >> :: b'' ++ << N k t'; os >> :: b''') os1 rs1 term1); eauto.
      * instantiate (1:=C ((b0 ++ << N k0 t'0; os2 >> :: b'') ++ << N k t'; os >> :: b''') os1 rs1 term1); eauto.
        one_step; eapply S_Load; eauto; crush.
      * crush.
  (* S_LoadPFold *)
  - tsod.
    + gotw (C (b0 ++ << N k0 t'; os2 ++ l ->> pfold f t1' ks :: os' >> :: b3) os1 rs1 term1); eauto.
    + destruct Hfirst as [b' [b'' [b''']]].
      tu1.
      got.
      * instantiate (1:=C ((b' ++ << N k t'; os >> :: b'') ++ << N k0 t0; os2 ++ l ->> pfold f t1' ks :: os' >> :: b3) os1 rs1 term1); eauto.
        one_step; eapply S_LoadPFold; eauto; crush.
      * instantiate (1:=C (b' ++ << N k t'; os >> :: b'' ++ << N k0 t0; os2 ++ l ->> pfold f t1' ks :: os' >> :: b3) os1 rs1 term1); eauto.
      * crush.
    + destruct Hsecond as [b' [b'' [b''']]].
      tu2.
      got.
      * instantiate (1:=C (b0 ++ << N k0 t0; os2 ++ l ->> pfold f t1' ks :: os' >> :: b'' ++ << N k t'; os >> :: b''') os1 rs1 term1); eauto.
      * instantiate (1:=C ((b0 ++ << N k0 t0; os2 ++ l ->> pfold f t1' ks :: os' >> :: b'') ++ << N k t'; os >> :: b''') os1 rs1 term1); eauto.
        one_step; eapply S_Load; eauto; crush.
      * crush.
Unshelve.
auto.
auto.
auto.
auto.
Qed.
Hint Resolve lc_load.

Axiom pfold_get : forall rs t t' t'',
  C [] [] rs t' --> C [] [] rs t'' ->
  t_app t t' = t_app t t''.

Lemma lc_pfold :
  forall cx cy cz os rs term k t t' f l ks os1 b1 b2,
  well_typed cx ->
  cx = C (b1 ++ <<N k t; l ->> pfold f t' ks :: os1>> :: b2) os rs term ->
  cy = C (b1 ++ <<N k t; l ->> pfold f (t_app (t_app f t) t') (remove Nat.eq_dec k ks) :: os1>> :: b2) os rs term ->
  cx --> cy ->
  cx --> cz ->
  In k ks ->
  cy -v cz.
Proof using.
  intros cx cy cz os rs term k t t' f l ks os1 b1 b2.
  intros WT Heqcx Heqcy cxcy cxcz.
  intros HIn.
  inversion cxcz; ssame; try solve [subst; eauto].
  (* S_App *)
  - gotw (C (b1 ++ << N k t; l ->> pfold f (t_app (t_app f t) t') (remove Nat.eq_dec k ks) :: os1 >> :: b2) os0 rs0 (#[ x := v2] t12)); eauto.
  (* S_App1 *)
  - gotw (C (b1 ++ << N k t; l ->> pfold f (t_app (t_app f t) t') (remove Nat.eq_dec k ks) :: os1 >> :: b2) (os0 ++ os') rs0 (t_app t1' t2)); eauto.
  (* S_App2 *)
  - gotw (C (b1 ++ << N k t; l ->> pfold f (t_app (t_app f t) t') (remove Nat.eq_dec k ks) :: os1 >> :: b2) (os0 ++ os') rs0 (t_app v1 t2')); eauto.
  (* S_Empty *)
  - destruct b1; crush.
  (* S_First *)
  - destruct b1; simpl in *.
    + inv H1.
      gotw (C (<< N k t; l ->> pfold f (t_app (t_app f t) t') (remove Nat.eq_dec k ks) :: os1 ++ [l0 ->> op] >> :: b') os' rs0 term0); eauto.
      * rewrite -> List.app_comm_cons.
        eapply S_First; eauto.
      * eapply S_PFold with (b1:=[]); eauto; crush.
    + inv H1.
      gotw (C (<< n1; os2 ++ [l0 ->> op]>> :: b1 ++ << N k t; l ->> pfold f (t_app (t_app f t) t') (remove Nat.eq_dec k ks) :: os1 >> :: b2) os' rs0 term0); eauto.
      * rewrite List.app_comm_cons.
        eapply S_PFold with (b1:=(<< n1; os2 ++ [l0 ->> op] >> :: b1)); crush.
  (* S_Add *)
  - got.
    * instantiate (1:=C (<<N k0 v; []>> :: b1 ++ << N k t; l ->> pfold f (t_app (t_app f t) t') (remove Nat.eq_dec k ks) :: os1 >> :: b2) os' (l0 ->>> final H :: rs0) term0); eauto.
    * instantiate (1:=C ((<<N k0 v; []>> :: b1) ++ << N k t; l ->> pfold f (t_app (t_app f t) t') (remove Nat.eq_dec k ks) :: os1 >> :: b2) os' (l0 ->>> final H :: rs0) term0); eauto.
      one_step; eapply S_PFold; eauto; crush.
    * crush.
  (* S_PMap *)
  - tsod.
    + crush.
    + destruct Hfirst as [b' [b'' [b''']]].
      tu1.
      got.
      * instantiate (1:=C ((b' ++ << N k t; l ->> pfold f (t_app (t_app f t) t') (remove Nat.eq_dec k ks) :: os1 >> :: b'') ++ << N k0 (t_app f0 v); l0 ->> pmap f0 (remove Nat.eq_dec k0 ks0) :: os1'' >> :: b3) os0 rs0 term0).
        one_step; eapply S_PMap; eauto; crush.
      * instantiate (1:=C (b' ++ << N k t; l ->> pfold f (t_app (t_app f t) t') (remove Nat.eq_dec k ks) :: os1 >> :: b'' ++ << N k0 (t_app f0 v); l0 ->> pmap f0 (remove Nat.eq_dec k0 ks0) :: os1'' >> :: b3) os0 rs0 term0); eauto.
      * crush.
    + destruct Hsecond as [b' [b'' [b''']]].
      tu2.
      got.
      * instantiate (1:=C (b0 ++ << N k0 (t_app f0 v); l0 ->> pmap f0 (remove Nat.eq_dec k0 ks0) :: os1'' >> :: b'' ++ << N k t; l ->> pfold f (t_app (t_app f t) t') (remove Nat.eq_dec k ks) :: os1 >> :: b''') os0 rs0 term0); eauto.
      * instantiate (1:=C ((b0 ++ << N k0 (t_app f0 v); l0 ->> pmap f0 (remove Nat.eq_dec k0 ks0) :: os1'' >> :: b'') ++ << N k t; l ->> pfold f (t_app (t_app f t) t') (remove Nat.eq_dec k ks) :: os1 >> :: b''') os0 rs0 term0); eauto.
        one_step; eapply S_PFold; eauto; crush.
      * crush.
  (* S_PFold *)
  - tsod.
    + inv Hsame5. crush.
    + destruct Hfirst as [b' [b'' [b''']]].
      tu1.
      got.
      * instantiate (1:=C ((b' ++ << N k t; l ->> pfold f (t_app (t_app f t) t') (remove Nat.eq_dec k ks) :: os1 >> :: b'') ++ << N k0 t0; l0 ->> pfold f0 (t_app (t_app f0 t0) t'0) (remove Nat.eq_dec k0 ks0) :: os1'' >> :: b3) os0 rs0 term0).
        one_step; eapply S_PFold; eauto; crush.
      * instantiate (1:=C (b' ++ << N k t; l ->> pfold f (t_app (t_app f t) t') (remove Nat.eq_dec k ks) :: os1 >> :: b'' ++ << N k0 t0; l0 ->> pfold f0 (t_app (t_app f0 t0) t'0) (remove Nat.eq_dec k0 ks0) :: os1'' >> :: b3) os0 rs0 term0); eauto.
      * crush.
    + destruct Hsecond as [b' [b'' [b''']]].
      tu2.
      got.
      * instantiate (1:=C (b0 ++ << N k0 t0; l0 ->> pfold f0 (t_app (t_app f0 t0) t'0) (remove Nat.eq_dec k0 ks0) :: os1'' >> :: b'' ++ << N k t; l ->> pfold f (t_app (t_app f t) t') (remove Nat.eq_dec k ks) :: os1 >> :: b''') os0 rs0 term0); eauto.
      * instantiate (1:=C ((b0 ++ << N k0 t0; l0 ->> pfold f0 (t_app (t_app f0 t0) t'0) (remove Nat.eq_dec k0 ks0) :: os1'' >> :: b'') ++ << N k t; l ->> pfold f (t_app (t_app f t) t') (remove Nat.eq_dec k ks) :: os1 >> :: b''') os0 rs0 term0).
        one_step; eapply S_PFold; eauto; crush.
      * crush.
  (* S_Last *)
  - destruct b2.
    + apply List.app_inj_tail in H2.
      destruct H2.
      inv H2.
      crush.
    + remember (s :: b2) as bend.
      assert (exists y ys, bend = ys ++ [y]) by (apply list_snoc with (xs:=bend) (x:=s) (xs':=b2); crush).
      destruct H1; destruct H1.
      inv H1.
      rewrite H3 in *. clear H3.
      assert (b1 ++ << N k t; l ->> pfold f t' ks :: os1 >> :: x0 ++ [x] = (b1 ++ << N k t; l ->> pfold f t' ks :: os1 >> :: x0) ++ [x]) by crush.
      rewrite H1 in H2; clear H1.
      apply List.app_inj_tail in H2.
      destruct H2.
      subst.
      got.
      * instantiate (1:=C ((b1 ++ << N k t; l ->> pfold f (t_app (t_app f t) t') (remove Nat.eq_dec k ks) :: os1 >> :: x0) ++ [<< n1; os1' >>]) os0 (l0 ->>> final H :: rs0) term0).
        one_step. eapply S_Last; eauto; crush.
      * instantiate (1:=C (b1 ++ << N k t; l ->> pfold f (t_app (t_app f t) t') (remove Nat.eq_dec k ks) :: os1 >> :: x0 ++ [<< n1; os1' >>]) os0 (l0 ->>> final H :: rs0) term0).
        one_step; eapply S_PFold; eauto; crush.
      * crush.
  (* S_FusePMap *)
  - destruct n as [k' v'].
    tsod.
    + destruct os2.
      * crush.
      * inv Hsame5.
      {
      got.
      - instantiate (1:=C (b0 ++ << N k' v'; (l ->> pfold f (t_app (t_app f v') t') (remove Nat.eq_dec k' ks) :: os2) ++ l0 ->> pmap (pmap_compose f' f0) ks0 :: os3 >> :: b3) os0 (l' ->>> final H :: rs0) term0).
        one_step. eapply S_FusePMap; crush.
      - instantiate (1:=C (b0 ++ << N k' v'; (l ->> pfold f (t_app (t_app f v') t') (remove Nat.eq_dec k' ks) :: os2) ++ l0 ->> pmap (pmap_compose f' f0) ks0 :: os3 >> :: b3) os0 (l' ->>> final H :: rs0) term0).
        one_step. eapply S_PFold; crush.
      - crush.
      }
    + destruct Hfirst as [b' [b'' [b''']]].
      tu1.
      got.
      * instantiate (1:=C ((b' ++ << N k t; l ->> pfold f (t_app (t_app f t) t') (remove Nat.eq_dec k ks) :: os1 >> :: b'') ++ << N k' v'; os2 ++ l0 ->> pmap (pmap_compose f' f0) ks0 :: os3 >> :: b3) os0 (l' ->>> 0 :: rs0) term0).
        one_step; eapply S_FusePMap; eauto; crush.
      * instantiate (1:=C (b' ++ << N k t; l ->> pfold f (t_app (t_app f t) t') (remove Nat.eq_dec k ks) :: os1 >> :: b'' ++ << N k' v'; os2 ++ l0 ->> pmap (pmap_compose f' f0) ks0 :: os3 >> :: b3) os0 (l' ->>> 0 :: rs0) term0).
        eauto.
      * crush.
    + destruct Hsecond as [b' [b'' [b''']]].
      tu2.
      got.
      * instantiate (1:=C (b0 ++ << N k' v'; os2 ++ l0 ->> pmap (pmap_compose f' f0) ks0 :: os3 >> :: b'' ++ << N k t; l ->> pfold f (t_app (t_app f t) t') (remove Nat.eq_dec k ks) :: os1 >> :: b''') os0 (l' ->>> 0 :: rs0) term0).
        eauto.
      * instantiate (1:=C ((b0 ++ << N k' v'; os2 ++ l0 ->> pmap (pmap_compose f' f0) ks0 :: os3 >> :: b'') ++ << N k t; l ->> pfold f (t_app (t_app f t) t') (remove Nat.eq_dec k ks) :: os1 >> :: b''') os0 (l' ->>> 0 :: rs0) term0).
        one_step; eapply S_PFold; eauto; crush.
      * crush.
  (* S_Prop *)
  - destruct n1 as [k' v'].
    tsod.
    + simpl in *. inv Hsame5. crush.
    + destruct Hfirst as [b' [b'' [b''']]].
      tu1.
      got.
      * instantiate (1:=C ((b' ++ << N k t; l ->> pfold f (t_app (t_app f t) t') (remove Nat.eq_dec k ks) :: os1 >> :: b'') ++ << N k' v'; os2 >> :: << n2; os3 ++ [l0 ->> op] >> :: b3) os0 rs0 term0).
        one_step; eapply S_Prop; eauto; crush.
      * instantiate (1:=C (b' ++ << N k t; l ->> pfold f (t_app (t_app f t) t') (remove Nat.eq_dec k ks) :: os1 >> :: b'' ++ << N k' v'; os2 >> :: << n2; os3 ++ [l0 ->> op] >> :: b3) os0 rs0 term0).
        eauto.
      * crush.
    + destruct Hsecond as [b' [b'' [b''']]].
      tu2.
      destruct b''.
      * inv H1; simpl in *.
        got.
        { instantiate (1:=C (b0 ++ << N k' v'; os2 >> :: << N k t; (l ->> pfold f (t_app (t_app f t) t') (remove Nat.eq_dec k ks) :: os1) ++ [l0 ->> op] >> :: b3) os0 rs0 term0).
          one_step; eapply S_Prop; eauto. }
        { instantiate (1:=C ((b0 ++ [<< N k' v'; os2 >>]) ++ << N k t; (l ->> pfold f (t_app (t_app f t) t') (remove Nat.eq_dec k ks) :: os1) ++ [l0 ->> op] >> :: b3) os0 rs0 term0).
          one_step; eapply S_PFold; eauto; crush. }
        { crush. }
      * inv H1; simpl in *.
        got.
        { instantiate (1:=C (b0 ++ << N k' v'; os2 >> :: << n2; os3 ++ [l0 ->> op] >> :: b'' ++ << N k t; l ->> pfold f (t_app (t_app f t) t') (remove Nat.eq_dec k ks) :: os1 >> :: b''') os0 rs0 term0).
          one_step; eapply S_Prop; eauto; crush. }
        { instantiate (1:=C ((b0 ++ << N k' v'; os2 >> :: << n2; os3 ++ [l0 ->> op] >> :: b'') ++ << N k t; l ->> pfold f (t_app (t_app f t) t') (remove Nat.eq_dec k ks) :: os1 >> :: b''') os0 rs0 term0).
          one_step; eapply S_PFold; eauto; crush. }
        { crush. }
  (* S_LoadPFold *)
  - tsod.
    + destruct os2.
      * inv Hsame5; simpl in *.
        got.
        { instantiate (1:=C (b0 ++ << N k0 t0; l0 ->> pfold f0 (t_app (t_app f0 t0) t1') (remove Nat.eq_dec k0 ks0) :: os' >> :: b3) os0 rs0 term0).
          rewrite pfold_get with (rs:=rs0) (t'':=t1'); eauto. }
        { instantiate (1:=C (b0 ++ << N k0 t0; l0 ->> pfold f0 (t_app (t_app f0 t0) t1') (remove Nat.eq_dec k0 ks0) :: os' >> :: b3) os0 rs0 term0).
          one_step; eapply S_PFold; eauto. }
      { crush. }
      * inv Hsame5.
        got.
        { instantiate (1:=C (b0 ++ << N k0 t0; (l ->> pfold f (t_app (t_app f t0) t') (remove Nat.eq_dec k0 ks) :: os2) ++ l0 ->> pfold f0 t1' ks0 :: os' >> :: b3) os0 rs0 term0).
          one_step; eapply S_LoadPFold; eauto; crush. }
        { instantiate (1:=C (b0 ++ << N k0 t0; l ->> pfold f (t_app (t_app f t0) t') (remove Nat.eq_dec k0 ks) :: os2 ++ l0 ->> pfold f0 t1' ks0 :: os' >> :: b3) os0 rs0 term0).
          one_step; eapply S_PFold; eauto; crush. }
        { crush. }
    + destruct Hfirst as [b' [b'' [b''']]].
      tu1.
      got.
      * instantiate (1:=C ((b' ++ << N k t; l ->> pfold f (t_app (t_app f t) t') (remove Nat.eq_dec k ks) :: os1 >> :: b'') ++ << N k0 t0; os2 ++ l0 ->> pfold f0 t1' ks0 :: os' >> :: b3) os0 rs0 term0).
        one_step; eapply S_LoadPFold; eauto; crush.
      * instantiate (1:=C (b' ++ << N k t; l ->> pfold f (t_app (t_app f t) t') (remove Nat.eq_dec k ks) :: os1 >> :: b'' ++ << N k0 t0; os2 ++ l0 ->> pfold f0 t1' ks0 :: os' >> :: b3) os0 rs0 term0).
        eauto.
      * crush.
    + destruct Hsecond as [b' [b'' [b''']]].
      tu2.
      got.
      * instantiate (1:=C (b0 ++ << N k0 t0; os2 ++ l0 ->> pfold f0 t1' ks0 :: os' >> :: b'' ++ << N k t; l ->> pfold f (t_app (t_app f t) t') (remove Nat.eq_dec k ks) :: os1 >> :: b''') os0 rs0 term0).
        eauto.
      * instantiate (1:=C ((b0 ++ << N k0 t0; os2 ++ l0 ->> pfold f0 t1' ks0 :: os' >> :: b'') ++ << N k t; l ->> pfold f (t_app (t_app f t) t') (remove Nat.eq_dec k ks) :: os1 >> :: b''') os0 rs0 term0).
        one_step; eapply S_PFold; eauto; crush.
      * crush.
Unshelve.
auto.
auto.
Qed.
Hint Resolve lc_pfold.

Ltac tsod''' := match goal with
              | [H : ?b1 ++ <<N ?k ?t; ?os ++ ?os'''>> :: ?b2 = ?b3 ++ <<N ?k' ?t'; ?os' ++ ?os''>> :: ?b4 |- _] =>
                  eapply (@target_same_or_different _ b1 b2 b3 b4 k t k' t' (os ++ os''') (os' ++ os'')) in H; eauto; destruct H as [Hsame|Hwhich]; try destruct Hwhich as [Hfirst|Hsecond];
                  try (destruct Hsame as [Hsame1 Hsame2]; destruct Hsame2 as [Hsame2 Hsame3]; destruct Hsame3 as [Hsame3 Hsame4]; destruct Hsame4 as [Hsame4 Hsame5]; subst)
              end.

Ltac osod := match goal with
              | [H : ?os1 ++ ?lop :: ?os2 = ?os3 ++ ?lop' :: ?os4 |- _] =>
                  eapply (@op_same_or_different _ _ _ _ _ _ _ os1 os2 os3 os4) in H; eauto; destruct H as [Hsame|Hwhich]; try destruct Hwhich as [Hfirst|Hsecond];
                  try (destruct Hsame as [Hsame1 Hsame2]; destruct Hsame2 as [Hsame2 Hsame3]; destruct Hsame3 as [Hsame3 Hsame4]; destruct Hsame4 as [Hsame4 Hsame5]; subst)
              end.

Ltac ou1 := match goal with
            | [H : ?os1 ++ ?lop :: ?os2 = ?os3 ++ ?lop :: ?os' ++ ?lop' :: ?os4 |- _] =>
            eapply (@op_unique _ _ _ _ _ _ _ os1 os2 os3) in H; crush
            end;
            match goal with
            | [H : C _ _ _ _ = C _ _ _ _ |- _] => inv H
            end;
            match goal with
            | [H : _ ++ _ = _ ++ _ |- _] => apply List.app_inv_head in H; inv H
            end;
            match goal with
            | [H : ?os1 ++ ?lop' :: ?os' ++ ?lop :: ?os2 = ?os3 ++ ?lop :: ?os4 |- _] =>
              eapply (@op_unique _ _ _ _ _ _ _ (os1 ++ lop' :: os') os2 os3 os4) in H; eauto; crush
            end.

Ltac ou2 := match goal with
            | [H : ?os1 ++ ?lop :: ?os2 = ?os3 ++ ?lop' :: ?os' ++ ?lop :: ?os4 |- _] =>
            eapply (@op_unique _ _ _ _ _ _ _ os1 os2 (os3 ++ lop' :: os') os4) in H; crush
            end;
            match goal with
            | [H : C _ _ _ _ = C _ _ _ _ |- _] => inv H
            end;
            match goal with
            | [H : _ ++ _ = _ ++ _ |- _] => apply List.app_inv_head in H; inv H
            end;
            match goal with
            | [H : ?os1 ++ ?lop :: ?os' ++ ?lop' :: ?os2 = ?os3 ++ ?lop :: ?os4 |- _] =>
              eapply (@op_unique _ _ _ _ _ _ _ os1 (os' ++ lop' :: os2) os3 os4) in H; eauto; crush
            end.

Lemma lc_loadpfold :
  forall cx cy cz b1 b2 k t f t1 t1' l ks os os' term0 os0 rs0,
  well_typed cx ->
  cx = C (b1 ++ <<N k t; os ++ l ->> pfold f t1 ks :: os'>> :: b2) os0 rs0 term0 ->
  cy = C (b1 ++ <<N k t; os ++ l ->> pfold f t1' ks :: os'>> :: b2) os0 rs0 term0 ->
  cx --> cy ->
  cx --> cz ->
  C [] [] rs0 t1 --> C [] [] rs0 t1' ->
  cy -v cz.
Proof using.
  intros cx cy cz b1 b2 k t f t1 t1' l ks os os' term0 os0 rs0.
  intros WT Heqcx Heqcy cxcy cxcz.
  intros tt'.
  inversion cxcz; ssame; try solve [subst; eauto].
  (* S_App *)
  - gotw (C (b1 ++ << N k t; os ++ l ->> pfold f t1' ks :: os' >> :: b2) os1 rs (#[ x := v2] t12)); eauto.
  (* S_App1 *)
  - gotw (C (b1 ++ << N k t; os ++ l ->> pfold f t1' ks :: os' >> :: b2) (os1 ++ os'0) rs (t_app t1'0 t2)); eauto.
  (* S_App2 *)
  - gotw (C (b1 ++ << N k t; os ++ l ->> pfold f t1' ks :: os' >> :: b2) (os1 ++ os'0) rs (t_app v1 t2')); eauto.
  (* S_Empty *)
  - destruct b1; crush.
  (* S_First *)
  - destruct b1; inv H1; simpl in *.
    + gotw (C (<< N k t; (os ++ l ->> pfold f t1' ks :: os') ++ [l0 ->> op] >> :: b') os'0 rs term1); eauto.
      * rewrite <- List.app_assoc. rewrite <- List.app_comm_cons. eapply S_LoadPFold with (b1:=[]); eauto; crush.
    + got.
      * instantiate (1:=(C (<< n1; os2 ++ [l0 ->> op] >> :: b1 ++ << N k t; os ++ l ->> pfold f t1' ks :: os' >> :: b2) os'0 rs term1)).
        one_step; eapply S_First; eauto; crush.
      * instantiate (1:=(C (<< n1; os2 ++ [l0 ->> op] >> :: b1 ++ << N k t; os ++ l ->> pfold f t1' ks :: os' >> :: b2) os'0 rs term1)).
        one_step; eapply S_LoadPFold; eauto; crush.
      * crush.
  (* S_Add *)
  - got.
    + instantiate (1:=C (<< N k0 v; [] >> :: b1 ++ << N k t; os ++ l ->> pfold f t1' ks :: os' >> :: b2) os'0 (l0 ->>> final H :: rs) term1).
      one_step; eapply S_Add; eauto.
    + instantiate (1:=C ((<< N k0 v; [] >> :: b1) ++ << N k t; os ++ l ->> pfold f t1' ks :: os' >> :: b2) os'0 (l0 ->>> final H :: rs) term1).
      one_step; eapply S_LoadPFold; eauto; crush.
    + crush.
  (* S_PMap *)
  - tsod.
    + destruct os.
      * inv Hsame5.
      * inv Hsame5.
        got.
        { instantiate (1:=C (b0 ++ << N k0 (t_app f0 v); l0 ->> pmap f0 (remove Nat.eq_dec k0 ks0) :: os ++ l ->> pfold f t1' ks :: os' >> :: b3) os1 rs term1).
          one_step; eapply S_PMap; eauto; crush. }
        { instantiate (1:=C (b0 ++ << N k0 (t_app f0 v); (l0 ->> pmap f0 (remove Nat.eq_dec k0 ks0) :: os) ++ l ->> pfold f t1' ks :: os' >> :: b3) os1 rs term1).
          one_step; eapply S_LoadPFold; eauto; crush. }
        { crush. }
    + destruct Hfirst as [b' [b'' [b''']]].
      tu1.
      got.
      * instantiate (1:=C ((b' ++ << N k t; os ++ l ->> pfold f t1' ks :: os' >> :: b'') ++ << N k0 (t_app f0 v); l0 ->> pmap f0 (remove Nat.eq_dec k0 ks0) :: os1'' >> :: b3) os1 rs term1).
        one_step; eapply S_PMap; eauto; crush.
      * instantiate (1:=C ((b' ++ << N k t; os ++ l ->> pfold f t1' ks :: os' >> :: b'') ++ << N k0 (t_app f0 v); l0 ->> pmap f0 (remove Nat.eq_dec k0 ks0) :: os1'' >> :: b3) os1 rs term1).
        one_step; eapply S_LoadPFold; eauto; crush.
      * crush.
    + destruct Hsecond as [b' [b'' [b''']]].
      tu2.
      got.
      * instantiate (1:=C (b0 ++ << N k0 (t_app f0 v); l0 ->> pmap f0 (remove Nat.eq_dec k0 ks0) :: os1'' >> :: b'' ++ << N k t; os ++ l ->> pfold f t1' ks :: os' >> :: b''') os1 rs term1).
        one_step; eapply S_PMap; eauto; crush.
      * instantiate (1:=C ((b0 ++ << N k0 (t_app f0 v); l0 ->> pmap f0 (remove Nat.eq_dec k0 ks0) :: os1'' >> :: b'') ++ << N k t; os ++ l ->> pfold f t1' ks :: os' >> :: b''') os1 rs term1).
        one_step; eapply S_LoadPFold; eauto; crush.
      * crush.
  (* S_Last *)
  - destruct b2; simpl in *.
    + destruct os; simpl in *.
      * apply List.app_inj_tail in H2; destruct H2; inv H2.
        exfalso.
        apply frontend_no_value' in tt'.
        {
        destruct H.
        - crush.
        - destruct e. destruct e. destruct e. inversion e. subst.
          crush.
        }
      * apply List.app_inj_tail in H2; destruct H2; inv H2.
        got.
        { instantiate (1:=C (b0 ++ [<< N k t; os ++ l ->> pfold f t1' ks :: os' >>]) os1 (l0 ->>> final H :: rs) term1).
          one_step; eapply S_Last; eauto; crush. }
        { instantiate (1:=C (b0 ++ [<< N k t; os ++ l ->> pfold f t1' ks :: os' >>]) os1 (l0 ->>> final H :: rs) term1).
          one_step; eapply S_LoadPFold; eauto; crush. }
        { crush. }
    + remember (s :: b2) as bend.
      assert (exists y ys, bend = ys ++ [y]) by (apply list_snoc with (xs:=bend) (x:=s) (xs':=b2); crush).
      destruct H1; destruct H1.
      inv H1.
      rewrite H3 in *. clear H3.
      assert (b1 ++ << N k t; os ++ l ->> pfold f t1 ks :: os' >> :: x0 ++ [x] = (b1 ++ << N k t; os ++ l ->> pfold f t1 ks :: os' >> :: x0) ++ [x]) by crush.
      rewrite H1 in H2. clear H1.
      apply List.app_inj_tail in H2.
      destruct H2.
      subst.
      got.
      * instantiate (1:=C ((b1 ++ << N k t; os ++ l ->> pfold f t1' ks :: os' >> :: x0) ++ [<< n1; os1' >>]) os1 (l0 ->>> final H :: rs) term1).
        one_step; eapply S_Last; eauto; crush.
      * instantiate (1:=C ((b1 ++ << N k t; os ++ l ->> pfold f t1' ks :: os' >> :: x0) ++ [<< n1; os1' >>]) os1 (l0 ->>> final H :: rs) term1).
        one_step; eapply S_LoadPFold; eauto; crush.
      * crush.
  (* S_FusePMap *)
  - destruct n as [k' t']. tsod'''.
    + osod.
      * inv Hsame. destruct H2. crush.
      * destruct Hfirst as [os''0 [os'' [os''']]].
        ou1.
        got.
        { instantiate (1:=C (b0 ++ << N k' t'; (os''0 ++ l ->> pfold f t1' ks :: os'') ++ l0 ->> pmap (pmap_compose f' f0) ks0 :: os3 >> :: b3) os1 (l' ->>> 0 :: rs) term1).
          one_step; eapply S_FusePMap; eauto; crush. }
        { instantiate (1:=C (b0 ++ << N k' t'; (os''0 ++ l ->> pfold f t1' ks :: os'') ++ l0 ->> pmap (pmap_compose f' f0) ks0 :: os3 >> :: b3) os1 (l' ->>> 0 :: rs) term1).
          one_step; eapply S_LoadPFold; eauto; crush. }
        { crush. }
      * destruct Hsecond as [os''0 [os'' [os''']]].
        ou2.
        {
        destruct os''; inv H2; simpl in *.
        - got.
          + instantiate (1:=C (b0 ++ << N k' t'; os2 ++ l0 ->> pmap (pmap_compose f' f0) ks0 :: os'' ++ l ->> pfold f t1' ks :: os''' >> :: b3) os1 (l' ->>> 0 :: rs) term1).
            one_step; eapply S_FusePMap; eauto; crush.
          + instantiate (1:=C (b0 ++ << N k' t'; (os2 ++ l0 ->> pmap (pmap_compose f' f0) ks0 :: os'') ++ l ->> pfold f t1' ks :: os''' >> :: b3) os1 (l' ->>> 0 :: rs) term1).
            one_step; eapply S_LoadPFold; eauto; crush.
          + crush.
        }
    + destruct Hfirst as [b' [b'' [b''']]].
      tu1.
      got.
      * instantiate (1:=C ((b' ++ << N k t; os ++ l ->> pfold f t1' ks :: os' >> :: b'') ++ << N k' t'; os2 ++ l0 ->> pmap (pmap_compose f' f0) ks0 :: os3 >> :: b3) os1 (l' ->>> 0 :: rs) term1).
        one_step; eapply S_FusePMap; eauto; crush.
      * instantiate (1:=C ((b' ++ << N k t; os ++ l ->> pfold f t1' ks :: os' >> :: b'') ++ << N k' t'; os2 ++ l0 ->> pmap (pmap_compose f' f0) ks0 :: os3 >> :: b3) os1 (l' ->>> 0 :: rs) term1).
        one_step; eapply S_LoadPFold; eauto; crush.
      * crush.
    + destruct Hsecond as [b' [b'' [b''']]].
      tu2.
      got.
      * instantiate (1:=C (b0 ++ << N k' t'; os2 ++ l0 ->> pmap (pmap_compose f' f0) ks0 :: os3 >> :: b'' ++ << N k t; os ++ l ->> pfold f t1' ks :: os' >> :: b''') os1 (l' ->>> 0 :: rs) term1).
        one_step; eapply S_FusePMap; eauto; crush.
      * instantiate (1:=C ((b0 ++ << N k' t'; os2 ++ l0 ->> pmap (pmap_compose f' f0) ks0 :: os3 >> :: b'') ++ << N k t; os ++ l ->> pfold f t1' ks :: os' >> :: b''') os1 (l' ->>> 0 :: rs) term1).
        one_step; eapply S_LoadPFold; eauto; crush.
      * crush.
  (* S_Prop *)
  - destruct n1 as [k' t']. tsod.
    + destruct os; simpl in *.
      * inv Hsame5.
        got.
        { instantiate (1:=C (b0 ++ << N k' t'; os2 >> :: << n2; os3 ++ [l0 ->> pfold f t1' ks] >> :: b3) os1 rs term1).
          one_step; eapply S_Prop; eauto; crush. }
        { instantiate (1:=C ((b0 ++ [<< N k' t'; os2 >>]) ++ << n2; os3 ++ [l0 ->> pfold f t1' ks] >> :: b3) os1 rs term1).
          destruct n2. one_step; eapply S_LoadPFold with (b1:=(b0 ++ [<< N k' t'; os2 >>])) (os:=os3) (os':=[]); eauto; crush. }
        { crush. }
      * inv Hsame5.
        got.
        { instantiate (1:=C (b0 ++ << N k' t'; os ++ l ->> pfold f t1' ks :: os' >> :: << n2; os3 ++ [l0 ->> op] >> :: b3) os1 rs term1).
          one_step; eapply S_Prop; eauto; crush. }
        { instantiate (1:=C (b0 ++ << N k' t'; os ++ l ->> pfold f t1' ks :: os' >> :: << n2; os3 ++ [l0 ->> op] >> :: b3) os1 rs term1).
          one_step; eapply S_LoadPFold; eauto; crush. }
        { crush. }
    + destruct Hfirst as [b' [b'' [b''']]].
      tu1.
      got.
      * instantiate (1:=C ((b' ++ << N k t; os ++ l ->> pfold f t1' ks :: os' >> :: b'') ++ << N k' t'; os2 >> :: << n2; os3 ++ [l0 ->> op] >> :: b3) os1 rs term1).
        one_step; eapply S_Prop; eauto; crush.
      * instantiate (1:=C ((b' ++ << N k t; os ++ l ->> pfold f t1' ks :: os' >> :: b'') ++ << N k' t'; os2 >> :: << n2; os3 ++ [l0 ->> op] >> :: b3) os1 rs term1).
        one_step; eapply S_LoadPFold; eauto; crush.
      * crush.
    + destruct Hsecond as [b' [b'' [b''']]].
      tu2.
      destruct b''; inv H1; simpl in *.
      * got.
        { instantiate (1:=C (b0 ++ << N k' t'; os2 >> :: << N k t; (os ++ l ->> pfold f t1' ks :: os') ++ [l0 ->> op] >> :: b3) os1 rs term1).
          one_step; eapply S_Prop; eauto; crush. }
        { instantiate (1:=C ((b0 ++ [<< N k' t'; os2 >>]) ++ << N k t; os ++ l ->> pfold f t1' ks :: os' ++ [l0 ->> op] >> :: b3) os1 rs term1).
          one_step; eapply S_LoadPFold; eauto; crush. }
        { crush. }
      * got.
        { instantiate (1:=C (b0 ++ << N k' t'; os2 >> :: << n2; os3 ++ [l0 ->> op] >> :: b'' ++ << N k t; os ++ l ->> pfold f t1' ks :: os' >> :: b''') os1 rs term1).
          one_step; eapply S_Prop; eauto; crush. }
        { instantiate (1:=C ((b0 ++ << N k' t'; os2 >> :: << n2; os3 ++ [l0 ->> op] >> :: b'') ++ << N k t; os ++ l ->> pfold f t1' ks :: os' >> :: b''') os1 rs term1).
          one_step; eapply S_LoadPFold; eauto; crush. }
        { crush. }
  (* S_LoadPFold *)
  - tsod.
    + osod.
      * crush. inv H4.
        eapply frontend_deterministic with (os:=[]) (t':=t1'0) in tt'; eauto. crush.
        inversion WT. destruct H3. split; try split; crush.
        apply distinct_concat in H2.
        destruct H2.
        apply distinct_concat in H4.
        destruct H4.
        apply distinct_concat in H5.
        crush.
        exists Result, false.
        constructor; eauto. eapply graph_typing'; eauto.
      * destruct Hfirst as [os''0 [os'' [os''']]].
        ou1.
        got.
        { instantiate (1:=C (b0 ++ << N k0 t0; (os''0 ++ l ->> pfold f t1' ks :: os'') ++ l0 ->> pfold f0 t1'0 ks0 :: os'0 >> :: b3) os1 rs1 term1).
          one_step; eapply S_LoadPFold with (os:=(os''0 ++ l ->> pfold f t1' ks :: os'')); eauto; crush. }
        { instantiate (1:=C (b0 ++ << N k0 t0; (os''0 ++ l ->> pfold f t1' ks :: os'') ++ l0 ->> pfold f0 t1'0 ks0 :: os'0 >> :: b3) os1 rs1 term1).
          one_step; eapply S_LoadPFold; eauto; crush. }
        { crush. }
      * destruct Hsecond as [os''0 [os'' [os''']]].
        ou2.
        got.
        { instantiate (1:=C (b0 ++ << N k0 t0; os2 ++ l0 ->> pfold f0 t1'0 ks0 :: os'' ++ l ->> pfold f t1' ks :: os''' >> :: b3) os1 rs1 term1).
          one_step; eapply S_LoadPFold; eauto; crush. }
        { instantiate (1:=C (b0 ++ << N k0 t0; (os2 ++ l0 ->> pfold f0 t1'0 ks0 :: os'') ++ l ->> pfold f t1' ks :: os''' >> :: b3) os1 rs1 term1).
          one_step; eapply S_LoadPFold with (b1:=b0) (t1':=t1') (os':=os''') (b2:=b3) (k:=k0) (f:=f) (l:=l) (ks:=ks) (t:=t0) (os:=(os2 ++ l0 ->> pfold f0 t1'0 ks0 :: os'')); eauto; crush. }
        { crush. }
    + destruct Hfirst as [b' [b'' [b''']]].
      tu1.
      got.
      * instantiate (1:=C ((b' ++ << N k t; os ++ l ->> pfold f t1' ks :: os' >> :: b'') ++ << N k0 t0; os2 ++ l0 ->> pfold f0 t1'0 ks0 :: os'0 >> :: b3) os1 rs1 term1).
        one_step; eapply S_LoadPFold with (b1:=(b' ++ << N k t; os ++ l ->> pfold f t1' ks :: os' >> :: b'')); eauto; crush.
      * instantiate (1:=C (b' ++ << N k t; os ++ l ->> pfold f t1' ks :: os' >> :: b'' ++ << N k0 t0; os2 ++ l0 ->> pfold f0 t1'0 ks0 :: os'0 >> :: b3) os1 rs1 term1).
        one_step; eapply S_LoadPFold; eauto; crush.
      * crush.
    + destruct Hsecond as [b' [b'' [b''']]].
      tu2.
      got.
      * instantiate (1:=C (b0 ++ << N k0 t0; os2 ++ l0 ->> pfold f0 t1'0 ks0 :: os'0 >> :: b'' ++ << N k t; os ++ l ->> pfold f t1' ks :: os' >> :: b''') os1 rs1 term1).
        one_step; eapply S_LoadPFold; eauto; crush.
      * instantiate (1:=C ((b0 ++ << N k0 t0; os2 ++ l0 ->> pfold f0 t1'0 ks0 :: os'0 >> :: b'') ++ << N k t; os ++ l ->> pfold f t1' ks :: os' >> :: b''') os1 rs1 term1).
        one_step; eapply S_LoadPFold with (k:=k) (t:=t) (t1':=t1') (os:=os) (l:=l) (f:=f) (ks:=ks) (b2:=b''') (os':=os') (b1:=(b0 ++ << N k0 t0; os2 ++ l0 ->> pfold f0 t1'0 ks0 :: os'0 >> :: b'')); eauto; crush.
      * crush.
Unshelve.
auto.
auto.
auto.
auto.
auto.
auto.
Qed.
Hint Resolve lc_loadpfold.

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
  - gotw (C (<< N k v; [] >> :: b1 ++ << n1; os1 >> :: << n2; os2 ++ [l ->> op] >> :: b2) os' (l0 ->>> final H :: rs0) term0); eauto.
    repeat (rewrite List.app_comm_cons).
    eauto.
  (* S_PMap *)
  - destruct n1.
    eapply target_same_or_different with (b1:=b1) (b2:=<< n2; os2 >> :: b2) (b3:=b0) (b4:=b3) (k:=n) (v:=t) (k':=k) (v':=v) in H1; eauto.
    destruct H1; try destruct H0.
    (* Same target *)
    + destruct H1. destruct H2. destruct H3. subst.
      inv H4.
      crush.
    (* First first *)
    + destruct H0. destruct H0. destruct H0.
      eapply target_unique with (b1:=b1) (b2:=<< n2; os2 >> :: b2) (b3:=x) (b4:=x0 ++ << N k v; l0 ->> pmap f ks :: os1'' >> :: x1) in H0; crush.
      rewrite H2 in *.
      destruct x0.
      * inv H.
        simpl in *.
        eapply target_unique with (b1:=x ++ [<< N n t; l ->> op :: os1 >>]) (b2:=x1) (b3:=b0) (b4:=b3) in H1; eauto; crush.
        inv H2.
        {
          got.
          - instantiate (1:=C ((x ++ [<< N n t; os1 >>]) ++ << N k (t_app f v); l0 ->> pmap f (remove Nat.eq_dec k ks) :: os1'' ++ [l ->> op] >> :: b3) os0 rs0 term0).
            one_step. eapply S_PMap; crush.
          - instantiate (1:=C (x ++ << N n t; os1 >> :: << N k (t_app f v); (l0 ->> pmap f (remove Nat.eq_dec k ks) :: os1'') ++ [l ->> op] >> :: b3) os0 rs0 term0).
            one_step. eapply S_Prop; crush.
          - crush.
        }
      * inv H2.
        inv H.
        eapply target_unique with (b1:=x ++ << N n t; l ->> op :: os1 >> :: << n2; os2 >> :: x0) (b2:=x1) (b3:=b0) (b4:=b3) in H1; eauto; crush.
        {
          got.
          - instantiate (1:=C ((x ++ << N n t; os1 >> :: << n2; os2 ++ [l ->> op] >> :: x0) ++ << N k (t_app f v); l0 ->> pmap f (remove Nat.eq_dec k ks) :: os1'' >> :: b3) os0 rs0 term0).
            one_step. eapply S_PMap; crush.
          - instantiate (1:=C (x ++ << N n t; os1 >> :: << n2; os2 ++ [l ->> op] >> :: x0 ++ << N k (t_app f v); l0 ->> pmap f (remove Nat.eq_dec k ks) :: os1'' >> :: b3) os0 rs0 term0).
            one_step. eapply S_Prop; crush.
          - crush.
        }
    (* First second *)
    + destruct H0. destruct H0. destruct H0.
      eapply target_unique with (b1:=b1) (b2:=<< n2; os2 >> :: b2) (b3:=x ++ << N k v; l0 ->> pmap f ks :: os1'' >> :: x0) (b4:=x1) in H0; eauto; crush.
      inv H.
      eapply target_unique with (b1:=x) (b2:=x0 ++ << N n t; l ->> op :: os1 >> :: << n2; os2 >> :: b2) (b3:=b0) (b4:=b3) in H1; eauto; crush.
      got.
      * instantiate (1:= C (b0 ++ << N k (t_app f v); l0 ->> pmap f (remove Nat.eq_dec k ks) :: os1'' >> :: x0 ++ << N n t; os1 >> :: << n2; os2 ++ [l ->> op] >> :: b2) os0 rs0 term0).
        one_step. eapply S_PMap; crush.
      * instantiate (1:= C ((b0 ++ << N k (t_app f v); l0 ->> pmap f (remove Nat.eq_dec k ks) :: os1'' >> :: x0) ++ << N n t; os1 >> :: << n2; os2 ++ [l ->> op] >> :: b2) os0 rs0 term0).
        one_step. eapply S_Prop; crush.
      * crush.
  (* S_Last *)
  - destruct b2; rename H into Hnot; rename H2 into H1; rename H0 into H.
    + assert (b1 ++ [<< n1; l ->> op :: os1 >>; << n2; os2 >>] = b1 ++ [<< n1; l ->> op :: os1 >>] ++ [<< n2; os2 >>]) by crush.
      rewrite H0 in H1; clear H0.
      rewrite List.app_assoc in H1.
      apply List.app_inj_tail in H1.
      destruct H1.
      subst.
      inv H1.
      got.
      * instantiate (1:=C ((b1 ++ [<< n1; os1 >>]) ++ [<< n0; os1' ++ [l ->> op] >>]) os0 (l0 ->>> final Hnot :: rs0) term0).
        one_step. eapply S_Last with (b1:=b1 ++ [<< n1; os1 >>]) (os1:=(l0 ->> op0 :: os1') ++ [l ->> op]); eauto.
        simpl.
        rewrite List.app_comm_cons.
        crush.
      * instantiate (1:=C (b1 ++ << n1; os1 >> :: [<< n0; os1' ++ [l ->> op] >>]) os0 (l0 ->>> final Hnot :: rs0) term0).
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
      gotw (C (b1 ++ << n1; os1 >> :: << n2; os2 ++ [l ->> op] >> :: x0 ++ [<< n0;  os1' >>]) os0 (l0 ->>> final Hnot :: rs0) term0); eauto.
      * assert (forall x, b1 ++ << n1; os1 >> :: << n2; os2 ++ [l ->> op] >> :: x0 ++ x = (b1 ++ << n1; os1 >> :: << n2; os2 ++ [l ->> op] >> :: x0) ++ x) by crush.
        repeat (rewrite H0). clear H0.
        eauto.
      * rewrite <- List.app_assoc.
        eauto.
  (* S_FusePMap *)
  - destruct n1 as [k v].
    destruct n as [k' v'].
    rename H into Hnot.
    rename H0 into H.
    rename H2 into H1.
    eapply target_same_or_different with (b1:=b1) (b2:=<< n2; os2 >> :: b2) (b3:=b0) (b4:=b3) (k:=k) (v:=v) (k':=k') (v':=v') in H1; eauto.
    destruct H1; try destruct H0.
    (* Same target *)
    + destruct H1. destruct H2. destruct H3. subst.
      destruct os3.
      * simpl in *.
        inv H4.
        {
        got.
        - instantiate (1:=C (b0 ++ << N k' v'; os4 >> :: << n2; os2 ++ [l0 ->> pmap (pmap_compose f' f) ks] >> :: b2) os0 (l' ->>> 0 :: rs0) term0).
          apply ex_intro with 2.
          eapply Step.
          instantiate (1:=C (b0 ++ << N k' v'; os4 >> :: << n2; (os2 ++ [l0 ->> pmap f ks]) ++ [l' ->> pmap f' ks] >> :: b2) os0 rs0 term0).
          eapply S_Prop; crush.
          apply one_star.
          assert ((os2 ++ [l0 ->> pmap f ks]) ++ [l' ->> pmap f' ks] = os2 ++ [l0 ->> pmap f ks] ++ [l' ->> pmap f' ks]) by crush.
          rewrite H0. clear H0.
          assert (forall x, b0 ++ << N k' v'; os4 >> :: x = (b0 ++ [<< N k' v'; os4 >>]) ++ x) by crush.
          rewrite H0. clear H0.
          assert (b0 ++ << N k' v'; os4 >> :: << n2; os2 ++ [l0 ->> pmap (pmap_compose f' f) ks] >> :: b2 = (b0 ++ [<< N k' v'; os4 >>]) ++ << n2; os2 ++ [l0 ->> pmap (pmap_compose f' f) ks] >> :: b2) by crush.
          rewrite H0. clear H0.
          eapply S_FusePMap; crush.
        - instantiate (1:=C (b0 ++ << N k' v'; os4 >> :: << n2; os2 ++ [l0 ->> pmap (pmap_compose f' f) ks] >> :: b2) os0 (l' ->>> 0 :: rs0) term0).
          one_step. eapply S_Prop; crush.
        - crush.
        }
      * simpl in *.
        inv H4.
        {
        got.
        - instantiate (1:=C (b0 ++ << N k' v'; os3 ++ l0 ->> pmap (pmap_compose f' f) ks :: os4 >> :: << n2; os2 ++ [l ->> op] >> :: b2) os0 (l' ->>> 0 :: rs0) term0).
          one_step. eapply S_FusePMap; crush.
        - instantiate (1:=C (b0 ++ << N k' v'; os3 ++ l0 ->> pmap (pmap_compose f' f) ks :: os4 >> :: << n2; os2 ++ [l ->> op] >> :: b2) os0 (l' ->>> 0 :: rs0) term0).
          one_step. eapply S_Prop; crush.
        - crush.
        }
    (* First first *)
    + destruct H0. destruct H0. destruct H0.
      destruct x0; simpl in *.
      * eapply target_unique with (b1:=b1) (b2:=<< n2; os2 >> :: b2) (b3:=x) (b4:=<< N k' v'; os3 ++ l0 ->> pmap f ks :: l' ->> pmap f' ks :: os4 >> :: x1) in H0; eauto; crush.
        inv H2.
        inv H.
        eapply target_unique with (b1:=x ++ [<< N k v; l ->> op :: os1 >>]) (b2:=x1) (b3:=b0) (b4:=b3) in H1; eauto; crush.
        {
        got.
        - instantiate (1:=C ((x ++ [<< N k v; os1 >>]) ++ << N k' v'; os3 ++ l0 ->> pmap (pmap_compose f' f) ks :: os4 ++ [l ->> op] >> :: b3) os0 (l' ->>> 0 :: rs0) term0).
          one_step. eapply S_FusePMap; crush.
        - instantiate (1:=C (x ++ << N k v; os1 >> :: << N k' v'; (os3 ++ l0 ->> pmap (pmap_compose f' f) ks :: os4) ++ [l ->> op] >> :: b3) os0 (l' ->>> 0 :: rs0) term0).
          one_step. eapply S_Prop; crush.
        - crush.
        }
      * eapply target_unique with (b1:=b1) (b2:=<< n2; os2 >> :: b2) (b3:=x) (b4:=s :: x0 ++ << N k' v'; os3 ++ l0 ->> pmap f ks :: l' ->> pmap f' ks :: os4 >> :: x1) in H0; eauto; crush.
        inv H.
        eapply target_unique with (b1:=x ++ << N k v; l ->> op :: os1 >> :: << n2; os2 >> :: x0) (b2:=x1) (b3:=b0) (b4:=b3) in H1; eauto; crush.
        {
        got.
        - instantiate (1:=C ((x ++ << N k v; os1 >> :: << n2; os2 ++ [l ->> op] >> :: x0) ++ << N k' v'; os3 ++ l0 ->> pmap (pmap_compose f' f) ks :: os4 >> :: b3) os0 (l' ->>> 0 :: rs0) term0).
          one_step. eapply S_FusePMap; crush.
        - instantiate (1:=C (x ++ << N k v; os1 >> :: << n2; os2 ++ [l ->> op] >> :: x0 ++ << N k' v'; os3 ++ l0 ->> pmap (pmap_compose f' f) ks :: os4 >> :: b3) os0 (l' ->>> 0 :: rs0) term0).
          one_step. eapply S_Prop; crush.
        - crush.
        }
    (* First second *)
    + destruct H0. destruct H0. destruct H0.
      eapply target_unique with (b1:=b1) (b2:=<< n2; os2 >> :: b2) (b3:=x ++ << N k' v'; os3 ++ l0 ->> pmap f ks :: l' ->> pmap f' ks :: os4 >> :: x0) (b4:=x1) in H0; eauto; crush.
      inv H.
      eapply target_unique with (b1:=x) (b2:=x0 ++ << N k v; l ->> op :: os1 >> :: << n2; os2 >> :: b2) (b3:=b0) (b4:=b3) in H1; eauto; crush.
      got.
      * instantiate (1:=C (b0 ++ << N k' v'; os3 ++ l0 ->> pmap (pmap_compose f' f) ks :: os4 >> :: x0 ++ << N k v; os1 >> :: << n2; os2 ++ [l ->> op] >> :: b2) os0 (l' ->>> 0 :: rs0) term0).
        one_step. eapply S_FusePMap; crush.
      * instantiate (1:=C ((b0 ++ << N k' v'; os3 ++ l0 ->> pmap (pmap_compose f' f) ks :: os4 >> :: x0) ++ << N k v; os1 >> :: << n2; os2 ++ [l ->> op] >> :: b2) os0 (l' ->>> 0 :: rs0) term0).
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
  (* S_PMap *)
  + match_app2.
    * eapply S_PMap; crush.
    * eapply S_App2; crush.
  (* S_Last *)
  + match_app2.
    * eapply S_Last; crush.
    * eapply S_App2; crush.
  (* S_FuseInc *)
  + match_app2.
    * eapply S_FusePMap; crush.
    * eapply S_App2; crush.
Unshelve.
auto.
auto.
Qed.
Hint Resolve lc_app2.

Ltac match_app :=
  match goal with
  | [H : _ --> C ?b ?os ?rs (t_app ?t1 ?t2) |- _] => match goal with
                                      | [H': C ?b' ?os' ?rs' ?t'' --> C ?b' ?os' ?rs' ?t' |- _] => gotw (C b os rs t'); simpl; eauto; trouble_makers
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
Unshelve.
auto.
auto.
Qed.
Hint Resolve lc_app.

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
  (* S_PMap *)
  + match_app1.
    * eapply S_PMap; eauto.
    * eapply S_App1; eauto.
  (* S_Last *)
  + match_app1.
    * eapply S_Last; eauto.
    * eapply S_App1; eauto.
  (* S_FusePMap *)
  + match_app1.
    * eapply S_FusePMap; eauto.
    * eapply S_App1; eauto.
Unshelve.
auto.
auto.
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
  (* S_PMap *)
  - destruct b1; simpl in *.
    * gotw (C (<< N k (t_app f v); l0 ->> pmap f (remove Nat.eq_dec k ks) :: os1'' ++ [l ->> op] >> :: b2)  os' rs0 term1).
      { inv H1; eapply S_PMap with (b1:=[]); crush. }
      { inv H1; eapply S_First with (os1:=l0 ->> pmap f (remove Nat.eq_dec k ks) :: os1''); crush. }
      { crush. }
    * gotw (C (<< n1; os1 ++ [l ->> op] >> :: b1 ++ << N k (t_app f v); l0 ->> pmap f (remove Nat.eq_dec k ks) :: os1'' >> :: b2) os' rs0 term1).
      { inv H1. eapply S_PMap with (b1:=<< n1; os1 ++ [l ->> op] >> :: b1); crush. }
      { inv H1. eapply S_First; crush. }
      { crush. }
  (* S_Last *)
  - crush.
    {
    destruct b1; eapply ex_intro; eapply ex_intro; intros.
    (* b1 = [] *)
    - split; try split.
      + simpl in *. instantiate (1 := C [<< n1; os1' ++ [l ->> op]>>] os' (l0 ->>> final H :: rs0) term1).
        inversion H2.
        one_step; eapply S_Last with (b1 := []); crush.
      + simpl in *. instantiate (1 := C [<< n1; os1' ++ [l ->> op]>>] os' (l0 ->>> final H :: rs0) term1).
        inversion H2.
        one_step; eapply S_First; crush.
      + crush.
    (* b1 != [] *)
    - split; try split.
      + instantiate (1 := C (<< n1; os1 ++ [l ->> op] >> :: b1 ++ [<< n0; os1' >>]) os' (l0 ->>> final H :: rs0) term1).
        inversion H2.
        one_step; eapply S_Last with (b1 := << n1; os1 ++ [l ->> op] >> :: b1); crush.
      + instantiate (1 := C (<< n1; os1 ++ [l ->> op] >> :: b1 ++ [<< n0; os1' >>]) os' (l0 ->>> final H :: rs0) term1).
        inversion H2.
        one_step; eapply S_First; crush.
      + crush.
    }
  (* S_FuseInc *)
  - destruct b1; simpl in *.
    (* b1 = [] *)
    * gotw (C (<< n; os0 ++ l0 ->> pmap (pmap_compose f' f) ks :: os2 ++ [l ->> op] >> :: b2) os' (l' ->>> 0 :: rs0) term1).
      { inv H2. eapply S_FusePMap with (b1:=[]); crush. }
      { inv H2. assert (os0 ++ l0 ->> pmap (pmap_compose f' f) ks :: os2 ++ [l ->> op] = (os0 ++ l0 ->> pmap (pmap_compose f' f) ks :: os2) ++ [l ->> op]) by crush. rewrite H1. eapply S_First; crush. }
      { crush. }
    (* b1 != [] *)
    * gotw (C (<< n1; os1 ++ [l ->> op] >> :: b1 ++ << n; os0 ++ l0 ->> pmap (pmap_compose f' f) ks :: os2 >> :: b2) os' (l' ->>> 0 :: rs0) term1).
      { inv H2. eapply S_FusePMap with (b1:=<< n1; os1 ++ [l ->> op] >> :: b1); crush. }
      { inv H2. eapply S_First; crush. }
      { crush. }
Unshelve.
auto.
auto.
Qed.
Hint Resolve lc_first.

Axiom pmap_compose_assoc : forall f f' t,
  t_app f (t_app f' t) = t_app (pmap_compose f f') t.

Lemma lc_pmap :
  forall cx cy cz rs term0 l f ks os1'' b1 b2 k os v,
  well_typed cx ->
  cx = C (b1 ++ << N k v; l ->> pmap f ks :: os1'' >> :: b2) os rs term0 ->
  cy = C (b1 ++ << N k (t_app f v); l ->> pmap f (remove Nat.eq_dec k ks) :: os1'' >> :: b2) os rs term0 ->
  In k ks ->
  cx --> cy ->
  cx --> cz ->
  cy -v cz.
Proof using.
  intros cx cy cz rs term0 l f ks os1'' b1 b2 k os v WT Heqcx Heqcy HIn cxcy cxcz.
  inversion cxcz; ssame; try solve [subst; eauto].
  (* S_Empty *)
  - destruct b1; crush.
  (* S_Add *)
  - gotw (C (<< N k0 v0; [] >> :: b1 ++ << N k (t_app f v); l ->> pmap f (remove Nat.eq_dec k ks) :: os1'' >> :: b2) os' (l0 ->>> final H :: rs0) term1).
    * eapply S_Add; eauto.
    * eapply S_PMap with (b1:=<< N k0 v0; [] >> :: b1); crush.
    * crush.
  (* S_PMap *)
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
        apply target_unique with (os:=l ->> pmap f ks :: os1'') (k:=k) (v:=v) (b1:=b1) (b2:=b2) (b3:=x) (b4:=x0 ++ << N k0 v0; l0 ->> pmap f0 ks0 :: os1''0 >> :: x1) (os0:=os0) (rs0:=rs0) (t0:=term1) (b:=b1 ++ << N k v; l ->> pmap f ks :: os1'' >> :: b2) in H0; crush.
        inv H.
        apply target_unique with (os:=l0 ->> pmap f0 ks0 :: os1''0) (k:=k0) (v:=v0) (b1:=x ++ << N k v; l ->> pmap f ks :: os1'' >> :: x0) (b2:=x1) (b3:=b3) (b4:=b4) (os0:=os0) (rs0:=rs0) (t0:=term1) (b:=x ++ << N k v; l ->> pmap f ks :: os1'' >> :: x0 ++ << N k0 v0; l0 ->> pmap f0 ks0 :: os1''0 >> :: x1) in H1; crush.
        got.
        * instantiate (1:=C ((x ++ << N k (t_app f v); l ->> pmap f (remove Nat.eq_dec k ks) :: os1'' >> :: x0) ++ << N k0 (t_app f0 v0); l0 ->> pmap f0 (remove Nat.eq_dec k0 ks0) :: os1''0 >> :: b4) os0 rs0 term1).
          one_step. eapply S_PMap; crush.
        * instantiate (1:=C (x ++ << N k (t_app f v); l ->> pmap f (remove Nat.eq_dec k ks) :: os1'' >> :: x0 ++ << N k0 (t_app f0 v0); l0 ->> pmap f0 (remove Nat.eq_dec k0 ks0) :: os1''0 >> :: b4) os0 rs0 term1).
          one_step. eapply S_PMap; crush.
        * crush.
      (* First second *)
      + destruct H0; destruct H0; destruct H0.
        apply target_unique with (os:=l ->> pmap f ks :: os1'') (k:=k) (v:=v) (b1:=b1) (b2:=b2) (b3:=x ++ << N k0 v0; l0 ->> pmap f0 ks0 :: os1''0 >> :: x0) (b4:=x1) (os0:=os0) (rs0:=rs0) (t0:=term1) (b:=b1 ++ << N k v; l ->> pmap f ks :: os1'' >> :: b2) in H0; crush.
        inv H.
        eapply target_unique with (os:=l0 ->> pmap f0 ks0 :: os1''0) (k:=k0) (v:=v0) (b1:=x) (b2:=x0 ++ << N k v; l ->> pmap f ks :: os1'' >> :: x1) (b3:=b3) (b4:=b4) (os0:=os0) (rs0:=rs0) (t0:=term1) in H1; eauto.
        got.
        * instantiate (1:=C (b3 ++ << N k0 (t_app f0 v0); l0 ->> pmap f0 (remove Nat.eq_dec k0 ks0) :: os1''0 >> :: x0 ++ << N k (t_app f v); l ->> pmap f (remove Nat.eq_dec k ks) :: os1'' >> :: x1) os0 rs0 term1).
          one_step. eapply S_PMap; crush.
        * instantiate (1:=C ((b3 ++ << N k0 (t_app f0 v0); l0 ->> pmap f0 (remove Nat.eq_dec k0 ks0) :: os1''0 >> :: x0) ++ << N k (t_app f v); l ->> pmap f (remove Nat.eq_dec k ks) :: os1'' >> :: x1) os0 rs0 term1).
          one_step. eapply S_PMap; crush.
        * crush.
    }
  (* S_Last *)
  - rename H into Hnot.
    rename H0 into H.
    rename H2 into H1.
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
      assert (b1 ++ << N k v; l ->> pmap f ks :: os1'' >> :: x0 ++ [x]=(b1 ++ << N k v; l ->> pmap f ks :: os1'' >> :: x0) ++ [x]) by crush.
      rewrite H0 in H1.
      apply List.app_inj_tail in H1.
      destruct H1.
      rewrite H0 in *.
      subst.
      got.
      + instantiate (1:=C ((b1 ++ << N k (t_app f v); l ->> pmap f (remove Nat.eq_dec k ks) :: os1'' >> :: x0) ++ [<< n1; os1' >>]) os0 (l0 ->>> final Hnot :: rs0) term1).
        one_step. eapply S_Last; crush.
      + instantiate (1:=C (b1 ++ << N k (t_app f v); l ->> pmap f (remove Nat.eq_dec k ks) :: os1'' >> :: x0 ++ [<< n1; os1' >>]) os0 (l0 ->>> final Hnot :: rs0) term1).
        one_step. eapply S_PMap; crush.
      + crush.
    }
  (* S_FusePMap *)
  - rename H into Hnot.
    rename H0 into H.
    rename H2 into H1.
    destruct n.
    eapply target_same_or_different with (b1:=b1) (b2:=b2) (b3:=b0) (b4:=b3) (k:=k) (v:=v) (k':=n) (v':=t) in H1; eauto.
    destruct H1; try destruct H0.
    (* Same target *)
    + destruct H1. destruct H2. destruct H3. subst.
      destruct os1.
      * simpl in *.
        inv H4.
        {
        destruct b3.
        - got.
          + instantiate (1:=C (b0 ++ [<< N n (t_app f' (t_app f0 t)); os2 >>]) os0 (l' ->>> final _ :: l0 ->>> 0 :: rs0) term1).
            apply ex_intro with 3.
            eapply Step.
            instantiate (1:=C (b0 ++ [<< N n (t_app f0 t); l' ->> pmap f' ks0 :: os2 >>]) os0 (l0 ->>> _ :: rs0) term1).
            eapply S_Last; crush.
            apply List.remove_In in H0. assumption.
            eapply Step.
            instantiate (1:=C (b0 ++ [<< N n (t_app f' (t_app f0 t)); l' ->> pmap f' (remove Nat.eq_dec n ks0) :: os2 >>]) os0 (l0 ->>> final _ :: rs0) term1).
            eapply S_PMap; crush.
            instantiate (1:=Hnot); crush.
            apply one_star.
            eapply S_Last with (b:=b0 ++ [<< N n (t_app f' (t_app f0 t)); l' ->> pmap f' (remove Nat.eq_dec n ks0) :: os2 >>]); eauto.
            crush.
            apply List.remove_In in H0. assumption.
          + instantiate (1:=C (b0 ++ [<< N n (t_app (pmap_compose f' f0) t); os2 >>]) os0 (l0 ->>> final _ :: l' ->>> 0 :: rs0) term1).
            apply ex_intro with 2.
            eapply Step.
            eapply S_PMap; crush.
            apply one_star.
            eapply S_Last with (op:=pmap (pmap_compose f' f0) (remove Nat.eq_dec n ks0)); crush.
            apply List.remove_In in H0. assumption.
          + rewrite pmap_compose_assoc; eauto.
        - destruct s.
          got.
          + instantiate (1:=C (b0 ++ << N n (t_app f' (t_app f0 t)); os2 >> :: << n0; l ++ [l0 ->> pmap (pmap_compose f' f0) (remove Nat.eq_dec n ks0)] >> :: b3) os0 (l' ->>> final _ :: rs0) term1).
            apply ex_intro with 4.
            eapply Step.
            instantiate (1:=C (b0 ++ << N n (t_app f0 t); l' ->> pmap f' ks0 :: os2 >> :: << n0; l ++ [l0 ->> pmap f0 (remove Nat.eq_dec n ks0)] >> :: b3) os0 rs0 term1).
            eapply S_Prop; crush.
            apply List.remove_In in H0. assumption.
            eapply Step.
            instantiate (1:=C (b0 ++ << N n (t_app f' (t_app f0 t)); l' ->> pmap f' (remove Nat.eq_dec n ks0) :: os2 >> :: << n0; l ++ [l0 ->> pmap f0 (remove Nat.eq_dec n ks0)] >> :: b3) os0 rs0 term1).
            eapply S_PMap; crush.
            eapply Step.
            instantiate (1:=C (b0 ++ << N n (t_app f' (t_app f0 t)); os2 >> :: << n0; (l ++ [l0 ->> pmap f0 (remove Nat.eq_dec n ks0)]) ++ [l' ->> pmap f' (remove Nat.eq_dec n ks0)] >> :: b3) os0 rs0 term1).
            eapply S_Prop; crush.
            apply List.remove_In in H0. assumption.
            apply one_star.
            assert (b0 ++ << N n (t_app f' (t_app f0 t)); os2 >> :: << n0; (l ++ [l0 ->> pmap f0 (remove Nat.eq_dec n ks0)]) ++ [l' ->> pmap f' (remove Nat.eq_dec n ks0)] >> :: b3 = (b0 ++ [<< N n (t_app f' (t_app f0 t)); os2 >>]) ++ << n0; l ++ l0 ->> pmap f0 (remove Nat.eq_dec n ks0) :: l' ->> pmap f' (remove Nat.eq_dec n ks0) :: [] >> :: b3) by crush.
            rewrite H0.
            assert (b0 ++ << N n (t_app f' (t_app f0 t)); os2 >> :: << n0; l ++ [l0 ->> pmap (pmap_compose f' f0) (remove Nat.eq_dec n ks0)] >> :: b3 = (b0 ++ [<< N n (t_app f' (t_app f0 t)); os2 >>]) ++ << n0; l ++ [l0 ->> pmap (pmap_compose f' f0) (remove Nat.eq_dec n ks0)] >> :: b3) by crush.
            rewrite H1.
            eapply S_FusePMap; crush.
          + instantiate (1:=C (b0 ++ << N n (t_app f' (t_app f0 t)); os2 >> :: << n0; l ++ [l0 ->> pmap (pmap_compose f' f0) (remove Nat.eq_dec n ks0)] >> :: b3) os0 (l' ->>> 0 :: rs0) term1).
            apply ex_intro with 2.
            eapply Step.
            instantiate (1:=C (b0 ++ << N n (t_app f' (t_app f0 t)); l0 ->> pmap (pmap_compose f' f0) (remove Nat.eq_dec n ks0) :: os2 >> :: << n0; l >> :: b3) os0 (l' ->>> 0 :: rs0) term1).
            eapply S_PMap; crush.
            rewrite pmap_compose_assoc; eauto.
            apply one_star.
            eapply S_Prop; crush.
            apply List.remove_In in H0. assumption.
          + crush.
        }
      * inv H4.
        {
          got.
          * instantiate (1:= C (b0 ++ << N n (t_app f t); (l ->> pmap f (remove Nat.eq_dec n ks) :: os1) ++ l0 ->> pmap (pmap_compose f' f0) ks0 :: os2 >> :: b3) os0 (l' ->>> final _ :: rs0) term1).
            one_step. eapply S_FusePMap; crush.
          * instantiate (1:= C (b0 ++ << N n (t_app f t); l ->> pmap f (remove Nat.eq_dec n ks) :: os1 ++ l0 ->> pmap (pmap_compose f' f0) ks0 :: os2 >> :: b3) os0 (l' ->>> 0 :: rs0) term1).
            one_step. eapply S_PMap; crush.
          * crush.
        }
    (* First first *)
    + destruct H0. destruct H0. destruct H0.
      eapply target_unique with (b1:=b1) (b2:=b2) (b3:=x) (b4:=x0 ++ << N n t; os1 ++ l0 ->> pmap f0 ks0 :: l' ->> pmap f' ks0 :: os2 >> :: x1) in H0; crush.
      inv H.
      eapply target_unique with (b1:=x ++ << N k v; l ->> pmap f ks :: os1'' >> :: x0) (b2:=x1) (b3:=b0) (b4:=b3) in H1; eauto; crush.
      got.
      * instantiate (1:=C ((x ++ << N k (t_app f v); l ->> pmap f (remove Nat.eq_dec k ks) :: os1'' >> :: x0) ++ << N n t; os1 ++ l0 ->> pmap (pmap_compose f' f0) ks0 :: os2 >> :: b3) os0 (l' ->>> 0 :: rs0) term1).
        one_step. eapply S_FusePMap; crush.
      * instantiate (1:=C (x ++ << N k (t_app f v); l ->> pmap f (remove Nat.eq_dec k ks) :: os1'' >> :: x0 ++ << N n t; os1 ++ l0 ->> pmap (pmap_compose f' f0) ks0 :: os2 >> :: b3) os0 (l' ->>> 0 :: rs0) term1).
        one_step. eapply S_PMap; crush.
      * crush.
    (* First second *)
    + destruct H0. destruct H0. destruct H0.
      eapply target_unique with (b1:=b1) (b2:=b2) (b3:=x ++ << N n t; os1 ++ l0 ->> pmap f0 ks0 :: l' ->> pmap f' ks0 :: os2 >> :: x0) (b4:=x1) in H0; eauto; crush.
      inv H.
      eapply target_unique with (b1:=x) (b2:=x0 ++ << N k v; l ->> pmap f ks :: os1'' >> :: x1) (b3:=b0) (b4:=b3) in H1; eauto; crush.
      got.
      * instantiate (1:=C (b0 ++ << N n t; os1 ++ l0 ->> pmap (pmap_compose f' f0) ks0 :: os2 >> :: x0 ++ << N k (t_app f v); l ->> pmap f (remove Nat.eq_dec k ks) :: os1'' >> :: x1) os0 (l' ->>> 0 :: rs0) term1).
        one_step. eapply S_FusePMap; crush.
      * instantiate (1:=C ((b0 ++ << N n t; os1 ++ l0 ->> pmap (pmap_compose f' f0) ks0 :: os2 >> :: x0) ++ << N k (t_app f v); l ->> pmap f (remove Nat.eq_dec k ks) :: os1'' >> :: x1) os0 (l' ->>> 0 :: rs0) term1).
        one_step. eapply S_PMap; crush.
      * crush.
Unshelve.
auto.
auto.
auto.
auto.
auto.
auto.
auto.
Qed.
Hint Resolve lc_pmap.

Axiom pmap_compose_assoc' : forall f f' f'',
  pmap_compose f (pmap_compose f' f'') = pmap_compose (pmap_compose f f') f''.

Lemma lc_fusepmap :
  forall cx cy cz n b1 b2 os os1 os2 rs term0 f f' ks l l' H,
  well_typed cx ->
  cx = C (b1 ++ << n; os1 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os2 >> :: b2) os rs term0 ->
  cy = C (b1 ++ << n; os1 ++ l ->> pmap (pmap_compose f' f) ks :: os2 >> :: b2) os (l' ->>> (@final (pmap f' ks)) H :: rs) term0 ->
  cx --> cy ->
  cx --> cz ->
  cy -v cz.
Proof using.
  intros cx cy cz n b1 b2 os os1 os2 rs term0 f f' ks l l' Hnot WT Heqcx Heqcy cxcy cxcz.
  remember (b1 ++ << n; os1 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os2 >> :: b2) as b.
  rename Heqb into H0.
  assert (H : cx = C b os rs term0) by assumption.
  remember cx as c.
  rename Heqc into H1.
  assert (H2 : C (b1 ++ << n; os1 ++ l ->> pmap (pmap_compose f' f) ks :: os2 >> :: b2) os (l' ->>> final Hnot :: rs) term0 = cy) by auto.
  inversion cxcz; ssame; try solve [subst; eauto].
  (* S_Empty *)
  - destruct b1; crush.
  (* S_Add *)
  - ssame.
    got.
    * instantiate (1:=C (<< N k v; [] >> :: b1 ++ << n; os1 ++ l ->> pmap (pmap_compose f' f) ks :: os2 >> :: b2) os' (l0 ->>> final _ :: l' ->>> final Hnot :: rs0) term1).
      one_step. eapply S_Add; crush.
    * instantiate (1:=C (<< N k v; [] >> :: b1 ++ << n; os1 ++ l ->> pmap (pmap_compose f' f) ks :: os2 >> :: b2) os' (l' ->>> final _ :: l0 ->>> k :: rs0) term1).
      one_step. apply S_FusePMap with (b:=<< N k v; [] >> :: b1 ++ << n; os1 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os2 >> :: b2) (b1:=<< N k v; [] >> :: b1); crush.
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
    rename H3 into Hnot'.
    rename H4 into H3.
    (* b3 = [] *)
    - apply List.app_inj_tail in H1. destruct H1. inv H1.
      destruct os2.
      (* os2 = [] *)
      + simpl in *.
        inv H6.
        got.
        * instantiate (1:=C (b1 ++ [<< n1; os3 >>]) os0 (l0 ->>> final _ :: l' ->>> 0 :: rs0) term1).
          one_step. eapply S_Last; crush.
        * instantiate (1:=C (b1 ++ [<< n1; os3 >>]) os0 (l' ->>> final Hnot :: l0 ->>> 0 :: rs0) term1).
          one_step. eapply S_Last; crush.
        * crush.
      (* os2 != [] *)
      + inv H6.
        got.
        * instantiate (1:=C (b1 ++ [<< n1; os2 ++ l ->> pmap (pmap_compose f' f) ks :: os3 >>]) os0 (l0 ->>> final Hnot' :: l' ->>> final Hnot :: rs0) term1).
          one_step. eapply S_Last; crush.
        * instantiate (1:=C (b1 ++ [<< n1; os2 ++ l ->> pmap (pmap_compose f' f) ks :: os3 >>]) os0 (l' ->>> final Hnot :: l0 ->>> final Hnot' :: rs0) term1).
          one_step. eapply S_FusePMap; crush.
        * crush.
    (* b3 != [] *)
    - remember (s :: b3) as bend.
      assert (exists y ys, bend = ys ++ [y]) by (apply list_snoc with (xs:=bend) (x:=s) (xs':=b3); crush).
      destruct H0; destruct H0.
      inv H0.
      rewrite H5 in *.
      assert (b2 ++ << n; os2 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os3 >> :: x0 ++ [x] = (b2 ++ << n; os2 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os3 >> :: x0) ++ [x]) by crush.
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
      + instantiate (1:=C ((b2 ++ << n; os2 ++ l ->> pmap (pmap_compose f' f) ks :: os3 >> :: x0) ++ [<< n1; os1' >>]) os0 (l0 ->>> final H3 :: l' ->>> final Hnot :: rs0) term1).
        one_step. eapply S_Last; crush.
      + instantiate (1:=C (b2 ++ << n; os2 ++ l ->> pmap (pmap_compose f' f) ks :: os3 >> :: x0 ++ [<< n1; os1' >>]) os0 (l' ->>> final Hnot :: l0 ->>> final H3 :: rs0) term1).
        assert (forall y, (b2 ++ << n; os2 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os3 >> :: x0) ++ y = b2 ++ << n; os2 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os3 >> :: x0 ++ y) by crush. rewrite H0.
        one_step. eapply S_FusePMap; crush.
      + crush.
    }
  (* S_FusePMap *)
  - destruct n as [k v].
    destruct n0 as [k' v'].
    rename H3 into Hnot'.
    rename H4 into H3.
    {
    eapply target_same_or_different with (b1:=b1) (b2:=b2) (b3:=b3) (b4:=b4) (k:=k) (v:=v) (k':=k') (v':=v') in H1; eauto.
    - destruct H1; try destruct H0.
      (* Same target *)
      + destruct H1; destruct H4; destruct H5; subst.
        {
        eapply op_same_or_different with (os1:=os1) (os2:=l' ->> pmap f' ks :: os2) (lop:=l ->> pmap f ks) (os3:=os3) (os4:=l'0 ->> pmap f'0 ks0 :: os4) (lop':=l0 ->> pmap f0 ks0) in H6; eauto.
        - destruct H6; destruct H0; try destruct H1.
          (* Same first lop *)
          + inv H1. inv H4. crush.
          (* First first *)
          + destruct H0; destruct H0; destruct H0.
            destruct x0.
            (* First's second is second's first *)
            * simpl in *.
              apply op_unique with (n:=N k' v') (os1:=os1) (os2:=l' ->> pmap f' ks :: os2) (os3:=x) (os4:=l0 ->> pmap f0 ks0 :: x1) (os0:=os0) (rs0:=rs0) (t0:=term1) (b:=b3 ++ << N k' v'; os1 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os2 >> :: b4) (b1:=b3) (b2:=b4) (os:=os1 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os2) in H0; crush.
              inv H4.
              inv H3.
              apply List.app_inv_head in H1.
              inv H1.
              apply op_unique with (n:=N k' v') (os1:=x ++ [l ->> pmap f ks0]) (os2:=x1) (os3:=os3) (os4:=l'0 ->> pmap f'0 ks0 :: os4) (os0:=os0) (rs0:=rs0) (t0:=term1) (b:=b3 ++ << N k' v'; x ++ l ->> pmap f ks0 :: l0 ->> pmap f0 ks0 :: x1 >> :: b4) (b1:=b3) (b2:=b4) (os:=x ++ l ->> pmap f ks0 :: l0 ->> pmap f0 ks0 :: x1) in H3; crush.
              {
              got.
              - instantiate (1:=C (b3 ++ << N k' v'; x ++ l ->> pmap (pmap_compose f'0 (pmap_compose f0 f)) ks0 :: os4 >> :: b4) os0 (l'0 ->>> final Hnot' :: l0 ->>> 0 :: rs0) term1).
                one_step. eapply S_FusePMap; crush.
              - instantiate (1:=C (b3 ++ << N k' v'; x ++ l ->> pmap (pmap_compose (pmap_compose f'0 f0) f) ks0 :: os4 >> :: b4) os0 (l0 ->>> final _ :: l'0 ->>> 0 :: rs0) term1).
                one_step. eapply S_FusePMap; crush.
              - rewrite pmap_compose_assoc'; eauto.
              }
            (* No overlap *)
            * simpl in *.
              apply op_unique with (n:=N k' v') (os1:=os1) (os2:=l' ->> pmap f' ks :: os2) (os3:=x) (os4:=l1 :: x0 ++ l0 ->> pmap f0 ks0 :: x1) (os0:=os0) (rs0:=rs0) (t0:=term1) (b:=b3 ++ << N k' v'; os1 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os2 >> :: b4) (b1:=b3) (b2:=b4) (os:=os1 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os2) in H0; crush.
              inv H3.
              apply List.app_inv_head in H1.
              inv H1.
              apply op_unique with (n:=N k' v') (os1:=x ++ l ->> pmap f ks :: l' ->> pmap f' ks :: x0) (os2:=x1) (os3:=os3) (os4:=l'0 ->> pmap f'0 ks0 :: os4) (os0:=os0) (rs0:=rs0) (t0:=term1) (b:=b3 ++ << N k' v'; x ++ l ->> pmap f ks :: l' ->> pmap f' ks :: x0 ++ l0 ->> pmap f0 ks0 :: x1 >> :: b4) (b1:=b3) (b2:=b4) (os:=x ++ l ->> pmap f ks :: l' ->> pmap f' ks :: x0 ++ l0 ->> pmap f0 ks0 :: x1) in H3; crush.
              {
              got.
              - instantiate (1:=C (b3 ++ << N k' v'; (x ++ l ->> pmap (pmap_compose f' f) ks :: x0) ++ l0 ->> pmap (pmap_compose f'0 f0) ks0 :: os4 >> :: b4) os0 (l'0 ->>> final Hnot' :: l' ->>> 0 :: rs0) term1).
                one_step. eapply S_FusePMap; crush.
              - instantiate (1:=C (b3 ++ << N k' v'; x ++ l ->> pmap (pmap_compose f' f) ks :: x0 ++ l0 ->> pmap (pmap_compose f'0 f0) ks0 :: os4 >> :: b4) os0 (l' ->>> final _ :: l'0 ->>> 0 :: rs0) term1).
                one_step. eapply S_FusePMap; crush.
              - crush.
              }
          (* First second *)
          + destruct H0; destruct H0; destruct H0.
            destruct x0.
            (* First's second is second's first *)
            * simpl in *.
              eapply op_unique with (n:=N k' v') (os1:=os1) (os2:=l' ->> pmap f' ks :: os2) (os3:=x ++ [l0 ->> pmap f0 ks0]) (os4:=x1) (os0:=os0) (rs0:=rs0) (t0:=term1) (b:=b3 ++ << N k' v'; os1 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os2 >> :: b4) (b1:=b3) (b2:=b4) (os:=os1 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os2) in H0; crush.
              inv H3.
              apply List.app_inv_head in H1.
              inv H1.
              apply op_unique with (n:=N k' v') (os1:=x) (os2:=l ->> pmap f ks :: l' ->> pmap f' ks :: os2) (os3:=os3) (os4:=l'0 ->> pmap f'0 ks0 :: os4) (os0:=os0) (rs0:=rs0) (t0:=term1) (b:=b3 ++ << N k' v'; x ++ l0 ->> pmap f0 ks0 :: l ->> pmap f ks :: l' ->> pmap f' ks :: os2 >> :: b4) (b1:=b3) (b2:=b4) (os:=x ++ l0 ->> pmap f0 ks0 :: l ->> pmap f ks :: l' ->> pmap f' ks :: os2) in H3; crush.
              inv H1.
              {
              got.
              - instantiate (1:=C (b3 ++ << N k' v'; os3 ++ l0 ->> pmap (pmap_compose (pmap_compose f' f'0) f0) ks0 :: os2 >> :: b4) os0 (l'0 ->>> final _ :: l' ->>> 0 :: rs0) term1).
                one_step. eapply S_FusePMap; crush.
              - instantiate (1:=C (b3 ++ << N k' v'; os3 ++ l0 ->> pmap (pmap_compose f' (pmap_compose f'0 f0)) ks0 :: os2 >> :: b4) os0 (l' ->>> final Hnot :: l'0 ->>> 0 :: rs0) term1).
                one_step. eapply S_FusePMap; crush.
              - rewrite pmap_compose_assoc'; eauto.
              }
            (* No overlap *)
            * simpl in *.
              eapply op_unique with (n:=N k' v') (os1:=os1) (os2:=l' ->> pmap f' ks :: os2) (os3:=x ++ l0 ->> pmap f0 ks0 :: l1 :: x0) (os4:=x1) (os0:=os0) (rs0:=rs0) (t0:=term1) (b:=b3 ++ << N k' v'; os1 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os2 >> :: b4) (b1:=b3) (b2:=b4) (os:=os1 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os2) in H0; crush.
              inv H3.
              apply List.app_inv_head in H1.
              inv H1.
              apply op_unique with (n:=N k' v') (os1:=x) (os2:=l1 :: x0 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os2) (os3:=os3) (os4:=l'0 ->> pmap f'0 ks0 :: os4) (os0:=os0) (rs0:=rs0) (t0:=term1) (b:=b3 ++ << N k' v'; x ++ l0 ->> pmap f0 ks0 :: l1 :: x0 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os2 >> :: b4) (b1:=b3) (b2:=b4) (os:=x ++ l0 ->> pmap f0 ks0 :: l1 :: x0 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os2) in H3; crush.
              {
              got.
              - instantiate (1:=C (b3 ++ << N k' v'; os3 ++ l0 ->> pmap (pmap_compose f'0 f0) ks0 :: x0 ++ l ->> pmap (pmap_compose f' f) ks :: os2 >> :: b4) os0 (l'0 ->>> final Hnot' :: l' ->>> 0 :: rs0) term1).
                one_step. eapply S_FusePMap; crush.
              - instantiate (1:=C (b3 ++ << N k' v'; (os3 ++ l0 ->> pmap (pmap_compose f'0 f0) ks0 :: x0) ++ l ->> pmap (pmap_compose f' f) ks :: os2 >> :: b4) os0 (l' ->>> final Hnot :: l'0 ->>> 0 :: rs0) term1).
                one_step. eapply S_FusePMap; crush.
              - crush.
              }
        }
      (* First first *)
      + destruct H0; destruct H0; destruct H0.
        apply target_unique with (os:=os1 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os2) (k:=k) (v:=v) (b1:=b1) (b2:=b2) (b3:=x) (b4:=x0 ++ << N k' v'; os3 ++ l0 ->> pmap f0 ks0 :: l'0 ->> pmap f'0 ks0 :: os4 >> :: x1) (os0:=os0) (rs0:=rs0) (t0:=term1) (b:=b1 ++ << N k v; os1 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os2 >> :: b2) in H0; crush.
        inv H3.
        apply target_unique with (os:=os3 ++ l0 ->> pmap f0 ks0 :: l'0 ->> pmap f'0 ks0 :: os4) (k:=k') (v:=v') (b1:=x ++ << N k v; os1 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os2 >> :: x0) (b2:=x1) (b3:=b3) (b4:=b4) (os0:=os0) (rs0:=rs0) (t0:=term1) (b:=x ++ << N k v; os1 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os2 >> :: x0 ++ << N k' v'; os3 ++ l0 ->> pmap f0 ks0 :: l'0 ->> pmap f'0 ks0 :: os4 >> :: x1) in H1; crush.
        got.
        * instantiate (1:=C ((x ++ << N k v; os1 ++ l ->> pmap (pmap_compose f' f) ks :: os2 >> :: x0) ++ << N k' v'; os3 ++ l0 ->> pmap (pmap_compose f'0 f0) ks0 :: os4 >> :: b4) os0 (l'0 ->>> 0 :: l' ->>> 0 :: rs0) term1).
          one_step. eapply S_FusePMap; crush.
        * instantiate (1:=C (x ++ << N k v; os1 ++ l ->> pmap (pmap_compose f' f) ks :: os2 >> :: x0 ++ << N k' v'; os3 ++ l0 ->> pmap (pmap_compose f'0 f0) ks0 :: os4 >> :: b4) os0 (l' ->>> 0 :: l'0 ->>> 0 :: rs0) term1).
          one_step. eapply S_FusePMap; crush.
        * crush.
      (* First second *)
      + destruct H0; destruct H0; destruct H0.
        apply target_unique with (os:=os1 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os2) (k:=k) (v:=v) (b1:=b1) (b2:=b2) (b3:=x ++ << N k' v'; os3 ++ l0 ->> pmap f0 ks0 :: l'0 ->> pmap f'0 ks0 :: os4 >> :: x0) (b4:=x1) (os0:=os0) (rs0:=rs0) (t0:=term1) (b:=b1 ++ << N k v; os1 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os2 >> :: b2) in H0; crush.
        inv H3.
        apply target_unique with (os:=os3 ++ l0 ->> pmap f0 ks0 :: l'0 ->> pmap f'0 ks0 :: os4) (k:=k') (v:=v') (b1:=x) (b2:=x0 ++ << N k v; os1 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os2 >> :: x1) (b3:=b3) (b4:=b4) (os0:=os0) (rs0:=rs0) (t0:=term1) (b:=x ++ << N k' v'; os3 ++ l0 ->> pmap f0 ks0 :: l'0 ->> pmap f'0 ks0 :: os4 >> :: x0 ++ << N k v; os1 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os2 >> :: x1) in H1; crush.
        got.
        * instantiate (1:=C (b3 ++ << N k' v'; os3 ++ l0 ->> pmap (pmap_compose f'0 f0) ks0 :: os4 >> :: x0 ++ << N k v; os1 ++ l ->> pmap (pmap_compose f' f) ks :: os2 >> :: x1) os0 (l'0 ->>> 0 :: l' ->>> 0 :: rs0) term1).
          one_step. eapply S_FusePMap; crush.
        * instantiate (1:=C ((b3 ++ << N k' v'; os3 ++ l0 ->> pmap (pmap_compose f'0 f0) ks0 :: os4 >> :: x0) ++ << N k v; os1 ++ l ->> pmap (pmap_compose f' f) ks :: os2 >> :: x1) os0 (l' ->>> 0 :: l'0 ->>> 0 :: rs0) term1).
          one_step. eapply S_FusePMap; crush.
        * crush.
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
auto.
auto.
Qed.
Hint Resolve lc_fusepmap.

Lemma lc_last :
  forall cx cy cz b1 n1 os rs term0 os1' l op H,
  well_typed cx ->
  cx = C (b1 ++ [<< n1; l ->> op :: os1' >>]) os rs term0 ->
  cy = C (b1 ++ [<< n1; os1' >>]) os (l ->>> (@final op) H :: rs) term0 ->
  ~ In (getKey n1) (target op) ->
  cx --> cy ->
  cx --> cz ->
  cy -v cz.
Proof using.
  intros cx cy cz b1 n1 os rs term0 os1' l op Hnot WT Heqcx Heqcy H3 cxcy cxcz.
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
    - simpl in *. inv H7. eapply ex_intro. eapply ex_intro.
      split; try split.
      + instantiate (1:=C [<< N k0 v; [] >>; << n1; os1' >>] os' (l0 ->>> _ :: l ->>> final _ :: rs0) term1).
        one_step; eapply S_Add with (b:=[<< n1; os1' >>]); crush.
      + instantiate (1:=C [<< N k0 v; [] >>; << n1; os1' >>] os' (l ->>> final Hnot :: l0 ->>> k0 :: rs0) term1).
        one_step; eapply S_Last with (b1:=[<< N k0 v; [] >>]); crush.
      + crush.
    (* b1 != [] *)
    - simpl in *. inv H7. eapply ex_intro. eapply ex_intro.
      split; try split.
      + instantiate (1:=C (<< N k0 v; [] >> :: s :: b1 ++ [<< n1; os1' >>]) os' (l0 ->>> k0 :: l ->>> final Hnot :: rs0) term1).
        one_step; eapply S_Add; crush.
      + instantiate (1:=C (<< N k0 v; [] >> :: s :: b1 ++ [<< n1; os1' >>]) os' (l ->>> final Hnot :: l0 ->>> k0 :: rs0) term1).
        one_step; eapply S_Last with (b1:=<< N k0 v; [] >> :: s :: b1); crush.
      + crush.
    }
  (* S_Last *)
  - ssame. apply List.app_inj_tail in H0. inv H0. inv H1.
    unfold not_fold_or_done in *.
    destruct H6; destruct Hnot.
    + destruct op0; crush.
    + destruct op0; crush.
    + destruct op0; crush.
    + destruct e0. destruct e0. destruct e0. destruct e. destruct e. destruct e. crush.
      inv e.
      crush.
Unshelve.
auto.
auto.
Qed.
Hint Resolve lc_last.

Lemma lc_empty :
  forall cx cy cz l op os' rs term0 Hnot,
  well_typed cx ->
  cx = C [] (l ->> op :: os') rs term0 ->
  cy = C [] os' (l ->>> (@final op) Hnot :: rs) term0 ->
  not_add op ->
  cx --> cy ->
  cx --> cz ->
  cy -v cz.
Proof using.
  intros cx cy cz l op os' rs term0 Hnot WT Heqcx Heqcy Hnotadd cxcy cxcz.
  inversion cxcz; ssame; eauto; crush.
  - unfold not_fold_or_done in *.
    destruct Hnot; destruct H; try solve [destruct op0; crush].
    destruct e0. destruct e0. destruct e0. destruct e. destruct e. destruct e. crush.
    inv e0.
    crush.
Qed.
Hint Resolve lc_empty.

Lemma lc_add :
  forall cx cy cz b l k v os' rs term0 Hnot,
  well_typed cx ->
  cx = C b (l ->> add k v :: os') rs term0 ->
  cy = C (<< N k v; [] >> :: b) os' (l ->>> (@final (add k v)) Hnot :: rs) term0 ->
  cx --> cy ->
  cx --> cz ->
  cy -v cz.
Proof using.
  intros cx cy cz b l k v os' rs term0 Hnot WT Heqcx Heqcy cxcy cxcz.
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
  destruct c as [b os rs t].
  remember WT as WT'.
  clear HeqWT'.
  eapply progress' in WT'; eauto.
  destruct WT'.
  - exists 0. exists (C b os rs t). remember (C b os rs t) as c. assert (normal_form c) by (eapply dry_normal_form; eauto). split; eauto.
  - destruct H. remember H as Hc. clear HeqHc. apply noe_indo' in H. destruct H. destruct H. destruct H.
    exists (S x0). exists x1. split; eauto.
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
