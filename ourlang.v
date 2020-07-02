
Require Import CpdtTactics.
From Coq Require Import Lists.List.
From Coq Require Import Bool.Bool.
From Coq Require Import Sorting.Permutation.
From Coq Require Import Arith.PeanoNat.
From Coq Require Import Arith.Peano_dec.
From Coq Require Import Classes.Equivalence.
From Coq Require Import Strings.String.
Require Import Maps.
Require NMaps.
Import ListNotations.

From Coq Require Import Relations.Relations.
From Coq Require Import Relations.Relation_Definitions.
Hint Constructors clos_refl_trans_1n.

Hint Constructors Permutation.Permutation.

Ltac inv H := inversion H; subst; clear H.
Ltac dtr := repeat (match goal with
                    | [H : _ /\ _ |- _] => destruct H
                    | [H : exists _ , _ |- _] => destruct H
                    end).
Ltac exi := eapply ex_intro.

Set Implicit Arguments.

Notation key := nat.
Notation label := nat.
Notation keyset := (list key).
Notation result := nat.

(* ***********************frontend *)

Inductive type : Type :=
| Node : type
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
| t_emit_pfold : label -> term -> term -> term -> term
| t_emit_pmap : label -> term -> term -> term
| t_emit_add : label -> term -> term -> term
| t_node : term -> term -> term -> term
| t_na1 : term -> term
| t_na2 : term -> term
| t_na3 : term -> term
| t_fix : type -> term -> term.
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
                  value (t_ks_cons k ks)
| v_node : forall k p es,
    value k ->
    value p ->
    value es ->
    value (t_node k p es).
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
  | t_emit_pfold l t1 t2 t3 =>
      t_emit_pfold l (#[x:=s] t1) (#[x:=s] t2) (#[x:=s] t3)
  | t_emit_pmap l t1 t2 =>
      t_emit_pmap l (#[x:=s] t1) (#[x:=s] t2)
  | t_emit_add l t1 t2 =>
      t_emit_add l (#[x:=s] t1) (#[x:=s] t2)
  | t_node k p es =>
      t_node (#[x:=s]k) (#[x:=s]p) (#[x:=s]es)
  | t_na1 t =>
      t_na1 (#[x:=s]t)
  | t_na2 t =>
      t_na2 (#[x:=s]t)
  | t_na3 t =>
      t_na3 (#[x:=s]t)
  | t_fix T t =>
      t_fix T (#[x:=s] t)
  end
where "'#[' x ':=' s ']' t" := (e_subst x s t).

(* ***********************end frontend *)

Notation payload := term.
Definition edgeset := term.
Hint Unfold edgeset.

Inductive node : Type :=
| N : key -> payload -> edgeset -> node.
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
  | N k _ _ => k
end.
Hint Unfold getKey.

Definition get_payload (n : node) :=
match n with
  | N _ p _ => p
end.
Hint Unfold get_payload.

(* ****** typing *)
Definition context := partial_map type.
Definition lcontext := NMaps.partial_map type.

Definition nempty {A : Type} := (@NMaps.empty A).
Notation "x '#->' v ';' m" := (NMaps.update m x v) (at level 100, v at next level, right associativity).

Inductive has_type : context -> lcontext -> term -> type -> bool -> Prop :=
| T_Var : forall Gamma ll x T,
    Gamma x = Some T ->
    has_type Gamma ll (t_var x) T false
| T_Abs : forall Gamma ll x T11 T12 t12 E,
    has_type (x |-> T11 ; Gamma) ll t12 T12 E ->
    has_type Gamma ll (t_abs x T11 t12) (Arrow T11 T12 E) false
| T_App : forall T11 T12 Gamma ll t1 t2 E1 E2 E3,
    has_type Gamma ll t1 (Arrow T11 T12 E1) E2 ->
    has_type Gamma ll t2 T11 E3 ->
    has_type Gamma ll (t_app t1 t2) T12 (E1 || E2 || E3)
| T_Result : forall r Gamma ll,
    has_type Gamma ll (t_result r) Result false
| T_KS_Nil : forall Gamma ll,
    has_type Gamma ll t_ks_nil Keyset false
| T_KS_Cons : forall k ks Gamma ll E1 E2,
    has_type Gamma ll k Result E1 ->
    has_type Gamma ll ks Keyset E2 ->
    has_type Gamma ll (t_ks_cons k ks) Keyset (E1 || E2)
| T_Downarrow : forall ft t Gamma ll E,
    has_type Gamma ll t (Label ft) E ->
    has_type Gamma ll (t_downarrow t) ft E
| T_Label : forall l Gamma ll T,
    ll l = Some T ->
    has_type Gamma ll (t_label l) (Label T) false
| T_Emit_PFold : forall l t1 t2 t3 Gamma ll E1 E2 E3,
    has_type Gamma ll t1 (Arrow Result (Arrow Result Result false) false) E1 ->
    has_type Gamma ll t2 Result E2 ->
    has_type Gamma ll t3 Keyset E3 ->
    has_type Gamma ll (t_emit_pfold l t1 t2 t3) (Label Result) true
| T_Emit_PMap : forall l t1 t2 Gamma ll E1 E2,
    has_type Gamma ll t1 (Arrow Result Result false) E1 ->
    has_type Gamma ll t2 Keyset E2 ->
    has_type Gamma ll (t_emit_pmap l t1 t2) (Label Result) true
| T_Emit_Add : forall l t1 t2 Gamma ll E1 E2,
    has_type Gamma ll t1 Result E1 ->
    has_type Gamma ll t2 Result E2 ->
    has_type Gamma ll (t_emit_add l t1 t2) (Label Result) true
| T_Node : forall k p es Gamma ll E1 E2 E3,
    has_type Gamma ll k Result E1 ->
    has_type Gamma ll p Result E2 ->
    has_type Gamma ll es Keyset E3 ->
    has_type Gamma ll (t_node k p es) Node (E1 || E2 || E3)
| T_Na1 : forall t Gamma ll E,
    has_type Gamma ll t Node E ->
    has_type Gamma ll (t_na1 t) Result E
| T_Na2 : forall t Gamma ll E,
    has_type Gamma ll t Node E ->
    has_type Gamma ll (t_na2 t) Result E
| T_Na3 : forall t Gamma ll E,
    has_type Gamma ll t Node E ->
    has_type Gamma ll (t_na3 t) Keyset E
| T_Fix : forall t T Gamma ll E2 E3 E4,
    has_type Gamma ll t (Arrow (Arrow T T (E2 || E3)) (Arrow T T E2) E3) E4 ->
    has_type Gamma ll (t_fix T t) (Arrow T T (E2 || E3)) E4.
Hint Constructors has_type.

Inductive well_typed_operation : lcontext -> operation -> Prop :=
| WTO_PFold : forall t1 t2 ks ll,
    value t1 ->
    has_type empty ll t1 (Arrow Result (Arrow Result Result false) false) false ->
    has_type empty ll t2 Result false ->
    well_typed_operation ll (pfold t1 t2 ks)
| WTO_PMap : forall t ks ll,
    value t ->
    has_type empty ll t (Arrow Result Result false) false ->
    well_typed_operation ll (pmap t ks)
| WTO_Add : forall k t ll,
    has_type empty ll t Result false ->
    well_typed_operation ll (add k t).
Hint Constructors well_typed_operation.

Definition op_type (op : operation) : type :=
match op with
| pmap _ _ => Result
| add _ _ => Result
| pfold _ _ _ => Result
end.
Hint Unfold op_type.

Inductive well_typed_top_ostream : lcontext -> lcontext -> ostream -> Prop :=
| WTTO_nil : forall ll,
    well_typed_top_ostream ll ll []
| WTTO_cons : forall l op os ll ll',
    (match op with
     | pfold _ t _ => exists r, t = t_result r
     | _ => True
     end) ->
    well_typed_top_ostream (l#->(op_type op);ll) ll' os ->
    well_typed_operation ll op ->
    well_typed_top_ostream ll ll' (l ->> op :: os).
Hint Constructors well_typed_top_ostream.

Inductive well_typed_ostream : lcontext -> lcontext -> ostream -> Prop :=
| WTO_nil : forall ll,
    well_typed_ostream ll ll []
| WTO_cons : forall l op os ll ll',
    well_typed_ostream (l#->(op_type op);ll) ll' os ->
    well_typed_operation ll op ->
    well_typed_ostream ll ll' (l ->> op :: os).
Hint Constructors well_typed_ostream.

Inductive well_typed_backend : lcontext -> lcontext -> backend -> Prop :=
| WTB_nil : forall ll,
    well_typed_backend ll ll []
| WTB_cons : forall k t es os b ll ll' ll'',
    has_type empty ll' t Result false ->
    has_type empty ll' es Keyset false ->
    well_typed_ostream ll' ll'' os ->
    well_typed_backend ll ll' b ->
    well_typed_backend ll ll'' (<<N k t es; os>> :: b).
Hint Constructors well_typed_backend.

Fixpoint rstream_types (rs : rstream) : lcontext :=
match rs with
| [] => nempty
| l ->>> r :: rs => (l#->Result;(rstream_types rs))
end.

Inductive config_has_type : config -> type -> bool -> Prop :=
| CT : forall b os rs t T E ll ll',
    well_typed_backend (rstream_types rs) ll b ->
    well_typed_top_ostream ll ll' os ->
    has_type empty ll' t T E ->
    config_has_type (C b os rs t) T E.
Hint Constructors config_has_type.

Fixpoint ostream_types (os : ostream) z : lcontext :=
match os with
| [] => z
| l ->> op :: os => (l#->(op_type op);ostream_types os z)
end.

Fixpoint backend_types (b : backend) z : lcontext :=
match b with
| [] => z
| <<N k t es; os>> :: b => ostream_types os (backend_types b z)
end.

Axiom fresh_labels : forall (l:label) l', l <> l'.
Hint Immediate fresh_labels.

Lemma ostream_types_zero_lift : forall os l T ll,
  ostream_types os (l#->T;ll) = (l#->T;(ostream_types os ll)).
Proof using.
  induction os; intros; auto.
  - destruct a. crush. apply NMaps.update_permute; auto.
Qed.
Hint Resolve ostream_types_zero_lift.

Lemma wt_to_ostream_types : forall os ll ll',
  well_typed_ostream ll ll' os ->
  ll' = ostream_types os ll.
Proof using.
  induction os; intros.
  - inv H; auto.
  - destruct a; simpl; inv H; apply IHos in H4. subst. apply ostream_types_zero_lift.
Qed.
Hint Resolve wt_to_ostream_types.

Lemma wt_to_top_ostream_types : forall os ll ll',
  well_typed_top_ostream ll ll' os ->
  ll' = ostream_types os ll.
Proof using.
  induction os; intros.
  - inv H; auto.
  - destruct a; simpl; inv H; apply IHos in H6. subst. apply ostream_types_zero_lift.
Qed.
Hint Resolve wt_to_top_ostream_types.

Lemma wt_to_backend_types : forall b ll ll',
  well_typed_backend ll ll' b ->
  ll' = backend_types b ll.
Proof using.
  induction b; intros.
  - inv H; auto.
  - inv H; apply IHb in H7; crush.
Qed.
Hint Resolve wt_to_backend_types.

(* ****** end typing *)

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


Definition pmap_compose f f' :=
t_abs "x" Result (t_app f (t_app f' (t_var "x"))).

Reserved Notation "c1 '-->' c2" (at level 40).

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
| S_FusePMap : forall c b n b1 b2 os os1 os2 rs term f f' ks l l' H,
    c = C b os rs term ->
    b = b1 ++ <<n; os1 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os2>> :: b2 ->
    c --> C (b1 ++ <<n; os1 ++ l' ->> pmap (pmap_compose f' f) ks :: os2>> :: b2) os (l ->>> (@final (pmap f ks)) H :: rs) term
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
(* S_Complete *)
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

Inductive well_typed : config -> Prop :=
| WT : forall c,
    distinct (config_keys c) ->
    distinct (config_labels c) ->
    (exists T b, config_has_type c T b) ->
    well_typed c.
Hint Constructors well_typed.

Example wt : well_typed (C [<<(N 1 (t_result 2) t_ks_nil); [5 ->> pmap (t_abs "x" Result (t_var "x")) []]>>; <<(N 2 (t_result 3) t_ks_nil); [4 ->> pmap (t_abs "x" Result (t_var "x")) []]>>] [2 ->> pmap (t_abs "x" Result (t_var "x")) []; 3 ->> pmap (t_abs "x" Result (t_var "x")) []] [1 ->>> 2] noop).
Proof using.
  eapply WT; repeat crush; repeat (eapply distinct_many; crush).
  unfold noop; eauto.
  exists Result, false.
  econstructor; eauto.
  econstructor; eauto.
  econstructor; eauto.
  econstructor; eauto.
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

Lemma free_in_lcontext : forall l t T E Gamma ll,
   lappears_free_in l t ->
   has_type Gamma ll t T E ->
   exists T', ll l = Some T'.
Proof using.
  intros x t T E Gamma ll H H0. generalize dependent Gamma.
  generalize dependent T.
  generalize dependent E.
  induction H;
         intros; try solve [inversion H0; eauto].
Qed.

Ltac copy H := let h := fresh "H" in assert (h := H).
Ltac capply H1 H2 := copy H2; apply H1 in H2.
Ltac ceapply H1 H2 := copy H2; eapply H1 in H2.
Tactic Notation "capply" ident(h1) "in" ident(h2) := capply h1 h2.
Tactic Notation "ceapply" ident(h1) "in" ident(h2) := ceapply h1 h2.

Ltac wtbt := match goal with
             | [H : well_typed_backend _ _ _ |- _] => apply wt_to_backend_types in H; subst
             end.
Ltac wtost := match goal with
              | [H : well_typed_ostream _ _ _ |- _] => apply wt_to_ostream_types in H; subst
              end.
Ltac wttost := match goal with
               | [H : well_typed_top_ostream _ _ _ |- _] => apply wt_to_top_ostream_types in H; subst
               end.
Ltac wtbt' := match goal with
              | [H : well_typed_backend _ _ _ |- _] => copy H; apply wt_to_backend_types in H; subst
              end.
Ltac wttost' := match goal with
                | [H : well_typed_top_ostream _ _ _ |- _] => copy H; apply wt_to_top_ostream_types in H; subst
                end.
Ltac wtost' := match goal with
               | [H : well_typed_ostream _ _ _ |- _] => copy H; apply wt_to_ostream_types in H; subst
               end.

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

Lemma op_in_dec : forall os l, (exists op, In (l ->> op) os) \/ (not (exists op, In (l ->> op) os)).
Proof using.
  induction os; intros.
  - right; crush.
  - destruct IHos with (l:=l).
    + left. destruct H. exists x. crush.
    + destruct a.
      destruct (Nat.eq_dec n l).
      * subst. left. exists o. crush.
      * right. intro.
        destruct H0.
        apply List.in_inv in H0.
        {
        destruct H0.
        - crush.
        - apply H. exists x. crush.
        }
Qed.

Lemma op_in_backend_dec : forall b l, (exists b1 s b2 op, b = b1 ++ s :: b2 /\ In (l ->> op) (get_ostream s)) \/ (not (exists b1 s b2 op, b = b1 ++ s :: b2 /\ In (l ->> op) (get_ostream s))).
Proof using.
  induction b; intros.
  - right; crush. destruct x; crush.
  - destruct IHb with (l:=l); dtr.
    + left. exists (a::x), x0, x1, x2. crush.
    + destruct a.
      destruct (@op_in_dec l0 l); dtr; eauto.
      * left. exists [], <<n;l0>>, b, x. eauto.
      * right. intro; dtr; apply H.
        {
        destruct x; simpl in *.
        - inv H1.
          exfalso; apply H0; eauto.
        - inv H1. exists x, x0, x1, x2. eauto.
        }
Qed.

Lemma lcontext_in_or_os : forall os l ll T,
  (ostream_types os ll) l = Some T ->
  (exists op, In (l ->> op) os) \/ ll l = Some T.
Proof using.
  induction os; intros; auto.
  destruct a. simpl in H. destruct (Nat.eq_dec n l).
  - left. exi; crush.
  - replace ((n#->(op_type o); ostream_types os ll) l) with ((ostream_types os ll) l) in *.
    destruct (@IHos l ll T); dtr; auto.
    left; exists x; crush.
    rewrite NMaps.update_neq; eauto.
Qed.

Lemma lcontext_in_or_b : forall b l ll T,
  (backend_types b ll) l = Some T ->
  (exists b1 s b2 op, b = b1 ++ s :: b2 /\ In (l ->> op) (get_ostream s)) \/ ll l = Some T.
Proof using.
  induction b; intros; auto.
  destruct a. destruct n. simpl in H.
  apply lcontext_in_or_os in H. destruct H; dtr.
  - left. exists [], <<N n t e; l0>>, b, x. eauto.
  - apply IHb in H. destruct H; dtr.
    + left. exists (<<N n t e; l0>> :: x), x0, x1, x2. crush.
    + eauto.
Qed.

Lemma type_in_rstream : forall rs l T,
  (rstream_types rs) l = Some T ->
  exists v, In (l ->>> v) rs.
Proof using.
  induction rs; intros.
  - inv H.
  - destruct a.
    destruct (Nat.eq_dec l n); subst.
    + exists n0. crush.
    + simpl in H.
      replace ((n#->Result; rstream_types rs) l) with ((rstream_types rs) l) in *.
      apply IHrs in H; dtr. exists x; crush.
      rewrite NMaps.update_neq; auto.
Qed.

Lemma all_labels : forall t l b os rs,
    lappears_free_in l t ->
    well_typed (C b os rs t) ->
    (exists v, In (l ->>> v) rs) \/ (exists op, In (l ->> op) os) \/ (exists op b1 s b2, b = b1 ++ s :: b2 /\ In (l ->> op) (get_ostream s)).
Proof using.
  intros.
  inv H0.
  destruct H3 as [T[E]].
  inv H0.
  eapply free_in_lcontext in H; eauto.
  destruct H.
  wtbt.
  wttost.
  destruct (@op_in_dec os l); dtr; eauto.
  destruct (@result_in_dec rs l); dtr; eauto.
  destruct (@op_in_backend_dec b l); dtr.
  - right. right. exi; eauto.
  - exfalso.
    destruct (@lcontext_in_or_os os l (backend_types b (rstream_types rs)) x); auto.
    destruct (@lcontext_in_or_b b l (rstream_types rs) x); auto.
    apply H3.
    apply type_in_rstream in H6. eauto.
Qed.

Lemma cons_app :
  forall {A: Type} (x : A) xs,
  x :: xs = [x] ++ xs.
Proof using.
  crush.
Qed.

Ltac ssame := subst; match goal with
                     | [ H : C _ _ _ _ = C _ _ _ _ |- _ ] => inversion H
                     end; subst.
Ltac ssame' := subst; match goal with
                      | [ H : C _ _ _ _ = C _ _ _ _ |- _ ] => inv H
                      end.

Lemma frontend_no_value :
  forall t rs os t',
  FRf t rs ==> FRt t' os ->
  ~ (value t).
Proof using.
  induction t; intros; try solve [inv H].
  - intro. inv H0.
  - inv H.
    + apply IHt1 in H1. intro. inv H. auto.
    + apply IHt2 in H6. intro. inv H. auto.
  - inv H.
    + intro. inv H.
    + apply IHt in H1. intro. inv H.
  - inv H.
    + intro. inv H.
    + apply IHt1 in H1. intro. inv H.
    + apply IHt2 in H8. intro. inv H.
    + apply IHt3 in H9. intro. inv H.
  - inv H.
    + intro. inv H.
    + apply IHt1 in H1. intro. inv H.
    + apply IHt2 in H7. intro. inv H.
  - inv H.
    + intro. inv H.
    + apply IHt1 in H1. intro. inv H.
    + apply IHt2 in H7. intro. inv H.
  - inv H.
    + apply IHt1 in H1. intro. inv H. auto.
    + apply IHt2 in H7. intro. inv H. auto.
    + apply IHt3 in H8. intro. inv H. auto.
  - inv H; intro; inv H.
  - inv H; intro; inv H.
  - inv H; intro; inv H.
  - inv H; intro; inv H.
Qed.

Ltac narrow_terms := try (match goal with
                          | [H : value _ |- _] => inv H
                          end);
                     try (match goal with
                          | [H : empty _ = Some _ |- _] => inv H
                          end);
                     try solve [match goal with
                                | [H : has_type _ _ _ _ _ |- _] => inv H
                                end].

(* ****** typing *)
Lemma canonical_forms_fun : forall t T1 T2 E1 E2 ll,
  has_type empty ll t (Arrow T1 T2 E1) E2 ->
  value t ->
  exists x u, t = t_abs x T1 u.
Proof using.
  intros t T1 T2 E1 E2 ll HT HVal.
  inversion HVal; intros; subst; try inversion HT; subst; auto; narrow_terms; eauto.
Qed.

Lemma canonical_forms_result : forall t E ll,
  has_type empty ll t Result E ->
  value t ->
  exists r, t = t_result r.
Proof using.
  destruct t; intros; try solve [inv H0; inv H].
  eauto.
Qed.
Hint Resolve canonical_forms_result.

Lemma canonical_forms_label : forall t E T ll,
  has_type empty ll t (Label T) E ->
  value t ->
  exists l, t = t_label l.
Proof using.
  destruct t; intros; try solve [inv H0; inv H].
  eauto.
Qed.
Hint Resolve canonical_forms_label.

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
  - destruct IHt1; destruct IHt2; try solve [eauto]; right; intro; inv H1; eauto.
  - destruct IHt1; destruct IHt2; destruct IHt3; try solve [eauto]; right; intro; inv H2; eauto.
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
| nr_emit_pfold1 : forall l t1 t2 t3 t', not (value t1) -> next_reduction t1 t' -> next_reduction (t_emit_pfold l t1 t2 t3) t'
| nr_emit_pfold2 : forall l t1 t2 t3 t', value t1 -> not (value t2) -> next_reduction t2 t' -> next_reduction (t_emit_pfold l t1 t2 t3) t'
| nr_emit_pfold3 : forall l t1 t2 t3 t', value t1 -> value t2 -> not (value t3) -> next_reduction t3 t' -> next_reduction (t_emit_pfold l t1 t2 t3) t'
| nr_emit_pfold : forall l t1 t2 t3, value t1 -> value t2 -> value t3 -> next_reduction (t_emit_pfold l t1 t2 t3) (t_emit_pfold l t1 t2 t3)
| nr_emit_pmap1 : forall l t1 t2 t', not (value t1) -> next_reduction t1 t' -> next_reduction (t_emit_pmap l t1 t2) t'
| nr_emit_pmap2 : forall l t1 t2 t', value t1 -> not (value t2) -> next_reduction t2 t' -> next_reduction (t_emit_pmap l t1 t2) t'
| nr_emit_pmap : forall l t1 t2, value t1 -> value t2 -> next_reduction (t_emit_pmap l t1 t2) (t_emit_pmap l t1 t2)
| nr_emit_add1 : forall l t1 t2 t', not (value t1) -> next_reduction t1 t' -> next_reduction (t_emit_add l t1 t2) t'
| nr_emit_add2 : forall l t1 t2 t', value t1 -> not (value t2) -> next_reduction t2 t' -> next_reduction (t_emit_add l t1 t2) t'
| nr_emit_add : forall l t1 t2, value t1 -> value t2 -> next_reduction (t_emit_add l t1 t2) (t_emit_add l t1 t2)
| nr_node1 : forall t1 t2 t3 t1', not (value t1) -> next_reduction t1 t1' -> next_reduction (t_node t1 t2 t3) t1'
| nr_node2 : forall t1 t2 t3 t2', value t1 -> not (value t2) -> next_reduction t2 t2' -> next_reduction (t_node t1 t2 t3) t2'
| nr_node3 : forall t1 t2 t3 t3', value t1 -> value t2 -> not (value t3) -> next_reduction t3 t3' -> next_reduction (t_node t1 t2 t3) t3'
| nr_na1 : forall t t', not (value t) -> next_reduction t t' -> next_reduction (t_na1 t) t'
| nr_na2 : forall t t', not (value t) -> next_reduction t t' -> next_reduction (t_na2 t) t'
| nr_na3 : forall t t', not (value t) -> next_reduction t t' -> next_reduction (t_na3 t) t'
| nr_na1_get : forall t, value t -> next_reduction (t_na1 t) (t_na1 t)
| nr_na2_get : forall t, value t -> next_reduction (t_na2 t) (t_na2 t)
| nr_na3_get : forall t, value t -> next_reduction (t_na3 t) (t_na3 t)
| nr_fix : forall t t' T, not (value t) -> next_reduction t t' -> next_reduction (t_fix T t) t'
| nr_fix_fix : forall t T, value t -> next_reduction (t_fix T t) (t_fix T t).
Hint Constructors next_reduction.

Ltac find_type := match goal with
                 | [H : has_type _ _ _ _ _ |- _] => inv H; eauto
                 | [H : config_has_type _ _ _ |- _] => inv H; find_type
                 end.
Ltac easy_wt := inversion WT; split; try split; crush; find_type.

Ltac can_fun :=
    match goal with
    | [H : has_type empty _ ?t (Arrow _ _ _) _, H' : value ?t |- _] =>
      let x := fresh "x" in let u := fresh "u" in apply canonical_forms_fun in H; [|assumption]; destruct H as [x[u]]; subst t
    end.

Ltac can_res :=
    match goal with
    | [H : has_type empty _ ?t Result _, H' : value ?t |- _] =>
      let r := fresh "r" in apply canonical_forms_result in H; [|assumption]; destruct H as [r]; subst t
    end.

Ltac can_lab :=
    match goal with
    | [H : has_type empty _ ?t (Label _) _, H' : value ?t |- _] =>
      let l := fresh "l" in apply canonical_forms_label in H; [|assumption]; destruct H as [l]; subst t
    end.

Lemma next_reduction_to_reduction' :
  forall t rs b os t',
  well_typed (C b os rs t) ->
  next_reduction t t' ->
  (exists t'' os', FRf t rs ==> FRt t'' os') \/ (exists l, t' = t_downarrow (t_label l) /\ not (exists v, In (l ->>> v) rs)).
Proof using.
  intros t rs b os t' WT NR.
  induction NR; subst.
  - destruct IHNR; dtr; [try solve [easy_wt]| |]; try solve [eauto].
  - destruct IHNR; dtr; [try solve [easy_wt]| |]; try solve [eauto].
  - inv WT. dtr. inv H3. inv H12. can_fun. left. eauto.
  - inv WT; dtr. inv H1. inv H10. inv H4.
  - destruct IHNR; dtr; [try solve [easy_wt]| |]; try solve [eauto].
  - destruct IHNR; dtr; [try solve [easy_wt]| |]; try solve [eauto].
  - destruct IHNR; dtr; [try solve [easy_wt]| |]; try solve [eauto].
  - inv WT; dtr. inv H2. inv H11. can_lab.
    destruct (result_in_dec rs l).
    + destruct H2. eauto.
    + right. eauto.
  - destruct IHNR; dtr; [try solve [easy_wt]| |]; try solve [eauto].
  - destruct IHNR; dtr; [try solve [easy_wt]| |]; try solve [eauto].
  - destruct IHNR; dtr; [try solve [easy_wt]| |]; try solve [eauto].
  - eauto.
  - destruct IHNR; dtr; [try solve [easy_wt]| |]; try solve [eauto].
  - destruct IHNR; dtr; [try solve [easy_wt]| |]; try solve [eauto].
  - eauto.
  - destruct IHNR; dtr; [try solve [easy_wt]| |]; try solve [eauto].
  - destruct IHNR; dtr; [try solve [easy_wt]| |]; try solve [eauto].
  - inv WT; dtr. inv H3. inv H12. can_res. can_res.
    eauto.
  - destruct IHNR; dtr; [try solve [easy_wt]| |]; try solve [eauto].
  - destruct IHNR; dtr; [try solve [easy_wt]| |]; try solve [eauto].
  - destruct IHNR; dtr; [try solve [easy_wt]| |]; try solve [eauto].
  - destruct IHNR; dtr; [try solve [easy_wt]| |]; try solve [eauto].
  - destruct IHNR; dtr; [try solve [easy_wt]| |]; try solve [eauto].
  - destruct IHNR; dtr; [try solve [easy_wt]| |]; try solve [eauto].
  - inv WT; dtr. inv H2. inv H11. destruct t; narrow_terms. eauto.
  - inv WT; dtr. inv H2. inv H11. destruct t; narrow_terms. eauto.
  - inv WT; dtr. inv H2. inv H11. destruct t; narrow_terms; eauto.
  - destruct IHNR; dtr; [try solve [easy_wt]| |]; try solve [eauto].
  - eauto.
Unshelve.
auto.
auto.
Qed.

Lemma next_reduction_to_reduction :
  forall t t' rs b os,
  well_typed (C b os rs t) ->
  next_reduction t t' ->
  (exists t'' os', C b os rs t --> C b (os ++ os') rs t'') \/ (exists l, t' = t_downarrow (t_label l) /\ not (exists v, In (l ->>> v) rs)).
Proof using.
  intros t t' rs0 b0 os0 WT NR.
  apply next_reduction_to_reduction' with (t':=t') in WT; auto. destruct WT; dtr; eauto.
Qed.

Lemma term_to_next_reduction :
  forall t b os rs, well_typed (C b os rs t) -> not (value t) -> exists t', next_reduction t t'.
Proof using.
  induction t; intros b os rs WT; intros; eauto.
  - destruct (value_dec t1); destruct (value_dec t2); eauto.
    + copy H1. eapply IHt2 in H1. destruct H1. eauto. easy_wt.
    + copy H0. eapply IHt1 in H0. destruct H0. eauto. easy_wt.
    + copy H0. eapply IHt1 in H0. destruct H0. eauto. easy_wt.
  - crush.
  - crush.
  - crush.
  - crush.
  - destruct (value_dec t1); destruct (value_dec t2).
    + assert (value (t_ks_cons t1 t2)) by eauto; crush.
    + remember H1. clear Heqn. eapply IHt2 in H1. destruct H1. eauto. easy_wt.
    + remember H0. clear Heqn. eapply IHt1 in H0. destruct H0. eauto. easy_wt.
    + remember H0. clear Heqn. eapply IHt1 in H0. destruct H0. eauto. easy_wt.
  - destruct (value_dec t).
    + assert (exists l, t = t_label l).
      {
        inversion WT; dtr. find_type; narrow_terms.
      }
      destruct H1. info_eauto.
    + remember H0. clear Heqn. eapply IHt in H0. destruct H0. eauto. easy_wt.
  - destruct (value_dec t1).
    + destruct (value_dec t2).
      * {
        destruct (value_dec t3).
        - eauto.
        - remember H2. clear Heqn0. eapply IHt3 in H2. destruct H2. eauto. easy_wt.
        }
      * remember H1. clear Heqn0. eapply IHt2 in H1. destruct H1. eauto. easy_wt.
    + remember H0. clear Heqn0. eapply IHt1 in H0. destruct H0. eauto. easy_wt.
  - destruct (value_dec t1).
    + destruct (value_dec t2).
      * eauto.
      * remember H1. clear Heqn0. eapply IHt2 in H1. destruct H1. eauto. easy_wt.
    + remember H0. clear Heqn0. eapply IHt1 in H0. destruct H0. eauto. easy_wt.
  - destruct (value_dec t1).
    + destruct (value_dec t2).
      * eauto.
      * remember H1. clear Heqn0. eapply IHt2 in H1. destruct H1. eauto. easy_wt.
    + remember H0. clear Heqn0. eapply IHt1 in H0. destruct H0. eauto. easy_wt.
  - destruct (value_dec t1).
    + destruct (value_dec t2).
      * destruct (value_dec t3); [exfalso; apply H; eauto|].
        ceapply IHt3 in H2; dtr; eauto; easy_wt.
      * ceapply IHt2 in H1; dtr; eauto; easy_wt.
    + ceapply IHt1 in H0; dtr; eauto; easy_wt.
  - destruct (value_dec t).
    + eauto.
    + ceapply IHt in H0; dtr. eauto. easy_wt.
  - destruct (value_dec t).
    + eauto.
    + ceapply IHt in H0; dtr. eauto. easy_wt.
  - destruct (value_dec t).
    + eauto.
    + ceapply IHt in H0; dtr. eauto. easy_wt.
  - destruct (value_dec t0).
    + eauto.
    + ceapply IHt in H0; dtr. eauto. easy_wt.
Qed.

Lemma well_typed_backend_dist' : forall b b' ll ll',
  well_typed_backend ll ll' (b ++ b') ->
  exists ll'', well_typed_backend ll'' ll' b /\ well_typed_backend ll ll'' b'.
Proof using.
  induction b; intros.
  - exists ll'; crush.
  - simpl in *. inv H. apply IHb in H7; dtr. exi; eauto.
Qed.
Hint Resolve well_typed_backend_dist'.

Lemma well_typed_backend_empty : forall ll ll',
  well_typed_backend ll ll' [] ->
  ll = ll'.
Proof using.
  intros; inv H; auto.
Qed.
Hint Resolve well_typed_backend_empty.

Lemma well_typed_ostream_empty : forall ll ll',
  well_typed_ostream ll ll' [] ->
  ll = ll'.
Proof using.
  intros; inv H; auto.
Qed.
Hint Resolve well_typed_ostream_empty.

Lemma well_typed_backend_dist : forall b b' ll ll' ll'',
  well_typed_backend ll'' ll' b ->
  well_typed_backend ll ll'' b' ->
  well_typed_backend ll ll' (b ++ b').
Proof using.
  induction b; intros.
  - replace ll' with ll'' in * by auto; eauto.
  - simpl; destruct a; destruct n; inv H; econstructor; eauto.
Qed.
Hint Resolve well_typed_backend_dist.

Ltac wtbdist := match goal with
                | [H : well_typed_backend _ _ (_ ++ _) |- _] => apply well_typed_backend_dist' in H; dtr
                end.

Lemma graph_typing : forall b1 b2 os0 rs0 os t0 k t es,
    well_typed (C (b1 ++ <<N k t es; os>> :: b2) os0 rs0 t0) ->
    has_type empty (backend_types b2 (rstream_types rs0)) t Result false.
Proof using.
  intros.
  inv H.
  dtr.
  inv H.
  wtbdist.
  inv H2.
  wtbt.
  auto.
Qed.

Lemma well_typed_ostream_dist' : forall os os' ll ll',
  well_typed_ostream ll ll' (os ++ os') ->
  exists ll'', well_typed_ostream ll ll'' os /\ well_typed_ostream ll'' ll' os'.
Proof using.
  induction os; intros.
  - eauto.
  - simpl in *; destruct a; inv H; apply IHos in H4; dtr; exists x; crush.
Qed.
Hint Resolve well_typed_ostream_dist'.

Lemma well_typed_ostream_dist : forall os os' ll ll' ll'',
  well_typed_ostream ll ll'' os ->
  well_typed_ostream ll'' ll' os' ->
  well_typed_ostream ll ll' (os ++ os').
Proof using.
  induction os; intros.
  - inv H; subst; auto.
  - simpl; destruct a; destruct o; constructor; inv H; eauto.
Qed.
Hint Resolve well_typed_ostream_dist.

Ltac wtosdist := match goal with
             | [H : well_typed_ostream _ _ (_ ++ _) |- _] => apply well_typed_ostream_dist' in H; dtr
             end.

Lemma graph_typing' : forall b1 n os l f v ks os' b2 os0 rs0 t0,
    well_typed (C (b1 ++ <<n; os ++ l ->> pfold f v ks :: os'>> :: b2) os0 rs0 t0) ->
    has_type empty (ostream_types os (backend_types b2 (rstream_types rs0))) v Result false.
Proof using.
  intros.
  inv H; dtr.
  inv H.
  wtbdist.
  inv H2.
  wtosdist.
  inv H3.
  inv H15.
  wtbt.
  wtost.
  wtost.
  auto.
Qed.

Lemma well_typed_top_ostream_dist : forall os os' ll ll' ll'',
  well_typed_top_ostream ll ll'' os ->
  well_typed_top_ostream ll'' ll' os' ->
  well_typed_top_ostream ll ll' (os ++ os').
Proof using.
  induction os; intros.
  - inv H; auto.
  - simpl; destruct a; destruct o; constructor; inv H; eauto.
Qed.
Hint Resolve well_typed_top_ostream_dist.

Lemma well_typed_top_ostream_dist' : forall os os' ll ll',
  well_typed_top_ostream ll ll' (os ++ os') ->
  exists ll'', well_typed_top_ostream ll ll'' os /\ well_typed_top_ostream ll'' ll' os'.
Proof using.
  induction os; intros.
  - eauto.
  - simpl in *; destruct a; inv H; apply IHos in H6; dtr; exists x; crush.
Qed.
Hint Resolve well_typed_top_ostream_dist'.

Ltac wttosdist := match goal with
                  | [H : well_typed_top_ostream _ _ (_ ++ _) |- _] => apply well_typed_top_ostream_dist' in H; dtr
                  end.

Lemma graph_typing''' : forall b os l f v ks os' rs0 t0,
    well_typed (C b (os ++ l ->> pfold f v ks :: os') rs0 t0) ->
    has_type empty (ostream_types os (rstream_types rs0)) v Result false.
Proof using.
  intros.
  inv H; dtr.
  inv H.
  wttosdist.
  inv H2; dtr; subst; auto.
Qed.

Lemma graph_typing'' : forall b1 n os l f v ks os' b2 os0 rs0 t0,
    well_typed (C (b1 ++ <<n; os ++ l ->> pfold f v ks :: os'>> :: b2) os0 rs0 t0) ->
    has_type empty (ostream_types os (backend_types b2 (rstream_types rs0))) f (Arrow Result (Arrow Result Result false) false) false.
Proof using.
  intros.
  inv H; dtr.
  inv H.
  wtbdist.
  inv H2.
  wtosdist.
  inv H3.
  inv H15.
  wtbt.
  wtost.
  wtost.
  auto.
Qed.

Lemma value_no_emit : forall v Gamma ll T E,
  has_type Gamma ll v T E ->
  value v ->
  E = false.
Proof using.
  induction v; intros; try solve [inv H0]; try solve [inv H; eauto]; eauto.
  - inv H0. inv H. apply IHv1 in H6; auto. apply IHv2 in H9; auto. subst. auto.
  - inv H0. inv H. apply IHv1 in H8; auto. apply IHv2 in H11; auto. apply IHv3 in H12; auto. subst. auto.
Qed.

Lemma emittability' : forall t T t' rs os ll,
  has_type empty ll t T false ->
  FRf t rs ==> FRt t' os ->
  os = [].
Proof using.
  induction t; intros T t' rs os ll HHT Hstep.
  - inv Hstep.
  - inv Hstep.
    + auto.
    + inv HHT.
      eapply IHt1 in H0; eauto.
      destruct E1; destruct E2; destruct E3; try solve [inv H4]; eauto.
    + inv HHT.
      eapply IHt2 in H5; eauto.
      destruct E1; destruct E2; destruct E3; try solve [inv H4]; eauto.
  - exfalso; apply frontend_no_value in Hstep; eauto.
  - exfalso; apply frontend_no_value in Hstep; eauto.
  - exfalso; apply frontend_no_value in Hstep; eauto.
  - exfalso; apply frontend_no_value in Hstep; eauto.
  - inv Hstep.
    + inv HHT.
      eapply IHt1 in H0; eauto.
      destruct E1; destruct E2; try solve [inv H4]; eauto.
    + inv HHT.
      eapply IHt2 in H5; eauto.
      destruct E1; destruct E2; try solve [inv H4]; eauto.
  - inv Hstep.
    + auto.
    + eapply IHt in H0; eauto.
      inv HHT. eauto.
  - inv Hstep; inv HHT.
  - inv Hstep; inv HHT.
  - inv Hstep; inv HHT.
  - inv Hstep; inv HHT.
    + eapply IHt1 in H0; eauto.
      destruct E1; destruct E2; destruct E3; try solve [inv H5]; eauto.
    + eapply IHt2 in H6; eauto.
      destruct E1; destruct E2; destruct E3; try solve [inv H5]; eauto.
    + eapply IHt3 in H7; eauto.
      destruct E1; destruct E2; destruct E3; try solve [inv H5]; eauto.
  - inv Hstep; inv HHT; eauto.
  - inv Hstep; inv HHT; eauto.
  - inv Hstep; inv HHT; eauto.
  - inv Hstep; inv HHT; eauto.
Qed.

Lemma list_not_cons_self : forall {A : Type} (x : A) xs,
    x :: xs = xs -> False.
Proof using.
  induction xs; crush.
Qed.
Hint Resolve list_not_cons_self.

Lemma list_not_cons_self' : forall {A : Type} (x : A) xs,
  xs ++ [x] = xs -> False.
Proof using.
  induction xs; crush.
Qed.
Hint Resolve list_not_cons_self'.

Lemma list_app_self_nil : forall {A : Type} (xs : list A) ys,
  xs = xs ++ ys -> ys = [].
Proof using.
  induction xs; crush.
Qed.
Hint Resolve list_app_self_nil.

Lemma emittability : forall t T b os rs t' os' ll,
  has_type empty ll t T false ->
  C b os rs t --> C b (os ++ os') rs t' ->
  os' = [].
Proof using.
  intros t T b os rs t' os' ll HHT Hstep.
  inv Hstep; ssame'; try solve [exfalso; eauto]; try solve [eauto].
  - eapply emittability' in H5; eauto.
    apply List.app_inv_head in H0; subst; auto.
Qed.

Lemma nr_to_lafi : forall t l,
  next_reduction t (t_downarrow (t_label l)) ->
  lappears_free_in l t.
Proof using.
  induction t; intros; inv H; try solve [apply IHt1 in H4; auto]; try solve [apply IHt2 in H5; auto]; try solve [apply IHt3 in H6; auto]; try solve [apply IHt in H2; auto].
  - auto.
  - apply IHt1 in H6; auto.
  - apply IHt2 in H7; auto.
  - apply IHt3 in H8; auto.
  - apply IHt1 in H5; auto.
  - apply IHt2 in H6; auto.
  - apply IHt1 in H5; auto.
  - apply IHt2 in H6; auto.
  - apply IHt1 in H5; auto.
  - apply IHt2 in H6; auto.
  - apply IHt3 in H7; auto.
  - apply IHt in H4; auto.
Qed.

Lemma dependent_load_after : forall k t es l c b1 b2 os os0 rs0 term0,
  c = C (b1 ++ <<N k t es; os>> :: b2) os0 rs0 term0 ->
  next_reduction t (t_downarrow (t_label l)) ->
  well_typed c ->
  (exists v, In (l ->>> v) rs0) \/ (exists n' op b2' b2'' os'', b2 = b2' ++ <<n'; os''>> :: b2'' /\ In (l ->> op) os'').
Proof using.
  intros; subst.
  inv H1; dtr.
  inv H1.
  wtbdist.
  inv H3.
  apply nr_to_lafi in H0.
  eapply free_in_lcontext in H12; eauto.
  dtr.
  wtbt.
  apply lcontext_in_or_b in H3; destruct H3; dtr.
  - right. destruct x4. exists n, x6, x3, x5, l0. eauto.
  - left. apply type_in_rstream in H3; auto.
Qed.

Lemma dependent_loadpfold_after : forall l' l c b1 b2 t1 t2 t3 n os os' os0 rs0 term0,
  c = C (b1 ++ <<n; os ++ l' ->> pfold t1 t2 t3 :: os'>> :: b2) os0 rs0 term0 ->
  next_reduction t2 (t_downarrow (t_label l)) ->
  well_typed c ->
  (exists v, In (l ->>> v) rs0) \/ (exists op, In (l ->> op) os) \/ (exists n' op b2' b2'' os'', b2 = b2' ++ <<n'; os''>> :: b2'' /\ In (l ->> op) os'').
Proof using.
  intros; subst.
  inv H1; dtr.
  inv H1.
  wtbdist.
  inv H3.
  wtosdist.
  inv H4.
  inv H16.
  apply nr_to_lafi in H0.
  eapply free_in_lcontext with (l:=l) in H17; eauto; dtr.
  wtbt.
  wtost.
  wtost.
  apply lcontext_in_or_os in H4; destruct H4; dtr; eauto.
  - apply lcontext_in_or_b in H3; destruct H3; dtr; eauto.
    + right. right. destruct x2. exists n, x5, x1, x4, l0. eauto.
    + left. apply type_in_rstream in H3; auto.
Qed.

Lemma distinct_deduce1 : forall b l os os' rs,
  distinct (backend_labels b ++ l :: ostream_labels os ++ ostream_labels os' ++ rstream_labels rs) ->
  distinct (rstream_labels rs).
Proof using.
  intros.
  apply distinct_concat in H; dtr.
  apply distinct_remove in H0; dtr.
  apply distinct_concat in H0; dtr.
  apply distinct_concat in H2; dtr.
  auto.
Qed.
Hint Resolve distinct_deduce1.

Lemma distinct_deduce2 : forall l os os' rs,
  distinct (l :: ostream_labels os ++ ostream_labels os' ++ rstream_labels rs) ->
  distinct (rstream_labels rs).
Proof using.
  intros.
  apply distinct_remove in H; dtr.
  apply distinct_concat in H; dtr.
  apply distinct_concat in H1; dtr.
  auto.
Qed.
Hint Resolve distinct_deduce2.

Lemma op_reduction_exists : forall c b b1 b2 rs0 os0 term0 k t es os l op,
  well_typed c ->
  c = C b os0 rs0 term0 ->
  b = b1 ++ <<N k t es; l ->> op :: os>> :: b2 ->
  exists c', C b os0 rs0 term0 --> c'.
Proof using.
  intros c b b1 b2 rs0 os0 term0 k t es os l op WT Hceq Hbeq.
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
        - assert (has_type empty (rstream_types rs0) t1 Result false) by (eapply graph_typing' with (os:=[]) (b2:=[]); eauto).
          destruct t1; try solve [inv H]; try solve [inv H0].
          eapply ex_intro; eapply S_Last; eauto.
          Unshelve.
          right; eauto.
        - rename H into HNV. eapply term_to_next_reduction with (b:=[]) (os:=[]) (rs:=rs0) in HNV.
          + dtr. copy H. rename H0 into HNR. apply next_reduction_to_reduction' with (b:=[]) (os:=[]) (rs:=rs0) (t:=t1) in H.
            * {
              destruct H; dtr.
              - exi. eapply S_LoadPFold with (b1:=b1) (b2:=[]) (os:=[]) (t1:=t1) (t1':=x0); eauto. crush.
                assert (x1 = []).
                {
                  eapply emittability' in H; eauto.
                  instantiate (1:=Result).
                  instantiate (1:=rstream_types rs0).
                  inv WT; dtr. inv H2. apply well_typed_backend_dist' in H9; dtr.
                  inv H3. inv H15. inv H9. wtbt. auto.
                }
                subst.
                auto.
              - subst. eapply dependent_loadpfold_after with (os:=[]) (b2:=[]) in HNR.
                + destruct HNR.
                  * exfalso; eauto.
                  * {
                    destruct H.
                    - dtr. exfalso. auto.
                    - dtr. exfalso. destruct x2; inv H.
                    }
                + instantiate (1:=term0).
                  instantiate (1:=os0).
                  instantiate (1:=os).
                  instantiate (1:=l0).
                  instantiate (1:=t0).
                  instantiate (1:=l).
                  instantiate (1:=N k t es).
                  instantiate (1:=b1).
                  auto.
                + auto.
              }
            * inv WT; dtr. inv H2. wtbdist. inv H3. inv H15. inv H9. split; try split; eauto.
              crush. crush. eauto.
          + inv WT; dtr. split; try split; eauto. crush. crush. apply distinct_concat in H0; dtr.
            eauto.
            inv H1. wtbdist. inv H2. inv H14. inv H8. eauto.
        }
      * destruct s. eapply ex_intro; eapply S_Prop; eauto; crush.
Qed.

Lemma ll_update : forall t Gamma l T' ll T E,
  has_type Gamma ll t T E ->
  has_type Gamma (l #-> T'; ll) t T E.
Proof using.
  induction t; intros; try solve [inv H; eauto].
  - inv H. assert (n <> l) by (apply fresh_labels). constructor.
    replace ((l#->T';ll) n) with (ll n); auto.
    rewrite NMaps.update_neq; auto.
Qed.
Hint Resolve ll_update.

Lemma ht_ostream_extension : forall os ll t T E,
  has_type empty ll t T E ->
  has_type empty (ostream_types os ll) t T E.
Proof using.
  induction os; intros; auto.
  destruct a; simpl.
  apply IHos in H; eauto.
Qed.
Hint Resolve ht_ostream_extension.

Lemma ht_backend_extension : forall b ll t T E,
  has_type empty ll t T E ->
  has_type empty (backend_types b ll) t T E.
Proof using.
  induction b; intros; auto.
  destruct a; destruct n; simpl.
  apply IHb in H; eauto.
Qed.
Hint Resolve ht_backend_extension.

Lemma ll_extract_ostream : forall os l T ll,
    ostream_types os (l#->T;ll) = (l#->T;ostream_types os ll).
Proof using.
  induction os; intros; auto.
Qed.

Lemma ll_extract_backend : forall b l T ll,
    backend_types b (l#->T;ll) = (l#->T;backend_types b ll).
Proof using.
  induction b; intros; auto.
  destruct a; destruct n; simpl.
  rewrite <- ll_extract_ostream. rewrite IHb. auto.
Qed.

Lemma ll_swap_ostream_backend : forall os b ll,
  ostream_types os (backend_types b ll) = backend_types b (ostream_types os ll).
Proof using.
  induction os; intros; auto.
  destruct a; simpl. rewrite ll_extract_backend. crush.
Qed.

Lemma ll_swap_backend : forall b b' ll,
  backend_types b (backend_types b' ll) = backend_types b' (backend_types b ll).
Proof using.
  induction b; intros; auto.
  destruct a; destruct n; simpl. rewrite IHb. rewrite ll_swap_ostream_backend. auto.
Qed.

Lemma ht_ostream_extract : forall os ll l T' t T E,
  has_type empty (ostream_types os (l#->T';ll)) t T E ->
  has_type empty (l#->T';ostream_types os ll) t T E.
Proof using.
  induction os; intros; auto.
  destruct a; simpl in *.
  repeat (rewrite ll_extract_ostream in H).
  replace (n #-> op_type o; l #-> T'; ostream_types os ll)
          with (l#->T';n #-> op_type o; ostream_types os ll) in H.
  auto.
  apply NMaps.update_permute; apply fresh_labels.
Qed.

Lemma ht_ostream_extract' : forall os ll l T' t T E,
  has_type empty (l#->T';ostream_types os ll) t T E ->
  has_type empty (ostream_types os (l#->T';ll)) t T E.
Proof using.
  induction os; intros; auto.
  destruct a; simpl in *.
  repeat (rewrite ll_extract_ostream).
  replace (n #-> op_type o; l #-> T'; ostream_types os ll)
          with (l#->T';n #-> op_type o; ostream_types os ll).
  auto.
  apply NMaps.update_permute; apply fresh_labels.
Qed.

Lemma ht_ostream_extension' : forall os l T' ll t T E,
  has_type empty (ostream_types os ll) t T E ->
  has_type empty (ostream_types os (l#->T';ll)) t T E.
Proof using.
  intros.
  apply ht_ostream_extract'. auto.
Qed.
Hint Resolve ht_ostream_extension'.

Lemma ht_backend_extract' : forall b ll l T' t T E,
  has_type empty (l#->T';backend_types b ll) t T E ->
  has_type empty (backend_types b (l#->T';ll)) t T E.
Proof using.
  induction b; intros; auto.
  destruct a; destruct n; simpl in *.
  rewrite ll_extract_backend.
  rewrite ll_extract_ostream.
  auto.
Qed.

Lemma ht_backend_extension' : forall b l T' ll t T E,
  has_type empty (backend_types b ll) t T E ->
  has_type empty (backend_types b (l#->T';ll)) t T E.
Proof using.
  intros.
  apply ht_backend_extract'. auto.
Qed.
Hint Resolve ht_backend_extension'.

Lemma wt_operation_extension : forall ll l T op,
  well_typed_operation ll op ->
  well_typed_operation (l#->T;ll) op.
Proof using.
  intros.
  inv H; econstructor; eauto.
Qed.
Hint Resolve wt_operation_extension.

Lemma wt_ostream_build : forall os ll ll',
  well_typed_ostream ll ll' os ->
  well_typed_ostream ll (ostream_types os ll) os.
Proof using.
  induction os; intros; auto.
  destruct a; simpl in *.
  wtost'. simpl in *. auto.
Qed.

Lemma wt_ostream_extension : forall os ll ll' l T,
  well_typed_ostream ll ll' os ->
  exists ll'', well_typed_ostream (l#->T;ll) ll'' os.
Proof using.
  induction os; intros; eauto.
  destruct a; simpl in *. inv H. eapply IHos with (l:=l) (T:=T) in H4; dtr.
  wtost'. exi. econstructor; eauto.
  eapply wt_ostream_build.
  destruct o; simpl in *;
  replace (n #-> Result; l #-> T; ll) with (l#->T;n #-> Result;ll); eauto; apply NMaps.update_permute; apply fresh_labels.
Qed.
Hint Resolve wt_ostream_extension.

Lemma wt_ostream_backend_extract' : forall b os ll ll' l T,
  well_typed_ostream (l#->T;backend_types b ll) ll' os ->
  exists ll'', well_typed_ostream (backend_types b (l#->T;ll)) ll'' os.
Proof using.
  induction b; intros; eauto.
  destruct a; destruct n; simpl in *.
  wtost'.
  rewrite ll_extract_backend.
  rewrite ll_extract_ostream.
  eauto.
Qed.

Lemma wt_ostream_backend_extension' : forall b os l T ll ll',
  well_typed_ostream (backend_types b ll) ll' os ->
  exists ll'', well_typed_ostream (backend_types b (l#->T;ll)) ll'' os.
Proof using.
  intros.
  eapply wt_ostream_extension with (l:=l) (T:=T) in H; dtr.
  eapply wt_ostream_backend_extract'. eauto.
Qed.
Hint Resolve wt_ostream_backend_extension'.

Lemma wt_backend_build : forall b ll ll',
  well_typed_backend ll ll' b ->
  well_typed_backend ll (backend_types b ll) b.
Proof using.
  induction b; intros; auto.
  destruct a; destruct n; simpl in *.
  wtbt'. simpl in *. auto.
Qed.

Lemma wt_backend_extension : forall b ll ll' l T,
  well_typed_backend ll ll' b ->
  exists ll'', well_typed_backend (l#->T;ll) ll'' b.
Proof using.
  induction b; intros; eauto.
  destruct a; destruct n; simpl in *.
  inv H.
  wtbt'. wtost'.
  eapply IHb with (l:=l) (T:=T) in H; dtr.
  exists (ostream_types l0 (backend_types b (l#->T;ll))).
  econstructor. Focus 4.
  - eauto.
  - wtbt. wtost. eauto.
  - wtbt. wtost. eauto.
  - wtbt'. wtost'. apply wt_ostream_extension with (l:=l) (T:=T) in H; dtr.
    eapply wt_ostream_build.
    rewrite ll_extract_backend. eauto.
Qed.
Hint Resolve wt_backend_extension.

Lemma load_exists : forall c b b1 b2 rs0 os0 term0 k t es os,
  well_typed c ->
  c = C b os0 rs0 term0 ->
  b = b1 ++ <<N k t es; os>> :: b2 ->
  not (value t) ->
  exists c', C b os0 rs0 term0 --> c'.
Proof using.
  intros c b b1 b2 rs0 os0 term0 k t es os WT Hceq Hbeq HNV.
  assert (has_type empty (backend_types b2 (rstream_types rs0)) t Result false) by (subst; eapply graph_typing; eauto).
  destruct t; try solve [inv H; inv H3].
  - eapply term_to_next_reduction in HNV; subst; dtr.
    + copy H0. rename H1 into HNR. eapply next_reduction_to_reduction' with (rs:=rs0) in H0.
      * {
        destruct H0; dtr.
        - assert (x1 = []) by (eapply emittability'; eauto); subst.
          exi. eapply S_Load; eauto.
        - subst.
          edestruct dependent_load_after with (c:=C (b1 ++ << N k (t_app t1 t2) es; os >> :: b2) os0 rs0 term0) (l:=x0); eauto; dtr.
          + exfalso; eauto.
          + apply List.in_split in H2; dtr.
            subst.
            replace ((b1 ++ << N k (t_app t1 t2) es; os >> :: x2 ++ << x; x5 ++ x0 ->> x1 :: x6 >> :: x3))
                    with (((b1 ++ << N k (t_app t1 t2) es; os >> :: x2) ++ << x; x5 ++ x0 ->> x1 :: x6 >> :: x3)) by crush.
            destruct x. destruct x5; simpl.
            * eapply op_reduction_exists; eauto. crush.
            * destruct l. eapply op_reduction_exists; eauto. crush.
        }
      * instantiate (1:=os0).
        instantiate (1:=b1 ++ << N k (t_app t1 t2) es; os >> :: b2).
        inv WT; dtr.
        split; try split; eauto.
        inv H3.
        exists Result, false.
        econstructor.
        eauto.
        eauto.
        wtbdist.
        inv H4.
        wtbt.
        wtbt.
        wtost.
        wttost.
        auto.
    + instantiate (1:=rs0).
      instantiate (1:=os0).
      instantiate (1:=b1 ++ << N k (t_app t1 t2) es; os >> :: b2).
      inv WT; dtr.
      split; try split; eauto.
      inv H2.
      exists Result, false.
      econstructor.
      eauto.
      eauto.
      wtbdist.
      inv H3.
      wtbt.
      wtbt.
      wtost.
      wttost.
      auto.
  - exfalso. auto.
  - eapply term_to_next_reduction in HNV; subst; dtr.
    + copy H0. rename H1 into HNR. eapply next_reduction_to_reduction' with (rs:=rs0) in H0.
      * {
        destruct H0; dtr.
        - assert (x1 = []) by (eapply emittability'; eauto); subst.
          exi. eapply S_Load; eauto.
        - subst.
          edestruct dependent_load_after with (c:=C (b1 ++ << N k (t_downarrow t) es; os >> :: b2) os0 rs0 term0) (l:=x0); eauto; dtr.
          + exfalso; eauto.
          + apply List.in_split in H2; dtr.
            subst.
            replace ((b1 ++ << N k (t_downarrow t) es; os >> :: x2 ++ << x; x5 ++ x0 ->> x1 :: x6 >> :: x3))
                    with (((b1 ++ << N k (t_downarrow t) es; os >> :: x2) ++ << x; x5 ++ x0 ->> x1 :: x6 >> :: x3)) by crush.
            destruct x. destruct x5; simpl.
            * eapply op_reduction_exists; eauto. crush.
            * destruct l. eapply op_reduction_exists; eauto. crush.
        }
      * instantiate (1:=os0).
        instantiate (1:=(b1 ++ << N k (t_downarrow t) es; os >> :: b2)).
        inv WT; dtr.
        split; try split; eauto.
        inv H3.
        exists Result, false.
        econstructor.
        eauto.
        eauto.
        wtbdist.
        inv H4.
        wtbt.
        wtbt.
        wtost.
        wttost.
        auto.
    + instantiate (1:=rs0).
      instantiate (1:=os0).
      instantiate (1:=(b1 ++ << N k (t_downarrow t) es; os >> :: b2)).
      inv WT; dtr.
      split; try split; eauto.
      inv H2.
      exists Result, false.
      econstructor.
      eauto.
      eauto.
      wtbdist.
      inv H3.
      wtbt.
      wtbt.
      wtost.
      wttost.
      auto.
  - eapply term_to_next_reduction in HNV; subst; dtr.
    + copy H0. rename H1 into HNR. eapply next_reduction_to_reduction' with (rs:=rs0) in H0.
      * {
        destruct H0; dtr.
        - assert (x1 = []) by (eapply emittability'; eauto); subst.
          exi. eapply S_Load; eauto.
        - subst.
          edestruct dependent_load_after with (c:=C (b1 ++ << N k (t_na1 t) es; os >> :: b2) os0 rs0 term0) (l:=x0); eauto; dtr.
          + exfalso; eauto.
          + apply List.in_split in H2; dtr.
            subst.
            replace ((b1 ++ << N k (t_na1 t) es; os >> :: x2 ++ << x; x5 ++ x0 ->> x1 :: x6 >> :: x3))
                    with (((b1 ++ << N k (t_na1 t) es; os >> :: x2) ++ << x; x5 ++ x0 ->> x1 :: x6 >> :: x3)) by crush.
            destruct x. destruct x5; simpl.
            * eapply op_reduction_exists; eauto. crush.
            * destruct l. eapply op_reduction_exists; eauto. crush.
        }
      * instantiate (1:=os0).
        instantiate (1:=(b1 ++ << N k (t_na1 t) es; os >> :: b2)).
        inv WT; dtr.
        split; try split; eauto.
        inv H3.
        exists Result, false.
        econstructor.
        eauto.
        eauto.
        wtbdist.
        inv H4.
        wtbt.
        wtbt.
        wtost.
        wttost.
        auto.
    + instantiate (1:=rs0).
      instantiate (1:=os0).
      instantiate (1:=(b1 ++ << N k (t_na1 t) es; os >> :: b2)).
      inv WT; dtr.
      split; try split; eauto.
      inv H2.
      exists Result, false.
      econstructor.
      eauto.
      eauto.
      wtbdist.
      inv H3.
      wtbt.
      wtbt.
      wtost.
      wttost.
      auto.
  - eapply term_to_next_reduction in HNV; subst; dtr.
    + copy H0. rename H1 into HNR. eapply next_reduction_to_reduction' with (rs:=rs0) in H0.
      * {
        destruct H0; dtr.
        - assert (x1 = []) by (eapply emittability'; eauto); subst.
          exi. eapply S_Load; eauto.
        - subst.
          edestruct dependent_load_after with (c:=C (b1 ++ << N k (t_na2 t) es; os >> :: b2) os0 rs0 term0) (l:=x0); eauto; dtr.
          + exfalso; eauto.
          + apply List.in_split in H2; dtr.
            subst.
            replace ((b1 ++ << N k (t_na2 t) es; os >> :: x2 ++ << x; x5 ++ x0 ->> x1 :: x6 >> :: x3))
                    with (((b1 ++ << N k (t_na2 t) es; os >> :: x2) ++ << x; x5 ++ x0 ->> x1 :: x6 >> :: x3)) by crush.
            destruct x. destruct x5; simpl.
            * eapply op_reduction_exists; eauto. crush.
            * destruct l. eapply op_reduction_exists; eauto. crush.
        }
      * instantiate (1:=os0).
        instantiate (1:=(b1 ++ << N k (t_na2 t) es; os >> :: b2)).
        inv WT; dtr.
        split; try split; eauto.
        inv H3.
        exists Result, false.
        econstructor.
        eauto.
        eauto.
        wtbdist.
        inv H4.
        wtbt.
        wtbt.
        wtost.
        wttost.
        auto.
    + instantiate (1:=rs0).
      instantiate (1:=os0).
      instantiate (1:=(b1 ++ << N k (t_na2 t) es; os >> :: b2)).
      inv WT; dtr.
      split; try split; eauto.
      inv H2.
      exists Result, false.
      econstructor.
      eauto.
      eauto.
      wtbdist.
      inv H3.
      wtbt.
      wtbt.
      wtost.
      wttost.
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
  config_has_type (C b os rs (t_emit_pfold l t1 t2 t3)) T E ->
  exists T' E', config_has_type (C b os rs t1) T' E'.
Proof using.
  intros. inv H. inv H8. eauto.
Qed.
Hint Resolve cht_pfold1.

Lemma cht_pfold2 : forall b os rs l t1 t2 t3 T E,
  config_has_type (C b os rs (t_emit_pfold l t1 t2 t3)) T E ->
  exists T' E', config_has_type (C b os rs t2) T' E'.
Proof using.
  intros. inv H. inv H8. eauto.
Qed.
Hint Resolve cht_pfold2.

Lemma cht_pfold3 : forall b os rs l t1 t2 t3 T E,
  config_has_type (C b os rs (t_emit_pfold l t1 t2 t3)) T E ->
  exists T' E', config_has_type (C b os rs t3) T' E'.
Proof using.
  intros. inv H. inv H8. eauto.
Qed.
Hint Resolve cht_pfold3.

Lemma cht_pmap1 : forall b os rs l t1 t2 T E,
  config_has_type (C b os rs (t_emit_pmap l t1 t2)) T E ->
  exists T' E', config_has_type (C b os rs t1) T' E'.
Proof using.
  intros. inv H. inv H8. eauto.
Qed.
Hint Resolve cht_pmap1.

Lemma cht_pmap2 : forall b os rs l t1 t2 T E,
  config_has_type (C b os rs (t_emit_pmap l t1 t2)) T E ->
  exists T' E', config_has_type (C b os rs t2) T' E'.
Proof using.
  intros. inv H. inv H8. eauto.
Qed.
Hint Resolve cht_pmap2.

Lemma cht_add1 : forall b os rs l t1 t2 T E,
  config_has_type (C b os rs (t_emit_add l t1 t2)) T E ->
  exists T' E', config_has_type (C b os rs t1) T' E'.
Proof using.
  intros. inv H. inv H8. eauto.
Qed.
Hint Resolve cht_add1.

Lemma cht_add2 : forall b os rs l t1 t2 T E,
  config_has_type (C b os rs (t_emit_add l t1 t2)) T E ->
  exists T' E', config_has_type (C b os rs t2) T' E'.
Proof using.
  intros. inv H. inv H8. eauto.
Qed.
Hint Resolve cht_add2.

Lemma waiting_fold_value : forall b os rs l t t1 t2 t3,
  well_typed (C b (l ->> pfold t1 t2 t3 :: os) rs t) ->
  value t2.
Proof using.
  intros.
  inv H.
  dtr.
  inv H.
  inv H9.
  dtr. subst. auto.
Qed.

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
        exists (C b (os ++ []) rs (#[x:=t2]x0))...
        can_fun. inv H1. eauto.
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
        apply all_labels with (l:=label) in WT; auto.
        {
        destruct WT; dtr.
        - eauto.
        - destruct H0; dtr.
          + apply List.in_split in H0; dtr; subst.
            destruct x0; [|destruct l].
            * simpl; destruct x; destruct b; eauto; destruct s; eauto.
            * simpl; destruct o; eauto; destruct b; eauto; destruct s; eauto.
          + simpl in *.
            destruct x1.
            simpl in *.
            destruct l.
            * crush.
            * destruct l.
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
  - destruct IHET1...
    + inversion WT. split; crush; eauto.
      inv H1. inv H10.
      exists Result, E0.
      econstructor. eauto. eauto. eauto.
    + destruct IHET2...
      * inversion WT. split; crush; eauto.
        inv H2. inv H11.
        exists Result, E4.
        econstructor. eauto. eauto. eauto.
      * {
        destruct IHET3...
        - inversion WT. split; crush; eauto.
          inv H3. inv H12.
          exists Keyset, E5.
          econstructor. eauto. eauto. eauto.
        - right. dtr. inv H1; ssame; eauto.
        }
      * right. dtr. inv H0; ssame; eauto.
    + right. dtr. inv H; ssame; eauto.
  - destruct IHET...
    + inv WT. split; try split; eauto; dtr. inv H1. inv H10. exi; eauto.
    + destruct t; narrow_terms. eauto.
    + right. dtr. inv H; ssame; eauto.
  - destruct IHET...
    + inv WT. split; try split; eauto; dtr. inv H1. inv H10. exi; eauto.
    + destruct t; narrow_terms. eauto.
    + right. dtr. inv H; ssame; eauto.
  - destruct IHET...
    + inv WT. split; try split; eauto; dtr. inv H1. inv H10. exi; eauto.
    + destruct t; narrow_terms. eauto.
    + right. dtr. inv H; ssame; eauto.
  - destruct IHET...
    + inv WT. split; try split; eauto; dtr. inv H1. inv H10. exi; eauto.
    + right. dtr. inv H; ssame; eauto.
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
assert (value t0) by (eapply waiting_fold_value; eauto). inv WT'. dtr. inv H3. inv H11. inv H13. can_res. right. eauto.
auto.
auto.
assert (value t0) by (eapply waiting_fold_value; eauto). inv WT'. dtr. inv H3. inv H11. inv H13. can_res. right. eauto.
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

Lemma wt_cons : forall b a ll ll',
  well_typed_backend ll ll' (a :: b) ->
  exists ll'', well_typed_backend ll ll'' b.
Proof using.
  intros.
  inv H.
  eauto.
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
  inversion WT. subst c. destruct H1 as [T [E]]. rename H into Hdk; rename H0 into Hdl. inv H1. rename H7 into Hwtb. rename H6 into Hwtto. rename H8 into ET.
  remember WT as WT'. clear HeqWT'. apply progress with (b:=b) (os:=os) (rs:=rs) in WT'.
  destruct WT'.
  - destruct os.
    * {
      generalize dependent ll.
      generalize dependent ll'.
      induction b; intros ll' ET ll Hwtb Hwtto.
      - crush.
      - destruct a as [n os].
        destruct os.
        + assert (dry (C b [] rs t) \/ (exists c' : config, C b [] rs t --> c')).
          {
            eapply IHb.
            inversion WT.
            split; try split; crush.
            - apply distinct_remove in H0; dtr. auto.
            - exists x, x0. inv H2.
              econstructor; eauto.
              inv H9.
              replace ll0 with ll'1 in * by auto.
              wtbt'.
              auto.
            - eapply dck_cons; eauto.
            - eapply dcl_cons; eauto.
            - instantiate (1:=ll'); auto.
            - instantiate (1:=ll). inv Hwtb.
              replace ll with ll'0 in * by auto; auto.
            - auto.
          }
          destruct H0.
          * destruct n.
            {
            destruct (value_dec t0).
            - left.
              constructor; eauto.
              constructor; eauto.
              inv H0; eauto.
            - right.
              copy WT.
              eapply load_exists with (os:=[]) (b1:=[]) (b2:=b) (k:=n) (rs0:=rs) (t:=t0) (es:=e) in H2; eauto.
            }
          * right.
            destruct H0.
            {
            inversion H0; ssame; try solve [match goal with | [H : value _ |- _] => inv H end].
            - eapply ex_intro; eauto.
            - eapply ex_intro; eapply S_PMap; eauto; crush.
            - eapply ex_intro; eapply S_PFold; eauto; crush.
            - eapply ex_intro; eapply S_Last; eauto; crush.
              Unshelve.
              auto.
            - eapply ex_intro; eapply S_FusePMap; eauto; crush.
              Unshelve.
              auto.
            - eapply ex_intro; eapply S_Prop; eauto; crush.
            - exi; eapply S_Load; eauto; crush.
            - exi; eapply S_LoadPFold; eauto; crush.
            }
        + right.
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
          assert (has_type empty (rstream_types rs) t1 Result false) by (eapply graph_typing''' with (os:=[]); eauto).
          destruct t1; try solve [inv H; inv H4]; try solve [inv H0]; try solve [inv H1].
          right. eauto.
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
| afi_node1 : forall x k p es,
    appears_free_in x k ->
    appears_free_in x (t_node k p es)
| afi_node2 : forall x k p es,
    appears_free_in x p ->
    appears_free_in x (t_node k p es)
| afi_node3 : forall x k p es,
    appears_free_in x es ->
    appears_free_in x (t_node k p es)
| afi_downarrow : forall x t,
    appears_free_in x t ->
    appears_free_in x (t_downarrow t)
| afi_emit_getpay1 : forall x l t1 t2 t3,
    appears_free_in x t1 ->
    appears_free_in x (t_emit_pfold l t1 t2 t3)
| afi_emit_getpay2 : forall x l t1 t2 t3,
    appears_free_in x t2 ->
    appears_free_in x (t_emit_pfold l t1 t2 t3)
| afi_emit_getpay3 : forall x l t1 t2 t3,
    appears_free_in x t3 ->
    appears_free_in x (t_emit_pfold l t1 t2 t3)
| afi_emit_pmap1 : forall x l t1 t2,
    appears_free_in x t1 ->
    appears_free_in x (t_emit_pmap l t1 t2)
| afi_emit_pmap2 : forall x l t1 t2,
    appears_free_in x t2 ->
    appears_free_in x (t_emit_pmap l t1 t2)
| afi_emit_add1 : forall x l t1 t2,
    appears_free_in x t1 ->
    appears_free_in x (t_emit_add l t1 t2)
| afi_emit_add2 : forall x l t1 t2,
    appears_free_in x t2 ->
    appears_free_in x (t_emit_add l t1 t2)
| afi_na1 : forall x t,
    appears_free_in x t ->
    appears_free_in x (t_na1 t)
| afi_na2 : forall x t,
    appears_free_in x t ->
    appears_free_in x (t_na2 t)
| afi_na3 : forall x t,
    appears_free_in x t ->
    appears_free_in x (t_na3 t)
| afi_fix : forall x t T,
    appears_free_in x t ->
    appears_free_in x (t_fix T t).
Hint Constructors appears_free_in.

Definition closed (t:term) :=
  forall x, ~ appears_free_in x t.

Definition lclosed (t:term) :=
  forall l, ~ lappears_free_in l t.

Lemma free_in_context : forall x t T E Gamma ll,
   appears_free_in x t ->
   has_type Gamma ll t T E ->
   exists T', Gamma x = Some T'.
Proof using.
  intros x t T E Gamma ll H H0. generalize dependent Gamma.
  generalize dependent T.
  generalize dependent E.
  induction H;
         intros; try solve [inversion H0; eauto].
  - (* afi_abs *)
    inversion H1; subst.
    apply IHappears_free_in in H9.
    rewrite update_neq in H9; assumption.
Qed.

Corollary typable_empty__lclosed : forall t T E Gamma,
    has_type Gamma nempty t T E ->
    lclosed t.
Proof using.
  unfold lclosed. intros. intro.
  eapply free_in_lcontext with (ll:=nempty) in H0.
  destruct H0.
  inv H0.
  eauto.
Qed.

Corollary typable_empty__closed : forall t T E ll,
    has_type empty ll t T E ->
    closed t.
Proof using.
  unfold closed. intros. intro.
  eapply free_in_context with (Gamma:=empty) in H0.
  destruct H0.
  inv H0.
  eauto.
Qed.

Lemma lcontext_invariance : forall ll ll' Gamma t T E,
     has_type Gamma ll t T E ->
     (forall l, lappears_free_in l t -> ll l = ll' l) ->
     has_type Gamma ll' t T E.
Proof with eauto.
  intros.
  generalize dependent ll'.
  induction H; intros; auto; try solve [econstructor; eauto].
  - apply T_Label. rewrite <- H0...
Qed.

Lemma context_invariance : forall Gamma Gamma' ll t T E,
     has_type Gamma ll t T E ->
     (forall x, appears_free_in x t -> Gamma x = Gamma' x) ->
     has_type Gamma' ll t T E.
Proof with eauto.
  intros.
  generalize dependent Gamma'.
  induction H; intros; auto; try solve [econstructor; eauto].
  - (* T_Var *)
    apply T_Var. rewrite <- H0...
  - (* T_Abs *)
    apply T_Abs.
    apply IHhas_type. intros x1 Hafi.
    unfold update. unfold t_update. destruct (eqb_string x x1) eqn: Hx0x1...
    rewrite eqb_string_false_iff in Hx0x1. auto.
Qed.

Lemma substitution_preserves_typing : forall Gamma ll x U t v T E1,
  has_type (x |-> U ; Gamma) ll t T E1 ->
  has_type empty ll v U false ->
  has_type Gamma ll (#[x:=v]t) T E1.
Proof with eauto.
  intros Gamma ll x U t v T E1 Ht Ht'.
  generalize dependent Gamma. generalize dependent T. generalize dependent E1. generalize dependent Ht'. generalize dependent ll.
  induction t; intros ll Ht' E1 T Gamma H;
    inversion H; subst; simpl...
  - (* var *)
    rename s into y. destruct (eqb_stringP x y) as [Hxy|Hxy].
    + (* x=y *)
      subst.
      rewrite update_eq in H3.
      inversion H3; subst.
      eapply context_invariance.
      * eapply lcontext_invariance. eassumption.
        auto.
      * apply typable_empty__closed in Ht'. unfold closed in Ht'.
        intros.  apply (Ht' x) in H0. inversion H0.
    + (* x<>y *)
      apply T_Var. rewrite update_neq in H3...
  - (* abs *)
    rename s into y. rename t into T. apply T_Abs.
    destruct (eqb_stringP x y) as [Hxy | Hxy].
    + (* x=y *)
      subst. rewrite update_shadow in H7. apply H7.
    + (* x<>y *)
      apply IHt. assumption. eapply context_invariance...
      intros z Hafi. unfold update, t_update.
      destruct (eqb_stringP y z) as [Hyz | Hyz]; subst; trivial.
      rewrite <- eqb_string_false_iff in Hxy.
      rewrite Hxy...
Qed.

Lemma emit_well_typed_top_ostream : forall t b os os' rs t' T E,
  config_has_type (C b os rs t) T E ->
  FRf t rs ==> FRt t' os' ->
  exists ll, well_typed_top_ostream (ostream_types os (backend_types b (rstream_types rs))) ll os'.
Proof using.
  induction t; intros;
  rename H into HT;
  inversion HT; subst;
  inv H8.
  - inv H3.
  - inversion H0; eauto.
  - inversion H0; eauto.
  - inversion H0; eauto.
  - inversion H0; eauto.
  - inversion H0; eauto.
  - inversion H0; eauto.
  - inversion H0; eauto.
  - inversion H0; eauto; subst.
    + econstructor. econstructor; eauto.
      constructor; eauto.
      * wtbt. wttost. assert (E1 = false) by (eapply value_no_emit; eauto); subst.
        auto.
      * wtbt. wttost. assert (E2 = false) by (eapply value_no_emit; eauto); subst.
        auto.
  - inversion H0; eauto; subst.
    + econstructor. econstructor; eauto.
      constructor; eauto.
      assert (E1 = false) by (eapply value_no_emit; eauto); subst.
      wtbt. wttost. auto.
  - inversion H0; eauto.
  - inversion H0; eauto.
  - inversion H0; eauto.
  - inversion H0; eauto.
  - inversion H0; eauto.
  - inversion H0; eauto.
Qed.
Hint Resolve emit_well_typed_top_ostream.

Lemma wt_btop_cons : forall n os os0 op b l ll ll' ll'',
  well_typed_backend ll ll' (<<n; os>> :: b) ->
  well_typed_top_ostream ll' ll'' (l ->> op :: os0) ->
  exists ll''', well_typed_backend ll ll''' (<<n; os ++ [l ->> op]>> :: b).
Proof using.
  intros.
  inv H.
  inv H0.
  destruct op; eauto.
Qed.
Hint Resolve wt_btop_cons.

Lemma wt_top_to_ht1 : forall l k v os ll ll',
  well_typed_top_ostream ll ll' (l ->> add k v :: os) ->
  has_type empty ll v Result false.
Proof using.
  intros. inv H. inv H7. auto.
Qed.
Hint Resolve wt_top_to_ht1.

Lemma wt_to_wt1 : forall b1 k v es l f ks os b2 ll ll',
  well_typed_backend ll ll' (b1 ++ << N k v es; l ->> pmap f ks :: os >> :: b2) ->
  well_typed_backend ll ll' (b1 ++ << N k (t_app f v) es; l ->> pmap f (remove Nat.eq_dec k ks) :: os >> :: b2).
Proof using.
  intros.
  wtbdist.
  eapply well_typed_backend_dist; eauto.
  inv H0.
  inv H10.
  inv H6.
  econstructor; eauto.
  - remember H5. clear Heqh. can_fun.
    assert (false = false || false || false)%bool by crush.
    rewrite H0; clear H0.
    eapply T_App with Result.
    constructor.
    inv H5.
    auto.
    auto.
Qed.
Hint Resolve wt_to_wt1.

Lemma wt_to_wt2 : forall b1 k t es l f t' ks os b2 ll ll',
  well_typed_backend ll ll' (b1 ++ << N k t es; l ->> pfold f t' ks :: os >> :: b2) ->
  well_typed_backend ll ll' (b1 ++ << N k t es; l ->> pfold f (t_app (t_app f t) t') (remove Nat.eq_dec k ks) :: os >> :: b2).
Proof using.
  intros.
  wtbdist.
  eapply well_typed_backend_dist; eauto.
  inv H0.
  inv H10.
  inv H6.
  econstructor; eauto.
  - remember H8. clear Heqh. can_fun.
    constructor; eauto.
    constructor; eauto.
    assert (false = false || false || false)%bool by crush.
    rewrite H0.
    eapply T_App with Result.
    rewrite H0.
    eapply T_App with Result.
    constructor.
    inv H8.
    auto.
    auto.
    auto.
Qed.
Hint Resolve wt_to_wt2.

Lemma wt_to_wt3 : forall b n l op os ll ll',
  well_typed_backend ll ll' (b ++ [<< n; l ->> op :: os >>]) ->
  well_typed_backend (l#->(op_type op);ll) ll' (b ++ [<< n; os >>]).
Proof using.
  intros.
  wtbdist.
  eapply well_typed_backend_dist; eauto.
  inv H0.
  inv H8.
  replace ll'0 with ll in * by auto.
  econstructor; [| | eauto|eauto].
  - auto.
  - auto.
Qed.
Hint Resolve wt_to_wt3.

Lemma wt_to_wt4 : forall b1 n os l f l' f' ks os' b2 ll ll',
  well_typed_backend ll ll' (b1 ++ << n; os ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os' >> :: b2) ->
  exists ll'', well_typed_backend (l#->(op_type (pmap f ks));ll) ll'' (b1 ++ << n; os ++ l' ->> pmap (pmap_compose f' f) ks :: os' >> :: b2).
Proof using.
  intros.
  wtbdist.
  inv H0.
  wtosdist.
  inversion H1.
  inv H11.
  can_fun.
  simpl in *.
  copy H; wtbt.
  exi; eapply well_typed_backend_dist.
  - instantiate (1:=backend_types b1 x).
    instantiate (1:=x).
    auto.
  - wtbt'. wtost'.
    econstructor. Focus 4.
    + instantiate (1:=backend_types b2 (l#->Result;ll)).
      eapply wt_backend_extension with (l:=l) (T:=Result) in H2; dtr.
      eapply wt_backend_build; eauto.
    + eauto.
    + eauto.
    + eapply well_typed_ostream_dist; simpl in *.
      * instantiate (1:=ostream_types os (backend_types b2 (l#->Result;ll))).
        eapply wt_ostream_backend_extension' with (l:=l) (T:=Result) in H0; dtr.
        eapply wt_ostream_build. eauto.
      * {
        constructor; simpl in *.
        - apply wt_to_ostream_types in H0; subst.
          inv H3; simpl in *.
          rewrite ll_extract_backend.
          rewrite ll_extract_ostream. auto.
        - constructor; unfold pmap_compose in *; eauto.
          + constructor.
            replace false with (false || false || false) by auto; econstructor; simpl.
            * inv H3. inv H12.
              wtost. wtost. wtost. instantiate (1:=Result).
              simpl in *.
              {
              eapply context_invariance with (Gamma:=empty).
              + rewrite ll_extract_backend. rewrite ll_extract_ostream. auto.
              + intros; apply typable_empty__closed in H9; unfold closed in H9; exfalso; apply (@H9 x); auto.
              }
            * {
              replace false with (false || false || false) by auto; econstructor; simpl.
                - instantiate (1:=Result).
                  inv H1. inv H12.
                  wtbt. wtbt. wtost. wtost. wtost.
                  eapply context_invariance with (Gamma:=empty).
                  + rewrite ll_extract_backend. rewrite ll_extract_ostream. eauto.
                  + intros; apply typable_empty__closed in H9; unfold closed in H9; exfalso; apply (@H9 x); auto.
                - auto.
              }
        }
Qed.
Hint Resolve wt_to_wt4.

Lemma wt_to_wt5 : forall b1 n l op os n' os' b2 ll ll',
  well_typed_backend ll ll' (b1 ++ << n; l ->> op :: os >> :: << n'; os' >> :: b2) ->
  well_typed_backend ll ll' (b1 ++ << n; os >> :: << n'; os' ++ [l ->> op] >> :: b2).
Proof using.
  intros; wtbdist; eapply well_typed_backend_dist; eauto.
  inv H0. inv H8. inv H9.
  econstructor; [| |eauto|eauto].
  - eauto.
  - eauto.
Qed.
Hint Resolve wt_to_wt5.

Lemma cht_to_ht : forall b os rs t T E,
  config_has_type (C b os rs t) T E ->
  has_type empty (ostream_types os (backend_types b (rstream_types rs))) t T E.
Proof using.
  intros; inv H; wtbt; wttost; auto.
Qed.
Hint Resolve cht_to_ht.

Lemma cht_to_wtop_cons : forall b l op os rs t T E,
  config_has_type (C b (l ->> op :: os) rs t) T E ->
  exists ll, well_typed_top_ostream (l#->(op_type op);backend_types b (rstream_types rs)) ll os.
Proof using.
  intros; inv H; wtbt; inv H7; eauto.
Qed.
Hint Resolve cht_to_wtop_cons.

Axiom label_types_only_results : forall (ll:lcontext) l T, ll l = Some T -> T = Result.

Ltac inv_type := try (match goal with | [H : config_has_type _ _ _ |- _] => inv H end);
                      match goal with | [H : has_type _ _ _ _ _ |- _] => inv H end.

Hint Immediate NMaps.update_eq.

Theorem preservation' : forall t rs os t' ll T E,
  has_type empty ll t T E ->
  FRf t rs ==> FRt t' os ->
  exists E', has_type empty (ostream_types os ll) t' T E' /\ (match E with
                                                         | false => E' = false
                                                         | _ => True
                                                         end).
Proof using.
  induction t; intros; try solve [inv H0].
  - inv H0.
    + exists E. split; [|destruct E; auto].
      inv H. inv H5.
      assert (E3 = false) by (eapply value_no_emit; eauto); subst.
      replace (E1 || false || false) with E1.
      eapply substitution_preserves_typing; eauto.
      destruct E1; auto.
    + inv H.
      eapply IHt1 with (ll:=ll) (T:=Arrow T11 T E1) (E:=E2) in H2; dtr.
      exists (E1 || x || E3). split.
      * {
        econstructor.
        - instantiate (1:=T11).
          eauto.
        - auto.
        }
      * destruct E1; destruct E2; destruct E3; crush.
      * auto.
    + inv H.
      eapply IHt2 with (T:=T11) (E:=E3) in H7; dtr.
      exists (E1 || E2 || x). split.
      * eauto.
      * destruct E1; destruct E2; destruct E3; crush.
      * eauto.
  - inv H0.
    + inv H.
      eapply IHt1 in H2; eauto; dtr.
      exists (x || E2). split; eauto.
      * destruct E1; destruct E2; crush.
    + inv H.
      eapply IHt2 in H7; eauto; dtr.
      exists (E1 || x). split; eauto.
      * destruct E1; destruct E2; crush.
  - inv H0.
    + inv H. exists E. inv H4. apply label_types_only_results in H5; subst. split; eauto.
    + inv H.
      eapply IHt in H2; eauto; dtr.
      exists x. split; eauto.
  - inv H0.
    + inv H. exists false. split; simpl; eauto.
    + inv H.
      eapply IHt1 in H2; eauto; dtr.
      exists true. split; eauto.
    + inv H.
      eapply IHt2 in H11; eauto; dtr.
      exists true. split; eauto.
    + inv H.
      eapply IHt3 in H13; eauto; dtr.
      exists true. split; eauto.
  - inv H0.
    + inv H. exists false. split; simpl; eauto.
    + inv H.
      eapply IHt1 in H2; eauto; dtr.
      exists true. split; eauto.
    + inv H.
      eapply IHt2 in H10; eauto; dtr.
      exists true. split; eauto.
  - inv H0.
    + inv H. exists false. split; simpl; auto.
    + inv H.
      eapply IHt1 in H2; eauto; dtr.
      exists true. split; eauto.
    + inv H.
      eapply IHt2 in H10; eauto; dtr.
      exists true. split; eauto.
  - inv H0.
    + inv H.
      eapply IHt1 in H2; eauto; dtr.
      exists (x || E2 || E3). split; eauto.
      * destruct E1; destruct E2; destruct E3; crush.
    + inv H.
      eapply IHt2 in H8; eauto; dtr.
      exists (E1 || x || E3). split; eauto.
      * destruct E1; destruct E2; destruct E3; crush.
    + inv H.
      eapply IHt3 in H9; eauto; dtr.
      exists (E1 || E2 || x). split; eauto.
      * destruct E1; destruct E2; destruct E3; crush.
  - inv H0.
    + inv H. eapply IHt in H2; eauto; dtr. exists x. split; eauto.
    + inv H. inv H3. assert (E1 = false) by (eapply value_no_emit; eauto); subst. simpl. exists false. split; eauto. destruct E2; destruct E3; crush.
  - inv H0.
    + inv H. eapply IHt in H2; eauto; dtr. exists x. split; eauto.
    + inv H. inv H3. assert (E2 = false) by (eapply value_no_emit; eauto); subst. simpl. exists false. split; eauto. destruct E1; destruct E3; crush.
  - inv H0.
    + inv H. eapply IHt in H2; eauto; dtr. exists x. split; eauto.
    + inv H. inv H3. assert (E3 = false) by (eapply value_no_emit; eauto); subst. simpl. exists false. split; eauto. destruct E1; destruct E2; crush.
  - inv H0.
    + inv H. exists (false || false || false). split; [|destruct E; auto].
      assert (E = false) by (eapply value_no_emit; eauto); subst.
      constructor.
      replace (E2 || E3) with (E2 || E3 || false).
      econstructor; [instantiate (1:=t)|].
      * replace E3 with (E3 || false || false).
        {
        econstructor; [instantiate (1:=(Arrow t t (E2 || E3)))|].
        - apply context_invariance with empty; auto.
          intros; apply typable_empty__closed in H7; unfold closed in H7; exfalso; apply (@H7 x); auto.
        - replace false with (false || false || false).
          econstructor; simpl.
          apply context_invariance with empty. auto.
          intros; apply typable_empty__closed in H7; unfold closed in H7; exfalso; apply (@H7 x); auto.
          auto.
        }
        destruct E3; auto.
      * auto.
      * destruct E2; destruct E3; auto.
    + inv H. eapply IHt in H7; eauto; dtr.
      exists x. split; eauto.
Qed.

Lemma ostream_types_app : forall os os' ll,
  ostream_types (os ++ os') ll = ostream_types os' (ostream_types os ll).
Proof using.
  induction os; intros; auto.
  destruct a; simpl.
  rewrite IHos. crush.
Qed.

Lemma backend_types_app : forall b b' ll,
  backend_types (b ++ b') ll = backend_types b' (backend_types b ll).
Proof using.
  induction b; intros; auto.
  destruct a; destruct n; simpl.
  rewrite IHb. rewrite ll_swap_ostream_backend. auto.
Qed.

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
  - inversion Hht; subst.
    copy H0. rename H0 into Hstep. apply preservation' with (ll:=ll') (T:=T) (E:=E) in H; eauto; dtr.
    exists x. split; eauto.
    wtbt'. wttost'.
    econstructor.
    + eauto.
    + instantiate (1:=ostream_types os' (ostream_types os (backend_types b (rstream_types rs)))).
      apply emit_well_typed_top_ostream with (T:=T) (E:=E) (b:=b) (os:=os) in Hstep; auto; dtr.
      copy H3. apply wt_to_top_ostream_types in H3; subst.
      eapply well_typed_top_ostream_dist; eauto.
    + auto.
  - subst. exists E. split; eauto. econstructor; auto.
    + apply cht_to_wtop_cons in Hht; dtr. simpl in *. wttost'. instantiate (1:=ostream_types os' (l#->op_type op; rstream_types rs)). destruct op; simpl in *; auto.
    + inv Hht. wtbt. wttost. destruct op; simpl in *; rewrite ll_extract_ostream; auto.
    + destruct E; auto.
  - subst. exists E. split; eauto; [|destruct E; auto]. econstructor; eauto.
    + inv Hht. instantiate (1:=backend_types (<<n1;os1++[l->>op]>>::b') (rstream_types rs)).
      wtbt'. wttost'.
      eapply wt_backend_build. destruct n1. econstructor. Focus 4.
      * instantiate (1:=backend_types b' (rstream_types rs)).
        inv H.
        eapply wt_backend_build; eauto.
      * inv H. wtbt. eauto.
      * inv H. wtbt. eauto.
      * {
        eapply well_typed_ostream_dist.
        - inv H. wtbt. eauto.
        - constructor; eauto. inv H0. auto.
        }
    + destruct n1; simpl in *. rewrite ostream_types_app. simpl in *.
      rewrite <- ll_extract_ostream.
      rewrite <- ll_extract_ostream.
      rewrite ll_extract_ostream.
      inv Hht.
      wtbt. simpl in *. inv H7. wttost'. auto.
  - subst. exists E. split; eauto; [|destruct E; auto]. econstructor; auto.
    + simpl in *. econstructor. Focus 4.
      * instantiate (1:=backend_types b (l#->Result;rstream_types rs)).
        inv Hht. wtbt'. wttost'.
        apply wt_backend_extension with (l:=l) (T:=Result) in H0; dtr.
        eapply wt_backend_build; eauto.
      * inv Hht. inv H7. inv H10. wtbt'. eauto.
      * inv Hht. inv H7. inv H10. wtbt'. eauto.
      * inv Hht. inv H7. inv H10. wtbt'. eauto.
    + inv Hht. wtbt. inv H7. simpl in *. rewrite ll_extract_backend. wttost'. eauto.
    + inv Hht. wtbt. wttost. simpl in *. rewrite ll_extract_ostream. eauto.
  - subst. exists E. split; eauto; [|destruct E; auto]. econstructor; auto; inv Hht.
    + apply wt_to_wt1 in H6; dtr. simpl in *. wtbt'. eauto.
    + wtbt. rewrite backend_types_app in *. simpl in *. wttost'. eauto.
    + wtbt. rewrite backend_types_app in H7. simpl in *. wttost. eauto.
  - subst. exists E. split; eauto; [|destruct E; auto]. econstructor; auto; inv Hht.
    + apply wt_to_wt2 in H6; dtr. simpl in *. wtbt'. eauto.
    + wtbt. rewrite backend_types_app in *. simpl in *. wttost'. eauto.
    + wtbt. rewrite backend_types_app in H7. simpl in *. wttost. eauto.
  - subst. exists E. split; eauto; [|destruct E; auto]. econstructor; auto; inv Hht.
    + apply wt_to_wt3 in H7; dtr. simpl in *. wtbt'. destruct op; eauto.
    + simpl in *. wtbt. wttost'. rewrite backend_types_app in *. simpl in H0. destruct n1; simpl in *.
      rewrite ll_extract_backend.
      rewrite ll_extract_ostream.
      eauto.
    + wtbt. wttost. rewrite backend_types_app in H9. simpl in *. destruct n1; simpl in *. auto.
  - subst. exists E. split; eauto; [|destruct E; auto]. econstructor; auto; inv Hht.
    + apply wt_to_wt4 in H6; dtr. simpl in *. wtbt'. eauto.
    + simpl in *. wtbt. wttost'. rewrite backend_types_app in *. simpl in *. destruct n; simpl in *.
      clear H8.
      rewrite ostream_types_app in *; simpl in *.
      rewrite ll_extract_backend.
      rewrite ll_extract_backend.
      rewrite ll_extract_ostream.
      rewrite ll_extract_ostream.
      replace (l' #-> Result; l #-> Result; ostream_types os2 (ostream_types os1 (backend_types b2 (backend_types b1 (rstream_types rs)))))
              with (l #-> Result; l' #-> Result; ostream_types os2 (ostream_types os1 (backend_types b2 (backend_types b1 (rstream_types rs))))).
      eauto.
      apply NMaps.update_permute. apply fresh_labels.
    + wtbt. wttost. rewrite backend_types_app in *. simpl in *. destruct n; simpl in *.
      rewrite ostream_types_app in *; simpl in *; eauto.
  - subst. exists E. split; eauto; [|destruct E; auto]. econstructor; auto; inv Hht.
    + wtbdist. inv H1. inv H11. inv H12.
      copy H6; apply wt_to_ostream_types in H6; subst.
      copy H15; apply wt_to_ostream_types in H15; subst.
      copy H; apply wt_to_backend_types in H; subst.
      copy H7; apply wt_to_top_ostream_types in H7; subst.
      copy H16; apply wt_to_backend_types in H16; subst.
      eapply well_typed_backend_dist; eauto.
      econstructor. Focus 4.
      * instantiate (1:=ostream_types (os2 ++ [l ->> op]) (backend_types b2 (rstream_types rs))).
        econstructor; eauto.
        rewrite ostream_types_app. simpl in *. eapply well_typed_ostream_dist; eauto.
      * rewrite ostream_types_app. eauto.
      * rewrite ostream_types_app. eauto.
      * rewrite ostream_types_app. eauto.
    + wtbt. wttost'. rewrite backend_types_app in H. simpl in *. destruct n2; simpl in *. destruct n1; simpl in *.
      rewrite ll_extract_ostream. rewrite ll_extract_backend.
      rewrite <- ll_swap_ostream_backend. rewrite <- ll_swap_ostream_backend.
      rewrite ll_swap_backend. eauto.
    + wtbt. wttost. rewrite backend_types_app in H8. simpl in *. destruct n1; destruct n2; simpl in *. eauto.
  - subst. exists E. split; [|destruct E; eauto].
    inv Hht. apply well_typed_backend_dist' in H6; dtr. inv H0.
    copy H1. rename H1 into Hstep. eapply preservation' with (T:=Result) (E:=false) in H0; dtr; subst; eauto.
  - subst. exists E. split; [|destruct E; eauto].
    inv Hht. apply well_typed_backend_dist' in H6; dtr. inv H0.
    wtosdist. inv H2. inv H13.
    copy H1. rename H1 into Hstep. eapply preservation' with (T:=Result) (E:=false) in H2; dtr; subst; eauto.
    econstructor; eauto.
    eapply well_typed_backend_dist; auto.
    + instantiate (1:=x); auto.
    + copy H14; apply wt_to_backend_types in H14; subst.
      copy H9; apply wt_to_ostream_types in H9; subst.
      copy H0; apply wt_to_ostream_types in H0; subst.
      copy H; apply wt_to_backend_types in H; subst.
      copy H7; apply wt_to_top_ostream_types in H7; subst.
      simpl in *.
      assert (well_typed_backend (rstream_types rs0) (backend_types (<< N k t es; os ++ l ->> pfold f t1' ks :: os' >> :: b2) (rstream_types rs0)) (<< N k t es; os ++ l ->> pfold f t1' ks :: os' >> :: b2)).
      {
        eapply wt_backend_build; eauto.
      }
      simpl in H5. rewrite ostream_types_app in H5. simpl in H5.
      eauto.
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
    + subst. exfalso; eapply frontend_no_value; eauto.
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
            apply dry_no_in with (n:=N k v0 es) (s:=<< N k v0 es; l ->> pmap f ks :: os1'' >>) (os:=l ->> pmap f ks :: os1'') in H6; crush.
        }
    + subst. inv H0.
      * destruct b2; crush.
      * {
          destruct b2.
          - inv H5; crush.
          - inv H5.
            apply dry_no_in with (n:=N k t0 es) (s:=<< N k t0 es; l ->> pfold f t' ks :: os1'' >>) (os:=l ->> pfold f t' ks :: os1'') in H6; crush.
        }
    + subst. inv H0.
      * destruct b2; crush.
      * {
          destruct b2.
          - inv H5; crush.
          - inv H5.
            eapply dry_no_in with (n:=n1) (os:=l ->> op :: os1') in H6; eauto; crush.
        }
    + subst. inv H0.
      * destruct b2; crush.
      * {
          destruct b2.
          - inv H5; crush.
          - inv H5.
            eapply dry_no_in with (n:=n1) (os:=l ->> op :: os1') in H6; eauto; crush.
        }
    + subst. inv H0.
      * destruct b2; crush.
      * {
          destruct b2.
          - inv H5; crush.
            destruct os1; crush.
          - inv H5.
            eapply dry_no_in with (n:=n) (os:=os1 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os2) in H6; eauto; crush. destruct os1; crush.
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
            eapply dry_no_in with (n:=n1) (os:=l ->> op :: os1) in H7; eauto; crush.
        }
    + subst. inv H2. inv H4.
      apply dry_backend_dist with (b1:=b2) (b2:=<< N k t0 es; os1 >> :: b3) in H0; eauto.
      destruct H0.
      inv H2.
      simpl in H8.
      apply frontend_no_value in H6. apply H6. eauto.
    + subst. inv H2. inv H4.
      apply dry_backend_dist with (b1:=b2) (b2:=<< N k t0 es; os1 ++ l ->> pfold f t1 ks :: os' >> :: b3) in H0; eauto.
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
                  subst. exists x, x0. econstructor.
                  + instantiate (1:=ll).
                    inv H10.
                    replace ll with ll'0 in * by eauto.
                    auto.
                  + instantiate (1:=ll'). auto.
                  + auto.
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
          auto.
          assert (value t1) by (eapply waiting_fold_value; eauto).
          assert (has_type empty (rstream_types rs) t1 Result false) by (eapply graph_typing''' with (os:=[]); eauto).
          destruct t1; try solve [inv H; inv H4]; try solve [inv H1]; try solve [inv H2].
          right. eauto.
        }
    + crush.
Qed.

Definition stuck c : Prop := normal_form c /\ ~ dry c.

(* ****** end typing *)

Ltac apply_preservation :=
  match goal with
  | [H: C _ _ _ _ --> C _ _ _ _ |- _] => eapply preservation in H; eauto
  end.

Axiom fresh :
  forall b os rs t t' os',
  distinct (config_labels (C b os rs t)) ->
  C b os rs t --> C b (os ++ os') rs t' ->
  distinct (config_labels (C b (os ++ os') rs t')).

Axiom fresh' :
  forall b os rs t os' t',
  distinct (config_keys (C b os rs t)) ->
  C b os rs t --> C b (os ++ os') rs t' ->
  distinct (config_keys (C b (os ++ os') rs t')).

Lemma well_typed_preservation :
  forall c1 c2,
  well_typed c1 ->
  c1 --> c2 ->
  well_typed c2.
Proof using.
  intros.
  inversion H0; inversion H; eapply WT; subst;
  try solve [match goal with | [H : exists _ _, _|- _] => destruct H as [T[E]] end; apply preservation with (T:=T) (E:=E) in H0; auto; destruct H0; destruct H0; inv H0; eauto];
  try solve [match goal with | [H : distinct (config_keys _) |- _] => eapply fresh' in H end; [|eauto]; crush];
  try solve [match goal with | [H : distinct (config_labels _) |- _] => eapply fresh in H end; [|eauto]; crush];
  try solve [apply_preservation].
  (* S_Empty *)
  - destruct op; crush.
  (* S_First *)
  - crush.
  - destruct op; crush.
  - crush. unfold backend_labels. simpl.
    rewrite ostream_labels_dist. simpl. repeat (rewrite <- List.app_assoc). simpl.
    unfold backend_labels in H9. simpl in H9. apply distinct_rotate_rev in H9.
    apply distinct_rotate. crush.
  (* S_Add *)
  - crush. apply distinct_rotate_rev in H7. crush.
  - crush. unfold backend_labels in *. simpl in *.
    rewrite List.app_assoc.
    apply distinct_rotate.
    apply distinct_rotate_rev in H8.
    crush.
  - crush.
  - crush.
  (* S_PFold *)
  - crush.
  - crush.
  (* S_Last *)
  - crush.
  - crush.
    rewrite List.app_assoc.
    rewrite List.app_assoc.
    apply distinct_rotate.
    apply distinct_rotate_rev in H10.
    unfold backend_labels at 2.
    crush.
  (* S_FusePMap *)
  - crush.
  - crush.
    unfold backend_labels at 2; simpl.
    rewrite ostream_labels_dist; simpl.
    repeat (rewrite <- List.app_assoc); simpl.
    unfold backend_labels at 2 in H7; simpl in H7.
    rewrite ostream_labels_dist in H7; simpl in H7.
    repeat (rewrite <- List.app_assoc in H7); simpl in H7.
    replace (backend_labels b1 ++ ostream_labels os1 ++ l' :: ostream_labels os2 ++ List.concat (map (fun s : station => ostream_labels (get_ostream s)) b2) ++ ostream_labels os ++ l :: rstream_labels rs)
            with ((backend_labels b1 ++ ostream_labels os1 ++ l' :: ostream_labels os2 ++ List.concat (map (fun s : station => ostream_labels (get_ostream s)) b2) ++ ostream_labels os) ++ l :: rstream_labels rs) by crush.
    apply distinct_rotate.
    replace (l :: (backend_labels b1 ++ ostream_labels os1 ++ l' :: ostream_labels os2 ++ List.concat (map (fun s : station => ostream_labels (get_ostream s)) b2) ++ ostream_labels os) ++ rstream_labels rs)
            with ((l :: (backend_labels b1 ++ ostream_labels os1)) ++ l' :: ostream_labels os2 ++ List.concat (map (fun s : station => ostream_labels (get_ostream s)) b2) ++ ostream_labels os ++ rstream_labels rs) by crush.
    apply distinct_rotate.
    replace (backend_labels b1 ++ ostream_labels os1 ++ l :: l' :: ostream_labels os2 ++ List.concat (map (fun s : station => ostream_labels (get_ostream s)) b2) ++ ostream_labels os ++ rstream_labels rs)
            with ((backend_labels b1 ++ ostream_labels os1 ++ [l]) ++ l' :: ostream_labels os2 ++ List.concat (map (fun s : station => ostream_labels (get_ostream s)) b2) ++ ostream_labels os ++ rstream_labels rs) in H7 by crush.
    apply distinct_rotate_rev in H7.
    replace (l' :: (backend_labels b1 ++ ostream_labels os1 ++ [l]) ++ ostream_labels os2 ++ List.concat (map (fun s : station => ostream_labels (get_ostream s)) b2) ++ ostream_labels os ++ rstream_labels rs)
            with((l' :: (backend_labels b1 ++ ostream_labels os1)) ++ l :: ostream_labels os2 ++ List.concat (map (fun s : station => ostream_labels (get_ostream s)) b2) ++ ostream_labels os ++ rstream_labels rs) in H7 by crush.
    apply distinct_rotate_rev in H7.
    apply distinct_rotate_front.
    crush.
  (* S_Prop *)
  - crush.
  - crush.
    rewrite cons_app.
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
  - crush.
  - crush.
  (* S_LoadPFold *)
  - crush.
  - crush. unfold backend_labels at 2 in H8; simpl in H8.
    rewrite ostream_labels_dist in H8.
    unfold backend_labels at 2; simpl.
    rewrite ostream_labels_dist.
    assumption.
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

Theorem unique_types : forall t Gamma ll T T' E E',
  has_type Gamma ll t T E ->
  has_type Gamma ll t T' E' ->
  T = T' /\ E = E'.
Proof using.
  induction t; intros Gamma ll T T' E E' HT HT'.
  - inv HT; inv HT'; crush.
  - inv HT; inv HT'.
    eapply IHt1 in H3; eauto.
    eapply IHt2 in H6; eauto.
    crush.
  - inv HT; inv HT'.
    eapply IHt in H6; eauto.
    crush.
  - inv HT; inv HT'; eauto. crush.
  - inv HT; inv HT'; eauto.
  - inv HT; inv HT'; eauto.
  - inv HT; inv HT'.
    eapply IHt1 with (T':=Result) (E':=E0) in H3; eauto.
    eapply IHt2 with (T':=Keyset) (E':= E3) in H6; eauto.
    crush.
  - inv HT; inv HT'.
    eapply IHt in H2; eauto.
    crush.
  - inv HT; inv HT'; eauto.
  - inv HT; inv HT'; eauto.
  - inv HT; inv HT'; eauto.
  - inv HT; inv HT'.
    eapply IHt1 with (T':=Result) (E':=E0) in H4; eauto.
    eapply IHt2 with (T':=Result) (E':= E4) in H7; eauto.
    eapply IHt3 with (T':=Keyset) (E':= E5) in H8; eauto.
    crush.
  - inv HT; inv HT'.
    eapply IHt with (T:=Node) (E:=E') in H2; dtr; auto.
  - inv HT; inv HT'.
    eapply IHt with (T:=Node) (E:=E') in H2; dtr; auto.
  - inv HT; inv HT'.
    eapply IHt with (T:=Node) (E:=E') in H2; dtr; auto.
  - inv HT; inv HT'.
    eapply IHt with (T':=Arrow (Arrow t t (E0 || E1)) (Arrow t t E0) E1) (E':=E') in H5; crush.
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

Ltac dconcat := match goal with | [H : distinct (_ ++ _) |- _] => apply distinct_concat in H; dtr end.

Lemma distinct_nodes :
  forall b os0 rs0 term0,
  distinct (config_keys (C b os0 rs0 term0)) ->
  distinct b.
Proof using.
  induction b; intros; auto.
  destruct a. destruct n. simpl in *.
  econstructor; [eauto| |].
  - intro.
    apply List.in_split in H0; dtr; subst.
    apply distinct_remove in H; dtr.
    crush.
  - apply distinct_remove in H; dtr.
    eauto.
Qed.

Lemma distinct_ops :
  forall b1 b2 n os os0 rs0 term0,
  distinct (config_labels (C (b1 ++ <<n; os>> :: b2) os0 rs0 term0)) ->
  distinct os.
Proof using.
  induction os; intros; auto.
  destruct a; simpl in *.
  econstructor; [eauto| |].
  - intro.
    apply List.in_split in H0; dtr; subst.
    rewrite backend_labels_dist in H. apply distinct_concat in H; dtr. apply distinct_concat in H; dtr.
    unfold backend_labels in H1; simpl in *. rewrite ostream_labels_dist in H1; simpl in *.
    apply distinct_remove in H1. crush.
  - eapply IHos with (os0:=os0) (rs0:=rs0); auto.
    rewrite backend_labels_dist in *. unfold backend_labels in H at 2. simpl in *.
    repeat (rewrite <- List.app_assoc in H).
    apply distinct_rotate_rev in H. apply distinct_remove in H; dtr. unfold backend_labels at 2. crush.
Qed.

Lemma target_unique :
  forall b b' b1 b2 b3 b4 k v es os os0 rs0 t0,
  well_typed (C b os0 rs0 t0) ->
  b = b' ->
  b = b1 ++ [<<N k v es; os>>] ++ b2 ->
  b' = b3 ++ [<<N k v es; os>>] ++ b4 ->
  (b1 = b3 /\ b2 = b4).
Proof using.
  intros.
  eapply distinct_center with (l:=b).
  eapply distinct_nodes with (os0:=os0) (rs0:=rs0) (term0:=t0); eauto. { inv H; eauto. }
  instantiate (1:=b').
  assumption.
  instantiate (1:=<<N k v es; os>>).
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
  inv H; crush.
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
  forall k v es es' os v' os' b os0 rs0 term0,
  well_typed (C b os0 rs0 term0) ->
  In <<N k v es; os>> b ->
  In <<N k v' es'; os'>> b ->
  v = v' /\ os = os' /\ es = es'.
Proof using.
  intros k v es es' os v' os' b os0 rs0 term0 WT Inb Inb'.
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
  forall b b' b1 b2 b3 b4 k v es es' v' os' os os0 rs0 t0,
  well_typed (C b os0 rs0 t0) ->
  b = b' ->
  b = b1 ++ [<<N k v es; os>>] ++ b2 ->
  b' = b3 ++ [<<N k v' es'; os'>>] ++ b4 ->
  (b1 = b3 /\ b2 = b4 /\ v = v' /\ os = os' /\ es = es').
Proof using.
  intros.
  assert (v = v') by (eapply unique_key with (es:=es) (es':=es') (k:=k) (v:=v) (v':=v') (os:=os) (os':=os'); eauto; subst; crush).
  assert (os = os') by (eapply unique_key with (es:=es) (es':=es') (k:=k) (v:=v) (v':=v') (os:=os) (os':=os'); eauto; subst; crush).
  assert (es = es') by (eapply unique_key with (es:=es) (es':=es') (k:=k) (v:=v) (v':=v') (os:=os) (os':=os'); eauto; subst; crush).
  subst.
  split; try split; try split; try split; try assumption; try reflexivity.
  eapply target_unique with (b1:=b1) (b2:=b2) (b3:=b3) (b4:=b4); eauto.
  eapply target_unique with (b1:=b1) (b2:=b2) (b3:=b3) (b4:=b4); eauto.
Qed.
Hint Resolve target_unique.

Lemma target_same_or_different :
  forall b b1 b2 b3 b4 k v es es' k' v' os os' os0 rs0 term0,
  well_typed (C b os0 rs0 term0) ->
  b = b1 ++ <<N k v es; os>> :: b2 ->
  b = b3 ++ <<N k' v' es'; os'>> :: b4 ->
  (b1 = b3 /\ b2 = b4 /\ k = k' /\ v = v' /\ os = os') \/
  (exists (b' : backend) b'' b''', b = b' ++ <<N k v es; os>> :: b'' ++ <<N k' v' es'; os'>> :: b''') \/
  (exists (b' : backend) b'' b''', b = b' ++ <<N k' v' es'; os'>> :: b'' ++ <<N k v es; os>> :: b''').
Proof using.
  intros.
  destruct (Nat.eq_dec k k') as [keq|kneq].
  - rewrite keq in *. clear keq.
    assert (v = v') by (eapply target_unique' with (es:=es) (es':=es'); eauto; crush).
    assert (os = os') by (eapply target_unique'; eauto; crush).
    assert (es = es') by (eapply target_unique'; eauto; crush).
    assert (b1 = b3 /\ b2 = b4) by (eapply target_unique with (b:=b) (b1:=b1) (b2:=b2) (b3:=b3) (b4:=b4); eauto; crush).
    left.
    crush.
  - subst.
    assert (In << N k' v' es'; os' >> (b1 ++ << N k v es; os >> :: b2)) by crush.
    apply List.in_app_or in H0.
    destruct H0.
    * right.
      right.
      apply List.in_split in H0.
      destruct H0.
      destruct H0.
      subst.
      assert ((x ++ << N k' v' es'; os' >> :: x0) ++ << N k v es; os >> :: b2 = x ++ << N k' v' es'; os' >> :: x0 ++ << N k v es; os >> :: b2) by crush.
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
  forall t rs t' os lr,
  FRf t rs ==> FRt t' os ->
  FRf t (lr :: rs) ==> FRt t' os.
Proof using.
  induction t; intros; rename H into Hstep; try solve [inv Hstep; eauto].
  - inv Hstep.
    + eapply F_Claim. crush.
    + eauto.
Unshelve.
auto.
auto.
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
                     end); try solve [split; crush]; try solve [exfalso; eapply frontend_no_value; eauto]].

Ltac fnv :=
      match goal with
      | [H : FRf ?t _ ==> FRt _ _, H' : value ?t |- _] => exfalso; eapply frontend_no_value in H; eauto
      end.

Lemma frontend_deterministic' :
  forall t b0 os0 rs os t',
  well_typed (C b0 os0 rs t) ->
  FRf t rs ==> FRt t' os ->
  forall t'' os',
  FRf t rs ==> FRt t'' os' ->
  t' = t'' /\ os = os'.
Proof using.
  induction t; intros; rename H0 into Hstep; rename H1 into Hstep'; try solve [inv Hstep].
  - inv Hstep; inv Hstep'; try solve [fnv].
    + split; eauto.
    + inv H2.
    + inv H1.
    + eapply IHt1 with (t':= t1'0) (os:=os') in H1; dtr; subst; eauto.
      inv H; dtr; split; try split; eauto.
    + eapply IHt2 with (t':= t2'0) (os:=os') in H6; dtr; subst; eauto.
      inv H; dtr; split; try split; eauto.
  - inv Hstep; inv Hstep'; try solve [fnv].
    + eapply IHt1 with (t':=k'0) (os:=os') in H1; dtr; subst; eauto.
      inv H; dtr; split; try split; eauto.
    + eapply IHt2 with (t':=ks'0) (os:=os') in H6; dtr; subst; eauto.
      inv H; dtr; split; try split; eauto.
  - inv Hstep; inv Hstep'; try solve [fnv].
    + eapply unique_result with (r':=v0) in H1; eauto.
    + inv H2.
    + inv H1.
    + eapply IHt with (t':=t') (os:=os') in H1; dtr; subst; eauto.
      inv H; dtr; split; try split; eauto.
  - inv Hstep; inv Hstep'; try solve [fnv].
    + eauto.
    + eapply IHt1 with (t':=t1'0) (os:=os') in H1; dtr; subst; eauto.
      inv H; dtr; split; try split; eauto.
    + eapply IHt2 with (t':=t2'0) (os:=os') in H8; dtr; subst; eauto.
      inv H; dtr; split; try split; eauto.
    + eapply IHt3 with (t':=t3'0) (os:=os') in H9; dtr; subst; eauto.
      inv H; dtr; split; try split; eauto.
  - inv Hstep; inv Hstep'; try solve [fnv].
    + eauto.
    + eapply IHt1 with (t':=t1'0) (os:=os') in H1; dtr; subst; eauto.
      inv H; dtr; split; try split; eauto.
    + eapply IHt2 with (t':=t2'0) (os:=os') in H7; dtr; subst; eauto.
      inv H; dtr; split; try split; eauto.
  - inv Hstep; inv Hstep'; try solve [fnv].
    + eauto.
    + inv H1.
    + inv H7.
    + inv H1.
    + eapply IHt1 with (t':=t1'0) (os:=os') in H1; dtr; subst; eauto.
      inv H; dtr; split; try split; eauto.
    + inv H7.
    + eapply IHt2 with (t':=t2'0) (os:=os') in H7; dtr; subst; eauto.
      inv H; dtr; split; try split; eauto.
  - inv Hstep; inv Hstep'; try solve [fnv].
    + eapply IHt1 with (t':=k'0) (os:=os') in H1; dtr; subst; eauto.
      inv H; dtr; split; try split; eauto.
      inv H; dtr. inv H12. exi; eauto.
    + eapply IHt2 with (t':=p'0) (os:=os') in H7; dtr; subst; eauto.
      inv H; dtr; split; try split; eauto.
      inv H; dtr. inv H14. exi; eauto.
    + eapply IHt3 with (t':=es'0) (os:=os') in H8; dtr; subst; eauto.
      inv H; dtr; split; try split; eauto.
      inv H; dtr. inv H16. exi; eauto.
  - inv Hstep; inv Hstep'; try solve [fnv]; try solve [exfalso; eapply frontend_no_value; eauto]; try solve [eauto].
    + eapply IHt with (t':=t') (os:=os') in H1; dtr; subst; eauto.
      inv H; dtr; split; try split; eauto.
      inv H; dtr. inv H12. exi; eauto.
  - inv Hstep; inv Hstep'; try solve [fnv]; try solve [exfalso; eapply frontend_no_value; eauto]; try solve [eauto].
    + eapply IHt with (t':=t') (os:=os') in H1; dtr; subst; eauto.
      inv H; dtr; split; try split; eauto.
      inv H; dtr. inv H12. exi; eauto.
  - inv Hstep; inv Hstep'; try solve [fnv]; try solve [exfalso; eapply frontend_no_value; eauto]; try solve [eauto].
    + eapply IHt with (t':=t') (os:=os') in H1; dtr; subst; eauto.
      inv H; dtr; split; try split; eauto.
      inv H; dtr. inv H12. exi; eauto.
  - inv Hstep; inv Hstep'; try solve [fnv].
    + eauto.
    + eapply IHt with (t':=t') (os:=os') in H1; dtr; subst; eauto.
      inv H; dtr; split; try split; eauto.
      inv H; dtr. inv H12. exi; eauto.
Qed.

Lemma list_app_cons_empty : forall {A : Type} (x : A) xs ys,
  xs ++ x :: ys = [] -> False.
Proof using.
  induction xs; crush.
Qed.
Hint Resolve list_app_cons_empty.

Ltac trouble_makers := try solve [eapply S_Add; eauto]; try solve [eapply S_FusePMap; eauto].

Ltac match_frontend :=
  match goal with
  | [H : C ?b ?os ?rs ?t --> C ?b' ?os' ?rs' ?t, H' : FRf ?t ?rs ==> FRt ?t' ?os'' |- _] =>
    gotw (C b' (os' ++ os'') rs' t'); simpl; eauto; trouble_makers
  end.

Lemma lc_frontend :
  forall cx cy cz b os os' rs t t',
  well_typed cx ->
  cx = C b os rs t ->
  cy = C b (os ++ os') rs t' ->
  FRf t rs ==> FRt t' os' ->
  cx --> cy ->
  cx --> cz ->
  cy -v cz.
Proof using.
  intros cx cy cz b os os' rs t t'.
  intros WT Heqcx Heqcy.
  intros Hstep.
  intros cxcy cxcz.
  inversion cxcz; ssame; try solve match_frontend; ssame'.
  (* S_Frontend *)
  - eapply frontend_deterministic' with (t':=t'0) (os:=os'0) in Hstep; dtr; subst; auto.
    + inv WT; dtr. split; try split; eauto.
Unshelve.
auto.
auto.
Qed.
Hint Resolve lc_frontend.

Ltac tsod := match goal with
             | [H : ?b1 ++ <<N ?k ?t ?es; ?os>> :: ?b2 = ?b3 ++ <<N ?k' ?t' ?es'; ?os'>> :: ?b4 |- _] =>
                 eapply (@target_same_or_different _ b1 b2 b3 b4 k t es es' k' t') in H; eauto; destruct H as [Hsame|Hwhich]; try destruct Hwhich as [Hfirst|Hsecond];
                 try (destruct Hsame as [Hsame1 Hsame2]; destruct Hsame2 as [Hsame2 Hsame3]; destruct Hsame3 as [Hsame3 Hsame4]; destruct Hsame4 as [Hsame4 Hsame5]; subst)
             end.

Ltac tsod' := match goal with
              | [H : ?b1 ++ <<N ?k ?t ?es; ?os>> :: ?b2 = ?b3 ++ <<N ?k' ?t' ?es'; ?os' ++ ?os''>> :: ?b4 |- _] =>
                  eapply (@target_same_or_different _ b1 b2 b3 b4 k t es es' k' t' os (os' ++ os'')) in H; eauto; destruct H as [Hsame|Hwhich]; try destruct Hwhich as [Hfirst|Hsecond];
                  try (destruct Hsame as [Hsame1 Hsame2]; destruct Hsame2 as [Hsame2 Hsame3]; destruct Hsame3 as [Hsame3 Hsame4]; destruct Hsame4 as [Hsame4 Hsame5]; subst)
              end.

Ltac tsod'' := match goal with
              | [H : ?b1 ++ <<N ?k ?t ?es; ?os ++ ?os'''>> :: ?b2 = ?b3 ++ <<N ?k' ?t' ?es'; ?os' ++ ?os''>> :: ?b4 |- _] =>
                  eapply (@target_same_or_different _ b1 b2 b3 b4 k t es es' k' t' (os ++ os''') (os' ++ os'')) in H; eauto; destruct H as [Hsame|Hwhich]; try destruct Hwhich as [Hfirst|Hsecond];
                  try (destruct Hsame as [Hsame1 Hsame2]; destruct Hsame2 as [Hsame2 Hsame3]; destruct Hsame3 as [Hsame3 Hsame4]; destruct Hsame4 as [Hsame4 Hsame5]; subst)
              end.

Ltac tu1 := match goal with
            | [H : ?b1 ++ <<N ?k ?t ?es; ?os>> :: ?b2 = ?b3 ++ <<N ?k ?t ?es; ?os>> :: ?b' ++ <<N ?k' ?t' ?es'; ?os'>> :: ?b4 |- _] =>
            eapply (@target_unique _ _ b1 b2 b3 _) in H; crush
            end;
            match goal with
            | [H : C _ _ _ _ = C _ _ _ _ |- _] => inv H
            end;
            match goal with
            | [H : ?b1 ++ <<N ?k' ?t' ?es'; ?os'>> :: ?b' ++ <<N ?k ?t ?es; ?os>> :: ?b2 = ?b3 ++ <<N ?k ?t ?es; ?os>> :: ?b4 |- _] =>
              eapply (@target_unique _ _ (b1 ++ <<N k' t' es'; os'>> :: b') b2 b3 b4) in H; eauto; crush
            end.

Ltac tu2 := match goal with
            | [H : ?b1 ++ <<N ?k ?t ?es; ?os>> :: ?b2 = ?b3 ++ <<N ?k' ?t' ?es'; ?os'>> :: ?b' ++ <<N ?k ?t ?es; ?os>> :: ?b4 |- _] =>
              eapply (@target_unique _ _ b1 b2 (b3 ++ <<N k' t' es'; os'>> :: b') b4) in H; eauto; crush
            end;
            match goal with
            | [H : C _ _ _ _ = C _ _ _ _ |- _] => inv H
            end;
            match goal with
            | [H : ?b1 ++ <<N ?k ?t ?es; ?os>> :: ?b' ++ <<N ?k' ?t' ?es'; ?os'>> :: ?b2 = ?b3 ++ <<N ?k ?t ?es; ?os>> :: ?b4 |- _] =>
              eapply (@target_unique _ _ b1 (b' ++ <<N k' t' es'; os'>> :: b2) b3 b4) in H; eauto; crush
            end.

Lemma pmap_value : forall b1 b2 n l os0 rs0 t0 f ks os os',
  well_typed (C (b1 ++ <<n; os ++ l ->> pmap f ks :: os'>> :: b2) os0 rs0 t0) ->
  value f.
Proof using.
  intros.
  inv H.
  destruct H2 as [T[E]].
  inv H.
  wtbdist.
  inv H2.
  wtosdist.
  inv H3.
  inv H15.
  auto.
Qed.

Lemma pfold_value : forall b1 b2 n l os0 rs0 t0 f t ks os os',
  well_typed (C (b1 ++ <<n; os ++ l ->> pfold f t ks :: os'>> :: b2) os0 rs0 t0) ->
  value f.
Proof using.
  intros.
  inv H.
  destruct H2 as [T[E]].
  inv H.
  wtbdist.
  inv H2.
  wtosdist.
  inv H3.
  inv H15.
  auto.
Qed.

Lemma lc_load :
  forall cx cy cz b1 b2 k os t es t' term0 os0 rs0,
  well_typed cx ->
  cx = C (b1 ++ <<N k t es; os>> :: b2) os0 rs0 term0 ->
  cy = C (b1 ++ <<N k t' es; os>> :: b2) os0 rs0 term0 ->
  cx --> cy ->
  cx --> cz ->
  FRf t rs0 ==> FRt t' [] ->
  cy -v cz.
Proof using.
  intros cx cy cz b1 b2 k os t es t' term0 os0 rs0.
  intros WT Heqcx Heqcy cxcy cxcz.
  intros tt'.
  inversion cxcz; ssame; try solve [subst; eauto].
  (* S_Empty *)
  - exfalso; eauto.
  (* S_First *)
  - destruct b1; simpl in *.
    + inv H1.
      gotw (C (<< N k t' es; os2 ++ [l ->> op] >> :: b') os' rs term1); eauto.
      eapply S_Load with (b1:=[]); eauto; crush.
    + inv H1.
      gotw (C (<< n1; os2 ++ [l ->> op] >> :: b1 ++ << N k t' es; os >> :: b2) os' rs term1); eauto.
      eapply S_Load with (b1:=<< n1; os2 ++ [l ->> op] >> :: b1); eauto; crush.
  (* S_Add *)
  - gotw (C (<< N k0 v t_ks_nil; [] >> :: b1 ++ << N k t' es; os >> :: b2) os' (l ->>> final H :: rs) term1); eauto.
    eapply S_Load with (b1:=<< N k0 v t_ks_nil; [] >> :: b1); eauto; crush.
  (* S_PMap *)
  - tsod.
    + inv H. apply List.app_inv_head in H1. inv H1.
      got.
      * one_step. instantiate (1:=C (b0 ++ << N k0 (t_app f t') es0; l ->> pmap f (remove Nat.eq_dec k0 ks) :: os1'' >> :: b3) os1 rs term1).
        eapply S_PMap; eauto.
      * one_step. instantiate (1:=C (b0 ++ << N k0 (t_app f t') es0; l ->> pmap f (remove Nat.eq_dec k0 ks) :: os1'' >> :: b3) os1 rs term1).
        eapply S_Load; eauto.
        eapply F_App2 with (os:=[]); eauto.
        remember (pmap f ks) as op; subst op; eapply pmap_value with (os:=[]); eauto.
      * crush.
    + destruct Hfirst as [b' [b'' [b''']]].
      tu1.
      got.
      * one_step. instantiate (1:=C ((b' ++ << N k t' es; os >> :: b'') ++ << N k0 (t_app f v) es0; l ->> pmap f (remove Nat.eq_dec k0 ks) :: os1'' >> :: b3) os1 rs term1).
        eapply S_PMap; eauto; crush.
      * one_step. instantiate (1:=C (b' ++ << N k t' es; os >> :: b'' ++ << N k0 (t_app f v) es0; l ->> pmap f (remove Nat.eq_dec k0 ks) :: os1'' >> :: b3) os1 rs term1).
        eapply S_Load; eauto; crush.
      * crush.
    + destruct Hsecond as [b' [b'' [b''']]].
      tu2.
      got.
      * instantiate (1:=C (b0 ++ << N k0 (t_app f v) es0; l ->> pmap f (remove Nat.eq_dec k0 ks) :: os1'' >> :: b'' ++ << N k t' es; os >> :: b''') os1 rs term1).
        one_step; eapply S_PMap; eauto.
      * instantiate (1:=C ((b0 ++ << N k0 (t_app f v) es0; l ->> pmap f (remove Nat.eq_dec k0 ks) :: os1'' >> :: b'') ++ << N k t' es; os >> :: b''') os1 rs term1).
        one_step; eapply S_Load; eauto; crush.
      * crush.
  (* S_PFold *)
  - tsod.
    + got. inv H. apply List.app_inv_head in H1. inv H1.
      * instantiate (1:=C (b0 ++ << N k0 t' es0; l ->> pfold f (t_app (t_app f t') t'0) (remove Nat.eq_dec k0 ks) :: os1'' >> :: b3) os1 rs term1).
        one_step. eapply S_PFold; eauto.
      * instantiate (1:=C (b0 ++ << N k0 t' es0; l ->> pfold f (t_app (t_app f t') t'0) (remove Nat.eq_dec k0 ks) :: os1'' >> :: b3) os1 rs term1).
        exists 2.
        eapply Step.
        instantiate (1:=C (b0 ++ << N k0 t' es0; l ->> pfold f (t_app (t_app f t0) t'0) (remove Nat.eq_dec k0 ks) :: os1'' >> :: b3) os1 rs term1).
        eapply S_Load; eauto.
        apply one_star.
        {
        eapply S_LoadPFold with (os:=[]).
        - instantiate (1:=(b0 ++ << N k0 t' es0; l ->> pfold f (t_app (t_app f t0) t'0) (remove Nat.eq_dec k0 ks) :: os1'' >> :: b3)).
          reflexivity.
        - simpl. eauto.
        - instantiate (1:=(t_app (t_app f t') t'0)).
          eapply F_App1 with (os:=[]).
          eapply F_App2 with (os:=[]).
          eapply pfold_value with (os:=[]); eauto.
          assumption.
        - crush.
        }
      * crush.
    + destruct Hfirst as [b' [b'' [b''']]].
      tu1.
      got.
      * instantiate (1:=C ((b' ++ << N k t' es; os >> :: b'') ++ << N k0 t0 es0; l ->> pfold f (t_app (t_app f t0) t'0) (remove Nat.eq_dec k0 ks) :: os1'' >> :: b3) os1 rs term1).
        one_step; eapply S_PFold; eauto; crush.
      * instantiate (1:=C (b' ++ << N k t' es; os >> :: b'' ++ << N k0 t0 es0; l ->> pfold f (t_app (t_app f t0) t'0) (remove Nat.eq_dec k0 ks) :: os1'' >> :: b3) os1 rs term1).
        one_step; eapply S_Load; eauto.
      * crush.
    + destruct Hsecond as [b' [b'' [b''']]].
      tu2.
      got.
      * instantiate (1:=C (b0 ++ << N k0 t0 es0; l ->> pfold f (t_app (t_app f t0) t'0) (remove Nat.eq_dec k0 ks) :: os1'' >> :: b'' ++ << N k t' es; os >> :: b''') os1 rs term1).
        one_step; eapply S_PFold; eauto; crush.
      * instantiate (1:=C ((b0 ++ << N k0 t0 es0; l ->> pfold f (t_app (t_app f t0) t'0) (remove Nat.eq_dec k0 ks) :: os1'' >> :: b'') ++ << N k t' es; os >> :: b''') os1 rs term1).
        one_step; eapply S_Load; eauto; crush.
      * crush.
  (* S_Last *)
  - destruct b2.
    + apply List.app_inj_tail in H2. destruct H2. inv H2.
      gotw (C (b0 ++ [<< N k t' es; os1' >>]) os1 (l ->>> final H :: rs) term1); eauto.
    + remember (s :: b2) as bend.
      assert (exists y ys, bend = ys ++ [y]) by (apply list_snoc with (xs:=bend) (x:=s) (xs':=b2); crush).
      destruct H1; destruct H1.
      inv H1.
      rewrite H3 in *. clear H3.
      assert (b1 ++ << N k t es; os >> :: x0 ++ [x] = (b1 ++ << N k t es; os >> :: x0) ++ [x]) by crush.
      rewrite H1 in H2; clear H1.
      apply List.app_inj_tail in H2.
      destruct H2.
      subst.
      got.
      * instantiate (1:=C ((b1 ++ << N k t' es; os >> :: x0) ++ [<< n1; os1' >>]) os1 (l ->>> final H :: rs) term1).
        one_step; eapply S_Last; eauto; crush.
      * instantiate (1:=C (b1 ++ << N k t' es; os >> :: x0 ++ [<< n1; os1' >>]) os1 (l ->>> final H :: rs) term1).
        one_step; eapply S_Load; eauto; crush.
      * crush.
  (* S_FusePMap *)
  - destruct n. tsod'. inv H0. apply List.app_inv_head in H2. inv H2.
    + gotw (C (b0 ++ << N n t' e; os2 ++ l' ->> pmap (pmap_compose f' f) ks :: os3 >> :: b3) os1 (l ->>> final H :: rs) term1); eauto.
    + destruct Hfirst as [b' [b'' [b''']]].
      tu1.
      got.
      * instantiate (1:=C ((b' ++ << N k t' es; os >> :: b'') ++ << N n t0 e; os2 ++ l' ->> pmap (pmap_compose f' f) ks :: os3 >> :: b3) os1 (l ->>> 0 :: rs) term1).
        one_step; eapply S_FusePMap; eauto; crush.
      * instantiate (1:=C (b' ++ << N k t' es; os >> :: b'' ++ << N n t0 e; os2 ++ l' ->> pmap (pmap_compose f' f) ks :: os3 >> :: b3) os1 (l ->>> 0 :: rs) term1).
        one_step; eapply S_Load; eauto; crush.
      * crush.
    + destruct Hsecond as [b' [b'' [b''']]].
      tu2.
      got.
      * instantiate (1:=C (b0 ++ << N n t0 e; os2 ++ l' ->> pmap (pmap_compose f' f) ks :: os3 >> :: b'' ++ << N k t' es; os >> :: b''') os1 (l ->>> 0 :: rs) term1).
        one_step; eapply S_FusePMap; eauto; crush.
      * instantiate (1:=C ((b0 ++ << N n t0 e; os2 ++ l' ->> pmap (pmap_compose f' f) ks :: os3 >> :: b'') ++ << N k t' es; os >> :: b''') os1 (l ->>> 0 :: rs) term1).
        one_step; eapply S_Load; eauto; crush.
      * crush.
  (* S_Prop *)
  - destruct n1. tsod.
    + inv H. apply List.app_inv_head in H2; inv H2.
      gotw (C (b0 ++ << N n t' e; os2 >> :: << n2; os3 ++ [l ->> op] >> :: b3) os1 rs term1); eauto.
    + destruct Hfirst as [b' [b'' [b''']]].
      tu1.
      got.
      * instantiate (1:=C ((b' ++ << N k t' es; os >> :: b'') ++ << N n t0 e; os2 >> :: << n2; os3 ++ [l ->> op] >> :: b3) os1 rs term1); eauto.
        one_step; eapply S_Prop; eauto; crush.
      * instantiate (1:=C (b' ++ << N k t' es; os >> :: b'' ++ << N n t0 e; os2 >> :: << n2; os3 ++ [l ->> op] >> :: b3) os1 rs term1); eauto.
      * crush.
    + destruct Hsecond as [b' [b'' [b''']]].
      tu2.
      {
      destruct b''; simpl in *.
      - inv H1.
        got.
        + instantiate (1:=C (b0 ++ << N n t0 e; os2 >> :: << N k t' es; os3 ++ [l ->> op] >> :: b3) os1 rs term1); eauto.
          one_step; eapply S_Prop; eauto; crush.
        + instantiate (1:=C ((b0 ++ [<< N n t0 e; os2 >>]) ++ << N k t' es; os3 ++ [l ->> op] >> :: b3) os1 rs term1); eauto.
          one_step; eapply S_Load; eauto; crush.
        + crush.
      - inv H1.
        got.
        + instantiate (1:=C (b0 ++ << N n t0 e; os2 >> :: << n2; os3 ++ [l ->> op] >> :: b'' ++ << N k t' es; os >> :: b''') os1 rs term1); eauto.
          one_step; eapply S_Prop; eauto; crush.
        + instantiate (1:=C ((b0 ++ << N n t0 e; os2 >> :: << n2; os3 ++ [l ->> op] >> :: b'') ++ << N k t' es; os >> :: b''') os1 rs term1); eauto.
          one_step; eapply S_Load; eauto; crush.
        + crush.
      }
  (* S_Load *)
  - tsod.
    + inv H. apply List.app_inv_head in H2; inv H2.
      eapply frontend_deterministic' with (b0:=b0 ++ <<N k0 t0 es0; os2>> :: b3) (os0:=os1) (os:=[]) (t':=t'0) in tt'; eauto. destruct tt'.
      crush.
      split.
      * crush. inv WT. crush.
      * crush. inv WT. crush.
      * exists Result, false.
        {
        inv WT; dtr. inv H2.
        econstructor.
        - eapply wt_backend_build; eauto.
        - wtbt. eauto.
        - wtbdist. inv H3. wtbt. wtost. wtbt. wttost.
          eauto.
        }
    + destruct Hfirst as [b' [b'' [b''']]].
      tu1.
      got.
      * instantiate (1:=C ((b' ++ << N k t' es; os >> :: b'') ++ << N k0 t'0 es0; os2 >> :: b3) os1 rs1 term1); eauto.
        one_step; eapply S_Load; eauto; crush.
      * instantiate (1:=C (b' ++ << N k t' es; os >> :: b'' ++ << N k0 t'0 es0; os2 >> :: b3) os1 rs1 term1); eauto.
      * crush.
    + destruct Hsecond as [b' [b'' [b''']]].
      tu2.
      got.
      * instantiate (1:=C (b0 ++ << N k0 t'0 es0; os2 >> :: b'' ++ << N k t' es; os >> :: b''') os1 rs1 term1); eauto.
      * instantiate (1:=C ((b0 ++ << N k0 t'0 es0; os2 >> :: b'') ++ << N k t' es; os >> :: b''') os1 rs1 term1); eauto.
        one_step; eapply S_Load; eauto; crush.
      * crush.
  (* S_LoadPFold *)
  - tsod. inv H. apply List.app_inv_head in H2; inv H2.
    + gotw (C (b0 ++ << N k0 t' es0; os2 ++ l ->> pfold f t1' ks :: os' >> :: b3) os1 rs1 term1); eauto.
    + destruct Hfirst as [b' [b'' [b''']]].
      tu1.
      got.
      * instantiate (1:=C ((b' ++ << N k t' es; os >> :: b'') ++ << N k0 t0 es0; os2 ++ l ->> pfold f t1' ks :: os' >> :: b3) os1 rs1 term1); eauto.
        one_step; eapply S_LoadPFold; eauto; crush.
      * instantiate (1:=C (b' ++ << N k t' es; os >> :: b'' ++ << N k0 t0 es0; os2 ++ l ->> pfold f t1' ks :: os' >> :: b3) os1 rs1 term1); eauto.
      * crush.
    + destruct Hsecond as [b' [b'' [b''']]].
      tu2.
      got.
      * instantiate (1:=C (b0 ++ << N k0 t0 es0; os2 ++ l ->> pfold f t1' ks :: os' >> :: b'' ++ << N k t' es; os >> :: b''') os1 rs1 term1); eauto.
      * instantiate (1:=C ((b0 ++ << N k0 t0 es0; os2 ++ l ->> pfold f t1' ks :: os' >> :: b'') ++ << N k t' es; os >> :: b''') os1 rs1 term1); eauto.
        one_step; eapply S_Load; eauto; crush.
      * crush.
Unshelve.
auto.
auto.
Qed.
Hint Resolve lc_load.

Inductive fstar : nat -> term -> rstream -> term -> Prop :=
| FZero : forall t rs, fstar 0 t rs t
| FStep : forall t rs t', FRf t rs ==> FRt t' [] -> forall n t'', fstar n t' rs t'' -> fstar (S n) t rs t''.
Hint Constructors fstar.

Lemma fstar_zero :
  forall t t' rs,
  fstar 0 t rs t' ->
  t = t'.
Proof using.
  intros.
  inversion H; subst; clear H; crush.
Qed.

Lemma fstar_trans :
  forall m n t t' t'' rs,
  fstar m t rs t' ->
  fstar n t' rs t'' ->
  fstar (m+n) t rs t''.
Proof using.
  induction m; induction n; intros.
  - crush.
    apply fstar_zero in H; subst; crush.
  - simpl.
    apply fstar_zero in H; subst; crush.
  - apply fstar_zero in H0; subst.
    assert (S m = S m + 0) by crush.
    rewrite H0 in H.
    crush.
  - simpl in *.
    inversion H; subst; clear H.
    inversion H0; subst; clear H0.
    eapply FStep.
    instantiate (1:=t'0).
    assumption.
    eapply IHm.
    instantiate (1:=t').
    assumption.
    eapply FStep.
    instantiate (1:=t'1).
    assumption.
    assumption.
Qed.

Definition non_emitting (t : term) := exists T ll, has_type empty ll t T false.
Hint Unfold non_emitting.

Lemma fstar_app1 : forall m t t' t'' rs,
  fstar m t rs t' ->
  fstar m (t_app t t'') rs (t_app t' t'').
Proof using.
  induction m; intros.
  - apply fstar_zero in H; subst; auto.
  - inv H. econstructor. instantiate (1:=t_app t'0 t''). auto. auto.
Qed.

Lemma pfold_get : forall rs t t' t'',
    non_emitting t ->
    non_emitting t' ->
    FRf t' rs ==> FRt t'' [] ->
    (exists n v, fstar n t rs v /\ value v) ->
    exists n m t''', fstar n (t_app t t') rs t''' /\ fstar m (t_app t t'') rs t'''.
Proof using.
  intros; dtr.
  exists (S x), x, (t_app x0 t'').
  split.
  - replace (S x) with (x + 1).
    eapply fstar_trans.
    instantiate (1:=t_app x0 t').
    apply fstar_app1; auto.
    econstructor. instantiate (1:=t_app x0 t''). auto. auto. crush.
  - apply fstar_app1. auto.
Qed.

Lemma fstar_into_star_load : forall n t t' rs b1 k es os b2 os0 t0,
    fstar n t rs t' ->
    C (b1 ++ <<N k t es; os>> :: b2) os0 rs t0 -->*[n] C (b1 ++ <<N k t' es; os>> :: b2) os0 rs t0.
Proof using.
  induction n; intros.
  - apply fstar_zero in H; subst. auto.
  - inv H. econstructor.
    + instantiate (1:=C (b1 ++ << N k t'0 es; os >> :: b2) os0 rs t0). eauto.
    + apply IHn; eauto.
Qed.

Lemma fstar_into_star_loadpfold : forall n t t' n' rs b1 os1 l t1 t3 os2 b2 os0 t0,
    fstar n t rs t' ->
    C (b1 ++ <<n'; os1 ++ l ->> pfold t1 t t3 :: os2>> :: b2) os0 rs t0 -->*[n] C (b1 ++ <<n'; os1 ++ l ->> pfold t1 t' t3 :: os2>> :: b2) os0 rs t0.
Proof using.
  induction n; intros.
  - apply fstar_zero in H; subst. auto.
  - inv H. econstructor.
    + instantiate (1:=C (b1 ++ << n'; os1 ++ l ->> pfold t1 t'0 t3 :: os2 >> :: b2) os0 rs t0). destruct n'. eauto.
    + apply IHn; eauto.
Qed.

(* we are only interested in reductions that terminate *)
Hypothesis to_value : forall t rs, exists n t', fstar n t rs t' /\ value t'.

Ltac fsame := ssame'; match goal with | [H : ?b ++ _ = ?b ++ _ |- _] => apply List.app_inv_head in H; inv H end.

Lemma lc_pfold :
  forall cx cy cz os rs term k t es t' f l ks os1 b1 b2,
  well_typed cx ->
  cx = C (b1 ++ <<N k t es; l ->> pfold f t' ks :: os1>> :: b2) os rs term ->
  cy = C (b1 ++ <<N k t es; l ->> pfold f (t_app (t_app f t) t') (remove Nat.eq_dec k ks) :: os1>> :: b2) os rs term ->
  cx --> cy ->
  cx --> cz ->
  In k ks ->
  cy -v cz.
Proof using.
  intros cx cy cz os rs term k t es t' f l ks os1 b1 b2.
  intros WT Heqcx Heqcy cxcy cxcz.
  intros HIn.
  inversion cxcz; ssame; try solve [subst; eauto].
  (* S_Empty *)
  - destruct b1; crush.
  (* S_First *)
  - destruct b1; simpl in *.
    + inv H1.
      gotw (C (<< N k t es; l ->> pfold f (t_app (t_app f t) t') (remove Nat.eq_dec k ks) :: os1 ++ [l0 ->> op] >> :: b') os' rs0 term0); eauto.
      * rewrite -> List.app_comm_cons.
        eapply S_First; eauto.
      * eapply S_PFold with (b1:=[]); eauto; crush.
    + inv H1.
      gotw (C (<< n1; os2 ++ [l0 ->> op]>> :: b1 ++ << N k t es; l ->> pfold f (t_app (t_app f t) t') (remove Nat.eq_dec k ks) :: os1 >> :: b2) os' rs0 term0); eauto.
      * rewrite List.app_comm_cons.
        eapply S_PFold with (b1:=(<< n1; os2 ++ [l0 ->> op] >> :: b1)); crush.
  (* S_Add *)
  - got.
    * instantiate (1:=C (<<N k0 v t_ks_nil; []>> :: b1 ++ << N k t es; l ->> pfold f (t_app (t_app f t) t') (remove Nat.eq_dec k ks) :: os1 >> :: b2) os' (l0 ->>> final H :: rs0) term0); eauto.
    * instantiate (1:=C ((<<N k0 v t_ks_nil; []>> :: b1) ++ << N k t es; l ->> pfold f (t_app (t_app f t) t') (remove Nat.eq_dec k ks) :: os1 >> :: b2) os' (l0 ->>> final H :: rs0) term0); eauto.
      one_step; eapply S_PFold; eauto; crush.
    * crush.
  (* S_PMap *)
  - tsod.
    + crush.
    + destruct Hfirst as [b' [b'' [b''']]].
      tu1.
      got.
      * instantiate (1:=C ((b' ++ << N k t es; l ->> pfold f (t_app (t_app f t) t') (remove Nat.eq_dec k ks) :: os1 >> :: b'') ++ << N k0 (t_app f0 v) es0; l0 ->> pmap f0 (remove Nat.eq_dec k0 ks0) :: os1'' >> :: b3) os0 rs0 term0).
        one_step; eapply S_PMap; eauto; crush.
      * instantiate (1:=C (b' ++ << N k t es; l ->> pfold f (t_app (t_app f t) t') (remove Nat.eq_dec k ks) :: os1 >> :: b'' ++ << N k0 (t_app f0 v) es0; l0 ->> pmap f0 (remove Nat.eq_dec k0 ks0) :: os1'' >> :: b3) os0 rs0 term0); eauto.
      * crush.
    + destruct Hsecond as [b' [b'' [b''']]].
      tu2.
      got.
      * instantiate (1:=C (b0 ++ << N k0 (t_app f0 v) es0; l0 ->> pmap f0 (remove Nat.eq_dec k0 ks0) :: os1'' >> :: b'' ++ << N k t es; l ->> pfold f (t_app (t_app f t) t') (remove Nat.eq_dec k ks) :: os1 >> :: b''') os0 rs0 term0); eauto.
      * instantiate (1:=C ((b0 ++ << N k0 (t_app f0 v) es0; l0 ->> pmap f0 (remove Nat.eq_dec k0 ks0) :: os1'' >> :: b'') ++ << N k t es; l ->> pfold f (t_app (t_app f t) t') (remove Nat.eq_dec k ks) :: os1 >> :: b''') os0 rs0 term0); eauto.
        one_step; eapply S_PFold; eauto; crush.
      * crush.
  (* S_PFold *)
  - tsod.
    + inv Hsame5. inv H. apply List.app_inv_head in H1; inv H1. crush.
    + destruct Hfirst as [b' [b'' [b''']]].
      tu1.
      got.
      * instantiate (1:=C ((b' ++ << N k t es; l ->> pfold f (t_app (t_app f t) t') (remove Nat.eq_dec k ks) :: os1 >> :: b'') ++ << N k0 t0 es0; l0 ->> pfold f0 (t_app (t_app f0 t0) t'0) (remove Nat.eq_dec k0 ks0) :: os1'' >> :: b3) os0 rs0 term0).
        one_step; eapply S_PFold; eauto; crush.
      * instantiate (1:=C (b' ++ << N k t es; l ->> pfold f (t_app (t_app f t) t') (remove Nat.eq_dec k ks) :: os1 >> :: b'' ++ << N k0 t0 es0; l0 ->> pfold f0 (t_app (t_app f0 t0) t'0) (remove Nat.eq_dec k0 ks0) :: os1'' >> :: b3) os0 rs0 term0); eauto.
      * crush.
    + destruct Hsecond as [b' [b'' [b''']]].
      tu2.
      got.
      * instantiate (1:=C (b0 ++ << N k0 t0 es0; l0 ->> pfold f0 (t_app (t_app f0 t0) t'0) (remove Nat.eq_dec k0 ks0) :: os1'' >> :: b'' ++ << N k t es; l ->> pfold f (t_app (t_app f t) t') (remove Nat.eq_dec k ks) :: os1 >> :: b''') os0 rs0 term0); eauto.
      * instantiate (1:=C ((b0 ++ << N k0 t0 es0; l0 ->> pfold f0 (t_app (t_app f0 t0) t'0) (remove Nat.eq_dec k0 ks0) :: os1'' >> :: b'') ++ << N k t es; l ->> pfold f (t_app (t_app f t) t') (remove Nat.eq_dec k ks) :: os1 >> :: b''') os0 rs0 term0).
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
      assert (b1 ++ << N k t es; l ->> pfold f t' ks :: os1 >> :: x0 ++ [x] = (b1 ++ << N k t es; l ->> pfold f t' ks :: os1 >> :: x0) ++ [x]) by crush.
      rewrite H1 in H2; clear H1.
      apply List.app_inj_tail in H2.
      destruct H2.
      subst.
      got.
      * instantiate (1:=C ((b1 ++ << N k t es; l ->> pfold f (t_app (t_app f t) t') (remove Nat.eq_dec k ks) :: os1 >> :: x0) ++ [<< n1; os1' >>]) os0 (l0 ->>> final H :: rs0) term0).
        one_step. eapply S_Last; eauto; crush.
      * instantiate (1:=C (b1 ++ << N k t es; l ->> pfold f (t_app (t_app f t) t') (remove Nat.eq_dec k ks) :: os1 >> :: x0 ++ [<< n1; os1' >>]) os0 (l0 ->>> final H :: rs0) term0).
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
      - instantiate (1:=C (b0 ++ << N k' v' es; (l ->> pfold f (t_app (t_app f v') t') (remove Nat.eq_dec k' ks) :: os2) ++ l' ->> pmap (pmap_compose f' f0) ks0 :: os3 >> :: b3) os0 (l0 ->>> final H :: rs0) term0).
        one_step. eapply S_FusePMap; crush.
      - instantiate (1:=C (b0 ++ << N k' v' es; (l ->> pfold f (t_app (t_app f v') t') (remove Nat.eq_dec k' ks) :: os2) ++ l' ->> pmap (pmap_compose f' f0) ks0 :: os3 >> :: b3) os0 (l0 ->>> final H :: rs0) term0).
        one_step. inv H0. apply List.app_inv_head in H2; inv H2. eapply S_PFold; crush.
      - crush.
      }
    + destruct Hfirst as [b' [b'' [b''']]].
      tu1.
      got.
      * instantiate (1:=C ((b' ++ << N k t es; l ->> pfold f (t_app (t_app f t) t') (remove Nat.eq_dec k ks) :: os1 >> :: b'') ++ << N k' v' e; os2 ++ l' ->> pmap (pmap_compose f' f0) ks0 :: os3 >> :: b3) os0 (l0 ->>> 0 :: rs0) term0).
        one_step; eapply S_FusePMap; eauto; crush.
      * instantiate (1:=C (b' ++ << N k t es; l ->> pfold f (t_app (t_app f t) t') (remove Nat.eq_dec k ks) :: os1 >> :: b'' ++ << N k' v' e; os2 ++ l' ->> pmap (pmap_compose f' f0) ks0 :: os3 >> :: b3) os0 (l0 ->>> 0 :: rs0) term0).
        eauto.
      * crush.
    + destruct Hsecond as [b' [b'' [b''']]].
      tu2.
      got.
      * instantiate (1:=C (b0 ++ << N k' v' e; os2 ++ l' ->> pmap (pmap_compose f' f0) ks0 :: os3 >> :: b'' ++ << N k t es; l ->> pfold f (t_app (t_app f t) t') (remove Nat.eq_dec k ks) :: os1 >> :: b''') os0 (l0 ->>> 0 :: rs0) term0).
        eauto.
      * instantiate (1:=C ((b0 ++ << N k' v' e; os2 ++ l' ->> pmap (pmap_compose f' f0) ks0 :: os3 >> :: b'') ++ << N k t es; l ->> pfold f (t_app (t_app f t) t') (remove Nat.eq_dec k ks) :: os1 >> :: b''') os0 (l0 ->>> 0 :: rs0) term0).
        one_step; eapply S_PFold; eauto; crush.
      * crush.
  (* S_Prop *)
  - destruct n1 as [k' v'].
    tsod.
    + simpl in *. inv Hsame5. crush.
    + destruct Hfirst as [b' [b'' [b''']]].
      tu1.
      got.
      * instantiate (1:=C ((b' ++ << N k t es; l ->> pfold f (t_app (t_app f t) t') (remove Nat.eq_dec k ks) :: os1 >> :: b'') ++ << N k' v' e; os2 >> :: << n2; os3 ++ [l0 ->> op] >> :: b3) os0 rs0 term0).
        one_step; eapply S_Prop; eauto; crush.
      * instantiate (1:=C (b' ++ << N k t es; l ->> pfold f (t_app (t_app f t) t') (remove Nat.eq_dec k ks) :: os1 >> :: b'' ++ << N k' v' e; os2 >> :: << n2; os3 ++ [l0 ->> op] >> :: b3) os0 rs0 term0).
        eauto.
      * crush.
    + destruct Hsecond as [b' [b'' [b''']]].
      tu2.
      destruct b''.
      * inv H1; simpl in *.
        got.
        { instantiate (1:=C (b0 ++ << N k' v' e; os2 >> :: << N k t es; (l ->> pfold f (t_app (t_app f t) t') (remove Nat.eq_dec k ks) :: os1) ++ [l0 ->> op] >> :: b3) os0 rs0 term0).
          one_step; eapply S_Prop; eauto. }
        { instantiate (1:=C ((b0 ++ [<< N k' v' e; os2 >>]) ++ << N k t es; (l ->> pfold f (t_app (t_app f t) t') (remove Nat.eq_dec k ks) :: os1) ++ [l0 ->> op] >> :: b3) os0 rs0 term0).
          one_step; eapply S_PFold; eauto; crush. }
        { crush. }
      * inv H1; simpl in *.
        got.
        { instantiate (1:=C (b0 ++ << N k' v' e; os2 >> :: << n2; os3 ++ [l0 ->> op] >> :: b'' ++ << N k t es; l ->> pfold f (t_app (t_app f t) t') (remove Nat.eq_dec k ks) :: os1 >> :: b''') os0 rs0 term0).
          one_step; eapply S_Prop; eauto; crush. }
        { instantiate (1:=C ((b0 ++ << N k' v' e; os2 >> :: << n2; os3 ++ [l0 ->> op] >> :: b'') ++ << N k t es; l ->> pfold f (t_app (t_app f t) t') (remove Nat.eq_dec k ks) :: os1 >> :: b''') os0 rs0 term0).
          one_step; eapply S_PFold; eauto; crush. }
        { crush. }
  (* S_LoadPFold *)
  - tsod.
    + destruct os2.
      * inv Hsame5; simpl in *. fsame.
        copy H1. rename H into Hfstep. apply pfold_get with (t:=t_app f0 t0) in Hfstep; dtr.
        apply fstar_into_star_loadpfold with (b1:=b0) (b2:=b3) (n':=N k0 t0 es0) (os1:=[]) (l:=l0) (t1:=f0) (t3:=remove Nat.eq_dec k0 ks0) (os2:=os') (os0:=os0) (rs:=rs0) (t0:=term0) in H.
        apply fstar_into_star_loadpfold with (b1:=b0) (b2:=b3) (n':=N k0 t0 es0) (os1:=[]) (l:=l0) (t1:=f0) (t3:=remove Nat.eq_dec k0 ks0) (os2:=os') (os0:=os0) (rs:=rs0) (t0:=term0) in H0.
        rename H into star1.
        rename H0 into star2.
        got.
        { instantiate (1:=C (b0 ++ << N k0 t0 es0; l0 ->> pfold f0 x1 (remove Nat.eq_dec k0 ks0) :: os' >> :: b3) os0 rs0 term0).
          eauto. }
        { instantiate (1:=C (b0 ++ << N k0 t0 es0; l0 ->> pfold f0 x1 (remove Nat.eq_dec k0 ks0) :: os' >> :: b3) os0 rs0 term0).
          eauto. }
      { crush. }
      { unfold non_emitting. inv WT; dtr. inv H2. wtbdist. inv H3. inv H15. inv H9. replace false with (false || false || false). eauto. auto. }
      { unfold non_emitting. inv WT; dtr. inv H2. wtbdist. inv H3. inv H15. inv H9. replace false with (false || false || false). eauto. auto. }
      { apply to_value. }
      * inv Hsame5.
        got.
        { instantiate (1:=C (b0 ++ << N k0 t0 es0; (l ->> pfold f (t_app (t_app f t0) t') (remove Nat.eq_dec k0 ks) :: os2) ++ l0 ->> pfold f0 t1' ks0 :: os' >> :: b3) os0 rs0 term0).
          inv H. apply List.app_inv_head in H2; inv H2. one_step; eapply S_LoadPFold; eauto; crush. }
        { instantiate (1:=C (b0 ++ << N k0 t0 es0; l ->> pfold f (t_app (t_app f t0) t') (remove Nat.eq_dec k0 ks) :: os2 ++ l0 ->> pfold f0 t1' ks0 :: os' >> :: b3) os0 rs0 term0).
          one_step; eapply S_PFold; eauto; crush. }
        { crush. }
    + destruct Hfirst as [b' [b'' [b''']]].
      tu1.
      got.
      * instantiate (1:=C ((b' ++ << N k t es; l ->> pfold f (t_app (t_app f t) t') (remove Nat.eq_dec k ks) :: os1 >> :: b'') ++ << N k0 t0 es0; os2 ++ l0 ->> pfold f0 t1' ks0 :: os' >> :: b3) os0 rs0 term0).
        one_step; eapply S_LoadPFold; eauto; crush.
      * instantiate (1:=C (b' ++ << N k t es; l ->> pfold f (t_app (t_app f t) t') (remove Nat.eq_dec k ks) :: os1 >> :: b'' ++ << N k0 t0 es0; os2 ++ l0 ->> pfold f0 t1' ks0 :: os' >> :: b3) os0 rs0 term0).
        eauto.
      * crush.
    + destruct Hsecond as [b' [b'' [b''']]].
      tu2.
      got.
      * instantiate (1:=C (b0 ++ << N k0 t0 es0; os2 ++ l0 ->> pfold f0 t1' ks0 :: os' >> :: b'' ++ << N k t es; l ->> pfold f (t_app (t_app f t) t') (remove Nat.eq_dec k ks) :: os1 >> :: b''') os0 rs0 term0).
        eauto.
      * instantiate (1:=C ((b0 ++ << N k0 t0 es0; os2 ++ l0 ->> pfold f0 t1' ks0 :: os' >> :: b'') ++ << N k t es; l ->> pfold f (t_app (t_app f t) t') (remove Nat.eq_dec k ks) :: os1 >> :: b''') os0 rs0 term0).
        one_step; eapply S_PFold; eauto; crush.
      * crush.
Unshelve.
auto.
auto.
auto.
Qed.
Hint Resolve lc_pfold.

Ltac tsod''' := match goal with
              | [H : ?b1 ++ <<N ?k ?t ?es; ?os ++ ?os'''>> :: ?b2 = ?b3 ++ <<N ?k' ?t' ?es'; ?os' ++ ?os''>> :: ?b4 |- _] =>
                  eapply (@target_same_or_different _ b1 b2 b3 b4 k t es es' k' t' (os ++ os''') (os' ++ os'')) in H; eauto; destruct H as [Hsame|Hwhich]; try destruct Hwhich as [Hfirst|Hsecond];
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
  forall cx cy cz b1 b2 k t es f t1 t1' l ks os os' term0 os0 rs0,
  well_typed cx ->
  cx = C (b1 ++ <<N k t es; os ++ l ->> pfold f t1 ks :: os'>> :: b2) os0 rs0 term0 ->
  cy = C (b1 ++ <<N k t es; os ++ l ->> pfold f t1' ks :: os'>> :: b2) os0 rs0 term0 ->
  cx --> cy ->
  cx --> cz ->
  FRf t1 rs0 ==> FRt t1' [] ->
  cy -v cz.
Proof using.
  intros cx cy cz b1 b2 k t es f t1 t1' l ks os os' term0 os0 rs0.
  intros WT Heqcx Heqcy cxcy cxcz.
  intros tt'.
  inversion cxcz; ssame; try solve [subst; eauto].
  (* S_Empty *)
  - destruct b1; crush.
  (* S_First *)
  - destruct b1; inv H1; simpl in *.
    + gotw (C (<< N k t es; (os ++ l ->> pfold f t1' ks :: os') ++ [l0 ->> op] >> :: b') os'0 rs term1); eauto.
      * rewrite <- List.app_assoc. rewrite <- List.app_comm_cons. eapply S_LoadPFold with (b1:=[]); eauto; crush.
    + got.
      * instantiate (1:=(C (<< n1; os2 ++ [l0 ->> op] >> :: b1 ++ << N k t es; os ++ l ->> pfold f t1' ks :: os' >> :: b2) os'0 rs term1)).
        one_step; eapply S_First; eauto; crush.
      * instantiate (1:=(C (<< n1; os2 ++ [l0 ->> op] >> :: b1 ++ << N k t es; os ++ l ->> pfold f t1' ks :: os' >> :: b2) os'0 rs term1)).
        one_step; eapply S_LoadPFold; eauto; crush.
      * crush.
  (* S_Add *)
  - got.
    + instantiate (1:=C (<< N k0 v t_ks_nil; [] >> :: b1 ++ << N k t es; os ++ l ->> pfold f t1' ks :: os' >> :: b2) os'0 (l0 ->>> final H :: rs) term1).
      one_step; eapply S_Add; eauto.
    + instantiate (1:=C ((<< N k0 v t_ks_nil; [] >> :: b1) ++ << N k t es; os ++ l ->> pfold f t1' ks :: os' >> :: b2) os'0 (l0 ->>> final H :: rs) term1).
      one_step; eapply S_LoadPFold; eauto; crush.
    + crush.
  (* S_PMap *)
  - tsod.
    + destruct os.
      * inv Hsame5.
      * inv Hsame5.
        got.
        { instantiate (1:=C (b0 ++ << N k0 (t_app f0 v) es; l0 ->> pmap f0 (remove Nat.eq_dec k0 ks0) :: os ++ l ->> pfold f t1' ks :: os' >> :: b3) os1 rs term1).
          one_step; eapply S_PMap; eauto; crush. }
        { instantiate (1:=C (b0 ++ << N k0 (t_app f0 v) es; (l0 ->> pmap f0 (remove Nat.eq_dec k0 ks0) :: os) ++ l ->> pfold f t1' ks :: os' >> :: b3) os1 rs term1).
          fsame. one_step; eapply S_LoadPFold; eauto; crush. }
        { crush. }
    + destruct Hfirst as [b' [b'' [b''']]].
      tu1.
      got.
      * instantiate (1:=C ((b' ++ << N k t es; os ++ l ->> pfold f t1' ks :: os' >> :: b'') ++ << N k0 (t_app f0 v) es0; l0 ->> pmap f0 (remove Nat.eq_dec k0 ks0) :: os1'' >> :: b3) os1 rs term1).
        one_step; eapply S_PMap; eauto; crush.
      * instantiate (1:=C ((b' ++ << N k t es; os ++ l ->> pfold f t1' ks :: os' >> :: b'') ++ << N k0 (t_app f0 v) es0; l0 ->> pmap f0 (remove Nat.eq_dec k0 ks0) :: os1'' >> :: b3) os1 rs term1).
        one_step; eapply S_LoadPFold; eauto; crush.
      * crush.
    + destruct Hsecond as [b' [b'' [b''']]].
      tu2.
      got.
      * instantiate (1:=C (b0 ++ << N k0 (t_app f0 v) es0; l0 ->> pmap f0 (remove Nat.eq_dec k0 ks0) :: os1'' >> :: b'' ++ << N k t es; os ++ l ->> pfold f t1' ks :: os' >> :: b''') os1 rs term1).
        one_step; eapply S_PMap; eauto; crush.
      * instantiate (1:=C ((b0 ++ << N k0 (t_app f0 v) es0; l0 ->> pmap f0 (remove Nat.eq_dec k0 ks0) :: os1'' >> :: b'') ++ << N k t es; os ++ l ->> pfold f t1' ks :: os' >> :: b''') os1 rs term1).
        one_step; eapply S_LoadPFold; eauto; crush.
      * crush.
  (* S_Last *)
  - destruct b2; simpl in *.
    + destruct os; simpl in *.
      * apply List.app_inj_tail in H2; destruct H2; inv H2.
        exfalso.
        apply frontend_no_value in tt'.
        {
        destruct H.
        - crush.
        - destruct e. destruct e. destruct e. inversion e. subst.
          crush.
        }
      * apply List.app_inj_tail in H2; destruct H2; inv H2.
        got.
        { instantiate (1:=C (b0 ++ [<< N k t es; os ++ l ->> pfold f t1' ks :: os' >>]) os1 (l0 ->>> final H :: rs) term1).
          one_step; eapply S_Last; eauto; crush. }
        { instantiate (1:=C (b0 ++ [<< N k t es; os ++ l ->> pfold f t1' ks :: os' >>]) os1 (l0 ->>> final H :: rs) term1).
          one_step; eapply S_LoadPFold; eauto; crush. }
        { crush. }
    + remember (s :: b2) as bend.
      assert (exists y ys, bend = ys ++ [y]) by (apply list_snoc with (xs:=bend) (x:=s) (xs':=b2); crush).
      destruct H1; destruct H1.
      inv H1.
      rewrite H3 in *. clear H3.
      assert (b1 ++ << N k t es; os ++ l ->> pfold f t1 ks :: os' >> :: x0 ++ [x] = (b1 ++ << N k t es; os ++ l ->> pfold f t1 ks :: os' >> :: x0) ++ [x]) by crush.
      rewrite H1 in H2. clear H1.
      apply List.app_inj_tail in H2.
      destruct H2.
      subst.
      got.
      * instantiate (1:=C ((b1 ++ << N k t es; os ++ l ->> pfold f t1' ks :: os' >> :: x0) ++ [<< n1; os1' >>]) os1 (l0 ->>> final H :: rs) term1).
        one_step; eapply S_Last; eauto; crush.
      * instantiate (1:=C ((b1 ++ << N k t es; os ++ l ->> pfold f t1' ks :: os' >> :: x0) ++ [<< n1; os1' >>]) os1 (l0 ->>> final H :: rs) term1).
        one_step; eapply S_LoadPFold; eauto; crush.
      * crush.
  (* S_FusePMap *)
  - destruct n as [k' t']. tsod'''.
    + osod.
      * inv Hsame. destruct H2. crush.
      * destruct Hfirst as [os''0 [os'' [os''']]].
        ou1.
        got.
        { instantiate (1:=C (b0 ++ << N k' t' e; (os''0 ++ l ->> pfold f t1' ks :: os'') ++ l' ->> pmap (pmap_compose f' f0) ks0 :: os3 >> :: b3) os1 (l0 ->>> 0 :: rs) term1).
          one_step; eapply S_FusePMap; eauto; crush. }
        { instantiate (1:=C (b0 ++ << N k' t' e; (os''0 ++ l ->> pfold f t1' ks :: os'') ++ l' ->> pmap (pmap_compose f' f0) ks0 :: os3 >> :: b3) os1 (l0 ->>> 0 :: rs) term1).
          one_step; eapply S_LoadPFold; eauto; crush. }
        { crush. }
      * destruct Hsecond as [os''0 [os'' [os''']]].
        ou2.
        {
        destruct os''; inv H1; simpl in *.
        - got.
          + instantiate (1:=C (b0 ++ << N k' t' e; os2 ++ l' ->> pmap (pmap_compose f' f0) ks0 :: os'' ++ l ->> pfold f t1' ks :: os''' >> :: b3) os1 (l0 ->>> 0 :: rs) term1).
            one_step; eapply S_FusePMap; eauto; crush.
          + instantiate (1:=C (b0 ++ << N k' t' e; (os2 ++ l' ->> pmap (pmap_compose f' f0) ks0 :: os'') ++ l ->> pfold f t1' ks :: os''' >> :: b3) os1 (l0 ->>> 0 :: rs) term1).
            one_step; eapply S_LoadPFold; eauto; crush.
          + crush.
        }
    + destruct Hfirst as [b' [b'' [b''']]].
      tu1.
      got.
      * instantiate (1:=C ((b' ++ << N k t es; os ++ l ->> pfold f t1' ks :: os' >> :: b'') ++ << N k' t' e; os2 ++ l' ->> pmap (pmap_compose f' f0) ks0 :: os3 >> :: b3) os1 (l0 ->>> 0 :: rs) term1).
        one_step; eapply S_FusePMap; eauto; crush.
      * instantiate (1:=C ((b' ++ << N k t es; os ++ l ->> pfold f t1' ks :: os' >> :: b'') ++ << N k' t' e; os2 ++ l' ->> pmap (pmap_compose f' f0) ks0 :: os3 >> :: b3) os1 (l0 ->>> 0 :: rs) term1).
        one_step; eapply S_LoadPFold; eauto; crush.
      * crush.
    + destruct Hsecond as [b' [b'' [b''']]].
      tu2.
      got.
      * instantiate (1:=C (b0 ++ << N k' t' e; os2 ++ l' ->> pmap (pmap_compose f' f0) ks0 :: os3 >> :: b'' ++ << N k t es; os ++ l ->> pfold f t1' ks :: os' >> :: b''') os1 (l0 ->>> 0 :: rs) term1).
        one_step; eapply S_FusePMap; eauto; crush.
      * instantiate (1:=C ((b0 ++ << N k' t' e; os2 ++ l' ->> pmap (pmap_compose f' f0) ks0 :: os3 >> :: b'') ++ << N k t es; os ++ l ->> pfold f t1' ks :: os' >> :: b''') os1 (l0 ->>> 0 :: rs) term1).
        one_step; eapply S_LoadPFold; eauto; crush.
      * crush.
  (* S_Prop *)
  - destruct n1 as [k' t']. tsod.
    + destruct os; simpl in *.
      * inv Hsame5.
        got.
        { instantiate (1:=C (b0 ++ << N k' t' e; os2 >> :: << n2; os3 ++ [l0 ->> pfold f t1' ks] >> :: b3) os1 rs term1).
          fsame. one_step; eapply S_Prop; eauto; crush. }
        { instantiate (1:=C ((b0 ++ [<< N k' t' e; os2 >>]) ++ << n2; os3 ++ [l0 ->> pfold f t1' ks] >> :: b3) os1 rs term1).
          destruct n2. one_step; eapply S_LoadPFold with (b1:=(b0 ++ [<< N k' t' e; os2 >>])) (os:=os3) (os':=[]); eauto; crush. }
        { crush. }
      * inv Hsame5.
        got.
        { instantiate (1:=C (b0 ++ << N k' t' e; os ++ l ->> pfold f t1' ks :: os' >> :: << n2; os3 ++ [l0 ->> op] >> :: b3) os1 rs term1).
          fsame. one_step; eapply S_Prop; eauto; crush. }
        { instantiate (1:=C (b0 ++ << N k' t' e; os ++ l ->> pfold f t1' ks :: os' >> :: << n2; os3 ++ [l0 ->> op] >> :: b3) os1 rs term1).
          one_step; eapply S_LoadPFold; eauto; crush. }
        { crush. }
    + destruct Hfirst as [b' [b'' [b''']]].
      tu1.
      got.
      * instantiate (1:=C ((b' ++ << N k t es; os ++ l ->> pfold f t1' ks :: os' >> :: b'') ++ << N k' t' e; os2 >> :: << n2; os3 ++ [l0 ->> op] >> :: b3) os1 rs term1).
        one_step; eapply S_Prop; eauto; crush.
      * instantiate (1:=C ((b' ++ << N k t es; os ++ l ->> pfold f t1' ks :: os' >> :: b'') ++ << N k' t' e; os2 >> :: << n2; os3 ++ [l0 ->> op] >> :: b3) os1 rs term1).
        one_step; eapply S_LoadPFold; eauto; crush.
      * crush.
    + destruct Hsecond as [b' [b'' [b''']]].
      tu2.
      destruct b''; inv H1; simpl in *.
      * got.
        { instantiate (1:=C (b0 ++ << N k' t' e; os2 >> :: << N k t es; (os ++ l ->> pfold f t1' ks :: os') ++ [l0 ->> op] >> :: b3) os1 rs term1).
          one_step; eapply S_Prop; eauto; crush. }
        { instantiate (1:=C ((b0 ++ [<< N k' t' e; os2 >>]) ++ << N k t es; os ++ l ->> pfold f t1' ks :: os' ++ [l0 ->> op] >> :: b3) os1 rs term1).
          one_step; eapply S_LoadPFold; eauto; crush. }
        { crush. }
      * got.
        { instantiate (1:=C (b0 ++ << N k' t' e; os2 >> :: << n2; os3 ++ [l0 ->> op] >> :: b'' ++ << N k t es; os ++ l ->> pfold f t1' ks :: os' >> :: b''') os1 rs term1).
          one_step; eapply S_Prop; eauto; crush. }
        { instantiate (1:=C ((b0 ++ << N k' t' e; os2 >> :: << n2; os3 ++ [l0 ->> op] >> :: b'') ++ << N k t es; os ++ l ->> pfold f t1' ks :: os' >> :: b''') os1 rs term1).
          one_step; eapply S_LoadPFold; eauto; crush. }
        { crush. }
  (* S_LoadPFold *)
  - tsod.
    + osod.
      * crush. inv H4. fsame.
        eapply frontend_deterministic' with (b0:=b0 ++ << N k0 t0 es0; os2 ++ l0 ->> pfold f0 t2 ks0 :: os'0 >> :: b3) (os0:=os1) (os:=[]) (t':=t1'0) in tt'; eauto. crush.
        inversion WT. dtr.
        {
        split; try split.
        - crush.
        - crush.
        - exists Result, false.
          inv WT; dtr. inv H3.
          econstructor.
          + eapply wt_backend_build; eauto.
          + wtbt. eauto.
          + wtbdist. inv H6. wtosdist. inv H7. inv H18. wtbt. wtost. wtbt. wttost. wtost.
            simpl in *. eauto.
        }
      * destruct Hfirst as [os''0 [os'' [os''']]].
        ou1.
        got.
        { instantiate (1:=C (b0 ++ << N k0 t0 es0; (os''0 ++ l ->> pfold f t1' ks :: os'') ++ l0 ->> pfold f0 t1'0 ks0 :: os'0 >> :: b3) os1 rs1 term1).
          one_step; eapply S_LoadPFold with (os:=(os''0 ++ l ->> pfold f t1' ks :: os'')); eauto; crush. }
        { instantiate (1:=C (b0 ++ << N k0 t0 es0; (os''0 ++ l ->> pfold f t1' ks :: os'') ++ l0 ->> pfold f0 t1'0 ks0 :: os'0 >> :: b3) os1 rs1 term1).
          one_step; eapply S_LoadPFold; eauto; crush. }
        { crush. }
      * destruct Hsecond as [os''0 [os'' [os''']]].
        ou2.
        got.
        { instantiate (1:=C (b0 ++ << N k0 t0 es0; os2 ++ l0 ->> pfold f0 t1'0 ks0 :: os'' ++ l ->> pfold f t1' ks :: os''' >> :: b3) os1 rs1 term1).
          one_step; eapply S_LoadPFold; eauto; crush. }
        { instantiate (1:=C (b0 ++ << N k0 t0 es0; (os2 ++ l0 ->> pfold f0 t1'0 ks0 :: os'') ++ l ->> pfold f t1' ks :: os''' >> :: b3) os1 rs1 term1).
          one_step; eapply S_LoadPFold with (b1:=b0) (t1':=t1') (os':=os''') (b2:=b3) (k:=k0) (f:=f) (l:=l) (ks:=ks) (t:=t0) (os:=(os2 ++ l0 ->> pfold f0 t1'0 ks0 :: os'')); eauto; crush. }
        { crush. }
    + destruct Hfirst as [b' [b'' [b''']]].
      tu1.
      got.
      * instantiate (1:=C ((b' ++ << N k t es; os ++ l ->> pfold f t1' ks :: os' >> :: b'') ++ << N k0 t0 es0; os2 ++ l0 ->> pfold f0 t1'0 ks0 :: os'0 >> :: b3) os1 rs1 term1).
        one_step; eapply S_LoadPFold with (b1:=(b' ++ << N k t es; os ++ l ->> pfold f t1' ks :: os' >> :: b'')); eauto; crush.
      * instantiate (1:=C (b' ++ << N k t es; os ++ l ->> pfold f t1' ks :: os' >> :: b'' ++ << N k0 t0 es0; os2 ++ l0 ->> pfold f0 t1'0 ks0 :: os'0 >> :: b3) os1 rs1 term1).
        one_step; eapply S_LoadPFold; eauto; crush.
      * crush.
    + destruct Hsecond as [b' [b'' [b''']]].
      tu2.
      got.
      * instantiate (1:=C (b0 ++ << N k0 t0 es0; os2 ++ l0 ->> pfold f0 t1'0 ks0 :: os'0 >> :: b'' ++ << N k t es; os ++ l ->> pfold f t1' ks :: os' >> :: b''') os1 rs1 term1).
        one_step; eapply S_LoadPFold; eauto; crush.
      * instantiate (1:=C ((b0 ++ << N k0 t0 es0; os2 ++ l0 ->> pfold f0 t1'0 ks0 :: os'0 >> :: b'') ++ << N k t es; os ++ l ->> pfold f t1' ks :: os' >> :: b''') os1 rs1 term1).
        one_step; eapply S_LoadPFold with (k:=k) (t:=t) (t1':=t1') (os:=os) (l:=l) (f:=f) (ks:=ks) (b2:=b''') (os':=os') (b1:=(b0 ++ << N k0 t0 es0; os2 ++ l0 ->> pfold f0 t1'0 ks0 :: os'0 >> :: b'')); eauto; crush.
      * crush.
Unshelve.
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
  - gotw (C (<< N k v t_ks_nil; [] >> :: b1 ++ << n1; os1 >> :: << n2; os2 ++ [l ->> op] >> :: b2) os' (l0 ->>> final H :: rs0) term0); eauto.
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
      eapply target_unique with (b1:=b1) (b2:=<< n2; os2 >> :: b2) (b3:=x) (b4:=x0 ++ << N k v es; l0 ->> pmap f ks :: os1'' >> :: x1) in H0; crush.
      rewrite H2 in *.
      destruct x0.
      * inv H.
        simpl in *.
        eapply target_unique with (b1:=x ++ [<< N n t e; l ->> op :: os1 >>]) (b2:=x1) (b3:=b0) (b4:=b3) in H1; eauto; crush.
        inv H2.
        {
          got.
          - instantiate (1:=C ((x ++ [<< N n t e; os1 >>]) ++ << N k (t_app f v) es; l0 ->> pmap f (remove Nat.eq_dec k ks) :: os1'' ++ [l ->> op] >> :: b3) os0 rs0 term0).
            one_step. eapply S_PMap; crush.
          - instantiate (1:=C (x ++ << N n t e; os1 >> :: << N k (t_app f v) es; (l0 ->> pmap f (remove Nat.eq_dec k ks) :: os1'') ++ [l ->> op] >> :: b3) os0 rs0 term0).
            one_step. eapply S_Prop; crush.
          - crush.
        }
      * inv H2.
        inv H.
        eapply target_unique with (b1:=x ++ << N n t e; l ->> op :: os1 >> :: << n2; os2 >> :: x0) (b2:=x1) (b3:=b0) (b4:=b3) in H1; eauto; crush.
        {
          got.
          - instantiate (1:=C ((x ++ << N n t e; os1 >> :: << n2; os2 ++ [l ->> op] >> :: x0) ++ << N k (t_app f v) es; l0 ->> pmap f (remove Nat.eq_dec k ks) :: os1'' >> :: b3) os0 rs0 term0).
            one_step. eapply S_PMap; crush.
          - instantiate (1:=C (x ++ << N n t e; os1 >> :: << n2; os2 ++ [l ->> op] >> :: x0 ++ << N k (t_app f v) es; l0 ->> pmap f (remove Nat.eq_dec k ks) :: os1'' >> :: b3) os0 rs0 term0).
            one_step. eapply S_Prop; crush.
          - crush.
        }
    (* First second *)
    + destruct H0. destruct H0. destruct H0.
      eapply target_unique with (b1:=b1) (b2:=<< n2; os2 >> :: b2) (b3:=x ++ << N k v es; l0 ->> pmap f ks :: os1'' >> :: x0) (b4:=x1) in H0; eauto; crush.
      inv H.
      eapply target_unique with (b1:=x) (b2:=x0 ++ << N n t e; l ->> op :: os1 >> :: << n2; os2 >> :: b2) (b3:=b0) (b4:=b3) in H1; eauto; crush.
      got.
      * instantiate (1:= C (b0 ++ << N k (t_app f v) es; l0 ->> pmap f (remove Nat.eq_dec k ks) :: os1'' >> :: x0 ++ << N n t e; os1 >> :: << n2; os2 ++ [l ->> op] >> :: b2) os0 rs0 term0).
        one_step. eapply S_PMap; crush.
      * instantiate (1:= C ((b0 ++ << N k (t_app f v) es; l0 ->> pmap f (remove Nat.eq_dec k ks) :: os1'' >> :: x0) ++ << N n t e; os1 >> :: << n2; os2 ++ [l ->> op] >> :: b2) os0 rs0 term0).
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
        - fsame.
          instantiate (1:=C (b0 ++ << N k' v' e0; os4 >> :: << n2; os2 ++ [l' ->> pmap (pmap_compose f' f) ks] >> :: b2) os0 (l0 ->>> 0 :: rs0) term0).
          apply ex_intro with 2.
          eapply Step.
          instantiate (1:=C (b0 ++ << N k' v' e0; os4 >> :: << n2; (os2 ++ [l0 ->> pmap f ks]) ++ [l' ->> pmap f' ks] >> :: b2) os0 rs0 term0).
          eapply S_Prop; crush.
          apply one_star.
          assert ((os2 ++ [l0 ->> pmap f ks]) ++ [l' ->> pmap f' ks] = os2 ++ [l0 ->> pmap f ks] ++ [l' ->> pmap f' ks]) by crush.
          rewrite H. clear H.
          assert (forall x, b0 ++ << N k' v' e0; os4 >> :: x = (b0 ++ [<< N k' v' e0; os4 >>]) ++ x) by crush.
          rewrite H. clear H.
          assert (b0 ++ << N k' v' e0; os4 >> :: << n2; os2 ++ [l' ->> pmap (pmap_compose f' f) ks] >> :: b2 = (b0 ++ [<< N k' v' e0; os4 >>]) ++ << n2; os2 ++ [l' ->> pmap (pmap_compose f' f) ks] >> :: b2) by crush.
          rewrite H. clear H.
          eapply S_FusePMap; crush.
        - instantiate (1:=C (b0 ++ << N k' v' e0; os4 >> :: << n2; os2 ++ [l' ->> pmap (pmap_compose f' f) ks] >> :: b2) os0 (l0 ->>> 0 :: rs0) term0).
          one_step. eapply S_Prop; crush.
        - crush.
        }
      * simpl in *.
        inv H4.
        {
        fsame.
        got.
        - instantiate (1:=C (b0 ++ << N k' v' e0; os3 ++ l' ->> pmap (pmap_compose f' f) ks :: os4 >> :: << n2; os2 ++ [l ->> op] >> :: b2) os0 (l0 ->>> 0 :: rs0) term0).
          one_step. eapply S_FusePMap; crush.
        - instantiate (1:=C (b0 ++ << N k' v' e0; os3 ++ l' ->> pmap (pmap_compose f' f) ks :: os4 >> :: << n2; os2 ++ [l ->> op] >> :: b2) os0 (l0 ->>> 0 :: rs0) term0).
          one_step. eapply S_Prop; crush.
        - crush.
        }
    (* First first *)
    + destruct H0. destruct H0. destruct H0.
      destruct x0; simpl in *.
      * eapply target_unique with (b1:=b1) (b2:=<< n2; os2 >> :: b2) (b3:=x) (b4:=<< N k' v' e0; os3 ++ l0 ->> pmap f ks :: l' ->> pmap f' ks :: os4 >> :: x1) in H0; eauto; crush.
        inv H2.
        inv H.
        eapply target_unique with (b1:=x ++ [<< N k v e; l ->> op :: os1 >>]) (b2:=x1) (b3:=b0) (b4:=b3) in H1; eauto; crush.
        {
        got.
        - instantiate (1:=C ((x ++ [<< N k v e; os1 >>]) ++ << N k' v' e0; os3 ++ l' ->> pmap (pmap_compose f' f) ks :: os4 ++ [l ->> op] >> :: b3) os0 (l0 ->>> 0 :: rs0) term0).
          one_step. eapply S_FusePMap; crush.
        - instantiate (1:=C (x ++ << N k v e; os1 >> :: << N k' v' e0; (os3 ++ l' ->> pmap (pmap_compose f' f) ks :: os4) ++ [l ->> op] >> :: b3) os0 (l0 ->>> 0 :: rs0) term0).
          one_step. eapply S_Prop; crush.
        - crush.
        }
      * eapply target_unique with (b1:=b1) (b2:=<< n2; os2 >> :: b2) (b3:=x) (b4:=s :: x0 ++ << N k' v' e0; os3 ++ l0 ->> pmap f ks :: l' ->> pmap f' ks :: os4 >> :: x1) in H0; eauto; crush.
        inv H.
        eapply target_unique with (b1:=x ++ << N k v e; l ->> op :: os1 >> :: << n2; os2 >> :: x0) (b2:=x1) (b3:=b0) (b4:=b3) in H1; eauto; crush.
        {
        got.
        - instantiate (1:=C ((x ++ << N k v e; os1 >> :: << n2; os2 ++ [l ->> op] >> :: x0) ++ << N k' v' e0; os3 ++ l' ->> pmap (pmap_compose f' f) ks :: os4 >> :: b3) os0 (l0 ->>> 0 :: rs0) term0).
          one_step. eapply S_FusePMap; crush.
        - instantiate (1:=C (x ++ << N k v e; os1 >> :: << n2; os2 ++ [l ->> op] >> :: x0 ++ << N k' v' e0; os3 ++ l' ->> pmap (pmap_compose f' f) ks :: os4 >> :: b3) os0 (l0 ->>> 0 :: rs0) term0).
          one_step. eapply S_Prop; crush.
        - crush.
        }
    (* First second *)
    + destruct H0. destruct H0. destruct H0.
      eapply target_unique with (b1:=b1) (b2:=<< n2; os2 >> :: b2) (b3:=x ++ << N k' v' e0; os3 ++ l0 ->> pmap f ks :: l' ->> pmap f' ks :: os4 >> :: x0) (b4:=x1) in H0; eauto; crush.
      inv H.
      eapply target_unique with (b1:=x) (b2:=x0 ++ << N k v e; l ->> op :: os1 >> :: << n2; os2 >> :: b2) (b3:=b0) (b4:=b3) in H1; eauto; crush.
      got.
      * instantiate (1:=C (b0 ++ << N k' v' e0; os3 ++ l' ->> pmap (pmap_compose f' f) ks :: os4 >> :: x0 ++ << N k v e; os1 >> :: << n2; os2 ++ [l ->> op] >> :: b2) os0 (l0 ->>> 0 :: rs0) term0).
        one_step. eapply S_FusePMap; crush.
      * instantiate (1:=C ((b0 ++ << N k' v' e0; os3 ++ l' ->> pmap (pmap_compose f' f) ks :: os4 >> :: x0) ++ << N k v e; os1 >> :: << n2; os2 ++ [l ->> op] >> :: b2) os0 (l0 ->>> 0 :: rs0) term0).
        one_step. eapply S_Prop; crush.
      * crush.
  (* S_Prop *)
  - destruct n1 as [k v].
    destruct n0 as [k' v'].
    eapply target_same_or_different with (b1:=b1) (b2:=<< n2; os2 >> :: b2) (b3:=b0) (b4:=<< n3; os4 >> :: b3) (k:=k) (v:=v) (k':=k') (v':=v') in H2; eauto.
    destruct H2; try destruct H1.
    (* Same target *)
    + inv H2.
      fsame. destruct H4. destruct H1. inv H2. inv H3. crush.
    (* First first *)
    + destruct H1. destruct H1. destruct H1.
      destruct x0.
      * simpl in *.
        eapply target_unique with (b1:=b1) (b2:=<< n2; os2 >> :: b2) (b3:=x) (b4:=<< N k' v' e0; l0 ->> op0 :: os3 >> :: x1) in H1; eauto; crush.
        inv H3.
        inv H.
        eapply target_unique with (b1:=x ++ [<< N k v e; l ->> op :: os1 >>]) (b2:=x1) (b3:=b0) (b4:=<< n3; os4 >> :: b3) in H2; eauto; crush.
        {
        got.
        - instantiate (1:=C ((x ++ [<< N k v e; os1 >>]) ++ << N k' v' e0; os3 ++ [l ->> op] >> :: << n3; os4 ++ [l0 ->> op0] >> :: b3) os0 rs0 term0).
          one_step. eapply S_Prop; crush.
        - instantiate (1:=C (x ++ << N k v e; os1 >> :: << N k' v' e0; os3 ++ [l ->> op] >> :: << n3; os4 ++ [l0 ->> op0] >> :: b3) os0 rs0 term0).
          one_step. eapply S_Prop; crush.
        - crush.
        }
      * simpl in *.
        eapply target_unique with (b1:=b1) (b2:=<< n2; os2 >> :: b2) (b3:=x) (b4:=s :: x0 ++ << N k' v' e0; l0 ->> op0 :: os3 >> :: x1) in H1; eauto; crush.
        inv H.
        eapply target_unique with (b1:=x ++ << N k v e; l ->> op :: os1 >> :: << n2; os2 >> :: x0) (b2:=x1) (b3:=b0) (b4:=<< n3; os4 >> :: b3) in H2; eauto; crush.
        {
        got.
        - instantiate (1:=C ((x ++ << N k v e; os1 >> :: << n2; os2 ++ [l ->> op] >> :: x0) ++ << N k' v' e0; os3 >> :: << n3; os4 ++ [l0 ->> op0] >> :: b3) os0 rs0 term0).
          one_step. eapply S_Prop; crush.
        - instantiate (1:=C (x ++ << N k v e; os1 >> :: << n2; os2 ++ [l ->> op] >> :: x0 ++ << N k' v' e0; os3 >> :: << n3; os4 ++ [l0 ->> op0] >> :: b3) os0 rs0 term0).
          one_step. eapply S_Prop; crush.
        - crush.
        }
    (* First second *)
    + destruct H1. destruct H1. destruct H1.
      destruct x0.
      * simpl in *.
        eapply target_unique with (b1:=b1) (b2:=<< n2; os2 >> :: b2) (b3:=x ++ [<< N k' v' e0; l0 ->> op0 :: os3 >>]) (b4:=x1) in H1; eauto; crush.
        inv H.
        eapply target_unique with (b1:=x) (b2:=<< N k v e; l ->> op :: os1 >> :: << n2; os2 >> :: b2) (b3:=b0) (b4:=<< n3; os4 >> :: b3) in H2; eauto; crush.
        inv H1.
        {
        got.
        - instantiate (1:=C (b0 ++ << N k' v' e0; os3 >> :: << N k v e; os1 ++ [l0 ->> op0] >> :: << n2; os2 ++ [l ->> op] >> :: b2) os0 rs0 term0).
          one_step. eapply S_Prop; crush.
        - instantiate (1:=C ((b0 ++ [<< N k' v' e0; os3 >>]) ++ << N k v e; os1 ++ [l0 ->> op0] >> :: << n2; os2 ++ [l ->> op] >> :: b2) os0 rs0 term0).
          one_step. eapply S_Prop; crush.
        - crush.
        }
      * simpl in *.
        eapply target_unique with (b1:=b1) (b2:=<< n2; os2 >> :: b2) (b3:=x ++ << N k' v' e0; l0 ->> op0 :: os3 >> :: s :: x0) (b4:=x1) in H1; eauto; crush.
        inv H.
        eapply target_unique with (b1:=x) (b2:=s :: x0 ++ << N k v e; l ->> op :: os1 >> :: << n2; os2 >> :: b2) (b3:=b0) (b4:=<< n3; os4 >> :: b3) in H2; eauto; crush.
        {
        got.
        - instantiate (1:=C (b0 ++ << N k' v' e0; os3 >> :: << n3; os4 ++ [l0 ->> op0] >> :: x0 ++ << N k v e; os1 >> :: << n2; os2 ++ [l ->> op] >> :: b2) os0 rs0 term0).
          one_step. eapply S_Prop; crush.
        - instantiate (1:=C ((b0 ++ << N k' v' e0; os3 >> :: << n3; os4 ++ [l0 ->> op0] >> :: x0) ++ << N k v e; os1 >> :: << n2; os2 ++ [l ->> op] >> :: b2) os0 rs0 term0).
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
    * gotw (C (<< N k (t_app f v) es; l0 ->> pmap f (remove Nat.eq_dec k ks) :: os1'' ++ [l ->> op] >> :: b2)  os' rs0 term1).
      { inv H1; eapply S_PMap with (b1:=[]); crush. }
      { inv H1; eapply S_First with (os1:=l0 ->> pmap f (remove Nat.eq_dec k ks) :: os1''); crush. }
      { crush. }
    * gotw (C (<< n1; os1 ++ [l ->> op] >> :: b1 ++ << N k (t_app f v) es; l0 ->> pmap f (remove Nat.eq_dec k ks) :: os1'' >> :: b2) os' rs0 term1).
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
  (* S_FusePMap *)
  - destruct b1; simpl in *.
    (* b1 = [] *)
    * gotw (C (<< n; os0 ++ l' ->> pmap (pmap_compose f' f) ks :: os2 ++ [l ->> op] >> :: b2) os' (l0 ->>> 0 :: rs0) term1).
      { inv H2. eapply S_FusePMap with (b1:=[]); crush. }
      { inv H2. assert (os0 ++ l' ->> pmap (pmap_compose f' f) ks :: os2 ++ [l ->> op] = (os0 ++ l' ->> pmap (pmap_compose f' f) ks :: os2) ++ [l ->> op]) by crush. rewrite H1. eapply S_First; crush. }
      { crush. }
    (* b1 != [] *)
    * gotw (C (<< n1; os1 ++ [l ->> op] >> :: b1 ++ << n; os0 ++ l' ->> pmap (pmap_compose f' f) ks :: os2 >> :: b2) os' (l0 ->>> 0 :: rs0) term1).
      { inv H2. eapply S_FusePMap with (b1:=<< n1; os1 ++ [l ->> op] >> :: b1); crush. }
      { inv H2. eapply S_First; crush. }
      { crush. }
Unshelve.
auto.
auto.
Qed.
Hint Resolve lc_first.

Lemma not_afi_subst : forall t x t',
  not (appears_free_in x t) ->
  #[x:=t'] t = t.
Proof using.
  induction t; auto; intros.
  - destruct (string_dec x s).
    + exfalso. apply H. subst. auto.
    + simpl. assert (eqb_string x s = false) by (apply eqb_string_false_iff; auto). rewrite H0. auto.
  - assert (#[x:=t'] t1 = t1) by (apply IHt1; auto).
    assert (#[x:=t'] t2 = t2) by (apply IHt2; auto).
    crush.
  - destruct (string_dec x s).
    + simpl. subst. assert (eqb_string s s = true) by (subst; apply eqb_string_true_iff; auto). rewrite H0. auto.
    + assert (#[x:=t'] t0 = t0) by (apply IHt; auto).
      simpl.
      assert (eqb_string x s = false) by (apply eqb_string_false_iff; auto). rewrite H1.
      assert (#[x:=t'] t0 = t0) by (apply IHt; auto).
      crush.
  - assert (#[x:=t'] t1 = t1) by (apply IHt1; auto).
    assert (#[x:=t'] t2 = t2) by (apply IHt2; auto).
    crush.
  - assert (#[x:=t'] t = t) by (apply IHt; auto).
    crush.
  - assert (#[x:=t'] t1 = t1) by (apply IHt1; auto).
    assert (#[x:=t'] t2 = t2) by (apply IHt2; auto).
    assert (#[x:=t'] t3 = t3) by (apply IHt3; auto).
    crush.
  - assert (#[x:=t'] t1 = t1) by (apply IHt1; auto).
    assert (#[x:=t'] t2 = t2) by (apply IHt2; auto).
    crush.
  - assert (#[x:=t'] t1 = t1) by (apply IHt1; auto).
    assert (#[x:=t'] t2 = t2) by (apply IHt2; auto).
    crush.
  - assert (#[x:=t'] t1 = t1) by (apply IHt1; auto).
    assert (#[x:=t'] t2 = t2) by (apply IHt2; auto).
    assert (#[x:=t'] t3 = t3) by (apply IHt3; auto).
    crush.
  - crush.
  - crush.
  - crush.
  - assert (#[x:=t'] t0 = t0) by (apply IHt; auto).
    crush.
Qed.

Lemma fstar_app2 : forall m t t' t'' rs,
  value t ->
  fstar m t' rs t'' ->
  fstar m (t_app t t') rs (t_app t t'').
Proof using.
  induction m; intros.
  - apply fstar_zero in H0; subst; auto.
  - inv H0. econstructor. instantiate (1:=t_app t t'0). auto. auto.
Qed.

Lemma rewrite_e_subst : forall t1 t2 x v,
  #[x:=v] (t_app t1 t2) = t_app (#[x:=v] t1) (#[x:=v] t2).
Proof using.
  auto.
Qed.

Lemma pmap_compose_comm : forall f f' rs t,
  (exists T1 T2 ll, has_type empty ll f (Arrow T1 T2 false) false) ->
  (exists T1 T2 ll, has_type empty ll f' (Arrow T1 T2 false) false) ->
  value f ->
  value f' ->
  (exists n v, fstar n t rs v /\ value v) ->
  exists n m t', fstar n (t_app f (t_app f' t)) rs t' /\ fstar m (t_app (pmap_compose f f') t) rs t'.
Proof using.
  intros; dtr. unfold pmap_compose. copy H. copy H0. can_fun. can_fun.
  exists x, (S x), (t_app (t_abs x8 x4 u0) (t_app (t_abs x7 x1 u) x0)).
  split.
  - apply fstar_app2; auto. apply fstar_app2; auto.
  - replace (S x) with (x + 1).
    eapply fstar_trans.
    instantiate (1:=t_app (t_abs "x" Result (t_app (t_abs x8 x4 u0) (t_app (t_abs x7 x1 u) (t_var "x")))) x0).
    apply fstar_app2; auto.
    eapply FStep. eapply F_App; auto.
    rewrite rewrite_e_subst.
    replace (#[ "x" := x0] t_abs x8 x4 u0) with (t_abs x8 x4 u0).
    rewrite rewrite_e_subst.
    replace (#[ "x" := x0] t_abs x7 x1 u) with (t_abs x7 x1 u).
    simpl. auto.
    assert (~ (appears_free_in "x" (t_abs x7 x1 u))) by (eapply typable_empty__closed; eauto).
    eapply not_afi_subst in H5; eauto.
    assert (~ (appears_free_in "x" (t_abs x8 x4 u0))) by (eapply typable_empty__closed; eauto).
    eapply not_afi_subst in H5; eauto.
    crush.
Qed.

Lemma rstream_cons_swap : forall t rs t' lr lr',
    FRf t (lr :: lr' :: rs) ==> FRt t' [] ->
    FRf t (lr' :: lr :: rs) ==> FRt t' [].
Proof using.
  induction t; intros; try solve [inv H; constructor; auto].
  - inv H. constructor. crush. auto.
Qed.
Hint Immediate rstream_cons_swap.

Lemma rstream_cons_swap_star : forall n t rs t' lr lr',
    fstar n t (lr :: lr' :: rs) t' ->
    fstar n t (lr' :: lr :: rs) t'.
Proof using.
  induction n; intros.
  - apply fstar_zero in H; subst; auto.
  - inv H.
    inversion H1; subst; econstructor; eauto.
Qed.

Lemma lc_pmap :
  forall cx cy cz rs term0 l f ks os1'' b1 b2 k es os v,
  well_typed cx ->
  cx = C (b1 ++ << N k v es; l ->> pmap f ks :: os1'' >> :: b2) os rs term0 ->
  cy = C (b1 ++ << N k (t_app f v) es; l ->> pmap f (remove Nat.eq_dec k ks) :: os1'' >> :: b2) os rs term0 ->
  In k ks ->
  cx --> cy ->
  cx --> cz ->
  cy -v cz.
Proof using.
  intros cx cy cz rs term0 l f ks os1'' b1 b2 k es os v WT Heqcx Heqcy HIn cxcy cxcz.
  inversion cxcz; ssame; try solve [subst; eauto].
  (* S_Empty *)
  - destruct b1; crush.
  (* S_Add *)
  - gotw (C (<< N k0 v0 t_ks_nil; [] >> :: b1 ++ << N k (t_app f v) es; l ->> pmap f (remove Nat.eq_dec k ks) :: os1'' >> :: b2) os' (l0 ->>> final H :: rs0) term1).
    * eapply S_Add; eauto.
    * eapply S_PMap with (b1:=<< N k0 v0 t_ks_nil; [] >> :: b1); crush.
    * crush.
  (* S_PMap *)
  - rename H1 into H0.
    rename b3 into b4.
    rename b0 into b3.
    {
    eapply target_same_or_different with (b1:=b1) (b2:=b2) (b3:=b3) (b4:=b4) (k:=k) (v:=v) (k':=k0) (v':=v0) in H0; eauto.
    - destruct H0; try destruct H0.
      (* Same target *)
      + fsame. dtr. inv H2. crush.
      (* First first *)
      + destruct H0; destruct H0; destruct H0.
        apply target_unique with (os:=l ->> pmap f ks :: os1'') (k:=k) (v:=v) (b1:=b1) (b2:=b2) (b3:=x) (b4:=x0 ++ << N k0 v0 es0; l0 ->> pmap f0 ks0 :: os1''0 >> :: x1) (os0:=os0) (rs0:=rs0) (t0:=term1) (b:=b1 ++ << N k v es; l ->> pmap f ks :: os1'' >> :: b2) in H0; crush.
        inv H.
        apply target_unique with (os:=l0 ->> pmap f0 ks0 :: os1''0) (k:=k0) (v:=v0) (b1:=x ++ << N k v es; l ->> pmap f ks :: os1'' >> :: x0) (b2:=x1) (b3:=b3) (b4:=b4) (os0:=os0) (rs0:=rs0) (t0:=term1) (b:=x ++ << N k v es; l ->> pmap f ks :: os1'' >> :: x0 ++ << N k0 v0 es0; l0 ->> pmap f0 ks0 :: os1''0 >> :: x1) in H1; crush.
        got.
        * instantiate (1:=C ((x ++ << N k (t_app f v) es; l ->> pmap f (remove Nat.eq_dec k ks) :: os1'' >> :: x0) ++ << N k0 (t_app f0 v0) es0; l0 ->> pmap f0 (remove Nat.eq_dec k0 ks0) :: os1''0 >> :: b4) os0 rs0 term1).
          one_step. eapply S_PMap; crush.
        * instantiate (1:=C (x ++ << N k (t_app f v) es; l ->> pmap f (remove Nat.eq_dec k ks) :: os1'' >> :: x0 ++ << N k0 (t_app f0 v0) es0; l0 ->> pmap f0 (remove Nat.eq_dec k0 ks0) :: os1''0 >> :: b4) os0 rs0 term1).
          one_step. eapply S_PMap; crush.
        * crush.
      (* First second *)
      + destruct H0; destruct H0; destruct H0.
        apply target_unique with (os:=l ->> pmap f ks :: os1'') (k:=k) (v:=v) (b1:=b1) (b2:=b2) (b3:=x ++ << N k0 v0 es0; l0 ->> pmap f0 ks0 :: os1''0 >> :: x0) (b4:=x1) (os0:=os0) (rs0:=rs0) (es:=es) (t0:=term1) (b:=b1 ++ << N k v es; l ->> pmap f ks :: os1'' >> :: b2) in H0; crush.
        inv H.
        eapply target_unique with (os:=l0 ->> pmap f0 ks0 :: os1''0) (k:=k0) (v:=v0) (b1:=x) (b2:=x0 ++ << N k v es; l ->> pmap f ks :: os1'' >> :: x1) (b3:=b3) (b4:=b4) (os0:=os0) (rs0:=rs0) (t0:=term1) in H1; eauto.
        got.
        * instantiate (1:=C (b3 ++ << N k0 (t_app f0 v0) es0; l0 ->> pmap f0 (remove Nat.eq_dec k0 ks0) :: os1''0 >> :: x0 ++ << N k (t_app f v) es; l ->> pmap f (remove Nat.eq_dec k ks) :: os1'' >> :: x1) os0 rs0 term1).
          one_step. eapply S_PMap; crush.
        * instantiate (1:=C ((b3 ++ << N k0 (t_app f0 v0) es0; l0 ->> pmap f0 (remove Nat.eq_dec k0 ks0) :: os1''0 >> :: x0) ++ << N k (t_app f v) es; l ->> pmap f (remove Nat.eq_dec k ks) :: os1'' >> :: x1) os0 rs0 term1).
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
      assert (b1 ++ << N k v es; l ->> pmap f ks :: os1'' >> :: x0 ++ [x]=(b1 ++ << N k v es; l ->> pmap f ks :: os1'' >> :: x0) ++ [x]) by crush.
      rewrite H0 in H1.
      apply List.app_inj_tail in H1.
      destruct H1.
      rewrite H0 in *.
      subst.
      got.
      + instantiate (1:=C ((b1 ++ << N k (t_app f v) es; l ->> pmap f (remove Nat.eq_dec k ks) :: os1'' >> :: x0) ++ [<< n1; os1' >>]) os0 (l0 ->>> final Hnot :: rs0) term1).
        one_step. eapply S_Last; crush.
      + instantiate (1:=C (b1 ++ << N k (t_app f v) es; l ->> pmap f (remove Nat.eq_dec k ks) :: os1'' >> :: x0 ++ [<< n1; os1' >>]) os0 (l0 ->>> final Hnot :: rs0) term1).
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
      fsame.
      destruct os1.
      * simpl in *.
        inv H4.
        {
        destruct b3.
        - assert (exists n m t', fstar n (t_app f' (t_app f0 t)) (l' ->>> 0 :: l0 ->>> 0 :: rs0) t' /\ fstar m (t_app (pmap_compose f' f0) t) (l' ->>> 0 :: l0 ->>> 0 :: rs0) t').
          {
            apply pmap_compose_comm.
            - inv WT; dtr. inv H1. wtbdist. inv H3. inv H15. inv H7. inv H15. eauto.
            - inv WT; dtr. inv H1. wtbdist. inv H3. inv H15. inv H7. inv H9. eauto.
            - inv WT; dtr. inv H1. wtbdist. inv H3. inv H15. inv H7. inv H15. eauto.
            - inv WT; dtr. inv H1. wtbdist. inv H3. inv H15. inv H7. inv H9. eauto.
            - apply to_value.
          }
          dtr. rename H into star1. rename H0 into star2.
          assert (Hnot' : not_fold_or_done (pmap f' (remove Nat.eq_dec n ks0))) by eauto.
          got.
          + instantiate (1:=C (b0 ++ [<< N n x1 e; os2 >>]) os0 (l' ->>> final _ :: l0 ->>> 0 :: rs0) term1).
            apply ex_intro with (3 + x).
            eapply Step.
            instantiate (1:=C (b0 ++ [<< N n (t_app f0 t) e; l' ->> pmap f' ks0 :: os2 >>]) os0 (l0 ->>> _ :: rs0) term1).
            eapply S_Last; crush.
            apply List.remove_In in H. assumption.
            eapply Step.
            instantiate (1:=C (b0 ++ [<< N n (t_app f' (t_app f0 t)) e; l' ->> pmap f' (remove Nat.eq_dec n ks0) :: os2 >>]) os0 (l0 ->>> final _ :: rs0) term1).
            eapply S_PMap; crush.
            instantiate (1:=Hnot); crush.
            eapply Step.
            eapply S_Last with (b:=b0 ++ [<< N n (t_app f' (t_app f0 t)) e; l' ->> pmap f' (remove Nat.eq_dec n ks0) :: os2 >>]); eauto.
            crush.
            apply List.remove_In in H. assumption.
            apply fstar_into_star_load with (b1:=b0) (k:=n) (b2:=[]) (es:=e) (os:=os2) (os0:=os0) (rs:=l' ->>> 0 :: l0 ->>> 0 :: rs0) (t0:=term1) in star1.
            simpl. instantiate (1:=Hnot'). simpl. auto.
          + instantiate (1:=C (b0 ++ [<< N n x1 e; os2 >>]) os0 (l' ->>> final _ :: l0 ->>> 0 :: rs0) term1).
            apply ex_intro with (2 + x0).
            eapply Step.
            eapply S_PMap; crush.
            eapply Step.
            eapply S_Last with (op:=pmap (pmap_compose f' f0) (remove Nat.eq_dec n ks0)); crush.
            apply List.remove_In in H. assumption.
            apply fstar_into_star_load with (b1:=b0) (k:=n) (b2:=[]) (es:=e) (os:=os2) (os0:=os0) (rs:=l' ->>> 0 :: l0 ->>> 0 :: rs0) (t0:=term1) in star2.
            simpl. instantiate (1:=Hnot'). simpl. auto.
          + crush.
        - destruct s.
          assert (exists n m t', fstar n (t_app f' (t_app f0 t)) (l0 ->>> 0 :: rs0) t' /\ fstar m (t_app (pmap_compose f' f0) t) (l0 ->>> 0 :: rs0) t').
          {
            apply pmap_compose_comm.
            - inv WT; dtr. inv H1. wtbdist. inv H3. inv H15. inv H7. inv H15. eauto.
            - inv WT; dtr. inv H1. wtbdist. inv H3. inv H15. inv H7. inv H9. eauto.
            - inv WT; dtr. inv H1. wtbdist. inv H3. inv H15. inv H7. inv H15. eauto.
            - inv WT; dtr. inv H1. wtbdist. inv H3. inv H15. inv H7. inv H9. eauto.
            - apply to_value.
          }
          dtr. rename H into star1. rename H0 into star2.
          assert (Hnot' : not_fold_or_done (pmap f' (remove Nat.eq_dec n ks0))) by eauto.
          got.
          + instantiate (1:=C (b0 ++ << N n x1 e; os2 >> :: << n0; l ++ [l' ->> pmap (pmap_compose f' f0) (remove Nat.eq_dec n ks0)] >> :: b3) os0 (l0 ->>> final _ :: rs0) term1).
            apply ex_intro with (4+x).
            eapply Step.
            instantiate (1:=C (b0 ++ << N n (t_app f0 t) e; l' ->> pmap f' ks0 :: os2 >> :: << n0; l ++ [l0 ->> pmap f0 (remove Nat.eq_dec n ks0)] >> :: b3) os0 rs0 term1).
            eapply S_Prop; crush.
            apply List.remove_In in H. assumption.
            eapply Step.
            instantiate (1:=C (b0 ++ << N n (t_app f' (t_app f0 t)) e; l' ->> pmap f' (remove Nat.eq_dec n ks0) :: os2 >> :: << n0; l ++ [l0 ->> pmap f0 (remove Nat.eq_dec n ks0)] >> :: b3) os0 rs0 term1).
            eapply S_PMap; crush.
            eapply Step.
            instantiate (1:=C (b0 ++ << N n (t_app f' (t_app f0 t)) e; os2 >> :: << n0; (l ++ [l0 ->> pmap f0 (remove Nat.eq_dec n ks0)]) ++ [l' ->> pmap f' (remove Nat.eq_dec n ks0)] >> :: b3) os0 rs0 term1).
            eapply S_Prop; crush.
            apply List.remove_In in H. assumption.
            eapply Step.
            assert (b0 ++ << N n (t_app f' (t_app f0 t)) e; os2 >> :: << n0; (l ++ [l0 ->> pmap f0 (remove Nat.eq_dec n ks0)]) ++ [l' ->> pmap f' (remove Nat.eq_dec n ks0)] >> :: b3 = (b0 ++ [<< N n (t_app f' (t_app f0 t)) e; os2 >>]) ++ << n0; l ++ l0 ->> pmap f0 (remove Nat.eq_dec n ks0) :: l' ->> pmap f' (remove Nat.eq_dec n ks0) :: [] >> :: b3) by crush.
            rewrite H.
            eapply S_FusePMap; crush.
            apply fstar_into_star_load with (b1:=b0) (k:=n) (b2:=<< n0; l ++ [l' ->> pmap (pmap_compose f' f0) (remove Nat.eq_dec n ks0)] >> :: b3) (es:=e) (os:=os2) (os0:=os0) (rs:=l0 ->>> 0 :: rs0) (t0:=term1) in star1.
            simpl. instantiate (1:=Hnot'). simpl. crush.
          + instantiate (1:=C (b0 ++ << N n x1 e; os2 >> :: << n0; l ++ [l' ->> pmap (pmap_compose f' f0) (remove Nat.eq_dec n ks0)] >> :: b3) os0 (l0 ->>> 0 :: rs0) term1).
            apply ex_intro with (2 + x0).
            eapply Step.
            instantiate (1:=C (b0 ++ << N n (t_app (pmap_compose f' f0) t) e; l' ->> pmap (pmap_compose f' f0) (remove Nat.eq_dec n ks0) :: os2 >> :: << n0; l >> :: b3) os0 (l0 ->>> 0 :: rs0) term1).
            eapply S_PMap; crush.
            eapply Step.
            instantiate (1:=C (b0 ++ << N n (t_app (pmap_compose f' f0) t) e; os2 >> :: << n0; l  ++ [l' ->> pmap (pmap_compose f' f0) (remove Nat.eq_dec n ks0)] >> :: b3) os0 (l0 ->>> 0 :: rs0) term1).
            eapply S_Prop; eauto. crush. apply List.remove_In in H. assumption.
            apply fstar_into_star_load with (b1:=b0) (k:=n) (b2:=<< n0; l ++ [l' ->> pmap (pmap_compose f' f0) (remove Nat.eq_dec n ks0)] >> :: b3) (es:=e) (os:=os2) (os0:=os0) (rs:=l0 ->>> 0 :: rs0) (t0:=term1) in star2.
            auto.
          + crush.
        }
      * inv H4.
        {
          got.
          * instantiate (1:= C (b0 ++ << N n (t_app f t) e; (l ->> pmap f (remove Nat.eq_dec n ks) :: os1) ++ l' ->> pmap (pmap_compose f' f0) ks0 :: os2 >> :: b3) os0 (l0 ->>> final _ :: rs0) term1).
            one_step. eapply S_FusePMap; crush.
          * instantiate (1:= C (b0 ++ << N n (t_app f t) e; l ->> pmap f (remove Nat.eq_dec n ks) :: os1 ++ l' ->> pmap (pmap_compose f' f0) ks0 :: os2 >> :: b3) os0 (l0 ->>> 0 :: rs0) term1).
            one_step. eapply S_PMap; crush.
          * crush.
        }
    (* First first *)
    + destruct H0. destruct H0. destruct H0.
      eapply target_unique with (b1:=b1) (b2:=b2) (b3:=x) (b4:=x0 ++ << N n t e; os1 ++ l0 ->> pmap f0 ks0 :: l' ->> pmap f' ks0 :: os2 >> :: x1) in H0; crush.
      inv H.
      eapply target_unique with (b1:=x ++ << N k v es; l ->> pmap f ks :: os1'' >> :: x0) (b2:=x1) (b3:=b0) (b4:=b3) in H1; eauto; crush.
      got.
      * instantiate (1:=C ((x ++ << N k (t_app f v) es; l ->> pmap f (remove Nat.eq_dec k ks) :: os1'' >> :: x0) ++ << N n t e; os1 ++ l' ->> pmap (pmap_compose f' f0) ks0 :: os2 >> :: b3) os0 (l0 ->>> 0 :: rs0) term1).
        one_step. eapply S_FusePMap; crush.
      * instantiate (1:=C (x ++ << N k (t_app f v) es; l ->> pmap f (remove Nat.eq_dec k ks) :: os1'' >> :: x0 ++ << N n t e; os1 ++ l' ->> pmap (pmap_compose f' f0) ks0 :: os2 >> :: b3) os0 (l0 ->>> 0 :: rs0) term1).
        one_step. eapply S_PMap; crush.
      * crush.
    (* First second *)
    + destruct H0. destruct H0. destruct H0.
      eapply target_unique with (b1:=b1) (b2:=b2) (b3:=x ++ << N n t e; os1 ++ l0 ->> pmap f0 ks0 :: l' ->> pmap f' ks0 :: os2 >> :: x0) (b4:=x1) in H0; eauto; crush.
      inv H.
      eapply target_unique with (b1:=x) (b2:=x0 ++ << N k v es; l ->> pmap f ks :: os1'' >> :: x1) (b3:=b0) (b4:=b3) in H1; eauto; crush.
      got.
      * instantiate (1:=C (b0 ++ << N n t e; os1 ++ l' ->> pmap (pmap_compose f' f0) ks0 :: os2 >> :: x0 ++ << N k (t_app f v) es; l ->> pmap f (remove Nat.eq_dec k ks) :: os1'' >> :: x1) os0 (l0 ->>> 0 :: rs0) term1).
        one_step. eapply S_FusePMap; crush.
      * instantiate (1:=C ((b0 ++ << N n t e; os1 ++ l' ->> pmap (pmap_compose f' f0) ks0 :: os2 >> :: x0) ++ << N k (t_app f v) es; l ->> pmap f (remove Nat.eq_dec k ks) :: os1'' >> :: x1) os0 (l0 ->>> 0 :: rs0) term1).
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

Axiom functional_extension : forall f f' rs t,
  (exists n m t', fstar n (t_app f t) rs t' /\ fstar m (t_app f' t) rs t') ->
  f = f'.

Lemma pmap_compose_assoc_apply : forall f f' f'' rs t,
  (exists T1 T2 ll, has_type empty ll f (Arrow T1 T2 false) false) ->
  (exists T1 T2 ll, has_type empty ll f' (Arrow T1 T2 false) false) ->
  (exists T1 T2 ll, has_type empty ll f'' (Arrow T1 T2 false) false) ->
  value f ->
  value f' ->
  value f'' ->
  value t ->
  (exists n v, fstar n (t_app f'' t) rs v /\ value v) ->
  exists n m t', fstar n (t_app (pmap_compose f (pmap_compose f' f'')) t) rs t' /\ fstar m (t_app (pmap_compose (pmap_compose f f') f'') t) rs t'.
Proof using.
  unfold pmap_compose; intros. destruct H6 as [n[v]]. destruct H6.
  exists (S (S n)), (S (S n)), (t_app f (t_app f' v)).
  split.
  - eapply FStep.
    eapply F_App; auto.
    rewrite rewrite_e_subst.
    replace (#["x":=t]f) with f.
    rewrite rewrite_e_subst.
    simpl.
    eapply FStep.
    eapply F_App2; auto.
    rewrite rewrite_e_subst.
    replace (#["x":=t]f') with f'.
    rewrite rewrite_e_subst.
    replace (#["x":=t]f'') with f''.
    simpl.
    apply fstar_app2; auto.
    apply fstar_app2; auto.
    assert (~ (appears_free_in "x" f'')) by (dtr; eapply typable_empty__closed; eauto).
    eapply not_afi_subst in H8; eauto.
    assert (~ (appears_free_in "x" f')) by (dtr; eapply typable_empty__closed; eauto).
    eapply not_afi_subst in H8; eauto.
    assert (~ (appears_free_in "x" f)) by (dtr; eapply typable_empty__closed; eauto).
    eapply not_afi_subst in H8; eauto.
  - eapply FStep.
    eapply F_App; auto.
    rewrite rewrite_e_subst.
    rewrite rewrite_e_subst.
    replace (#["x":=t]f'') with f''.
    simpl.
    replace (S n) with (n + 1).
    eapply fstar_trans.
    apply fstar_app2; auto. instantiate (1:=v). auto.
    eapply FStep. eapply F_App; auto.
    simpl.
    replace (#["x":=v]f) with f.
    replace (#["x":=v]f') with f'.
    auto.
    assert (~ (appears_free_in "x" f')) by (dtr; eapply typable_empty__closed; eauto).
    eapply not_afi_subst in H8; eauto.
    assert (~ (appears_free_in "x" f)) by (dtr; eapply typable_empty__closed; eauto).
    eapply not_afi_subst in H8; eauto.
    crush.
    assert (~ (appears_free_in "x" f'')) by (dtr; eapply typable_empty__closed; eauto).
    eapply not_afi_subst in H8; eauto.
Qed.

Lemma pmap_compose_assoc : forall f f' f'' (rs:rstream),
  (exists ll, has_type empty ll f (Arrow Result Result false) false) ->
  (exists ll, has_type empty ll f' (Arrow Result Result false) false) ->
  (exists ll, has_type empty ll f'' (Arrow Result Result false) false) ->
  value f ->
  value f' ->
  value f'' ->
  pmap_compose f (pmap_compose f' f'') = pmap_compose (pmap_compose f f') f''.
Proof using.
  intros.
  eapply functional_extension.
  apply pmap_compose_assoc_apply; eauto.
  instantiate (1:=rs). apply to_value.
Qed.

Lemma lc_fusepmap :
  forall cx cy cz n b1 b2 os os1 os2 rs term0 f f' ks l l' H,
  well_typed cx ->
  cx = C (b1 ++ << n; os1 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os2 >> :: b2) os rs term0 ->
  cy = C (b1 ++ << n; os1 ++ l' ->> pmap (pmap_compose f' f) ks :: os2 >> :: b2) os (l ->>> (@final (pmap f ks)) H :: rs) term0 ->
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
  assert (H2 : C (b1 ++ << n; os1 ++ l' ->> pmap (pmap_compose f' f) ks :: os2 >> :: b2) os (l ->>> final Hnot :: rs) term0 = cy) by auto.
  inversion cxcz; ssame; try solve [subst; eauto].
  (* S_Empty *)
  - destruct b1; crush.
  (* S_Add *)
  - ssame.
    got.
    * instantiate (1:=C (<< N k v t_ks_nil; [] >> :: b1 ++ << n; os1 ++ l' ->> pmap (pmap_compose f' f) ks :: os2 >> :: b2) os' (l0 ->>> final _ :: l ->>> final Hnot :: rs0) term1).
      one_step. eapply S_Add; crush.
    * instantiate (1:=C (<< N k v t_ks_nil; [] >> :: b1 ++ << n; os1 ++ l' ->> pmap (pmap_compose f' f) ks :: os2 >> :: b2) os' (l ->>> final _ :: l0 ->>> k :: rs0) term1).
      one_step. apply S_FusePMap with (b:=<< N k v t_ks_nil; [] >> :: b1 ++ << n; os1 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os2 >> :: b2) (b1:=<< N k v t_ks_nil; [] >> :: b1); crush.
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
        * instantiate (1:=C (b1 ++ [<< n1; os3 >>]) os0 (l' ->>> final _ :: l0 ->>> 0 :: rs0) term1).
          one_step. eapply S_Last; crush.
        * instantiate (1:=C (b1 ++ [<< n1; os3 >>]) os0 (l' ->>> final _ :: l0 ->>> 0 :: rs0) term1).
          one_step. eapply S_Last; crush.
        * crush.
      (* os2 != [] *)
      + inv H6.
        got.
        * instantiate (1:=C (b1 ++ [<< n1; os2 ++ l' ->> pmap (pmap_compose f' f) ks :: os3 >>]) os0 (l0 ->>> final Hnot' :: l ->>> final Hnot :: rs0) term1).
          one_step. eapply S_Last; crush.
        * instantiate (1:=C (b1 ++ [<< n1; os2 ++ l' ->> pmap (pmap_compose f' f) ks :: os3 >>]) os0 (l ->>> final Hnot :: l0 ->>> final Hnot' :: rs0) term1).
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
      + instantiate (1:=C ((b2 ++ << n; os2 ++ l' ->> pmap (pmap_compose f' f) ks :: os3 >> :: x0) ++ [<< n1; os1' >>]) os0 (l0 ->>> final H3 :: l ->>> final Hnot :: rs0) term1).
        one_step. eapply S_Last; crush.
      + instantiate (1:=C (b2 ++ << n; os2 ++ l' ->> pmap (pmap_compose f' f) ks :: os3 >> :: x0 ++ [<< n1; os1' >>]) os0 (l ->>> final Hnot :: l0 ->>> final H3 :: rs0) term1).
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
          + fsame. inv H1. inv H4. crush.
          (* First first *)
          + destruct H0; destruct H0; destruct H0.
            destruct x0.
            (* First's second is second's first *)
            * simpl in *.
              inv H3. apply List.app_inv_head in H4; inv H4.
              apply op_unique with (n:=N k' v' e0) (os1:=os1) (os2:=l' ->> pmap f' ks :: os2) (os3:=x) (os4:=l0 ->> pmap f0 ks0 :: x1) (os0:=os0) (rs0:=rs0) (t0:=term1) (b:=b3 ++ << N k' v' e0; os1 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os2 >> :: b4) (b1:=b3) (b2:=b4) (os:=os1 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os2) in H0; crush.
              inv H2. inv H.
              inv H3.
              apply op_unique with (n:=N k' v' e0) (os1:=x ++ [l ->> pmap f ks0]) (os2:=x1) (os3:=os3) (os4:=l'0 ->> pmap f'0 ks0 :: os4) (os0:=os0) (rs0:=rs0) (t0:=term1) (b:=b3 ++ << N k' v' e0; x ++ l ->> pmap f ks0 :: l0 ->> pmap f0 ks0 :: x1 >> :: b4) (b1:=b3) (b2:=b4) (os:=x ++ l ->> pmap f ks0 :: l0 ->> pmap f0 ks0 :: x1) in H5; crush.
              {
              got.
              - instantiate (1:=C (b3 ++ << N k' v' e0; x ++ l'0 ->> pmap (pmap_compose f'0 (pmap_compose f0 f)) ks0 :: os4 >> :: b4) os0 (l0 ->>> final _ :: l ->>> 0 :: rs0) term1).
                one_step. eapply S_FusePMap; crush.
              - instantiate (1:=C (b3 ++ << N k' v' e0; x ++ l'0 ->> pmap (pmap_compose (pmap_compose f'0 f0) f) ks0 :: os4 >> :: b4) os0 (l ->>> final _ :: l0 ->>> 0 :: rs0) term1).
                one_step. eapply S_FusePMap; crush.
              - rewrite pmap_compose_assoc; eauto.
                + inv WT; dtr. inv H1. wtbdist. inv H2. wtosdist. inv H3. inv H8. inv H7. inv H17. eauto.
                + inv WT; dtr. inv H1. wtbdist. inv H2. wtosdist. inv H3. inv H8. inv H16. eauto.
                + inv WT; dtr. inv H1. wtbdist. inv H2. wtosdist. inv H3. inv H14. eauto.
                + inv WT; dtr. inv H1. wtbdist. inv H2. wtosdist. inv H3. inv H8. inv H7. inv H17. eauto.
                + inv WT; dtr. inv H1. wtbdist. inv H2. wtosdist. inv H3. inv H8. inv H16. eauto.
                + inv WT; dtr. inv H1. wtbdist. inv H2. wtosdist. inv H3. inv H14. eauto.
              }
            (* No overlap *)
            * simpl in *.
              inv H3. apply List.app_inv_head in H4; inv H.
              apply op_unique with (n:=N k' v' e0) (os1:=os1) (os2:=l' ->> pmap f' ks :: os2) (os3:=x) (os4:=l1 :: x0 ++ l0 ->> pmap f0 ks0 :: x1) (os0:=os0) (rs0:=rs0) (t0:=term1) (b:=b3 ++ << N k' v' e0; os1 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os2 >> :: b4) (b1:=b3) (b2:=b4) (os:=os1 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os2) in H0; crush.
              inv H4.
              apply op_unique with (n:=N k' v' e0) (os1:=x ++ l ->> pmap f ks :: l' ->> pmap f' ks :: x0) (os2:=x1) (os3:=os3) (os4:=l'0 ->> pmap f'0 ks0 :: os4) (os0:=os0) (rs0:=rs0) (t0:=term1) (b:=b3 ++ << N k' v' e0; x ++ l ->> pmap f ks :: l' ->> pmap f' ks :: x0 ++ l0 ->> pmap f0 ks0 :: x1 >> :: b4) (b1:=b3) (b2:=b4) (os:=x ++ l ->> pmap f ks :: l' ->> pmap f' ks :: x0 ++ l0 ->> pmap f0 ks0 :: x1) in H1; crush.
              {
              got.
              - instantiate (1:=C (b3 ++ << N k' v' e0; (x ++ l' ->> pmap (pmap_compose f' f) ks :: x0) ++ l'0 ->> pmap (pmap_compose f'0 f0) ks0 :: os4 >> :: b4) os0 (l0 ->>> final Hnot' :: l ->>> 0 :: rs0) term1).
                one_step. eapply S_FusePMap; crush.
              - instantiate (1:=C (b3 ++ << N k' v' e0; x ++ l' ->> pmap (pmap_compose f' f) ks :: x0 ++ l'0 ->> pmap (pmap_compose f'0 f0) ks0 :: os4 >> :: b4) os0 (l ->>> final _ :: l0 ->>> 0 :: rs0) term1).
                one_step. eapply S_FusePMap; crush.
              - crush.
              }
          (* First second *)
          + destruct H0; destruct H0; destruct H0.
            inv H3. apply List.app_inv_head in H4; inv H4.
            destruct x0.
            (* First's second is second's first *)
            * simpl in *.
              eapply op_unique with (n:=N k' v' e0) (os1:=os1) (os2:=l' ->> pmap f' ks :: os2) (os3:=x ++ [l0 ->> pmap f0 ks0]) (os4:=x1) (os0:=os0) (rs0:=rs0) (t0:=term1) (b:=b3 ++ << N k' v' e0; os1 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os2 >> :: b4) (b1:=b3) (b2:=b4) (os:=os1 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os2) in H0; crush.
              inv H2.
              apply op_unique with (n:=N k' v' e0) (os1:=x) (os2:=l ->> pmap f ks :: l' ->> pmap f' ks :: os2) (os3:=os3) (os4:=l'0 ->> pmap f'0 ks0 :: os4) (os0:=os0) (rs0:=rs0) (t0:=term1) (b:=b3 ++ << N k' v' e0; x ++ l0 ->> pmap f0 ks0 :: l ->> pmap f ks :: l' ->> pmap f' ks :: os2 >> :: b4) (b1:=b3) (b2:=b4) (os:=x ++ l0 ->> pmap f0 ks0 :: l ->> pmap f ks :: l' ->> pmap f' ks :: os2) in H5; crush.
              inv H1.
              {
              got.
              - instantiate (1:=C (b3 ++ << N k' v' e0; os3 ++ l' ->> pmap (pmap_compose (pmap_compose f' f'0) f0) ks0 :: os2 >> :: b4) os0 (l0 ->>> final _ :: l'0 ->>> 0 :: rs0) term1).
                one_step. eapply S_FusePMap; crush.
              - instantiate (1:=C (b3 ++ << N k' v' e0; os3 ++ l' ->> pmap (pmap_compose f' (pmap_compose f'0 f0)) ks0 :: os2 >> :: b4) os0 (l'0 ->>> final _ :: l0 ->>> 0 :: rs0) term1).
                one_step. eapply S_FusePMap; crush.
              - rewrite pmap_compose_assoc; eauto.
                + inv WT; dtr. inv H2. wtbdist. inv H3. wtosdist. inv H4. inv H9. inv H8. inv H18. eauto.
                + inv WT; dtr. inv H2. wtbdist. inv H3. wtosdist. inv H4. inv H9. inv H17. eauto.
                + inv WT; dtr. inv H2. wtbdist. inv H3. wtosdist. inv H4. inv H15. eauto.
                + inv WT; dtr. inv H2. wtbdist. inv H3. wtosdist. inv H4. inv H9. inv H8. inv H18. eauto.
                + inv WT; dtr. inv H2. wtbdist. inv H3. wtosdist. inv H4. inv H9. inv H17. eauto.
                + inv WT; dtr. inv H2. wtbdist. inv H3. wtosdist. inv H4. inv H15. eauto.
              }
            (* No overlap *)
            * simpl in *.
              eapply op_unique with (n:=N k' v' e0) (os1:=os1) (os2:=l' ->> pmap f' ks :: os2) (os3:=x ++ l0 ->> pmap f0 ks0 :: l1 :: x0) (os4:=x1) (os0:=os0) (rs0:=rs0) (t0:=term1) (b:=b3 ++ << N k' v' e0; os1 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os2 >> :: b4) (b1:=b3) (b2:=b4) (os:=os1 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os2) in H0; crush.
              inv H2.
              apply op_unique with (n:=N k' v' e0) (os1:=x) (os2:=l1 :: x0 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os2) (os3:=os3) (os4:=l'0 ->> pmap f'0 ks0 :: os4) (os0:=os0) (rs0:=rs0) (t0:=term1) (b:=b3 ++ << N k' v' e0; x ++ l0 ->> pmap f0 ks0 :: l1 :: x0 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os2 >> :: b4) (b1:=b3) (b2:=b4) (os:=x ++ l0 ->> pmap f0 ks0 :: l1 :: x0 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os2) in H5; crush.
              {
              got.
              - instantiate (1:=C (b3 ++ << N k' v' e0; os3 ++ l'0 ->> pmap (pmap_compose f'0 f0) ks0 :: x0 ++ l' ->> pmap (pmap_compose f' f) ks :: os2 >> :: b4) os0 (l0 ->>> final _ :: l ->>> 0 :: rs0) term1).
                one_step. eapply S_FusePMap; crush.
              - instantiate (1:=C (b3 ++ << N k' v' e0; (os3 ++ l'0 ->> pmap (pmap_compose f'0 f0) ks0 :: x0) ++ l' ->> pmap (pmap_compose f' f) ks :: os2 >> :: b4) os0 (l ->>> final Hnot :: l0 ->>> 0 :: rs0) term1).
                one_step. eapply S_FusePMap; crush.
              - crush.
              }
        }
      (* First first *)
      + destruct H0; destruct H0; destruct H0.
        apply target_unique with (os:=os1 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os2) (k:=k) (v:=v) (b1:=b1) (b2:=b2) (b3:=x) (b4:=x0 ++ << N k' v' e0; os3 ++ l0 ->> pmap f0 ks0 :: l'0 ->> pmap f'0 ks0 :: os4 >> :: x1) (os0:=os0) (rs0:=rs0) (t0:=term1) (b:=b1 ++ << N k v e; os1 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os2 >> :: b2) in H0; crush.
        inv H3.
        apply target_unique with (os:=os3 ++ l0 ->> pmap f0 ks0 :: l'0 ->> pmap f'0 ks0 :: os4) (k:=k') (v:=v') (b1:=x ++ << N k v e; os1 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os2 >> :: x0) (b2:=x1) (b3:=b3) (b4:=b4) (os0:=os0) (rs0:=rs0) (t0:=term1) (b:=x ++ << N k v e; os1 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os2 >> :: x0 ++ << N k' v' e0; os3 ++ l0 ->> pmap f0 ks0 :: l'0 ->> pmap f'0 ks0 :: os4 >> :: x1) in H1; crush.
        got.
        * instantiate (1:=C ((x ++ << N k v e; os1 ++ l' ->> pmap (pmap_compose f' f) ks :: os2 >> :: x0) ++ << N k' v' e0; os3 ++ l'0 ->> pmap (pmap_compose f'0 f0) ks0 :: os4 >> :: b4) os0 (l0 ->>> 0 :: l ->>> 0 :: rs0) term1).
          one_step. eapply S_FusePMap; crush.
        * instantiate (1:=C (x ++ << N k v e; os1 ++ l' ->> pmap (pmap_compose f' f) ks :: os2 >> :: x0 ++ << N k' v' e0; os3 ++ l'0 ->> pmap (pmap_compose f'0 f0) ks0 :: os4 >> :: b4) os0 (l ->>> 0 :: l0 ->>> 0 :: rs0) term1).
          one_step. eapply S_FusePMap; crush.
        * crush.
      (* First second *)
      + destruct H0; destruct H0; destruct H0.
        apply target_unique with (es:=e) (os:=os1 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os2) (k:=k) (v:=v) (b1:=b1) (b2:=b2) (b3:=x ++ << N k' v' e0; os3 ++ l0 ->> pmap f0 ks0 :: l'0 ->> pmap f'0 ks0 :: os4 >> :: x0) (b4:=x1) (os0:=os0) (rs0:=rs0) (t0:=term1) (b:=b1 ++ << N k v e; os1 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os2 >> :: b2) in H0; crush.
        inv H3.
        apply target_unique with (os:=os3 ++ l0 ->> pmap f0 ks0 :: l'0 ->> pmap f'0 ks0 :: os4) (k:=k') (v:=v') (b1:=x) (b2:=x0 ++ << N k v e; os1 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os2 >> :: x1) (b3:=b3) (b4:=b4) (os0:=os0) (rs0:=rs0) (t0:=term1) (b:=x ++ << N k' v' e0; os3 ++ l0 ->> pmap f0 ks0 :: l'0 ->> pmap f'0 ks0 :: os4 >> :: x0 ++ << N k v e; os1 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os2 >> :: x1) in H1; crush.
        got.
        * instantiate (1:=C (b3 ++ << N k' v' e0; os3 ++ l'0 ->> pmap (pmap_compose f'0 f0) ks0 :: os4 >> :: x0 ++ << N k v e; os1 ++ l' ->> pmap (pmap_compose f' f) ks :: os2 >> :: x1) os0 (l0 ->>> 0 :: l ->>> 0 :: rs0) term1).
          one_step. eapply S_FusePMap; crush.
        * instantiate (1:=C ((b3 ++ << N k' v' e0; os3 ++ l'0 ->> pmap (pmap_compose f'0 f0) ks0 :: os4 >> :: x0) ++ << N k v e; os1 ++ l' ->> pmap (pmap_compose f' f) ks :: os2 >> :: x1) os0 (l ->>> 0 :: l0 ->>> 0 :: rs0) term1).
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
      + instantiate (1:=C [<< N k0 v t_ks_nil; [] >>; << n1; os1' >>] os' (l0 ->>> _ :: l ->>> final _ :: rs0) term1).
        one_step; eapply S_Add with (b:=[<< n1; os1' >>]); crush.
      + instantiate (1:=C [<< N k0 v t_ks_nil; [] >>; << n1; os1' >>] os' (l ->>> final Hnot :: l0 ->>> k0 :: rs0) term1).
        one_step; eapply S_Last with (b1:=[<< N k0 v t_ks_nil; [] >>]); crush.
      + crush.
    (* b1 != [] *)
    - simpl in *. inv H7. eapply ex_intro. eapply ex_intro.
      split; try split.
      + instantiate (1:=C (<< N k0 v t_ks_nil; [] >> :: s :: b1 ++ [<< n1; os1' >>]) os' (l0 ->>> k0 :: l ->>> final Hnot :: rs0) term1).
        one_step; eapply S_Add; crush.
      + instantiate (1:=C (<< N k0 v t_ks_nil; [] >> :: s :: b1 ++ [<< n1; os1' >>]) os' (l ->>> final Hnot :: l0 ->>> k0 :: rs0) term1).
        one_step; eapply S_Last with (b1:=<< N k0 v t_ks_nil; [] >> :: s :: b1); crush.
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
  cy = C (<< N k v t_ks_nil; [] >> :: b) os' (l ->>> (@final (add k v)) Hnot :: rs) term0 ->
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

(* we are only interested in reductions that terminate *)
Hypothesis to_dry : forall c, exists n c', c -->*[n] c' /\ dry c'.

(* noetharian induction hypothesis,
   check that it's only used starting from smaller structures relative to the starting configurations *)
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

Hint Resolve well_typed_preservation'.

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
      destruct (@to_dry cy); dtr.
      exists x, x0. destruct x0.
      split; [eauto|eapply dry_normal_form; eauto].
    }
    destruct H6 as [n' H']. destruct H' as [cw cycw]. destruct cycw as [cycw nfcw].
    assert (exists n cw', cy'' -->*[n] cw' /\ normal_form cw').
    {
      destruct (@to_dry cy''); dtr.
      exists x, x0. destruct x0.
      split; [eauto|eapply dry_normal_form; eauto].
    }
    destruct H6 as [n'' H']. destruct H' as [cw' cycw']. destruct cycw' as [cycw' nfcw'].
    assert (exists n cv, cz'' -->*[n] cv /\ normal_form cv).
    {
      destruct (@to_dry cz''); dtr.
      exists x, x0. destruct x0.
      split; [eauto|eapply dry_normal_form; eauto].
    }
    destruct H6 as [n''' H']. destruct H' as [cv cycv]. destruct cycv as [cycv nfcv].
    assert (exists n cv', cz -->*[n] cv' /\ normal_form cv').
    {
      destruct (@to_dry cz); dtr.
      exists x, x0. destruct x0.
      split; [eauto|eapply dry_normal_form; eauto].
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

Lemma dry_goes_nowhere : forall c c',
  well_typed c ->
  dry c ->
  (exists n, c -->*[n] c') ->
  c = c'.
Proof using.
  intros; dtr.
  destruct c as [b os rs t].
  remember (C b os rs t) as c.
  eapply dry_normal_form in H0; eauto.
  unfold normal_form in H0.
  destruct x.
  - eauto.
  - exfalso. apply H0. inv H1. eauto.
Qed.
Hint Resolve dry_goes_nowhere.

Definition init (b : backend) (t : term) := C b [] [] t.

Theorem determinism : forall b t i i' i'',
  i = init b t ->
  well_typed i ->
  (exists n, i -->*[n] i') ->
  (exists m, i -->*[m] i'') ->
  dry i' ->
  dry i'' ->
  i' == i''.
Proof using.
  intros.
  copy H1.
  apply confluence with (cy:=i'') in H1; auto.
  dtr.
  assert (i'' = x1) by eauto.
  assert (i' = x2) by eauto.
  subst.
  apply cequiv_symmetric; auto.
Qed.
