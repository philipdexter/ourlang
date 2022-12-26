
Require Import Maps.
Require NMaps.

From Coq Require Import Lists.List.
Import ListNotations.
Require Import CpdtTactics.

Require Import SyntaxRuntime.

Local Set Warnings "-implicit-core-hint-db".

Ltac inv H := inversion H; subst; clear H.

Definition context := partial_map type.
Definition lcontext := NMaps.partial_map type.

Definition nempty {A : Type} := (@NMaps.empty A).
Notation "x '#->' v ';' m" := (NMaps.update m x v) (at level 100, v at next level, right associativity).

(* Fig 13: Type system *)

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
Axiom fresh_keys : forall (k:key) k', k <> k'.
Hint Immediate fresh_keys.

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
