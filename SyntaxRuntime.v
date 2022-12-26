
Require Import Maps.
Require NMaps.

From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
Import ListNotations.

Set Implicit Arguments.
Local Set Warnings "-implicit-core-hint-db".

Ltac inv H := inversion H; subst; clear H.

Definition key := nat.
Definition label := nat.
Definition keyset := (list key).
Definition result := nat.

(* Fig 6: Abstract Syntax and Fig 8: Runtime Definitions *)

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

Lemma value_dec : forall t, value t \/ ~ value t.
Proof using.
  induction t; try solve [right; intro; inv H1]; try solve [right; intro; inv H]; try solve [left; eauto].
  - destruct IHt1; destruct IHt2; try solve [eauto]; right; intro; inv H1; eauto.
  - destruct IHt1; destruct IHt2; destruct IHt3; try solve [eauto]; right; intro; inv H2; eauto.
Qed.

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

Definition payload := term.
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
