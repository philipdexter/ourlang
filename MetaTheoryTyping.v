
Require Import CpdtTactics.
From Coq Require Import Arith.PeanoNat.
From Coq Require Import Bool.Bool.
From Coq Require Import Lists.List.
Import ListNotations.

Require Import Maps.
Require Import SyntaxRuntime.
Require Import Typing.
Require Import OperationalSemantics.
Require Import MetaTheoryBase.

Local Set Warnings "-implicit-core-hint-db".
Local Set Warnings "-deprecated-focus".

Ltac inv H := inversion H; subst; clear H.

Ltac narrow_terms := try (match goal with
                          | [H : value _ |- _] => inv H
                          end);
                     try (match goal with
                          | [H : empty _ = Some _ |- _] => inv H
                          end);
                     try solve [match goal with
                                | [H : has_type _ _ _ _ _ |- _] => inv H
                                end].
Ltac ssame := subst; match goal with
                     | [ H : C _ _ _ _ = C _ _ _ _ |- _ ] => inversion H
                     end; subst.
Ltac ssame' := subst; match goal with
                      | [ H : C _ _ _ _ = C _ _ _ _ |- _ ] => inv H
                      end.

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
      destruct H1. eauto.
    + remember H0. clear Heqn. eapply IHt in H0. destruct H0. eauto. easy_wt.
  - destruct (value_dec t1).
    + destruct (value_dec t2).
      * {
        destruct (value_dec t3).
        - eauto.
        - remember H2. clear Heqn. eapply IHt3 in H2. destruct H2. eauto. easy_wt.
        }
      * remember H1. clear Heqn. eapply IHt2 in H1. destruct H1. eauto. easy_wt.
    + remember H0. clear Heqn. eapply IHt1 in H0. destruct H0. eauto. easy_wt.
  - destruct (value_dec t1).
    + destruct (value_dec t2).
      * eauto.
      * remember H1. clear Heqn. eapply IHt2 in H1. destruct H1. eauto. easy_wt.
    + remember H0. clear Heqn. eapply IHt1 in H0. destruct H0. eauto. easy_wt.
  - destruct (value_dec t1).
    + destruct (value_dec t2).
      * eauto.
      * remember H1. clear Heqn. eapply IHt2 in H1. destruct H1. eauto. easy_wt.
    + remember H0. clear Heqn. eapply IHt1 in H0. destruct H0. eauto. easy_wt.
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
  destruct op; subst. rename k0 into l0.
  - destruct (List.in_dec Nat.eq_dec k l0).
    + eapply ex_intro; eapply S_PMap; eauto.
    + destruct b2.
      * eapply ex_intro; eapply S_Last; eauto.
      * destruct s. eapply ex_intro; eapply S_Prop; eauto; crush.
  - destruct b2.
    + eapply ex_intro; eapply S_Last; eauto.
    + destruct s. eapply ex_intro; eapply S_Prop; eauto; crush.
  - rename k0 into l0.
    destruct (List.in_dec Nat.eq_dec k l0).
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
  - inv H. assert (l0 <> l) by (apply fresh_labels). constructor.
    replace ((l0#->T';ll) l) with (ll l); auto.
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
  repeat (rewrite ll_extract_ostream in H). rename l0 into n.
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
  repeat (rewrite ll_extract_ostream). rename l0 into n.
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
  replace (l0 #-> Result; l #-> T; ll) with (l#->T;l0 #-> Result;ll); eauto; apply NMaps.update_permute; apply fresh_labels.
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

(* Lemma 6.2 *)
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
            destruct (value_dec p).
            - left.
              constructor; eauto.
              constructor; eauto.
              inv H0; eauto.
            - right.
              copy WT.
              eapply load_exists with (os:=[]) (b1:=[]) (b2:=b) (k:=k) (rs0:=rs) (t:=p) (es:=e) in H2; eauto.
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
            - eapply ex_intro; eapply S_SwapReads with (f':=f'); eauto; crush.
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

Lemma backend_types_app : forall b b' ll,
  backend_types (b ++ b') ll = backend_types b' (backend_types b ll).
Proof using.
  induction b; intros; auto.
  destruct a; destruct n; simpl.
  rewrite IHb. rewrite ll_swap_ostream_backend. auto.
Qed.

Lemma ostream_types_app : forall os os' ll,
  ostream_types (os ++ os') ll = ostream_types os' (ostream_types os ll).
Proof using.
  induction os; intros; auto.
  destruct a; simpl.
  rewrite IHos. crush.
Qed.

Lemma wt_to_wt6 : forall b1 n os l l' ks os' b2 ll ll' f t f' t' ks',
  not (lappears_free_in l f') ->
  not (lappears_free_in l t') ->
  well_typed_backend ll ll' (b1 ++ << n; os ++ l ->> pfold f t ks :: l' ->> pfold f' t' ks' :: os' >> :: b2) ->
  exists ll'', well_typed_backend ll ll'' (b1 ++ << n; os ++ l' ->> pfold f' t' ks' :: l ->> pfold f t ks :: os' >> :: b2).
Proof using.
  intros.
  apply well_typed_backend_dist' in H1; dtr.
  inv H2.
  apply well_typed_ostream_dist' in H10; dtr.
  inv H3.
  inv H10.
  inv H14.
  inv H13.
  exi; eapply well_typed_backend_dist.
  - instantiate (2:=x). instantiate (1:=backend_types b1 x). copy H1; apply wt_to_backend_types in H1; subst. eauto.
  - econstructor; simpl in *. Focus 4.
    + copy H11; apply wt_to_backend_types in H11; subst. eauto.
    + wtbt. eauto.
    + wtbt. eauto.
    + eapply well_typed_ostream_dist.
      * wtbt. wtost'. eauto.
      * {
        constructor.
        - constructor.
          + simpl in *. replace (l #-> Result; l' #-> Result; x0) with (l' #-> Result; l #-> Result; x0).
            eauto.
            apply NMaps.update_permute. apply fresh_labels.
          + eauto.
        - constructor; eauto.
          + apply lcontext_invariance with (ll:=(l #-> Result;x0)); auto.
            crush.
            rewrite NMaps.update_neq; eauto.
          + apply lcontext_invariance with (ll:=(l #-> Result;x0)); auto.
            crush.
            rewrite NMaps.update_neq; eauto.
        }
Qed.
Hint Resolve wt_to_wt6.

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

Ltac inv_type := try (match goal with | [H : config_has_type _ _ _ |- _] => inv H end);
                      match goal with | [H : has_type _ _ _ _ _ |- _] => inv H end.

Hint Immediate NMaps.update_eq.

Lemma type_in_rstream' : forall rs l v,
  In (l ->>> v) rs ->
  (rstream_types rs) l = Some Result.
Proof using.
  induction rs; intros; crush.
  - destruct a. destruct (Nat.eq_dec l l0); subst.
    + apply NMaps.update_eq.
    + rewrite NMaps.update_neq; auto. apply IHrs with v; auto.
Qed.

Lemma in_rstream_labels : forall rs l v,
  In (l ->>> v) rs ->
  In l (rstream_labels rs).
Proof using.
  induction rs; intros.
  - auto.
  - destruct a. simpl. rename l0 into n. destruct (Nat.eq_dec n l).
    + auto.
    + inv H; eauto.
      inv H0. eauto.
Qed.

(* Lemma 6.1 *)
Theorem preservation' : forall t b os0 rs os t' T E,
  config_has_type (C b os0 rs t) T E ->
  distinct (List.concat [backend_labels b; ostream_labels os0; rstream_labels rs]) ->
  FRf t rs ==> FRt t' os ->
  exists E', has_type empty (ostream_types os (ostream_types os0 (backend_types b (rstream_types rs)))) t' T E' /\
        (match E with
         | false => E' = false
         | _ => True
         end).
Proof using.
  induction t; intros b os0 rs os t' T E H Hdistinct H0; try solve [inv H0]; inv H; rename H7 into Hwtb; rename H8 into Hwttos; rename H9 into H.
  - inv H0.
    + exists E. split; [|destruct E; auto]; simpl in *.
      inv H. inv H5.
      assert (E3 = false) by (eapply value_no_emit; eauto); subst.
      replace (E1 || false || false) with E1.
      eapply substitution_preserves_typing; wtbt; wttost; eauto.
      destruct E1; auto.
    + inv H.
      eapply IHt1 with (T:=Arrow T11 T E1) (E:=E2) in H2; eauto; dtr.
      exists (E1 || x || E3). split.
      * {
        econstructor.
        - instantiate (1:=T11).
          eauto.
        - wtbt; wttost; auto.
        }
      * destruct E1; destruct E2; destruct E3; crush.
    + inv H.
      eapply IHt2 with (T:=T11) (E:=E3) in H7; eauto; dtr.
      exists (E1 || E2 || x). split.
      * eauto.
      * destruct E1; destruct E2; destruct E3; crush.
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
    + inv H. exists E. inv H4. simpl. wtbt; wttost.
      assert (T = Result).
      { assert (distinct (List.concat [backend_labels b; ostream_labels os0; rstream_labels rs])) by eauto.
        apply lcontext_in_or_os in H5; destruct H5; dtr.
        - simpl in *. apply List.in_split in H0; dtr; subst.
          exfalso. rewrite ostream_labels_dist in H. simpl in *.
          replace (backend_labels b ++ (ostream_labels x0 ++ l :: ostream_labels x1) ++ rstream_labels rs ++ [])
                  with ((backend_labels b ++ ostream_labels x0) ++ l :: ostream_labels x1 ++ rstream_labels rs ++ []) in H by crush.
          apply distinct_rotate_rev in H. apply distinct_remove in H; dtr.
          apply H0. apply List.in_or_app. right. apply List.in_or_app. right. apply in_rstream_labels in H2. crush.
        - apply lcontext_in_or_b in H0; destruct H0; dtr.
          + simpl in *. apply List.in_split in H1; dtr; subst; destruct x0; simpl in *; subst.
            exfalso. rewrite backend_labels_dist in H; simpl in *.
            unfold backend_labels at 2 in H; simpl in *. rewrite ostream_labels_dist in H; simpl in *.
            replace ((backend_labels x ++
          (ostream_labels x3 ++ l :: ostream_labels x4) ++ List.concat (map (fun s : station => ostream_labels (get_ostream s)) x1)) ++
         ostream_labels os0 ++ rstream_labels rs ++ []) with ((backend_labels x ++
          ostream_labels x3) ++ l :: ostream_labels x4 ++ List.concat (map (fun s : station => ostream_labels (get_ostream s)) x1) ++
         ostream_labels os0 ++ rstream_labels rs ++ []) in H by crush.
            apply distinct_rotate_rev in H. apply distinct_remove in H; dtr.
          apply H0. apply List.in_or_app. right. apply List.in_or_app. right. apply in_rstream_labels in H2. crush.
          + apply type_in_rstream' in H2. crush.
      }
      subst; split; eauto.
    + inv H.
      eapply IHt in H2; eauto; dtr.
      exists x. split; eauto.
  - inv H0.
    + inv H. exists false. split; simpl; eauto.
    + inv H.
      eapply IHt1 in H2; eauto; dtr.
      exists true. split; wtbt; wttost; eauto.
    + inv H.
      eapply IHt2 in H9; eauto; dtr.
      exists true. split; wtbt; wttost; eauto.
    + inv H.
      eapply IHt3 in H10; eauto; dtr.
      exists true. split; wtbt; wttost; eauto.
  - inv H0.
    + inv H. exists false. split; simpl; eauto.
    + inv H.
      eapply IHt1 in H2; eauto; dtr.
      exists true. split; eauto.
    + inv H.
      eapply IHt2 in H8; eauto; dtr.
      exists true. split; eauto.
  - inv H0.
    + inv H. exists false. split; simpl; auto.
    + inv H.
      eapply IHt1 in H2; eauto; dtr.
      exists true. split; eauto.
    + inv H.
      eapply IHt2 in H8; eauto; dtr.
      exists true. split; eauto.
  - inv H0.
    + inv H.
      eapply IHt1 in H2; eauto; dtr.
      exists (x || E2 || E3). split; wtbt; wttost; eauto.
      * destruct E1; destruct E2; destruct E3; crush.
    + inv H.
      eapply IHt2 in H8; eauto; dtr.
      exists (E1 || x || E3). split; wtbt; wttost; eauto.
      * destruct E1; destruct E2; destruct E3; crush.
    + inv H.
      eapply IHt3 in H9; eauto; dtr.
      exists (E1 || E2 || x). split; wtbt; wttost; eauto.
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
        - apply context_invariance with empty; wtbt; wttost; auto.
          intros; apply typable_empty__closed in H7; unfold closed in H7; exfalso; apply (@H7 x); auto.
        - replace false with (false || false || false).
          econstructor; simpl.
          apply context_invariance with empty. wtbt; wttost; auto.
          intros; apply typable_empty__closed in H7; unfold closed in H7; exfalso; apply (@H7 x); auto.
          auto.
        }
        destruct E3; auto.
      * auto.
      * destruct E2; destruct E3; auto.
    + inv H. eapply IHt in H2; eauto; dtr.
      exists x. split; eauto.
Qed.

Theorem preservation : forall c c' T E,
  config_has_type c T E ->
  distinct (config_labels c) ->
  c --> c'  ->
  exists E', config_has_type c' T E' /\ (match E with
                                    | false => E' = false
                                    | _ => True
                                    end).
Proof with eauto.
  intros c c' T E Hht Hdistinct Hstep.
  generalize dependent T.
  generalize dependent E.
  induction Hstep; intros; subst c.
  - inversion Hht; subst.
    copy H0. rename H0 into Hstep. apply preservation' with (b:= b) (os0:=os) (rs:=rs) (T:=T) (E:=E) in H; eauto; dtr.
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
    + apply wt_to_wt6 in H7; eauto; dtr. wtbt'. eauto.
    + wtbt'. rewrite backend_types_app in *. destruct n. simpl in *. rewrite ostream_types_app in *. simpl in *.
      clear H9 H. wttost'.
      replace (l' #-> Result; l #-> Result; ostream_types os2 (ostream_types os1 (backend_types b2 (backend_types b1 (rstream_types rs)))))
              with (l #-> Result; l' #-> Result; ostream_types os2 (ostream_types os1 (backend_types b2 (backend_types b1 (rstream_types rs))))).
      eauto.
      apply NMaps.update_permute. apply fresh_labels.
    + wtbt. wttost. rewrite backend_types_app in *. destruct n. simpl in *. rewrite ostream_types_app in *. simpl in *.
      eauto.
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
    copy Hht. rename H into Hht'. inv Hht. apply well_typed_backend_dist' in H6; dtr. copy H0. inv H0.
    copy H1. rename H1 into Hstep. eapply preservation' with (T:=Result) (E:=false) in H0; dtr; subst; eauto.
    econstructor; eauto. eapply well_typed_backend_dist; eauto.
    inv H2. econstructor; eauto. simpl. wtbt. eauto. simpl. wtbt. wtbt'. eauto.
    clear H0 H15 H14 H13 H11 H2 H8 H7 Hht' Hstep.
    unfold config_labels in *.
    rewrite backend_labels_dist in *. simpl in *.
    rewrite <- List.app_assoc in Hdistinct.
    apply distinct_concat in Hdistinct; dtr.
    unfold backend_labels in H1; simpl in *.
    rewrite <- List.app_assoc in H1.
    apply distinct_concat in H1; dtr.
    apply distinct_app_comm in H2.
    rewrite <- List.app_assoc in H2.
    apply distinct_concat in H2; dtr. auto.
  - subst. exists E. split; [|destruct E; eauto].
    inv Hht. apply well_typed_backend_dist' in H6; dtr. inv H0.
    wtosdist. inv H2. inv H13.
    copy H1. rename H1 into Hstep.
    eapply preservation' with (T:=Result) (E:=false) in H2; dtr; subst; eauto.
    + econstructor; eauto.
      eapply well_typed_backend_dist; auto.
      * instantiate (1:=x); auto.
      * copy H14; apply wt_to_backend_types in H14; subst.
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
    + instantiate (1:=k).
      clear H0 H15 H14 H11 H2 H8 H7 H9 H10 H12 H Hstep.
      unfold config_labels in Hdistinct; simpl in *.
      apply distinct_app_comm in Hdistinct.
      rewrite <- List.app_assoc in Hdistinct.
      apply distinct_concat in Hdistinct; dtr.
      apply distinct_app_comm in H0.
      rewrite backend_labels_dist in H0.
      rewrite <- List.app_assoc in H0.
      apply distinct_concat in H0; dtr.
      unfold backend_labels in H1; simpl in *.
      rewrite <- List.app_assoc in H1.
      rewrite ostream_labels_dist in H1.
      rewrite <- List.app_assoc in H1.
      apply distinct_app_comm in H1.
      rewrite <- List.app_assoc in H1.
      apply distinct_concat in H1; dtr.
      apply distinct_app_comm in H2. unfold backend_labels. crush.
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
            eapply dry_no_in with (n:=n) (os:=os1 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os2) in H6; eauto; crush. (* destruct os1; crush. *)
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
      * inv H2. inv H5.
        {
          destruct b2.
          - inv H2; crush. destruct os1; crush.
          - inv H2.
            eapply dry_no_in with (n:=n) (os:=os1 ++ l ->> pfold f t0 ks :: l' ->> pfold f' t' ks' :: os2) in H8; eauto.
            + destruct os1; crush.
            (* + crush. *)
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
                  + exfalso; apply H. eapply ex_intro; eapply S_SwapReads with (f':=f'); eauto; crush.
                  + exfalso; apply H. eapply ex_intro; eapply S_Prop; eauto; crush.
                  + exfalso; apply H. eapply ex_intro; eapply S_Load; eauto; crush.
                  + exfalso; apply H. eapply ex_intro; eapply S_LoadPFold; eauto; crush.
              }
              inv H1.
              destruct n.
              destruct (value_dec p); eauto.
              eapply load_exists with (k:=k) (os:=[]) (b1:=[]) (b2:=b) in WT; eauto.
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

Ltac apply_preservation :=
  match goal with
  | [H: C _ _ _ _ --> C _ _ _ _ |- _] => eapply preservation in H; eauto
  end.

Lemma not_equal_not_in : forall {A : Type} (x:A) xs,
  (forall x', In x' xs -> x <> x') ->
  not (In x xs).
Proof using.
  intros. intro. apply (@H x); auto.
Qed.

Lemma fresh_not_in : forall b os rs t t' l op,
  distinct (config_labels (C b os rs t)) ->
  FRf t rs ==> FRt t' [l ->> op] ->
  not (In l (config_labels (C b os rs t))).
Proof using. intros; apply not_equal_not_in; auto. Qed.

Lemma fresh_not_in' : forall b os rs t t' l k v,
  distinct (config_keys (C b os rs t)) ->
  FRf t rs ==> FRt t' [l ->> add k v] ->
  not (In k (config_keys (C b os rs t))).
Proof using. intros; apply not_equal_not_in; auto. Qed.

Lemma fresh :
  forall t b os rs t' os',
  distinct (config_labels (C b os rs t)) ->
  FRf t rs ==> FRt t' os' ->
  distinct (List.concat [backend_labels b; ostream_labels (os ++ os'); rstream_labels rs]).
Proof using.
  induction t; intros; try solve [inv H0]; try solve [inv H0; try solve [eapply IHt in H; eauto]; try solve [eapply IHt1 in H; eauto]; try solve [eapply IHt2 in H; eauto]; try solve [eapply IHt3 in H; eauto]; try solve [crush]].
  - inversion H0; subst; try solve [eapply IHt1 in H; eauto]; try solve [eapply IHt2 in H; eauto]; try solve [eapply IHt3 in H; eauto].
    simpl. rewrite ostream_labels_dist. simpl.
    replace  (backend_labels b ++ (ostream_labels os ++ [l]) ++ rstream_labels rs ++ []) with ((backend_labels b ++ ostream_labels os) ++ l :: rstream_labels rs) by crush.
    apply distinct_rotate. econstructor; eauto.
    + eapply fresh_not_in in H0; eauto. simpl in *. crush.
    + crush.
  - inversion H0; subst; try solve [eapply IHt1 in H; eauto]; try solve [eapply IHt2 in H; eauto]; try solve [eapply IHt3 in H; eauto].
    simpl. rewrite ostream_labels_dist. simpl.
    replace  (backend_labels b ++ (ostream_labels os ++ [l]) ++ rstream_labels rs ++ []) with ((backend_labels b ++ ostream_labels os) ++ l :: rstream_labels rs) by crush.
    apply distinct_rotate. econstructor; eauto.
    + eapply fresh_not_in in H0; eauto. simpl in *. crush.
    + crush.
  - inversion H0; subst; try solve [eapply IHt1 in H; eauto]; try solve [eapply IHt2 in H; eauto]; try solve [eapply IHt3 in H; eauto].
    simpl. rewrite ostream_labels_dist. simpl.
    replace  (backend_labels b ++ (ostream_labels os ++ [l]) ++ rstream_labels rs ++ []) with ((backend_labels b ++ ostream_labels os) ++ l :: rstream_labels rs) by crush.
    apply distinct_rotate. econstructor; eauto.
    + eapply fresh_not_in in H0; eauto. simpl in *. crush.
    + crush.
Qed.

Lemma fresh' :
  forall b os rs t os' t',
  distinct (config_keys (C b os rs t)) ->
  FRf t rs ==> FRt t' os' ->
  distinct (List.concat [backend_keys b; ostream_keys (os ++ os')]).
Proof using.
  induction t; intros; try solve [inv H0]; try solve [inv H0; try solve [eapply IHt in H; eauto]; try solve [eapply IHt1 in H; eauto]; try solve [eapply IHt2 in H; eauto]; try solve [eapply IHt3 in H; eauto]; try solve [crush]].
  - inversion H0; subst; try solve [eapply IHt1 in H; eauto]; try solve [eapply IHt2 in H; eauto]; try solve [eapply IHt3 in H; eauto].
    simpl. rewrite ostream_keys_dist. unfold ostream_keys in *; crush.
  - inversion H0; subst; try solve [eapply IHt1 in H; eauto]; try solve [eapply IHt2 in H; eauto]; try solve [eapply IHt3 in H; eauto].
    simpl. rewrite ostream_keys_dist. unfold ostream_keys in *; crush.
  - inversion H0; subst; try solve [eapply IHt1 in H; eauto]; try solve [eapply IHt2 in H; eauto]; try solve [eapply IHt3 in H; eauto].
    simpl. rewrite ostream_keys_dist. unfold ostream_keys at 2; simpl.
    rewrite List.app_nil_r. rewrite List.app_assoc.
    apply distinct_rotate. econstructor; eauto.
    + eapply fresh_not_in' in H0; eauto. simpl in *. crush.
    + crush.
Qed.

Lemma well_typed_preservation :
  forall c1 c2,
  well_typed c1 ->
  c1 --> c2 ->
  well_typed c2.
Proof using.
  intros.
  inversion H0; inversion H; eapply WT; subst;
  try solve [match goal with | [H : exists _ _, _|- _] => destruct H as [T[E]] end; apply preservation with (T:=T) (E:=E) in H0; auto; destruct H0; destruct H0; inv H0; eauto];
  try solve [apply_preservation].
  (* S_Frontend *)
  - eapply fresh'; eauto.
  - eapply fresh; eauto.
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
  (* S_SwapReads *)
  - crush.
  - crush.
    unfold backend_labels at 2 in H8; simpl in *. rewrite ostream_labels_dist in H8; simpl in *.
    unfold backend_labels at 2; simpl in *. rewrite ostream_labels_dist; simpl in *.
    repeat (rewrite <- List.app_assoc in *).
    replace (backend_labels b1 ++ ostream_labels os1 ++ (l' :: l :: ostream_labels os2) ++ List.concat (map (fun s : station => ostream_labels (get_ostream s)) b2) ++ ostream_labels os ++ rstream_labels rs)
            with ((backend_labels b1 ++ ostream_labels os1 ++ [l']) ++ l :: ostream_labels os2 ++ List.concat (map (fun s : station => ostream_labels (get_ostream s)) b2) ++ ostream_labels os ++ rstream_labels rs) by crush.
    apply distinct_rotate.
    rewrite List.app_assoc in H8. apply distinct_rotate_rev in H8. crush.
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

(* Theorem 6.3 *)
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
