
Require Import CpdtTactics.
From Coq Require Import Lists.List.
From Coq Require Import Sorting.Permutation.
From Coq Require Import Arith.PeanoNat.
Import ListNotations.

Require Import Maps.
Require Import SyntaxRuntime.
Require Import Typing.
Require Import OperationalSemantics.

Local Set Warnings "-implicit-core-hint-db".

Ltac dtr := repeat (match goal with
                    | [H : _ /\ _ |- _] => destruct H
                    | [H : exists _ , _ |- _] => destruct H
                    end).
Ltac exi := eapply ex_intro.

Inductive well_typed : config -> Prop :=
| WT : forall c,
    distinct (config_keys c) ->
    distinct (config_labels c) ->
    (exists T b, config_has_type c T b) ->
    well_typed c.
Hint Constructors well_typed.

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
      destruct (Nat.eq_dec l0 l).
      * subst. left. exists r. crush.
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
      destruct (Nat.eq_dec l0 l).
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
  destruct a. simpl in H. destruct (Nat.eq_dec l0 l).
  - left. exi; crush.
  - replace ((l0#->(op_type o); ostream_types os ll) l) with ((ostream_types os ll) l) in *.
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
  - left. exists [], <<N k p e; l0>>, b, x. eauto.
  - apply IHb in H. destruct H; dtr.
    + left. exists (<<N k p e; l0>> :: x), x0, x1, x2. crush.
    + eauto.
Qed.

Lemma type_in_rstream : forall rs l T,
  (rstream_types rs) l = Some T ->
  exists v, In (l ->>> v) rs.
Proof using.
  induction rs; intros.
  - inv H.
  - destruct a. rename l0 into n.
    destruct (Nat.eq_dec l n); subst.
    + exists r. crush.
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

Lemma list_app_cons_empty : forall {A : Type} (x : A) xs ys,
  xs ++ x :: ys = [] -> False.
Proof using.
  induction xs; crush.
Qed.
Hint Resolve list_app_cons_empty.

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
