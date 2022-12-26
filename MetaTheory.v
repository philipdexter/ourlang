
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

Local Set Warnings "-implicit-core-hint-db".
Local Set Warnings "-deprecated-focus".
Local Set Warnings "-unused-intro-pattern".
Local Set Warnings "-local-declaration".

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

Require Import SyntaxRuntime.
Require Import Typing.
Require Import OperationalSemantics.

Require Import MetaTheoryBase.
Require Import MetaTheoryTyping.
Require Import MetaTheoryLocalConfluence.

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

Definition r_complete (p : config -> config -> Prop) :=
  forall cx, (forall cy cy' n m, n > 0 -> m > 0 -> cx -->*[n] cy -> cx -->*[m] cy' -> p cy cy') -> p cx cx.

Axiom principal_of_noe_indo : forall P, r_complete P -> forall cx, P cx cx.

Definition pp cx cy := well_typed cx -> well_typed cy -> cx == cy ->
                                  forall cx' cy' n m,
                                    cx -->*[n] cx' ->
                                    cy -->*[m] cy' ->
                                    cx' -v cy'.

(* we are only interested in reductions that terminate *)
Hypothesis to_dry : forall c, exists n c', c -->*[n] c' /\ dry c'.

Lemma pp_r_complete :
  r_complete pp.
Proof using.
  unfold r_complete; intros.
    unfold pp in *.
  intros.
  rename cy' into cz.
  rename cx' into cy.
  rename H3 into XY.
  rename H4 into XZ.
  assert (H3: 1 + 1 = 2) by auto.
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
    destruct (local_confluence H1 H5 H7).
    destruct H4. destruct H4. destruct H9. destruct H4. destruct H9.
    rename x into cy''.
    rename x0 into cz''.
    assert (exists n cw, cy -->*[n] cw /\ normal_form cw).
    {
      destruct (@to_dry cy); dtr.
      exists x, x0. destruct x0.
      split; [eauto|eapply dry_normal_form; eauto].
    }
    destruct H11 as [n' H']. destruct H' as [cw cycw]. destruct cycw as [cycw nfcw].
    assert (exists n cw', cy'' -->*[n] cw' /\ normal_form cw').
    {
      destruct (@to_dry cy''); dtr.
      exists x, x0. destruct x0.
      split; [eauto|eapply dry_normal_form; eauto].
    }
    destruct H11 as [n'' H']. destruct H' as [cw' cycw']. destruct cycw' as [cycw' nfcw'].
    assert (exists n cv, cz'' -->*[n] cv /\ normal_form cv).
    {
      destruct (@to_dry cz''); dtr.
      exists x, x0. destruct x0.
      split; [eauto|eapply dry_normal_form; eauto].
    }
    destruct H11 as [n''' H']. destruct H' as [cv cycv]. destruct cycv as [cycv nfcv].
    assert (exists n cv', cz -->*[n] cv' /\ normal_form cv').
    {
      destruct (@to_dry cz); dtr.
      exists x, x0. destruct x0.
      split; [eauto|eapply dry_normal_form; eauto].
    }
    destruct H11 as [n'''' H']. destruct H' as [cv' cycv']. destruct cycv' as [cycv' nfcv'].
    assert (Hsimcy' : cy' == cy') by crush.
    assert (cw == cw').
    {
      edestruct H with (cy:=cy') (cy':=cy') (cx':=cw) (cy'0:=cw') (n:=1) (m:=1); eauto.
      - destruct H11.
        destruct H11.
        destruct H11.
        destruct H12.
        destruct H12.
        assert (x = cw).
        {
          destruct x3.
          - apply star_zero in H11; eauto.
          - inversion H11. subst. exfalso. unfold normal_form in nfcw. apply nfcw. eauto.
        }
        subst.
        assert (x0 = cw').
        {
          destruct x4.
          - apply star_zero in H12; eauto.
          - inversion H12. subst. exfalso. unfold normal_form in nfcw'. apply nfcw'. eauto.
        }
        subst.
        assumption.
    }
    assert (Hsimcz' : cz' == cz') by crush.
    assert (cv == cv').
    {
      edestruct H with (cy:=cz') (cy':=cz') (cx':=cv) (cy'0:=cv') (n:=1); eauto.
      - destruct H12.
        destruct H12.
        destruct H12.
        destruct H13.
        destruct H13.
        assert (x = cv).
        {
          destruct x3.
          - apply star_zero in H12; eauto.
          - inversion H12. subst. exfalso. unfold normal_form in nfcv. apply nfcv. eauto.
        }
        subst.
        assert (x0 = cv').
        {
          destruct x4.
          - apply star_zero in H13; eauto.
          - inversion H13. subst. exfalso. unfold normal_form in nfcv'. apply nfcv'. eauto.
        }
        subst. assumption.
    }
    assert (cw' == cv).
    {
      edestruct H with (cy:=cy'') (cy':=cz'') (cx':=cw') (cy'0:=cv) (n:=S x1) (m:=S x2); eauto.
      - crush.
      - crush.
      - destruct H13.
        destruct H13.
        destruct H13.
        destruct H14.
        destruct H14.
        assert (x = cw').
        {
          destruct x3.
          - apply star_zero in H13; eauto.
          - inversion H13. subst. exfalso. unfold normal_form in nfcw'. apply nfcw'. eauto.
        }
        subst.
        assert (x0 = cv).
        {
          destruct x4.
          - apply star_zero in H14; eauto.
          - inversion H14. subst. exfalso. unfold normal_form in nfcv. apply nfcv. eauto.
        }
        subst. assumption.
    }
    apply ex_intro with cw.
    apply ex_intro with cv'.
    split; try split.
    + eauto.
    + eauto.
    + apply cequiv_trans with cw'; auto.
      apply cequiv_trans with cv; auto.
Qed.

(* Theorem 6.5 and Corollary 6.7 *)
(* Note that eager processing is a set of specific context choices of lazy processing (Fig 14) *)
Theorem confluence :
  forall cx cy cz,
  well_typed cx ->
  (exists n, cx -->*[n] cy) ->
  (exists m, cx -->*[m] cz) ->
  (cy -v cz).
Proof using.
  intros.
  destruct H0.
  destruct H1.
  edestruct (@principal_of_noe_indo pp) with (cx:=cx) (cx':=cy); eauto.
- apply pp_r_complete.
Qed.

Definition init (b : backend) (t : term) := C b [] [] t.

(* Theorem 6.6 *)
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
