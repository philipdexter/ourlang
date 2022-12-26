
Require Import CpdtTactics.
From Coq Require Import Lists.List.
From Coq Require Import Bool.Bool.
Import ListNotations.
From Coq Require Import Arith.PeanoNat.
From Coq Require Import Sorting.Permutation.

Require Import Maps.
Require Import SyntaxRuntime.
Require Import Typing.
Require Import OperationalSemantics.
Require Import MetaTheoryTyping.
Require Import MetaTheoryBase.

Local Set Warnings "-implicit-core-hint-db".
Local Set Warnings "-local-declaration".
Local Set Warnings "-unused-intro-pattern".

Hint Constructors Permutation.Permutation.

Set Implicit Arguments.

Ltac got := eapply ex_intro; eapply ex_intro; split; try split.
Ltac one_step := apply ex_intro with (1); apply one_star.
Ltac gotw X := got; try instantiate (1:=X); try one_step.

Ltac fnv :=
      match goal with
      | [H : FRf ?t _ ==> FRt _ _, H' : value ?t |- _] => exfalso; eapply frontend_no_value in H; eauto
      end.

Lemma frontend_deterministic :
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
  - eapply frontend_deterministic with (t':=t'0) (os:=os'0) in Hstep; dtr; subst; auto.
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
      gotw (C (<< N k t' es; os2 ++ [l ->> op] >> :: b') os' rs term); eauto.
      eapply S_Load with (b1:=[]); eauto; crush.
    + inv H1.
      gotw (C (<< n1; os2 ++ [l ->> op] >> :: b1 ++ << N k t' es; os >> :: b2) os' rs term); eauto.
      eapply S_Load with (b1:=<< n1; os2 ++ [l ->> op] >> :: b1); eauto; crush.
  (* S_Add *)
  - gotw (C (<< N k0 v t_ks_nil; [] >> :: b1 ++ << N k t' es; os >> :: b2) os' (l ->>> final H :: rs) term); eauto.
    eapply S_Load with (b1:=<< N k0 v t_ks_nil; [] >> :: b1); eauto; crush.
  (* S_PMap *)
  - tsod.
    + inv H. apply List.app_inv_head in H1. inv H1.
      got.
      * one_step. instantiate (1:=C (b0 ++ << N k0 (t_app f t') es0; l ->> pmap f (remove Nat.eq_dec k0 ks) :: os1'' >> :: b3) os1 rs term).
        eapply S_PMap; eauto.
      * one_step. instantiate (1:=C (b0 ++ << N k0 (t_app f t') es0; l ->> pmap f (remove Nat.eq_dec k0 ks) :: os1'' >> :: b3) os1 rs term).
        eapply S_Load; eauto.
        eapply F_App2 with (os:=[]); eauto.
        remember (pmap f ks) as op; subst op; eapply pmap_value with (os:=[]); eauto.
      * crush.
    + destruct Hfirst as [b' [b'' [b''']]].
      tu1.
      got.
      * one_step. instantiate (1:=C ((b' ++ << N k t' es; os >> :: b'') ++ << N k0 (t_app f v) es0; l ->> pmap f (remove Nat.eq_dec k0 ks) :: os1'' >> :: b3) os1 rs term).
        eapply S_PMap; eauto; crush.
      * one_step. instantiate (1:=C (b' ++ << N k t' es; os >> :: b'' ++ << N k0 (t_app f v) es0; l ->> pmap f (remove Nat.eq_dec k0 ks) :: os1'' >> :: b3) os1 rs term).
        eapply S_Load; eauto; crush.
      * crush.
    + destruct Hsecond as [b' [b'' [b''']]].
      tu2.
      got.
      * instantiate (1:=C (b0 ++ << N k0 (t_app f v) es0; l ->> pmap f (remove Nat.eq_dec k0 ks) :: os1'' >> :: b'' ++ << N k t' es; os >> :: b''') os1 rs term).
        one_step; eapply S_PMap; eauto.
      * instantiate (1:=C ((b0 ++ << N k0 (t_app f v) es0; l ->> pmap f (remove Nat.eq_dec k0 ks) :: os1'' >> :: b'') ++ << N k t' es; os >> :: b''') os1 rs term).
        one_step; eapply S_Load; eauto; crush.
      * crush.
  (* S_PFold *)
  - tsod.
    + got. inv H. apply List.app_inv_head in H1. inv H1.
      * instantiate (1:=C (b0 ++ << N k0 t' es0; l ->> pfold f (t_app (t_app f t') t'0) (remove Nat.eq_dec k0 ks) :: os1'' >> :: b3) os1 rs term).
        one_step. eapply S_PFold; eauto.
      * instantiate (1:=C (b0 ++ << N k0 t' es0; l ->> pfold f (t_app (t_app f t') t'0) (remove Nat.eq_dec k0 ks) :: os1'' >> :: b3) os1 rs term).
        exists 2.
        eapply Step.
        instantiate (1:=C (b0 ++ << N k0 t' es0; l ->> pfold f (t_app (t_app f t0) t'0) (remove Nat.eq_dec k0 ks) :: os1'' >> :: b3) os1 rs term).
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
      * instantiate (1:=C ((b' ++ << N k t' es; os >> :: b'') ++ << N k0 t0 es0; l ->> pfold f (t_app (t_app f t0) t'0) (remove Nat.eq_dec k0 ks) :: os1'' >> :: b3) os1 rs term).
        one_step; eapply S_PFold; eauto; crush.
      * instantiate (1:=C (b' ++ << N k t' es; os >> :: b'' ++ << N k0 t0 es0; l ->> pfold f (t_app (t_app f t0) t'0) (remove Nat.eq_dec k0 ks) :: os1'' >> :: b3) os1 rs term).
        one_step; eapply S_Load; eauto.
      * crush.
    + destruct Hsecond as [b' [b'' [b''']]].
      tu2.
      got.
      * instantiate (1:=C (b0 ++ << N k0 t0 es0; l ->> pfold f (t_app (t_app f t0) t'0) (remove Nat.eq_dec k0 ks) :: os1'' >> :: b'' ++ << N k t' es; os >> :: b''') os1 rs term).
        one_step; eapply S_PFold; eauto; crush.
      * instantiate (1:=C ((b0 ++ << N k0 t0 es0; l ->> pfold f (t_app (t_app f t0) t'0) (remove Nat.eq_dec k0 ks) :: os1'' >> :: b'') ++ << N k t' es; os >> :: b''') os1 rs term).
        one_step; eapply S_Load; eauto; crush.
      * crush.
  (* S_Last *)
  - destruct b2.
    + apply List.app_inj_tail in H2. destruct H2. inv H2.
      gotw (C (b0 ++ [<< N k t' es; os1' >>]) os1 (l ->>> final H :: rs) term); eauto.
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
      * instantiate (1:=C ((b1 ++ << N k t' es; os >> :: x0) ++ [<< n1; os1' >>]) os1 (l ->>> final H :: rs) term).
        one_step; eapply S_Last; eauto; crush.
      * instantiate (1:=C (b1 ++ << N k t' es; os >> :: x0 ++ [<< n1; os1' >>]) os1 (l ->>> final H :: rs) term).
        one_step; eapply S_Load; eauto; crush.
      * crush.
  (* S_FusePMap *)
  - destruct n. tsod'. inv H0. apply List.app_inv_head in H2. inv H2.
    + gotw (C (b0 ++ << N k0 t' e; os2 ++ l' ->> pmap (pmap_compose f' f) ks :: os3 >> :: b3) os1 (l ->>> final H :: rs) term); eauto.
    + destruct Hfirst as [b' [b'' [b''']]].
      tu1.
      got.
      * instantiate (1:=C ((b' ++ << N k t' es; os >> :: b'') ++ << N k0 p e; os2 ++ l' ->> pmap (pmap_compose f' f) ks :: os3 >> :: b3) os1 (l ->>> 0 :: rs) term).
        one_step; eapply S_FusePMap; eauto; crush.
      * instantiate (1:=C (b' ++ << N k t' es; os >> :: b'' ++ << N k0 p e; os2 ++ l' ->> pmap (pmap_compose f' f) ks :: os3 >> :: b3) os1 (l ->>> 0 :: rs) term).
        one_step; eapply S_Load; eauto; crush.
      * crush.
    + destruct Hsecond as [b' [b'' [b''']]].
      tu2.
      got.
      * instantiate (1:=C (b0 ++ << N k0 p e; os2 ++ l' ->> pmap (pmap_compose f' f) ks :: os3 >> :: b'' ++ << N k t' es; os >> :: b''') os1 (l ->>> 0 :: rs) term).
        one_step; eapply S_FusePMap; eauto; crush.
      * instantiate (1:=C ((b0 ++ << N k0 p e; os2 ++ l' ->> pmap (pmap_compose f' f) ks :: os3 >> :: b'') ++ << N k t' es; os >> :: b''') os1 (l ->>> 0 :: rs) term).
        one_step; eapply S_Load; eauto; crush.
      * crush.
  (* S_SwapReads *)
  - destruct n. tsod'.
    + inv H. apply List.app_inv_head in H3. inv H3.
      gotw (C (b0 ++ << N k0 t' e; os2 ++ l' ->> pfold f' t'0 ks' :: l ->> pfold f t0 ks :: os3 >> :: b3) os1 rs term); eauto.
    + destruct Hfirst as [b' [b'' [b''']]].
      tu1.
      got.
      * instantiate (1:=C ((b' ++ << N k t' es; os >> :: b'') ++ << N k0 p e; os2 ++ l' ->> pfold f' t'0 ks' :: l ->> pfold f t0 ks :: os3 >> :: b3) os1 rs term).
        one_step; eapply S_SwapReads; eauto; crush.
      * instantiate (1:=C (b' ++ << N k t' es; os >> :: b'' ++ << N k0 p e; os2 ++ l' ->> pfold f' t'0 ks' :: l ->> pfold f t0 ks :: os3 >> :: b3) os1 rs term).
        one_step; eapply S_Load; eauto; crush.
      * crush.
    + destruct Hsecond as [b' [b'' [b''']]].
      tu2.
      got.
      * instantiate (1:=C (b0 ++ << N k0 p e; os2 ++ l' ->> pfold f' t'0 ks' :: l ->> pfold f t0 ks :: os3 >> :: b'' ++ << N k t' es; os >> :: b''') os1 rs term).
        one_step; eapply S_SwapReads; eauto; crush.
      * instantiate (1:=C ((b0 ++ << N k0 p e; os2 ++ l' ->> pfold f' t'0 ks' :: l ->> pfold f t0 ks :: os3 >> :: b'') ++ << N k t' es; os >> :: b''') os1 rs term).
        one_step; eapply S_Load; eauto; crush.
      * crush.
  (* S_Prop *)
  - destruct n1. tsod.
    + inv H. apply List.app_inv_head in H2; inv H2.
      gotw (C (b0 ++ << N k0 t' e; os2 >> :: << n2; os3 ++ [l ->> op] >> :: b3) os1 rs term); eauto.
    + destruct Hfirst as [b' [b'' [b''']]].
      tu1.
      got.
      * instantiate (1:=C ((b' ++ << N k t' es; os >> :: b'') ++ << N k0 p e; os2 >> :: << n2; os3 ++ [l ->> op] >> :: b3) os1 rs term); eauto.
        one_step; eapply S_Prop; eauto; crush.
      * instantiate (1:=C (b' ++ << N k t' es; os >> :: b'' ++ << N k0 p e; os2 >> :: << n2; os3 ++ [l ->> op] >> :: b3) os1 rs term); eauto.
      * crush.
    + destruct Hsecond as [b' [b'' [b''']]].
      tu2.
      {
      destruct b''; simpl in *.
      - inv H1.
        got.
        + instantiate (1:=C (b0 ++ << N k0 p e; os2 >> :: << N k t' es; os3 ++ [l ->> op] >> :: b3) os1 rs term); eauto.
          one_step; eapply S_Prop; eauto; crush.
        + instantiate (1:=C ((b0 ++ [<< N k0 p e; os2 >>]) ++ << N k t' es; os3 ++ [l ->> op] >> :: b3) os1 rs term); eauto.
          one_step; eapply S_Load; eauto; crush.
        + crush.
      - inv H1.
        got.
        + instantiate (1:=C (b0 ++ << N k0 p e; os2 >> :: << n2; os3 ++ [l ->> op] >> :: b'' ++ << N k t' es; os >> :: b''') os1 rs term); eauto.
          one_step; eapply S_Prop; eauto; crush.
        + instantiate (1:=C ((b0 ++ << N k0 p e; os2 >> :: << n2; os3 ++ [l ->> op] >> :: b'') ++ << N k t' es; os >> :: b''') os1 rs term); eauto.
          one_step; eapply S_Load; eauto; crush.
        + crush.
      }
  (* S_Load *)
  - tsod.
    + inv H. apply List.app_inv_head in H2; inv H2.
      eapply frontend_deterministic with (b0:=b0 ++ <<N k0 t0 es0; os2>> :: b3) (os0:=os1) (os:=[]) (t':=t'0) in tt'; eauto. destruct tt'.
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

Lemma not_appears_none : forall t l Gamma ll T E,
  has_type Gamma ll t T E ->
  ll l = None ->
  not (lappears_free_in l t).
Proof using.
  intros.
  intro.
  generalize dependent T.
  generalize dependent E.
  generalize dependent Gamma.
  induction H1; intros; subst; try solve [inv H; eauto].
  - inv H. crush.
Qed.

Lemma lcontext_not_in_or_os' : forall os l ll,
  not (exists op, In (l ->> op) os) ->
  ll l = None ->
  (ostream_types os ll) l = None.
Proof using.
  induction os; intros.
  - auto.
  - destruct a. simpl. rename l0 into n. destruct (Nat.eq_dec n l); subst.
    + exfalso. apply H. exists o. crush.
    + replace ((n #-> op_type o; ostream_types os ll) l) with ((ostream_types os ll) l).
      apply IHos.
      intro. dtr. apply H. exists x. crush. auto.
      rewrite NMaps.update_neq; auto.
Qed.

Lemma lcontext_not_in_or_b' : forall b l ll,
  not (exists os1 os2 b1 b2 s op, b = b1 ++ s :: b2 /\ get_ostream s = os1 ++ l ->> op :: os2) ->
  ll l = None ->
  (backend_types b ll) l = None.
Proof using.
  induction b; intros.
  - auto.
  - destruct a. destruct n. simpl in *.
    apply lcontext_not_in_or_os'.
    + intro; dtr. apply H. apply List.in_split in H1; dtr. exists x0, x1, [], b, <<N k p e; l0>>, x. crush.
    + apply IHb.
      intro. dtr. apply H. exists x, x0, (<<N k p e; l0>> :: x1), x2, x3, x4. destruct x3. simpl in *. subst. crush. auto.
Qed.

Lemma lcontext_not_in_or_rs' : forall rs l,
  not (exists v, In (l ->>> v) rs) ->
  (rstream_types rs) l = None.
Proof using.
  induction rs; intros.
  - auto.
  - destruct a. simpl in *. rename l0 into n.
    destruct (Nat.eq_dec n l); subst.
    + exfalso. apply H. exists r. left. auto.
    + replace ((n #-> Result; rstream_types rs) l) with ((rstream_types rs) l).
      apply IHrs.
      intro. dtr. apply H. exists x. crush.
      rewrite NMaps.update_neq; auto.
Qed.

Lemma in_ostream_labels : forall os l op,
  In (l ->> op) os ->
  In l (ostream_labels os).
Proof using.
  induction os; intros.
  - auto.
  - destruct a. simpl. rename l0 into n. destruct (Nat.eq_dec n l).
    + auto.
    + inv H; eauto.
      inv H0. eauto.
Qed.

Lemma lcontext_not_in_or_os : forall os l ll,
  (ostream_types os ll) l = None ->
  not (exists op, In (l ->> op) os) /\ ll l = None.
Proof using.
  induction os; intros. split; try intro.
  - dtr. inv H0.
  - inv H. auto.
  - destruct a. simpl in *.
    rename l0 into n. destruct (Nat.eq_dec n l).
    + subst. rewrite NMaps.update_eq in H. inv H.
    + replace ((n #-> op_type o; ostream_types os ll) l) with ((ostream_types os ll) l) in H.
      apply IHos in H; dtr.
      split; eauto.
      intro. dtr. apply H. destruct H1; eauto. inv H1. exfalso. apply n0. reflexivity.
      rewrite NMaps.update_neq; auto.
Qed.

Lemma no_dep_backwards : forall b1 b2 os1 os2 os0 rs0 t0 n l l' f t ks f' t' ks',
  well_typed (C (b1 ++ <<n; os1 ++ l ->> pfold f t ks :: l' ->> pfold f' t' ks' :: os2>> :: b2) os0 rs0 t0) ->
  not (lappears_free_in l' t).
Proof using.
  intros.
  inv H; dtr.
  simpl in *.
  inv H.
  wtbdist.
  inv H2.
  wtosdist.
  inv H3.
  inv H12.
  simpl in *.
  inv H15.
  wtbt.
  wtost.
  wtost.
  wttost.
  wtbt.
  assert ((ostream_types os1 (backend_types b2 (rstream_types rs0))) l' = None).
  {
    apply lcontext_not_in_or_os'.
    - clear H10 H11 H6 H16 H12 H17 H14 H0.
      rewrite backend_labels_dist in H1.
      repeat (rewrite <- List.app_assoc in *).
      unfold backend_labels at 2 in H1; simpl in *.
      rewrite ostream_labels_dist in H1; simpl in *.
      repeat (rewrite <- List.app_assoc in *).
      replace (backend_labels b1 ++ ostream_labels os1 ++ (l :: l' :: ostream_labels os2) ++ List.concat (map (fun s : station => ostream_labels (get_ostream s)) b2) ++ ostream_labels os0 ++ rstream_labels rs0 ++ [])
              with ((backend_labels b1 ++ ostream_labels os1 ++ [l]) ++ l' :: ostream_labels os2 ++ List.concat (map (fun s : station => ostream_labels (get_ostream s)) b2) ++ ostream_labels os0 ++ rstream_labels rs0 ++ []) in H1 by crush.
      apply distinct_rotate_rev in H1.
      apply distinct_remove in H1; dtr.
      intro; dtr. apply H0.
      repeat (rewrite <- List.app_assoc in *).
      apply List.in_or_app. right.
      apply List.in_or_app. left.
      eapply in_ostream_labels; eauto.
    - apply lcontext_not_in_or_b'.
      + clear H10 H11 H6 H16 H12 H17 H14 H0.
        rewrite backend_labels_dist in H1.
        repeat (rewrite <- List.app_assoc in *).
        unfold backend_labels at 2 in H1; simpl in *.
        rewrite ostream_labels_dist in H1; simpl in *.
        repeat (rewrite <- List.app_assoc in *).
        replace (backend_labels b1 ++ ostream_labels os1 ++ (l :: l' :: ostream_labels os2) ++ List.concat (map (fun s : station => ostream_labels (get_ostream s)) b2) ++ ostream_labels os0 ++ rstream_labels rs0 ++ [])
                with ((backend_labels b1 ++ ostream_labels os1 ++ [l]) ++ l' :: ostream_labels os2 ++ List.concat (map (fun s : station => ostream_labels (get_ostream s)) b2) ++ ostream_labels os0 ++ rstream_labels rs0 ++ []) in H1 by crush.
        apply distinct_rotate_rev in H1.
        apply distinct_remove in H1; dtr.
        intro; dtr. apply H0.
        repeat (rewrite <- List.app_assoc in *).
        apply List.in_or_app. right.
        apply List.in_or_app. right.
        apply List.in_or_app. right.
        apply List.in_or_app. right.
        apply List.in_or_app. left.
        subst; simpl. destruct x5. simpl in *. subst. simpl.
        rewrite List.map_app. simpl.
        rewrite concat_app.
        apply List.in_or_app. right.
        simpl.
        apply List.in_or_app. left.
        rewrite ostream_labels_dist.
        apply List.in_or_app. right.
        simpl. crush.
      + apply lcontext_not_in_or_rs'.
        clear H10 H11 H6 H16 H12 H17 H14 H0.
        rewrite backend_labels_dist in H1.
        repeat (rewrite <- List.app_assoc in *).
        unfold backend_labels at 2 in H1; simpl in *.
        rewrite ostream_labels_dist in H1; simpl in *.
        repeat (rewrite <- List.app_assoc in *).
        replace (backend_labels b1 ++ ostream_labels os1 ++ (l :: l' :: ostream_labels os2) ++ List.concat (map (fun s : station => ostream_labels (get_ostream s)) b2) ++ ostream_labels os0 ++ rstream_labels rs0 ++ [])
                with ((backend_labels b1 ++ ostream_labels os1 ++ [l]) ++ l' :: ostream_labels os2 ++ List.concat (map (fun s : station => ostream_labels (get_ostream s)) b2) ++ ostream_labels os0 ++ rstream_labels rs0 ++ []) in H1 by crush.
        apply distinct_rotate_rev in H1.
        apply distinct_remove in H1; dtr.
        intro; dtr. apply H0.
        repeat (rewrite <- List.app_assoc in *).
        apply List.in_or_app. right.
        apply List.in_or_app. right.
        apply List.in_or_app. right.
        apply List.in_or_app. right.
        apply List.in_or_app. right.
        apply List.in_or_app. right.
        apply List.in_or_app. left.
        eapply in_rstream_labels; eauto.
  }
  eapply not_appears_none; eauto.
Qed.

Lemma no_dep_backwards' : forall b1 b2 os1 os2 os0 rs0 t0 n l l' f t ks f' t' ks',
  well_typed (C (b1 ++ <<n; os1 ++ l ->> pfold f t ks :: l' ->> pfold f' t' ks' :: os2>> :: b2) os0 rs0 t0) ->
  not (lappears_free_in l' f).
Proof using.
  intros.
  inv H; dtr.
  simpl in *.
  inv H.
  wtbdist.
  inv H2.
  wtosdist.
  inv H3.
  inv H12.
  simpl in *.
  inv H15.
  wtbt.
  wtost.
  wtost.
  wttost.
  wtbt.
  assert ((ostream_types os1 (backend_types b2 (rstream_types rs0))) l' = None).
  {
    apply lcontext_not_in_or_os'.
    - clear H10 H11 H6 H16 H12 H17 H14 H0.
      rewrite backend_labels_dist in H1.
      repeat (rewrite <- List.app_assoc in *).
      unfold backend_labels at 2 in H1; simpl in *.
      rewrite ostream_labels_dist in H1; simpl in *.
      repeat (rewrite <- List.app_assoc in *).
      replace (backend_labels b1 ++ ostream_labels os1 ++ (l :: l' :: ostream_labels os2) ++ List.concat (map (fun s : station => ostream_labels (get_ostream s)) b2) ++ ostream_labels os0 ++ rstream_labels rs0 ++ [])
              with ((backend_labels b1 ++ ostream_labels os1 ++ [l]) ++ l' :: ostream_labels os2 ++ List.concat (map (fun s : station => ostream_labels (get_ostream s)) b2) ++ ostream_labels os0 ++ rstream_labels rs0 ++ []) in H1 by crush.
      apply distinct_rotate_rev in H1.
      apply distinct_remove in H1; dtr.
      intro; dtr. apply H0.
      repeat (rewrite <- List.app_assoc in *).
      apply List.in_or_app. right.
      apply List.in_or_app. left.
      eapply in_ostream_labels; eauto.
    - apply lcontext_not_in_or_b'.
      + clear H10 H11 H6 H16 H12 H17 H14 H0.
        rewrite backend_labels_dist in H1.
        repeat (rewrite <- List.app_assoc in *).
        unfold backend_labels at 2 in H1; simpl in *.
        rewrite ostream_labels_dist in H1; simpl in *.
        repeat (rewrite <- List.app_assoc in *).
        replace (backend_labels b1 ++ ostream_labels os1 ++ (l :: l' :: ostream_labels os2) ++ List.concat (map (fun s : station => ostream_labels (get_ostream s)) b2) ++ ostream_labels os0 ++ rstream_labels rs0 ++ [])
                with ((backend_labels b1 ++ ostream_labels os1 ++ [l]) ++ l' :: ostream_labels os2 ++ List.concat (map (fun s : station => ostream_labels (get_ostream s)) b2) ++ ostream_labels os0 ++ rstream_labels rs0 ++ []) in H1 by crush.
        apply distinct_rotate_rev in H1.
        apply distinct_remove in H1; dtr.
        intro; dtr. apply H0.
        repeat (rewrite <- List.app_assoc in *).
        apply List.in_or_app. right.
        apply List.in_or_app. right.
        apply List.in_or_app. right.
        apply List.in_or_app. right.
        apply List.in_or_app. left.
        subst; simpl. destruct x5. simpl in *. subst. simpl.
        rewrite List.map_app. simpl.
        rewrite concat_app.
        apply List.in_or_app. right.
        simpl.
        apply List.in_or_app. left.
        rewrite ostream_labels_dist.
        apply List.in_or_app. right.
        simpl. crush.
      + apply lcontext_not_in_or_rs'.
        clear H10 H11 H6 H16 H12 H17 H14 H0.
        rewrite backend_labels_dist in H1.
        repeat (rewrite <- List.app_assoc in *).
        unfold backend_labels at 2 in H1; simpl in *.
        rewrite ostream_labels_dist in H1; simpl in *.
        repeat (rewrite <- List.app_assoc in *).
        replace (backend_labels b1 ++ ostream_labels os1 ++ (l :: l' :: ostream_labels os2) ++ List.concat (map (fun s : station => ostream_labels (get_ostream s)) b2) ++ ostream_labels os0 ++ rstream_labels rs0 ++ [])
                with ((backend_labels b1 ++ ostream_labels os1 ++ [l]) ++ l' :: ostream_labels os2 ++ List.concat (map (fun s : station => ostream_labels (get_ostream s)) b2) ++ ostream_labels os0 ++ rstream_labels rs0 ++ []) in H1 by crush.
        apply distinct_rotate_rev in H1.
        apply distinct_remove in H1; dtr.
        intro; dtr. apply H0.
        repeat (rewrite <- List.app_assoc in *).
        apply List.in_or_app. right.
        apply List.in_or_app. right.
        apply List.in_or_app. right.
        apply List.in_or_app. right.
        apply List.in_or_app. right.
        apply List.in_or_app. right.
        apply List.in_or_app. left.
        eapply in_rstream_labels; eauto.
  }
  eapply not_appears_none; eauto.
Qed.

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
  (* S_SwapReads *)
  - destruct n as [k' v'].
    tsod.
    + destruct os2.
      *
      {
      inv Hsame5. inv H. apply List.app_inv_head in H3. inv H3.
      got.
      - instantiate (1:=C (b0 ++ << N k' v' e; l' ->> pfold f' t'0 ks' :: l0 ->> pfold f0 (t_app (t_app f0 v') t0) (remove Nat.eq_dec k' ks0) :: os3 >> :: b3) os0 rs0 term0).
        one_step. eapply S_SwapReads with (os1:=[]); crush.
      - instantiate (1:=C (b0 ++ << N k' v' e; l' ->> pfold f' t'0 ks' :: l0 ->> pfold f0 (t_app (t_app f0 v') t0) (remove Nat.eq_dec k' ks0) :: os3 >> :: b3) os0 rs0 term0).
        simpl in *.
        exists 3.
        eapply Step.
        instantiate (1:=C (b0 ++ << N k' v' e; l0 ->> pfold f0 t0 ks0 :: l' ->> pfold f' t'0 ks' :: os3 >> :: b3) os0 rs0 term0).
        eapply S_SwapReads with (os1:=[]); eauto.
        eapply no_dep_backwards' with (os1:=[]); eauto.
        eapply no_dep_backwards with (os1:=[]); eauto.
        eapply Step.
        eapply S_PFold; eauto.
        eapply Step.
        instantiate (1:=C (b0 ++ << N k' v' e; l' ->> pfold f' t'0 ks' :: l0 ->> pfold f0 (t_app (t_app f0 v') t0) (remove Nat.eq_dec k' ks0) :: os3 >> :: b3) os0 rs0 term0).
        eapply S_SwapReads with (os1:=[]); eauto.
        eauto.
      - crush.
      }
      * inv Hsame5.
      {
      got.
      - instantiate (1:=C (b0 ++ << N k' v' es; (l ->> pfold f (t_app (t_app f v') t') (remove Nat.eq_dec k' ks) :: os2) ++ l' ->> pfold f' t'0 ks' :: l0 ->> pfold f0 t0 ks0 :: os3 >> :: b3) os0 rs0 term0).
        one_step. eapply S_SwapReads; crush.
      - instantiate (1:=C (b0 ++ << N k' v' es; l ->> pfold f (t_app (t_app f v') t') (remove Nat.eq_dec k' ks) :: os2 ++ l' ->> pfold f' t'0 ks' :: l0 ->> pfold f0 t0 ks0 :: os3 >> :: b3) os0 rs0 term0).
        one_step. inv H. apply List.app_inv_head in H3; inv H3. eapply S_PFold; crush.
      - crush.
      }
    + destruct Hfirst as [b' [b'' [b''']]].
      tu1.
      got.
      * instantiate (1:=C ((b' ++ << N k t es; l ->> pfold f (t_app (t_app f t) t') (remove Nat.eq_dec k ks) :: os1 >> :: b'') ++ << N k' v' e; os2 ++ l' ->> pfold f' t'0 ks' :: l0 ->> pfold f0 t0 ks0 :: os3 >> :: b3) os0 rs0 term0).
        one_step; eapply S_SwapReads; eauto; crush.
      * instantiate (1:=C (b' ++ << N k t es; l ->> pfold f (t_app (t_app f t) t') (remove Nat.eq_dec k ks) :: os1 >> :: b'' ++ << N k' v' e; os2 ++ l' ->> pfold f' t'0 ks' :: l0 ->> pfold f0 t0 ks0 :: os3 >> :: b3) os0 rs0 term0).
        eauto.
      * crush.
    + destruct Hsecond as [b' [b'' [b''']]].
      tu2.
      got.
      * instantiate (1:=C (b0 ++ << N k' v' e; os2 ++ l' ->> pfold f' t'0 ks' :: l0 ->> pfold f0 t0 ks0 :: os3 >> :: b'' ++ << N k t es; l ->> pfold f (t_app (t_app f t) t') (remove Nat.eq_dec k ks) :: os1 >> :: b''') os0 rs0 term0).
        eauto.
      * instantiate (1:=C ((b0 ++ << N k' v' e; os2 ++ l' ->> pfold f' t'0 ks' :: l0 ->> pfold f0 t0 ks0 :: os3 >> :: b'') ++ << N k t es; l ->> pfold f (t_app (t_app f t) t') (remove Nat.eq_dec k ks) :: os1 >> :: b''') os0 rs0 term0).
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

Lemma lfree_subst_preservation : forall t2 l x T t1,
  lappears_free_in l (#[ x := t1] t2) ->
  lappears_free_in l (t_app (t_abs x T t2) t1).
Proof using.
  induction t2; intros; simpl in *; try solve [inv H; eauto].
  - destruct (eqb_string x s).
    + auto.
    + inv H.
  - inv H.
    + eapply IHt2_1 in H2.
      inv H2; eauto. inv H1; eauto.
    + eapply IHt2_2 in H2.
      inv H2; eauto. inv H1; eauto.
  - inv H.
    + destruct (eqb_string x s); auto. eapply IHt2 in H2. inv H2; eauto. inv H1; eauto.
  - inv H.
    + eapply IHt2_1 in H2.
      inv H2; eauto. inv H1; eauto.
    + eapply IHt2_2 in H2.
      inv H2; eauto. inv H1; eauto.
  - inv H.
    + eapply IHt2 in H2.
      inv H2; eauto. inv H1; eauto.
  - inv H.
    + eapply IHt2_1 in H2.
      inv H2; eauto. inv H1; eauto.
    + eapply IHt2_2 in H2.
      inv H2; eauto. inv H1; eauto.
    + eapply IHt2_3 in H2.
      inv H2; eauto. inv H1; eauto.
  - inv H.
    + eapply IHt2_1 in H2.
      inv H2; eauto. inv H1; eauto.
    + eapply IHt2_2 in H2.
      inv H2; eauto. inv H1; eauto.
  - inv H.
    + eapply IHt2_1 in H2.
      inv H2; eauto. inv H1; eauto.
    + eapply IHt2_2 in H2.
      inv H2; eauto. inv H1; eauto.
  - inv H.
    + eapply IHt2_1 in H2.
      inv H2; eauto. inv H1; eauto.
    + eapply IHt2_2 in H2.
      inv H2; eauto. inv H1; eauto.
    + eapply IHt2_3 in H2.
      inv H2; eauto. inv H1; eauto.
  - inv H.
    + eapply IHt2 in H2.
      inv H2; eauto. inv H1; eauto.
  - inv H.
    + eapply IHt2 in H2.
      inv H2; eauto. inv H1; eauto.
  - inv H.
    + eapply IHt2 in H2.
      inv H2; eauto. inv H1; eauto.
  - inv H.
    + eapply IHt2 in H2.
      inv H2; eauto. inv H1; eauto.
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
Qed.

Lemma lfree_preservation : forall t rs t' os l,
  FRf t rs ==> FRt t' os ->
  not (lappears_free_in l t) ->
  not (lappears_free_in l t').
Proof using.
  induction t; intros; try solve [inv H].
  - inv H.
    + intro. apply H0. apply lfree_subst_preservation; auto.
    + apply IHt1 with (l:=l) in H2; auto.
      intro. inv H; auto.
    + apply IHt2 with (l:=l) in H7; auto.
      intro. inv H; auto.
  - inv H.
    + apply IHt1 with (l:=l) in H2; auto.
      intro. inv H; auto.
    + apply IHt2 with (l:=l) in H7; auto.
      intro. inv H; auto.
  - inv H.
    + intro. inv H; auto.
    + apply IHt with (l:=l) in H2; auto.
      intro. inv H; auto.
  - inv H.
    + intro. inversion H. eapply fresh_labels; eauto.
    + apply IHt1 with (l:=l0) in H2; auto.
      intro. inv H; auto.
    + apply IHt2 with (l:=l0) in H9; auto.
      intro. inv H; auto.
    + apply IHt3 with (l:=l0) in H10; auto.
      intro. inv H; auto.
  - inv H.
    + intro. inversion H. eapply fresh_labels; eauto.
    + apply IHt1 with (l:=l0) in H2; auto.
      intro. inv H; auto.
    + apply IHt2 with (l:=l0) in H8; auto.
      intro. inv H; auto.
  - inv H.
    + intro. inversion H. eapply fresh_labels; eauto.
    + apply IHt1 with (l:=l0) in H2; auto.
      intro. inv H; auto.
    + apply IHt2 with (l:=l0) in H8; auto.
      intro. inv H; auto.
  - inv H.
    + apply IHt1 with (l:=l) in H2; auto.
      intro. inv H; auto.
    + apply IHt2 with (l:=l) in H8; auto.
      intro. inv H; auto.
    + apply IHt3 with (l:=l) in H9; auto.
      intro. inv H; auto.
  - inv H.
    + apply IHt with (l:=l) in H2; auto.
      intro. inv H; auto.
    + intro. inv H; auto.
  - inv H.
    + apply IHt with (l:=l) in H2; auto.
      intro. inv H; auto.
    + intro. inv H; auto.
  - inv H.
    + apply IHt with (l:=l) in H2; auto.
      intro. inv H; auto.
    + intro. inv H; auto.
  - inv H.
    + intro. inv H; auto. inv H4; auto. inv H3; auto. inv H3.
    + apply IHt with (l:=l) in H2; auto.
      intro. inv H; auto.
Qed.

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
    + gotw (C (<< N k t es; (os ++ l ->> pfold f t1' ks :: os') ++ [l0 ->> op] >> :: b') os'0 rs term); eauto.
      * rewrite <- List.app_assoc. rewrite <- List.app_comm_cons. eapply S_LoadPFold with (b1:=[]); eauto; crush.
    + got.
      * instantiate (1:=(C (<< n1; os2 ++ [l0 ->> op] >> :: b1 ++ << N k t es; os ++ l ->> pfold f t1' ks :: os' >> :: b2) os'0 rs term)).
        one_step; eapply S_First; eauto; crush.
      * instantiate (1:=(C (<< n1; os2 ++ [l0 ->> op] >> :: b1 ++ << N k t es; os ++ l ->> pfold f t1' ks :: os' >> :: b2) os'0 rs term)).
        one_step; eapply S_LoadPFold; eauto; crush.
      * crush.
  (* S_Add *)
  - got.
    + instantiate (1:=C (<< N k0 v t_ks_nil; [] >> :: b1 ++ << N k t es; os ++ l ->> pfold f t1' ks :: os' >> :: b2) os'0 (l0 ->>> final H :: rs) term).
      one_step; eapply S_Add; eauto.
    + instantiate (1:=C ((<< N k0 v t_ks_nil; [] >> :: b1) ++ << N k t es; os ++ l ->> pfold f t1' ks :: os' >> :: b2) os'0 (l0 ->>> final H :: rs) term).
      one_step; eapply S_LoadPFold; eauto; crush.
    + crush.
  (* S_PMap *)
  - tsod.
    + destruct os.
      * inv Hsame5.
      * inv Hsame5.
        got.
        { instantiate (1:=C (b0 ++ << N k0 (t_app f0 v) es; l0 ->> pmap f0 (remove Nat.eq_dec k0 ks0) :: os ++ l ->> pfold f t1' ks :: os' >> :: b3) os1 rs term).
          one_step; eapply S_PMap; eauto; crush. }
        { instantiate (1:=C (b0 ++ << N k0 (t_app f0 v) es; (l0 ->> pmap f0 (remove Nat.eq_dec k0 ks0) :: os) ++ l ->> pfold f t1' ks :: os' >> :: b3) os1 rs term).
          fsame. one_step; eapply S_LoadPFold; eauto; crush. }
        { crush. }
    + destruct Hfirst as [b' [b'' [b''']]].
      tu1.
      got.
      * instantiate (1:=C ((b' ++ << N k t es; os ++ l ->> pfold f t1' ks :: os' >> :: b'') ++ << N k0 (t_app f0 v) es0; l0 ->> pmap f0 (remove Nat.eq_dec k0 ks0) :: os1'' >> :: b3) os1 rs term).
        one_step; eapply S_PMap; eauto; crush.
      * instantiate (1:=C ((b' ++ << N k t es; os ++ l ->> pfold f t1' ks :: os' >> :: b'') ++ << N k0 (t_app f0 v) es0; l0 ->> pmap f0 (remove Nat.eq_dec k0 ks0) :: os1'' >> :: b3) os1 rs term).
        one_step; eapply S_LoadPFold; eauto; crush.
      * crush.
    + destruct Hsecond as [b' [b'' [b''']]].
      tu2.
      got.
      * instantiate (1:=C (b0 ++ << N k0 (t_app f0 v) es0; l0 ->> pmap f0 (remove Nat.eq_dec k0 ks0) :: os1'' >> :: b'' ++ << N k t es; os ++ l ->> pfold f t1' ks :: os' >> :: b''') os1 rs term).
        one_step; eapply S_PMap; eauto; crush.
      * instantiate (1:=C ((b0 ++ << N k0 (t_app f0 v) es0; l0 ->> pmap f0 (remove Nat.eq_dec k0 ks0) :: os1'' >> :: b'') ++ << N k t es; os ++ l ->> pfold f t1' ks :: os' >> :: b''') os1 rs term).
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
        { instantiate (1:=C (b0 ++ [<< N k t es; os ++ l ->> pfold f t1' ks :: os' >>]) os1 (l0 ->>> final H :: rs) term).
          one_step; eapply S_Last; eauto; crush. }
        { instantiate (1:=C (b0 ++ [<< N k t es; os ++ l ->> pfold f t1' ks :: os' >>]) os1 (l0 ->>> final H :: rs) term).
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
      * instantiate (1:=C ((b1 ++ << N k t es; os ++ l ->> pfold f t1' ks :: os' >> :: x0) ++ [<< n1; os1' >>]) os1 (l0 ->>> final H :: rs) term).
        one_step; eapply S_Last; eauto; crush.
      * instantiate (1:=C ((b1 ++ << N k t es; os ++ l ->> pfold f t1' ks :: os' >> :: x0) ++ [<< n1; os1' >>]) os1 (l0 ->>> final H :: rs) term).
        one_step; eapply S_LoadPFold; eauto; crush.
      * crush.
  (* S_FusePMap *)
  - destruct n as [k' t']. tsod'''.
    + osod.
      * inv Hsame. destruct H2. crush.
      * destruct Hfirst as [os''0 [os'' [os''']]].
        ou1.
        got.
        { instantiate (1:=C (b0 ++ << N k' t' e; (os''0 ++ l ->> pfold f t1' ks :: os'') ++ l' ->> pmap (pmap_compose f' f0) ks0 :: os3 >> :: b3) os1 (l0 ->>> 0 :: rs) term).
          one_step; eapply S_FusePMap; eauto; crush. }
        { instantiate (1:=C (b0 ++ << N k' t' e; (os''0 ++ l ->> pfold f t1' ks :: os'') ++ l' ->> pmap (pmap_compose f' f0) ks0 :: os3 >> :: b3) os1 (l0 ->>> 0 :: rs) term).
          one_step; eapply S_LoadPFold; eauto; crush. }
        { crush. }
      * destruct Hsecond as [os''0 [os'' [os''']]].
        ou2.
        {
        destruct os''; inv H1; simpl in *.
        - got.
          + instantiate (1:=C (b0 ++ << N k' t' e; os2 ++ l' ->> pmap (pmap_compose f' f0) ks0 :: os'' ++ l ->> pfold f t1' ks :: os''' >> :: b3) os1 (l0 ->>> 0 :: rs) term).
            one_step; eapply S_FusePMap; eauto; crush.
          + instantiate (1:=C (b0 ++ << N k' t' e; (os2 ++ l' ->> pmap (pmap_compose f' f0) ks0 :: os'') ++ l ->> pfold f t1' ks :: os''' >> :: b3) os1 (l0 ->>> 0 :: rs) term).
            one_step; eapply S_LoadPFold; eauto; crush.
          + crush.
        }
    + destruct Hfirst as [b' [b'' [b''']]].
      tu1.
      got.
      * instantiate (1:=C ((b' ++ << N k t es; os ++ l ->> pfold f t1' ks :: os' >> :: b'') ++ << N k' t' e; os2 ++ l' ->> pmap (pmap_compose f' f0) ks0 :: os3 >> :: b3) os1 (l0 ->>> 0 :: rs) term).
        one_step; eapply S_FusePMap; eauto; crush.
      * instantiate (1:=C ((b' ++ << N k t es; os ++ l ->> pfold f t1' ks :: os' >> :: b'') ++ << N k' t' e; os2 ++ l' ->> pmap (pmap_compose f' f0) ks0 :: os3 >> :: b3) os1 (l0 ->>> 0 :: rs) term).
        one_step; eapply S_LoadPFold; eauto; crush.
      * crush.
    + destruct Hsecond as [b' [b'' [b''']]].
      tu2.
      got.
      * instantiate (1:=C (b0 ++ << N k' t' e; os2 ++ l' ->> pmap (pmap_compose f' f0) ks0 :: os3 >> :: b'' ++ << N k t es; os ++ l ->> pfold f t1' ks :: os' >> :: b''') os1 (l0 ->>> 0 :: rs) term).
        one_step; eapply S_FusePMap; eauto; crush.
      * instantiate (1:=C ((b0 ++ << N k' t' e; os2 ++ l' ->> pmap (pmap_compose f' f0) ks0 :: os3 >> :: b'') ++ << N k t es; os ++ l ->> pfold f t1' ks :: os' >> :: b''') os1 (l0 ->>> 0 :: rs) term).
        one_step; eapply S_LoadPFold; eauto; crush.
      * crush.
  (* S_SwapReads *)
  - destruct n as [k' t'']. tsod'''.
    + osod.
      * inv Hsame; dtr. inv H3. inv H. apply List.app_inv_head in H3. inv H3.
        gotw (C (b0 ++ << N k' t'' e; os2 ++ l' ->> pfold f' t' ks' :: l0 ->> pfold f0 t1' ks0 :: os3 >> :: b3) os1 rs term); eauto.
        eapply S_LoadPFold with (os:=os2 ++ [l' ->> pfold f' t' ks']). eauto. crush. eauto. crush.
      * destruct Hfirst as [os''0 [os'' [os''']]].
        ou1.
        got.
        { instantiate (1:=C (b0 ++ << N k' t'' e; (os''0 ++ l ->> pfold f t1' ks :: os'') ++ l' ->> pfold f' t' ks' :: l0 ->> pfold f0 t0 ks0 :: os3 >> :: b3) os1 rs term).
          one_step; eapply S_SwapReads; eauto; crush. }
        { instantiate (1:=C (b0 ++ << N k' t'' e; (os''0 ++ l ->> pfold f t1' ks :: os'') ++ l' ->> pfold f' t' ks' :: l0 ->> pfold f0 t0 ks0 :: os3 >> :: b3) os1 rs term).
          one_step; eapply S_LoadPFold; eauto; crush. }
        { crush. }
      * destruct Hsecond as [os''0 [os'' [os''']]].
        ou2.
        {
        destruct os''; inv H0; simpl in *.
        - got.
          + instantiate (1:=C (b0 ++ << N k' t'' e; os2 ++ l' ->> pfold f' t1' ks' :: l0 ->> pfold f0 t0 ks0 :: os3 >> :: b3) os1 rs term).
            one_step; eapply S_SwapReads; eauto.
            eapply lfree_preservation; eauto.
          + instantiate (1:=C (b0 ++ << N k' t'' e; os2 ++ l' ->> pfold f' t1' ks' :: l0 ->> pfold f0 t0 ks0 :: os3 >> :: b3) os1 rs term).
            one_step; eapply S_LoadPFold; eauto; crush.
          + crush.
        - got.
          + instantiate (1:=C (b0 ++ << N k' t'' e; os2 ++ l' ->> pfold f' t' ks' :: l0 ->> pfold f0 t0 ks0 :: os'' ++ l ->> pfold f t1' ks :: os''' >> :: b3) os1 rs term).
            one_step; eapply S_SwapReads; eauto.
          + instantiate (1:=C (b0 ++ << N k' t'' e; (os2 ++ l' ->> pfold f' t' ks' :: l0 ->> pfold f0 t0 ks0 :: os'') ++ l ->> pfold f t1' ks :: os''' >> :: b3) os1 rs term).
            one_step; eapply S_LoadPFold with (os:=(os2 ++ l' ->> pfold f' t' ks' :: l0 ->> pfold f0 t0 ks0 :: os'')); eauto; crush.
          + crush.
        }
    + destruct Hfirst as [b' [b'' [b''']]].
      tu1.
      got.
      * instantiate (1:=C ((b' ++ << N k t es; os ++ l ->> pfold f t1' ks :: os' >> :: b'') ++ << N k' t'' e; os2 ++ l' ->> pfold f' t' ks' :: l0 ->> pfold f0 t0 ks0 :: os3 >> :: b3) os1 rs term).
        one_step; eapply S_SwapReads; eauto; crush.
      * instantiate (1:=C (b' ++ << N k t es; os ++ l ->> pfold f t1' ks :: os' >> :: b'' ++ << N k' t'' e; os2 ++ l' ->> pfold f' t' ks' :: l0 ->> pfold f0 t0 ks0 :: os3 >> :: b3) os1 rs term).
        one_step; eapply S_LoadPFold; eauto; crush.
      * crush.
    + destruct Hsecond as [b' [b'' [b''']]].
      tu2.
      got.
      * instantiate (1:=C (b0 ++ << N k' t'' e; os2 ++ l' ->> pfold f' t' ks' :: l0 ->> pfold f0 t0 ks0 :: os3 >> :: b'' ++ << N k t es; os ++ l ->> pfold f t1' ks :: os' >> :: b''') os1 rs term).
        one_step; eapply S_SwapReads; eauto; crush.
      * instantiate (1:=C ((b0 ++ << N k' t'' e; os2 ++ l' ->> pfold f' t' ks' :: l0 ->> pfold f0 t0 ks0 :: os3 >> :: b'') ++ << N k t es; os ++ l ->> pfold f t1' ks :: os' >> :: b''') os1 rs term).
        one_step; eapply S_LoadPFold with (b1:=(b0 ++ << N k' t'' e; os2 ++ l' ->> pfold f' t' ks' :: l0 ->> pfold f0 t0 ks0 :: os3 >> :: b'')); eauto; crush.
      * crush.
  (* S_Prop *)
  - destruct n1 as [k' t']. tsod.
    + destruct os; simpl in *.
      * inv Hsame5.
        got.
        { instantiate (1:=C (b0 ++ << N k' t' e; os2 >> :: << n2; os3 ++ [l0 ->> pfold f t1' ks] >> :: b3) os1 rs term).
          fsame. one_step; eapply S_Prop; eauto; crush. }
        { instantiate (1:=C ((b0 ++ [<< N k' t' e; os2 >>]) ++ << n2; os3 ++ [l0 ->> pfold f t1' ks] >> :: b3) os1 rs term).
          destruct n2. one_step; eapply S_LoadPFold with (b1:=(b0 ++ [<< N k' t' e; os2 >>])) (os:=os3) (os':=[]); eauto; crush. }
        { crush. }
      * inv Hsame5.
        got.
        { instantiate (1:=C (b0 ++ << N k' t' e; os ++ l ->> pfold f t1' ks :: os' >> :: << n2; os3 ++ [l0 ->> op] >> :: b3) os1 rs term).
          fsame. one_step; eapply S_Prop; eauto; crush. }
        { instantiate (1:=C (b0 ++ << N k' t' e; os ++ l ->> pfold f t1' ks :: os' >> :: << n2; os3 ++ [l0 ->> op] >> :: b3) os1 rs term).
          one_step; eapply S_LoadPFold; eauto; crush. }
        { crush. }
    + destruct Hfirst as [b' [b'' [b''']]].
      tu1.
      got.
      * instantiate (1:=C ((b' ++ << N k t es; os ++ l ->> pfold f t1' ks :: os' >> :: b'') ++ << N k' t' e; os2 >> :: << n2; os3 ++ [l0 ->> op] >> :: b3) os1 rs term).
        one_step; eapply S_Prop; eauto; crush.
      * instantiate (1:=C ((b' ++ << N k t es; os ++ l ->> pfold f t1' ks :: os' >> :: b'') ++ << N k' t' e; os2 >> :: << n2; os3 ++ [l0 ->> op] >> :: b3) os1 rs term).
        one_step; eapply S_LoadPFold; eauto; crush.
      * crush.
    + destruct Hsecond as [b' [b'' [b''']]].
      tu2.
      destruct b''; inv H1; simpl in *.
      * got.
        { instantiate (1:=C (b0 ++ << N k' t' e; os2 >> :: << N k t es; (os ++ l ->> pfold f t1' ks :: os') ++ [l0 ->> op] >> :: b3) os1 rs term).
          one_step; eapply S_Prop; eauto; crush. }
        { instantiate (1:=C ((b0 ++ [<< N k' t' e; os2 >>]) ++ << N k t es; os ++ l ->> pfold f t1' ks :: os' ++ [l0 ->> op] >> :: b3) os1 rs term).
          one_step; eapply S_LoadPFold; eauto; crush. }
        { crush. }
      * got.
        { instantiate (1:=C (b0 ++ << N k' t' e; os2 >> :: << n2; os3 ++ [l0 ->> op] >> :: b'' ++ << N k t es; os ++ l ->> pfold f t1' ks :: os' >> :: b''') os1 rs term).
          one_step; eapply S_Prop; eauto; crush. }
        { instantiate (1:=C ((b0 ++ << N k' t' e; os2 >> :: << n2; os3 ++ [l0 ->> op] >> :: b'') ++ << N k t es; os ++ l ->> pfold f t1' ks :: os' >> :: b''') os1 rs term).
          one_step; eapply S_LoadPFold; eauto; crush. }
        { crush. }
  (* S_LoadPFold *)
  - tsod.
    + osod.
      * crush. inv H4. fsame.
        eapply frontend_deterministic with (b0:=b0 ++ << N k0 t0 es0; os2 ++ l0 ->> pfold f0 t2 ks0 :: os'0 >> :: b3) (os0:=os1) (os:=[]) (t':=t1'0) in tt'; eauto. crush.
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
    eapply target_same_or_different with (b1:=b1) (b2:=<< n2; os2 >> :: b2) (b3:=b0) (b4:=b3) (k:=k0) (v:=p) (k':=k) (v':=v) in H1; eauto.
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
        eapply target_unique with (b1:=x ++ [<< N k0 p e; l ->> op :: os1 >>]) (b2:=x1) (b3:=b0) (b4:=b3) in H1; eauto; crush.
        inv H2.
        {
          got.
          - instantiate (1:=C ((x ++ [<< N k0 p e; os1 >>]) ++ << N k (t_app f v) es; l0 ->> pmap f (remove Nat.eq_dec k ks) :: os1'' ++ [l ->> op] >> :: b3) os0 rs0 term0).
            one_step. eapply S_PMap; crush.
          - instantiate (1:=C (x ++ << N k0 p e; os1 >> :: << N k (t_app f v) es; (l0 ->> pmap f (remove Nat.eq_dec k ks) :: os1'') ++ [l ->> op] >> :: b3) os0 rs0 term0).
            one_step. eapply S_Prop; crush.
          - crush.
        }
      * inv H2.
        inv H.
        eapply target_unique with (b1:=x ++ << N k0 p e; l ->> op :: os1 >> :: << n2; os2 >> :: x0) (b2:=x1) (b3:=b0) (b4:=b3) in H1; eauto; crush.
        {
          got.
          - instantiate (1:=C ((x ++ << N k0 p e; os1 >> :: << n2; os2 ++ [l ->> op] >> :: x0) ++ << N k (t_app f v) es; l0 ->> pmap f (remove Nat.eq_dec k ks) :: os1'' >> :: b3) os0 rs0 term0).
            one_step. eapply S_PMap; crush.
          - instantiate (1:=C (x ++ << N k0 p e; os1 >> :: << n2; os2 ++ [l ->> op] >> :: x0 ++ << N k (t_app f v) es; l0 ->> pmap f (remove Nat.eq_dec k ks) :: os1'' >> :: b3) os0 rs0 term0).
            one_step. eapply S_Prop; crush.
          - crush.
        }
    (* First second *)
    + destruct H0. destruct H0. destruct H0.
      eapply target_unique with (b1:=b1) (b2:=<< n2; os2 >> :: b2) (b3:=x ++ << N k v es; l0 ->> pmap f ks :: os1'' >> :: x0) (b4:=x1) in H0; eauto; crush.
      inv H.
      eapply target_unique with (b1:=x) (b2:=x0 ++ << N k0 p e; l ->> op :: os1 >> :: << n2; os2 >> :: b2) (b3:=b0) (b4:=b3) in H1; eauto; crush.
      got.
      * instantiate (1:= C (b0 ++ << N k (t_app f v) es; l0 ->> pmap f (remove Nat.eq_dec k ks) :: os1'' >> :: x0 ++ << N k0 p e; os1 >> :: << n2; os2 ++ [l ->> op] >> :: b2) os0 rs0 term0).
        one_step. eapply S_PMap; crush.
      * instantiate (1:= C ((b0 ++ << N k (t_app f v) es; l0 ->> pmap f (remove Nat.eq_dec k ks) :: os1'' >> :: x0) ++ << N k0 p e; os1 >> :: << n2; os2 ++ [l ->> op] >> :: b2) os0 rs0 term0).
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
  (* S_SwapReads *)
  - destruct n1 as [k v].
    destruct n as [k' v'].
    tsod'.
    + destruct os3.
      *
      {
      simpl in *. inv Hsame5. inv H. apply List.app_inv_head in H3. inv H3.
      got.
      - instantiate (1:=C (b0 ++ << N k' v' e0; l' ->> pfold f' t' ks' :: os4 >> :: << n2; os2 ++ [l0 ->> pfold f t ks] >> :: b2) os0 rs0 term0).
        exists 0. auto.
      - instantiate (1:=C (b0 ++ << N k' v' e0; l' ->> pfold f' t' ks' :: os4 >> :: << n2; os2 ++ [l0 ->> pfold f t ks] >> :: b2) os0 rs0 term0).
        exists 2.
        eapply Step.
        instantiate (1:=C (b0 ++ << N k' v' e0; l0 ->> pfold f t ks :: l' ->> pfold f' t' ks' :: os4 >> :: << n2; os2 >> :: b2) os0 rs0 term0).
        eapply S_SwapReads with (os1:=[]) (b2:=<<n2; os2>>::b2); eauto.
        eapply no_dep_backwards' with (os1:=[]); eauto.
        eapply no_dep_backwards with (os1:=[]); eauto.
        eapply Step.
        eapply S_Prop; eauto. simpl. auto.
        auto.
      - crush.
      }
      * inv Hsame5.
      {
      inv H. apply List.app_inv_head in H3. inv H3. got.
      - instantiate (1:=C (b0 ++ << N k' v' e0; os3 ++ l' ->> pfold f' t' ks' :: l0 ->> pfold f t ks :: os4 >> :: << n2; os2 ++ [l ->> op] >> :: b2) os0 rs0 term0).
        one_step. eapply S_SwapReads; crush.
      - instantiate (1:=C (b0 ++ << N k' v' e0; os3 ++ l' ->> pfold f' t' ks' :: l0 ->> pfold f t ks :: os4 >> :: << n2; os2 ++ [l ->> op] >> :: b2) os0 rs0 term0).
        one_step. eapply S_Prop; eauto.
      - crush.
      }
    + destruct Hfirst as [b' [b'' [b''']]].
      destruct b''; simpl in *.
      * eapply target_unique with (b1:=b1) (b2:=<< n2; os2 >> :: b2) (b3:=b') (b4:=<< N k' v' e0; os3 ++ l0 ->> pfold f t ks :: l' ->> pfold f' t' ks' :: os4 >> :: b''') in H0; eauto; crush.
        inv H4. inv H.
        eapply target_unique with (b1:=b' ++ [<< N k v e; l ->> op :: os1 >>]) (b2:=b''') (b3:=b0) (b4:=b3) in H3; eauto; crush.
        got.
        { instantiate (1:=C ((b' ++ [<< N k v e; os1 >>]) ++ << N k' v' e0; os3 ++ l' ->> pfold f' t' ks' :: l0 ->> pfold f t ks :: os4 ++ [l ->> op] >> :: b3) os0 rs0 term0).
          one_step. eapply S_SwapReads; eauto; crush. }
        { instantiate (1:=C (b' ++ << N k v e; os1 >> :: << N k' v' e0; (os3 ++ l' ->> pfold f' t' ks' :: l0 ->> pfold f t ks :: os4) ++ [l ->> op] >> :: b3) os0 rs0 term0).
          one_step. eapply S_Prop; eauto; crush. }
        { crush. }
      * eapply target_unique with (b1:=b1) (b2:=<< n2; os2 >> :: b2) (b3:=b') (b4:=s :: b'' ++ << N k' v' e0; os3 ++ l0 ->> pfold f t ks :: l' ->> pfold f' t' ks' :: os4 >> :: b''') in H0; eauto; crush.
        inv H.
        eapply target_unique with (b1:=b' ++ << N k v e; l ->> op :: os1 >> :: <<n2;os2>>::b'') (b2:=b''') (b3:=b0) (b4:=b3) in H3; eauto; crush.
        got.
        { instantiate (1:=C ((b' ++ << N k v e; os1 >> :: << n2; os2 ++ [l ->> op] >> :: b'') ++ << N k' v' e0; os3 ++ l' ->> pfold f' t' ks' :: l0 ->> pfold f t ks :: os4 >> :: b3) os0 rs0 term0).
          one_step. eapply S_SwapReads; eauto; crush. }
        { instantiate (1:=C (b' ++ << N k v e; os1 >> :: << n2; os2 ++ [l ->> op] >> :: b'' ++ << N k' v' e0; os3 ++ l' ->> pfold f' t' ks' :: l0 ->> pfold f t ks :: os4 >> :: b3) os0 rs0 term0).
          one_step. eapply S_Prop; eauto; crush. }
        { crush. }
    + destruct Hsecond as [b' [b'' [b''']]].
      tu2.
      got.
      * instantiate (1:=C (b0 ++ << N k' v' e0; os3 ++ l' ->> pfold f' t' ks' :: l0 ->> pfold f t ks :: os4 >> :: b'' ++ << N k v e; os1 >> :: << n2; os2 ++ [l ->> op] >> :: b2) os0 rs0 term0).
        eauto.
      * instantiate (1:=C ((b0 ++ << N k' v' e0; os3 ++ l' ->> pfold f' t' ks' :: l0 ->> pfold f t ks :: os4 >> :: b'') ++ << N k v e; os1 >> :: << n2; os2 ++ [l ->> op] >> :: b2) os0 rs0 term0).
        one_step; eapply S_Prop; eauto; crush.
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
    * gotw (C (<< N k (t_app f v) es; l0 ->> pmap f (remove Nat.eq_dec k ks) :: os1'' ++ [l ->> op] >> :: b2)  os' rs0 term).
      { inv H1; eapply S_PMap with (b1:=[]); crush. }
      { inv H1; eapply S_First with (os1:=l0 ->> pmap f (remove Nat.eq_dec k ks) :: os1''); crush. }
      { crush. }
    * gotw (C (<< n1; os1 ++ [l ->> op] >> :: b1 ++ << N k (t_app f v) es; l0 ->> pmap f (remove Nat.eq_dec k ks) :: os1'' >> :: b2) os' rs0 term).
      { inv H1. eapply S_PMap with (b1:=<< n1; os1 ++ [l ->> op] >> :: b1); crush. }
      { inv H1. eapply S_First; crush. }
      { crush. }
  (* S_Last *)
  - crush.
    {
    destruct b1; eapply ex_intro; eapply ex_intro; intros.
    (* b1 = [] *)
    - split; try split.
      + simpl in *. instantiate (1 := C [<< n1; os1' ++ [l ->> op]>>] os' (l0 ->>> final H :: rs0) term).
        inversion H2.
        one_step; eapply S_Last with (b1 := []); crush.
      + simpl in *. instantiate (1 := C [<< n1; os1' ++ [l ->> op]>>] os' (l0 ->>> final H :: rs0) term).
        inversion H2.
        one_step; eapply S_First; crush.
      + crush.
    (* b1 != [] *)
    - split; try split.
      + instantiate (1 := C (<< n1; os1 ++ [l ->> op] >> :: b1 ++ [<< n0; os1' >>]) os' (l0 ->>> final H :: rs0) term).
        inversion H2.
        one_step; eapply S_Last with (b1 := << n1; os1 ++ [l ->> op] >> :: b1); crush.
      + instantiate (1 := C (<< n1; os1 ++ [l ->> op] >> :: b1 ++ [<< n0; os1' >>]) os' (l0 ->>> final H :: rs0) term).
        inversion H2.
        one_step; eapply S_First; crush.
      + crush.
    }
  (* S_FusePMap *)
  - destruct b1; simpl in *.
    (* b1 = [] *)
    * gotw (C (<< n; os0 ++ l' ->> pmap (pmap_compose f' f) ks :: os2 ++ [l ->> op] >> :: b2) os' (l0 ->>> 0 :: rs0) term).
      { inv H2. eapply S_FusePMap with (b1:=[]); crush. }
      { inv H2. assert (os0 ++ l' ->> pmap (pmap_compose f' f) ks :: os2 ++ [l ->> op] = (os0 ++ l' ->> pmap (pmap_compose f' f) ks :: os2) ++ [l ->> op]) by crush. rewrite H1. eapply S_First; crush. }
      { crush. }
    (* b1 != [] *)
    * gotw (C (<< n1; os1 ++ [l ->> op] >> :: b1 ++ << n; os0 ++ l' ->> pmap (pmap_compose f' f) ks :: os2 >> :: b2) os' (l0 ->>> 0 :: rs0) term).
      { inv H2. eapply S_FusePMap with (b1:=<< n1; os1 ++ [l ->> op] >> :: b1); crush. }
      { inv H2. eapply S_First; crush. }
      { crush. }
  (* S_SwapReads *)
  - destruct b1; simpl in *.
    (* b1 = [] *)
    * inv H. inv H3.
      gotw (C (<< n; os0 ++ l' ->> pfold f' t' ks' :: l0 ->> pfold f t ks :: os2 ++ [l ->> op] >> :: b2) os' rs0 term).
      { eapply S_SwapReads with (b1:=[]); crush. }
      { replace (os0 ++ l' ->> pfold f' t' ks' :: l0 ->> pfold f t ks :: os2 ++ [l ->> op]) with ((os0 ++ l' ->> pfold f' t' ks' :: l0 ->> pfold f t ks :: os2) ++ [l ->> op]) by crush. eapply S_First; crush. }
      { crush. }
    (* b1 != [] *)
    * inv H3.
      gotw (C (<< n1; os1 ++ [l ->> op] >> :: b1 ++ << n; os0 ++ l' ->> pfold f' t' ks' :: l0 ->> pfold f t ks :: os2 >> :: b2) os' rs0 term); eauto.
      { eapply S_SwapReads with (b1:=<< n1; os1 ++ [l ->> op] >> :: b1); crush. }
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
  - gotw (C (<< N k0 v0 t_ks_nil; [] >> :: b1 ++ << N k (t_app f v) es; l ->> pmap f (remove Nat.eq_dec k ks) :: os1'' >> :: b2) os' (l0 ->>> final H :: rs0) term).
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
        apply target_unique with (os:=l ->> pmap f ks :: os1'') (k:=k) (v:=v) (b1:=b1) (b2:=b2) (b3:=x) (b4:=x0 ++ << N k0 v0 es0; l0 ->> pmap f0 ks0 :: os1''0 >> :: x1) (os0:=os0) (rs0:=rs0) (t0:=term) (b:=b1 ++ << N k v es; l ->> pmap f ks :: os1'' >> :: b2) in H0; crush.
        inv H.
        apply target_unique with (os:=l0 ->> pmap f0 ks0 :: os1''0) (k:=k0) (v:=v0) (b1:=x ++ << N k v es; l ->> pmap f ks :: os1'' >> :: x0) (b2:=x1) (b3:=b3) (b4:=b4) (os0:=os0) (rs0:=rs0) (t0:=term) (b:=x ++ << N k v es; l ->> pmap f ks :: os1'' >> :: x0 ++ << N k0 v0 es0; l0 ->> pmap f0 ks0 :: os1''0 >> :: x1) in H1; crush.
        got.
        * instantiate (1:=C ((x ++ << N k (t_app f v) es; l ->> pmap f (remove Nat.eq_dec k ks) :: os1'' >> :: x0) ++ << N k0 (t_app f0 v0) es0; l0 ->> pmap f0 (remove Nat.eq_dec k0 ks0) :: os1''0 >> :: b4) os0 rs0 term).
          one_step. eapply S_PMap; crush.
        * instantiate (1:=C (x ++ << N k (t_app f v) es; l ->> pmap f (remove Nat.eq_dec k ks) :: os1'' >> :: x0 ++ << N k0 (t_app f0 v0) es0; l0 ->> pmap f0 (remove Nat.eq_dec k0 ks0) :: os1''0 >> :: b4) os0 rs0 term).
          one_step. eapply S_PMap; crush.
        * crush.
      (* First second *)
      + destruct H0; destruct H0; destruct H0.
        apply target_unique with (os:=l ->> pmap f ks :: os1'') (k:=k) (v:=v) (b1:=b1) (b2:=b2) (b3:=x ++ << N k0 v0 es0; l0 ->> pmap f0 ks0 :: os1''0 >> :: x0) (b4:=x1) (os0:=os0) (rs0:=rs0) (es:=es) (t0:=term) (b:=b1 ++ << N k v es; l ->> pmap f ks :: os1'' >> :: b2) in H0; crush.
        inv H.
        eapply target_unique with (os:=l0 ->> pmap f0 ks0 :: os1''0) (k:=k0) (v:=v0) (b1:=x) (b2:=x0 ++ << N k v es; l ->> pmap f ks :: os1'' >> :: x1) (b3:=b3) (b4:=b4) (os0:=os0) (rs0:=rs0) (t0:=term) in H1; eauto.
        got.
        * instantiate (1:=C (b3 ++ << N k0 (t_app f0 v0) es0; l0 ->> pmap f0 (remove Nat.eq_dec k0 ks0) :: os1''0 >> :: x0 ++ << N k (t_app f v) es; l ->> pmap f (remove Nat.eq_dec k ks) :: os1'' >> :: x1) os0 rs0 term).
          one_step. eapply S_PMap; crush.
        * instantiate (1:=C ((b3 ++ << N k0 (t_app f0 v0) es0; l0 ->> pmap f0 (remove Nat.eq_dec k0 ks0) :: os1''0 >> :: x0) ++ << N k (t_app f v) es; l ->> pmap f (remove Nat.eq_dec k ks) :: os1'' >> :: x1) os0 rs0 term).
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
      + instantiate (1:=C ((b1 ++ << N k (t_app f v) es; l ->> pmap f (remove Nat.eq_dec k ks) :: os1'' >> :: x0) ++ [<< n1; os1' >>]) os0 (l0 ->>> final Hnot :: rs0) term).
        one_step. eapply S_Last; crush.
      + instantiate (1:=C (b1 ++ << N k (t_app f v) es; l ->> pmap f (remove Nat.eq_dec k ks) :: os1'' >> :: x0 ++ [<< n1; os1' >>]) os0 (l0 ->>> final Hnot :: rs0) term).
        one_step. eapply S_PMap; crush.
      + crush.
    }
  (* S_FusePMap *)
  - rename H into Hnot.
    rename H0 into H.
    rename H2 into H1.
    destruct n.
    eapply target_same_or_different with (b1:=b1) (b2:=b2) (b3:=b0) (b4:=b3) (k:=k) (v:=v) (k':=k0) (v':=p) in H1; eauto.
    destruct H1; try destruct H0.
    (* Same target *)
    + destruct H1. destruct H2. destruct H3. subst.
      fsame.
      destruct os1.
      * simpl in *.
        inv H4.
        {
        destruct b3.
        - assert (exists n m t', fstar n (t_app f' (t_app f0 p)) (l' ->>> 0 :: l0 ->>> 0 :: rs0) t' /\ fstar m (t_app (pmap_compose f' f0) p) (l' ->>> 0 :: l0 ->>> 0 :: rs0) t').
          {
            apply pmap_compose_comm.
            - inv WT; dtr. inv H1. wtbdist. inv H3. inv H15. inv H7. inv H15. eauto.
            - inv WT; dtr. inv H1. wtbdist. inv H3. inv H15. inv H7. inv H9. eauto.
            - inv WT; dtr. inv H1. wtbdist. inv H3. inv H15. inv H7. inv H15. eauto.
            - inv WT; dtr. inv H1. wtbdist. inv H3. inv H15. inv H7. inv H9. eauto.
            - apply to_value.
          }
          dtr. rename H into star1. rename H0 into star2.
          assert (Hnot' : not_fold_or_done (pmap f' (remove Nat.eq_dec k0 ks0))) by eauto.
          got.
          + instantiate (1:=C (b0 ++ [<< N k0 x1 e; os2 >>]) os0 (l' ->>> final _ :: l0 ->>> 0 :: rs0) term).
            apply ex_intro with (3 + x).
            eapply Step.
            instantiate (1:=C (b0 ++ [<< N k0 (t_app f0 p) e; l' ->> pmap f' ks0 :: os2 >>]) os0 (l0 ->>> _ :: rs0) term).
            eapply S_Last; crush.
            apply List.remove_In in H. assumption.
            eapply Step.
            instantiate (1:=C (b0 ++ [<< N k0 (t_app f' (t_app f0 p)) e; l' ->> pmap f' (remove Nat.eq_dec k0 ks0) :: os2 >>]) os0 (l0 ->>> final _ :: rs0) term).
            eapply S_PMap; crush.
            instantiate (1:=Hnot); crush.
            eapply Step.
            eapply S_Last with (b:=b0 ++ [<< N k0 (t_app f' (t_app f0 p)) e; l' ->> pmap f' (remove Nat.eq_dec k0 ks0) :: os2 >>]); eauto.
            crush.
            apply List.remove_In in H. assumption.
            apply fstar_into_star_load with (b1:=b0) (k:=k0) (b2:=[]) (es:=e) (os:=os2) (os0:=os0) (rs:=l' ->>> 0 :: l0 ->>> 0 :: rs0) (t0:=term) in star1.
            simpl. instantiate (1:=Hnot'). simpl. auto.
          + instantiate (1:=C (b0 ++ [<< N k0 x1 e; os2 >>]) os0 (l' ->>> final _ :: l0 ->>> 0 :: rs0) term).
            apply ex_intro with (2 + x0).
            eapply Step.
            eapply S_PMap; crush.
            eapply Step.
            eapply S_Last with (op:=pmap (pmap_compose f' f0) (remove Nat.eq_dec k0 ks0)); crush.
            apply List.remove_In in H. assumption.
            apply fstar_into_star_load with (b1:=b0) (k:=k0) (b2:=[]) (es:=e) (os:=os2) (os0:=os0) (rs:=l' ->>> 0 :: l0 ->>> 0 :: rs0) (t0:=term) in star2.
            simpl. instantiate (1:=Hnot'). simpl. auto.
          + crush.
        - destruct s.
          assert (exists n m t', fstar n (t_app f' (t_app f0 p)) (l0 ->>> 0 :: rs0) t' /\ fstar m (t_app (pmap_compose f' f0) p) (l0 ->>> 0 :: rs0) t').
          {
            apply pmap_compose_comm.
            - inv WT; dtr. inv H1. wtbdist. inv H3. inv H15. inv H7. inv H15. eauto.
            - inv WT; dtr. inv H1. wtbdist. inv H3. inv H15. inv H7. inv H9. eauto.
            - inv WT; dtr. inv H1. wtbdist. inv H3. inv H15. inv H7. inv H15. eauto.
            - inv WT; dtr. inv H1. wtbdist. inv H3. inv H15. inv H7. inv H9. eauto.
            - apply to_value.
          }
          dtr. rename H into star1. rename H0 into star2.
          assert (Hnot' : not_fold_or_done (pmap f' (remove Nat.eq_dec k0 ks0))) by eauto.
          got.
          + instantiate (1:=C (b0 ++ << N k0 x1 e; os2 >> :: << n; l ++ [l' ->> pmap (pmap_compose f' f0) (remove Nat.eq_dec k0 ks0)] >> :: b3) os0 (l0 ->>> final _ :: rs0) term).
            apply ex_intro with (4+x).
            eapply Step.
            instantiate (1:=C (b0 ++ << N k0 (t_app f0 p) e; l' ->> pmap f' ks0 :: os2 >> :: << n; l ++ [l0 ->> pmap f0 (remove Nat.eq_dec k0 ks0)] >> :: b3) os0 rs0 term).
            eapply S_Prop; crush.
            apply List.remove_In in H. assumption.
            eapply Step.
            instantiate (1:=C (b0 ++ << N k0 (t_app f' (t_app f0 p)) e; l' ->> pmap f' (remove Nat.eq_dec k0 ks0) :: os2 >> :: << n; l ++ [l0 ->> pmap f0 (remove Nat.eq_dec k0 ks0)] >> :: b3) os0 rs0 term).
            eapply S_PMap; crush.
            eapply Step.
            instantiate (1:=C (b0 ++ << N k0 (t_app f' (t_app f0 p)) e; os2 >> :: << n; (l ++ [l0 ->> pmap f0 (remove Nat.eq_dec k0 ks0)]) ++ [l' ->> pmap f' (remove Nat.eq_dec k0 ks0)] >> :: b3) os0 rs0 term).
            eapply S_Prop; crush.
            apply List.remove_In in H. assumption.
            eapply Step.
            assert (b0 ++ << N k0 (t_app f' (t_app f0 p)) e; os2 >> :: << n; (l ++ [l0 ->> pmap f0 (remove Nat.eq_dec k0 ks0)]) ++ [l' ->> pmap f' (remove Nat.eq_dec k0 ks0)] >> :: b3 = (b0 ++ [<< N k0 (t_app f' (t_app f0 p)) e; os2 >>]) ++ << n; l ++ l0 ->> pmap f0 (remove Nat.eq_dec k0 ks0) :: l' ->> pmap f' (remove Nat.eq_dec k0 ks0) :: [] >> :: b3) by crush.
            rewrite H.
            eapply S_FusePMap; crush.
            apply fstar_into_star_load with (b1:=b0) (k:=k0) (b2:=<< n; l ++ [l' ->> pmap (pmap_compose f' f0) (remove Nat.eq_dec k0 ks0)] >> :: b3) (es:=e) (os:=os2) (os0:=os0) (rs:=l0 ->>> 0 :: rs0) (t0:=term) in star1.
            simpl. instantiate (1:=Hnot'). simpl. crush.
          + instantiate (1:=C (b0 ++ << N k0 x1 e; os2 >> :: << n; l ++ [l' ->> pmap (pmap_compose f' f0) (remove Nat.eq_dec k0 ks0)] >> :: b3) os0 (l0 ->>> 0 :: rs0) term).
            apply ex_intro with (2 + x0).
            eapply Step.
            instantiate (1:=C (b0 ++ << N k0 (t_app (pmap_compose f' f0) p) e; l' ->> pmap (pmap_compose f' f0) (remove Nat.eq_dec k0 ks0) :: os2 >> :: << n; l >> :: b3) os0 (l0 ->>> 0 :: rs0) term).
            eapply S_PMap; crush.
            eapply Step.
            instantiate (1:=C (b0 ++ << N k0 (t_app (pmap_compose f' f0) p) e; os2 >> :: << n; l  ++ [l' ->> pmap (pmap_compose f' f0) (remove Nat.eq_dec k0 ks0)] >> :: b3) os0 (l0 ->>> 0 :: rs0) term).
            eapply S_Prop; eauto. crush. apply List.remove_In in H. assumption.
            apply fstar_into_star_load with (b1:=b0) (k:=k0) (b2:=<< n; l ++ [l' ->> pmap (pmap_compose f' f0) (remove Nat.eq_dec k0 ks0)] >> :: b3) (es:=e) (os:=os2) (os0:=os0) (rs:=l0 ->>> 0 :: rs0) (t0:=term) in star2.
            auto.
          + crush.
        }
      * inv H4.
        {
          got.
          * instantiate (1:= C (b0 ++ << N k0 (t_app f p) e; (l ->> pmap f (remove Nat.eq_dec k0 ks) :: os1) ++ l' ->> pmap (pmap_compose f' f0) ks0 :: os2 >> :: b3) os0 (l0 ->>> final _ :: rs0) term).
            one_step. eapply S_FusePMap; crush.
          * instantiate (1:= C (b0 ++ << N k0 (t_app f p) e; l ->> pmap f (remove Nat.eq_dec k0 ks) :: os1 ++ l' ->> pmap (pmap_compose f' f0) ks0 :: os2 >> :: b3) os0 (l0 ->>> 0 :: rs0) term).
            one_step. eapply S_PMap; crush.
          * crush.
        }
    (* First first *)
    + destruct H0. destruct H0. destruct H0.
      eapply target_unique with (b1:=b1) (b2:=b2) (b3:=x) (b4:=x0 ++ << N k0 p e; os1 ++ l0 ->> pmap f0 ks0 :: l' ->> pmap f' ks0 :: os2 >> :: x1) in H0; crush.
      inv H.
      eapply target_unique with (b1:=x ++ << N k v es; l ->> pmap f ks :: os1'' >> :: x0) (b2:=x1) (b3:=b0) (b4:=b3) in H1; eauto; crush.
      got.
      * instantiate (1:=C ((x ++ << N k (t_app f v) es; l ->> pmap f (remove Nat.eq_dec k ks) :: os1'' >> :: x0) ++ << N k0 p e; os1 ++ l' ->> pmap (pmap_compose f' f0) ks0 :: os2 >> :: b3) os0 (l0 ->>> 0 :: rs0) term).
        one_step. eapply S_FusePMap; crush.
      * instantiate (1:=C (x ++ << N k (t_app f v) es; l ->> pmap f (remove Nat.eq_dec k ks) :: os1'' >> :: x0 ++ << N k0 p e; os1 ++ l' ->> pmap (pmap_compose f' f0) ks0 :: os2 >> :: b3) os0 (l0 ->>> 0 :: rs0) term).
        one_step. eapply S_PMap; crush.
      * crush.
    (* First second *)
    + destruct H0. destruct H0. destruct H0.
      eapply target_unique with (b1:=b1) (b2:=b2) (b3:=x ++ << N k0 p e; os1 ++ l0 ->> pmap f0 ks0 :: l' ->> pmap f' ks0 :: os2 >> :: x0) (b4:=x1) in H0; eauto; crush.
      inv H.
      eapply target_unique with (b1:=x) (b2:=x0 ++ << N k v es; l ->> pmap f ks :: os1'' >> :: x1) (b3:=b0) (b4:=b3) in H1; eauto; crush.
      got.
      * instantiate (1:=C (b0 ++ << N k0 p e; os1 ++ l' ->> pmap (pmap_compose f' f0) ks0 :: os2 >> :: x0 ++ << N k (t_app f v) es; l ->> pmap f (remove Nat.eq_dec k ks) :: os1'' >> :: x1) os0 (l0 ->>> 0 :: rs0) term).
        one_step. eapply S_FusePMap; crush.
      * instantiate (1:=C ((b0 ++ << N k0 p e; os1 ++ l' ->> pmap (pmap_compose f' f0) ks0 :: os2 >> :: x0) ++ << N k (t_app f v) es; l ->> pmap f (remove Nat.eq_dec k ks) :: os1'' >> :: x1) os0 (l0 ->>> 0 :: rs0) term).
        one_step. eapply S_PMap; crush.
      * crush.
  (* S_SwapReads *)
  - destruct n as [k' v'].
    tsod'.
    + destruct os1; simpl in *; inv Hsame5.
      inv H. apply List.app_inv_head in H3. inv H3.
      got.
      * instantiate (1:=C (b0 ++ << N k' (t_app f v') e; (l ->> pmap f (remove Nat.eq_dec k' ks) :: os1) ++ l' ->> pfold f' t' ks' :: l0 ->> pfold f0 t ks0 :: os2 >> :: b3) os0 rs0 term).
        one_step; eapply S_SwapReads; eauto.
      * instantiate (1:=C (b0 ++ << N k' (t_app f v') e; l ->> pmap f (remove Nat.eq_dec k' ks) :: os1 ++ l' ->> pfold f' t' ks' :: l0 ->> pfold f0 t ks0 :: os2 >> :: b3) os0 rs0 term).
        one_step; eauto.
      * crush.
    + destruct Hfirst as [b' [b'' [b''']]].
      destruct b''; simpl in *.
      * eapply target_unique with (b1:=b1) (b2:=b2) (b3:=b') (b4:=<< N k' v' e; os1 ++ l0 ->> pfold f0 t ks0 :: l' ->> pfold f' t' ks' :: os2 >> :: b''') in H0; eauto; crush.
        inv H.
        eapply target_unique with (b1:=b' ++ [<< N k v es; l ->> pmap f ks :: os1'' >>]) (b2:=b''') (b3:=b0) (b4:=b3) in H3; eauto; crush.
        got.
        { instantiate (1:=C ((b' ++ [<< N k (t_app f v) es; l ->> pmap f (remove Nat.eq_dec k ks) :: os1'' >>]) ++ << N k' v' e; os1 ++ l' ->> pfold f' t' ks' :: l0 ->> pfold f0 t ks0 :: os2 >> :: b3) os0 rs0 term).
          one_step. eapply S_SwapReads; eauto; crush. }
        { instantiate (1:=C (b' ++ << N k (t_app f v) es; l ->> pmap f (remove Nat.eq_dec k ks) :: os1'' >> :: << N k' v' e; os1 ++ l' ->> pfold f' t' ks' :: l0 ->> pfold f0 t ks0 :: os2 >> :: b3) os0 rs0 term).
          one_step. eapply S_PMap; eauto; crush. }
        { crush. }
      * eapply target_unique with (b1:=b1) (b2:=b2) (b3:=b') (b4:=s :: b'' ++ << N k' v' e; os1 ++ l0 ->> pfold f0 t ks0 :: l' ->> pfold f' t' ks' :: os2 >> :: b''') in H0; eauto; crush.
        inv H.
        eapply target_unique with (b1:=b' ++ << N k v es; l ->> pmap f ks :: os1'' >> :: s :: b'') (b2:=b''') (b3:=b0) (b4:=b3) in H3; eauto; crush.
        got.
        { instantiate (1:=C ((b' ++ << N k (t_app f v) es; l ->> pmap f (remove Nat.eq_dec k ks) :: os1'' >> :: s :: b'') ++ << N k' v' e; os1 ++ l' ->> pfold f' t' ks' :: l0 ->> pfold f0 t ks0 :: os2 >> :: b3) os0 rs0 term).
          one_step. eapply S_SwapReads; eauto; crush. }
        { instantiate (1:=C (b' ++ << N k (t_app f v) es; l ->> pmap f (remove Nat.eq_dec k ks) :: os1'' >> :: s :: b'' ++ << N k' v' e; os1 ++ l' ->> pfold f' t' ks' :: l0 ->> pfold f0 t ks0 :: os2 >> :: b3) os0 rs0 term).
          one_step. eapply S_PMap; eauto; crush. }
        { crush. }
    + destruct Hsecond as [b' [b'' [b''']]].
      tu2.
      got.
      * instantiate (1:=C (b0 ++ << N k' v' e; os1 ++ l' ->> pfold f' t' ks' :: l0 ->> pfold f0 t ks0 :: os2 >> :: b'' ++ << N k (t_app f v) es; l ->> pmap f (remove Nat.eq_dec k ks) :: os1'' >> :: b''') os0 rs0 term).
        eauto.
      * instantiate (1:=C ((b0 ++ << N k' v' e; os1 ++ l' ->> pfold f' t' ks' :: l0 ->> pfold f0 t ks0 :: os2 >> :: b'') ++ << N k (t_app f v) es; l ->> pmap f (remove Nat.eq_dec k ks) :: os1'' >> :: b''') os0 rs0 term).
        one_step; eapply S_PMap; eauto; crush.
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
    * instantiate (1:=C (<< N k v t_ks_nil; [] >> :: b1 ++ << n; os1 ++ l' ->> pmap (pmap_compose f' f) ks :: os2 >> :: b2) os' (l0 ->>> final _ :: l ->>> final Hnot :: rs0) term).
      one_step. eapply S_Add; crush.
    * instantiate (1:=C (<< N k v t_ks_nil; [] >> :: b1 ++ << n; os1 ++ l' ->> pmap (pmap_compose f' f) ks :: os2 >> :: b2) os' (l ->>> final _ :: l0 ->>> k :: rs0) term).
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
        * instantiate (1:=C (b1 ++ [<< n1; os3 >>]) os0 (l' ->>> final _ :: l0 ->>> 0 :: rs0) term).
          one_step. eapply S_Last; crush.
        * instantiate (1:=C (b1 ++ [<< n1; os3 >>]) os0 (l' ->>> final _ :: l0 ->>> 0 :: rs0) term).
          one_step. eapply S_Last; crush.
        * crush.
      (* os2 != [] *)
      + inv H6.
        got.
        * instantiate (1:=C (b1 ++ [<< n1; os2 ++ l' ->> pmap (pmap_compose f' f) ks :: os3 >>]) os0 (l0 ->>> final Hnot' :: l ->>> final Hnot :: rs0) term).
          one_step. eapply S_Last; crush.
        * instantiate (1:=C (b1 ++ [<< n1; os2 ++ l' ->> pmap (pmap_compose f' f) ks :: os3 >>]) os0 (l ->>> final Hnot :: l0 ->>> final Hnot' :: rs0) term).
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
      + instantiate (1:=C ((b2 ++ << n; os2 ++ l' ->> pmap (pmap_compose f' f) ks :: os3 >> :: x0) ++ [<< n1; os1' >>]) os0 (l0 ->>> final H3 :: l ->>> final Hnot :: rs0) term).
        one_step. eapply S_Last; crush.
      + instantiate (1:=C (b2 ++ << n; os2 ++ l' ->> pmap (pmap_compose f' f) ks :: os3 >> :: x0 ++ [<< n1; os1' >>]) os0 (l ->>> final Hnot :: l0 ->>> final H3 :: rs0) term).
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
              apply op_unique with (n:=N k' v' e0) (os1:=os1) (os2:=l' ->> pmap f' ks :: os2) (os3:=x) (os4:=l0 ->> pmap f0 ks0 :: x1) (os0:=os0) (rs0:=rs0) (t0:=term) (b:=b3 ++ << N k' v' e0; os1 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os2 >> :: b4) (b1:=b3) (b2:=b4) (os:=os1 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os2) in H0; crush.
              inv H2. inv H.
              inv H3.
              apply op_unique with (n:=N k' v' e0) (os1:=x ++ [l ->> pmap f ks0]) (os2:=x1) (os3:=os3) (os4:=l'0 ->> pmap f'0 ks0 :: os4) (os0:=os0) (rs0:=rs0) (t0:=term) (b:=b3 ++ << N k' v' e0; x ++ l ->> pmap f ks0 :: l0 ->> pmap f0 ks0 :: x1 >> :: b4) (b1:=b3) (b2:=b4) (os:=x ++ l ->> pmap f ks0 :: l0 ->> pmap f0 ks0 :: x1) in H5; crush.
              {
              got.
              - instantiate (1:=C (b3 ++ << N k' v' e0; x ++ l'0 ->> pmap (pmap_compose f'0 (pmap_compose f0 f)) ks0 :: os4 >> :: b4) os0 (l0 ->>> final _ :: l ->>> 0 :: rs0) term).
                one_step. eapply S_FusePMap; crush.
              - instantiate (1:=C (b3 ++ << N k' v' e0; x ++ l'0 ->> pmap (pmap_compose (pmap_compose f'0 f0) f) ks0 :: os4 >> :: b4) os0 (l ->>> final _ :: l0 ->>> 0 :: rs0) term).
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
              apply op_unique with (n:=N k' v' e0) (os1:=os1) (os2:=l' ->> pmap f' ks :: os2) (os3:=x) (os4:=l1 :: x0 ++ l0 ->> pmap f0 ks0 :: x1) (os0:=os0) (rs0:=rs0) (t0:=term) (b:=b3 ++ << N k' v' e0; os1 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os2 >> :: b4) (b1:=b3) (b2:=b4) (os:=os1 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os2) in H0; crush.
              inv H4.
              apply op_unique with (n:=N k' v' e0) (os1:=x ++ l ->> pmap f ks :: l' ->> pmap f' ks :: x0) (os2:=x1) (os3:=os3) (os4:=l'0 ->> pmap f'0 ks0 :: os4) (os0:=os0) (rs0:=rs0) (t0:=term) (b:=b3 ++ << N k' v' e0; x ++ l ->> pmap f ks :: l' ->> pmap f' ks :: x0 ++ l0 ->> pmap f0 ks0 :: x1 >> :: b4) (b1:=b3) (b2:=b4) (os:=x ++ l ->> pmap f ks :: l' ->> pmap f' ks :: x0 ++ l0 ->> pmap f0 ks0 :: x1) in H1; crush.
              {
              got.
              - instantiate (1:=C (b3 ++ << N k' v' e0; (x ++ l' ->> pmap (pmap_compose f' f) ks :: x0) ++ l'0 ->> pmap (pmap_compose f'0 f0) ks0 :: os4 >> :: b4) os0 (l0 ->>> final Hnot' :: l ->>> 0 :: rs0) term).
                one_step. eapply S_FusePMap; crush.
              - instantiate (1:=C (b3 ++ << N k' v' e0; x ++ l' ->> pmap (pmap_compose f' f) ks :: x0 ++ l'0 ->> pmap (pmap_compose f'0 f0) ks0 :: os4 >> :: b4) os0 (l ->>> final _ :: l0 ->>> 0 :: rs0) term).
                one_step. eapply S_FusePMap; crush.
              - crush.
              }
          (* First second *)
          + destruct H0; destruct H0; destruct H0.
            inv H3. apply List.app_inv_head in H4; inv H4.
            destruct x0.
            (* First's second is second's first *)
            * simpl in *.
              eapply op_unique with (n:=N k' v' e0) (os1:=os1) (os2:=l' ->> pmap f' ks :: os2) (os3:=x ++ [l0 ->> pmap f0 ks0]) (os4:=x1) (os0:=os0) (rs0:=rs0) (t0:=term) (b:=b3 ++ << N k' v' e0; os1 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os2 >> :: b4) (b1:=b3) (b2:=b4) (os:=os1 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os2) in H0; crush.
              inv H2.
              apply op_unique with (n:=N k' v' e0) (os1:=x) (os2:=l ->> pmap f ks :: l' ->> pmap f' ks :: os2) (os3:=os3) (os4:=l'0 ->> pmap f'0 ks0 :: os4) (os0:=os0) (rs0:=rs0) (t0:=term) (b:=b3 ++ << N k' v' e0; x ++ l0 ->> pmap f0 ks0 :: l ->> pmap f ks :: l' ->> pmap f' ks :: os2 >> :: b4) (b1:=b3) (b2:=b4) (os:=x ++ l0 ->> pmap f0 ks0 :: l ->> pmap f ks :: l' ->> pmap f' ks :: os2) in H5; crush.
              inv H1.
              {
              got.
              - instantiate (1:=C (b3 ++ << N k' v' e0; os3 ++ l' ->> pmap (pmap_compose (pmap_compose f' f'0) f0) ks0 :: os2 >> :: b4) os0 (l0 ->>> final _ :: l'0 ->>> 0 :: rs0) term).
                one_step. eapply S_FusePMap; crush.
              - instantiate (1:=C (b3 ++ << N k' v' e0; os3 ++ l' ->> pmap (pmap_compose f' (pmap_compose f'0 f0)) ks0 :: os2 >> :: b4) os0 (l'0 ->>> final _ :: l0 ->>> 0 :: rs0) term).
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
              eapply op_unique with (n:=N k' v' e0) (os1:=os1) (os2:=l' ->> pmap f' ks :: os2) (os3:=x ++ l0 ->> pmap f0 ks0 :: l1 :: x0) (os4:=x1) (os0:=os0) (rs0:=rs0) (t0:=term) (b:=b3 ++ << N k' v' e0; os1 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os2 >> :: b4) (b1:=b3) (b2:=b4) (os:=os1 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os2) in H0; crush.
              inv H2.
              apply op_unique with (n:=N k' v' e0) (os1:=x) (os2:=l1 :: x0 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os2) (os3:=os3) (os4:=l'0 ->> pmap f'0 ks0 :: os4) (os0:=os0) (rs0:=rs0) (t0:=term) (b:=b3 ++ << N k' v' e0; x ++ l0 ->> pmap f0 ks0 :: l1 :: x0 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os2 >> :: b4) (b1:=b3) (b2:=b4) (os:=x ++ l0 ->> pmap f0 ks0 :: l1 :: x0 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os2) in H5; crush.
              {
              got.
              - instantiate (1:=C (b3 ++ << N k' v' e0; os3 ++ l'0 ->> pmap (pmap_compose f'0 f0) ks0 :: x0 ++ l' ->> pmap (pmap_compose f' f) ks :: os2 >> :: b4) os0 (l0 ->>> final _ :: l ->>> 0 :: rs0) term).
                one_step. eapply S_FusePMap; crush.
              - instantiate (1:=C (b3 ++ << N k' v' e0; (os3 ++ l'0 ->> pmap (pmap_compose f'0 f0) ks0 :: x0) ++ l' ->> pmap (pmap_compose f' f) ks :: os2 >> :: b4) os0 (l ->>> final Hnot :: l0 ->>> 0 :: rs0) term).
                one_step. eapply S_FusePMap; crush.
              - crush.
              }
        }
      (* First first *)
      + destruct H0; destruct H0; destruct H0.
        apply target_unique with (os:=os1 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os2) (k:=k) (v:=v) (b1:=b1) (b2:=b2) (b3:=x) (b4:=x0 ++ << N k' v' e0; os3 ++ l0 ->> pmap f0 ks0 :: l'0 ->> pmap f'0 ks0 :: os4 >> :: x1) (os0:=os0) (rs0:=rs0) (t0:=term) (b:=b1 ++ << N k v e; os1 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os2 >> :: b2) in H0; crush.
        inv H3.
        apply target_unique with (os:=os3 ++ l0 ->> pmap f0 ks0 :: l'0 ->> pmap f'0 ks0 :: os4) (k:=k') (v:=v') (b1:=x ++ << N k v e; os1 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os2 >> :: x0) (b2:=x1) (b3:=b3) (b4:=b4) (os0:=os0) (rs0:=rs0) (t0:=term) (b:=x ++ << N k v e; os1 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os2 >> :: x0 ++ << N k' v' e0; os3 ++ l0 ->> pmap f0 ks0 :: l'0 ->> pmap f'0 ks0 :: os4 >> :: x1) in H1; crush.
        got.
        * instantiate (1:=C ((x ++ << N k v e; os1 ++ l' ->> pmap (pmap_compose f' f) ks :: os2 >> :: x0) ++ << N k' v' e0; os3 ++ l'0 ->> pmap (pmap_compose f'0 f0) ks0 :: os4 >> :: b4) os0 (l0 ->>> 0 :: l ->>> 0 :: rs0) term).
          one_step. eapply S_FusePMap; crush.
        * instantiate (1:=C (x ++ << N k v e; os1 ++ l' ->> pmap (pmap_compose f' f) ks :: os2 >> :: x0 ++ << N k' v' e0; os3 ++ l'0 ->> pmap (pmap_compose f'0 f0) ks0 :: os4 >> :: b4) os0 (l ->>> 0 :: l0 ->>> 0 :: rs0) term).
          one_step. eapply S_FusePMap; crush.
        * crush.
      (* First second *)
      + destruct H0; destruct H0; destruct H0.
        apply target_unique with (es:=e) (os:=os1 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os2) (k:=k) (v:=v) (b1:=b1) (b2:=b2) (b3:=x ++ << N k' v' e0; os3 ++ l0 ->> pmap f0 ks0 :: l'0 ->> pmap f'0 ks0 :: os4 >> :: x0) (b4:=x1) (os0:=os0) (rs0:=rs0) (t0:=term) (b:=b1 ++ << N k v e; os1 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os2 >> :: b2) in H0; crush.
        inv H3.
        apply target_unique with (os:=os3 ++ l0 ->> pmap f0 ks0 :: l'0 ->> pmap f'0 ks0 :: os4) (k:=k') (v:=v') (b1:=x) (b2:=x0 ++ << N k v e; os1 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os2 >> :: x1) (b3:=b3) (b4:=b4) (os0:=os0) (rs0:=rs0) (t0:=term) (b:=x ++ << N k' v' e0; os3 ++ l0 ->> pmap f0 ks0 :: l'0 ->> pmap f'0 ks0 :: os4 >> :: x0 ++ << N k v e; os1 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os2 >> :: x1) in H1; crush.
        got.
        * instantiate (1:=C (b3 ++ << N k' v' e0; os3 ++ l'0 ->> pmap (pmap_compose f'0 f0) ks0 :: os4 >> :: x0 ++ << N k v e; os1 ++ l' ->> pmap (pmap_compose f' f) ks :: os2 >> :: x1) os0 (l0 ->>> 0 :: l ->>> 0 :: rs0) term).
          one_step. eapply S_FusePMap; crush.
        * instantiate (1:=C ((b3 ++ << N k' v' e0; os3 ++ l'0 ->> pmap (pmap_compose f'0 f0) ks0 :: os4 >> :: x0) ++ << N k v e; os1 ++ l' ->> pmap (pmap_compose f' f) ks :: os2 >> :: x1) os0 (l ->>> 0 :: l0 ->>> 0 :: rs0) term).
          one_step. eapply S_FusePMap; crush.
        * crush.
    }
  (* S_SwapReads *)
  - destruct n as [k v].
    destruct n0 as [k' v'].
    tsod'''.
    + osod.
      * dtr; inv H1.
      * destruct Hfirst as [os''0 [os'' [os''']]].
        inv H3. apply List.app_inv_head in H4. inv H4.
        {
        destruct os''.
        - simpl in *.
          eapply op_unique with (n:=N k' v' e0) (os1:=os1) (os2:=l' ->> pmap f' ks :: os2) (os3:=os''0) (os4:=l0 ->> pfold f0 t ks0 :: os''') (os0:=os0) (rs0:=rs0) (t0:=term) in H0; crush.
        - simpl in *.
          eapply op_unique with (n:=N k' v' e0) (os1:=os1) (os2:=l' ->> pmap f' ks :: os2) (os3:=os''0) (os4:=l1 :: os'' ++ l0 ->> pfold f0 t ks0 :: os''') (os0:=os0) (rs0:=rs0) (t0:=term) in H0; crush.
          inv H. inv H2.
          eapply op_unique with (n:=N k' v' e0) (os1:=os''0 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os'') (os2:=os''') (os3:=os3) (os4:=l'0 ->> pfold f'0 t' ks' :: os4) (os0:=os0) (rs0:=rs0) (t0:=term) (b1:=b3) (b2:=b4) in H7; auto; crush.
          got.
          + instantiate (1:=C (b3 ++ << N k' v' e0; (os''0 ++ l' ->> pmap (pmap_compose f' f) ks :: os'') ++ l'0 ->> pfold f'0 t' ks' :: l0 ->> pfold f0 t ks0 :: os4 >> :: b4) os0 (l ->>> 0 :: rs0) term).
            one_step; eapply S_SwapReads; eauto; crush.
          + instantiate (1:=C (b3 ++ << N k' v' e0; os''0 ++ l' ->> pmap (pmap_compose f' f) ks :: os'' ++ l'0 ->> pfold f'0 t' ks' :: l0 ->> pfold f0 t ks0 :: os4 >> :: b4) os0 (l ->>> 0 :: rs0) term).
            one_step; eapply S_FusePMap; eauto; crush.
          + crush.
        }
      * destruct Hsecond as [os''0 [os'' [os''']]].
        ou2. destruct os''; inv H1.
        inv H2. inv H. simpl in *.
        got.
        { instantiate (1:=C (b3 ++ << N k' v' e0; os3 ++ l'0 ->> pfold f'0 t' ks' :: l0 ->> pfold f0 t ks0 :: os'' ++ l' ->> pmap (pmap_compose f' f) ks :: os2 >> :: b4) os0 (l ->>> 0 :: rs0) term).
          one_step; eapply S_SwapReads; eauto. }
        { instantiate (1:=C (b3 ++ << N k' v' e0; (os3 ++ l'0 ->> pfold f'0 t' ks' :: l0 ->> pfold f0 t ks0 :: os'') ++ l' ->> pmap (pmap_compose f' f) ks :: os2 >> :: b4) os0 (l ->>> 0 :: rs0) term).
          one_step; eapply S_FusePMap; eauto; crush. }
        { crush. }
    + destruct Hfirst as [b' [b'' [b''']]].
      eapply target_unique with (b1:=b1) (b2:=b2) (b3:=b') (b4:=b'' ++ << N k' v' e0; os3 ++ l0 ->> pfold f0 t ks0 :: l'0 ->> pfold f'0 t' ks' :: os4 >> :: b''') in H0; eauto; dtr; subst.
      inv H2. inv H3. inv H.
      eapply target_unique with (b1:=b' ++ << N k v e; os1 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os2 >> :: b'') (b2:=b''') (b3:=b3) (b4:=b4) in H1; eauto; [|crush]; dtr; subst.
      got.
      * instantiate (1:=C ((b' ++ << N k v e; os1 ++ l' ->> pmap (pmap_compose f' f) ks :: os2 >> :: b'') ++ << N k' v' e0; os3 ++ l'0 ->> pfold f'0 t' ks' :: l0 ->> pfold f0 t ks0 :: os4 >> :: b4) os0 (l ->>> final Hnot :: rs0) term).
        one_step; eapply S_SwapReads; eauto; crush.
      * instantiate (1:=C (b' ++ << N k v e; os1 ++ l' ->> pmap (pmap_compose f' f) ks :: os2 >> :: b'' ++ << N k' v' e0; os3 ++ l'0 ->> pfold f'0 t' ks' :: l0 ->> pfold f0 t ks0 :: os4 >> :: b4) os0 (l ->>> final Hnot :: rs0) term).
        one_step; eapply S_FusePMap; eauto; crush.
      * crush.
    + destruct Hsecond as [b' [b'' [b''']]].
      eapply target_unique with (b1:=b1) (b2:=b2) (b3:=b' ++ << N k' v' e0; os3 ++ l0 ->> pfold f0 t ks0 :: l'0 ->> pfold f'0 t' ks' :: os4 >> :: b'') (b4:=b''') in H0; eauto; crush.
      inv H3. inv H2. inv H.
      eapply target_unique with (b1:=b') (b2:=b'' ++ << N k v e; os1 ++ l ->> pmap f ks :: l' ->> pmap f' ks :: os2 >> :: b''') (b3:=b3) (b4:=b4) in H1; eauto; crush.
      got.
      * instantiate (1:=C (b3 ++ << N k' v' e0; os3 ++ l'0 ->> pfold f'0 t' ks' :: l0 ->> pfold f0 t ks0 :: os4 >> :: b'' ++ << N k v e; os1 ++ l' ->> pmap (pmap_compose f' f) ks :: os2 >> :: b''') os0 (l ->>> 0 :: rs0) term).
        one_step; eapply S_SwapReads; eauto; crush.
      * instantiate (1:=C ((b3 ++ << N k' v' e0; os3 ++ l'0 ->> pfold f'0 t' ks' :: l0 ->> pfold f0 t ks0 :: os4 >> :: b'') ++ << N k v e; os1 ++ l' ->> pmap (pmap_compose f' f) ks :: os2 >> :: b''') os0 (l ->>> 0 :: rs0) term).
        one_step; eapply S_FusePMap; eauto; crush.
      * crush.
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
Qed.
Hint Resolve lc_fusepmap.

Lemma lc_swapreads :
  forall cx cy cz b1 b2 f f' t t' ks ks' l l' term0 os os1 os2 rs n,
  well_typed cx ->
  cx = C (b1 ++ << n; os1 ++ l ->> pfold f t ks :: l' ->> pfold f' t' ks' :: os2 >> :: b2) os rs term0 ->
  cy = C (b1 ++ << n; os1 ++ l' ->> pfold f' t' ks' :: l ->> pfold f t ks :: os2 >> :: b2) os rs term0 ->
  not (lappears_free_in l f') ->
  not (lappears_free_in l t') ->
  cx --> cy ->
  cx --> cz ->
  cy -v cz.
Proof using.
  intros cx cy cz b1 b2 f f' t t' ks ks' l l' term0 os os1 os2 rs n.
  intros WT Heqcx Heqcy.
  intros Hlfree1 Hlfree2.
  intros cxcy cxcz.
  inversion cxcz; ssame; try solve [subst; eauto].
  (* S_Empty *)
  - exfalso; eauto.
  (* S_Add *)
  - gotw (C (<< N k v t_ks_nil; [] >> :: b1 ++ << n; os1 ++ l' ->> pfold f' t' ks' :: l ->> pfold f t ks :: os2 >> :: b2) os' (l0 ->>> final H :: rs0) term); eauto.
    eapply S_SwapReads with (b1:=<< N k v t_ks_nil; [] >> :: b1); eauto.
  (* S_Last *)
  - inv H0. clear H2.
    destruct b2; simpl in *.
    + apply List.app_inj_tail in H3; dtr. inv H1.
      destruct os1; simpl in *.
      (* os1 = [] *)
      * inv H5.
        got.
        { instantiate (1:=C (b0 ++ [<< n1; l' ->> pfold f' t' ks' :: os2 >>]) os0 (l0 ->>> final H :: rs0) term).
          exists 2.
          eapply Step.
          instantiate (1:=C (b0 ++ [<< n1; l0 ->> pfold f t ks :: l' ->> pfold f' t' ks' :: os2 >>]) os0 rs0 term).
          eapply S_SwapReads with (l:=l') (l':=l0) (f:=f') (f':=f) (t:=t') (t':=t) (os1:=[]) (b1:=b0) (b2:=[]); eauto.
          eapply no_dep_backwards' with (os1:=[]); eauto.
          eapply no_dep_backwards with (os1:=[]); eauto.
          eapply Step.
          eapply S_Last; eauto.
          auto. }
        { instantiate (1:=C (b0 ++ [<< n1; l' ->> pfold f' t' ks' :: os2 >>]) os0 (l0 ->>> final H :: rs0) term).
          exists 0. auto. }
        { crush. }
        (* os2 != [] *)
      * inv H5.
        got.
        { instantiate (1:=C (b0 ++ [<< n1; os1 ++ l' ->> pfold f' t' ks' :: l ->> pfold f t ks :: os2 >>]) os0 (l0 ->>> final H :: rs0) term).
          one_step. eapply S_Last; crush. }
        { instantiate (1:=C (b0 ++ [<< n1; os1 ++ l' ->> pfold f' t' ks' :: l ->> pfold f t ks :: os2 >>]) os0 (l0 ->>> final H :: rs0) term).
          one_step. eapply S_SwapReads; crush. }
        { crush. }
    + remember (s :: b2) as bend.
      assert (exists y ys, bend = ys ++ [y]) by (apply list_snoc with (xs:=bend) (x:=s) (xs':=b2); crush); dtr; subst.
      rewrite H0 in *. clear H0.
      replace (b1 ++ << n; os1 ++ l ->> pfold f t ks :: l' ->> pfold f' t' ks' :: os2 >> :: x0 ++ [x]) with ((b1 ++ << n; os1 ++ l ->> pfold f t ks :: l' ->> pfold f' t' ks' :: os2 >> :: x0) ++ [x]) in H3 by crush.
      apply List.app_inj_tail in H3; dtr.
      subst.
      got.
      * instantiate (1:=C ((b1 ++ << n; os1 ++ l' ->> pfold f' t' ks' :: l ->> pfold f t ks :: os2 >> :: x0) ++ [<< n1; os1' >>]) os0 (l0 ->>> final H :: rs0) term).
        one_step. eapply S_Last; crush.
      * instantiate (1:=C (b1 ++ << n; os1 ++ l' ->> pfold f' t' ks' :: l ->> pfold f t ks :: os2 >> :: x0 ++ [<< n1; os1' >>]) os0 (l0 ->>> final H :: rs0) term).
        one_step. eapply S_SwapReads; crush.
      * crush.
  (* S_SwapReads *)
  - destruct n as [k v].
    destruct n0 as [k' v'].
    {
    tsod''.
    - osod.
      + dtr. inv H3. inv H4. inv H. apply List.app_inv_head in H3. inv H3. auto.
      + inv H. apply List.app_inv_head in H3. inv H3.
        destruct Hfirst as [os'[os''[os''']]].
        destruct os''; simpl in *.
        * eapply op_unique with (n:=N k' v' e0) (os1:=os1) (os2:=l' ->> pfold f' t' ks' :: os2) (os3:=os') (os4:=l0 ->> pfold f0 t0 ks0 :: os''') (os0:=os0) (rs0:=rs0) (t0:=term) in H; eauto; crush.
          inv H3.
          eapply op_unique with (n:=N k' v' e0) (os1:=os' ++ [l ->> pfold f t ks]) (os2:=os''') (os3:=os3) (os4:=l'0 ->> pfold f'0 t'0 ks'0 :: os4) (os0:=os0) (rs0:=rs0) (t0:=term) in H4; eauto; crush.
          got.
          { instantiate (1:=C (b0 ++ << N k' v' e0; os' ++ l ->> pfold f t ks :: l0 ->> pfold f0 t0 ks0 :: l'0 ->> pfold f'0 t'0 ks'0 :: os4 >> :: b3) os0 rs0 term).
            one_step; eapply S_SwapReads; eauto.
            eapply no_dep_backwards'; eauto.
            eapply no_dep_backwards; eauto. }
          { instantiate (1:=C (b0 ++ << N k' v' e0; (os' ++ [l ->> pfold f t ks]) ++ l0 ->> pfold f0 t0 ks0 :: l'0 ->> pfold f'0 t'0 ks'0 :: os4 >> :: b3) os0 rs0 term).
            one_step; eapply S_SwapReads; eauto. crush.
            eapply no_dep_backwards' with (os1:=os' ++ [l ->> pfold f t ks]); eauto.
            instantiate (1:=term).
            instantiate (1:=rs0).
            instantiate (1:=os0).
            instantiate (1:=b3).
            instantiate (1:=os4).
            instantiate (1:=ks'0).
            instantiate (1:=t'0).
            instantiate (1:=f'0).
            instantiate (1:=ks0).
            instantiate (1:=t0).
            instantiate (1:=l0).
            instantiate (1:=N k' v' e0).
            instantiate (1:=b0). crush.
            eapply no_dep_backwards with (os1:=os' ++ [l ->> pfold f t ks]); eauto.
            instantiate (1:=term).
            instantiate (1:=rs0).
            instantiate (1:=os0).
            instantiate (1:=b3).
            instantiate (1:=os4).
            instantiate (1:=ks'0).
            instantiate (1:=t'0).
            instantiate (1:=f'0).
            instantiate (1:=ks0).
            instantiate (1:=f0).
            instantiate (1:=l0).
            instantiate (1:=N k' v' e0).
            instantiate (1:=b0). crush. }
          { crush. }
        * eapply op_unique with (n:=N k' v' e0) (os1:=os1) (os2:=l' ->> pfold f' t' ks' :: os2) (os3:=os') (os4:=l1 :: os'' ++ l0 ->> pfold f0 t0 ks0 :: os''') (os0:=os0) (rs0:=rs0) (t0:=term) in H; eauto; crush.
          eapply op_unique with (n:=N k' v' e0) (os1:=os' ++ l ->> pfold f t ks :: l' ->> pfold f' t' ks' :: os'') (os2:=os''') (os3:=os3) (os4:=l'0 ->> pfold f'0 t'0 ks'0 :: os4) (os0:=os0) (rs0:=rs0) (t0:=term) in H4; eauto; crush.
          got.
          { instantiate (1:=C (b0 ++ << N k' v' e0; (os' ++ l' ->> pfold f' t' ks' :: l ->> pfold f t ks :: os'') ++ l'0 ->> pfold f'0 t'0 ks'0 :: l0 ->> pfold f0 t0 ks0 :: os4 >> :: b3) os0 rs0 term).
            one_step; eapply S_SwapReads; eauto; crush. }
          { instantiate (1:=C (b0 ++ << N k' v' e0; os' ++ l' ->> pfold f' t' ks' :: l ->> pfold f t ks :: os'' ++ l'0 ->> pfold f'0 t'0 ks'0 :: l0 ->> pfold f0 t0 ks0 :: os4 >> :: b3) os0 rs0 term).
            one_step; eapply S_SwapReads; eauto. }
          { crush. }
      + inv H. apply List.app_inv_head in H3. inv H3.
        destruct Hsecond as [os'[os''[os''']]].
        destruct os''; simpl in *.
        * eapply op_unique with (n:=N k' v' e0) (os1:=os1) (os2:=l' ->> pfold f' t' ks' :: os2) (os3:=os' ++ [l0 ->> pfold f0 t0 ks0]) (os4:=os''') (os0:=os0) (rs0:=rs0) (t0:=term) in H; eauto; crush.
          eapply op_unique with (n:=N k' v' e0) (os1:=os') (os2:=l ->> pfold f t ks :: l' ->> pfold f' t' ks' :: os2) (os3:=os3) (os4:=l'0 ->> pfold f'0 t'0 ks'0 :: os4) (os0:=os0) (rs0:=rs0) (t0:=term) in H4; eauto; crush.
          inv H0.
          got.
          { instantiate (1:=C (b0 ++ << N k' v' e0; (os3 ++ [l0 ->> pfold f0 t0 ks0]) ++ l'0 ->> pfold f'0 t'0 ks'0 :: l' ->> pfold f' t' ks' :: os2 >> :: b3) os0 rs0 term).
            one_step; eapply S_SwapReads; eauto. crush.
            eapply no_dep_backwards' with (os1:=os3 ++ [l0 ->> pfold f0 t0 ks0]); eauto.
            instantiate (1:=term).
            instantiate (1:=rs0).
            instantiate (1:=os0).
            instantiate (1:=b3).
            instantiate (1:=os2).
            instantiate (1:=ks').
            instantiate (1:=t').
            instantiate (1:=f').
            instantiate (1:=ks'0).
            instantiate (1:=t'0).
            instantiate (1:=l'0).
            instantiate (1:=N k' v' e0).
            instantiate (1:=b0). crush.
            eapply no_dep_backwards with (os1:=os3 ++ [l0 ->> pfold f0 t0 ks0]); eauto.
            instantiate (1:=term).
            instantiate (1:=rs0).
            instantiate (1:=os0).
            instantiate (1:=b3).
            instantiate (1:=os2).
            instantiate (1:=ks').
            instantiate (1:=t').
            instantiate (1:=f').
            instantiate (1:=ks'0).
            instantiate (1:=f'0).
            instantiate (1:=l'0).
            instantiate (1:=N k' v' e0).
            instantiate (1:=b0). crush. }
          { instantiate (1:=C (b0 ++ << N k' v' e0; os3 ++ l0 ->> pfold f0 t0 ks0 :: l'0 ->> pfold f'0 t'0 ks'0 :: l' ->> pfold f' t' ks' :: os2 >> :: b3) os0 rs0 term).
            one_step; eapply S_SwapReads; eauto.
            eapply no_dep_backwards'; eauto.
            eapply no_dep_backwards; eauto. }
          { crush. }
        * eapply op_unique with (n:=N k' v' e0) (os1:=os1) (os2:=l' ->> pfold f' t' ks' :: os2) (os3:=os' ++ l0 ->> pfold f0 t0 ks0 :: l1 :: os'') (os4:=os''') (os0:=os0) (rs0:=rs0) (t0:=term) in H; eauto; crush.
          eapply op_unique with (n:=N k' v' e0) (os1:=os') (os2:=l1 :: os'' ++ l ->> pfold f t ks :: l' ->> pfold f' t' ks' :: os2) (os3:=os3) (os4:=l'0 ->> pfold f'0 t'0 ks'0 :: os4) (os0:=os0) (rs0:=rs0) (t0:=term) in H4; eauto; crush.
          got.
          { instantiate (1:=C (b0 ++ << N k' v' e0; os3 ++ l'0 ->> pfold f'0 t'0 ks'0 :: l0 ->> pfold f0 t0 ks0 :: os'' ++ l' ->> pfold f' t' ks' :: l ->> pfold f t ks :: os2 >> :: b3) os0 rs0 term).
            one_step; eapply S_SwapReads; eauto; crush. }
          { instantiate (1:=C (b0 ++ << N k' v' e0; (os3 ++ l'0 ->> pfold f'0 t'0 ks'0 :: l0 ->> pfold f0 t0 ks0 :: os'') ++ l' ->> pfold f' t' ks' :: l ->> pfold f t ks :: os2 >> :: b3) os0 rs0 term).
            one_step; eapply S_SwapReads; eauto; crush. }
          { crush. }
    - destruct Hfirst as [b'[b''[b''']]].
      tu1.
      got.
      + instantiate (1:=C ((b' ++ << N k v e; os1 ++ l' ->> pfold f' t' ks' :: l ->> pfold f t ks :: os2 >> :: b'') ++ << N k' v' e0; os3 ++ l'0 ->> pfold f'0 t'0 ks'0 :: l0 ->> pfold f0 t0 ks0 :: os4 >> :: b3) os0 rs0 term).
        one_step; eapply S_SwapReads; eauto; crush.
      + instantiate (1:=C (b' ++ << N k v e; os1 ++ l' ->> pfold f' t' ks' :: l ->> pfold f t ks :: os2 >> :: b'' ++ << N k' v' e0; os3 ++ l'0 ->> pfold f'0 t'0 ks'0 :: l0 ->> pfold f0 t0 ks0 :: os4 >> :: b3) os0 rs0 term).
        one_step; eapply S_SwapReads; eauto.
      + crush.
    - destruct Hsecond as [b'[b''[b''']]].
      tu2.
      got.
      + instantiate (1:=C (b0 ++ << N k' v' e0; os3 ++ l'0 ->> pfold f'0 t'0 ks'0 :: l0 ->> pfold f0 t0 ks0 :: os4 >> :: b'' ++ << N k v e; os1 ++ l' ->> pfold f' t' ks' :: l ->> pfold f t ks :: os2 >> :: b''') os0 rs0 term).
        one_step; eapply S_SwapReads; eauto.
      + instantiate (1:=C ((b0 ++ << N k' v' e0; os3 ++ l'0 ->> pfold f'0 t'0 ks'0 :: l0 ->> pfold f0 t0 ks0 :: os4 >> :: b'') ++ << N k v e; os1 ++ l' ->> pfold f' t' ks' :: l ->> pfold f t ks :: os2 >> :: b''') os0 rs0 term).
        one_step; eapply S_SwapReads; eauto; crush.
      + crush.
    }
Qed.
Hint Resolve lc_swapreads.

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
      + instantiate (1:=C [<< N k0 v t_ks_nil; [] >>; << n1; os1' >>] os' (l0 ->>> _ :: l ->>> final _ :: rs0) term).
        one_step; eapply S_Add with (b:=[<< n1; os1' >>]); crush.
      + instantiate (1:=C [<< N k0 v t_ks_nil; [] >>; << n1; os1' >>] os' (l ->>> final Hnot :: l0 ->>> k0 :: rs0) term).
        one_step; eapply S_Last with (b1:=[<< N k0 v t_ks_nil; [] >>]); crush.
      + crush.
    (* b1 != [] *)
    - simpl in *. inv H7. eapply ex_intro. eapply ex_intro.
      split; try split.
      + instantiate (1:=C (<< N k0 v t_ks_nil; [] >> :: s :: b1 ++ [<< n1; os1' >>]) os' (l0 ->>> k0 :: l ->>> final Hnot :: rs0) term).
        one_step; eapply S_Add; crush.
      + instantiate (1:=C (<< N k0 v t_ks_nil; [] >> :: s :: b1 ++ [<< n1; os1' >>]) os' (l ->>> final Hnot :: l0 ->>> k0 :: rs0) term).
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
