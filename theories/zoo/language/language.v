From zoo Require Import
  prelude.
From zoo.iris.program_logic Require Export
  language
  ectx_language
  ectxi_language.
From zoo.language Require Export
  semantics.
From zoo Require Import
  options.

Implicit Types e : expr.
Implicit Types es : list expr.
Implicit Types v : val.
Implicit Types K : ectx.
Implicit Types σ : state.
Implicit Types κ : list observation.

Lemma zoo_mixin :
  EctxiLanguageMixin of_val to_val ectxi_fill base_step.
Proof.
  split.
  all: try apply _.
  all: eauto using
    to_of_val,
    of_to_val,
    val_base_stuck,
    ectxi_fill_val,
    ectxi_fill_no_val_inj,
    base_step_ectxi_fill_val.
Qed.

Canonical zoo_ectxi_lang :=
  Build_ectxi_language zoo_mixin.
Canonical zoo_ectx_lang :=
  EctxLanguageOfEctxi zoo_ectxi_lang.
Canonical zoo :=
  LanguageOfEctx zoo_ectx_lang.
#[global] Arguments zoo : simpl never.

Lemma to_val_fill_some K e v :
  to_val (fill K e) = Some v →
  K = [] ∧ e = Val v.
Proof.
  intro H. destruct K as [| k K]; first by apply of_to_val in H. exfalso.
  assert (to_val e ≠ None) as He.
  { intro A. rewrite fill_not_val // in H. }
  assert (∃ w, e = Val w) as [w ->].
  { destruct e; try done; eauto. }
  assert (to_val (fill (k :: K) (Val w)) = None).
  { destruct k; simpl; apply fill_not_val; done. }
  simplify.
Qed.
Lemma prim_step_to_val_is_base_step tid e σ1 κ v σ2 es :
  prim_step tid e σ1 κ (Val v) σ2 es →
  base_step tid e σ1 κ (Val v) σ2 es.
Proof.
  intro H. destruct H as [K e1 e2 H1 H2].
  assert (to_val (fill K e2) = Some v) as H3; first rewrite -H2 //.
  apply to_val_fill_some in H3 as [-> ->]. subst e. done.
Qed.

Lemma base_reducible_no_obs_equal tid v1 v2 σ :
  base_reducible_no_obs tid (Equal (Val v1) (Val v2)) σ.
Proof.
  destruct (val_similar_or_nonsimilar v1 v2).
  all: repeat econstructor; done.
Qed.
Lemma base_reducible_equal tid v1 v2 σ :
  base_reducible tid (Equal (Val v1) (Val v2)) σ.
Proof.
  apply base_reducible_no_obs_base_reducible, base_reducible_no_obs_equal.
Qed.
Lemma reducible_equal tid v1 v2 σ :
  reducible tid (Equal (Val v1) (Val v2)) σ.
Proof.
  apply base_reducible_reducible, base_reducible_equal.
Qed.

Lemma base_reducible_no_obs_cas tid l fld v1 v2 v σ :
  σ.(state_heap) !! (l +ₗ fld) = Some v →
  base_reducible_no_obs tid (CAS (Val $ ValTuple [ValLoc l; ValInt fld]) (Val v1) (Val v2)) σ.
Proof.
  destruct (val_similar_or_nonsimilar v v1).
  all: repeat econstructor; done.
Qed.
Lemma base_reducible_cas tid l fld v1 v2 v σ :
  σ.(state_heap) !! (l +ₗ fld) = Some v →
  base_reducible tid (CAS (Val $ ValTuple [ValLoc l; ValInt fld]) (Val v1) (Val v2)) σ.
Proof.
  intros.
  eapply base_reducible_no_obs_base_reducible, base_reducible_no_obs_cas. done.
Qed.
Lemma reducible_cas tid l fld v1 v2 v σ :
  σ.(state_heap) !! (l +ₗ fld) = Some v →
  reducible tid (CAS (Val $ ValTuple [ValLoc l; ValInt fld]) (Val v1) (Val v2)) σ.
Proof.
  intros.
  eapply base_reducible_reducible, base_reducible_cas. done.
Qed.

Lemma reducible_resolve tid e σ pid v :
  Atomic e →
  reducible tid e σ →
  reducible tid (Resolve e (Val $ ValProph pid) (Val v)) σ.
Proof.
  intros Hatomic (κ & e' & σ' & es & H).
  exists (κ ++ [(pid, (default v (to_val e'), v))]), e', σ', es.
  eapply (base_step_fill_prim_step' []); try done.
  assert (∃ w, Val w = e') as (w & <-).
  { apply (Hatomic tid σ e' κ σ' es) in H as (w & H).
    exists w. apply (of_to_val _ _ H).
  }
  econstructor.
  apply prim_step_to_val_is_base_step. done.
Qed.
Lemma prim_step_resolve_inv tid e v1 v2 σ1 κ e2 σ2 es :
  Atomic e →
  prim_step tid (Resolve e (Val v1) (Val v2)) σ1 κ e2 σ2 es →
  base_step tid (Resolve e (Val v1) (Val v2)) σ1 κ e2 σ2 es.
Proof.
  intros Hatomic [K e1' e2' Hfill -> Hstep]. simpl in *.
  induction K as [| k K _] using rev_ind.
  - invert Hstep.
    constructor. done.
  - rewrite fill_app /= in Hfill. destruct k; inversion Hfill; subst; clear Hfill.
    + assert (fill_item k (fill K e1') = fill (K ++ [k]) e1') as Heq1; first by rewrite fill_app.
      assert (fill_item k (fill K e2') = fill (K ++ [k]) e2') as Heq2; first by rewrite fill_app.
      rewrite fill_app /=. rewrite Heq1 in Hatomic.
      assert (is_Some (to_val (fill (K ++ [k]) e2'))) as H.
      { eapply (Hatomic tid σ1 _ κ σ2 es), (base_step_fill_prim_step' (K ++ [k])); done. }
      destruct H as [v H]. apply to_val_fill_some in H. destruct H, K; done.
    + rename select (of_val v1 = _) into Hv1.
      assert (to_val (fill K e1') = Some v1) as Hfill_v1 by rewrite -Hv1 //.
      apply to_val_fill_some in Hfill_v1 as (-> & ->).
      invert Hstep.
    + rename select (of_val v2 = _) into Hv2.
      assert (to_val (fill K e1') = Some v2) as Hfill_v2 by rewrite -Hv2 //.
      apply to_val_fill_some in Hfill_v2 as (-> & ->).
      invert Hstep.
Qed.

Lemma irreducible_resolve tid e v1 v2 σ :
  irreducible tid e σ →
  irreducible tid (Resolve e (Val v1) (Val v2)) σ.
Proof.
  intros H κ ? σ' es [K' e1' e2' Hfill -> step].
  simplify.
  induction K' as [| K K' _] using rev_ind; simpl in Hfill.
  - subst e1'. inversion step. eapply H. apply base_step_prim_step. done.
  - rewrite fill_app /= in Hfill.
    destruct K.
    all: inversion Hfill; subst; clear Hfill.
    all:
      try
        match goal with H: Val ?v = fill _ ?e |- _ =>
          assert (to_val (fill K' e) = Some v) as Heq by rewrite -H //;
          apply to_val_fill_some in Heq;
          destruct Heq as [-> ->];
          inversion step
        end.
    eapply (H κ (fill_item _ (foldl (flip fill_item) e2' K')) σ' es).
    eapply (base_step_fill_prim_step' (K' ++ [_])); last done.
    all: rewrite /= fill_app //.
Qed.
