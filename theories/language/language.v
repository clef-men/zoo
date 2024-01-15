From iris.program_logic Require Export
  language
  ectx_language
  ectxi_language.

From zebra Require Import
  prelude.
From zebra.language Require Export
  semantics.
From zebra Require Import
  options.

Implicit Types e : expr.
Implicit Types es : list expr.
Implicit Types v : val.
Implicit Types K : ectx.
Implicit Types σ : state.
Implicit Types κ : list observation.

Lemma zebra_mixin :
  EctxiLanguageMixin of_val to_val ectxi_fill head_step.
Proof.
  split.
  all: try apply _.
  all: eauto using
    to_of_val,
    of_to_val,
    val_head_stuck,
    ectxi_fill_val,
    ectxi_fill_no_val_inj,
    head_step_ectxi_fill_val.
Qed.

Canonical zebra_ectxi_lang :=
  EctxiLanguage zebra_mixin.
Canonical zebra_ectx_lang :=
  EctxLanguageOfEctxi zebra_ectxi_lang.
Canonical zebra :=
  LanguageOfEctx zebra_ectx_lang.

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
  simplify_eq.
Qed.
Lemma prim_step_to_val_is_head_step e σ1 κ v σ2 es :
  prim_step e σ1 κ (Val v) σ2 es →
  head_step e σ1 κ (Val v) σ2 es.
Proof.
  intro H. destruct H as [K e1 e2 H1 H2].
  assert (to_val (fill K e2) = Some v) as H3; first rewrite -H2 //.
  apply to_val_fill_some in H3 as [-> ->]. subst e. done.
Qed.
Lemma head_step_to_val e1 σ1 κ e2 σ2 es σ1' κ' e2' σ2' es' :
  head_step e1 σ1 κ e2 σ2 es →
  head_step e1 σ1' κ' e2' σ2' es' →
  is_Some (to_val e2) →
  is_Some (to_val e2').
Proof.
  destruct 1; inversion 1; naive_solver.
Qed.
Lemma irreducible_resolve e v1 v2 σ :
  irreducible e σ →
  irreducible (Resolve e (Val v1) (Val v2)) σ.
Proof.
  intros H κ ? σ' es [K' e1' e2' Hfill -> step]. simpl in *.
  induction K' as [| K K' _] using rev_ind; simpl in Hfill.
  - subst e1'. inversion step. eapply H. apply head_prim_step. done.
  - rewrite fill_app /= in Hfill.
    destruct K;
      inversion Hfill; subst; clear Hfill;
      try match goal with H : Val ?v = fill K' ?e |- _ =>
        assert (to_val (fill K' e) = Some v) as HEq by rewrite -H //;
        apply to_val_fill_some in HEq; destruct HEq as [-> ->]; inversion step
      end.
    eapply (H κ (fill_item _ (foldl (flip fill_item) e2' K')) σ' es).
    eapply (Ectx_step (K' ++ [_])); last done; simpl; rewrite fill_app //.
Qed.
