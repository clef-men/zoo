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
Lemma prim_step_to_val_is_base_step e σ1 κ v σ2 es :
  prim_step e σ1 κ (Val v) σ2 es →
  base_step e σ1 κ (Val v) σ2 es.
Proof.
  intro H. destruct H as [K e1 e2 H1 H2].
  assert (to_val (fill K e2) = Some v) as H3; first rewrite -H2 //.
  apply to_val_fill_some in H3 as [-> ->]. subst e. done.
Qed.
Lemma base_step_to_val e σ1 κ1 e1 σ1' es1 σ2 κ2 e2 σ2' es2 :
  base_step e σ1 κ1 e1 σ1' es1 →
  base_step e σ2 κ2 e2 σ2' es2 →
  is_Some (to_val e1) →
  is_Some (to_val e2).
Proof.
  destruct 1; inversion 1; naive_solver.
Qed.
