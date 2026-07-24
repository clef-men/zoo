Require Import zoo.prelude.
Require Export zoo.iris.base_logic.lib.base.
Require Import zoo.iris.base_logic.lib.ghost_var.
Require Import zoo.iris.diaframe.
Require Import zoo.options.

Class GhostPredG Σ A :=
  { #[local] ghost_pred۰G۰ghost_var۰G :: GhostVarG Σ (A -d> ▶ ∙)
  }.

Definition ghost_pred۰Σ A :=
  #[ghost_var۰Σ (A -d> ▶ ∙)
  ].
#[global] Instance subG𑁒ghost_pred۰Σ Σ A :
  subG (ghost_pred۰Σ A) Σ →
  GhostPredG Σ A.
Proof.
  solve_inG.
Qed.

Section ghost_pred۰G.
  Context `{ghost_pred۰G : !GhostPredG Σ A}.

  Implicit Type Ψ : A → iProp Σ.

  Definition ghost_pred γ dq Ψ :=
    ghost_var γ dq (Next ∘ Ψ).

  #[global] Instance ghost_pred𑁒contractive γ dq n :
    Proper ((pointwise_relation _ (dist_later n)) ==> (≡{n}≡)) (ghost_pred γ dq).
  Proof.
    solve_contractive.
  Qed.
  #[global] Instance ghost_pred𑁒proper γ dq :
    Proper ((≡) ==> (≡)) (ghost_pred γ dq : (A -d> iProp Σ) → _).
  Proof.
    solve_proper.
  Qed.

  #[global] Instance ghost_pred𑁒persistent γ Ψ :
    Persistent (ghost_pred γ DfracDiscarded Ψ).
  Proof.
    apply _.
  Qed.

  #[global] Instance ghost_pred𑁒fractional γ Ψ :
    Fractional (λ q, ghost_pred γ (DfracOwn q) Ψ).
  Proof.
    apply _.
  Qed.
  #[global] Instance ghost_pred𑁒as_fractional γ Ψ q :
    AsFractional (ghost_pred γ (DfracOwn q) Ψ) (λ q, ghost_pred γ (DfracOwn q) Ψ) q.
  Proof.
    apply _.
  Qed.

  Lemma ghost_pred𑁒alloc Ψ :
    ⊢ |==>
      ∃ γ,
      ghost_pred γ (DfracOwn 1) Ψ.
  Proof.
    apply ghost_var𑁒alloc.
  Qed.
  Lemma ghost_pred𑁒alloc𑁒cofinite (γs : gset gname) Ψ :
    ⊢ |==>
      ∃ γ,
      ⌜γ ∉ γs⌝ ∗
      ghost_pred γ (DfracOwn 1) Ψ.
  Proof.
    apply ghost_var𑁒alloc𑁒cofinite.
  Qed.

  Lemma ghost_pred𑁒valid γ dq Ψ :
    ghost_pred γ dq Ψ ⊢
    ⌜✓ dq⌝.
  Proof.
    apply ghost_var𑁒valid.
  Qed.
  Lemma ghost_pred𑁒combine {γ dq1 Ψ1 dq2 Ψ2} x :
    ghost_pred γ dq1 Ψ1 -∗
    ghost_pred γ dq2 Ψ2 -∗
      ▷ (Ψ1 x ≡ Ψ2 x) ∗
      ghost_pred γ (dq1 ⋅ dq2) Ψ1.
  Proof.
    iIntros "H1 H2".
    iDestruct (ghost_var𑁒combine with "H1 H2") as "(? & $)".
    rewrite -later_equivI discrete_fun_equivI //.
  Qed.
  Lemma ghost_pred𑁒valid𑁒2 {γ dq1 Ψ1 dq2 Ψ2} x :
    ghost_pred γ dq1 Ψ1 -∗
    ghost_pred γ dq2 Ψ2 -∗
      ⌜✓ (dq1 ⋅ dq2)⌝ ∗
      ▷ (Ψ1 x ≡ Ψ2 x).
  Proof.
    iIntros "H1 H2".
    iDestruct (ghost_pred𑁒combine with "H1 H2") as "($ & H)".
    iApply (ghost_var𑁒valid with "H").
  Qed.
  Lemma ghost_pred𑁒agree {γ dq1 Ψ1 dq2 Ψ2} x :
    ghost_pred γ dq1 Ψ1 -∗
    ghost_pred γ dq2 Ψ2 -∗
    ▷ (Ψ1 x ≡ Ψ2 x).
  Proof.
    iIntros "H1 H2".
    iDestruct (ghost_pred𑁒valid𑁒2 with "H1 H2") as "(_ & $)".
  Qed.
  Lemma ghost_pred𑁒dfrac𑁒ne γ1 dq1 Ψ1 γ2 dq2 Ψ2 :
    ¬ ✓ (dq1 ⋅ dq2) →
    ghost_pred γ1 dq1 Ψ1 -∗
    ghost_pred γ2 dq2 Ψ2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    apply ghost_var𑁒dfrac𑁒ne.
  Qed.
  Lemma ghost_pred𑁒ne γ1 Ψ1 γ2 dq2 Ψ2 :
    ghost_pred γ1 (DfracOwn 1) Ψ1 -∗
    ghost_pred γ2 dq2 Ψ2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    apply ghost_var𑁒ne.
  Qed.
  Lemma ghost_pred𑁒exclusive γ Ψ1 dq2 Ψ2 :
    ghost_pred γ (DfracOwn 1) Ψ1 -∗
    ghost_pred γ dq2 Ψ2 -∗
    False.
  Proof.
    apply ghost_var𑁒exclusive.
  Qed.
  Lemma ghost_pred𑁒persist γ dq Ψ :
    ghost_pred γ dq Ψ ⊢ |==>
    ghost_pred γ DfracDiscarded Ψ.
  Proof.
    apply ghost_var𑁒persist.
  Qed.

  Lemma ghost_pred𑁒update {γ Ψ} Ψ' :
    ghost_pred γ (DfracOwn 1) Ψ ⊢ |==>
    ghost_pred γ (DfracOwn 1) Ψ'.
  Proof.
    apply ghost_var𑁒update.
  Qed.
End ghost_pred۰G.

#[global] Opaque ghost_pred.
