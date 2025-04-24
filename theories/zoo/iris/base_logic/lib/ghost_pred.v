From zoo Require Import
  prelude.
From zoo.iris.base_logic Require Export
  lib.base.
From zoo.iris.base_logic Require Import
  ghost_var.
From zoo.iris Require Import
  diaframe.
From zoo Require Import
  options.

Class GhostPredG Σ A := {
  #[local] ghost_pred_G_ghost_var_G :: GhostVarG Σ (A -d> ▶ ∙) ;
}.

Definition ghost_pred_Σ A := #[
  ghost_var_Σ (A -d> ▶ ∙)
].
#[global] Instance subG_ghost_pred_Σ Σ A :
  subG (ghost_pred_Σ A) Σ →
  GhostPredG Σ A.
Proof.
  solve_inG.
Qed.

Section ghost_pred_G.
  Context `{ghost_pred_G : !GhostPredG Σ A}.

  Implicit Types Ψ : A → iProp Σ.

  Definition ghost_pred γ dq Ψ :=
    ghost_var γ dq (Next ∘ Ψ).

  #[global] Instance ghost_pred_contractive γ dq n :
    Proper ((pointwise_relation _ (dist_later n)) ==> (≡{n}≡)) (ghost_pred γ dq).
  Proof.
    solve_contractive.
  Qed.
  #[global] Instance ghost_pred_proper γ dq :
    Proper ((≡) ==> (≡)) (ghost_pred γ dq : (A -d> iProp Σ) → _).
  Proof.
    solve_proper.
  Qed.

  #[global] Instance ghost_pred_persistent γ Ψ :
    Persistent (ghost_pred γ DfracDiscarded Ψ).
  Proof.
    apply _.
  Qed.

  #[global] Instance ghost_pred_fractional γ Ψ :
    Fractional (λ q, ghost_pred γ (DfracOwn q) Ψ).
  Proof.
    apply _.
  Qed.
  #[global] Instance ghost_pred_as_fractional γ Ψ q :
    AsFractional (ghost_pred γ (DfracOwn q) Ψ) (λ q, ghost_pred γ (DfracOwn q) Ψ) q.
  Proof.
    apply _.
  Qed.

  Lemma ghost_pred_alloc Ψ :
    ⊢ |==>
      ∃ γ,
      ghost_pred γ (DfracOwn 1) Ψ.
  Proof.
    apply ghost_var_alloc.
  Qed.
  Lemma ghost_pred_alloc_cofinite (γs : gset gname) Ψ :
    ⊢ |==>
      ∃ γ,
      ⌜γ ∉ γs⌝ ∗
      ghost_pred γ (DfracOwn 1) Ψ.
  Proof.
    apply ghost_var_alloc_cofinite.
  Qed.

  Lemma ghost_pred_valid γ dq Ψ :
    ghost_pred γ dq Ψ ⊢
    ⌜✓ dq⌝.
  Proof.
    apply ghost_var_valid.
  Qed.
  Lemma ghost_pred_combine {γ dq1 Ψ1 dq2 Ψ2} x :
    ghost_pred γ dq1 Ψ1 -∗
    ghost_pred γ dq2 Ψ2 -∗
      ▷ (Ψ1 x ≡ Ψ2 x) ∗
      ghost_pred γ (dq1 ⋅ dq2) Ψ1.
  Proof.
    iIntros "H1 H2".
    iDestruct (ghost_var_combine with "H1 H2") as "(? & $)".
    rewrite -later_equivI discrete_fun_equivI //.
  Qed.
  Lemma ghost_pred_valid_2 {γ dq1 Ψ1 dq2 Ψ2} x :
    ghost_pred γ dq1 Ψ1 -∗
    ghost_pred γ dq2 Ψ2 -∗
      ⌜✓ (dq1 ⋅ dq2)⌝ ∗
      ▷ (Ψ1 x ≡ Ψ2 x).
  Proof.
    iIntros "H1 H2".
    iDestruct (ghost_pred_combine with "H1 H2") as "($ & H)".
    iApply (ghost_var_valid with "H").
  Qed.
  Lemma ghost_pred_agree {γ dq1 Ψ1 dq2 Ψ2} x :
    ghost_pred γ dq1 Ψ1 -∗
    ghost_pred γ dq2 Ψ2 -∗
    ▷ (Ψ1 x ≡ Ψ2 x).
  Proof.
    iIntros "H1 H2".
    iDestruct (ghost_pred_valid_2 with "H1 H2") as "(_ & $)".
  Qed.
  Lemma ghost_pred_dfrac_ne γ1 dq1 Ψ1 γ2 dq2 Ψ2 :
    ¬ ✓ (dq1 ⋅ dq2) →
    ghost_pred γ1 dq1 Ψ1 -∗
    ghost_pred γ2 dq2 Ψ2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    apply ghost_var_dfrac_ne.
  Qed.
  Lemma ghost_pred_ne γ1 Ψ1 γ2 dq2 Ψ2 :
    ghost_pred γ1 (DfracOwn 1) Ψ1 -∗
    ghost_pred γ2 dq2 Ψ2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    apply ghost_var_ne.
  Qed.
  Lemma ghost_pred_exclusive γ Ψ1 dq2 Ψ2 :
    ghost_pred γ (DfracOwn 1) Ψ1 -∗
    ghost_pred γ dq2 Ψ2 -∗
    False.
  Proof.
    apply ghost_var_exclusive.
  Qed.
  Lemma ghost_pred_persist γ dq Ψ :
    ghost_pred γ dq Ψ ⊢ |==>
    ghost_pred γ DfracDiscarded Ψ.
  Proof.
    apply ghost_var_persist.
  Qed.

  Lemma ghost_pred_update {γ Ψ} Ψ' :
    ghost_pred γ (DfracOwn 1) Ψ ⊢ |==>
    ghost_pred γ (DfracOwn 1) Ψ'.
  Proof.
    apply ghost_var_update.
  Qed.
End ghost_pred_G.

#[global] Opaque ghost_pred.
