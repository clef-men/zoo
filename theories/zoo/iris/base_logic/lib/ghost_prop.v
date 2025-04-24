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

Class GhostPropG Σ := {
  #[local] ghost_prop_G_ghost_var_G :: GhostVarG Σ (▶ ∙) ;
}.

Definition ghost_prop_Σ := #[
  ghost_var_Σ (▶ ∙)
].
#[global] Instance subG_ghost_prop_Σ Σ :
  subG ghost_prop_Σ Σ →
  GhostPropG Σ.
Proof.
  solve_inG.
Qed.

Section ghost_prop_G.
  Context `{ghost_prop_G : !GhostPropG Σ}.

  Implicit Types P : iProp Σ.

  Definition ghost_prop γ dq P :=
    ghost_var γ dq (Next P).

  #[global] Instance ghost_prop_contractive γ dq :
    Contractive (ghost_prop γ dq).
  Proof.
    solve_contractive.
  Qed.
  #[global] Instance ghost_prop_proper γ dq :
    Proper ((≡) ==> (≡)) (ghost_prop γ dq).
  Proof.
    apply _.
  Qed.

  #[global] Instance ghost_prop_persistent γ P :
    Persistent (ghost_prop γ DfracDiscarded P).
  Proof.
    apply _.
  Qed.

  #[global] Instance ghost_prop_fractional γ P :
    Fractional (λ q, ghost_prop γ (DfracOwn q) P).
  Proof.
    apply _.
  Qed.
  #[global] Instance ghost_prop_as_fractional γ P q :
    AsFractional (ghost_prop γ (DfracOwn q) P) (λ q, ghost_prop γ (DfracOwn q) P) q.
  Proof.
    apply _.
  Qed.

  Lemma ghost_prop_alloc P :
    ⊢ |==>
      ∃ γ,
      ghost_prop γ (DfracOwn 1) P.
  Proof.
    apply ghost_var_alloc.
  Qed.
  Lemma ghost_prop_alloc_cofinite (γs : gset gname) P :
    ⊢ |==>
      ∃ γ,
      ⌜γ ∉ γs⌝ ∗
      ghost_prop γ (DfracOwn 1) P.
  Proof.
    apply ghost_var_alloc_cofinite.
  Qed.

  Lemma ghost_prop_valid γ dq P :
    ghost_prop γ dq P ⊢
    ⌜✓ dq⌝.
  Proof.
    apply ghost_var_valid.
  Qed.
  Lemma ghost_prop_combine γ dq1 P1 dq2 P2 :
    ghost_prop γ dq1 P1 -∗
    ghost_prop γ dq2 P2 -∗
      ▷ (P1 ≡ P2) ∗
      ghost_prop γ (dq1 ⋅ dq2) P1.
  Proof.
    rewrite -later_equivI.
    apply: ghost_var_combine.
  Qed.
  Lemma ghost_prop_valid_2 γ dq1 P1 dq2 P2 :
    ghost_prop γ dq1 P1 -∗
    ghost_prop γ dq2 P2 -∗
      ⌜✓ (dq1 ⋅ dq2)⌝ ∗
      ▷ (P1 ≡ P2).
  Proof.
    rewrite -later_equivI.
    apply: ghost_var_valid_2.
  Qed.
  Lemma ghost_prop_agree γ dq1 P1 dq2 P2 :
    ghost_prop γ dq1 P1 -∗
    ghost_prop γ dq2 P2 -∗
    ▷ (P1 ≡ P2).
  Proof.
    rewrite -later_equivI.
    apply: ghost_var_agree.
  Qed.
  Lemma ghost_prop_dfrac_ne γ1 dq1 P1 γ2 dq2 P2 :
    ¬ ✓ (dq1 ⋅ dq2) →
    ghost_prop γ1 dq1 P1 -∗
    ghost_prop γ2 dq2 P2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    apply ghost_var_dfrac_ne.
  Qed.
  Lemma ghost_prop_ne γ1 P1 γ2 dq2 P2 :
    ghost_prop γ1 (DfracOwn 1) P1 -∗
    ghost_prop γ2 dq2 P2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    apply ghost_var_ne.
  Qed.
  Lemma ghost_prop_exclusive γ P1 dq2 P2 :
    ghost_prop γ (DfracOwn 1) P1 -∗
    ghost_prop γ dq2 P2 -∗
    False.
  Proof.
    apply ghost_var_exclusive.
  Qed.
  Lemma ghost_prop_persist γ dq P :
    ghost_prop γ dq P ⊢ |==>
    ghost_prop γ DfracDiscarded P.
  Proof.
    apply ghost_var_persist.
  Qed.

  Lemma ghost_prop_update {γ P} P' :
    ghost_prop γ (DfracOwn 1) P ⊢ |==>
    ghost_prop γ (DfracOwn 1) P'.
  Proof.
    apply ghost_var_update.
  Qed.
End ghost_prop_G.

#[global] Opaque ghost_prop.
