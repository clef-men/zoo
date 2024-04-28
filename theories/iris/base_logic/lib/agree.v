From iris.algebra Require Import
  agree.

From zebre Require Import
  prelude.
From zebre.iris.base_logic Require Export
  lib.base.
From zebre.iris Require Import
  diaframe.
From zebre Require Import
  options.

Class AgreeG Σ F := {
  #[local] agree_G_inG :: inG Σ (agreeR $ oFunctor_apply F $ iPropO Σ) ;
}.

Definition agree_Σ F `{!oFunctorContractive F} := #[
  GFunctor (agreeRF F)
].
#[global] Instance subG_agree_Σ Σ F `{!oFunctorContractive F} :
  subG (agree_Σ F) Σ →
  AgreeG Σ F.
Proof.
  solve_inG.
Qed.

Section agree_G.
  Context `{agree_G : !AgreeG Σ F}.

  Definition agree_on γ a :=
    own γ (to_agree a).

  #[global] Instance agree_on_proper γ :
    Proper ((≡) ==> (≡)) (agree_on γ).
  Proof.
    solve_proper.
  Qed.

  #[global] Instance agree_on_timeless γ a :
    Discrete a →
    Timeless (agree_on γ a).
  Proof.
    apply _.
  Qed.
  #[global] Instance agree_on_persistent γ a :
    Persistent (agree_on γ a).
  Proof.
    apply _.
  Qed.

  Lemma agree_alloc a :
    ⊢ |==>
      ∃ γ,
      agree_on γ a.
  Proof.
    apply own_alloc. done.
  Qed.
  Lemma agree_alloc_cofinite (γs : gset gname) a :
    ⊢ |==>
      ∃ γ,
      ⌜γ ∉ γs⌝ ∗
      agree_on γ a.
  Proof.
    apply own_alloc_cofinite. done.
  Qed.

  Lemma agree_on_agree γ a1 a2 :
    agree_on γ a1 -∗
    agree_on γ a2 -∗
    a1 ≡ a2.
  Proof.
    iIntros "H1 H2".
    iApply to_agree_op_validI.
    iApply (own_valid_2 with "H1 H2").
  Qed.
  Section discrete.
    Context `{!OfeDiscrete $ oFunctor_apply F $ iPropO Σ}.
    Lemma agree_on_agree_discrete γ a1 a2 :
      agree_on γ a1 -∗
      agree_on γ a2 -∗
      ⌜a1 ≡ a2⌝.
    Proof.
      iIntros "H1 H2".
      iDestruct (agree_on_agree with "H1 H2") as %?.
      iSteps.
    Qed.
    Lemma agree_on_agree_L `{!LeibnizEquiv $ oFunctor_apply F $ iPropO Σ} γ a1 a2 :
      agree_on γ a1 -∗
      agree_on γ a2 -∗
      ⌜a1 = a2⌝.
    Proof.
      iIntros "H1 H2".
      iDestruct (agree_on_agree_discrete with "H1 H2") as %?%leibniz_equiv.
      iSteps.
    Qed.
  End discrete.
End agree_G.

#[global] Opaque agree_on.
