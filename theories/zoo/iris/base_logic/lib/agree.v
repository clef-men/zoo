Require Import iris.algebra.agree.

Require Import zoo.prelude.
Require Export zoo.iris.base_logic.lib.base.
Require Import zoo.iris.diaframe.
Require Import zoo.options.

Class AgreeG Σ F :=
  { #[local] agree۰G۰inG :: inG Σ (agreeR $ oFunctor_apply F $ iPropO Σ)
  }.

Definition agree۰Σ F `{!oFunctorContractive F} :=
  #[GFunctor (agreeRF F)
  ].
#[global] Instance subG𑁒agree۰Σ Σ F `{!oFunctorContractive F} :
  subG (agree۰Σ F) Σ →
  AgreeG Σ F.
Proof.
  solve_inG.
Qed.

Section agree۰G.
  Context `{agree۰G : !AgreeG Σ F}.

  Definition agree۰on γ a :=
    own γ (to_agree a).

  #[global] Instance agree۰on𑁒ne γ :
    NonExpansive (agree۰on γ).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance agree۰on𑁒proper γ :
    Proper ((≡) ==> (≡)) (agree۰on γ).
  Proof.
    solve_proper.
  Qed.

  #[global] Instance agree۰on𑁒timeless γ a :
    Discrete a →
    Timeless (agree۰on γ a).
  Proof.
    apply _.
  Qed.

  #[global] Instance agree۰on𑁒persistent γ a :
    Persistent (agree۰on γ a).
  Proof.
    apply _.
  Qed.

  Lemma agree𑁒alloc a :
    ⊢ |==>
      ∃ γ,
      agree۰on γ a.
  Proof.
    apply own_alloc. done.
  Qed.
  Lemma agree𑁒alloc𑁒cofinite (γs : gset gname) a :
    ⊢ |==>
      ∃ γ,
      ⌜γ ∉ γs⌝ ∗
      agree۰on γ a.
  Proof.
    apply own_alloc_cofinite. done.
  Qed.

  Lemma agree۰on𑁒agree γ a1 a2 :
    agree۰on γ a1 -∗
    agree۰on γ a2 -∗
    a1 ≡ a2.
  Proof.
    iIntros "H1 H2".
    iApply to_agree_op_validI.
    iApply (own_valid_2 with "H1 H2").
  Qed.
  Section discrete.
    Context `{!OfeDiscrete $ oFunctor_apply F $ iPropO Σ}.
    Lemma agree۰on𑁒agree𑁒discrete γ a1 a2 :
      agree۰on γ a1 -∗
      agree۰on γ a2 -∗
      ⌜a1 ≡ a2⌝.
    Proof.
      iIntros "H1 H2".
      iDestruct (agree۰on𑁒agree with "H1 H2") as %?.
      iSteps.
    Qed.
    Lemma agree۰on𑁒agree𑁒L `{!LeibnizEquiv $ oFunctor_apply F $ iPropO Σ} γ a1 a2 :
      agree۰on γ a1 -∗
      agree۰on γ a2 -∗
      ⌜a1 = a2⌝.
    Proof.
      iIntros "H1 H2".
      iDestruct (agree۰on𑁒agree𑁒discrete with "H1 H2") as %?%leibniz_equiv.
      iSteps.
    Qed.
  End discrete.
End agree۰G.

#[global] Opaque agree۰on.
