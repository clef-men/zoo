Require Import iris.algebra.excl.

Require Import zoo.prelude.
Require Export zoo.iris.base_logic.lib.base.
Require Import zoo.iris.diaframe.
Require Import zoo.options.

Class ExclG Σ F :=
  { #[local] excl۰G۰inG :: inG Σ (exclR $ oFunctor_apply F $ iPropO Σ)
  }.

Definition excl۰Σ F `{!oFunctorContractive F} :=
  #[GFunctor (exclRF F)
  ].
#[global] Instance subG𑁒excl۰Σ Σ F `{!oFunctorContractive F} :
  subG (excl۰Σ F) Σ →
  ExclG Σ F.
Proof.
  solve_inG.
Qed.

Section excl۰G.
  Context `{excl۰G : !ExclG Σ F}.

  Definition excl γ a :=
    own γ (Excl a).

  #[global] Instance excl𑁒proper γ :
    Proper ((≡) ==> (≡)) (excl γ).
  Proof.
    solve_proper.
  Qed.

  #[global] Instance excl𑁒timeless γ a :
    Discrete a →
    Timeless (excl γ a).
  Proof.
    apply _.
  Qed.

  Lemma excl𑁒alloc a :
    ⊢ |==>
      ∃ γ,
      excl γ a.
  Proof.
    apply own_alloc. done.
  Qed.

  Lemma excl𑁒exclusive γ a1 a2 :
    excl γ a1 -∗
    excl γ a2 -∗
    False.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as "H".
    iApply (excl_validI with "H").
  Qed.

  Lemma excl𑁒update γ a b :
    excl γ a ⊢ |==>
    excl γ b.
  Proof.
    apply own_update, cmra_update_exclusive. done.
  Qed.
End excl۰G.

#[global] Opaque excl.
