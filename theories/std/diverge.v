From zoo Require Import
  prelude.
From zoo.language Require Import
  notations
  diaframe.
From zoo.std Require Export
  base.
From zoo Require Import
  options.

Definition diverge : val :=
  rec: "diverge" <> =>
    "diverge" ().

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Implicit Types Φ : val → iProp Σ.

  Lemma diverge_spec E Φ :
    ⊢ WP diverge () @ E {{ Φ }}.
  Proof.
    iLöb as "IH". wp_rec. iSteps.
  Qed.
End zoo_G.

#[global] Opaque diverge.
