From zebre Require Import
  prelude.
From zebre.language Require Import
  notations
  diaframe.
From zebre.std Require Export
  base.
From zebre Require Import
  options.

Definition diverge : val :=
  rec: "diverge" <> :=
    "diverge" ().

Section zebre_G.
  Context `{zebre_G : !ZebreG Σ}.

  Implicit Types Φ : val → iProp Σ.

  Lemma diverge_spec E Φ :
    ⊢ WP diverge () @ E {{ Φ }}.
  Proof.
    iLöb as "IH". wp_rec. iSteps.
  Qed.
End zebre_G.

#[global] Opaque diverge.
