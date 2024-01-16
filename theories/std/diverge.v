From zebra Require Import
  prelude.
From zebra.language Require Import
  notations
  diaframe.
From zebra.std Require Export
  base.
From zebra Require Import
  options.

Definition diverge : val :=
  rec: "diverge" <> :=
    "diverge" #().

Section zebra_G.
  Context `{zebra_G : !ZebraG Σ}.

  Implicit Types Φ : val → iProp Σ.

  Lemma diverge_spec E Φ :
    ⊢ WP diverge #() @ E {{ Φ }}.
  Proof.
    iLöb as "IH". wp_rec. iSteps.
  Qed.
End zebra_G.

#[global] Opaque diverge.
