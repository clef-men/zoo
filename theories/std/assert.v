From zebre Require Import
  prelude.
From zebre.language Require Import
  notations
  diaframe.
From zebre.std Require Export
  base.
From zebre Require Import
  options.

Definition assert : val :=
  λ: "b",
    ifnot: "b" then
      Fail.

Section zebre_G.
  Context `{zebre_G : !ZebreG Σ}.

  Lemma assert_spec (b : bool) Φ :
    b = true →
    ▷ Φ ()%V -∗
    WP assert #b {{ Φ }}.
  Proof.
    iSteps.
  Qed.
End zebre_G.

#[global] Opaque assert.
