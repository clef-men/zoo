From zoo Require Import
  prelude.
From zoo.language Require Import
  notations
  diaframe.
From zoo_std Require Export
  base.
From zoo Require Import
  options.

Definition assert : val :=
  fun: "b" =>
    ifnot: "b" then
      Fail.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Lemma assert_spec (b : bool) Φ :
    b = true →
    ▷ Φ ()%V -∗
    WP assert #b {{ Φ }}.
  Proof.
    iSteps.
  Qed.
End zoo_G.

#[global] Opaque assert.
