Require Import zoo.prelude.
Require Import zoo.base.
Require Import zoo.options.

Definition assert : val :=
  fun: "b" =>
    if: ~ "b" then
      Fail.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Lemma assert𑁒spec (b : bool) Φ :
    b = true →
    ▷ Φ ()%V -∗
    WP assert #b {{ Φ }}.
  Proof.
    iSteps.
  Qed.
End zoo_G.

#[global] Opaque assert.
