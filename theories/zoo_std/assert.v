Require Import zoo.prelude.
Require Import zoo.base.
Require Import zoo.options.

Definition assert : val :=
  fun: "b" =>
    if: ~ "b" then
      Fail.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  Lemma assert𑁒spec (b : bool) Φ :
    b = true →
    ▷ Φ ()%V -∗
    WP assert #b {{ Φ }}.
  Proof.
    iSteps.
  Qed.
End zoo۰G.

#[global] Opaque assert.
