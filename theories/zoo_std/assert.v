Require Import zoo.prelude.
Require Import zoo.base.
Require Import zoo.options.

Definition assert : val :=
  𝗳𝘂𝗻 "b" ->
    𝗶𝗳 ~ "b" 𝘁𝗵𝗲𝗻
      𝗳𝗮𝗶𝗹.

Notation "'𝗮𝘀𝘀𝗲𝗿𝘁'" :=
  assert
: expr_scope.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  Lemma assertｰspec (b : bool) Φ :
    b = true →
    ▷ Φ ()%V -∗
    WP 𝗮𝘀𝘀𝗲𝗿𝘁 #b {{ Φ }}.
  Proof.
    iSteps.
  Qed.
End zoo۰G.

#[global] Opaque assert.
