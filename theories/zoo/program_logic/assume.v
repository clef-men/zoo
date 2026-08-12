Require Import zoo.prelude.
Require Import zoo.base.
Require Import zoo.program_logic.diverge.
Require Import zoo.options.

Definition assume : val :=
  𝗳𝘂𝗻 "b" ->
    𝗶𝗳 ~ "b" 𝘁𝗵𝗲𝗻
      𝗱𝗶𝘃𝗲𝗿𝗴𝗲 ().

Notation "'𝗮𝘀𝘀𝘂𝗺𝗲'" :=
  assume
: expr_scope.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  Lemma assumeｰspec (b : bool) Φ :
    ▷ (⌜b = true⌝ → Φ ()%V) -∗
    WP 𝗮𝘀𝘀𝘂𝗺𝗲 #b {{ Φ }}.
  Proof.
    iIntros "HΦ".
    wp۰rec. destruct b; first iSteps.
    wp۰apply+ divergeｰspec.
  Qed.
  Lemma assumeｰspec' ϕ `{!Decision ϕ} Φ :
    ▷ (⌜ϕ⌝ → Φ ()%V) -∗
    WP 𝗮𝘀𝘀𝘂𝗺𝗲 #(bool_decide ϕ) {{ Φ }}.
  Proof.
    iIntros "HΦ".
    wp۰apply assumeｰspec as (Hϕ%bool_decide_eq_true_1) "".
    iSteps.
  Qed.
End zoo۰G.

#[global] Opaque assume.
