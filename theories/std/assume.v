From zebre Require Import
  prelude.
From zebre.language Require Import
  notations
  diaframe.
From zebre.std Require Export
  base.
From zebre.std Require Import
  diverge.
From zebre Require Import
  options.

Definition assume : val :=
  λ: "b",
    ifnot: "b" then
      diverge ().

Section zebre_G.
  Context `{zebre_G : !ZebreG Σ}.

  Lemma assume_spec (b : bool) Φ :
    ▷ (⌜b = true⌝ → Φ ()%V) -∗
    WP assume #b {{ Φ }}.
  Proof.
    iIntros "HΦ".
    wp_rec. destruct b; first iSteps.
    wp_smart_apply diverge_spec.
  Qed.
  Lemma assume_spec' ϕ `{!Decision ϕ} Φ :
    ▷ (⌜ϕ⌝ → Φ ()%V) -∗
    WP assume #(bool_decide ϕ) {{ Φ }}.
  Proof.
    iIntros "HΦ".
    wp_apply assume_spec as (Hϕ%bool_decide_eq_true_1) "".
    iSteps.
  Qed.
End zebre_G.

#[global] Opaque assume.
