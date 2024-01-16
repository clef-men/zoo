From zebra Require Import
  prelude.
From zebra.language Require Import
  notations
  diaframe.
From zebra.std Require Export
  base.
From zebra.std Require Import
  diverge.
From zebra Require Import
  options.

Definition assume : val :=
  λ: "b",
    ifnot: "b" then
      diverge #().

Section zebra_G.
  Context `{zebra_G : !ZebraG Σ}.

  Lemma assume_spec (b : bool) Φ :
    ▷ (⌜b = true⌝ → Φ #()) -∗
    WP assume #b {{ Φ }}.
  Proof.
    iIntros "HΦ".
    wp_rec. destruct b; first iSteps.
    wp_smart_apply diverge_spec.
  Qed.
  Lemma assume_spec' ϕ `{!Decision ϕ} Φ :
    ▷ (⌜ϕ⌝ → Φ #()) -∗
    WP assume #(bool_decide ϕ) {{ Φ }}.
  Proof.
    iIntros "HΦ".
    wp_apply assume_spec as (Hϕ%bool_decide_eq_true_1) "".
    iSteps.
  Qed.
End zebra_G.

#[global] Opaque assume.
