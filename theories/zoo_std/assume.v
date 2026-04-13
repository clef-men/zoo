From zoo Require Import
  prelude.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Export
  base.
From zoo_std Require Import
  diverge.
From zoo Require Import
  options.

Definition assume : val :=
  fun: "b" =>
    if: ~ "b" then
      diverge ().

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Lemma assume𑁒spec (b : bool) Φ :
    ▷ (⌜b = true⌝ → Φ ()%V) -∗
    WP assume #b {{ Φ }}.
  Proof.
    iIntros "HΦ".
    wp_rec. destruct b; first iSteps.
    wp_apply+ diverge𑁒spec.
  Qed.
  Lemma assume𑁒spec' ϕ `{!Decision ϕ} Φ :
    ▷ (⌜ϕ⌝ → Φ ()%V) -∗
    WP assume #(bool_decide ϕ) {{ Φ }}.
  Proof.
    iIntros "HΦ".
    wp_apply assume𑁒spec as (Hϕ%bool_decide_eq_true_1) "".
    iSteps.
  Qed.
End zoo_G.

#[global] Opaque assume.
