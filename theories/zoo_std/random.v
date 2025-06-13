From zoo Require Import
  prelude.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Export
  base
  random__code.
From zoo Require Import
  options.

Axiom random_init_spec : ∀ `{zoo_G : !ZooG Σ} Φ,
  Φ ()%V ⊢
  WP random_init () {{ Φ }}.

Axiom random_bits_spec : ∀ `{zoo_G : !ZooG Σ} Φ,
  ( ∀ n : Z,
    Φ #n
  ) ⊢
  WP random_bits () {{ Φ }}.

Axiom random_int_spec : ∀ `{zoo_G : !ZooG Σ} ub Φ,
  (0 < ub)%Z →
  ( ∀ n,
    ⌜0 ≤ n < ub⌝%Z -∗
    Φ #n
  ) ⊢
  WP random_int #ub {{ Φ }}.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Lemma random_int_spec_nat (ub : nat) Φ :
    0 < ub →
    ( ∀ n,
      ⌜n < ub⌝ -∗
      Φ #n
    ) ⊢
    WP random_int #ub {{ Φ }}.
  Proof.
    iIntros "%Hub HΦ".
    wp_apply random_int_spec as (n) "%Hn"; first lia.
    Z_to_nat n. iSteps.
  Qed.

  Lemma random_int_in_range_spec lb ub Φ :
    (lb < ub)%Z →
    ( ∀ n,
      ⌜lb ≤ n < ub⌝%Z -∗
      Φ #n
    ) ⊢
    WP random_int_in_range #lb #ub {{ Φ }}.
  Proof.
    iIntros "%Hlt HΦ".
    wp_rec.
    wp_smart_apply random_int_spec as "%n %Hn"; first lia.
    iSteps.
  Qed.
  Lemma random_int_in_range_spec_nat lb ub Φ :
    lb < ub →
    ( ∀ n,
      ⌜lb ≤ n < ub⌝ -∗
      Φ #n
    ) ⊢
    WP random_int_in_range #lb #ub {{ Φ }}.
  Proof.
    iIntros "%Hlt HΦ".
    wp_rec.
    wp_smart_apply random_int_spec as "%n %Hn"; first lia.
    wp_pures.
    Z_to_nat n. rewrite -Nat2Z.inj_add. iSteps.
  Qed.
End zoo_G.

From zoo_std Require
  random__opaque.
