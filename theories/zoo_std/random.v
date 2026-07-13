Require Import zoo.prelude.
Require Import zoo.base.
Require Export zoo_std.random__code.
Require Import zoo.options.

Axiom random٠init𑁒spec : ∀ `{zoo_G : !ZooG Σ} Φ,
  Φ ()%V ⊢
  WP random٠init () {{ Φ }}.

Axiom random٠bits𑁒spec : ∀ `{zoo_G : !ZooG Σ} Φ,
  ( ∀ n : Z,
    Φ #n
  ) ⊢
  WP random٠bits () {{ Φ }}.

Axiom random٠int𑁒spec : ∀ `{zoo_G : !ZooG Σ} ub Φ,
  (0 < ub)%Z →
  ( ∀ n,
    ⌜0 ≤ n < ub⌝%Z -∗
    Φ #n
  ) ⊢
  WP random٠int #ub {{ Φ }}.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Lemma random٠int𑁒spec_nat (ub : nat) Φ :
    0 < ub →
    ( ∀ n,
      ⌜n < ub⌝ -∗
      Φ #n
    ) ⊢
    WP random٠int #ub {{ Φ }}.
  Proof.
    iIntros "%Hub HΦ".
    wp_apply random٠int𑁒spec as (n) "%Hn"; first lia.
    Z_to_nat n. iSteps.
  Qed.

  Lemma random٠int_in_range𑁒spec lb ub Φ :
    (lb < ub)%Z →
    ( ∀ n,
      ⌜lb ≤ n < ub⌝%Z -∗
      Φ #n
    ) ⊢
    WP random٠int_in_range #lb #ub {{ Φ }}.
  Proof.
    iIntros "%Hlt HΦ".
    wp_rec.
    wp_apply+ random٠int𑁒spec as "%n %Hn"; first lia.
    iSteps.
  Qed.
  Lemma random٠int_in_range𑁒spec_nat lb ub Φ :
    lb < ub →
    ( ∀ n,
      ⌜lb ≤ n < ub⌝ -∗
      Φ #n
    ) ⊢
    WP random٠int_in_range #lb #ub {{ Φ }}.
  Proof.
    iIntros "%Hlt HΦ".
    wp_rec.
    wp_apply+ random٠int𑁒spec as "%n %Hn"; first lia.
    wp_pures.
    Z_to_nat n. rewrite -Nat2Z.inj_add. iSteps.
  Qed.
End zoo_G.

Require zoo_std.random__opaque.
