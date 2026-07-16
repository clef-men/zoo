Require Import zoo.prelude.
Require Import zoo.base.
Require Export zoo_std.random__code.
Require Import zoo.options.

Axiom random٠init𑁒spec : ∀ `{zoo۰G : !ZooG Σ} Φ,
  Φ ()%V ⊢
  WP random٠init () {{ Φ }}.

Axiom random٠bits𑁒spec : ∀ `{zoo۰G : !ZooG Σ} Φ,
  ( ∀ n : Z,
    Φ #n
  ) ⊢
  WP random٠bits () {{ Φ }}.

Axiom random٠int𑁒spec : ∀ `{zoo۰G : !ZooG Σ} ub Φ,
  (0 < ub)%Z →
  ( ∀ n,
    ⌜0 ≤ n < ub⌝%Z -∗
    Φ #n
  ) ⊢
  WP random٠int #ub {{ Φ }}.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  Lemma random٠int𑁒spec𑁒nat (ub : nat) Φ :
    0 < ub →
    ( ∀ n,
      ⌜n < ub⌝ -∗
      Φ #n
    ) ⊢
    WP random٠int #ub {{ Φ }}.
  Proof.
    iIntros "%Hub HΦ".
    wp۰apply random٠int𑁒spec as (n) "%Hn"; first lia.
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
    wp۰rec.
    wp۰apply+ random٠int𑁒spec as "%n %Hn"; first lia.
    iSteps.
  Qed.
  Lemma random٠int_in_range𑁒spec𑁒nat lb ub Φ :
    lb < ub →
    ( ∀ n,
      ⌜lb ≤ n < ub⌝ -∗
      Φ #n
    ) ⊢
    WP random٠int_in_range #lb #ub {{ Φ }}.
  Proof.
    iIntros "%Hlt HΦ".
    wp۰rec.
    wp۰apply+ random٠int𑁒spec as "%n %Hn"; first lia.
    wp۰pures.
    Z_to_nat n. rewrite -Nat2Z.inj_add. iSteps.
  Qed.
End zoo۰G.

Require zoo_std.random__opaque.
