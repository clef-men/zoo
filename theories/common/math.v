From zoo Require Import
  prelude.
From zoo Require Import
  options.

#[global] Instance ge_partialorder :
  PartialOrder ge.
Proof.
  split; first split.
  - auto.
  - intros ?**. lia.
  - intros ?**. lia.
Qed.

Section Z.
  #[local] Open Scope Z_scope.

  Lemma Z_rem_mod x y :
    0 ≤ x →
    0 ≤ y →
    x `rem` y = x `mod` y.
  Proof.
    intros Hx Hy.
    destruct (decide (y = 0)) as [-> | Hy'].
    - rewrite Z.mod_0_r_ext // Z.rem_0_r_ext //.
    - rewrite Z.rem_mod_nonneg //. lia.
  Qed.
End Z.
