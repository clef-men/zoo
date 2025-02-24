From zoo Require Import
  prelude.
From zoo Require Import
  options.

#[global] Instance b2n_inj :
  Inj (=) (=) Nat.b2n.
Proof.
  intros [] []; done.
Qed.

Definition nat_elim {A} (x : A) f n :=
  match n with
  | 0 =>
      x
  | S n =>
      f n
  end.
#[global] Arguments nat_elim _ _ _ !_ / : assert.

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
