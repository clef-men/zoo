From Coq Require Export
  ZifyNat.

From zoo Require Import
  prelude.
From zoo Require Import
  options.

Section nat.
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

  Lemma minus_mod_1 a b n :
    b ≤ a →
    b `mod` n ≤ a `mod` n →
    (a `mod` n - b `mod` n) `mod` n = (a - b) `mod` n.
  Proof.
    intros.
    rewrite -(Nat2Z.id ((a `mod` n - b `mod` n) `mod` n)).
    rewrite Nat2Z.inj_mod Nat2Z.inj_sub // !Nat2Z.inj_mod -Zminus_mod.
    rewrite -Nat2Z.inj_sub // -Nat2Z.inj_mod Nat2Z.id //.
  Qed.
  Lemma minus_mod_1' a b n :
    n ≠ 0 →
    b ≤ a →
    b `mod` n ≤ a `mod` n →
    a `mod` n - b `mod` n = (a - b) `mod` n.
  Proof.
    intros.
    rewrite -(Nat.mod_small (a `mod` n - b `mod` n) n); first lia.
    rewrite minus_mod_1 //.
  Qed.
  Lemma minus_mod_1'' a b n :
    n ≠ 0 →
    a `mod` n ≤ (a + b) `mod` n →
    (a + b) `mod` n - a `mod` n = b `mod` n.
  Proof.
    intros.
    rewrite minus_mod_1' //; first lia.
    rewrite Nat.add_sub' //.
  Qed.
  Lemma minus_mod_2 a b n :
    n ≠ 0 →
    a ≤ b →
    b `mod` n ≤ a `mod` n →
    a `mod` n - b `mod` n = (n - (b - a) `mod` n) `mod` n.
  Proof.
    intros.
    rewrite -(Nat.mod_small (a `mod` n - b `mod` n) n); first lia.
    rewrite -(Nat2Z.id ((a `mod` n - b `mod` n) `mod` n)).
    rewrite Nat2Z.inj_mod Nat2Z.inj_sub // !Nat2Z.inj_mod -Zminus_mod.
    assert (a - b = - ⁺(b - a))%Z as -> by lia.
    destruct_decide (⁺(b - a) `mod` n = 0)%Z.
    - rewrite Z.mod_opp_l_z; [lia.. |].
      replace ((b - a) `mod` n) with 0 by lia.
      rewrite Nat.sub_0_r Nat.Div0.mod_same //.
    - rewrite Z.mod_opp_l_nz; [lia.. |].
      rewrite -Nat2Z.inj_mod -Nat2Z.inj_sub; first lia.
      rewrite Nat2Z.id.
      rewrite (Nat.mod_small (n - (b - a) `mod` n)) //; first lia.
  Qed.
End nat.

Section Z.
  #[local] Open Scope Z_scope.

  Lemma Z_rem_mod x y :
    0 ≤ x →
    0 ≤ y →
    x `rem` y = x `mod` y.
  Proof.
    intros Hx Hy.
    destruct_decide (y = 0) as -> | Hy'.
    - rewrite Z.mod_0_r_ext // Z.rem_0_r_ext //.
    - rewrite Z.rem_mod_nonneg //. lia.
  Qed.
End Z.
