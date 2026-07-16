Require Export Stdlib.micromega.ZifyNat.

Require Export stdpp.numbers.

Require Import zoo.prelude.
Require Import zoo.common.relations.
Require Import zoo.options.

Section nat.
  #[global] Instance b2n𑁒inj :
    Inj (=) (=) Nat.b2n.
  Proof.
    intros [] []; done.
  Qed.

  Definition nat۰elim {A} (x : A) f n :=
    match n with
    | 0 =>
        x
    | ˖n =>
        f n
    end.
  #[global] Arguments nat۰elim _ _ _ !_ / : assert.

  #[global] Instance ge𑁒partialorder :
    PartialOrder ge.
  Proof.
    split; first split.
    - auto.
    - intros ?**. lia.
    - intros ?**. lia.
  Qed.

  #[global] Instance le𑁒initial : Initial (≤) :=
    {|initial := 0
    ; initial𑁒lb := Nat.le_0_l
    |}.

  Lemma minus𑁒mod₁ a b n :
    b ≤ a →
    b `mod` n ≤ a `mod` n →
    (a `mod` n - b `mod` n) `mod` n = (a - b) `mod` n.
  Proof.
    intros.
    rewrite -(Nat2Z.id ((a `mod` n - b `mod` n) `mod` n)).
    rewrite Nat2Z.inj_mod Nat2Z.inj_sub // !Nat2Z.inj_mod -Zminus_mod.
    rewrite -Nat2Z.inj_sub // -Nat2Z.inj_mod Nat2Z.id //.
  Qed.
  Lemma minus𑁒mod₁' a b n :
    n ≠ 0 →
    b ≤ a →
    b `mod` n ≤ a `mod` n →
    a `mod` n - b `mod` n = (a - b) `mod` n.
  Proof.
    intros.
    rewrite -(Nat.mod_small (a `mod` n - b `mod` n) n); first lia.
    rewrite minus𑁒mod₁ //.
  Qed.
  Lemma minus𑁒mod₁'' a b n :
    n ≠ 0 →
    a `mod` n ≤ (a + b) `mod` n →
    (a + b) `mod` n - a `mod` n = b `mod` n.
  Proof.
    intros.
    rewrite minus𑁒mod₁' //; first lia.
    rewrite Nat.add_sub' //.
  Qed.
  Lemma minus𑁒mod₂ a b n :
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

Notation "(≥)" :=
  Z.ge
( only parsing
) : Z_scope.

Section Z.
  #[local] Open Scope Z_scope.

  Lemma Z𑁒rem𑁒mod x y :
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

Section Qp۰of_nat.
  Implicit Types n : nat.

  Definition Qp۰of_nat :=
    pos_to_Qp ∘ Pos.of_nat.

  Lemma Qp۰of_nat𑁒1 :
    Qp۰of_nat 1 = 1%Qp.
  Proof.
    done.
  Qed.
  Lemma Qp۰of_nat𑁒S n :
    n ≠ 0 →
    Qp۰of_nat ˖n = (1 + Qp۰of_nat n)%Qp.
  Proof.
    intros Hn.
    rewrite /Qp۰of_nat /=.
    rewrite Nat2Pos.inj_succ //.
    rewrite pos_to_Qp_add Pos.add_1_l //.
  Qed.
End Qp۰of_nat.
