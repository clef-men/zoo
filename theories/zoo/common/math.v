Require Export Stdlib.micromega.ZifyNat.

Require Export stdpp.numbers.

Require Import zoo.prelude.
Require Import zoo.common.relations.
Require Import zoo.options.

Section nat.
  #[global] Instance b2nｰinj :
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

  #[global] Instance geｰpartialorder :
    PartialOrder ge.
  Proof.
    split; first split.
    - auto.
    - intros ?**. lia.
    - intros ?**. lia.
  Qed.

  #[global] Instance leｰinitial : Initial (≤) :=
    {|initial := 0
    ; initialｰlb := Nat.le_0_l
    |}.

  Lemma minusｰmod₁ a b n :
    b ≤ a →
    b `mod` n ≤ a `mod` n →
    (a `mod` n - b `mod` n) `mod` n = (a - b) `mod` n.
  Proof.
    intros.
    rewrite -(Nat2Z.id ((a `mod` n - b `mod` n) `mod` n)).
    rewrite Nat2Z.inj_mod Nat2Z.inj_sub // !Nat2Z.inj_mod -Zminus_mod.
    rewrite -Nat2Z.inj_sub // -Nat2Z.inj_mod Nat2Z.id //.
  Qed.
  Lemma minusｰmod₁' a b n :
    n ≠ 0 →
    b ≤ a →
    b `mod` n ≤ a `mod` n →
    a `mod` n - b `mod` n = (a - b) `mod` n.
  Proof.
    intros.
    rewrite -(Nat.mod_small (a `mod` n - b `mod` n) n); first lia.
    rewrite minusｰmod₁ //.
  Qed.
  Lemma minusｰmod₁'' a b n :
    n ≠ 0 →
    a `mod` n ≤ (a + b) `mod` n →
    (a + b) `mod` n - a `mod` n = b `mod` n.
  Proof.
    intros.
    rewrite minusｰmod₁' //; first lia.
    rewrite Nat.add_sub' //.
  Qed.
  Lemma minusｰmod₂ a b n :
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

  Lemma Zｰremｰmod x y :
    0 ≤ x →
    0 ≤ y →
    x `rem` y = x `mod` y.
  Proof.
    intros Hx Hy.
    destruct_decide (y = 0) as -> | Hy'.
    - rewrite Z.mod_0_r_ext // Z.rem_0_r_ext //.
    - rewrite Z.rem_mod_nonneg //. lia.
  Qed.

  Definition Z۰to_nat n :=
    match n with
    | 0 =>
        Some 0%nat
    | Z.pos n =>
        Some $ Pos.to_nat n
    | Z.neg _ =>
        None
    end.
End Z.

Section pow2.
  Definition is_pow2 (n : nat) :=
    ∃ k,
    n = 2 ^ k.

  Lemma is_pow2ｰpos n :
    is_pow2 n →
    0 < n.
  Proof.
    intros (k & ->). apply Nat.neq_0_lt_0, Nat.pow_nonzero. done.
  Qed.
  Lemma is_pow2ｰdouble n :
    is_pow2 n →
    is_pow2 (2 * n).
  Proof.
    intros (k & ->). exists ˖k. done.
  Qed.
  Lemma is_pow2ｰhalf n :
    is_pow2 n →
    1 < n →
      is_pow2 (n / 2) ∧
      n = 2 * (n / 2).
  Proof.
    intros (k & ->) Hn.
    destruct k as [| k]; first (simpl in Hn; lia).
    rewrite Nat.pow_succ_r' (Nat.mul_comm 2) Nat.div_mul //.
    split; first by exists k. lia.
  Qed.

  Lemma Zｰof_natｰpow2 k :
    ⁺(2 ^ k) = (2 ^ ⁺k)%Z.
  Proof.
    rewrite Nat2Z.inj_pow //.
  Qed.

  Lemma Zｰmodｰmulｰr (a b c : Z) :
    (0 < b)%Z →
    (0 < c)%Z →
    (a `mod` (b * c) = a `mod` b + b * ((a `div` b) `mod` c))%Z.
  Proof.
    intros Hb Hc.
    symmetry. apply Z.mod_unique with (Z.div (Z.div a b) c).
    - pose proof (Z.mod_pos_bound a b Hb).
      pose proof (Z.mod_pos_bound (Z.div a b) c Hc).
      left. nia.
    - pose proof (Z.div_mod a b ltac:(lia)) as H1.
      pose proof (Z.div_mod (Z.div a b) c ltac:(lia)) as H2.
      set q := Z.div a b in H1 H2 |- *.
      set q' := Z.div q c in H2 |- *.
      set r := Z.modulo q c in H2 |- *.
      nia.
  Qed.

  Lemma Zｰlandｰpow2ｰpred (h : Z) (n : nat) :
    is_pow2 n →
    (Z.land h (⁺n - 1) = h `mod` ⁺n)%Z.
  Proof.
    intros (k & ->).
    rewrite Zｰof_natｰpow2 -Z.land_ones; first lia.
    rewrite Z.ones_equiv. f_equal; lia.
  Qed.

  Lemma Zｰlandｰpow2 (h : Z) (n : nat) :
    is_pow2 n →
    (Z.land h ⁺n = ⁺n * Z.b2z (Z.testbit h (Z.log2 ⁺n)))%Z.
  Proof.
    intros (k & ->).
    rewrite Zｰof_natｰpow2 Z.log2_pow2; first lia.
    apply Z.bits_inj'. intros m Hm.
    rewrite Z.land_spec Z.pow2_bits_eqb; first lia.
    destruct (Z.testbit h ⁺k) eqn:Hb => /=.
    - rewrite Z.mul_1_r Z.pow2_bits_eqb; first lia.
      destruct (Z.eqb_spec ⁺k m) as [<- |]; first rewrite Hb //.
      rewrite andb_false_r //.
    - rewrite Z.mul_0_r Z.bits_0.
      destruct (Z.eqb_spec ⁺k m) as [<- |]; first rewrite Hb //.
      rewrite andb_false_r //.
  Qed.

  Lemma Zｰmodｰpow2ｰdouble (h : Z) (n : nat) :
    is_pow2 n →
    (h `mod` ⁺(2 * n) = h `mod` ⁺n + ⁺n * Z.b2z (Z.testbit h (Z.log2 ⁺n)))%Z.
  Proof.
    intros Hn. pose proof (is_pow2ｰpos _ Hn).
    destruct Hn as (k & ->).
    rewrite Nat2Z.inj_mul Zｰof_natｰpow2 Z.log2_pow2; first lia.
    rewrite (Z.mul_comm 2) Zｰmodｰmulｰr; [lia.. |].
    rewrite Z.testbit_spec' //; lia.
  Qed.

  Lemma Zｰmodｰpow2ｰhalf (h : Z) (n : nat) :
    is_pow2 n →
    ((h `mod` ⁺(2 * n)) `mod` ⁺n = h `mod` ⁺n)%Z.
  Proof.
    intros Hn. pose proof (is_pow2ｰpos _ Hn).
    rewrite Nat2Z.inj_mul Z.mul_comm Zｰmodｰmulｰr; [lia.. |].
    rewrite Z.add_mod; first lia.
    rewrite Z.mod_mod; first lia.
    rewrite (Z.mul_comm ⁺n) Z.mod_mul; first lia.
    rewrite Z.add_0_r Z.mod_mod //. lia.
  Qed.

  Lemma Zｰmodｰpow2ｰdoubleｰcases (h : Z) (n : nat) :
    is_pow2 n →
    ( h `mod` ⁺(2 * n) = h `mod` ⁺n
    ∨ h `mod` ⁺(2 * n) = h `mod` ⁺n + ⁺n
    )%Z.
  Proof.
    intros Hn.
    rewrite Zｰmodｰpow2ｰdouble //.
    destruct (Z.testbit _ _); simpl; [right | left]; lia.
  Qed.

  Lemma Zｰgcdｰpow2ｰodd (n : nat) (step : Z) :
    is_pow2 n →
    Z.Odd step →
    Z.gcd ⁺n step = 1%Z.
  Proof.
    intros (k & ->) (r & Hr).
    rewrite Zｰof_natｰpow2.
    apply Z.coprime_pow_l; first lia.
    apply Z.coprime_mod_r_iff.
    replace (step `mod` 2)%Z with 1%Z; first apply Z.coprime_1_r.
    apply Z.mod_unique with r; [left; lia | lia].
  Qed.

  Lemma Zｰmodｰeqｰdivide (a b c : Z) :
    (0 < c)%Z →
    (a `mod` c = b `mod` c)%Z →
    (c | a - b)%Z.
  Proof.
    intros Hc Hab.
    exists (Z.div a c - Z.div b c)%Z.
    pose proof (Z.div_mod a c ltac:(lia)).
    pose proof (Z.div_mod b c ltac:(lia)).
    nia.
  Qed.

  Lemma Zｰcoverage (n : nat) (step : Z) (m : nat) j :
    is_pow2 n →
    Z.Odd step →
    1 ≤ m →
    ((⁺m * step) `mod` ⁺n = 0)%Z →
    (0 ≤ j < ⁺n)%Z →
      ∃ a,
      1 ≤ a ≤ m ∧
      ((⁺a * step) `mod` ⁺n = j)%Z.
  Proof.
    intros Hn Hstep Hm Hmn Hj.
    pose proof (is_pow2ｰpos _ Hn).
    pose proof (Zｰgcdｰpow2ｰodd _ _ Hn Hstep) as Hgcd.
    assert (n ≤ m) as Hnm.
    { apply (Z.mod_divide _ ⁺n ltac:(lia)) in Hmn.
      rewrite Z.mul_comm in Hmn.
      pose proof (Z.gauss _ _ _ Hmn Hgcd) as Hdiv.
      apply Z.divide_pos_le in Hdiv; lia.
    }
    pose f (a : nat) := ((⁺a * step) `mod` ⁺n)%Z.
    assert (NoDup (f <$> seq 1 n)) as Hl.
    { apply NoDup_fmap_2_strong; last apply NoDup_seq.
      intros a1 a2 (? & ?)%elem_of_seq (? & ?)%elem_of_seq Ha.
      apply (Zｰmodｰeqｰdivide _ _ ⁺n ltac:(lia)) in Ha.
      rewrite -Z.mul_sub_distr_r Z.mul_comm in Ha.
      pose proof (Z.gauss _ _ _ Ha Hgcd) as Hdiv.
      destruct (decide (a1 = a2)); first done.
      destruct (Z.le_gt_cases ⁺a2 ⁺a1).
      - apply Z.divide_pos_le in Hdiv; lia.
      - apply Z.divide_opp_r, Z.divide_pos_le in Hdiv; lia.
    }
    assert (List.incl (seqZ 0 ⁺n) (f <$> seq 1 n)) as Hincl.
    { apply NoDup_length_incl.
      - apply NoDup_ListNoDup. done.
      - rewrite length_fmap length_seq length_seqZ. lia.
      - intros x (a & -> & _)%list_elem_of_In%list_elem_of_fmap.
        apply list_elem_of_In, elem_of_seqZ.
        split; [apply Z.mod_pos_bound | apply Z.mod_pos_bound]; lia.
    }
    opose proof* (Hincl j) as Hj'.
    { apply list_elem_of_In, elem_of_seqZ. lia. }
    apply list_elem_of_In, list_elem_of_fmap in Hj' as (a & -> & (? & ?)%elem_of_seq).
    exists a. split; [lia | done].
  Qed.

  Lemma Zｰlorｰ1ｰodd (k : Z) :
    Z.Odd (Z.lor k 1).
  Proof.
    apply Z.odd_spec. rewrite -Z.bit0_odd Z.lor_spec orb_true_r //.
  Qed.
End pow2.

Section Qp۰of_nat.
  Implicit Type n : nat.

  Definition Qp۰of_nat :=
    pos_to_Qp ∘ Pos.of_nat.

  Lemma Qp۰of_natｰ1 :
    Qp۰of_nat 1 = 1%Qp.
  Proof.
    done.
  Qed.
  Lemma Qp۰of_natｰS n :
    n ≠ 0 →
    Qp۰of_nat ˖n = (1 + Qp۰of_nat n)%Qp.
  Proof.
    intros Hn.
    rewrite /Qp۰of_nat /=.
    rewrite Nat2Pos.inj_succ //.
    rewrite pos_to_Qp_add Pos.add_1_l //.
  Qed.
End Qp۰of_nat.
