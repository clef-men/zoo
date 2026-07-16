Require Import zoo.prelude.
Require Import zoo.common.list.
Require Export zoo.iris.bi.big_op.big_sepL.
Require Import zoo.iris.diaframe.
Require Import zoo.options.

Section bi.
  Context {PROP : bi}.

  Section big_sepL۰seqZ.
    Context {A : Type}.

    Implicit Types l : list A.
    Implicit Types Φ : Z → PROP.

    Lemma big_sepL𑁒seqZ𑁒intro Φ i n :
      □ (
        ∀ k,
        ⌜i ≤ k < i + n⌝%Z -∗
        Φ k
      ) ⊢
      [∗ list] k ∈ seqZ i n, Φ k.
    Proof.
      iIntros "#H".
      iApply big_sepL_intro. iIntros "!>" (k k_ (-> & Hk)%lookup_seqZ).
      iSteps.
    Qed.

    Lemma big_sepL𑁒seqZ𑁒impl Φ1 Φ2 i n :
      ([∗ list] k ∈ seqZ i n, Φ1 k) -∗
      □ (
        ∀ k,
        ⌜i ≤ k < i + n⌝%Z -∗
        Φ1 k -∗
        Φ2 k
      ) -∗
      [∗ list] k ∈ seqZ i n, Φ2 k.
    Proof.
      iIntros "HΦ1 #H".
      iApply (big_sepL_impl with "HΦ1"). iIntros "!>" (k k_ (-> & Hk)%lookup_seqZ).
      iSteps.
    Qed.

    Lemma big_sepL𑁒seqZ𑁒cons Φ i n :
      (0 < n)%Z →
      ([∗ list] k ∈ seqZ i n, Φ k) ⊣⊢
        Φ i ∗
        ([∗ list] k ∈ seqZ (Z.succ i) (Z.pred n), Φ k).
    Proof.
      intros.
      rewrite seqZ_cons; first lia.
      rewrite big_sepL_cons //.
    Qed.
    Lemma big_sepL𑁒seqZ𑁒cons₁ Φ i n :
      (0 < n)%Z →
      ([∗ list] k ∈ seqZ i n, Φ k) ⊢
        Φ i ∗
        ([∗ list] k ∈ seqZ (Z.succ i) (Z.pred n), Φ k).
    Proof.
      intros.
      rewrite big_sepL𑁒seqZ𑁒cons //.
    Qed.
    Lemma big_sepL𑁒seqZ𑁒cons₂ Φ i n :
      (0 ≤ n)%Z →
      ([∗ list] k ∈ seqZ i n, Φ k) -∗
      Φ (Z.pred i) -∗
      [∗ list] k ∈ seqZ (Z.pred i) (Z.succ n), Φ k.
    Proof.
      intros.
      rewrite (big_sepL𑁒seqZ𑁒cons _ (Z.pred i)); first lia.
      rewrite Z.succ_pred Z.pred_succ.
      iSteps.
    Qed.

    Lemma big_sepL𑁒seqZ𑁒snoc Φ i n :
      (0 ≤ n)%Z →
      ([∗ list] k ∈ seqZ i (Z.succ n), Φ k) ⊣⊢
        ([∗ list] k ∈ seqZ i n, Φ k) ∗
        Φ (i + n)%Z.
    Proof.
      intros.
      Z_to_nat n.
      rewrite -Nat2Z.inj_succ seqZ_S big_sepL_snoc //.
    Qed.
    Lemma big_sepL𑁒seqZ𑁒snoc₁ Φ i n :
      (0 ≤ n)%Z →
      ([∗ list] k ∈ seqZ i (Z.succ n), Φ k) ⊢
        ([∗ list] k ∈ seqZ i n, Φ k) ∗
        Φ (i + n)%Z.
    Proof.
      intros.
      rewrite big_sepL𑁒seqZ𑁒snoc //.
    Qed.
    Lemma big_sepL𑁒seqZ𑁒snoc₂ Φ i n :
      (0 ≤ n)%Z →
      ([∗ list] k ∈ seqZ i n, Φ k) -∗
      Φ (i + n)%Z -∗
      [∗ list] k ∈ seqZ i (Z.succ n), Φ k.
    Proof.
      intros.
      rewrite big_sepL𑁒seqZ𑁒snoc //.
      iSteps.
    Qed.

    Lemma big_sepL𑁒seqZ𑁒app Φ i n1 n2 :
      (0 ≤ n1)%Z →
      (0 ≤ n2)%Z →
      ([∗ list] k ∈ seqZ i (n1 + n2), Φ k) ⊣⊢
        ([∗ list] k ∈ seqZ i n1, Φ k) ∗
        ([∗ list] k ∈ seqZ (i + n1) n2, Φ k).
    Proof.
      intros.
      rewrite seqZ_app // big_sepL_app //.
    Qed.
    Lemma big_sepL𑁒seqZ𑁒app₁ {Φ i n} n1 n2 :
      n = (n1 + n2)%Z →
      (0 ≤ n1)%Z →
      (0 ≤ n2)%Z →
      ([∗ list] k ∈ seqZ i n, Φ k) ⊢
        ([∗ list] k ∈ seqZ i n1, Φ k) ∗
        ([∗ list] k ∈ seqZ (i + n1) n2, Φ k).
    Proof.
      intros -> ? ?.
      rewrite big_sepL𑁒seqZ𑁒app //.
    Qed.
    Lemma big_sepL𑁒seqZ𑁒app₂ Φ i1 n1 i2 n2 :
      (0 ≤ n1)%Z →
      (0 ≤ n2)%Z →
      i2 = (i1 + n1)%Z →
      ([∗ list] k ∈ seqZ i1 n1, Φ k) -∗
      ([∗ list] k ∈ seqZ i2 n2, Φ k) -∗
      [∗ list] k ∈ seqZ i1 (n1 + n2), Φ k.
    Proof.
      intros ? ? ->.
      rewrite big_sepL𑁒seqZ𑁒app //.
      iSteps.
    Qed.

    Lemma big_sepL𑁒seqZ𑁒to𑁒seq `{!BiAffine PROP} Φ i n :
      (0 ≤ i)%Z →
      (0 ≤ n)%Z →
      ([∗ list] k ∈ seqZ i n, Φ k) ⊢
      [∗ list] k ∈ seq ₊i ₊n, Φ ⁺k.
    Proof.
      iIntros "%Hi %Hn H".
      iApply (big_sepL𑁒impl𑁒strong with "H").
      { simpl_length. }
      iIntros "!>" (k k1 k2 (-> & _)%lookup_seqZ (-> & _)%lookup_seq) "HΦ".
      replace ⁺(₊i + k) with (i + k)%Z by lia. done.
    Qed.
    Lemma big_sepL𑁒seqZ𑁒to𑁒seq' `{!BiAffine PROP} (Φ : nat → PROP) i n :
      (0 ≤ i)%Z →
      (0 ≤ n)%Z →
      ([∗ list] k ∈ seqZ i n, Φ ₊k) ⊢
      [∗ list] k ∈ seq ₊i ₊n, Φ k.
    Proof.
      intros.
      rewrite big_sepL𑁒seqZ𑁒to𑁒seq //.
      setoid_rewrite Nat2Z.id => //.
    Qed.

    Lemma big_sepL𑁒seqZ𑁒lookup `{!BiAffine PROP} {Φ i1 n} i2 :
      (i1 ≤ i2 < i1 + n)%Z →
      ([∗ list] k ∈ seqZ i1 n, Φ k) ⊢
      Φ i2.
    Proof.
      iIntros "%Hj H".
      iApply (big_sepL_lookup _ _ ₊(i2 - i1)%Z with "H").
      { rewrite lookup_seqZ. lia. }
    Qed.
  End big_sepL۰seqZ.
End bi.
