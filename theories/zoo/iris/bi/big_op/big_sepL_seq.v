Require Import zoo.prelude.
Require Import zoo.common.list.
Require Export zoo.iris.bi.big_op.big_sepL2.
Require Import zoo.iris.diaframe.
Require Import zoo.options.

Section bi.
  Context {PROP : bi}.

  Section big_sepL۰seq.
    Context {A : Type}.

    Implicit Types l : list A.
    Implicit Types Φ : nat → PROP.

    Lemma big_sepL𑁒seq𑁒intro Φ i n :
      □ (
        ∀ k,
        ⌜i ≤ k < i + n⌝ -∗
        Φ k
      ) ⊢
      [∗ list] k ∈ seq i n, Φ k.
    Proof.
      iIntros "#H".
      iApply big_sepL_intro. iIntros "!>" (k k_ (-> & Hk)%lookup_seq).
      iSteps.
    Qed.

    Lemma big_sepL𑁒seq𑁒impl Φ1 Φ2 i n :
      ([∗ list] k ∈ seq i n, Φ1 k) -∗
      □ (
        ∀ k,
        ⌜i ≤ k < i + n⌝ -∗
        Φ1 k -∗
        Φ2 k
      ) -∗
      [∗ list] k ∈ seq i n, Φ2 k.
    Proof.
      iIntros "HΦ1 #H".
      iApply (big_sepL_impl with "HΦ1"). iIntros "!>" (k k_ (-> & Hk)%lookup_seq).
      iSteps.
    Qed.

    Lemma big_sepL𑁒seq𑁒cons Φ i n :
      ([∗ list] k ∈ seq i ˖n, Φ k) ⊣⊢
        Φ i ∗
        ([∗ list] k ∈ seq ˖i n, Φ k).
    Proof.
      rewrite -cons_seq big_sepL_cons //.
    Qed.
    Lemma big_sepL𑁒seq𑁒cons₁ Φ i n :
      ([∗ list] k ∈ seq i ˖n, Φ k) ⊢
        Φ i ∗
        ([∗ list] k ∈ seq ˖i n, Φ k).
    Proof.
      rewrite big_sepL𑁒seq𑁒cons //.
    Qed.
    Lemma big_sepL𑁒seq𑁒cons₂ Φ i n :
      ([∗ list] k ∈ seq ˖i n, Φ k) -∗
      Φ i -∗
      [∗ list] k ∈ seq i ˖n, Φ k.
    Proof.
      rewrite big_sepL𑁒seq𑁒cons.
      iSteps.
    Qed.

    Lemma big_sepL𑁒seq𑁒snoc Φ i n :
      ([∗ list] k ∈ seq i ˖n, Φ k) ⊣⊢
        ([∗ list] k ∈ seq i n, Φ k) ∗
        Φ (i + n).
    Proof.
      rewrite seq_S big_sepL_snoc //.
    Qed.
    Lemma big_sepL𑁒seq𑁒snoc₁ Φ i n :
      ([∗ list] k ∈ seq i ˖n, Φ k) ⊢
        ([∗ list] k ∈ seq i n, Φ k) ∗
        Φ (i + n).
    Proof.
      rewrite big_sepL𑁒seq𑁒snoc //.
    Qed.
    Lemma big_sepL𑁒seq𑁒snoc₂ Φ i n :
      ([∗ list] k ∈ seq i n, Φ k) -∗
      Φ (i + n) -∗
      [∗ list] k ∈ seq i ˖n, Φ k.
    Proof.
      rewrite big_sepL𑁒seq𑁒snoc.
      iSteps.
    Qed.

    Lemma big_sepL𑁒seq𑁒app Φ i n1 n2 :
      ([∗ list] k ∈ seq i (n1 + n2), Φ k) ⊣⊢
        ([∗ list] k ∈ seq i n1, Φ k) ∗
        ([∗ list] k ∈ seq (i + n1) n2, Φ k).
    Proof.
      rewrite seq_app big_sepL_app //.
    Qed.
    Lemma big_sepL𑁒seq𑁒app₁ {Φ i n} n1 n2 :
      n = n1 + n2 →
      ([∗ list] k ∈ seq i n, Φ k) ⊢
        ([∗ list] k ∈ seq i n1, Φ k) ∗
        ([∗ list] k ∈ seq (i + n1) n2, Φ k).
    Proof.
      intros ->.
      rewrite big_sepL𑁒seq𑁒app //.
    Qed.
    Lemma big_sepL𑁒seq𑁒app₂ Φ i1 n1 i2 n2 :
      i2 = i1 + n1 →
      ([∗ list] k ∈ seq i1 n1, Φ k) -∗
      ([∗ list] k ∈ seq i2 n2, Φ k) -∗
      [∗ list] k ∈ seq i1 (n1 + n2), Φ k.
    Proof.
      rewrite big_sepL𑁒seq𑁒app.
      iSteps.
    Qed.

    Lemma big_sepL𑁒seq𑁒lookup𑁒acc {Φ i n} j :
      j < n →
      ([∗ list] k ∈ seq i n, Φ k) ⊢
        Φ (i + j) ∗
        ( Φ (i + j) -∗
          [∗ list] k ∈ seq i n, Φ k
        ).
    Proof.
      intros Hj.
      rewrite -big_sepL_lookup_acc //.
      apply lookup_seq_lt. done.
    Qed.
    Lemma big_sepL𑁒seq𑁒lookup𑁒acc' {Φ i n} j :
      i ≤ j < i + n →
      ([∗ list] k ∈ seq i n, Φ k) ⊢
        Φ j ∗
        ( Φ j -∗
          [∗ list] k ∈ seq i n, Φ k
        ).
    Proof.
      intros ((j' & ->)%Nat.le_sum & Hj).
      rewrite -big_sepL𑁒seq𑁒lookup𑁒acc //. lia.
    Qed.
    Lemma big_sepL𑁒seq𑁒lookup `{!BiAffine PROP} {Φ i n} j :
      j < n →
      ([∗ list] k ∈ seq i n, Φ k) ⊢
      Φ (i + j).
    Proof.
      intros Hj.
      rewrite big_sepL𑁒seq𑁒lookup𑁒acc //.
      iSteps.
    Qed.
    Lemma big_sepL𑁒seq𑁒lookup' `{!BiAffine PROP} {Φ i n} j :
      i ≤ j < i + n →
      ([∗ list] k ∈ seq i n, Φ k) ⊢
      Φ j.
    Proof.
      intros Hj.
      rewrite big_sepL𑁒seq𑁒lookup𑁒acc' //.
      iSteps.
    Qed.

    Lemma big_sepL𑁒seq𑁒index `{!BiAffine PROP} {Φ} l i n :
      length l = n →
      ([∗ list] k ∈ seq i n, Φ k) ⊣⊢
      [∗ list] k ↦ _ ∈ l, Φ (i + k).
    Proof.
      intros. iSplit.
      all: iIntros "H".
      all: iApply (big_sepL𑁒impl𑁒strong with "H"); first simpl_length.
      all: iIntros "!> %k %k_ % % % HΦ".
      all: pose proof lookup_seq.
      all: naive_solver.
    Qed.
    Lemma big_sepL𑁒seq𑁒index₁ `{!BiAffine PROP} {Φ} l i n :
      length l = n →
      ([∗ list] k ∈ seq i n, Φ k) ⊢
      [∗ list] k ↦ _ ∈ l, Φ (i + k).
    Proof.
      intros. rewrite big_sepL𑁒seq𑁒index //.
    Qed.
    Lemma big_sepL𑁒seq𑁒index₂ `{!BiAffine PROP} {Φ l} n :
      length l = n →
      ([∗ list] k ↦ _ ∈ l, Φ k) ⊢
      [∗ list] k ∈ seq 0 n, Φ k.
    Proof.
      intros. rewrite big_sepL𑁒seq𑁒index //.
    Qed.

    Lemma big_sepL𑁒seq𑁒shift `{!BiAffine PROP} {Φ} j i n :
      ([∗ list] k ∈ seq (i + j) n, Φ k) ⊣⊢
      [∗ list] k ∈ seq i n, Φ (k + j).
    Proof.
      iSplit.
      all: iIntros "H".
      all: iApply (big_sepL𑁒impl𑁒strong with "H"); first simpl_length.
      all: iIntros "!>" (k ? ? (-> & _)%lookup_seq (-> & _)%lookup_seq).
      all: rewrite Nat.add_shuffle0.
      all: iSteps.
    Qed.
    Lemma big_sepL𑁒seq𑁒shift' `{!BiAffine PROP} {Φ} j i n :
      ([∗ list] k ∈ seq (i + j) n, Φ (k - j)) ⊣⊢
      [∗ list] k ∈ seq i n, Φ k.
    Proof.
      rewrite big_sepL𑁒seq𑁒shift.
      setoid_rewrite Nat.add_sub => //.
    Qed.
    Lemma big_sepL𑁒seq𑁒shift₁ `{!BiAffine PROP} {Φ} j i n :
      ([∗ list] k ∈ seq (i + j) n, Φ k) ⊢
      [∗ list] k ∈ seq i n, Φ (k + j).
    Proof.
      rewrite big_sepL𑁒seq𑁒shift //.
    Qed.
    Lemma big_sepL𑁒seq𑁒shift₂ `{!BiAffine PROP} {Φ} j i n :
      ([∗ list] k ∈ seq i n, Φ (k + j)) ⊢
      [∗ list] k ∈ seq (i + j) n, Φ k.
    Proof.
      rewrite big_sepL𑁒seq𑁒shift //.
    Qed.
    Lemma big_sepL𑁒seq𑁒shift₂' `{!BiAffine PROP} {Φ} j i n :
      ([∗ list] k ∈ seq i n, Φ k) ⊢
      [∗ list] k ∈ seq (i + j) n, Φ (k - j).
    Proof.
      rewrite big_sepL𑁒seq𑁒shift' //.
    Qed.

    Lemma big_sepL𑁒seq𑁒shift𑁒1 `{!BiAffine PROP} Φ i n :
      ([∗ list] k ∈ seq ˖i n, Φ k) ⊣⊢
      [∗ list] k ∈ seq i n, Φ ˖k.
    Proof.
      setoid_rewrite <- Nat.add_1_r.
      apply big_sepL𑁒seq𑁒shift.
    Qed.
    Lemma big_sepL𑁒seq𑁒shift𑁒1₁ `{!BiAffine PROP} Φ i n :
      ([∗ list] k ∈ seq ˖i n, Φ k) ⊢
      [∗ list] k ∈ seq i n, Φ ˖k.
    Proof.
      rewrite big_sepL𑁒seq𑁒shift𑁒1 //.
    Qed.
    Lemma big_sepL𑁒seq𑁒shift𑁒1₂ `{!BiAffine PROP} Φ i n :
      ([∗ list] k ∈ seq i n, Φ ˖k) ⊢
      [∗ list] k ∈ seq ˖i n, Φ k.
    Proof.
      rewrite big_sepL𑁒seq𑁒shift𑁒1 //.
    Qed.

    Lemma big_sepL𑁒seq𑁒exists `{!BiAffine PROP} `(Φ : nat → A → PROP) i n :
      ([∗ list] k ∈ seq i n, ∃ x, Φ k x) ⊢
        ∃ xs,
        ⌜length xs = n⌝ ∗
        [∗ list] k ↦ x ∈ xs, Φ (i + k) x.
    Proof.
      iIntros "H".
      iDestruct (big_sepL𑁒exists with "H") as "(%xs & %Hxs & H)". simpl_length in Hxs.
      iDestruct (big_sepL2𑁒seq𑁒l with "H") as "H".
      iSteps.
    Qed.

    Lemma big_sepL𑁒seq𑁒to𑁒seqZ `{!BiAffine PROP} Φ i n :
      ([∗ list] k ∈ seq i n, Φ k) ⊢
      [∗ list] k ∈ seqZ ⁺i ⁺n, Φ ₊k.
    Proof.
      iIntros "H".
      iApply (big_sepL𑁒impl𑁒strong with "H").
      { simpl_length. lia. }
      iIntros "!>" (k k1 k2 (-> & _)%lookup_seq (-> & _)%lookup_seqZ) "HΦ".
      rewrite -Nat2Z.inj_add Nat2Z.id //.
    Qed.
    Lemma big_sepL𑁒seq𑁒to𑁒seqZ' `{!BiAffine PROP} Φ i n :
      (0 ≤ i)%Z →
      (0 ≤ n)%Z →
      ([∗ list] k ∈ seq ₊i ₊n, Φ k) ⊢
      [∗ list] k ∈ seqZ i n, Φ ₊k.
    Proof.
      intros.
      rewrite big_sepL𑁒seq𑁒to𑁒seqZ.
      setoid_rewrite Z2Nat.id => //.
    Qed.
  End big_sepL۰seq.
End bi.
