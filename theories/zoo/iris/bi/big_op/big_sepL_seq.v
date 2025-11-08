From zoo Require Import
  prelude.
From zoo.common Require Import
  list.
From zoo.iris.bi Require Export
  big_op.big_sepL2.
From zoo.iris Require Import
  diaframe.
From zoo Require Import
  options.

Section bi.
  Context {PROP : bi}.

  Section big_sepL_seq.
    Context {A : Type}.

    Implicit Types l : list A.
    Implicit Types Φ : nat → PROP.

    Lemma big_sepL_seq_intro Φ i n :
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

    Lemma big_sepL_seq_cons Φ i n :
      ([∗ list] k ∈ seq i (S n), Φ k) ⊣⊢
        Φ i ∗
        ([∗ list] k ∈ seq (S i) n, Φ k).
    Proof.
      rewrite -cons_seq big_sepL_cons //.
    Qed.
    Lemma big_sepL_seq_cons_1 Φ i n :
      ([∗ list] k ∈ seq i (S n), Φ k) ⊢
        Φ i ∗
        ([∗ list] k ∈ seq (S i) n, Φ k).
    Proof.
      rewrite big_sepL_seq_cons //.
    Qed.
    Lemma big_sepL_seq_cons_2 Φ i n :
      ([∗ list] k ∈ seq (S i) n, Φ k) -∗
      Φ i -∗
      [∗ list] k ∈ seq i (S n), Φ k.
    Proof.
      rewrite big_sepL_seq_cons. iSteps.
    Qed.

    Lemma big_sepL_seq_snoc Φ i n :
      ([∗ list] k ∈ seq i (S n), Φ k) ⊣⊢
        ([∗ list] k ∈ seq i n, Φ k) ∗
        Φ (i + n).
    Proof.
      rewrite seq_S big_sepL_snoc //.
    Qed.
    Lemma big_sepL_seq_snoc_1 Φ i n :
      ([∗ list] k ∈ seq i (S n), Φ k) ⊢
        ([∗ list] k ∈ seq i n, Φ k) ∗
        Φ (i + n).
    Proof.
      rewrite big_sepL_seq_snoc //.
    Qed.
    Lemma big_sepL_seq_snoc_2 Φ i n :
      ([∗ list] k ∈ seq i n, Φ k) -∗
      Φ (i + n) -∗
      [∗ list] k ∈ seq i (S n), Φ k.
    Proof.
      rewrite big_sepL_seq_snoc. iSteps.
    Qed.

    Lemma big_sepL_seq_lookup_acc {Φ i n} j :
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
    Lemma big_sepL_seq_lookup_acc' {Φ i n} j :
      i ≤ j < i + n →
      ([∗ list] k ∈ seq i n, Φ k) ⊢
        Φ j ∗
        ( Φ j -∗
          [∗ list] k ∈ seq i n, Φ k
        ).
    Proof.
      intros ((j' & ->)%Nat.le_sum & Hj).
      rewrite -big_sepL_seq_lookup_acc //. lia.
    Qed.
    Lemma big_sepL_seq_lookup `{!BiAffine PROP} {Φ i n} j :
      j < n →
      ([∗ list] k ∈ seq i n, Φ k) ⊢
      Φ (i + j).
    Proof.
      intros Hj.
      rewrite big_sepL_seq_lookup_acc //. iSteps.
    Qed.
    Lemma big_sepL_seq_lookup' `{!BiAffine PROP} {Φ i n} j :
      i ≤ j < i + n →
      ([∗ list] k ∈ seq i n, Φ k) ⊢
      Φ j.
    Proof.
      intros Hj.
      rewrite big_sepL_seq_lookup_acc' //. iSteps.
    Qed.

    Lemma big_sepL_seq_index `{!BiAffine PROP} {Φ} l i n :
      length l = n →
      ([∗ list] k ∈ seq i n, Φ k) ⊣⊢
      [∗ list] k ↦ _ ∈ l, Φ (i + k).
    Proof.
      intros. iSplit.
      all: iIntros "H".
      all: iApply (big_sepL_impl_strong with "H"); first simpl_length.
      all: iIntros "!> %k %k_ % % % HΦ".
      all: pose proof lookup_seq.
      all: naive_solver.
    Qed.
    Lemma big_sepL_seq_index_1 `{!BiAffine PROP} {Φ} l i n :
      length l = n →
      ([∗ list] k ∈ seq i n, Φ k) ⊢
      [∗ list] k ↦ _ ∈ l, Φ (i + k).
    Proof.
      intros. rewrite big_sepL_seq_index //.
    Qed.
    Lemma big_sepL_seq_index_2 `{!BiAffine PROP} {Φ l} n :
      length l = n →
      ([∗ list] k ↦ _ ∈ l, Φ k) ⊢
      [∗ list] k ∈ seq 0 n, Φ k.
    Proof.
      intros. rewrite big_sepL_seq_index //.
    Qed.

    Lemma big_sepL_seq_shift `{!BiAffine PROP} {Φ} j i n :
      ([∗ list] k ∈ seq (i + j) n, Φ k) ⊣⊢
      [∗ list] k ∈ seq i n, Φ (k + j).
    Proof.
      iSplit.
      all: iIntros "H".
      all: iApply (big_sepL_impl_strong with "H"); first simpl_length.
      all: iIntros "!>" (k ? ? (-> & _)%lookup_seq (-> & _)%lookup_seq).
      all: rewrite Nat.add_shuffle0.
      all: iSteps.
    Qed.
    Lemma big_sepL_seq_shift' `{!BiAffine PROP} {Φ} j i n :
      ([∗ list] k ∈ seq (i + j) n, Φ (k - j)) ⊣⊢
      [∗ list] k ∈ seq i n, Φ k.
    Proof.
      rewrite big_sepL_seq_shift.
      setoid_rewrite Nat.add_sub => //.
    Qed.
    Lemma big_sepL_seq_shift_1 `{!BiAffine PROP} {Φ} j i n :
      ([∗ list] k ∈ seq (i + j) n, Φ k) ⊢
      [∗ list] k ∈ seq i n, Φ (k + j).
    Proof.
      rewrite big_sepL_seq_shift //.
    Qed.
    Lemma big_sepL_seq_shift_2 `{!BiAffine PROP} {Φ} j i n :
      ([∗ list] k ∈ seq i n, Φ (k + j)) ⊢
      [∗ list] k ∈ seq (i + j) n, Φ k.
    Proof.
      rewrite big_sepL_seq_shift //.
    Qed.
    Lemma big_sepL_seq_shift_2' `{!BiAffine PROP} {Φ} j i n :
      ([∗ list] k ∈ seq i n, Φ k) ⊢
      [∗ list] k ∈ seq (i + j) n, Φ (k - j).
    Proof.
      rewrite big_sepL_seq_shift' //.
    Qed.

    Lemma big_sepL_seq_shift1 `{!BiAffine PROP} Φ i n :
      ([∗ list] k ∈ seq (S i) n, Φ k) ⊣⊢
      [∗ list] k ∈ seq i n, Φ (S k).
    Proof.
      setoid_rewrite <- Nat.add_1_r.
      apply big_sepL_seq_shift.
    Qed.
    Lemma big_sepL_seq_shift1_1 `{!BiAffine PROP} Φ i n :
      ([∗ list] k ∈ seq (S i) n, Φ k) ⊢
      [∗ list] k ∈ seq i n, Φ (S k).
    Proof.
      rewrite big_sepL_seq_shift1 //.
    Qed.
    Lemma big_sepL_seq_shift1_2 `{!BiAffine PROP} Φ i n :
      ([∗ list] k ∈ seq i n, Φ (S k)) ⊢
      [∗ list] k ∈ seq (S i) n, Φ k.
    Proof.
      rewrite big_sepL_seq_shift1 //.
    Qed.

    Lemma big_sepL_seq_exists `{!BiAffine PROP} `(Φ : nat → A → PROP) i n :
      ([∗ list] k ∈ seq i n, ∃ x, Φ k x) ⊢
        ∃ xs,
        ⌜length xs = n⌝ ∗
        [∗ list] k ↦ x ∈ xs, Φ (i + k) x.
    Proof.
      iIntros "H".
      iDestruct (big_sepL_exists with "H") as "(%xs & %Hxs & H)". simpl_length in Hxs.
      iDestruct (big_sepL2_seq_l with "H") as "H".
      iSteps.
    Qed.

    Lemma big_sepL_seq_to_seqZ `{!BiAffine PROP} Φ i n :
      ([∗ list] k ∈ seq i n, Φ k) ⊢
      [∗ list] k ∈ seqZ ⁺i ⁺n, Φ ₊k.
    Proof.
      iIntros "H".
      iApply (big_sepL_impl_strong with "H").
      { simpl_length. lia. }
      iIntros "!>" (k k1 k2 (-> & _)%lookup_seq (-> & _)%lookup_seqZ) "HΦ".
      rewrite -Nat2Z.inj_add Nat2Z.id //.
    Qed.
    Lemma big_sepL_seqZ_to_seq `{!BiAffine PROP} (Φ : Z → PROP) i n :
      (0 ≤ i)%Z →
      (0 ≤ n)%Z →
      ([∗ list] k ∈ seqZ i n, Φ k) ⊢
      [∗ list] k ∈ seq ₊i ₊n, Φ ⁺k.
    Proof.
      iIntros "%Hi %Hn H".
      iApply (big_sepL_impl_strong with "H").
      { simpl_length. }
      iIntros "!>" (k k1 k2 (-> & _)%lookup_seqZ (-> & _)%lookup_seq) "HΦ".
      replace ⁺(₊i + k) with (i + k)%Z by lia. done.
    Qed.
    Lemma big_sepL_seqZ_to_seq' `{!BiAffine PROP} Φ i n :
      (0 ≤ i)%Z →
      (0 ≤ n)%Z →
      ([∗ list] k ∈ seqZ i n, Φ ₊k) ⊢
      [∗ list] k ∈ seq ₊i ₊n, Φ k.
    Proof.
      intros.
      rewrite big_sepL_seqZ_to_seq //.
      setoid_rewrite Nat2Z.id => //.
    Qed.
  End big_sepL_seq.
End bi.
