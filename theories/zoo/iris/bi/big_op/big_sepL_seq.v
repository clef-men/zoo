Require Import zoo.prelude.
Require Import zoo.common.list.
Require Export zoo.iris.bi.big_op.big_sepL2.
Require Import zoo.iris.diaframe.
Require Import zoo.options.

Section bi.
  Context {PROP : bi}.

  Section big_sepL۰seq.
    Context {A : Type}.

    Implicit Type l : list A.
    Implicit Type Φ : nat → PROP.

    Lemma big_sepLｰseqｰintro Φ i n :
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

    Lemma big_sepLｰseqｰimpl Φ1 Φ2 i n :
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

    Lemma big_sepLｰseqｰcons Φ i n :
      ([∗ list] k ∈ seq i ˖n, Φ k) ⊣⊢
        Φ i ∗
        ([∗ list] k ∈ seq ˖i n, Φ k).
    Proof.
      rewrite -cons_seq big_sepL_cons //.
    Qed.
    Lemma big_sepLｰseqｰcons₁ Φ i n :
      ([∗ list] k ∈ seq i ˖n, Φ k) ⊢
        Φ i ∗
        ([∗ list] k ∈ seq ˖i n, Φ k).
    Proof.
      rewrite big_sepLｰseqｰcons //.
    Qed.
    Lemma big_sepLｰseqｰcons₂ Φ i n :
      ([∗ list] k ∈ seq ˖i n, Φ k) -∗
      Φ i -∗
      [∗ list] k ∈ seq i ˖n, Φ k.
    Proof.
      rewrite big_sepLｰseqｰcons.
      iSteps.
    Qed.

    Lemma big_sepLｰseqｰsnoc Φ i n :
      ([∗ list] k ∈ seq i ˖n, Φ k) ⊣⊢
        ([∗ list] k ∈ seq i n, Φ k) ∗
        Φ (i + n).
    Proof.
      rewrite seq_S big_sepL_snoc //.
    Qed.
    Lemma big_sepLｰseqｰsnoc₁ Φ i n :
      ([∗ list] k ∈ seq i ˖n, Φ k) ⊢
        ([∗ list] k ∈ seq i n, Φ k) ∗
        Φ (i + n).
    Proof.
      rewrite big_sepLｰseqｰsnoc //.
    Qed.
    Lemma big_sepLｰseqｰsnoc₂ Φ i n :
      ([∗ list] k ∈ seq i n, Φ k) -∗
      Φ (i + n) -∗
      [∗ list] k ∈ seq i ˖n, Φ k.
    Proof.
      rewrite big_sepLｰseqｰsnoc.
      iSteps.
    Qed.

    Lemma big_sepLｰseqｰapp Φ i n1 n2 :
      ([∗ list] k ∈ seq i (n1 + n2), Φ k) ⊣⊢
        ([∗ list] k ∈ seq i n1, Φ k) ∗
        ([∗ list] k ∈ seq (i + n1) n2, Φ k).
    Proof.
      rewrite seq_app big_sepL_app //.
    Qed.
    Lemma big_sepLｰseqｰapp₁ {Φ i n} n1 n2 :
      n = n1 + n2 →
      ([∗ list] k ∈ seq i n, Φ k) ⊢
        ([∗ list] k ∈ seq i n1, Φ k) ∗
        ([∗ list] k ∈ seq (i + n1) n2, Φ k).
    Proof.
      intros ->.
      rewrite big_sepLｰseqｰapp //.
    Qed.
    Lemma big_sepLｰseqｰapp₂ Φ i1 n1 i2 n2 :
      i2 = i1 + n1 →
      ([∗ list] k ∈ seq i1 n1, Φ k) -∗
      ([∗ list] k ∈ seq i2 n2, Φ k) -∗
      [∗ list] k ∈ seq i1 (n1 + n2), Φ k.
    Proof.
      rewrite big_sepLｰseqｰapp.
      iSteps.
    Qed.

    Lemma big_sepLｰseqｰlookupｰacc {Φ i n} j :
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
    Lemma big_sepLｰseqｰlookupｰacc' {Φ i n} j :
      i ≤ j < i + n →
      ([∗ list] k ∈ seq i n, Φ k) ⊢
        Φ j ∗
        ( Φ j -∗
          [∗ list] k ∈ seq i n, Φ k
        ).
    Proof.
      intros ((j' & ->)%Nat.le_sum & Hj).
      rewrite -big_sepLｰseqｰlookupｰacc //. lia.
    Qed.
    Lemma big_sepLｰseqｰlookup `{!BiAffine PROP} {Φ i n} j :
      j < n →
      ([∗ list] k ∈ seq i n, Φ k) ⊢
      Φ (i + j).
    Proof.
      intros Hj.
      rewrite big_sepLｰseqｰlookupｰacc //.
      iSteps.
    Qed.
    Lemma big_sepLｰseqｰlookup' `{!BiAffine PROP} {Φ i n} j :
      i ≤ j < i + n →
      ([∗ list] k ∈ seq i n, Φ k) ⊢
      Φ j.
    Proof.
      intros Hj.
      rewrite big_sepLｰseqｰlookupｰacc' //.
      iSteps.
    Qed.

    Lemma big_sepLｰseqｰindex `{!BiAffine PROP} {Φ} l i n :
      length l = n →
      ([∗ list] k ∈ seq i n, Φ k) ⊣⊢
      [∗ list] k ↦ _ ∈ l, Φ (i + k).
    Proof.
      intros. iSplit.
      all: iIntros "H".
      all: iApply (big_sepLｰimplｰstrong with "H"); first simp_length.
      all: iIntros "!> %k %k_ % % % HΦ".
      all: pose proof lookup_seq.
      all: naive_solver.
    Qed.
    Lemma big_sepLｰseqｰindex₁ `{!BiAffine PROP} {Φ} l i n :
      length l = n →
      ([∗ list] k ∈ seq i n, Φ k) ⊢
      [∗ list] k ↦ _ ∈ l, Φ (i + k).
    Proof.
      intros. rewrite big_sepLｰseqｰindex //.
    Qed.
    Lemma big_sepLｰseqｰindex₂ `{!BiAffine PROP} {Φ l} n :
      length l = n →
      ([∗ list] k ↦ _ ∈ l, Φ k) ⊢
      [∗ list] k ∈ seq 0 n, Φ k.
    Proof.
      intros. rewrite big_sepLｰseqｰindex //.
    Qed.

    Lemma big_sepLｰseqｰshift `{!BiAffine PROP} {Φ} j i n :
      ([∗ list] k ∈ seq (i + j) n, Φ k) ⊣⊢
      [∗ list] k ∈ seq i n, Φ (k + j).
    Proof.
      iSplit.
      all: iIntros "H".
      all: iApply (big_sepLｰimplｰstrong with "H"); first simp_length.
      all: iIntros "!>" (k ? ? (-> & _)%lookup_seq (-> & _)%lookup_seq).
      all: rewrite Nat.add_shuffle0.
      all: iSteps.
    Qed.
    Lemma big_sepLｰseqｰshift' `{!BiAffine PROP} {Φ} j i n :
      ([∗ list] k ∈ seq (i + j) n, Φ (k - j)) ⊣⊢
      [∗ list] k ∈ seq i n, Φ k.
    Proof.
      rewrite big_sepLｰseqｰshift.
      setoid_rewrite Nat.add_sub => //.
    Qed.
    Lemma big_sepLｰseqｰshift₁ `{!BiAffine PROP} {Φ} j i n :
      ([∗ list] k ∈ seq (i + j) n, Φ k) ⊢
      [∗ list] k ∈ seq i n, Φ (k + j).
    Proof.
      rewrite big_sepLｰseqｰshift //.
    Qed.
    Lemma big_sepLｰseqｰshift₂ `{!BiAffine PROP} {Φ} j i n :
      ([∗ list] k ∈ seq i n, Φ (k + j)) ⊢
      [∗ list] k ∈ seq (i + j) n, Φ k.
    Proof.
      rewrite big_sepLｰseqｰshift //.
    Qed.
    Lemma big_sepLｰseqｰshift₂' `{!BiAffine PROP} {Φ} j i n :
      ([∗ list] k ∈ seq i n, Φ k) ⊢
      [∗ list] k ∈ seq (i + j) n, Φ (k - j).
    Proof.
      rewrite big_sepLｰseqｰshift' //.
    Qed.

    Lemma big_sepLｰseqｰshiftｰ1 `{!BiAffine PROP} Φ i n :
      ([∗ list] k ∈ seq ˖i n, Φ k) ⊣⊢
      [∗ list] k ∈ seq i n, Φ ˖k.
    Proof.
      setoid_rewrite <- Nat.add_1_r.
      apply big_sepLｰseqｰshift.
    Qed.
    Lemma big_sepLｰseqｰshiftｰ1₁ `{!BiAffine PROP} Φ i n :
      ([∗ list] k ∈ seq ˖i n, Φ k) ⊢
      [∗ list] k ∈ seq i n, Φ ˖k.
    Proof.
      rewrite big_sepLｰseqｰshiftｰ1 //.
    Qed.
    Lemma big_sepLｰseqｰshiftｰ1₂ `{!BiAffine PROP} Φ i n :
      ([∗ list] k ∈ seq i n, Φ ˖k) ⊢
      [∗ list] k ∈ seq ˖i n, Φ k.
    Proof.
      rewrite big_sepLｰseqｰshiftｰ1 //.
    Qed.

    Lemma big_sepLｰseqｰexists `{!BiAffine PROP} `(Φ : nat → A → PROP) i n :
      ([∗ list] k ∈ seq i n, ∃ x, Φ k x) ⊢
        ∃ xs,
        ⌜length xs = n⌝ ∗
        [∗ list] k ↦ x ∈ xs, Φ (i + k) x.
    Proof.
      iIntros "H".
      iDestruct (big_sepLｰexists with "H") as "(%xs & %Hxs & H)". simp_length in Hxs.
      iDestruct (big_sepL2ｰseqｰl with "H") as "H".
      iSteps.
    Qed.

    Lemma big_sepLｰseqｰtoｰseqZ `{!BiAffine PROP} Φ i n :
      ([∗ list] k ∈ seq i n, Φ k) ⊢
      [∗ list] k ∈ seqZ ⁺i ⁺n, Φ ₊k.
    Proof.
      iIntros "H".
      iApply (big_sepLｰimplｰstrong with "H").
      { simp_length. lia. }
      iIntros "!>" (k k1 k2 (-> & _)%lookup_seq (-> & _)%lookup_seqZ) "HΦ".
      rewrite -Nat2Z.inj_add Nat2Z.id //.
    Qed.
    Lemma big_sepLｰseqｰtoｰseqZ' `{!BiAffine PROP} Φ i n :
      (0 ≤ i)%Z →
      (0 ≤ n)%Z →
      ([∗ list] k ∈ seq ₊i ₊n, Φ k) ⊢
      [∗ list] k ∈ seqZ i n, Φ ₊k.
    Proof.
      intros.
      rewrite big_sepLｰseqｰtoｰseqZ.
      setoid_rewrite Z2Nat.id => //.
    Qed.
  End big_sepL۰seq.
End bi.
