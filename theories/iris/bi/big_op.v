From iris.bi Require Export
  big_op.

From zoo Require Import
  prelude.
From zoo.iris Require Import
  diaframe.
From zoo.common Require Import
  list.
From zoo Require Import
  options.

Section bi.
  Context {PROP : bi}.

  Section big_sepL.
    Context {A : Type}.

    Implicit Types l : list A.
    Implicit Types Φ Ψ : nat → A → PROP.

    Lemma big_sepL_mono_strong' `{!BiAffine PROP} {A1 A2} (l1 : list A1) (l2 : list A2) (Φ1 : nat → A1 → PROP) (Φ2 : nat → A2 → PROP) :
      length l1 = length l2 →
      ([∗ list] k ↦ x ∈ l1, Φ1 k x) -∗
      ( [∗ list] k ∈ seq 0 (length l1), ∀ x1 x2,
        ⌜l1 !! k = Some x1 ∧ l2 !! k = Some x2⌝ -∗
        Φ1 k x1 -∗
        Φ2 k x2
      ) -∗
      [∗ list] k ↦ x ∈ l2, Φ2 k x.
    Proof.
      iIntros "%Hl2 HΦ1 HΦ". remember (length l1) as sz eqn:Hl1.
      iInduction sz as [| sz] "IH" forall (l1 l2 Hl1 Hl2).
      { apply symmetry, nil_length_inv in Hl2 as ->. iSteps. }
      destruct (rev_elim l1) as [-> | (x1 & l1' & ->)]; first done.
      destruct (rev_elim l2) as [-> | (x2 & l2' & ->)]; first done.
      rewrite !app_length !Nat.add_1_r !Nat.succ_inj_wd in Hl1 Hl2.
      rewrite List.seq_S /=. iDestruct (big_sepL_snoc with "HΦ") as "(HΦ & HΦ')".
      iDestruct (big_sepL_snoc with "HΦ1") as "(HΦ1 & HΦ1')".
      iApply big_sepL_snoc. iSplitL "HΦ HΦ1".
      - iApply ("IH" with "[] [] HΦ1 [HΦ]"); [iSteps.. |].
        iApply (big_sepL_mono with "HΦ"). iIntros "%k %_k %H_k HΦ %x1' %x2' % HΦ1". apply lookup_seq in H_k as (-> & ?).
        iApply "HΦ"; naive_solver eauto using lookup_app_l_Some.
      - rewrite -Hl1 -Hl2. iApply ("HΦ'" with "[] HΦ1'"). rewrite !list_lookup_middle //.
    Qed.
    Lemma big_sepL_mono_strong `{!BiAffine PROP} {A1 A2} (l1 : list A1) (l2 : list A2) (Φ1 : nat → A1 → PROP) (Φ2 : nat → A2 → PROP) :
      length l1 = length l2 →
      ([∗ list] k ↦ x ∈ l1, Φ1 k x) -∗
      □ (
        ∀ k x1 x2,
        ⌜l1 !! k = Some x1 ∧ l2 !! k = Some x2⌝ -∗
        Φ1 k x1 -∗
        Φ2 k x2
      ) -∗
      [∗ list] k ↦ x ∈ l2, Φ2 k x.
    Proof.
      iIntros "% HΦ1 #HΦ".
      iApply (big_sepL_mono_strong' with "HΦ1 [HΦ]"); first done.
      iApply big_sepL_intro. iIntros "!> %k %_k % %x1 %x2 % HΨ".
      iApply ("HΦ" with "[//] HΨ").
    Qed.

    Lemma big_sepL_seq_index `{!BiAffine PROP} l sz (Φ : nat → PROP) :
      length l = sz →
      ([∗ list] k ∈ seq 0 sz, Φ k) ⊣⊢
      [∗ list] k ↦ _ ∈ l, Φ k.
    Proof.
      intros. iSplit.
      all: iIntros "H".
      all: iApply (big_sepL_mono_strong with "H"); first rewrite seq_length //.
      all: iIntros "!> %k %_k % %".
      all: pose proof lookup_seq.
      all: naive_solver.
    Qed.
    Lemma big_sepL_seq_index_1 `{!BiAffine PROP} l sz (Φ : nat → PROP) :
      length l = sz →
      ([∗ list] k ∈ seq 0 sz, Φ k) ⊢
      [∗ list] k ↦ _ ∈ l, Φ k.
    Proof.
      intros. rewrite big_sepL_seq_index //.
    Qed.
    Lemma big_sepL_seq_index_2 `{!BiAffine PROP} l sz (Φ : nat → PROP) :
      length l = sz →
      ([∗ list] k ↦ _ ∈ l, Φ k) ⊢
      [∗ list] k ∈ seq 0 sz, Φ k.
    Proof.
      intros. rewrite big_sepL_seq_index //.
    Qed.

    Lemma big_sepL_seq_shift `{!BiAffine PROP} j i sz (Φ : nat → PROP) :
      ([∗ list] k ∈ seq i sz, Φ k) ⊣⊢
      [∗ list] k ∈ seq (i + j) sz, Φ (k - j).
    Proof.
      iSplit.
      all: iIntros "H".
      all: iApply (big_sepL_mono_strong with "H"); first rewrite !seq_length //.
      all: iIntros "!>" (k ? ? ((-> & _)%lookup_seq & (-> & _)%lookup_seq)).
      all: assert (i + j + k - j = i + k) as -> by lia.
      all: iSteps.
    Qed.
    Lemma big_sepL_seq_shift_1 `{!BiAffine PROP} j i sz (Φ : nat → PROP) :
      ([∗ list] k ∈ seq i sz, Φ k) ⊢
      [∗ list] k ∈ seq (i + j) sz, Φ (k - j).
    Proof.
      rewrite big_sepL_seq_shift //.
    Qed.
    Lemma big_sepL_seq_shift_2 `{!BiAffine PROP} j i sz (Φ : nat → PROP) :
      ([∗ list] k ∈ seq (i + j) sz, Φ (k - j)) ⊢
      [∗ list] k ∈ seq i sz, Φ k.
    Proof.
      rewrite -big_sepL_seq_shift //.
    Qed.

    Lemma big_sepL_delete_1 Φ l i x :
      l !! i = Some x →
      ([∗ list] k ↦ y ∈ l, Φ k y) ⊢
        Φ i x ∗
        [∗ list] k ↦ y ∈ l, if decide (k = i) then emp else Φ k y.
    Proof.
      intros. rewrite big_sepL_delete //.
    Qed.
    Lemma big_sepL_delete_2 Φ l i x :
      l !! i = Some x →
      Φ i x -∗
      ([∗ list] k ↦ y ∈ l, if decide (k = i) then emp else Φ k y) -∗
      [∗ list] k ↦ y ∈ l, Φ k y.
    Proof.
      intros. setoid_rewrite big_sepL_delete at 2; iSmash+.
    Qed.
    Lemma big_sepL_delete'_1 `{!BiAffine PROP} Φ l i x :
      l !! i = Some x →
      ([∗ list] k ↦ y ∈ l, Φ k y) ⊢
        Φ i x ∗
        [∗ list] k ↦ y ∈ l, ⌜k ≠ i⌝ → Φ k y.
    Proof.
      intros. rewrite big_sepL_delete' //.
    Qed.
    Lemma big_sepL_delete'_2 `{!BiAffine PROP} Φ l i x :
      l !! i = Some x →
      Φ i x -∗
      ([∗ list] k ↦ y ∈ l, ⌜k ≠ i⌝ → Φ k y) -∗
      [∗ list] k ↦ y ∈ l, Φ k y.
    Proof.
      intros. setoid_rewrite big_sepL_delete' at 2; iSmash+.
    Qed.

    Lemma big_sepL_replicate `{!BiAffine PROP} Φ n x :
      ([∗ list] k ↦ y ∈ replicate n x, Φ k y) ⊣⊢
      [∗ list] k ∈ seq 0 n, Φ k x.
    Proof.
      iSplit.
      all: iIntros "H".
      all: iApply (big_sepL_mono_strong with "H"); first rewrite replicate_length seq_length //.
      1: iIntros "!>" (? ? ? ((-> & _)%lookup_replicate_1 & (-> & _)%lookup_seq)).
      2: iIntros "!>" (? ? ? ((-> & _)%lookup_seq & (-> & _)%lookup_replicate_1)).
      all: iSteps.
    Qed.
    Lemma big_sepL_replicate_1 `{!BiAffine PROP} Φ n x :
      ([∗ list] k ↦ y ∈ replicate n x, Φ k y) ⊢
      [∗ list] k ∈ seq 0 n, Φ k x.
    Proof.
      rewrite big_sepL_replicate //.
    Qed.
    Lemma big_sepL_replicate_2 `{!BiAffine PROP} Φ n x :
      ([∗ list] k ∈ seq 0 n, Φ k x) ⊢
      [∗ list] k ↦ y ∈ replicate n x, Φ k y.
    Proof.
      rewrite big_sepL_replicate //.
    Qed.
  End big_sepL.

  Section big_sepL2.
    Context {A1 A2 : Type}.

    Implicit Types Φ Ψ : nat → A1 → A2 → PROP.

    Lemma big_sepL2_lookup_Some_l Φ i x1 l1 l2 :
      l1 !! i = Some x1 →
      ([∗ list] k ↦ y1; y2 ∈ l1; l2, Φ k y1 y2) ⊢
      ⌜is_Some (l2 !! i)⌝.
    Proof.
      iIntros (Hi%lookup_lt_Some) "H".
      iDestruct (big_sepL2_length with "H") as %Hlength.
      iPureIntro. apply lookup_lt_is_Some_2. lia.
    Qed.
    Lemma big_sepL2_lookup_Some_r Φ i x2 l1 l2 :
      l2 !! i = Some x2 →
      ([∗ list] k ↦ y1; y2 ∈ l1; l2, Φ k y1 y2) ⊢
      ⌜is_Some (l1 !! i)⌝.
    Proof.
      iIntros (Hi%lookup_lt_Some) "H".
      iDestruct (big_sepL2_length with "H") as %Hlength.
      iPureIntro. apply lookup_lt_is_Some_2. lia.
    Qed.

    Lemma big_sepL2_delete_1 Φ l1 l2 i x1 x2 :
      l1 !! i = Some x1 →
      l2 !! i = Some x2 →
      ([∗ list] k ↦ y1; y2 ∈ l1; l2, Φ k y1 y2) ⊢
        Φ i x1 x2 ∗
        [∗ list] k ↦ y1; y2 ∈ l1; l2, if decide (k = i) then emp else Φ k y1 y2.
    Proof.
      intros. rewrite big_sepL2_delete //.
    Qed.
    Lemma big_sepL2_delete_2 Φ l1 l2 i x1 x2 :
      l1 !! i = Some x1 →
      l2 !! i = Some x2 →
      Φ i x1 x2 -∗
      ([∗ list] k ↦ y1; y2 ∈ l1; l2, if decide (k = i) then emp else Φ k y1 y2) -∗
      [∗ list] k ↦ y1; y2 ∈ l1; l2, Φ k y1 y2.
    Proof.
      intros. setoid_rewrite big_sepL2_delete at 2; iSmash+.
    Qed.
    Lemma big_sepL2_delete'_1 `{!BiAffine PROP} Φ l1 l2 i x1 x2 :
      l1 !! i = Some x1 →
      l2 !! i = Some x2 →
      ([∗ list] k ↦ y1; y2 ∈ l1; l2, Φ k y1 y2) ⊢
        Φ i x1 x2 ∗
        [∗ list] k ↦ y1; y2 ∈ l1; l2, ⌜k ≠ i⌝ → Φ k y1 y2.
    Proof.
      intros. rewrite big_sepL2_delete' //.
    Qed.
    Lemma big_sepL2_delete'_2 `{!BiAffine PROP} Φ l1 l2 i x1 x2 :
      l1 !! i = Some x1 →
      l2 !! i = Some x2 →
      Φ i x1 x2 -∗
      ([∗ list] k ↦ y1; y2 ∈ l1; l2, ⌜k ≠ i⌝ → Φ k y1 y2) -∗
      [∗ list] k ↦ y1; y2 ∈ l1; l2, Φ k y1 y2.
    Proof.
      intros. setoid_rewrite big_sepL2_delete' at 2; iSmash+.
    Qed.

    Lemma big_sepL2_replicate_l_1 l x Φ n :
      length l = n →
      ([∗ list] k ↦ x1; x2 ∈ replicate n x; l, Φ k x1 x2) ⊢
      [∗ list] k ↦ x2 ∈ l, Φ k x x2.
    Proof.
      intros. rewrite big_sepL2_replicate_l //.
    Qed.
    Lemma big_sepL2_replicate_l_2 l x Φ n :
      length l = n →
      ([∗ list] k ↦ x2 ∈ l, Φ k x x2) ⊢
      [∗ list] k ↦ x1; x2 ∈ replicate n x; l, Φ k x1 x2.
    Proof.
      intros. rewrite big_sepL2_replicate_l //.
    Qed.
    Lemma big_sepL2_replicate_r_1 l x Φ n :
      length l = n →
      ([∗ list] k ↦ x1; x2 ∈ l; replicate n x, Φ k x1 x2) ⊢
      [∗ list] k ↦ x1 ∈ l, Φ k x1 x.
    Proof.
      intros. rewrite big_sepL2_replicate_r //.
    Qed.
    Lemma big_sepL2_replicate_r_2 l x Φ n :
      length l = n →
      ([∗ list] k ↦ x1 ∈ l, Φ k x1 x) ⊢
      [∗ list] k ↦ x1; x2 ∈ l; replicate n x, Φ k x1 x2.
    Proof.
      intros. rewrite big_sepL2_replicate_r //.
    Qed.
  End big_sepL2.
End bi.
