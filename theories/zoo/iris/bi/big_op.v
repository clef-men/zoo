From iris.bi Require Export
  big_op.

From zoo Require Import
  prelude.
From zoo.common Require Import
  fin_maps.
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

    Lemma big_sepL_cons_1 x l Φ :
      ([∗ list] k ↦ y ∈ (x :: l), Φ k y) ⊢
        Φ 0 x ∗
        [∗ list] k ↦ y ∈ l, Φ (S k) y.
    Proof.
      rewrite big_sepL_cons //.
    Qed.
    Lemma big_sepL_cons_2 x l Φ :
      Φ 0 x -∗
      ([∗ list] k ↦ y ∈ l, Φ (S k) y) -∗
      [∗ list] k ↦ y ∈ (x :: l), Φ k y.
    Proof.
      rewrite big_sepL_cons. iSteps.
    Qed.

    Lemma big_sepL_snoc_1 l x Φ :
      ([∗ list] k↦y ∈ (l ++ [x]), Φ k y) ⊢
        ([∗ list] k↦y ∈ l, Φ k y) ∗
        Φ (length l) x.
    Proof.
      rewrite big_sepL_snoc //.
    Qed.
    Lemma big_sepL_snoc_2 l x Φ :
      ([∗ list] k↦y ∈ l, Φ k y) -∗
      Φ (length l) x -∗
      ([∗ list] k↦y ∈ (l ++ [x]), Φ k y).
    Proof.
      rewrite big_sepL_snoc. iSteps.
    Qed.

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
      rewrite !length_app !Nat.add_1_r !Nat.succ_inj_wd in Hl1 Hl2.
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
      all: iApply (big_sepL_mono_strong with "H"); first rewrite length_seq //.
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
      all: iApply (big_sepL_mono_strong with "H"); first rewrite !length_seq //.
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
      ([∗ list] k ∈ seq (i + j) sz, Φ k) ⊢
      [∗ list] k ∈ seq i sz, Φ (k + j).
    Proof.
      setoid_rewrite (big_sepL_seq_shift j) at 2.
      iIntros "H".
      iApply (big_sepL_impl with "H"). iIntros "!>" (? ? (-> & ?)%lookup_seq).
      assert (i + j + k = i + j + k - j + j) as <- by lia.
      iSteps.
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
      all: iApply (big_sepL_mono_strong with "H"); first rewrite length_replicate length_seq //.
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

    Lemma big_sepL_or_l Ψ l Φ :
      ([∗ list] k ↦ x ∈ l, Φ k x) ⊢
      [∗ list] k ↦ x ∈ l, Ψ k x ∨ Φ k x.
    Proof.
      apply big_sepL_mono. iSteps.
    Qed.
    Lemma big_sepL_or_r Ψ l Φ :
      ([∗ list] k ↦ x ∈ l, Φ k x) ⊢
      [∗ list] k ↦ x ∈ l, Φ k x ∨ Ψ k x.
    Proof.
      apply big_sepL_mono. iSteps.
    Qed.

    Lemma big_sepL_exists `{!BiAffine PROP} {B} l (Φ : nat → A → B → PROP) :
      ([∗ list] k ↦ x ∈ l, ∃ (y : B), Φ k x y) ⊢
        ∃ ys,
        ⌜length ys = length l⌝ ∗
        [∗ list] k ↦ x; y ∈ l; ys, Φ k x y.
    Proof.
      iIntros "H".
      iInduction l as [| x l] "IH" forall (Φ) => /=.
      - iExists []. iSteps.
      - iDestruct "H" as "((%y & Hx) & H)".
        iDestruct ("IH" with "H") as "(%ys & %Hlength & H)".
        iExists (y :: ys). iSteps.
    Qed.

    Lemma big_sepL_impl_thread {Φ1} P Φ2 l :
      ([∗ list] k ↦ x ∈ l, Φ1 k x) -∗
      P -∗
      □ (
        ∀ k x,
        ⌜l !! k = Some x⌝ →
        Φ1 k x -∗
        P -∗
          Φ2 k x ∗
          P
      ) -∗
        ([∗ list] k ↦ x ∈ l, Φ2 k x) ∗
        P.
    Proof.
      cut (∀ n,
        ([∗ list] k ↦ x ∈ l, Φ1 (n + k) x) -∗
        P -∗
        □ (
          ∀ k x,
          ⌜l !! k = Some x⌝ →
          Φ1 (n + k) x -∗
          P -∗
            Φ2 (n + k) x ∗
            P
        ) -∗
          ([∗ list] k ↦ x ∈ l, Φ2 (n + k) x) ∗
          P
      ). {
        intros Hcut. apply (Hcut 0).
      }
      iIntros "%n Hl HP #HΦ".
      iInduction l as [| x l] "IH" forall (n); first iSteps.
      iDestruct (big_sepL_cons_1 with "Hl") as "(Hx & Hl)".
      iDestruct ("HΦ" with "[%] Hx HP") as "($ & HP)"; first done.
      setoid_rewrite Nat.add_succ_r.
      iApply ("IH" $! (S n) with "[] Hl HP").
      { iIntros "!> %k' %x' %Hlookup' Hx' HP".
        rewrite Nat.add_succ_comm.
        iApply ("HΦ" with "[%] Hx' HP"); first done.
      }
    Qed.
    Lemma big_sepL_impl_thread_fupd `{!BiFUpd PROP} {Φ1} P Φ2 l E :
      ([∗ list] k ↦ x ∈ l, Φ1 k x) -∗
      P -∗
      □ (
        ∀ k x,
        ⌜l !! k = Some x⌝ →
        Φ1 k x -∗
        P -∗
          |={E}=>
          Φ2 k x ∗
          P
      ) -∗
        |={E}=>
        ([∗ list] k ↦ x ∈ l, Φ2 k x) ∗
        P.
    Proof.
      cut (∀ n,
        ([∗ list] k ↦ x ∈ l, Φ1 (n + k) x) -∗
        P -∗
        □ (
          ∀ k x,
          ⌜l !! k = Some x⌝ →
          Φ1 (n + k) x -∗
          P -∗
            |={E}=>
            Φ2 (n + k) x ∗
            P
        ) -∗
          |={E}=>
          ([∗ list] k ↦ x ∈ l, Φ2 (n + k) x) ∗
          P
      ). {
        intros Hcut. apply (Hcut 0).
      }
      iIntros "%n Hl HP #HΦ".
      iInduction l as [| x l] "IH" forall (n); first iSteps.
      iDestruct (big_sepL_cons_1 with "Hl") as "(Hx & Hl)".
      iMod ("HΦ" with "[%] Hx HP") as "($ & HP)"; first done.
      setoid_rewrite Nat.add_succ_r.
      iApply ("IH" $! (S n) with "[] Hl HP").
      { iIntros "!> %k' %x' %Hlookup' Hx' HP".
        rewrite Nat.add_succ_comm.
        iApply ("HΦ" with "[%] Hx' HP"); first done.
      }
    Qed.
  End big_sepL.

  Section big_sepL2.
    Context {A1 A2 : Type}.

    Implicit Types ϕ : A1 → A2 → Prop.
    Implicit Types Φ Ψ : nat → A1 → A2 → PROP.

    Lemma big_sepL2_bupd `{BiBUpd PROP} Φ l1 l2 :
      ([∗ list] k ↦ y1; y2 ∈ l1; l2, |==> Φ k y1 y2) ==∗
      [∗ list] k ↦ y1; y2 ∈ l1; l2, Φ k y1 y2.
    Proof.
      rewrite !big_sepL2_alt big_sepL_bupd.
      iIntros "($ & H)". iSteps.
    Qed.

    Lemma big_sepL2_impl_bupd `{!BiBUpd PROP} Φ1 l1 Φ2 l2 :
      ([∗ list] k ↦ y1; y2 ∈ l1; l2, Φ1 k y1 y2) -∗
      □ (
        ∀ k x1 x2,
        ⌜l1 !! k = Some x1⌝ -∗
        ⌜l2 !! k = Some x2⌝ -∗
        Φ1 k x1 x2 ==∗
        Φ2 k x1 x2
      ) -∗
      |==> [∗ list] k ↦ y1; y2 ∈ l1; l2, Φ2 k y1 y2.
    Proof.
      iIntros "H1 #H".
      iApply big_sepL2_bupd.
      iApply (big_sepL2_impl with "H1 [H]"). iIntros "!>".
      iSteps.
    Qed.
    Lemma big_sepL2_impl_fupd `{!BiFUpd PROP} Φ1 l1 Φ2 l2 E :
      ([∗ list] k ↦ y1; y2 ∈ l1; l2, Φ1 k y1 y2) -∗
      □ (
        ∀ k x1 x2,
        ⌜l1 !! k = Some x1⌝ -∗
        ⌜l2 !! k = Some x2⌝ -∗
        Φ1 k x1 x2 ={E}=∗
        Φ2 k x1 x2
      ) -∗
      |={E}=> [∗ list] k ↦ y1; y2 ∈ l1; l2, Φ2 k y1 y2.
    Proof.
      iIntros "H1 #H".
      iApply big_sepL2_fupd.
      iApply (big_sepL2_impl with "H1 [H]"). iIntros "!>".
      iSteps.
    Qed.

    Lemma big_sepL2_wand_bupd `{!BiBUpd PROP} Φ1 l1 Φ2 l2 :
      ([∗ list] k ↦ y1; y2 ∈ l1; l2, Φ1 k y1 y2) -∗
      ([∗ list] k ↦ y1; y2 ∈ l1; l2, Φ1 k y1 y2 ==∗ Φ2 k y1 y2) -∗
      |==> [∗ list] k ↦ y1; y2 ∈ l1; l2, Φ2 k y1 y2.
    Proof.
      iIntros "H1 H2".
      iApply big_sepL2_bupd.
      iApply (big_sepL2_wand with "H1 H2").
    Qed.
    Lemma big_sepL2_wand_fupd `{!BiFUpd PROP} Φ1 l1 Φ2 l2 E :
      ([∗ list] k ↦ y1; y2 ∈ l1; l2, Φ1 k y1 y2) -∗
      ([∗ list] k ↦ y1; y2 ∈ l1; l2, Φ1 k y1 y2 ={E}=∗ Φ2 k y1 y2) -∗
      |={E}=> [∗ list] k↦y1;y2 ∈ l1;l2, Φ2 k y1 y2.
    Proof.
      iIntros "H1 H2".
      iApply big_sepL2_fupd.
      iApply (big_sepL2_wand with "H1 H2").
    Qed.

    Lemma big_sepL2_snoc_inv_l Φ l1 x1 l2 :
      ([∗ list] k ↦ y1; y2 ∈ l1 ++ [x1]; l2, Φ k y1 y2) ⊢
        ∃ l2' x2,
        ⌜l2 = l2' ++ [x2]⌝ ∗
        ([∗ list] k ↦ y1; y2 ∈ l1; l2', Φ k y1 y2) ∗
        Φ (length l1) x1 x2.
    Proof.
      iIntros "H".
      iDestruct (big_sepL2_app_inv_l with "H") as "(%l2' & %l2'' & -> & H1 & H2)".
      iDestruct (big_sepL2_cons_inv_l with "H2") as "(%x2 & %l2''' & -> & H2 & H3)".
      iDestruct (big_sepL2_nil_inv_l with "H3") as %->.
      rewrite right_id. iSteps.
    Qed.
    Lemma big_sepL2_snoc_inv_r Φ l1 l2 x2 :
      ([∗ list] k ↦ y1; y2 ∈ l1; l2 ++ [x2], Φ k y1 y2) ⊢
        ∃ l1' x1,
        ⌜l1 = l1' ++ [x1]⌝ ∗
        ([∗ list] k ↦ y1; y2 ∈ l1'; l2, Φ k y1 y2) ∗
        Φ (length l2) x1 x2.
    Proof.
      iIntros "H".
      iDestruct (big_sepL2_app_inv_r with "H") as "(%l1' & %l1'' & -> & H1 & H2)".
      iDestruct (big_sepL2_cons_inv_r with "H2") as "(%x1 & %l1''' & -> & H2 & H3)".
      iDestruct (big_sepL2_nil_inv_r with "H3") as %->.
      rewrite right_id. iSteps.
    Qed.

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

    Lemma big_sepL2_lookup_acc_l `{!BiAffine PROP} Φ i x1 l1 l2 :
      l1 !! i = Some x1 →
      ([∗ list] k ↦ y1; y2 ∈ l1; l2, Φ k y1 y2) ⊢
        ∃ x2,
        ⌜l2 !! i = Some x2⌝ ∗
        Φ i x1 x2 ∗
        ( Φ i x1 x2 -∗
          [∗ list] k ↦ y1; y2 ∈ l1; l2, Φ k y1 y2
        ).
    Proof.
      iIntros "%Hlookup1 H".
      iDestruct (big_sepL2_lookup_Some_l with "H") as %(x2 & Hlookup2); first done.
      iDestruct (big_sepL2_lookup_acc with "H") as "H"; [done.. |].
      iSteps.
    Qed.
    Lemma big_sepL2_lookup_acc_r `{!BiAffine PROP} Φ i x2 l1 l2 :
      l2 !! i = Some x2 →
      ([∗ list] k ↦ y1; y2 ∈ l1; l2, Φ k y1 y2) ⊢
        ∃ x1,
        ⌜l1 !! i = Some x1⌝ ∗
        Φ i x1 x2 ∗
        ( Φ i x1 x2 -∗
          [∗ list] k ↦ y1; y2 ∈ l1; l2, Φ k y1 y2
        ).
    Proof.
      iIntros "%Hlookup2 H".
      iDestruct (big_sepL2_lookup_Some_r with "H") as %(x1 & Hlookup1); first done.
      iDestruct (big_sepL2_lookup_acc with "H") as "H"; [done.. |].
      iSteps.
    Qed.

    Lemma big_sepL2_lookup_l `{!BiAffine PROP} Φ i x1 l1 l2 :
      l1 !! i = Some x1 →
      ([∗ list] k ↦ y1; y2 ∈ l1; l2, Φ k y1 y2) ⊢
        ∃ x2,
        ⌜l2 !! i = Some x2⌝ ∗
        Φ i x1 x2.
    Proof.
      intros. rewrite big_sepL2_lookup_acc_l //. iSteps.
    Qed.
    Lemma big_sepL2_lookup_r `{!BiAffine PROP} Φ i x2 l1 l2 :
      l2 !! i = Some x2 →
      ([∗ list] k ↦ y1; y2 ∈ l1; l2, Φ k y1 y2) ⊢
        ∃ x1,
        ⌜l1 !! i = Some x1⌝ ∗
        Φ i x1 x2.
    Proof.
      intros. rewrite big_sepL2_lookup_acc_r //. iSteps.
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

    Lemma big_sepL2_insert_acc_l Φ l1 l2 i x1 :
      l1 !! i = Some x1 →
      ([∗ list] k ↦ y1; y2 ∈ l1; l2, Φ k y1 y2) ⊢
        ∃ x2,
        ⌜l2 !! i = Some x2⌝ ∗
        Φ i x1 x2 ∗
        ( ∀ y1 y2,
          Φ i y1 y2 -∗
          [∗ list] k ↦ y1; y2 ∈ <[i := y1]> l1; <[i := y2]> l2, Φ k y1 y2
        ).
    Proof.
      iIntros "%Hl1_lookup H".
      iDestruct (big_sepL2_lookup_Some_l with "H") as %(x2 & Hl2_lookup); first done.
      iDestruct (big_sepL2_insert_acc with "H") as "$"; done.
    Qed.
    Lemma big_sepL2_insert_acc_r Φ l1 l2 i x2 :
      l2 !! i = Some x2 →
      ([∗ list] k ↦ y1; y2 ∈ l1; l2, Φ k y1 y2) ⊢
        ∃ x1,
        ⌜l1 !! i = Some x1⌝ ∗
        Φ i x1 x2 ∗
        ( ∀ y1 y2,
          Φ i y1 y2 -∗
          [∗ list] k ↦ y1; y2 ∈ <[i := y1]> l1; <[i := y2]> l2, Φ k y1 y2
        ).
    Proof.
      iIntros "%Hl2_lookup H".
      iDestruct (big_sepL2_lookup_Some_r with "H") as %(x1 & Hl1_lookup); first done.
      iDestruct (big_sepL2_insert_acc with "H") as "$"; done.
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

    Lemma big_sepL2_Forall `{!BiAffine PROP} `{!BiPureForall PROP} l1 l2 ϕ :
      ([∗ list] x1; x2 ∈ l1; l2, ⌜ϕ x1 x2⌝) ⊢@{PROP}
      ⌜Forall2 ϕ l1 l2⌝.
    Proof.
      rewrite Forall2_same_length_lookup big_sepL2_forall.
      iSteps.
    Qed.
  End big_sepL2.

  Section big_sepM.
    Context `{Countable K} {A : Type}.

    Implicit Types m : gmap K A.
    Implicit Types P : PROP.
    Implicit Types Φ : K → A → PROP.

    Lemma big_sepM_impl_thread {Φ1} P Φ2 m :
      ([∗ map] k ↦ x ∈ m, Φ1 k x) -∗
      P -∗
      □ (
        ∀ k x,
        ⌜m !! k = Some x⌝ →
        Φ1 k x -∗
        P -∗
          Φ2 k x ∗
          P
      ) -∗
        ([∗ map] k ↦ x ∈ m, Φ2 k x) ∗
        P.
    Proof.
      iIntros "Hm HP #HΦ".
      iInduction m as [| k x m Hlookup] "IH" using map_ind.
      - rewrite !big_sepM_empty. iSteps.
      - iDestruct (big_sepM_insert with "Hm") as "(Hk & Hm)"; first done.
        iDestruct ("HΦ" with "[%] Hk HP") as "(Hk & HP)".
        { rewrite lookup_insert //. }
        iDestruct ("IH" with "[HΦ] Hm HP") as "(Hm & $)".
        { iIntros "!> %k' %a' %Hlookup' Hk' HP".
          iApply ("HΦ" with "[%] Hk' HP").
          rewrite lookup_insert_ne //. congruence.
        }
        iApply big_sepM_insert; first done.
        iSteps.
    Qed.
    Lemma big_sepM_impl_thread_fupd `{!BiFUpd PROP} {Φ1} P Φ2 m E :
      ([∗ map] k ↦ x ∈ m, Φ1 k x) -∗
      P -∗
      □ (
        ∀ k x,
        ⌜m !! k = Some x⌝ →
        Φ1 k x -∗
        P -∗
          |={E}=>
          Φ2 k x ∗
          P
      ) -∗
        |={E}=>
        ([∗ map] k ↦ x ∈ m, Φ2 k x) ∗
        P.
    Proof.
      iIntros "Hm HP #HΦ".
      iInduction m as [| k x m Hlookup] "IH" using map_ind.
      - rewrite !big_sepM_empty. iSteps.
      - iDestruct (big_sepM_insert with "Hm") as "(Hk & Hm)"; first done.
        iMod ("HΦ" with "[%] Hk HP") as "(Hk & HP)".
        { rewrite lookup_insert //. }
        iMod ("IH" with "[HΦ] Hm HP") as "(Hm & $)".
        { iIntros "!> %k' %a' %Hlookup' Hk' HP".
          iApply ("HΦ" with "[%] Hk' HP").
          rewrite lookup_insert_ne //. congruence.
        }
        iApply big_sepM_insert; first done.
        iSteps.
    Qed.

    Lemma big_sepM_kmap f `{!Inj (=) (=) f} m Φ :
      ([∗ map] k ↦ x ∈ (kmap f m), Φ k x) ⊣⊢
      [∗ map] k ↦ x ∈ m, Φ (f k) x.
    Proof.
      rewrite !big_opM_map_to_list map_to_list_kmap big_sepL_fmap //.
    Qed.
  End big_sepM.
End bi.
