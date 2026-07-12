Require Import zoo.prelude.
Require Import zoo.common.list.
Require Export zoo.iris.bi.big_op.big_sepL.
Require Import zoo.iris.diaframe.
Require Import zoo.options.

Section bi.
  Context {PROP : bi}.

  Section big_sepL2.
    Context {A1 A2 : Type}.

    Implicit Types Φ : nat → A1 → A2 → PROP.

    Lemma big_sepL2_bupd `{BiBUpd PROP} Φ l1 l2 :
      ([∗ list] k ↦ y1; y2 ∈ l1; l2, |==> Φ k y1 y2) ==∗
      [∗ list] k ↦ y1; y2 ∈ l1; l2, Φ k y1 y2.
    Proof.
      rewrite !big_sepL2_alt big_sepL_bupd.
      iIntros "($ & H)". iSteps.
    Qed.

    Lemma big_sepL2_impl_strong `{!BiAffine PROP} {B1 B2} Φ1 l1 l2 (Φ2 : nat → B1 → B2 → PROP) 𝑙1 𝑙2 :
      length l1 = length 𝑙1 →
      length l2 = length 𝑙2 →
      ([∗ list] k ↦ y1; y2 ∈ l1; l2, Φ1 k y1 y2) -∗
      □ (
        ∀ k x1 x2 𝑥1 𝑥2,
        ⌜l1 !! k = Some x1⌝ -∗
        ⌜l2 !! k = Some x2⌝ -∗
        ⌜𝑙1 !! k = Some 𝑥1⌝ -∗
        ⌜𝑙2 !! k = Some 𝑥2⌝ -∗
        Φ1 k x1 x2 -∗
        Φ2 k 𝑥1 𝑥2
      ) -∗
      [∗ list] k ↦ y1; y2 ∈ 𝑙1; 𝑙2, Φ2 k y1 y2.
    Proof.
      rewrite !big_sepL2_alt.
      iIntros "% % (% & HΦ) #H". iStep 2.
      iApply (big_sepL_impl_strong with "HΦ").
      { simpl_length. lia. }
      iIntros "!>" (k (x1, x2) (𝑥1, 𝑥2) (? & ? & [= <- <-] & ? & ?)%lookup_zip_with_Some (? & ? & [= <- <-] & ? & ?)%lookup_zip_with_Some).
      iSteps.
    Qed.
    Lemma big_sepL2_impl_strong_l `{!BiAffine PROP} {B} Φ1 l1 l2 (Φ2 : nat → B → A2 → PROP) 𝑙 :
      length l1 = length 𝑙 →
      ([∗ list] k ↦ y1; y2 ∈ l1; l2, Φ1 k y1 y2) -∗
      □ (
        ∀ k x1 x2 𝑥,
        ⌜l1 !! k = Some x1⌝ -∗
        ⌜l2 !! k = Some x2⌝ -∗
        ⌜𝑙 !! k = Some 𝑥⌝ -∗
        Φ1 k x1 x2 -∗
        Φ2 k 𝑥 x2
      ) -∗
      [∗ list] k ↦ y1; y2 ∈ 𝑙; l2, Φ2 k y1 y2.
    Proof.
      iIntros "% HΦ #H".
      iApply (big_sepL2_impl_strong with "HΦ"); [done.. |].
      iModIntro. iSteps. simplify. iSteps.
    Qed.
    Lemma big_sepL2_impl_strong_r `{!BiAffine PROP} {B} Φ1 l1 l2 (Φ2 : nat → A1 → B → PROP) 𝑙 :
      length l2 = length 𝑙 →
      ([∗ list] k ↦ y1; y2 ∈ l1; l2, Φ1 k y1 y2) -∗
      □ (
        ∀ k x1 x2 𝑥,
        ⌜l1 !! k = Some x1⌝ -∗
        ⌜l2 !! k = Some x2⌝ -∗
        ⌜𝑙 !! k = Some 𝑥⌝ -∗
        Φ1 k x1 x2 -∗
        Φ2 k x1 𝑥
      ) -∗
      [∗ list] k ↦ y1; y2 ∈ l1; 𝑙, Φ2 k y1 y2.
    Proof.
      iIntros "% HΦ #H".
      iApply (big_sepL2_impl_strong with "HΦ"); [done.. |].
      iModIntro. iSteps. simplify. iSteps.
    Qed.

    Lemma big_sepL2_impl_sepL `{!BiAffine PROP} {B} Φ1 l1 l2 (Φ2 : nat → B → PROP) 𝑙 :
      length l1 = length 𝑙 ∨ length l2 = length 𝑙 →
      ([∗ list] k ↦ y1; y2 ∈ l1; l2, Φ1 k y1 y2) -∗
      □ (
        ∀ k x1 x2 𝑥,
        ⌜l1 !! k = Some x1⌝ -∗
        ⌜l2 !! k = Some x2⌝ -∗
        ⌜𝑙 !! k = Some 𝑥⌝ -∗
        Φ1 k x1 x2 -∗
        Φ2 k 𝑥
      ) -∗
      [∗ list] k ↦ y ∈ 𝑙, Φ2 k y.
    Proof.
      rewrite big_sepL2_alt.
      iIntros "% (% & HΦ) #H".
      iApply (big_sepL_impl_strong with "HΦ").
      { simpl_length. lia. }
      iIntros "!>" (k (x1, x2) 𝑥 (? & ? & [= <- <-] & ? & ?)%lookup_zip_with_Some ?).
      iSteps.
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

    Lemma big_sepL2_cons_1 Φ x1 x2 l1 l2 :
      ([∗ list] k ↦ y1; y2 ∈ x1 :: l1; x2 :: l2, Φ k y1 y2) ⊢
        Φ 0 x1 x2 ∗
        [∗ list] k ↦ y1; y2 ∈ l1; l2, Φ ˖k y1 y2.
    Proof.
      rewrite big_sepL2_cons //.
    Qed.
    Lemma big_sepL2_cons_2 Φ x1 x2 l1 l2 :
      Φ 0 x1 x2 -∗
      ([∗ list] k ↦ y1; y2 ∈ l1; l2, Φ ˖k y1 y2) -∗
      [∗ list] k ↦ y1; y2 ∈ x1 :: l1; x2 :: l2, Φ k y1 y2.
    Proof.
      rewrite big_sepL2_cons. iSteps.
    Qed.
    Lemma big_sepL2_cons_2' (Φ : A1 → A2 → PROP) x1 x2 l1 l2 :
      Φ x1 x2 -∗
      ([∗ list] k ↦ y1; y2 ∈ l1; l2, Φ y1 y2) -∗
      [∗ list] k ↦ y1; y2 ∈ x1 :: l1; x2 :: l2, Φ y1 y2.
    Proof.
      rewrite big_sepL2_cons. iSteps.
    Qed.

    Lemma big_sepL2_snoc_2 {Φ l1 l2} x1 x2 :
      ([∗ list] k ↦ y1; y2 ∈ l1; l2, Φ k y1 y2) -∗
      Φ (length l1) x1 x2 -∗
      [∗ list] k ↦ y1; y2 ∈ l1 ++ [x1]; l2 ++ [x2], Φ k y1 y2.
    Proof.
      rewrite big_sepL2_snoc. iSteps.
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

    Lemma big_sepL2_lookup_Some_l {Φ} i x1 l1 l2 :
      l1 !! i = Some x1 →
      ([∗ list] k ↦ y1; y2 ∈ l1; l2, Φ k y1 y2) ⊢
      ⌜is_Some (l2 !! i)⌝.
    Proof.
      iIntros (Hi%lookup_lt_Some) "H".
      iDestruct (big_sepL2_length with "H") as %Hlength.
      iPureIntro. apply lookup_lt_is_Some_2. lia.
    Qed.
    Lemma big_sepL2_lookup_Some_r {Φ} i x2 l1 l2 :
      l2 !! i = Some x2 →
      ([∗ list] k ↦ y1; y2 ∈ l1; l2, Φ k y1 y2) ⊢
      ⌜is_Some (l1 !! i)⌝.
    Proof.
      iIntros (Hi%lookup_lt_Some) "H".
      iDestruct (big_sepL2_length with "H") as %Hlength.
      iPureIntro. apply lookup_lt_is_Some_2. lia.
    Qed.

    Lemma big_sepL2_lookup_acc_l `{!BiAffine PROP} {Φ} i x1 l1 l2 :
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
    Lemma big_sepL2_lookup_acc_r `{!BiAffine PROP} {Φ} i x2 l1 l2 :
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

    Lemma big_sepL2_lookup_l `{!BiAffine PROP} {Φ} i x1 l1 l2 :
      l1 !! i = Some x1 →
      ([∗ list] k ↦ y1; y2 ∈ l1; l2, Φ k y1 y2) ⊢
        ∃ x2,
        ⌜l2 !! i = Some x2⌝ ∗
        Φ i x1 x2.
    Proof.
      intros. rewrite big_sepL2_lookup_acc_l //. iSteps.
    Qed.
    Lemma big_sepL2_lookup_r `{!BiAffine PROP} {Φ} i x2 l1 l2 :
      l2 !! i = Some x2 →
      ([∗ list] k ↦ y1; y2 ∈ l1; l2, Φ k y1 y2) ⊢
        ∃ x1,
        ⌜l1 !! i = Some x1⌝ ∗
        Φ i x1 x2.
    Proof.
      intros. rewrite big_sepL2_lookup_acc_r //. iSteps.
    Qed.

    Lemma big_sepL2_elem_of_l `{!BiAffine PROP} {Φ l1 l2} x1 :
      x1 ∈ l1 →
      ([∗ list] k ↦ y1; y2 ∈ l1; l2, Φ k y1 y2) ⊢
        ∃ k x2,
        ⌜x2 ∈ l2⌝ ∗
        Φ k x1 x2.
    Proof.
      setoid_rewrite list_elem_of_lookup.
      iIntros ((i & Hl1_lookup)) "H".
      iDestruct (big_sepL2_lookup_l with "H") as "(%x2 & %Hl2_lookup & H)"; first done.
      iSteps.
    Qed.
    Lemma big_sepL2_elem_of_l' `{!BiAffine PROP} {Φ : A1 → A2 → PROP} {l1 l2} x1 :
      x1 ∈ l1 →
      ([∗ list] k ↦ y1; y2 ∈ l1; l2, Φ y1 y2) ⊢
        ∃ x2,
        ⌜x2 ∈ l2⌝ ∗
        Φ x1 x2.
    Proof.
      intros.
      rewrite big_sepL2_elem_of_l //. iSteps.
    Qed.

    Lemma big_sepL2_delete_1 {Φ l1 l2} i x1 x2 :
      l1 !! i = Some x1 →
      l2 !! i = Some x2 →
      ([∗ list] k ↦ y1; y2 ∈ l1; l2, Φ k y1 y2) ⊢
        Φ i x1 x2 ∗
        [∗ list] k ↦ y1; y2 ∈ l1; l2, if decide (k = i) then emp else Φ k y1 y2.
    Proof.
      intros. rewrite big_sepL2_delete //.
    Qed.
    Lemma big_sepL2_delete_2 {Φ l1 l2} i x1 x2 :
      l1 !! i = Some x1 →
      l2 !! i = Some x2 →
      Φ i x1 x2 -∗
      ([∗ list] k ↦ y1; y2 ∈ l1; l2, if decide (k = i) then emp else Φ k y1 y2) -∗
      [∗ list] k ↦ y1; y2 ∈ l1; l2, Φ k y1 y2.
    Proof.
      intros.
      setoid_rewrite big_sepL2_delete at 2; [| done..].
      iSteps.
    Qed.
    Lemma big_sepL2_delete'_1 `{!BiAffine PROP} {Φ l1 l2} i x1 x2 :
      l1 !! i = Some x1 →
      l2 !! i = Some x2 →
      ([∗ list] k ↦ y1; y2 ∈ l1; l2, Φ k y1 y2) ⊢
        Φ i x1 x2 ∗
        [∗ list] k ↦ y1; y2 ∈ l1; l2, ⌜k ≠ i⌝ → Φ k y1 y2.
    Proof.
      intros. rewrite big_sepL2_delete' //.
    Qed.
    Lemma big_sepL2_delete'_2 `{!BiAffine PROP} {Φ l1 l2} i x1 x2 :
      l1 !! i = Some x1 →
      l2 !! i = Some x2 →
      Φ i x1 x2 -∗
      ([∗ list] k ↦ y1; y2 ∈ l1; l2, ⌜k ≠ i⌝ → Φ k y1 y2) -∗
      [∗ list] k ↦ y1; y2 ∈ l1; l2, Φ k y1 y2.
    Proof.
      intros.
      setoid_rewrite big_sepL2_delete' at 2; [| done..].
      iSteps.
    Qed.

    Lemma big_sepL2_delete_l {Φ l1 l2} i x1 :
      l1 !! i = Some x1 →
      ([∗ list] k ↦ y1; y2 ∈ l1; l2, Φ k y1 y2) ⊢
        ∃ x2,
        ⌜l2 !! i = Some x2⌝ ∗
        Φ i x1 x2 ∗
        [∗ list] k ↦ y1; y2 ∈ l1; l2, if decide (k = i) then emp else Φ k y1 y2.
    Proof.
      iIntros "%Hl1_lookup H".
      iDestruct (big_sepL2_lookup_Some_l with "H") as %(x2 & Hl2_lookup); first done.
      rewrite big_sepL2_delete //. iFrameSteps.
    Qed.
    Lemma big_sepL2_delete'_l `{!BiAffine PROP} {Φ l1 l2} i x1 :
      l1 !! i = Some x1 →
      ([∗ list] k ↦ y1; y2 ∈ l1; l2, Φ k y1 y2) ⊢
        ∃ x2,
        ⌜l2 !! i = Some x2⌝ ∗
        Φ i x1 x2 ∗
        [∗ list] k ↦ y1; y2 ∈ l1; l2, ⌜k ≠ i⌝ → Φ k y1 y2.
    Proof.
      iIntros "%Hl1_lookup H".
      iDestruct (big_sepL2_lookup_Some_l with "H") as %(x2 & Hl2_lookup); first done.
      rewrite big_sepL2_delete' //. iFrameSteps.
    Qed.

    Lemma big_sepL2_insert_acc_l {Φ l1 l2} i x1 :
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
    Lemma big_sepL2_insert_acc_r {Φ l1 l2} i x2 :
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

    Lemma big_sepL2_replicate_l_1 Φ l x n :
      length l = n →
      ([∗ list] k ↦ x1; x2 ∈ replicate n x; l, Φ k x1 x2) ⊢
      [∗ list] k ↦ x2 ∈ l, Φ k x x2.
    Proof.
      intros. rewrite big_sepL2_replicate_l //.
    Qed.
    Lemma big_sepL2_replicate_l_2 Φ l x n :
      length l = n →
      ([∗ list] k ↦ x2 ∈ l, Φ k x x2) ⊢
      [∗ list] k ↦ x1; x2 ∈ replicate n x; l, Φ k x1 x2.
    Proof.
      intros. rewrite big_sepL2_replicate_l //.
    Qed.
    Lemma big_sepL2_replicate_r_1 Φ l x n :
      length l = n →
      ([∗ list] k ↦ x1; x2 ∈ l; replicate n x, Φ k x1 x2) ⊢
      [∗ list] k ↦ x1 ∈ l, Φ k x1 x.
    Proof.
      intros. rewrite big_sepL2_replicate_r //.
    Qed.
    Lemma big_sepL2_replicate_r_2 Φ l x n :
      length l = n →
      ([∗ list] k ↦ x1 ∈ l, Φ k x1 x) ⊢
      [∗ list] k ↦ x1; x2 ∈ l; replicate n x, Φ k x1 x2.
    Proof.
      intros. rewrite big_sepL2_replicate_r //.
    Qed.

    Lemma big_sepL2_Forall2 `{!BiAffine PROP} `{!BiPureForall PROP} (ϕ : A1 → A2 → Prop) l1 l2 :
      ([∗ list] x1; x2 ∈ l1; l2, ⌜ϕ x1 x2⌝) ⊢@{PROP}
      ⌜Forall2 ϕ l1 l2⌝.
    Proof.
      rewrite Forall2_same_length_lookup big_sepL2_forall.
      iSteps.
    Qed.
    Lemma big_sepL2_Forall2i `{!BiAffine PROP} `{!BiPureForall PROP} (ϕ : nat → A1 → A2 → Prop) l1 l2 :
      ([∗ list] k ↦ x1; x2 ∈ l1; l2, ⌜ϕ k x1 x2⌝) ⊢@{PROP}
      ⌜Forall2i ϕ l1 l2⌝.
    Proof.
      rewrite Forall2i_same_length_lookup big_sepL2_forall.
      iSteps.
    Qed.

    Lemma big_sepL_extract_l `{!BiAffine PROP} Φ l1 l2 :
      length l1 = length l2 →
      ( [∗ list] k ↦ x2 ∈ l2,
        ∃ x1,
        ⌜l1 !! k = Some x1⌝ ∗
        Φ k x1 x2
      ) ⊢
      [∗ list] k ↦ x1; x2 ∈ l1; l2, Φ k x1 x2.
    Proof.
      iIntros "% H".
      iDestruct (big_sepL2_const_sepL_r with "[$H //]") as "H".
      iApply (big_sepL2_impl with "H"). iModIntro.
      iSteps. simplify. iSteps.
    Qed.
    Lemma big_sepL_extract_r `{!BiAffine PROP} Φ l1 l2 :
      length l1 = length l2 →
      ( [∗ list] k ↦ x1 ∈ l1,
        ∃ x2,
        ⌜l2 !! k = Some x2⌝ ∗
        Φ k x1 x2
      ) ⊢
      [∗ list] k ↦ x1; x2 ∈ l1; l2, Φ k x1 x2.
    Proof.
      iIntros "% H".
      iDestruct (big_sepL2_const_sepL_l with "[$H //]") as "H".
      iApply (big_sepL2_impl with "H"). iModIntro.
      iSteps. simplify. iSteps.
    Qed.

    Lemma big_sepL2_retract_l `{!BiAffine PROP} Φ l1 l2 :
      ([∗ list] k ↦ x1; x2 ∈ l1; l2, Φ k x1 x2) ⊢
        ⌜length l1 = length l2⌝ ∗
        [∗ list] k ↦ x2 ∈ l2,
          ∃ x1,
          ⌜l1 !! k = Some x1⌝ ∗
          Φ k x1 x2.
    Proof.
      iIntros "H".
      iDestruct (big_sepL2_length with "H") as %Hlen. iStep.
      iApply (big_sepL2_impl_sepL with "H"); first naive_solver. iIntros "!>".
      iSteps. simplify. iSteps.
    Qed.
    Lemma big_sepL2_retract_r `{!BiAffine PROP} Φ l1 l2 :
      ([∗ list] k ↦ x1; x2 ∈ l1; l2, Φ k x1 x2) ⊢
        ⌜length l1 = length l2⌝ ∗
        [∗ list] k ↦ x1 ∈ l1,
          ∃ x2,
          ⌜l2 !! k = Some x2⌝ ∗
          Φ k x1 x2.
    Proof.
      iIntros "H".
      iDestruct (big_sepL2_length with "H") as %Hlen. iStep.
      iApply (big_sepL2_impl_sepL with "H"); first naive_solver. iIntros "!>".
      iSteps. simplify. iSteps.
    Qed.

    Lemma big_sepL2_seq_l `{!BiAffine PROP} `(Φ : nat → nat → A → PROP) i n l2 :
      ([∗ list] k ↦ x1; x2 ∈ seq i n; l2, Φ k x1 x2) ⊢
      [∗ list] k ↦ x2 ∈ l2, Φ k (i + k) x2.
    Proof.
      rewrite big_sepL2_alt. simpl_length.
      iIntros "(-> & H)".
      iApply (big_sepL_impl_strong with "H").
      { simpl_length. lia. }
      iIntros "!>" (k ? x2 (k1 & x2_ & -> & (-> & _)%lookup_seq & Hlookup1)%lookup_zip_with_Some Hlookup2) "H". simplify.
      iSteps.
    Qed.
    Lemma big_sepL2_seq_r `{!BiAffine PROP} `(Φ : nat → A → nat → PROP) l1 i n :
      ([∗ list] k ↦ x1; x2 ∈ l1; seq i n, Φ k x1 x2) ⊢
      [∗ list] k ↦ x1 ∈ l1, Φ k x1 (i + k).
    Proof.
      rewrite big_sepL2_flip big_sepL2_seq_l //.
    Qed.
  End big_sepL2.

  Section big_sepL2.
    Context {A1 A2 : Type}.

    Implicit Types Φ : nat → A1 → A2 → PROP.

    Lemma big_sepL2_elem_of_r `{!BiAffine PROP} {Φ l1 l2} x2 :
      x2 ∈ l2 →
      ([∗ list] k ↦ y1; y2 ∈ l1; l2, Φ k y1 y2) ⊢
        ∃ k x1,
        ⌜x1 ∈ l1⌝ ∗
        Φ k x1 x2.
    Proof.
      intros.
      rewrite big_sepL2_flip big_sepL2_elem_of_l //.
    Qed.
    Lemma big_sepL2_elem_of_r' `{!BiAffine PROP} {Φ : A1 → A2 → PROP} {l1 l2} x2 :
      x2 ∈ l2 →
      ([∗ list] y1; y2 ∈ l1; l2, Φ y1 y2) ⊢
        ∃ x1,
        ⌜x1 ∈ l1⌝ ∗
        Φ x1 x2.
    Proof.
      intros.
      rewrite big_sepL2_elem_of_r //. iSteps.
    Qed.

    Lemma big_sepL2_delete_r {Φ l1 l2} i x2 :
      l2 !! i = Some x2 →
      ([∗ list] k ↦ y1; y2 ∈ l1; l2, Φ k y1 y2) ⊢
        ∃ x1,
        ⌜l1 !! i = Some x1⌝ ∗
        Φ i x1 x2 ∗
        [∗ list] k ↦ y1; y2 ∈ l1; l2, if decide (k = i) then emp else Φ k y1 y2.
    Proof.
      intros.
      setoid_rewrite big_sepL2_flip.
      rewrite big_sepL2_delete_l //.
    Qed.
    Lemma big_sepL2_delete'_r `{!BiAffine PROP} {Φ l1 l2} i x2 :
      l2 !! i = Some x2 →
      ([∗ list] k ↦ y1; y2 ∈ l1; l2, Φ k y1 y2) ⊢
        ∃ x1,
        ⌜l1 !! i = Some x1⌝ ∗
        Φ i x1 x2 ∗
        [∗ list] k ↦ y1; y2 ∈ l1; l2, ⌜k ≠ i⌝ → Φ k y1 y2.
    Proof.
      intros.
      setoid_rewrite big_sepL2_flip.
      rewrite big_sepL2_delete'_l //.
    Qed.
  End big_sepL2.
End bi.
