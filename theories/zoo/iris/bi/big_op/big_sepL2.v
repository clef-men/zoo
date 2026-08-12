Require Import zoo.prelude.
Require Import zoo.common.list.
Require Export zoo.iris.bi.big_op.big_sepL.
Require Import zoo.iris.diaframe.
Require Import zoo.options.

Section bi.
  Context {PROP : bi}.

  Section big_sepL2.
    Context {A1 A2 : Type}.

    Implicit Type Φ : nat → A1 → A2 → PROP.

    Lemma big_sepL2ｰbupd `{BiBUpd PROP} Φ l1 l2 :
      ([∗ list] k ↦ y1; y2 ∈ l1; l2, |==> Φ k y1 y2) ==∗
      [∗ list] k ↦ y1; y2 ∈ l1; l2, Φ k y1 y2.
    Proof.
      rewrite !big_sepL2_alt big_sepL_bupd.
      iIntros "($ & H)". iSteps.
    Qed.

    Lemma big_sepL2ｰimplｰstrong `{!BiAffine PROP} {B1 B2} Φ1 l1 l2 (Φ2 : nat → B1 → B2 → PROP) 𝑙1 𝑙2 :
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
      iApply (big_sepLｰimplｰstrong with "HΦ").
      { simpl_length. lia. }
      iIntros "!>" (k (x1, x2) (𝑥1, 𝑥2) (? & ? & [= <- <-] & ? & ?)%lookup_zip_with_Some (? & ? & [= <- <-] & ? & ?)%lookup_zip_with_Some).
      iSteps.
    Qed.
    Lemma big_sepL2ｰimplｰstrongｰl `{!BiAffine PROP} {B} Φ1 l1 l2 (Φ2 : nat → B → A2 → PROP) 𝑙 :
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
      iApply (big_sepL2ｰimplｰstrong with "HΦ"); [done.. |].
      iModIntro. iSteps. simp. iSteps.
    Qed.
    Lemma big_sepL2ｰimplｰstrongｰr `{!BiAffine PROP} {B} Φ1 l1 l2 (Φ2 : nat → A1 → B → PROP) 𝑙 :
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
      iApply (big_sepL2ｰimplｰstrong with "HΦ"); [done.. |].
      iModIntro. iSteps. simp. iSteps.
    Qed.

    Lemma big_sepL2ｰimplｰsepL `{!BiAffine PROP} {B} Φ1 l1 l2 (Φ2 : nat → B → PROP) 𝑙 :
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
      iApply (big_sepLｰimplｰstrong with "HΦ").
      { simpl_length. lia. }
      iIntros "!>" (k (x1, x2) 𝑥 (? & ? & [= <- <-] & ? & ?)%lookup_zip_with_Some ?).
      iSteps.
    Qed.

    Lemma big_sepL2ｰimplｰbupd `{!BiBUpd PROP} Φ1 l1 Φ2 l2 :
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
      iApply big_sepL2ｰbupd.
      iApply (big_sepL2_impl with "H1 [H]"). iIntros "!>".
      iSteps.
    Qed.
    Lemma big_sepL2ｰimplｰfupd `{!BiFUpd PROP} Φ1 l1 Φ2 l2 E :
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

    Lemma big_sepL2ｰwandｰbupd `{!BiBUpd PROP} Φ1 l1 Φ2 l2 :
      ([∗ list] k ↦ y1; y2 ∈ l1; l2, Φ1 k y1 y2) -∗
      ([∗ list] k ↦ y1; y2 ∈ l1; l2, Φ1 k y1 y2 ==∗ Φ2 k y1 y2) -∗
      |==> [∗ list] k ↦ y1; y2 ∈ l1; l2, Φ2 k y1 y2.
    Proof.
      iIntros "H1 H2".
      iApply big_sepL2ｰbupd.
      iApply (big_sepL2_wand with "H1 H2").
    Qed.
    Lemma big_sepL2ｰwandｰfupd `{!BiFUpd PROP} Φ1 l1 Φ2 l2 E :
      ([∗ list] k ↦ y1; y2 ∈ l1; l2, Φ1 k y1 y2) -∗
      ([∗ list] k ↦ y1; y2 ∈ l1; l2, Φ1 k y1 y2 ={E}=∗ Φ2 k y1 y2) -∗
      |={E}=> [∗ list] k↦y1;y2 ∈ l1;l2, Φ2 k y1 y2.
    Proof.
      iIntros "H1 H2".
      iApply big_sepL2_fupd.
      iApply (big_sepL2_wand with "H1 H2").
    Qed.

    Lemma big_sepL2_cons₁ Φ x1 x2 l1 l2 :
      ([∗ list] k ↦ y1; y2 ∈ x1 :: l1; x2 :: l2, Φ k y1 y2) ⊢
        Φ 0 x1 x2 ∗
        [∗ list] k ↦ y1; y2 ∈ l1; l2, Φ ˖k y1 y2.
    Proof.
      rewrite big_sepL2_cons //.
    Qed.
    Lemma big_sepL2_cons₂ Φ x1 x2 l1 l2 :
      Φ 0 x1 x2 -∗
      ([∗ list] k ↦ y1; y2 ∈ l1; l2, Φ ˖k y1 y2) -∗
      [∗ list] k ↦ y1; y2 ∈ x1 :: l1; x2 :: l2, Φ k y1 y2.
    Proof.
      rewrite big_sepL2_cons. iSteps.
    Qed.
    Lemma big_sepL2_cons₂' (Φ : A1 → A2 → PROP) x1 x2 l1 l2 :
      Φ x1 x2 -∗
      ([∗ list] k ↦ y1; y2 ∈ l1; l2, Φ y1 y2) -∗
      [∗ list] k ↦ y1; y2 ∈ x1 :: l1; x2 :: l2, Φ y1 y2.
    Proof.
      rewrite big_sepL2_cons. iSteps.
    Qed.

    Lemma big_sepL2ｰsnoc₂ {Φ l1 l2} x1 x2 :
      ([∗ list] k ↦ y1; y2 ∈ l1; l2, Φ k y1 y2) -∗
      Φ (length l1) x1 x2 -∗
      [∗ list] k ↦ y1; y2 ∈ l1 ++ [x1]; l2 ++ [x2], Φ k y1 y2.
    Proof.
      rewrite big_sepL2_snoc. iSteps.
    Qed.

    Lemma big_sepL2ｰsnocｰinvｰl Φ l1 x1 l2 :
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
    Lemma big_sepL2ｰsnocｰinvｰr Φ l1 l2 x2 :
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

    Lemma big_sepL2ｰlookupｰSomeｰl {Φ} i x1 l1 l2 :
      l1 !! i = Some x1 →
      ([∗ list] k ↦ y1; y2 ∈ l1; l2, Φ k y1 y2) ⊢
      ⌜is_Some (l2 !! i)⌝.
    Proof.
      iIntros (Hi%lookup_lt_Some) "H".
      iDestruct (big_sepL2_length with "H") as %Hlength.
      iPureIntro. apply lookup_lt_is_Some_2. lia.
    Qed.
    Lemma big_sepL2ｰlookupｰSomeｰr {Φ} i x2 l1 l2 :
      l2 !! i = Some x2 →
      ([∗ list] k ↦ y1; y2 ∈ l1; l2, Φ k y1 y2) ⊢
      ⌜is_Some (l1 !! i)⌝.
    Proof.
      iIntros (Hi%lookup_lt_Some) "H".
      iDestruct (big_sepL2_length with "H") as %Hlength.
      iPureIntro. apply lookup_lt_is_Some_2. lia.
    Qed.

    Lemma big_sepL2ｰlookupｰaccｰl `{!BiAffine PROP} {Φ} i x1 l1 l2 :
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
      iDestruct (big_sepL2ｰlookupｰSomeｰl with "H") as %(x2 & Hlookup2); first done.
      iDestruct (big_sepL2_lookup_acc with "H") as "H"; [done.. |].
      iSteps.
    Qed.
    Lemma big_sepL2ｰlookupｰaccｰr `{!BiAffine PROP} {Φ} i x2 l1 l2 :
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
      iDestruct (big_sepL2ｰlookupｰSomeｰr with "H") as %(x1 & Hlookup1); first done.
      iDestruct (big_sepL2_lookup_acc with "H") as "H"; [done.. |].
      iSteps.
    Qed.

    Lemma big_sepL2ｰlookupｰl `{!BiAffine PROP} {Φ} i x1 l1 l2 :
      l1 !! i = Some x1 →
      ([∗ list] k ↦ y1; y2 ∈ l1; l2, Φ k y1 y2) ⊢
        ∃ x2,
        ⌜l2 !! i = Some x2⌝ ∗
        Φ i x1 x2.
    Proof.
      intros. rewrite big_sepL2ｰlookupｰaccｰl //. iSteps.
    Qed.
    Lemma big_sepL2ｰlookupｰr `{!BiAffine PROP} {Φ} i x2 l1 l2 :
      l2 !! i = Some x2 →
      ([∗ list] k ↦ y1; y2 ∈ l1; l2, Φ k y1 y2) ⊢
        ∃ x1,
        ⌜l1 !! i = Some x1⌝ ∗
        Φ i x1 x2.
    Proof.
      intros. rewrite big_sepL2ｰlookupｰaccｰr //. iSteps.
    Qed.

    Lemma big_sepL2ｰelem_ofｰl `{!BiAffine PROP} {Φ l1 l2} x1 :
      x1 ∈ l1 →
      ([∗ list] k ↦ y1; y2 ∈ l1; l2, Φ k y1 y2) ⊢
        ∃ k x2,
        ⌜x2 ∈ l2⌝ ∗
        Φ k x1 x2.
    Proof.
      setoid_rewrite list_elem_of_lookup.
      iIntros ((i & Hl1_lookup)) "H".
      iDestruct (big_sepL2ｰlookupｰl with "H") as "(%x2 & %Hl2_lookup & H)"; first done.
      iSteps.
    Qed.
    Lemma big_sepL2ｰelem_ofｰl' `{!BiAffine PROP} {Φ : A1 → A2 → PROP} {l1 l2} x1 :
      x1 ∈ l1 →
      ([∗ list] k ↦ y1; y2 ∈ l1; l2, Φ y1 y2) ⊢
        ∃ x2,
        ⌜x2 ∈ l2⌝ ∗
        Φ x1 x2.
    Proof.
      intros.
      rewrite big_sepL2ｰelem_ofｰl //. iSteps.
    Qed.

    Lemma big_sepL2ｰdelete₁ {Φ l1 l2} i x1 x2 :
      l1 !! i = Some x1 →
      l2 !! i = Some x2 →
      ([∗ list] k ↦ y1; y2 ∈ l1; l2, Φ k y1 y2) ⊢
        Φ i x1 x2 ∗
        [∗ list] k ↦ y1; y2 ∈ l1; l2, if decide (k = i) then emp else Φ k y1 y2.
    Proof.
      intros. rewrite big_sepL2_delete //.
    Qed.
    Lemma big_sepL2ｰdelete₂ {Φ l1 l2} i x1 x2 :
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
    Lemma big_sepL2ｰdelete'₁ `{!BiAffine PROP} {Φ l1 l2} i x1 x2 :
      l1 !! i = Some x1 →
      l2 !! i = Some x2 →
      ([∗ list] k ↦ y1; y2 ∈ l1; l2, Φ k y1 y2) ⊢
        Φ i x1 x2 ∗
        [∗ list] k ↦ y1; y2 ∈ l1; l2, ⌜k ≠ i⌝ → Φ k y1 y2.
    Proof.
      intros. rewrite big_sepL2_delete' //.
    Qed.
    Lemma big_sepL2ｰdelete'₂ `{!BiAffine PROP} {Φ l1 l2} i x1 x2 :
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

    Lemma big_sepL2ｰdeleteｰl {Φ l1 l2} i x1 :
      l1 !! i = Some x1 →
      ([∗ list] k ↦ y1; y2 ∈ l1; l2, Φ k y1 y2) ⊢
        ∃ x2,
        ⌜l2 !! i = Some x2⌝ ∗
        Φ i x1 x2 ∗
        [∗ list] k ↦ y1; y2 ∈ l1; l2, if decide (k = i) then emp else Φ k y1 y2.
    Proof.
      iIntros "%Hl1_lookup H".
      iDestruct (big_sepL2ｰlookupｰSomeｰl with "H") as %(x2 & Hl2_lookup); first done.
      rewrite big_sepL2_delete //. iFrameSteps.
    Qed.
    Lemma big_sepL2ｰdelete'ｰl `{!BiAffine PROP} {Φ l1 l2} i x1 :
      l1 !! i = Some x1 →
      ([∗ list] k ↦ y1; y2 ∈ l1; l2, Φ k y1 y2) ⊢
        ∃ x2,
        ⌜l2 !! i = Some x2⌝ ∗
        Φ i x1 x2 ∗
        [∗ list] k ↦ y1; y2 ∈ l1; l2, ⌜k ≠ i⌝ → Φ k y1 y2.
    Proof.
      iIntros "%Hl1_lookup H".
      iDestruct (big_sepL2ｰlookupｰSomeｰl with "H") as %(x2 & Hl2_lookup); first done.
      rewrite big_sepL2_delete' //. iFrameSteps.
    Qed.

    Lemma big_sepL2ｰinsertｰaccｰl {Φ l1 l2} i x1 :
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
      iDestruct (big_sepL2ｰlookupｰSomeｰl with "H") as %(x2 & Hl2_lookup); first done.
      iDestruct (big_sepL2_insert_acc with "H") as "$"; done.
    Qed.
    Lemma big_sepL2ｰinsertｰaccｰr {Φ l1 l2} i x2 :
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
      iDestruct (big_sepL2ｰlookupｰSomeｰr with "H") as %(x1 & Hl1_lookup); first done.
      iDestruct (big_sepL2_insert_acc with "H") as "$"; done.
    Qed.

    Lemma big_sepL2ｰreplicateｰl₁ Φ l x n :
      length l = n →
      ([∗ list] k ↦ x1; x2 ∈ replicate n x; l, Φ k x1 x2) ⊢
      [∗ list] k ↦ x2 ∈ l, Φ k x x2.
    Proof.
      intros. rewrite big_sepL2_replicate_l //.
    Qed.
    Lemma big_sepL2ｰreplicateｰl₂ Φ l x n :
      length l = n →
      ([∗ list] k ↦ x2 ∈ l, Φ k x x2) ⊢
      [∗ list] k ↦ x1; x2 ∈ replicate n x; l, Φ k x1 x2.
    Proof.
      intros. rewrite big_sepL2_replicate_l //.
    Qed.
    Lemma big_sepL2ｰreplicateｰr₁ Φ l x n :
      length l = n →
      ([∗ list] k ↦ x1; x2 ∈ l; replicate n x, Φ k x1 x2) ⊢
      [∗ list] k ↦ x1 ∈ l, Φ k x1 x.
    Proof.
      intros. rewrite big_sepL2_replicate_r //.
    Qed.
    Lemma big_sepL2ｰreplicateｰr₂ Φ l x n :
      length l = n →
      ([∗ list] k ↦ x1 ∈ l, Φ k x1 x) ⊢
      [∗ list] k ↦ x1; x2 ∈ l; replicate n x, Φ k x1 x2.
    Proof.
      intros. rewrite big_sepL2_replicate_r //.
    Qed.

    Lemma big_sepL2ｰForall2 `{!BiAffine PROP} `{!BiPureForall PROP} (ϕ : A1 → A2 → Prop) l1 l2 :
      ([∗ list] x1; x2 ∈ l1; l2, ⌜ϕ x1 x2⌝) ⊢@{PROP}
      ⌜Forall2 ϕ l1 l2⌝.
    Proof.
      rewrite Forall2_same_length_lookup big_sepL2_forall.
      iSteps.
    Qed.
    Lemma big_sepL2ｰForall2i `{!BiAffine PROP} `{!BiPureForall PROP} (ϕ : nat → A1 → A2 → Prop) l1 l2 :
      ([∗ list] k ↦ x1; x2 ∈ l1; l2, ⌜ϕ k x1 x2⌝) ⊢@{PROP}
      ⌜Forall2i ϕ l1 l2⌝.
    Proof.
      rewrite Forall2iｰsame_lengthｰlookup big_sepL2_forall.
      iSteps.
    Qed.

    Lemma big_sepLｰextractｰl `{!BiAffine PROP} Φ l1 l2 :
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
      iSteps. simp. iSteps.
    Qed.
    Lemma big_sepLｰextractｰr `{!BiAffine PROP} Φ l1 l2 :
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
      iSteps. simp. iSteps.
    Qed.

    Lemma big_sepL2ｰretractｰl `{!BiAffine PROP} Φ l1 l2 :
      ([∗ list] k ↦ x1; x2 ∈ l1; l2, Φ k x1 x2) ⊢
        ⌜length l1 = length l2⌝ ∗
        [∗ list] k ↦ x2 ∈ l2,
          ∃ x1,
          ⌜l1 !! k = Some x1⌝ ∗
          Φ k x1 x2.
    Proof.
      iIntros "H".
      iDestruct (big_sepL2_length with "H") as %Hlen. iStep.
      iApply (big_sepL2ｰimplｰsepL with "H"); first naive_solver. iIntros "!>".
      iSteps. simp. iSteps.
    Qed.
    Lemma big_sepL2ｰretractｰr `{!BiAffine PROP} Φ l1 l2 :
      ([∗ list] k ↦ x1; x2 ∈ l1; l2, Φ k x1 x2) ⊢
        ⌜length l1 = length l2⌝ ∗
        [∗ list] k ↦ x1 ∈ l1,
          ∃ x2,
          ⌜l2 !! k = Some x2⌝ ∗
          Φ k x1 x2.
    Proof.
      iIntros "H".
      iDestruct (big_sepL2_length with "H") as %Hlen. iStep.
      iApply (big_sepL2ｰimplｰsepL with "H"); first naive_solver. iIntros "!>".
      iSteps. simp. iSteps.
    Qed.

    Lemma big_sepL2ｰseqｰl `{!BiAffine PROP} `(Φ : nat → nat → A → PROP) i n l2 :
      ([∗ list] k ↦ x1; x2 ∈ seq i n; l2, Φ k x1 x2) ⊢
      [∗ list] k ↦ x2 ∈ l2, Φ k (i + k) x2.
    Proof.
      rewrite big_sepL2_alt. simpl_length.
      iIntros "(-> & H)".
      iApply (big_sepLｰimplｰstrong with "H").
      { simpl_length. lia. }
      iIntros "!>" (k ? x2 (k1 & x2_ & -> & (-> & _)%lookup_seq & Hlookup1)%lookup_zip_with_Some Hlookup2) "H". simp.
      iSteps.
    Qed.
    Lemma big_sepL2ｰseqｰr `{!BiAffine PROP} `(Φ : nat → A → nat → PROP) l1 i n :
      ([∗ list] k ↦ x1; x2 ∈ l1; seq i n, Φ k x1 x2) ⊢
      [∗ list] k ↦ x1 ∈ l1, Φ k x1 (i + k).
    Proof.
      rewrite big_sepL2_flip big_sepL2ｰseqｰl //.
    Qed.
  End big_sepL2.

  Section big_sepL2.
    Context {A1 A2 : Type}.

    Implicit Type Φ : nat → A1 → A2 → PROP.

    Lemma big_sepL2ｰelem_ofｰr `{!BiAffine PROP} {Φ l1 l2} x2 :
      x2 ∈ l2 →
      ([∗ list] k ↦ y1; y2 ∈ l1; l2, Φ k y1 y2) ⊢
        ∃ k x1,
        ⌜x1 ∈ l1⌝ ∗
        Φ k x1 x2.
    Proof.
      intros.
      rewrite big_sepL2_flip big_sepL2ｰelem_ofｰl //.
    Qed.
    Lemma big_sepL2ｰelem_ofｰr' `{!BiAffine PROP} {Φ : A1 → A2 → PROP} {l1 l2} x2 :
      x2 ∈ l2 →
      ([∗ list] y1; y2 ∈ l1; l2, Φ y1 y2) ⊢
        ∃ x1,
        ⌜x1 ∈ l1⌝ ∗
        Φ x1 x2.
    Proof.
      intros.
      rewrite big_sepL2ｰelem_ofｰr //. iSteps.
    Qed.

    Lemma big_sepL2ｰdeleteｰr {Φ l1 l2} i x2 :
      l2 !! i = Some x2 →
      ([∗ list] k ↦ y1; y2 ∈ l1; l2, Φ k y1 y2) ⊢
        ∃ x1,
        ⌜l1 !! i = Some x1⌝ ∗
        Φ i x1 x2 ∗
        [∗ list] k ↦ y1; y2 ∈ l1; l2, if decide (k = i) then emp else Φ k y1 y2.
    Proof.
      intros.
      setoid_rewrite big_sepL2_flip.
      rewrite big_sepL2ｰdeleteｰl //.
    Qed.
    Lemma big_sepL2ｰdelete'ｰr `{!BiAffine PROP} {Φ l1 l2} i x2 :
      l2 !! i = Some x2 →
      ([∗ list] k ↦ y1; y2 ∈ l1; l2, Φ k y1 y2) ⊢
        ∃ x1,
        ⌜l1 !! i = Some x1⌝ ∗
        Φ i x1 x2 ∗
        [∗ list] k ↦ y1; y2 ∈ l1; l2, ⌜k ≠ i⌝ → Φ k y1 y2.
    Proof.
      intros.
      setoid_rewrite big_sepL2_flip.
      rewrite big_sepL2ｰdelete'ｰl //.
    Qed.
  End big_sepL2.
End bi.
