From zoo Require Import
  prelude.
From zoo.common Require Import
  list.
From zoo.iris.bi Require Export
  big_op.base.
From zoo.iris Require Import
  diaframe.
From zoo Require Import
  options.

Section bi.
  Context {PROP : bi}.

  Section big_sepL.
    Context {A : Type}.

    Implicit Types Φ : nat → A → PROP.

    Lemma big_sepL_to_seq `{!BiAffine PROP} Φ l i :
      ([∗ list] k ↦ y ∈ l, Φ k y) ⊣⊢
      [∗ list] k ∈ seq i (length l),
        ∃ y,
        ⌜l !! (k - i) = Some y⌝ ∗
        Φ (k - i) y.
    Proof.
      iInduction l as [| x l] "IH" forall (Φ i) => /=; first iSteps.
      iSplit.
      - rewrite Nat.sub_diag. iSteps as "H".
        iApply (big_sepL_impl with "(IH H)"). iIntros "!>" (k ? (-> & Hk)%lookup_seq) "/=".
        replace (i + k - i) with k by lia.
        replace (S (i + k) - i) with (S k) by lia.
        iSteps.
      - rewrite Nat.sub_diag. iSteps as (y) "H".
        iApply "IH".
        iApply (big_sepL_impl with "H"). iIntros "!>" (k ? (-> & Hk)%lookup_seq) "/=".
        replace (i + k - i) with k by lia.
        replace (S (i + k) - i) with (S k) by lia.
        iSteps.
    Qed.
    Lemma big_sepL_to_seq0 `{!BiAffine PROP} Φ l :
      ([∗ list] k ↦ y ∈ l, Φ k y) ⊣⊢
      [∗ list] k ∈ seq 0 (length l),
        ∃ y,
        ⌜l !! k = Some y⌝ ∗
        Φ k y.
    Proof.
      rewrite (big_sepL_to_seq _ _ 0).
      setoid_rewrite Nat.sub_0_r. done.
    Qed.
  End big_sepL.

  Section big_sepL.
    Context {A : Type}.

    Implicit Types Φ : nat → A → PROP.

    Lemma big_sepL_cons_1 Φ x l :
      ([∗ list] k ↦ y ∈ (x :: l), Φ k y) ⊢
        Φ 0 x ∗
        [∗ list] k ↦ y ∈ l, Φ (S k) y.
    Proof.
      rewrite big_sepL_cons //.
    Qed.
    Lemma big_sepL_cons_2 Φ x l :
      Φ 0 x -∗
      ([∗ list] k ↦ y ∈ l, Φ (S k) y) -∗
      [∗ list] k ↦ y ∈ (x :: l), Φ k y.
    Proof.
      rewrite big_sepL_cons. iSteps.
    Qed.
    Lemma big_sepL_cons_2' (Φ : A → PROP) x l :
      Φ x -∗
      ([∗ list] y ∈ l, Φ y) -∗
      [∗ list] y ∈ (x :: l), Φ y.
    Proof.
      rewrite big_sepL_cons. iSteps.
    Qed.

    Lemma big_sepL_app_1 Φ l1 l2 :
      ([∗ list] k ↦ y ∈ l1 ++ l2, Φ k y) ⊢
        ([∗ list] k ↦ y ∈ l1, Φ k y) ∗
        ([∗ list] k ↦ y ∈ l2, Φ (length l1 + k) y).
    Proof.
      rewrite big_sepL_app //.
    Qed.
    Lemma big_sepL_app_2 Φ l1 l2 :
      ([∗ list] k ↦ y ∈ l1, Φ k y) -∗
      ([∗ list] k ↦ y ∈ l2, Φ (length l1 + k) y) -∗
      [∗ list] k ↦ y ∈ l1 ++ l2, Φ k y.
    Proof.
      rewrite big_sepL_app. iSteps.
    Qed.

    Lemma big_sepL_snoc_1 Φ l x :
      ([∗ list] k ↦ y ∈ (l ++ [x]), Φ k y) ⊢
        ([∗ list] k ↦ y ∈ l, Φ k y) ∗
        Φ (length l) x.
    Proof.
      rewrite big_sepL_snoc //.
    Qed.
    Lemma big_sepL_snoc_2 {Φ l} x :
      ([∗ list] k ↦ y ∈ l, Φ k y) -∗
      Φ (length l) x -∗
      ([∗ list] k ↦ y ∈ (l ++ [x]), Φ k y).
    Proof.
      rewrite big_sepL_snoc. iSteps.
    Qed.

    Lemma big_sepL_impl_stronger `{!BiAffine PROP} {A1 A2} (Φ1 : nat → A1 → PROP) l1 (Φ2 : nat → A2 → PROP) l2 :
      length l1 = length l2 →
      ([∗ list] k ↦ x ∈ l1, Φ1 k x) -∗
      ( [∗ list] k ∈ seq 0 (length l1),
        ∀ x1 x2,
        ⌜l1 !! k = Some x1⌝ -∗
        ⌜l2 !! k = Some x2⌝ -∗
        Φ1 k x1 -∗
        Φ2 k x2
      ) -∗
      [∗ list] k ↦ x ∈ l2, Φ2 k x.
    Proof.
      setoid_rewrite big_sepL_to_seq0. simpl_length.
      iIntros "%Hlength Hl1 H". rewrite -Hlength.
      iDestruct (big_sepL_sep_2 with "Hl1 H") as "H".
      iApply (big_sepL_impl with "H"). iIntros "!>" (k ? (-> & Hk)%lookup_seq) "((%x1 & %Hl1_lookup & Hx1) & (% & %H & H))".
      apply lookup_seq in H as (-> & _) => /=.
      destruct (lookup_lt_is_Some_2 l2 k) as (x2 & Hl2_lookup); first lia.
      iSteps.
    Qed.
    Lemma big_sepL_impl_strong `{!BiAffine PROP} {A1 A2} (Φ1 : nat → A1 → PROP) (l1 : list A1) (Φ2 : nat → A2 → PROP) (l2 : list A2) :
      length l1 = length l2 →
      ([∗ list] k ↦ x ∈ l1, Φ1 k x) -∗
      □ (
        ∀ k x1 x2,
        ⌜l1 !! k = Some x1⌝ -∗
        ⌜l2 !! k = Some x2⌝ -∗
        Φ1 k x1 -∗
        Φ2 k x2
      ) -∗
      [∗ list] k ↦ x ∈ l2, Φ2 k x.
    Proof.
      iIntros "% HΦ #H".
      iApply (big_sepL_impl_stronger with "HΦ [H]"); first done.
      iApply big_sepL_intro. iIntros "!> %k %k_ % %x1 %x2 % % HΦ".
      iSteps.
    Qed.

    Lemma big_sepL_impl_sepL2 `{!BiAffine PROP} {B1 B2} Φ1 l (Φ2 : nat → B1 → B2 → PROP) 𝑙1 𝑙2 :
      length l = length 𝑙1 →
      length l = length 𝑙2 →
      ([∗ list] k ↦ y ∈ l, Φ1 k y) -∗
      □ (
        ∀ k x 𝑥1 𝑥2,
        ⌜l !! k = Some x⌝ -∗
        ⌜𝑙1 !! k = Some 𝑥1⌝ -∗
        ⌜𝑙2 !! k = Some 𝑥2⌝ -∗
        Φ1 k x -∗
        Φ2 k 𝑥1 𝑥2
      ) -∗
      [∗ list] k ↦ y1; y2 ∈ 𝑙1; 𝑙2, Φ2 k y1 y2.
    Proof.
      rewrite big_sepL2_alt.
      iIntros "% % HΦ #H". iStep 2.
      iApply (big_sepL_impl_strong with "HΦ").
      { simpl_length. lia. }
      iIntros "!>" (k x (𝑥1, 𝑥2) ? (? & ? & [= <- <-] & ? & ?)%lookup_zip_with_Some).
      iSteps.
    Qed.

    Lemma big_sepL_insert `{!BiAffine PROP} {Φ l} i x :
      i < length l →
      ([∗ list] k ↦ y ∈ l, Φ k y) -∗
      Φ i x -∗
      [∗ list] k ↦ y ∈ <[i := x]> l, Φ k y.
    Proof.
      intros (y & Hlookup)%lookup_lt_is_Some.
      rewrite big_sepL_insert_acc //. iSteps.
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
      intros.
      setoid_rewrite big_sepL_delete at 2; last done.
      iSteps.
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
      intros.
      setoid_rewrite big_sepL_delete' at 2; last done.
      iSteps.
    Qed.

    Lemma big_sepL_replicate `{!BiAffine PROP} Φ n x :
      ([∗ list] k ↦ y ∈ replicate n x, Φ k y) ⊣⊢
      [∗ list] k ∈ seq 0 n, Φ k x.
    Proof.
      iSplit.
      all: iIntros "H".
      all: iApply (big_sepL_impl_strong with "H"); first simpl_length.
      1: iIntros "!>" (? ? ? (-> & _)%lookup_replicate_1 (-> & _)%lookup_seq).
      2: iIntros "!>" (? ? ? (-> & _)%lookup_seq (-> & _)%lookup_replicate_1).
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

    Lemma big_sepL_exists `{!BiAffine PROP} {B} (Φ : nat → A → B → PROP) l :
      ([∗ list] k ↦ x ∈ l, ∃ y, Φ k x y) ⊢
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

    Lemma big_sepL_retract_index Φ l :
      ([∗ list] k ↦ x ∈ l, Φ k x) ⊢
      [∗ list] x ∈ l, ∃ k, Φ k x.
    Proof.
      iIntros "H".
      iApply (big_sepL_impl with "H").
      iModIntro. iSteps.
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
      ).
      { move/(_ 0) => //. }
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
      ).
      { move/(_ 0) => //. }
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

    Lemma big_sepL_Forall `{!BiPureForall PROP} (ϕ : A → Prop) l :
      ([∗ list] x ∈ l, ⌜ϕ x⌝) ⊢@{PROP}
      ⌜Forall ϕ l⌝.
    Proof.
      rewrite Forall_lookup.
      iIntros "H %i %x %Hlookup".
      iApply (big_sepL_lookup with "H"); first done.
    Qed.

    Lemma big_sepL_Foralli `{!BiPureForall PROP} (ϕ : nat → A → Prop) l :
      ([∗ list] k ↦ x ∈ l, ⌜ϕ k x⌝) ⊢@{PROP}
      ⌜Foralli ϕ l⌝.
    Proof.
      rewrite Foralli_lookup.
      iIntros "H %i %x %Hlookup".
      iApply (big_sepL_lookup with "H"); first done.
    Qed.
  End big_sepL.
End bi.
