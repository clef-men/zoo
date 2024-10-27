From Coq Require Import
  ZifyNat.

From zoo Require Import
  prelude.
From zoo.common Require Import
  math.
From zoo.language Require Import
  notations
  diaframe.
From zoo_std Require Export
  base
  array__code.
From zoo_std Require Import
  for_
  assume
  chunk.
From zoo Require Import
  options.

Implicit Types i j n : nat.
Implicit Types l : location.
Implicit Types v t fn acc : val.
Implicit Types vs vs_left vs_right ws : list val.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Section array_inv.
    Definition array_inv t (sz : nat) : iProp Σ :=
      ∃ l,
      ⌜t = #l⌝ ∗
      l ↦ₕ Header 0 sz.

    #[global] Instance array_inv_timeless t sz :
      Timeless (array_inv t sz).
    Proof.
      apply _.
    Qed.
    #[global] Instance array_inv_persistent t sz :
      Persistent (array_inv t sz).
    Proof.
      apply _.
    Qed.

    Lemma array_inv_agree t sz1 sz2 :
      array_inv t sz1 -∗
      array_inv t sz2 -∗
      ⌜sz1 = sz2⌝.
    Proof.
      iIntros "(%l & -> & #Hhdr1) (%_l & %Heq & #Hhdr2)". injection Heq as <-.
      iDestruct (has_header_agree with "Hhdr1 Hhdr2") as %[= ->]. done.
    Qed.
  End array_inv.

  Section array_slice.
    Definition array_slice t i dq vs : iProp Σ :=
      ∃ l,
      ⌜t = #l⌝ ∗
      chunk_model (l +ₗ i) dq vs.

    #[global] Instance array_slice_timeless t i dq vs :
      Timeless (array_slice t i dq vs).
    Proof.
      apply _.
    Qed.
    #[global] Instance array_slice_persistent t i vs :
      Persistent (array_slice t i DfracDiscarded vs).
    Proof.
      apply _.
    Qed.

    #[global] Instance array_slice_fractional t i vs :
      Fractional (λ q, array_slice t i (DfracOwn q) vs).
    Proof.
      intros q1 q2. iSplit.
      - iIntros "(%l & -> & Hmodel1 & Hmodel2)". iSteps.
      - iIntros "((%l & -> & Hmodel1) & (%_l & %Heq & Hmodel2))". injection Heq as <-.
        iExists l. iSteps.
        iApply chunk_model_fractional. iSteps.
    Qed.
    #[global] Instance array_slice_as_fractional t i q vs :
      AsFractional (array_slice t i (DfracOwn q) vs) (λ q, array_slice t i (DfracOwn q) vs) q.
    Proof.
      split; [done | apply _].
    Qed.

    Lemma array_slice_valid t i dq vs :
      0 < length vs →
      array_slice t i dq vs ⊢
      ⌜✓ dq⌝.
    Proof.
      iIntros "% (%l & -> & Hmodel)".
      iApply (chunk_model_valid with "Hmodel"); first done.
    Qed.
    Lemma array_slice_combine t i dq1 vs1 dq2 vs2 :
      length vs1 = length vs2 →
      array_slice t i dq1 vs1 -∗
      array_slice t i dq2 vs2 -∗
        ⌜vs1 = vs2⌝ ∗
        array_slice t i (dq1 ⋅ dq2) vs1.
    Proof.
      iIntros "% (%l & -> & Hmodel1) (%_l & %Heq & Hmodel2)". injection Heq as <-.
      iDestruct (chunk_model_combine with "Hmodel1 Hmodel2") as "(<- & Hmodel)"; first done.
      iSteps.
    Qed.
    Lemma array_slice_valid_2 t i dq1 vs1 dq2 vs2 :
      0 < length vs1 →
      length vs1 = length vs2 →
      array_slice t i dq1 vs1 -∗
      array_slice t i dq2 vs2 -∗
      ⌜✓ (dq1 ⋅ dq2) ∧ vs1 = vs2⌝.
    Proof.
      iIntros "% % Hslice1 Hslice2".
      iDestruct (array_slice_combine with "Hslice1 Hslice2") as "(<- & Hslice)"; first done.
      iDestruct (array_slice_valid with "Hslice") as %?; done.
    Qed.
    Lemma array_slice_agree t i dq1 vs1 dq2 vs2 :
      length vs1 = length vs2 →
      array_slice t i dq1 vs1 -∗
      array_slice t i dq2 vs2 -∗
      ⌜vs1 = vs2⌝.
    Proof.
      iIntros "% Hslice1 Hslice2".
      iDestruct (array_slice_combine with "Hslice1 Hslice2") as "(% & _)"; done.
    Qed.
    Lemma array_slice_dfrac_ne t1 i1 dq1 vs1 t2 i2 dq2 vs2 :
      0 < length vs1 →
      length vs1 = length vs2 →
      ¬ ✓ (dq1 ⋅ dq2) →
      array_slice t1 i1 dq1 vs1 -∗
      array_slice t2 i2 dq2 vs2 -∗
      ⌜t1 ≠ t2 ∨ i1 ≠ i2⌝.
    Proof.
      rewrite -not_and_r. iIntros "% % % Hslice1 Hslice2" ((-> & ->)).
      iDestruct (array_slice_valid_2 with "Hslice1 Hslice2") as %?; naive_solver.
    Qed.
    Lemma array_slice_ne t1 i1 vs1 t2 i2 dq2 vs2 :
      0 < length vs1 →
      length vs1 = length vs2 →
      array_slice t1 i1 (DfracOwn 1) vs1 -∗
      array_slice t2 i2 dq2 vs2 -∗
      ⌜t1 ≠ t2 ∨ i1 ≠ i2⌝.
    Proof.
      intros.
      iApply array_slice_dfrac_ne; [done.. | intros []%(exclusive_l _)].
    Qed.
    Lemma array_slice_exclusive t i vs1 vs2 :
      0 < length vs1 →
      length vs1 = length vs2 →
      array_slice t i (DfracOwn 1) vs1 -∗
      array_slice t i (DfracOwn 1) vs2 -∗
      False.
    Proof.
      iIntros "% % Hslice1 Hslice2".
      iDestruct (array_slice_valid_2 with "Hslice1 Hslice2") as %?; naive_solver.
    Qed.
    Lemma array_slice_persist t i dq vs :
      array_slice t i dq vs ⊢ |==>
      array_slice t i DfracDiscarded vs.
    Proof.
      iIntros "(%l & -> & Hmodel)".
      iMod (chunk_model_persist with "Hmodel") as "Hmodel".
      iSteps.
    Qed.

    Lemma array_slice_app t i dq vs1 vs2 :
      array_slice t i dq vs1 ∗
      array_slice t (i + length vs1) dq vs2 ⊣⊢
      array_slice t i dq (vs1 ++ vs2).
    Proof.
      iSplit.
      - iIntros "((%l & -> & Hmodel1) & (%_l & %Heq & Hmodel2))". injection Heq as <-.
        rewrite Nat2Z.inj_add -location_add_assoc.
        iDestruct (chunk_model_app_1 with "Hmodel1 Hmodel2") as "Hmodel"; first done.
        iSteps.
      - iIntros "(%l & -> & Hmodel)".
        iDestruct (chunk_model_app with "Hmodel") as "(Hmodel1 & Hmodel2)".
        iSplitL "Hmodel1"; iExists l; first iSteps.
        rewrite location_add_assoc -Nat2Z.inj_add. iSteps.
    Qed.
    Lemma array_slice_app_1 t i dq vs1 vs2 :
      array_slice t i dq vs1 -∗
      array_slice t (i + length vs1) dq vs2 -∗
      array_slice t i dq (vs1 ++ vs2).
    Proof.
      rewrite -array_slice_app. iSteps.
    Qed.
    Lemma array_slice_app_1' {t dq i1 vs1} i2 vs2 :
      i2 = i1 + length vs1 →
      array_slice t i1 dq vs1 -∗
      array_slice t i2 dq vs2 -∗
      array_slice t i1 dq (vs1 ++ vs2).
    Proof.
      intros ->. apply array_slice_app_1.
    Qed.
    Lemma array_slice_app_2 {t i dq vs} vs1 vs2 :
      vs = vs1 ++ vs2 →
      array_slice t i dq vs ⊢
        array_slice t i dq vs1 ∗
        array_slice t (i + length vs1) dq vs2.
    Proof.
      intros ->. rewrite array_slice_app //.
    Qed.

    Lemma array_slice_app3 t i dq vs1 vs2 vs3 :
      array_slice t i dq vs1 ∗
      array_slice t (i + length vs1) dq vs2 ∗
      array_slice t (i + length vs1 + length vs2) dq vs3 ⊣⊢
      array_slice t i dq (vs1 ++ vs2 ++ vs3).
    Proof.
      rewrite !array_slice_app //.
    Qed.
    Lemma array_slice_app3_1 t dq i1 vs1 i2 vs2 i3 vs3 :
      i2 = i1 + length vs1 →
      i3 = i1 + length vs1 + length vs2 →
      array_slice t i1 dq vs1 -∗
      array_slice t i2 dq vs2 -∗
      array_slice t i3 dq vs3 -∗
      array_slice t i1 dq (vs1 ++ vs2 ++ vs3).
    Proof.
      intros -> ->. rewrite -array_slice_app3. iSteps.
    Qed.
    Lemma array_slice_app3_2 {t i dq vs} vs1 vs2 vs3 :
      vs = vs1 ++ vs2 ++ vs3 →
      array_slice t i dq vs ⊢
        array_slice t i dq vs1 ∗
        array_slice t (i + length vs1) dq vs2 ∗
        array_slice t (i + length vs1 + length vs2) dq vs3.
    Proof.
      intros ->. rewrite array_slice_app3 //.
    Qed.

    Lemma array_slice_cons t i dq v vs :
      array_slice t i dq (v :: vs) ⊢
        array_slice t i dq [v] ∗
        array_slice t (S i) dq vs.
    Proof.
      rewrite -Nat.add_1_r (array_slice_app_2 [v] vs) //.
    Qed.

    Lemma array_slice_atomize t i dq vs :
      array_slice t i dq vs ⊢
      [∗ list] j ↦ v ∈ vs,
        array_slice t (i + j) dq [v].
    Proof.
      iInduction vs as [| v vs] "IH" forall (i); first iSteps.
      iIntros "Hvs".
      iDestruct (array_slice_cons with "Hvs") as "(Hv & Hvs)".
      rewrite /= Nat.add_0_r. iFrame.
      iDestruct ("IH" with "Hvs") as "Hvs".
      setoid_rewrite Nat.add_succ_comm. iSteps.
    Qed.

    Lemma array_slice_update {t i dq vs} j v :
      vs !! j = Some v →
      array_slice t i dq vs ⊢
        array_slice t (i + j) dq [v] ∗
        ( ∀ w,
          array_slice t (i + j) dq [w] -∗
          array_slice t i dq (<[j := w]> vs)
        ).
    Proof.
      iIntros "%Hlookup Hslice".
      pose proof Hlookup as Hj%lookup_lt_Some.
      pose proof Hlookup as <-%take_drop_middle.
      iDestruct (array_slice_app3_2 _ [v] with "Hslice") as "(Hslice1 & Hslice2 & Hslice3)"; first done.
      setoid_rewrite insert_app_r_alt; rewrite length_take; last lia.
      rewrite Nat.min_l; first lia. rewrite Nat.sub_diag /=.
      iFrame. iIntros "%w Hslice2".
      iApply (array_slice_app3_1 with "Hslice1 Hslice2 Hslice3"); rewrite length_take /=; lia.
    Qed.
    Lemma array_slice_lookup_acc {t i dq vs} j v :
      vs !! j = Some v →
      array_slice t i dq vs ⊢
        array_slice t (i + j) dq [v] ∗
        ( array_slice t (i + j) dq [v] -∗
          array_slice t i dq vs
        ).
    Proof.
      iIntros "%Hlookup Hslice".
      iDestruct (array_slice_update with "Hslice") as "(Hv & Hslice)"; first done.
      iSpecialize ("Hslice" $! v). rewrite list_insert_id //. iFrame.
    Qed.
    Lemma array_slice_lookup {t i dq vs} j v :
      vs !! j = Some v →
      array_slice t i dq vs ⊢
      array_slice t (i + j) dq [v].
    Proof.
      intros. rewrite array_slice_lookup_acc //. iSteps.
    Qed.
  End array_slice.

  Section array_model.
    Definition array_model t dq vs : iProp Σ :=
      ∃ l,
      ⌜t = #l⌝ ∗
      l ↦ₕ Header 0 (length vs) ∗
      chunk_model l dq vs.

    Lemma array_model_to_inv t dq vs :
      array_model t dq vs ⊢
      array_inv t (length vs).
    Proof.
      iSteps.
    Qed.
    Lemma array_slice_to_model t sz dq vs :
      sz = length vs →
      array_inv t sz -∗
      array_slice t 0 dq vs -∗
      array_model t dq vs.
    Proof.
      iSteps. rewrite location_add_0 //.
    Qed.
    Lemma array_model_to_slice t dq vs :
      array_model t dq vs ⊣⊢
        array_inv t (length vs) ∗
        array_slice t 0 dq vs.
    Proof.
      iSteps; rewrite location_add_0 //.
    Qed.
    Lemma array_model_to_slice' t dq vs :
      array_model t dq vs ⊢
        array_slice t 0 dq vs ∗
        □ (
          ∀ vs',
          ⌜length vs' = length vs⌝ -∗
          array_slice t 0 dq vs' -∗
          array_model t dq vs'
        ).
    Proof.
      setoid_rewrite array_model_to_slice.
      iIntros "(#Hinv & $) !> %vs' %Hvs' $".
      rewrite -Hvs' //.
    Qed.

    #[global] Instance array_model_timeless t dq vs :
      Timeless (array_model t dq vs).
    Proof.
      apply _.
    Qed.
    #[global] Instance array_model_persistent t vs :
      Persistent (array_model t DfracDiscarded vs).
    Proof.
      apply _.
    Qed.

    #[global] Instance array_model_fractional t vs :
      Fractional (λ q, array_model t (DfracOwn q) vs).
    Proof.
      intros q1 q2. iSplit.
      - iIntros "(%l & -> & #Hhdr & Hmodel1 & Hmodel2)". iSteps.
      - iIntros "((%l & -> & #Hhdr & Hmodel1) & (%_l & %Heq & _ & Hmodel2))". injection Heq as <-.
        iExists l. iSteps.
        iApply chunk_model_fractional. iSteps.
    Qed.
    #[global] Instance array_model_as_fractional t q vs :
      AsFractional (array_model t (DfracOwn q) vs) (λ q, array_model t (DfracOwn q) vs) q.
    Proof.
      split; [done | apply _].
    Qed.

    Lemma array_inv_model_agree t sz dq vs :
      array_inv t sz -∗
      array_model t dq vs -∗
      ⌜length vs = sz⌝.
    Proof.
      rewrite array_model_to_inv.
      iIntros "#Hinv1 #Hinv2".
      iDestruct (array_inv_agree with "Hinv1 Hinv2") as %->. done.
    Qed.

    Lemma array_model_valid t dq vs :
      0 < length vs →
      array_model t dq vs ⊢
      ⌜✓ dq⌝.
    Proof.
      iIntros "% (%l & -> & #Hhdr & Hmodel)".
      iApply (chunk_model_valid with "Hmodel"); first done.
    Qed.
    Lemma array_model_combine t dq1 vs1 dq2 vs2 :
      array_model t dq1 vs1 -∗
      array_model t dq2 vs2 -∗
        ⌜vs1 = vs2⌝ ∗
        array_model t (dq1 ⋅ dq2) vs1.
    Proof.
      iIntros "(%l & -> & #Hhdr1 & Hmodel1) (%_l & %Heq & #Hhdr2 & Hmodel2)". injection Heq as <-.
      iDestruct (has_header_agree with "Hhdr1 Hhdr2") as %[= Hlength].
      iDestruct (chunk_model_combine with "Hmodel1 Hmodel2") as "(<- & Hmodel)"; first done.
      iSteps.
    Qed.
    Lemma array_model_valid_2 t dq1 vs1 dq2 vs2 :
      0 < length vs1 →
      array_model t dq1 vs1 -∗
      array_model t dq2 vs2 -∗
      ⌜✓ (dq1 ⋅ dq2) ∧ vs1 = vs2⌝.
    Proof.
      iIntros "% Hmodel1 Hmodel2".
      iDestruct (array_model_combine with "Hmodel1 Hmodel2") as "(-> & Hmodel)".
      iDestruct (array_model_valid with "Hmodel") as %?; done.
    Qed.
    Lemma array_model_agree t dq1 vs1 dq2 vs2 :
      array_model t dq1 vs1 -∗
      array_model t dq2 vs2 -∗
      ⌜vs1 = vs2⌝.
    Proof.
      iIntros "Hmodel1 Hmodel2".
      iDestruct (array_model_combine with "Hmodel1 Hmodel2") as "(-> & _)".
      iSteps.
    Qed.
    Lemma array_model_dfrac_ne t1 dq1 vs1 t2 dq2 vs2 :
      0 < length vs1 →
      ¬ ✓ (dq1 ⋅ dq2) →
      array_model t1 dq1 vs1 -∗
      array_model t2 dq2 vs2 -∗
      ⌜t1 ≠ t2⌝.
    Proof.
      iIntros "% % Hmodel1 Hmodel2" (->).
      iDestruct (array_model_valid_2 with "Hmodel1 Hmodel2") as %?; naive_solver.
    Qed.
    Lemma array_model_ne t1 vs1 t2 dq2 vs2 :
      0 < length vs1 →
      array_model t1 (DfracOwn 1) vs1 -∗
      array_model t2 dq2 vs2 -∗
      ⌜t1 ≠ t2⌝.
    Proof.
      intros. iApply array_model_dfrac_ne; [done.. | intros []%(exclusive_l _)].
    Qed.
    Lemma array_model_exclusive t vs1 vs2 :
      0 < length vs1 →
      array_model t (DfracOwn 1) vs1 -∗
      array_model t (DfracOwn 1) vs2 -∗
      False.
    Proof.
      iIntros "% Hmodel1 Hmodel2".
      iDestruct (array_model_valid_2 with "Hmodel1 Hmodel2") as %?; naive_solver.
    Qed.
    Lemma array_model_persist t dq vs :
      array_model t dq vs ⊢ |==>
      array_model t DfracDiscarded vs.
    Proof.
      iIntros "(%l & -> & #Hhdr & Hmodel)".
      iMod (chunk_model_persist with "Hmodel") as "Hmodel".
      iSteps.
    Qed.

    Lemma array_model_atomize t dq vs :
      array_model t dq vs ⊢
        array_inv t (length vs) ∗
        [∗ list] i ↦ v ∈ vs,
          array_slice t i dq [v].
    Proof.
      rewrite array_model_to_slice array_slice_atomize.
      iSteps.
    Qed.

    #[local] Typeclasses Opaque array_slice.
    Lemma array_model_update {t dq vs} i v :
      vs !! i = Some v →
      array_model t dq vs ⊢
        array_inv t (length vs) ∗
        array_slice t i dq [v] ∗
        ( ∀ w,
          array_slice t i dq [w] -∗
          array_model t dq (<[i := w]> vs)
        ).
    Proof.
      intros.
      setoid_rewrite array_model_to_slice.
      rewrite array_slice_update //.
      iSteps. rewrite length_insert. iSteps.
    Qed.
    Lemma array_model_lookup_acc {t dq vs} i v :
      vs !! i = Some v →
      array_model t dq vs ⊢
        array_slice t i dq [v] ∗
        ( array_slice t i dq [v] -∗
          array_model t dq vs
        ).
    Proof.
      intros.
      rewrite array_model_to_slice {1}array_slice_lookup_acc //.
      iSteps.
    Qed.
    Lemma array_model_lookup {t dq vs} i v :
      vs !! i = Some v →
      array_model t dq vs ⊢
      array_slice t i dq [v].
    Proof.
      intros.
      rewrite array_model_to_slice {1}array_slice_lookup //.
      iSteps.
    Qed.
  End array_model.

  Section array_cslice.
    Definition array_cslice t (sz : nat) i dq vs : iProp Σ :=
      ∃ l,
      ⌜t = #l⌝ ∗
      l ↦ₕ Header 0 sz ∗
      chunk_cslice l sz i dq vs.

    Lemma array_cslice_to_inv t sz i dq vs :
      array_cslice t sz i dq vs ⊢
      array_inv t sz.
    Proof.
      iSteps.
    Qed.
    Lemma array_model_to_cslice t dq vs :
      array_model t dq vs ⊢
      array_cslice t (length vs) 0 dq vs.
    Proof.
      rewrite /array_model /array_slice /array_cslice.
      setoid_rewrite chunk_model_to_cslice. done.
    Qed.

    #[global] Instance array_cslice_timeless t sz i dq vs :
      Timeless (array_cslice t sz i dq vs).
    Proof.
      apply _.
    Qed.
    #[global] Instance array_cslice_persistent t sz i vs :
      Persistent (array_cslice t sz i DfracDiscarded vs).
    Proof.
      apply _.
    Qed.

    #[global] Instance array_cslice_fractional t sz i vs :
      Fractional (λ q, array_cslice t sz i (DfracOwn q) vs).
    Proof.
      intros q1 q2. iSplit.
      - iIntros "(%l & -> & #Hhdr & (Hcslice1 & Hcslice2))".
        iSteps.
      - iIntros "((%l & -> & #Hhdr & Hcslice1) & (%_l & %Heq & _ & Hcslice2))". injection Heq as <-.
        iCombine "Hcslice1 Hcslice2" as "Hcslice".
        iSteps.
    Qed.
    #[global] Instance array_cslice_as_fractionak t sz i q vs :
      AsFractional (array_cslice t sz i (DfracOwn q) vs) (λ q, array_cslice t sz i (DfracOwn q) vs) q.
    Proof.
      split; [done | apply _].
    Qed.

    Lemma array_cslice_nil t sz i dq :
      array_inv t sz ⊢
      array_cslice t sz i dq [].
    Proof.
      iSteps.
      iApply chunk_cslice_nil.
    Qed.

    Lemma array_cslice_app t sz i dq vs1 vs2 :
      array_cslice t sz i dq vs1 ∗
      array_cslice t sz (i + length vs1) dq vs2 ⊣⊢
      array_cslice t sz i dq (vs1 ++ vs2).
    Proof.
      rewrite /array_cslice. setoid_rewrite <- chunk_cslice_app. iSteps.
    Qed.
    Lemma array_cslice_app_1 t sz dq i1 vs1 i2 vs2 :
      i2 = i1 + length vs1 →
      array_cslice t sz i1 dq vs1 -∗
      array_cslice t sz i2 dq vs2 -∗
      array_cslice t sz i1 dq (vs1 ++ vs2).
    Proof.
      rewrite -array_cslice_app. iSteps.
    Qed.
    Lemma array_cslice_app_2 {t sz i dq vs} vs1 vs2 :
      vs = vs1 ++ vs2 →
      array_cslice t sz i dq vs ⊢
        array_cslice t sz i dq vs1 ∗
        array_cslice t sz (i + length vs1) dq vs2.
    Proof.
      rewrite array_cslice_app. iSteps.
    Qed.

    Lemma array_cslice_app3 t sz i dq vs1 vs2 vs3 :
      array_cslice t sz i dq vs1 ∗
      array_cslice t sz (i + length vs1) dq vs2 ∗
      array_cslice t sz (i + length vs1 + length vs2) dq vs3 ⊣⊢
      array_cslice t sz i dq (vs1 ++ vs2 ++ vs3).
    Proof.
      rewrite !array_cslice_app //.
    Qed.
    Lemma array_cslice_app3_1 t sz dq i1 vs1 i2 vs2 i3 vs3 :
      i2 = i1 + length vs1 →
      i3 = i1 + length vs1 + length vs2 →
      array_cslice t sz i1 dq vs1 -∗
      array_cslice t sz i2 dq vs2 -∗
      array_cslice t sz i3 dq vs3 -∗
      array_cslice t sz i1 dq (vs1 ++ vs2 ++ vs3).
    Proof.
      intros -> ->. rewrite -array_cslice_app3. iSteps.
    Qed.
    Lemma array_cslice_app3_2 {t sz i dq vs} vs1 vs2 vs3 :
      vs = vs1 ++ vs2 ++ vs3 →
      array_cslice t sz i dq vs ⊢
        array_cslice t sz i dq vs1 ∗
        array_cslice t sz (i + length vs1) dq vs2 ∗
        array_cslice t sz (i + length vs1 + length vs2) dq vs3.
    Proof.
      intros ->. rewrite array_cslice_app3 //.
    Qed.

    Lemma array_cslice_cons t sz i dq v vs :
      array_cslice t sz i dq (v :: vs) ⊢
        array_cslice t sz i dq [v] ∗
        array_cslice t sz (S i) dq vs.
    Proof.
      rewrite -Nat.add_1_r (array_cslice_app_2 [v] vs) //.
    Qed.

    Lemma array_cslice_atomize sz t i dq vs :
      array_cslice t sz i dq vs ⊢
      [∗ list] j ↦ v ∈ vs,
        array_cslice t sz (i + j) dq [v].
    Proof.
      iInduction vs as [| v vs] "IH" forall (i); first iSteps.
      iIntros "Hvs".
      iDestruct (array_cslice_cons with "Hvs") as "(Hv & Hvs)".
      rewrite /= Nat.add_0_r. iFrame.
      iDestruct ("IH" with "Hvs") as "Hvs".
      setoid_rewrite Nat.add_succ_comm. iSteps.
    Qed.

    Lemma array_cslice_update {t sz i dq vs} j v :
      vs !! j = Some v →
      array_cslice t sz i dq vs ⊢
        array_cslice t sz (i + j) dq [v] ∗
        ( ∀ w,
          array_cslice t sz (i + j) dq [w] -∗
          array_cslice t sz i dq (<[j := w]> vs)
        ).
    Proof.
      intros.
      rewrite /array_cslice.
      setoid_rewrite <- chunk_cslice_singleton.
      setoid_rewrite chunk_cslice_update at 1; last done.
      iSteps.
    Qed.
    Lemma array_cslice_lookup_acc {t sz i dq vs} j v :
      vs !! j = Some v →
      array_cslice t sz i dq vs ⊢
        array_cslice t sz (i + j) dq [v] ∗
        ( array_cslice t sz (i + j) dq [v] -∗
          array_cslice t sz i dq vs
        ).
    Proof.
      iIntros "%Hlookup Hslice".
      iDestruct (array_cslice_update with "Hslice") as "(Hv & Hslice)"; first done.
      iSpecialize ("Hslice" $! v). rewrite list_insert_id //. iFrame.
    Qed.
    Lemma array_cslice_lookup {t sz i dq vs} j v :
      vs !! j = Some v →
      array_cslice t sz i dq vs ⊢
      array_cslice t sz (i + j) dq [v].
    Proof.
      intros. rewrite array_cslice_lookup_acc //. iSteps.
    Qed.

    Lemma array_cslice_shift t sz i dq vs :
      array_cslice t sz i dq vs ⊢
      array_cslice t sz (i + sz) dq vs.
    Proof.
      rewrite /array_cslice.
      setoid_rewrite chunk_cslice_shift at 1.
      done.
    Qed.

    Lemma array_cslice_valid t sz i dq vs :
      0 < length vs →
      array_cslice t sz i dq vs ⊢
      ⌜✓ dq⌝.
    Proof.
      intros.
      rewrite /array_cslice.
      setoid_rewrite chunk_cslice_valid; last done.
      iSteps.
    Qed.
    Lemma array_cslice_combine t sz i dq1 vs1 dq2 vs2 :
      length vs1 = length vs2 →
      array_cslice t sz i dq1 vs1 -∗
      array_cslice t sz i dq2 vs2 -∗
        ⌜vs1 = vs2⌝ ∗
        array_cslice t sz i (dq1 ⋅ dq2) vs1.
    Proof.
      iIntros "% (%l & -> & #Hhdr & Hcslice1) (%_l & %Heq & _ & Hcslice2)". injection Heq as <-.
      iDestruct (chunk_cslice_combine with "Hcslice1 Hcslice2") as "($ & Hcslice)"; first done.
      iSteps.
    Qed.
    Lemma array_cslice_valid_2 t sz i dq1 vs1 dq2 vs2 :
      0 < length vs1 →
      length vs1 = length vs2 →
      array_cslice t sz i dq1 vs1 -∗
      array_cslice t sz i dq2 vs2 -∗
      ⌜✓ (dq1 ⋅ dq2) ∧ vs1 = vs2⌝.
    Proof.
      iIntros "% % Hcslice1 Hcslice2".
      iDestruct (array_cslice_combine with "Hcslice1 Hcslice2") as "(-> & Hcslice)"; first done.
      iDestruct (array_cslice_valid with "Hcslice") as %?; first done.
      iSteps.
    Qed.
    Lemma array_cslice_agree t sz i dq1 vs1 dq2 vs2 :
      length vs1 = length vs2 →
      array_cslice t sz i dq1 vs1 -∗
      array_cslice t sz i dq2 vs2 -∗
      ⌜vs1 = vs2⌝.
    Proof.
      iIntros "% Hcslice1 Hcslice2".
      iDestruct (array_cslice_combine with "Hcslice1 Hcslice2") as "(-> & _)"; first done.
      iSteps.
    Qed.
    Lemma array_cslice_dfrac_ne t sz i1 dq1 vs1 i2 dq2 vs2 :
      0 < length vs1 →
      length vs1 = length vs2 →
      ¬ ✓ (dq1 ⋅ dq2) →
      array_cslice t sz i1 dq1 vs1 -∗
      array_cslice t sz i2 dq2 vs2 -∗
      ⌜i1 ≠ i2⌝.
    Proof.
      iIntros "% % % Hcslice1 Hcslice2" (->).
      iDestruct (array_cslice_valid_2 with "Hcslice1 Hcslice2") as %?; naive_solver.
    Qed.
    Lemma array_cslice_ne t sz i1 vs1 i2 dq2 vs2 :
      0 < length vs1 →
      length vs1 = length vs2 →
      array_cslice t sz i1 (DfracOwn 1) vs1 -∗
      array_cslice t sz i2 dq2 vs2 -∗
      ⌜i1 ≠ i2⌝.
    Proof.
      intros.
      iApply array_cslice_dfrac_ne; [done.. | intros []%(exclusive_l _)].
    Qed.
    Lemma array_cslice_exclusive t sz i vs1 vs2 :
      0 < length vs1 →
      length vs1 = length vs2 →
      array_cslice t sz i (DfracOwn 1) vs1 -∗
      array_cslice t sz i (DfracOwn 1) vs2 -∗
      False.
    Proof.
      iIntros "% % Hcslice1 Hcslice2".
      iDestruct (array_cslice_valid_2 with "Hcslice1 Hcslice2") as %?; naive_solver.
    Qed.
    Lemma array_cslice_persist t sz i dq vs :
      array_cslice t sz i dq vs ⊢ |==>
      array_cslice t sz i DfracDiscarded vs.
    Proof.
      rewrite /array_cslice.
      setoid_rewrite chunk_cslice_persist at 1.
      iSteps.
    Qed.
  End array_cslice.

  #[local] Typeclasses Opaque
    array_inv
    array_slice
    array_model
    array_cslice.

  Notation au_load t i Φ := (
    AU <{
      ∃∃ dq v,
      array_slice t i dq [v]
    }> @ ⊤, ∅ <{
      array_slice t i dq [v],
    COMM
      Φ v
    }>
  )%I.
  Notation au_store t i v P := (
    AU <{
      ∃∃ w,
      array_slice t i (DfracOwn 1) [w]
    }> @ ⊤, ∅ <{
      array_slice t i (DfracOwn 1) [v],
    COMM
      P
    }>
  )%I.

  Notation au_cload t sz i Φ := (
    AU <{
      ∃∃ dq v,
      array_cslice t sz i dq [v]
    }> @ ⊤, ∅ <{
      array_cslice t sz i dq [v],
    COMM
      Φ v
    }>
  )%I.
  Notation au_cstore t sz i v P := (
    AU <{
      ∃∃ w,
      array_cslice t sz i (DfracOwn 1) [w]
    }> @ ⊤, ∅ <{
      array_cslice t sz i (DfracOwn 1) [v],
    COMM
      P
    }>
  )%I.

  Lemma array_unsafe_alloc_spec sz :
    (0 ≤ sz)%Z →
    {{{
      True
    }}}
      array_unsafe_alloc #sz
    {{{ t,
      RET t;
      array_model t (DfracOwn 1) (replicate (Z.to_nat sz) ()%V)
    }}}.
  Proof.
    rewrite /array_model /array_slice.
    iIntros "%Hsz %Φ _ HΦ".
    wp_rec.
    wp_alloc l as "#Hhdr" "_" "Hl"; [done.. |].
    iSteps. rewrite length_replicate. iSteps.
  Qed.

  Lemma array_alloc_spec sz :
    {{{
      True
    }}}
      array_alloc #sz
    {{{ t,
      RET t;
      ⌜0 ≤ sz⌝%Z ∗
      array_model t (DfracOwn 1) (replicate (Z.to_nat sz) ()%V)
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_rec.
    wp_smart_apply assume_spec' as "%Hsz".
    wp_smart_apply (array_unsafe_alloc_spec with "[//]"); first done.
    iSteps.
  Qed.

  Lemma array_create_spec :
    {{{
      True
    }}}
      array_create ()
    {{{ t,
      RET t;
      array_model t (DfracOwn 1) []
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_rec.
    wp_apply (array_unsafe_alloc_spec with "[//]"); first done.
    iSteps.
  Qed.

  Lemma array_size_spec_inv t sz :
    {{{
      array_inv t sz
    }}}
      array_size t
    {{{
      RET #sz;
      True
    }}}.
  Proof.
    rewrite /array_inv.
    iSteps.
  Qed.
  Lemma array_size_spec_atomic t :
    <<<
      True
    | ∀∀ dq vs,
      array_model t dq vs
    >>>
      array_size t
    <<<
      array_model t dq vs
    | RET #(length vs);
      £ 1
    >>>.
  Proof.
    rewrite /array_model.
    iIntros "!> %Φ _ HΦ".
    wp_rec credit:"H£".
    iMod "HΦ" as "(%dq & %vs & (%l & -> & #Hhdr & Hmodel) & _ & HΦ)".
    wp_get_size.
    iApply ("HΦ" with "[Hmodel] H£").
    iSteps.
  Qed.
  Lemma array_size_spec_atomic_cslice t :
    <<<
      True
    | ∀∀ sz i dq vs,
      array_cslice t sz i dq vs
    >>>
      array_size t
    <<<
      array_cslice t sz i dq vs
    | RET #sz;
      £ 1
    >>>.
  Proof.
    rewrite /array_cslice.
    iIntros "!> %Φ _ HΦ".
    wp_rec credit:"H£".
    iMod "HΦ" as "(%sz & %i & %dq & %vs & (%l & -> & #Hhdr & Hcslice) & _ & HΦ)".
    wp_get_size.
    iApply ("HΦ" with "[Hcslice] H£").
    iSteps.
  Qed.
  Lemma array_size_spec t dq vs :
    {{{
      array_model t dq vs
    }}}
      array_size t
    {{{
      RET #(length vs);
      array_model t dq vs
    }}}.
  Proof.
    rewrite /array_model. iSteps.
  Qed.
  Lemma array_size_spec_cslice t sz i dq vs :
    {{{
      array_cslice t sz i dq vs
    }}}
      array_size t
    {{{
      RET #sz;
      array_cslice t sz i dq vs
    }}}.
  Proof.
    rewrite /array_cslice. iSteps.
  Qed.

  Lemma array_unsafe_get_spec_atomic_slice t (j : Z) :
    <<<
      True
    | ∀∀ dq vs i v,
      ⌜(i ≤ j)%Z⌝ ∗
      ⌜vs !! (Z.to_nat j - i) = Some v⌝ ∗
      array_slice t i dq vs
    >>>
      array_unsafe_get t #j
    <<<
      array_slice t i dq vs
    | RET v;
      £ 1
    >>>.
  Proof.
    rewrite /array_slice.
    iIntros "!> %Φ _ HΦ".
    wp_rec credit:"H£". wp_pures.
    iMod "HΦ" as "(%dq & %vs & %i & %v & (%Hi & %Hlookup & (%l & -> & Hmodel)) & _ & HΦ)".
    iDestruct (chunk_model_lookup_acc' j with "Hmodel") as "(H↦ & Hmodel)"; [lia | done | lia |].
    wp_load.
    iApply ("HΦ" with "[H↦ Hmodel] H£").
    iSteps.
  Qed.
  Lemma array_unsafe_get_spec_atomic_cell t (i : Z) :
    <<<
      True
    | ∀∀ i_ dq v,
      ⌜i = Z.of_nat i_⌝ ∗
      array_slice t i_ dq [v]
    >>>
      array_unsafe_get t #i
    <<<
      array_slice t (Z.to_nat i) dq [v]
    | RET v;
      £ 1
    >>>.
  Proof.
    iIntros "!> %Φ _ HΦ".
    awp_apply (array_unsafe_get_spec_atomic_slice with "[//]").
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%i_ %dq %v (-> & Hslice)".
    rewrite /atomic_acc /= Nat2Z.id.
    iExists dq, [v], i_, v. rewrite Nat.sub_diag. iSteps.
  Qed.
  Lemma array_unsafe_get_spec_atomic t (i : Z) :
    (0 ≤ i)%Z →
    <<<
      True
    | ∀∀ dq vs v,
      ⌜vs !! Z.to_nat i = Some v⌝ ∗
      array_model t dq vs
    >>>
      array_unsafe_get t #i
    <<<
      array_model t dq vs
    | RET v;
      £ 1
    >>>.
  Proof.
    iIntros "%Hi !> %Φ _ HΦ".
    awp_apply (array_unsafe_get_spec_atomic_slice with "[//]").
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%dq %vs %v (%Hlookup & Hmodel)".
    iDestruct (array_model_to_slice' with "Hmodel") as "(Hslice & #?)".
    rewrite /atomic_acc /=.
    iExists dq, vs, 0, v. rewrite Nat.sub_0_r. iSteps.
  Qed.
  Lemma array_unsafe_get_spec_slice k t i dq vs (j : Z) v :
    (i ≤ j)%Z →
    vs !! k = Some v →
    k = Z.to_nat j - i →
    {{{
      array_slice t i dq vs
    }}}
      array_unsafe_get t #j
    {{{
      RET v;
      array_slice t i dq vs
    }}}.
  Proof.
    iIntros (Hj Hlookup ->) "%Φ Hslice HΦ".
    iApply wp_fupd.
    awp_apply (array_unsafe_get_spec_atomic_slice with "[//]") without "HΦ".
    rewrite /atomic_acc /=.
    iExists dq, vs, i, v.
    iApply fupd_mask_intro; first done. iIntros "Hclose".
    iSplitL "Hslice"; first auto. iSplit; first iSteps.
    iIntros "Hslice". iMod "Hclose" as "_". iIntros "!> H£ HΦ".
    iMod (lc_fupd_elim_later with "H£ HΦ") as "HΦ".
    iSteps.
  Qed.
  Lemma array_unsafe_get_spec_cell t (i : Z) i_ dq v :
    i = Z.to_nat i_ →
    {{{
      array_slice t i_ dq [v]
    }}}
      array_unsafe_get t #i
    {{{
      RET v;
      array_slice t i_ dq [v]
    }}}.
  Proof.
    intros.
    eapply (array_unsafe_get_spec_slice 0); [lia | done | lia].
  Qed.
  Lemma array_unsafe_get_spec i_ t (i : Z) dq vs v :
    (0 ≤ i)%Z →
    vs !! i_ = Some v →
    i_ = Z.to_nat i →
    {{{
      array_model t dq vs
    }}}
      array_unsafe_get t #i
    {{{
      RET v;
      array_model t dq vs
    }}}.
  Proof.
    setoid_rewrite array_model_to_slice' at 1.
    iIntros (Hi Hlookup ->) "%Φ (Hslice & #?) HΦ".
    wp_apply (array_unsafe_get_spec_slice with "Hslice"); [done.. | lia |].
    iSteps.
  Qed.

  Lemma array_get_spec_atomic_slice t sz (j : Z) :
    <<<
      array_inv t sz
    | ∀∀ dq vs i v,
      ⌜0 ≤ j < sz⌝%Z -∗
        ⌜i ≤ Z.to_nat j⌝ ∗
        ⌜vs !! (Z.to_nat j - i) = Some v⌝ ∗
        array_slice t i dq vs
    >>>
      array_get t #j
    <<<
      array_slice t i dq vs
    | RET v;
      ⌜0 ≤ j < sz⌝%Z ∗
      £ 1
    >>>.
  Proof.
    iIntros "!> %Φ #Hinv HΦ".
    wp_rec.
    wp_smart_apply assume_spec' as "%Hj1".
    wp_smart_apply (array_size_spec_inv with "Hinv") as "_".
    wp_smart_apply assume_spec' as "%Hj2".
    awp_smart_apply (array_unsafe_get_spec_atomic_slice with "[//]").
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%dq %vs %i %v H".
    iDestruct ("H" with "[//]") as "(%Hj3 & %Hlookup & Hslice)".
    rewrite /atomic_acc /=.
    repeat iExists _. iFrame. iSplitL; first iSteps. iSplitL; last iSteps. iIntros "!> (_ & _ & Hslice)". iSplitL; iSteps.
  Qed.
  Lemma array_get_spec_atomic_cell t sz (i : Z) i_ :
    i_ = Z.to_nat i →
    <<<
      array_inv t sz
    | ∀∀ dq v,
      ⌜0 ≤ i < sz⌝%Z -∗
      array_slice t i_ dq [v]
    >>>
      array_get t #i
    <<<
      array_slice t i_ dq [v]
    | RET v;
      ⌜0 ≤ i < sz⌝%Z ∗
      £ 1
    >>>.
  Proof.
    iIntros (->) "!> %Φ #Hinv HΦ".
    awp_apply (array_get_spec_atomic_slice with "Hinv").
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%dq %v H".
    rewrite /atomic_acc /=.
    iExists dq, [v], (Z.to_nat i), v. rewrite Nat.sub_diag. iSplitL; first iSteps. iSplitR; last iSteps. iIntros "!> H". iSplitL; iSteps.
  Qed.
  Lemma array_get_spec_atomic t sz (i : Z) :
    <<<
      array_inv t sz
    | ∀∀ dq vs v,
      ⌜0 ≤ i < sz⌝%Z -∗
        ⌜vs !! Z.to_nat i = Some v⌝ ∗
        array_model t dq vs
    >>>
      array_get t #i
    <<<
      array_model t dq vs
    | RET v;
      ⌜0 ≤ i < sz⌝%Z ∗
      £ 1
    >>>.
  Proof.
    iIntros "!> %Φ #Hinv HΦ".
    wp_rec.
    wp_smart_apply assume_spec' as "%Hi1".
    wp_smart_apply (array_size_spec_inv with "Hinv") as "_".
    wp_smart_apply assume_spec' as "%Hi2".
    awp_smart_apply (array_unsafe_get_spec_atomic with "[//]"); first done.
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%dq %vs %v H".
    iDestruct ("H" with "[//]") as "(%Hlookup & Hmodel)".
    rewrite /atomic_acc /=.
    repeat iExists _. iFrame. iSplitL; first iSteps. iSplitR; last iSteps. iIntros "!> H". iSplitL; iSteps.
  Qed.
  Lemma array_get_spec_slice k t sz i dq vs (j : Z) v :
    {{{
      array_inv t sz ∗
      ( ⌜0 ≤ j < sz⌝%Z -∗
          ⌜i ≤ Z.to_nat j⌝ ∗
          ⌜vs !! k = Some v⌝ ∗
          ⌜k = Z.to_nat j - i⌝ ∗
          array_slice t i dq vs
      )
    }}}
      array_get t #j
    {{{
      RET v;
      ⌜0 ≤ j < sz⌝%Z ∗
      array_slice t i dq vs
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & H) HΦ".
    wp_rec.
    wp_smart_apply assume_spec' as "%Hj1".
    wp_smart_apply (array_size_spec_inv with "Hinv") as "_".
    wp_smart_apply assume_spec' as "%Hj2".
    iDestruct ("H" with "[//]") as "(%Hj3 & %Hlookupk & -> & Hslice)".
    wp_smart_apply (array_unsafe_get_spec_slice with "Hslice"); [lia | done.. |].
    iSteps.
  Qed.
  Lemma array_get_spec_cell t sz (i : Z) i_ dq v :
    i_ = Z.to_nat i →
    {{{
      array_inv t sz ∗
      ( ⌜0 ≤ i < sz⌝%Z -∗
        array_slice t i_ dq [v]
      )
    }}}
      array_get t #i
    {{{
      RET v;
      ⌜0 ≤ i < sz⌝%Z ∗
      array_slice t i_ dq [v]
    }}}.
  Proof.
    iIntros (->) "%Φ (#Hinv & H) HΦ".
    wp_apply (array_get_spec_slice 0 with "[$Hinv H] HΦ").
    iSteps.
  Qed.
  Lemma array_get_spec t (i : Z) dq vs v :
    {{{
      array_model t dq vs ∗
      ( ⌜0 ≤ i < length vs⌝%Z -∗
        ⌜vs !! Z.to_nat i = Some v⌝
      )
    }}}
      array_get t #i
    {{{
      RET v;
      ⌜0 ≤ i < length vs⌝%Z ∗
      array_model t dq vs
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & H) HΦ".
    wp_rec.
    wp_smart_apply assume_spec' as "%Hi1".
    wp_smart_apply (array_size_spec with "Hmodel") as "Hmodel".
    wp_smart_apply assume_spec' as "%Hi2".
    iDestruct ("H" with "[//]") as "%Hlookup".
    wp_smart_apply (array_unsafe_get_spec with "Hmodel"); [done.. |].
    iSteps.
  Qed.

  Lemma array_unsafe_set_spec_atomic_slice t (j : Z) v :
    <<<
      True
    | ∀∀ vs i,
      ⌜i ≤ j < i + length vs⌝%Z ∗
      array_slice t i (DfracOwn 1) vs
    >>>
      array_unsafe_set t #j v
    <<<
      array_slice t i (DfracOwn 1) (<[Z.to_nat j - i := v]> vs)
    | RET ();
      £ 1
    >>>.
  Proof.
    rewrite /array_model /array_slice.
    iIntros "!> %Φ _ HΦ".
    wp_rec credit:"H£". wp_pures.
    iMod "HΦ" as "(%vs & %i & (%Hj & (%l & -> & Hmodel)) & _ & HΦ)".
    iDestruct (chunk_model_update' j with "Hmodel") as "(H↦ & Hmodel)"; [lia | | done |].
    { destruct (nth_lookup_or_length vs (Z.to_nat j - Z.to_nat i) inhabitant); [done | lia]. }
    wp_store.
    iApply ("HΦ" with "[H↦ Hmodel] [H£]"); last iSteps.
    rewrite Nat2Z.id. iSteps.
  Qed.
  Lemma array_unsafe_set_spec_atomic_cell t (i : Z) v :
    <<<
      True
    | ∀∀ i_ w,
      ⌜i = Z.of_nat i_⌝ ∗
      array_slice t i_ (DfracOwn 1) [w]
    >>>
      array_unsafe_set t #i v
    <<<
      array_slice t i_ (DfracOwn 1) [v]
    | RET ();
      £ 1
    >>>.
  Proof.
    iIntros "!> %Φ _ HΦ".
    awp_apply (array_unsafe_set_spec_atomic_slice with "[//]").
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%i_ %w (-> & Hslice)".
    rewrite /atomic_acc /= Nat2Z.id.
    iExists [w], i_. rewrite Nat.sub_diag. iSteps.
  Qed.
  Lemma array_unsafe_set_spec_atomic t (i : Z) v :
    (0 ≤ i)%Z →
    <<<
      True
    | ∀∀ vs,
      ⌜i < length vs⌝%Z ∗
      array_model t (DfracOwn 1) vs
    >>>
      array_unsafe_set t #i v
    <<<
      array_model t (DfracOwn 1) (<[Z.to_nat i := v]> vs)
    | RET ();
      £ 1
    >>>.
  Proof.
    iIntros "%Hi !> %Φ _ HΦ".
    awp_apply (array_unsafe_set_spec_atomic_slice with "[//]").
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs (%Hlookup & Hmodel)".
    iDestruct (array_model_to_slice' with "Hmodel") as "(Hslice & #?)".
    rewrite /atomic_acc /=.
    iExists vs, 0. rewrite Nat.sub_0_r. iSteps. rewrite length_insert //.
  Qed.
  Lemma array_unsafe_set_spec_slice t i vs (j : Z) v :
    (i ≤ j < i + length vs)%Z →
    {{{
      array_slice t i (DfracOwn 1) vs
    }}}
      array_unsafe_set t #j v
    {{{
      RET ();
      array_slice t i (DfracOwn 1) (<[Z.to_nat j - i := v]> vs)
    }}}.
  Proof.
    iIntros "%Hj %Φ Hslice HΦ".
    iApply wp_fupd.
    awp_apply (array_unsafe_set_spec_atomic_slice with "[//]") without "HΦ".
    rewrite /atomic_acc /=.
    iExists vs, i.
    iApply fupd_mask_intro; first done. iIntros "Hclose".
    iSplitL "Hslice"; first auto. iSplit; first iSteps.
    iIntros "Hslice". iMod "Hclose" as "_". iIntros "!> H£ HΦ".
    iMod (lc_fupd_elim_later with "H£ HΦ") as "HΦ".
    iSteps.
  Qed.
  Lemma array_unsafe_set_spec_cell t (i : Z) i_ w v :
    i = Z.of_nat i_ →
    {{{
      array_slice t i_ (DfracOwn 1) [w]
    }}}
      array_unsafe_set t #i v
    {{{
      RET ();
      array_slice t i_ (DfracOwn 1) [v]
    }}}.
  Proof.
    iIntros (->) "%Φ Hslice HΦ".
    wp_apply (array_unsafe_set_spec_slice with "Hslice").
    { simpl. lia. }
    rewrite Nat2Z.id Nat.sub_diag //.
  Qed.
  Lemma array_unsafe_set_spec t (i : Z) vs v :
    (0 ≤ i < length vs)%Z →
    {{{
      array_model t (DfracOwn 1) vs
    }}}
      array_unsafe_set t #i v
    {{{
      RET ();
      array_model t (DfracOwn 1) (<[Z.to_nat i := v]> vs)
    }}}.
  Proof.
    setoid_rewrite array_model_to_slice' at 1.
    iIntros "%Hi %Φ (Hslice & #?) HΦ".
    wp_apply (array_unsafe_set_spec_slice with "Hslice"); [done.. | lia |].
    iSteps.
    - rewrite length_insert //.
    - rewrite Nat.sub_0_r //.
  Qed.

  Lemma array_set_spec_atomic_slice t sz (j : Z) v :
    <<<
      array_inv t sz
    | ∀∀ vs i,
      ⌜0 ≤ j < sz⌝%Z -∗
        ⌜i ≤ Z.to_nat j < i + length vs⌝ ∗
        array_slice t i (DfracOwn 1) vs
    >>>
      array_set t #j v
    <<<
      array_slice t i (DfracOwn 1) (<[Z.to_nat j - i := v]> vs)
    | RET ();
      ⌜0 ≤ j < sz⌝%Z ∗
      £ 1
    >>>.
  Proof.
    iIntros "!> %Φ #Hinv HΦ".
    wp_rec.
    wp_smart_apply assume_spec' as "%Hj1".
    wp_smart_apply (array_size_spec_inv with "Hinv") as "_".
    wp_smart_apply assume_spec' as "%Hj2".
    awp_smart_apply (array_unsafe_set_spec_atomic_slice with "[//]").
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs %i H".
    iDestruct ("H" with "[//]") as "(%Hj3 & Hslice)".
    rewrite /atomic_acc /=.
    repeat iExists _. iFrame. iSplitL; first iSteps. iSplitL; last iSteps. iIntros "!> (_ & Hslice)". iSplitL; iSteps.
  Qed.
  Lemma array_set_spec_atomic_cell t sz (i : Z) i_ v :
    i_ = Z.to_nat i →
    <<<
      array_inv t sz
    | ∀∀ w,
      ⌜0 ≤ i < sz⌝%Z -∗
      array_slice t i_ (DfracOwn 1) [w]
    >>>
      array_set t #i v
    <<<
      array_slice t i_ (DfracOwn 1) [v]
    | RET ();
      ⌜0 ≤ i < sz⌝%Z ∗
      £ 1
    >>>.
  Proof.
    iIntros (->) "!> %Φ #Hinv HΦ".
    awp_apply (array_set_spec_atomic_slice with "Hinv").
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%w Hslice".
    rewrite /atomic_acc /=.
    iExists [w], (Z.to_nat i). rewrite Nat.sub_diag. iSplitL; first iSteps. iSplitR; last iSteps. iIntros "!> H". iSplitL; iSteps.
  Qed.
  Lemma array_set_spec_atomic t sz (i : Z) v :
    <<<
      array_inv t sz
    | ∀∀ vs,
      ⌜0 ≤ i < sz⌝%Z -∗
        ⌜(Z.to_nat i < length vs)%Z⌝ ∗
        array_model t (DfracOwn 1) vs
    >>>
      array_set t #i v
    <<<
      array_model t (DfracOwn 1) (<[Z.to_nat i := v]> vs)
    | RET ();
      ⌜0 ≤ i < sz⌝%Z ∗
      £ 1
    >>>.
  Proof.
    iIntros "!> %Φ #Hinv HΦ".
    wp_rec.
    wp_smart_apply assume_spec' as "%Hi1".
    wp_smart_apply (array_size_spec_inv with "Hinv") as "_".
    wp_smart_apply assume_spec' as "%Hi2".
    awp_smart_apply (array_unsafe_set_spec_atomic with "[//]"); first done.
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs H".
    iDestruct ("H" with "[//]") as "(%Hi3 & Hmodel)".
    rewrite /atomic_acc /=.
    repeat iExists _. iFrame. iSplitL; first iSteps. iSplitR; last iSteps. iIntros "!> H". iSplitL; iSteps.
  Qed.
  Lemma array_set_spec_slice t sz i vs (j : Z) v :
    {{{
      array_inv t sz ∗
      ( ⌜0 ≤ j < sz⌝%Z -∗
          ⌜i ≤ Z.to_nat j < i + length vs⌝ ∗
          array_slice t i (DfracOwn 1) vs
      )
    }}}
      array_set t #j v
    {{{
      RET ();
      ⌜0 ≤ j < sz⌝%Z ∗
      array_slice t i (DfracOwn 1) (<[Z.to_nat j - i := v]> vs)
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & H) HΦ".
    wp_rec.
    wp_smart_apply assume_spec' as "%Hj1".
    wp_smart_apply (array_size_spec_inv with "Hinv") as "_".
    wp_smart_apply assume_spec' as "%Hj2".
    iDestruct ("H" with "[//]") as "(%Hi3 & Hslice)".
    wp_smart_apply (array_unsafe_set_spec_slice with "Hslice"); first lia.
    iSteps.
  Qed.
  Lemma array_set_spec_cell t sz (i : Z) i_ w v :
    i_ = Z.to_nat i →
    {{{
      array_inv t sz ∗
      ( ⌜0 ≤ i < sz⌝%Z -∗
        array_slice t i_ (DfracOwn 1) [w]
      )
    }}}
      array_set t #i v
    {{{
      RET ();
      ⌜0 ≤ i < sz⌝%Z ∗
      array_slice t i_ (DfracOwn 1) [v]
    }}}.
  Proof.
    iIntros (->) "%Φ (#Hinv & H) HΦ".
    wp_apply (array_set_spec_slice _ _ (Z.to_nat i) [_] with "[$Hinv H]"); first iSteps.
    rewrite Nat.sub_diag //.
  Qed.
  Lemma array_set_spec t (i : Z) vs v :
    {{{
      array_model t (DfracOwn 1) vs
    }}}
      array_set t #i v
    {{{
      RET ();
      array_model t (DfracOwn 1) (<[Z.to_nat i := v]> vs)
    }}}.
  Proof.
    iIntros "%Φ Hmodel HΦ".
    wp_rec.
    wp_smart_apply assume_spec' as "%Hi1".
    wp_smart_apply (array_size_spec with "Hmodel") as "Hmodel".
    wp_smart_apply assume_spec' as "%Hi2".
    wp_smart_apply (array_unsafe_set_spec with "Hmodel HΦ"); first done.
  Qed.

  Lemma array_unsafe_fill_slice_spec_atomic Ψ t (i n : Z) v :
    (0 ≤ i)%Z →
    (0 ≤ n)%Z →
    {{{
      ▷ Ψ 0 ∗
      □ (
        ∀ j,
        ⌜j < Z.to_nat n⌝ -∗
        Ψ j -∗
        au_store t (Z.to_nat i + j) v (
          ▷ Ψ (S j)
        )
      )
    }}}
      array_unsafe_fill_slice t #i #n v
    {{{
      RET ();
      Ψ (Z.to_nat n)
    }}}.
  Proof.
    iIntros "%Hi %Hn %Φ (HΨ & #H) HΦ".
    wp_rec.
    pose Ψ' (_ : Z) i :=
      Ψ i.
    wp_smart_apply (for_spec_strong Ψ' with "[$HΨ]"); last rewrite Z.sub_0_r //.
    iIntros "!> %j_ %j -> %Hj HΨ". rewrite Z.add_0_l in Hj |- *.
    iDestruct ("H" with "[%] HΨ") as "H'"; first lia.
    awp_smart_apply (array_unsafe_set_spec_atomic_cell with "[//]").
    iApply (aacc_aupd_commit with "H'"); first done. iIntros "%w H↦".
    rewrite /atomic_acc /=.
    repeat iExists _. iFrame. iSteps.
  Qed.
  Lemma array_unsafe_fill_slice_spec t vs (i : Z) i_ (n : Z) v :
    i = Z.of_nat i_ →
    n = length vs →
    {{{
      array_slice t i_ (DfracOwn 1) vs
    }}}
      array_unsafe_fill_slice t #i #n v
    {{{
      RET ();
      array_slice t i_ (DfracOwn 1) (replicate (Z.to_nat n) v)
    }}}.
  Proof.
    iIntros (-> ->) "%Φ Hslice HΦ".
    pose Ψ j :=
      array_slice t i_ (DfracOwn 1) (replicate j v ++ drop j vs).
    wp_apply (array_unsafe_fill_slice_spec_atomic Ψ with "[$Hslice]"); [lia.. | |]; last first.
    { rewrite /Ψ skipn_all2; first lia. rewrite right_id //. }
    iIntros "!> %j %Hj Hslice". rewrite Nat2Z.id.
    opose proof* (list_lookup_lookup_total_lt vs j) as Hlookup; first lia.
    iDestruct (array_slice_update j with "Hslice") as "(H↦ & Hslice)".
    { rewrite lookup_app_r length_replicate // lookup_drop Nat.sub_diag right_id //. }
    iAuIntro. iAaccIntro with "H↦"; first auto with iFrame. iIntros "H↦".
    iDestruct ("Hslice" with "H↦") as "Hslice".
    rewrite /Ψ replicate_S_end -assoc insert_app_r_alt length_replicate // Nat.sub_diag.
    erewrite drop_S => //.
  Qed.

  Lemma array_fill_slice_spec t sz vs (i : Z) i_ (n : Z) v :
    i_ = Z.to_nat i →
    Z.to_nat n = length vs →
    {{{
      array_inv t sz ∗
      array_slice t i_ (DfracOwn 1) vs
    }}}
      array_fill_slice t #i #n v
    {{{
      RET ();
      ⌜0 ≤ i⌝%Z ∗
      ⌜0 ≤ n⌝%Z ∗
      ⌜i + n ≤ sz⌝%Z ∗
      array_slice t i_ (DfracOwn 1) (replicate (Z.to_nat n) v)
    }}}.
  Proof.
    iIntros (->) "%Hn %Φ (#Hinv & Hslice) HΦ".
    wp_rec.
    wp_smart_apply (array_size_spec_inv with "Hinv") as "_".
    repeat (wp_smart_apply assume_spec' as "%").
    wp_smart_apply (array_unsafe_fill_slice_spec with "Hslice"); [lia.. |].
    iSteps.
  Qed.

  Lemma array_fill_spec t vs v :
    {{{
      array_model t (DfracOwn 1) vs
    }}}
      array_fill t v
    {{{
      RET ();
      array_model t (DfracOwn 1) (replicate (length vs) v)
    }}}.
  Proof.
    iIntros "%Φ Hmodel HΦ".
    wp_rec.
    wp_smart_apply (array_size_spec with "Hmodel") as "Hmodel".
    iDestruct (array_model_to_slice' with "Hmodel") as "(Hslice & #?)".
    wp_apply (array_unsafe_fill_slice_spec with "Hslice") as "Hslice"; [done.. |].
    iSteps.
    - rewrite length_replicate //.
    - rewrite Nat2Z.id //.
  Qed.

  Lemma array_unsafe_make_spec sz v :
    (0 ≤ sz)%Z →
    {{{
      True
    }}}
      array_unsafe_make #sz v
    {{{ t,
      RET t;
      array_model t (DfracOwn 1) (replicate (Z.to_nat sz) v)
    }}}.
  Proof.
    iIntros "% %Φ _ HΦ".
    wp_rec.
    wp_smart_apply (array_unsafe_alloc_spec with "[//]") as "%t Hmodel"; first done.
    wp_smart_apply (array_fill_spec with "Hmodel").
    rewrite length_replicate . iSteps.
  Qed.

  Lemma array_make_spec sz v :
    {{{
      True
    }}}
      array_make #sz v
    {{{ t,
      RET t;
      ⌜0 ≤ sz⌝%Z ∗
      array_model t (DfracOwn 1) (replicate (Z.to_nat sz) v)
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_rec.
    wp_smart_apply assume_spec' as "%Hsz".
    wp_smart_apply (array_unsafe_make_spec with "[//]"); first done.
    iSteps.
  Qed.

  #[local] Lemma array_foldli_aux_spec i vs Ψ t sz acc fn :
    i ≤ sz →
    i = length vs →
    {{{
      ▷ Ψ i vs None acc ∗
      □ (
        ∀ i vs (o : option val) acc,
        ⌜i < sz⌝ -∗
        ⌜i = length vs⌝ -∗
        Ψ i vs o acc -∗
        match o with
        | None =>
            au_load t i (λ v,
              ▷ Ψ i vs (Some v) acc
            )
        | Some v =>
            WP fn acc #i v {{ acc,
              ▷ Ψ (S i) (vs ++ [v]) None acc
            }}
        end
      )
    }}}
      array_foldli_aux t #sz acc fn #i
    {{{ vs' acc,
      RET acc;
      ⌜(length vs + length vs')%nat = sz⌝ ∗
      Ψ sz (vs ++ vs') None acc
    }}}.
  Proof.
    iIntros "%Hi1 %Hi2 %Φ (HΨ & #H) HΦ".
    remember (sz - i) as j eqn:Hj.
    iInduction j as [| j] "IH" forall (i vs acc Hi1 Hi2 Hj).
    all: wp_rec; wp_pures.
    - rewrite bool_decide_eq_true_2; first (repeat f_equal; lia). wp_pures.
      iApply ("HΦ" $! []).
      rewrite !right_id. assert (sz = i) as -> by lia. iSteps.
    - rewrite bool_decide_eq_false_2; first naive_solver lia. wp_pures.
      iDestruct ("H" with "[%] [//] HΨ") as "H'"; first lia.
      awp_smart_apply (array_unsafe_get_spec_atomic_cell with "[//]") without "HΦ".
      iApply (aacc_aupd_commit with "H'"); first done. iIntros "%dq %v H↦".
      rewrite /atomic_acc /= Nat2Z.id.
      repeat iExists _. iFrame. iStep 2; first iSteps. iIntros "$ !> HΨ !> H£ HΦ".
      iMod (lc_fupd_elim_later with "H£ HΨ") as "HΨ".
      wp_smart_apply (wp_wand with "(H [%] [//] HΨ)") as "%acc' HΨ"; first lia.
      rewrite Z.add_1_r -Nat2Z.inj_succ.
      wp_apply ("IH" with "[%] [%] [%] HΨ [HΦ]"); rewrite ?length_app; [naive_solver lia.. |].
      clear acc. iIntros "!> %vs' %acc (<- & HΨ)".
      iApply ("HΦ" $! (v :: vs')).
      rewrite -(assoc (++)). iSteps.
  Qed.
  Lemma array_foldli_spec_atomic Ψ t sz acc fn :
    {{{
      array_inv t sz ∗
      ▷ Ψ 0 [] None acc ∗
      □ (
        ∀ i vs (o : option val) acc,
        ⌜i < sz⌝ -∗
        ⌜i = length vs⌝ -∗
        Ψ i vs o acc -∗
        match o with
        | None =>
            au_load t i (λ v,
              ▷ Ψ i vs (Some v) acc
            )
        | Some v =>
            WP fn acc #i v {{ acc,
              ▷ Ψ (S i) (vs ++ [v]) None acc
            }}
        end
      )
    }}}
      array_foldli t acc fn
    {{{ vs acc,
      RET acc;
      ⌜length vs = sz⌝ ∗
      Ψ sz vs None acc
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & HΨ & #H) HΦ".
    wp_rec.
    wp_smart_apply (array_size_spec_inv with "Hinv") as "_".
    rewrite -Nat2Z.inj_0.
    wp_apply (array_foldli_aux_spec 0 [] Ψ with "[$HΨ] HΦ"); [lia | done |].
    iSteps.
  Qed.
  Lemma array_foldli_spec Ψ t dq vs acc fn :
    {{{
      ▷ Ψ 0 [] acc ∗
      array_model t dq vs ∗
      □ (
        ∀ i v acc,
        ⌜vs !! i = Some v⌝ -∗
        Ψ i (take i vs) acc -∗
        WP fn acc #i v {{ acc,
          ▷ Ψ (S i) (take i vs ++ [v]) acc
        }}
      )
    }}}
      array_foldli t acc fn
    {{{ acc,
      RET acc;
      array_model t dq vs ∗
      Ψ (length vs) vs acc
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hmodel & #Hfn) HΦ".
    iDestruct (array_model_to_inv with "Hmodel") as "#Hinv".
    pose (Ψ' i vs_left o acc := (
      ⌜vs_left = take i vs⌝ ∗
      array_model t dq vs ∗
      Ψ i vs_left acc ∗
      ⌜from_option (λ v, v = vs !!! i) True o⌝%I
    )%I).
    wp_apply (array_foldli_spec_atomic Ψ' with "[$Hinv $Hmodel $HΨ]"); last first.
    { clear acc. iIntros "%vs_left %acc (%Hvs_left & (-> & Hmodel & HΨ & _))".
      rewrite /Ψ' firstn_all2 //.
      iApply ("HΦ" with "[$Hmodel $HΨ]").
    }
    iStep. clear acc. iIntros "!> %i %vs_left %o %acc %Hi1 %Hi2 (-> & Hmodel & HΨ & %Ho)".
    opose proof* (list_lookup_lookup_total_lt vs i); first lia.
    destruct o as [v |].
    - rewrite Ho.
      wp_apply (wp_wand with "(Hfn [] HΨ)"); first iSteps. clear acc. iIntros "%acc HΨ". iFrame.
      erewrite take_S_r => //.
    - iDestruct (array_model_lookup_acc i with "Hmodel") as "(H↦ & Hmodel)"; first done.
      iAuIntro. iAaccIntro with "H↦"; iSteps.
  Qed.
  Lemma array_foldli_spec' Ψ t dq vs acc fn :
    {{{
      ▷ Ψ 0 [] acc ∗
      array_model t dq vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        ∀ acc,
        Ψ i (take i vs) acc -∗
        WP fn acc #i v {{ acc,
          ▷ Ψ (S i) (take i vs ++ [v]) acc
        }}
      )
    }}}
      array_foldli t acc fn
    {{{ acc,
      RET acc;
      array_model t dq vs ∗
      Ψ (length vs) vs acc
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hmodel & Hfn) HΦ".
    match goal with |- context [big_opL bi_sep ?Ξ' _] => set Ξ := Ξ' end.
    pose (Ψ' i vs_left acc := (
      Ψ i vs_left acc ∗
      [∗ list] j ↦ v ∈ drop i vs, Ξ (i + j) v
    )%I).
    wp_apply (array_foldli_spec Ψ' with "[$HΨ $Hmodel $Hfn]"); last iSteps.
    clear acc. iIntros "!> %i %v %acc %Hlookup (HΨ & HΞ)".
    erewrite drop_S => //.
    iDestruct "HΞ" as "(Hfn & HΞ)".
    rewrite Nat.add_0_r. setoid_rewrite Nat.add_succ_r. iSteps.
  Qed.

  Lemma array_foldl_spec_atomic Ψ t sz acc fn :
    {{{
      array_inv t sz ∗
      ▷ Ψ 0 [] None acc ∗
      □ (
        ∀ i vs (o : option val) acc,
        ⌜i < sz⌝ -∗
        ⌜i = length vs⌝ -∗
        Ψ i vs o acc -∗
        match o with
        | None =>
            au_load t i (λ v,
              ▷ Ψ i vs (Some v) acc
            )
        | Some v =>
            WP fn acc v {{ acc,
              ▷ Ψ (S i) (vs ++ [v]) None acc
            }}
        end
      )
    }}}
      array_foldl t acc fn
    {{{ vs acc,
      RET acc;
      ⌜length vs = sz⌝ ∗
      Ψ sz vs None acc
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & HΨ & #H) HΦ".
    wp_rec.
    wp_smart_apply (array_foldli_spec_atomic Ψ with "[$Hinv $HΨ] HΦ"). clear acc. iIntros "!> %i %vs %o %acc %Hi1 %Hi2 HΨ".
    case_match; try wp_pures; iApply ("H" with "[%] [%] HΨ"); lia.
  Qed.
  Lemma array_foldl_spec Ψ t dq vs acc fn :
    {{{
      ▷ Ψ 0 [] acc ∗
      array_model t dq vs ∗
      □ (
        ∀ i v acc,
        ⌜vs !! i = Some v⌝ -∗
        Ψ i (take i vs) acc -∗
        WP fn acc v {{ acc,
          ▷ Ψ (S i) (take i vs ++ [v]) acc
        }}
      )
    }}}
      array_foldl t acc fn
    {{{ acc,
      RET acc;
      array_model t dq vs ∗
      Ψ (length vs) vs acc
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hmodel & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (array_foldli_spec Ψ with "[$HΨ $Hmodel] HΦ").
    iSteps.
  Qed.
  Lemma array_foldl_spec' Ψ t dq vs acc fn :
    {{{
      ▷ Ψ 0 [] acc ∗
      array_model t dq vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        ∀ acc,
        Ψ i (take i vs) acc -∗
        WP fn acc v {{ acc,
          ▷ Ψ (S i) (take i vs ++ [v]) acc
        }}
      )
    }}}
      array_foldl t acc fn
    {{{ acc,
      RET acc;
      array_model t dq vs ∗
      Ψ (length vs) vs acc
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hmodel & Hfn) HΦ".
    wp_rec.
    wp_smart_apply (array_foldli_spec' Ψ with "[$HΨ $Hmodel Hfn] HΦ").
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.

  #[local] Lemma array_foldri_aux_spec sz (i : Z) vs Ψ t fn acc :
    Z.to_nat i + length vs = sz →
    {{{
      ▷ Ψ (Z.to_nat i) acc None vs ∗
      □ (
        ∀ i acc (o : option val) vs,
        ⌜(S i + length vs)%nat = sz⌝ -∗
        Ψ (S i) acc o vs -∗
        match o with
        | None =>
            au_load t i (λ v,
              ▷ Ψ (S i) acc (Some v) vs
            )
        | Some v =>
            WP fn #i v acc {{ acc,
              ▷ Ψ i acc None (v :: vs)
            }}
        end
      )
    }}}
      array_foldri_aux t fn acc #i
    {{{ acc vs',
      RET acc;
      ⌜(length vs' + length vs)%nat = sz⌝ ∗
      Ψ 0 acc None (vs' ++ vs)
    }}}.
  Proof.
    iIntros "%Hi %Φ (HΨ & #H) HΦ".
    remember (Z.to_nat i) as j eqn:Hj.
    iInduction j as [| j] "IH" forall (i vs acc Hi Hj);
      wp_rec; wp_pures credit:"H£".
    - rewrite bool_decide_eq_true_2; first lia. wp_pures.
      iApply ("HΦ" $! _ []).
      iSteps.
    - rewrite bool_decide_eq_false_2; first lia. wp_pures.
      assert (i = S j) as -> by lia. rewrite Z.sub_1_r -Nat2Z.inj_pred /=; first lia.
      iDestruct ("H" with "[%] HΨ") as "H'"; first done.
      awp_smart_apply (array_unsafe_get_spec_atomic_cell with "[//]") without "HΦ".
      iApply (aacc_aupd_commit with "H'"); first done. iIntros "%dq %v H↦".
      rewrite /atomic_acc /= Nat2Z.id.
      repeat iExists _. iFrame. iStep 2; first iSteps. iIntros "$ !> HΨ !> H£ HΦ".
      iMod (lc_fupd_elim_later with "H£ HΨ") as "HΨ".
      wp_smart_apply (wp_wand with "(H [%] HΨ)") as "%acc' HΨ"; first lia.
      wp_apply ("IH" with "[] [] HΨ [HΦ]"); rewrite ?length_app; [iSteps.. |]. clear acc. iIntros "!> %acc %vs' (<- & HΨ)".
      iApply ("HΦ" $! _ (vs' ++ [v])).
      rewrite length_app -(assoc (++)). iSteps.
  Qed.
  Lemma array_foldri_spec_atomic Ψ t sz fn acc :
    {{{
      array_inv t sz ∗
      ▷ Ψ sz acc None [] ∗
      □ (
        ∀ i acc (o : option val) vs,
        ⌜(S i + length vs)%nat = sz⌝ -∗
        Ψ (S i) acc o vs -∗
        match o with
        | None =>
            au_load t i (λ v,
              ▷ Ψ (S i) acc (Some v) vs
            )
        | Some v =>
            WP fn #i v acc {{ acc,
              ▷ Ψ i acc None (v :: vs)
            }}
        end
      )
    }}}
      array_foldri t fn acc
    {{{ acc vs,
      RET acc;
      ⌜length vs = sz⌝ ∗
      Ψ 0 acc None vs
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & HΨ & #H) HΦ".
    wp_rec.
    wp_smart_apply (array_size_spec_inv with "Hinv") as "_".
    wp_apply (array_foldri_aux_spec sz sz [] Ψ with "[HΨ $H]").
    { rewrite right_id. lia. }
    { rewrite Nat2Z.id //. }
    clear acc. iIntros "%acc %vs".
    rewrite !right_id. iSteps.
  Qed.
  Lemma array_foldri_spec Ψ t dq vs fn acc :
    {{{
      array_model t dq vs ∗
      ▷ Ψ (length vs) acc [] ∗
      □ (
        ∀ i v acc,
        ⌜vs !! i = Some v⌝ -∗
        Ψ (S i) acc (drop (S i) vs) -∗
        WP fn #i v acc {{ acc,
          ▷ Ψ i acc (v :: drop (S i) vs)
        }}
      )
    }}}
      array_foldri t fn acc
    {{{ acc,
      RET acc;
      Ψ 0 acc vs ∗
      array_model t dq vs
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & HΨ & #Hfn) HΦ".
    iDestruct (array_model_to_inv with "Hmodel") as "#Hinv".
    pose (Ψ' i acc o vs_right := (
      ⌜vs_right = drop i vs⌝ ∗
      array_model t dq vs ∗
      Ψ i acc vs_right ∗
      ⌜from_option (λ v, v = vs !!! (i - 1)) True o⌝%I
    )%I).
    wp_apply (array_foldri_spec_atomic Ψ' with "[$Hinv $Hmodel $HΨ]"); last iSteps.
    iSplitR.
    - rewrite drop_all. iSteps.
    - clear acc. iIntros "!> %i %acc %o %vs_right %Hi (-> & Hmodel & HΨ & %Ho)".
      opose proof* (list_lookup_lookup_total_lt vs i) as Hlookup; first lia.
      destruct o as [v |].
      + rewrite Ho.
        wp_apply (wp_wand with "(Hfn [] HΨ)").
        { iPureIntro. rewrite Hlookup. repeat f_equal. lia. }
        clear acc. iIntros "%acc HΨ". iFrame.
        iPureIntro. rewrite -drop_S ?Hlookup; repeat f_equal; lia.
      + iDestruct (array_model_lookup_acc i with "Hmodel") as "(H↦ & Hmodel)"; first done.
        iAuIntro. iAaccIntro with "H↦"; first iSteps. iIntros "H↦ !>".
        iSteps; iPureIntro; rewrite length_drop; f_equal; lia.
  Qed.
  Lemma array_foldri_spec' Ψ t dq vs fn acc :
    {{{
      array_model t dq vs ∗
      ▷ Ψ (length vs) acc [] ∗
      ( [∗ list] i ↦ v ∈ vs,
        ∀ acc,
        Ψ (S i) acc (drop (S i) vs) -∗
        WP fn #i v acc {{ acc,
          ▷ Ψ i acc (v :: drop (S i) vs)
        }}
      )
    }}}
      array_foldri t fn acc
    {{{ acc,
      RET acc;
      Ψ 0 acc vs ∗
      array_model t dq vs
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & HΨ & Hfn) HΦ".
    match goal with |- context [big_opL bi_sep ?Ξ' _] => set Ξ := Ξ' end.
    pose (Ψ' i acc vs_right := (
      Ψ i acc vs_right ∗
      [∗ list] j ↦ v ∈ take i vs, Ξ j v
    )%I).
    wp_apply (array_foldri_spec Ψ' with "[$Hmodel HΨ Hfn]"); last iSteps.
    iFrame. rewrite firstn_all2; first lia. iFrame.
    clear acc. iIntros "!> %i %v %acc %Hlookup (HΨ & HΞ)".
    pose proof Hlookup as Hi%lookup_lt_Some.
    erewrite take_S_r => //.
    iDestruct "HΞ" as "(HΞ & Hfn & _)".
    rewrite Nat.add_0_r length_take Nat.min_l; first lia. iSteps.
  Qed.

  Lemma array_foldr_spec_atomic Ψ t sz fn acc :
    {{{
      array_inv t sz ∗
      ▷ Ψ sz acc None [] ∗
      □ (
        ∀ i acc (o : option val) vs,
        ⌜(S i + length vs)%nat = sz⌝ -∗
        Ψ (S i) acc o vs -∗
        match o with
        | None =>
            au_load t i (λ v,
              ▷ Ψ (S i) acc (Some v) vs
            )
        | Some v =>
            WP fn v acc {{ acc,
              ▷ Ψ i acc None (v :: vs)
            }}
        end
      )
    }}}
      array_foldr t fn acc
    {{{ acc vs,
      RET acc;
      ⌜length vs = sz⌝ ∗
      Ψ 0 acc None vs
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & HΨ & #H) HΦ".
    wp_rec.
    wp_smart_apply (array_foldri_spec_atomic Ψ with "[$Hinv $HΨ] HΦ"). clear acc. iIntros "!> %i %acc %o %vs %Hi HΨ".
    case_match; try wp_pures; iApply ("H" with "[//] HΨ").
  Qed.
  Lemma array_foldr_spec Ψ t dq vs fn acc :
    {{{
      array_model t dq vs ∗
      ▷ Ψ (length vs) acc [] ∗
      □ (
        ∀ i v acc,
        ⌜vs !! i = Some v⌝ -∗
        Ψ (S i) acc (drop (S i) vs) -∗
        WP fn v acc {{ acc,
          ▷ Ψ i acc (v :: drop (S i) vs)
        }}
      )
    }}}
      array_foldr t fn acc
    {{{ acc,
      RET acc;
      Ψ 0 acc vs ∗
      array_model t dq vs
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & HΨ & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (array_foldri_spec Ψ with "[$Hmodel $HΨ] HΦ").
    iSteps.
  Qed.
  Lemma array_foldr_spec' Ψ t dq vs fn acc :
    {{{
      array_model t dq vs ∗
      ▷ Ψ (length vs) acc [] ∗
      ( [∗ list] i ↦ v ∈ vs,
        ∀ acc,
        Ψ (S i) acc (drop (S i) vs) -∗
        WP fn v acc {{ acc,
          ▷ Ψ i acc (v :: drop (S i) vs)
        }}
      )
    }}}
      array_foldr t fn acc
    {{{ acc,
      RET acc;
      Ψ 0 acc vs ∗
      array_model t dq vs
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & HΨ & Hfn) HΦ".
    wp_rec.
    wp_smart_apply (array_foldri_spec' Ψ with "[$Hmodel $HΨ Hfn] HΦ").
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.

  Lemma array_iteri_spec_atomic Ψ t sz fn :
    {{{
      array_inv t sz ∗
      ▷ Ψ 0 [] None ∗
      □ (
        ∀ i vs (o : option val),
        ⌜i < sz⌝ -∗
        ⌜i = length vs⌝ -∗
        Ψ i vs o -∗
        match o with
        | None =>
            au_load t i (λ v,
              ▷ Ψ i vs (Some v)
            )
        | Some v =>
            WP fn #i v {{ res,
              ⌜res = ()%V⌝ ∗
              ▷ Ψ (S i) (vs ++ [v]) None
            }}
        end
      )
    }}}
      array_iteri t fn
    {{{ vs,
      RET ();
      ⌜length vs = sz⌝ ∗
      Ψ sz vs None
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & HΨ & #H) HΦ".
    wp_rec.
    wp_smart_apply (array_size_spec_inv with "Hinv") as "_".
    pose Ψ' (_ : Z) i := (
      ∃ vs,
      ⌜length vs = i⌝ ∗
      Ψ i vs None
    )%I.
    wp_smart_apply (for_spec_strong Ψ' with "[HΨ]").
    { iSplitL. { iExists []. iSteps. }
      iIntros "!> %i_ %i -> %Hi (%vs & %Hvs & HΨ)". rewrite Z.add_0_l in Hi |- *.
      iDestruct ("H" with "[%] [//] HΨ") as "H'"; first lia.
      awp_smart_apply (array_unsafe_get_spec_atomic_cell with "[//]").
      iApply (aacc_aupd_commit with "H'"); first done. iIntros "%dq %v H↦".
      rewrite /atomic_acc /= Nat2Z.id.
      repeat iExists _. iStep 2; first iSteps. iIntros "$ !> HΨ !> H£".
      iMod (lc_fupd_elim_later with "H£ HΨ") as "HΨ".
      wp_smart_apply (wp_wand with "(H [%] [//] HΨ)") as "%acc' (-> & HΨ)"; first lia.
      iSteps. iExists (vs ++ [v]). rewrite length_app. iSteps.
    }
    rewrite Z.sub_0_r Nat2Z.id. iSteps.
  Qed.
  Lemma array_iteri_spec Ψ t dq vs fn :
    {{{
      ▷ Ψ 0 [] ∗
      array_model t dq vs ∗
      □ (
        ∀ i v,
        ⌜vs !! i = Some v⌝ -∗
        Ψ i (take i vs) -∗
        WP fn #i v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ (S i) (take i vs ++ [v])
        }}
      )
    }}}
      array_iteri t fn
    {{{
      RET ();
      array_model t dq vs ∗
      Ψ (length vs) vs
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hmodel & #Hfn) HΦ".
    iDestruct (array_model_to_inv with "Hmodel") as "#Hinv".
    pose (Ψ' i vs_left o := (
      ⌜vs_left = take i vs⌝ ∗
      array_model t dq vs ∗
      Ψ i vs_left ∗
      ⌜from_option (λ v, v = vs !!! i) True o⌝%I
    )%I).
    wp_smart_apply (array_iteri_spec_atomic Ψ' with "[$Hinv $Hmodel $HΨ]"); last first.
    { iSteps. rewrite firstn_all //. }
    iStep. iIntros "!> %i %vs_left %o %Hi1 %Hi2 (-> & Hmodel & HΨ & %Ho)".
    opose proof* (list_lookup_lookup_total_lt vs i); first lia.
    destruct o as [v |].
    - rewrite Ho.
      wp_apply (wp_wand with "(Hfn [] HΨ)") as (res) "(-> & HΨ)"; first iSteps.
      iSteps. erewrite take_S_r => //.
    - iDestruct (array_model_lookup_acc i with "Hmodel") as "(H↦ & Hmodel)"; first done.
      iAuIntro. iAaccIntro with "H↦"; iSteps.
  Qed.
  Lemma array_iteri_spec' Ψ t dq vs fn :
    {{{
      ▷ Ψ 0 [] ∗
      array_model t dq vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i (take i vs) -∗
        WP fn #i v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ (S i) (take i vs ++ [v])
        }}
      )
    }}}
      array_iteri t fn
    {{{
      RET ();
      array_model t dq vs ∗
      Ψ (length vs) vs
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hmodel & Hfn) HΦ".
    match goal with |- context [big_opL bi_sep ?Ξ' _] => set Ξ := Ξ' end.
    pose (Ψ' i vs_left := (
      Ψ i vs_left ∗
      [∗ list] j ↦ v ∈ drop i vs, Ξ (i + j) v
    )%I).
    wp_apply (array_iteri_spec Ψ' with "[$HΨ $Hmodel $Hfn]"); last iSteps.
    iIntros "!> %i %v %Hlookup (HΨ & HΞ)".
    erewrite drop_S => //.
    iDestruct "HΞ" as "(Hfn & HΞ)".
    rewrite Nat.add_0_r. setoid_rewrite Nat.add_succ_r. iSteps.
  Qed.
  Lemma array_iteri_spec_disentangled Ψ t dq vs fn :
    {{{
      array_model t dq vs ∗
      □ (
        ∀ i v,
        ⌜vs !! i = Some v⌝ -∗
        WP fn #i v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ i v
        }}
      )
    }}}
      array_iteri t fn
    {{{
      RET ();
      array_model t dq vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & #Hfn) HΦ".
    pose (Ψ' i vs := (
      [∗ list] j ↦ v ∈ vs, Ψ j v
    )%I).
    wp_apply (array_iteri_spec Ψ' with "[$Hmodel]"); last iSteps.
    rewrite /Ψ'. iSteps.
    rewrite big_sepL_snoc length_take Nat.min_l; last iSteps.
    eapply Nat.lt_le_incl, lookup_lt_Some. done.
  Qed.
  Lemma array_iteri_spec_disentangled' Ψ t dq vs fn :
    {{{
      array_model t dq vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        WP fn #i v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ i v
        }}
      )
    }}}
      array_iteri t fn
    {{{
      RET ();
      array_model t dq vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & Hfn) HΦ".
    pose (Ψ' i vs := (
      [∗ list] j ↦ v ∈ vs, Ψ j v
    )%I).
    wp_apply (array_iteri_spec' Ψ' with "[$Hmodel Hfn]"); last iSteps.
    rewrite /Ψ'. iSteps.
    iApply (big_sepL_impl with "Hfn"). iSteps.
    rewrite big_sepL_snoc length_take Nat.min_l; last iSteps.
    eapply Nat.lt_le_incl, lookup_lt_Some. done.
  Qed.

  Lemma array_iter_spec_atomic Ψ t sz fn :
    {{{
      array_inv t sz ∗
      ▷ Ψ 0 [] None ∗
      □ (
        ∀ i vs (o : option val),
        ⌜i < sz⌝ -∗
        ⌜i = length vs⌝ -∗
        Ψ i vs o -∗
        match o with
        | None =>
            au_load t i (λ v,
              ▷ Ψ i vs (Some v)
            )
        | Some v =>
            WP fn v {{ res,
              ⌜res = ()%V⌝ ∗
              ▷ Ψ (S i) (vs ++ [v]) None
            }}
        end
      )
    }}}
      array_iter t fn
    {{{ vs,
      RET ();
      ⌜length vs = sz⌝ ∗
      Ψ sz vs None
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & HΨ & #H) HΦ".
    wp_rec.
    wp_smart_apply (array_iteri_spec_atomic Ψ with "[$Hinv $HΨ] HΦ") as "!> %i %vs %o % % HΨ".
    case_match; try wp_pures; iApply ("H" with "[//] [//] HΨ").
  Qed.
  Lemma array_iter_spec Ψ t dq vs fn :
    {{{
      ▷ Ψ 0 [] ∗
      array_model t dq vs ∗
      □ (
        ∀ i v,
        ⌜vs !! i = Some v⌝ -∗
        Ψ i (take i vs) -∗
        WP fn v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ (S i) (take i vs ++ [v])
        }}
      )
    }}}
      array_iter t fn
    {{{
      RET ();
      array_model t dq vs ∗
      Ψ (length vs) vs
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hmodel & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (array_iteri_spec Ψ with "[$HΨ $Hmodel] HΦ").
    iSteps.
  Qed.
  Lemma array_iter_spec' Ψ t dq vs fn :
    {{{
      ▷ Ψ 0 [] ∗
      array_model t dq vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i (take i vs) -∗
        WP fn v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ (S i) (take i vs ++ [v])
        }}
      )
    }}}
      array_iter t fn
    {{{
      RET ();
      array_model t dq vs ∗
      Ψ (length vs) vs
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hmodel & Hfn) HΦ".
    wp_rec.
    wp_smart_apply (array_iteri_spec' Ψ with "[$HΨ $Hmodel Hfn] HΦ").
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.
  Lemma array_iter_spec_disentangled Ψ t dq vs fn :
    {{{
      array_model t dq vs ∗
      □ (
        ∀ i v,
        ⌜vs !! i = Some v⌝ -∗
        WP fn v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ i v
        }}
      )
    }}}
      array_iter t fn
    {{{
      RET ();
      array_model t dq vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (array_iteri_spec_disentangled Ψ with "[$Hmodel] HΦ").
    iSteps.
  Qed.
  Lemma array_iter_spec_disentangled' Ψ t dq vs fn :
    {{{
      array_model t dq vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        WP fn v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ i v
        }}
      )
    }}}
      array_iter t fn
    {{{
      RET ();
      array_model t dq vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & Hfn) HΦ".
    wp_rec.
    wp_smart_apply (array_iteri_spec_disentangled' Ψ with "[$Hmodel Hfn] HΦ").
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.

  Lemma array_applyi_spec_atomic Ψ t sz fn :
    {{{
      array_inv t sz ∗
      ▷ Ψ 0 [] None [] ∗
      □ (
        ∀ i vs (o : option (val + val * val)) ws,
        ⌜i < sz⌝ -∗
        ⌜i = length vs⌝ -∗
        ⌜length vs = length ws⌝ -∗
        Ψ i vs o ws -∗
        match o with
        | None =>
            au_load t i (λ v,
              ▷ Ψ i vs (Some $ inl v) ws
            )
        | Some (inl v) =>
            WP fn #i v {{ w,
              ▷ Ψ i vs (Some $ inr (v, w)) ws
            }}
        | Some (inr (v, w)) =>
            au_store t i w (
              ▷ Ψ (S i) (vs ++ [v]) None (ws ++ [w])
            )
        end
      )
    }}}
      array_applyi t fn
    {{{ vs ws,
      RET ();
      ⌜length vs = sz⌝ ∗
      ⌜length vs = length ws⌝ ∗
      Ψ sz vs None ws
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & HΨ & #H) HΦ".
    wp_rec credit:"H£".
    pose (Ψ' i vs o := (
      ∃ ws,
      ⌜length vs = length ws⌝ ∗
      Ψ i vs (inl <$> o) ws ∗
      £ 1
    )%I).
    wp_smart_apply (array_iteri_spec_atomic Ψ' with "[$Hinv HΨ $H£]"); last iSteps.
    iSplitL "HΨ". { iExists []. iSteps. }
    iIntros "!> %i %vs %o %Hi1 %Hi2 (%ws & %Hws & HΨ & H£)".
    destruct o as [v |].
    - wp_smart_apply (wp_wand with "(H [//] [//] [//] HΨ)") as "%w HΨ".
      iMod (lc_fupd_elim_later with "H£ HΨ") as "HΨ".
      iDestruct ("H" with "[//] [//] [//] HΨ") as "H'".
      awp_apply (array_unsafe_set_spec_atomic_cell with "[//]").
      iApply (aacc_aupd_commit with "H'"); first done. iIntros "%v' Hslice".
      rewrite /atomic_acc /=.
      iStep 2; first iSteps. iIntros "$ !> HΨ !> H£". iStep.
      iExists (ws ++ [w]). rewrite !length_app. iSteps.
    - iApply (atomic_update_wand with "(H [//] [//] [//] HΨ)").
      iSteps.
  Qed.
  Lemma array_applyi_spec Ψ t vs fn :
    {{{
      ▷ Ψ 0 [] [] ∗
      array_model t (DfracOwn 1) vs ∗
      □ (
        ∀ i v ws,
        ⌜i = length ws⌝ -∗
        ⌜vs !! i = Some v⌝ -∗
        Ψ i (take i vs) ws -∗
        WP fn #i v {{ w,
          ▷ Ψ (S i) (take i vs ++ [v]) (ws ++ [w])
        }}
      )
    }}}
      array_applyi t fn
    {{{ ws,
      RET ();
      ⌜length vs = length ws⌝ ∗
      array_model t (DfracOwn 1) ws ∗
      Ψ (length vs) vs ws
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hmodel & #Hfn) HΦ".
    iDestruct (array_model_to_inv with "Hmodel") as "#Hinv".
    pose (Ψ' i vs_left o ws := (
      ⌜vs_left = take i vs⌝ ∗
      array_model t (DfracOwn 1) (ws ++ drop i vs) ∗
      match o with
      | None =>
          Ψ i vs_left ws
      | Some (inl v) =>
          ⌜v = vs !!! i⌝ ∗
          Ψ i vs_left ws
      | Some (inr (v, w)) =>
          ⌜v = vs !!! i⌝ ∗
          Ψ (S i) (vs_left ++ [v]) (ws ++ [w])
      end
    )%I).
    wp_apply (array_applyi_spec_atomic Ψ' with "[$Hinv $HΨ $Hmodel]"); last first.
    { iIntros "%vs_left %ws (%Hvs_left_1 & %Hws & (-> & Hmodel & HΨ))".
      rewrite firstn_all2; first lia. rewrite skipn_all2; first lia. rewrite right_id.
      iApply ("HΦ" $! ws). iSteps.
    }
    iStep. iIntros "!> %i %vs_left %o %ws %Hvs_left %Hi %Hws (-> & Hmodel & HΨ)".
    opose proof* (list_lookup_lookup_total_lt vs i); first lia.
    destruct o as [[v | (v & w)] |].
    - iDestruct "HΨ" as "(-> & HΨ)".
      wp_apply (wp_wand with "(Hfn [%] [//] HΨ)"); first lia.
      iSteps.
    - iDestruct "HΨ" as "(-> & HΨ)".
      assert ((ws ++ drop i vs) !! i = Some (vs !!! i)).
      { rewrite lookup_app_r; first lia.
        rewrite lookup_drop list_lookup_lookup_total_lt; first lia.
        repeat f_equal. lia.
      }
      iDestruct (array_model_update i with "Hmodel") as "(_ & H↦ & Hmodel)"; first done.
      iAuIntro. iAaccIntro with "H↦"; first iSteps. iIntros "H↦ !>". iFrame.
      iSplit; first rewrite -take_S_r //.
      iDestruct ("Hmodel" with "H↦") as "Hmodel".
      rewrite insert_app_r_alt; first lia.
      erewrite drop_S => //.
      rewrite Hi Hws Nat.sub_diag -assoc //.
    - assert ((ws ++ drop i vs) !! i = Some (vs !!! i)).
      { rewrite lookup_app_r; first lia.
        rewrite lookup_drop list_lookup_lookup_total_lt; first lia.
        repeat f_equal. lia.
      }
      iDestruct (array_model_lookup_acc i with "Hmodel") as "(H↦ & Hmodel)"; first done.
      iAuIntro. iAaccIntro with "H↦"; iSteps.
  Qed.
  Lemma array_applyi_spec' Ψ t vs fn :
    {{{
      ▷ Ψ 0 [] [] ∗
      array_model t (DfracOwn 1) vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        ∀ ws,
        ⌜i = length ws⌝ -∗
        Ψ i (take i vs) ws -∗
        WP fn #i v {{ w,
          ▷ Ψ (S i) (take i vs ++ [v]) (ws ++ [w])
        }}
      )
    }}}
      array_applyi t fn
    {{{ ws,
      RET ();
      ⌜length vs = length ws⌝ ∗
      array_model t (DfracOwn 1) ws ∗
      Ψ (length vs) vs ws
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hmodel & Hfn) HΦ".
    match goal with |- context [big_opL bi_sep ?Ξ' _] => set Ξ := Ξ' end.
    pose (Ψ' i vs_left ws := (
      Ψ i vs_left ws ∗
      [∗ list] j ↦ v ∈ drop i vs, Ξ (i + j) v
    )%I).
    wp_apply (array_applyi_spec Ψ' with "[HΨ $Hmodel Hfn]"); last iSteps.
    iFrame. iIntros "!> %i %v %ws %Hi %Hlookup (HΨ & HΞ)".
    erewrite drop_S => //.
    iDestruct "HΞ" as "(Hfn & HΞ)".
    rewrite Nat.add_0_r. setoid_rewrite Nat.add_succ_r. iSteps.
  Qed.
  Lemma array_applyi_spec_disentangled Ψ t vs fn :
    {{{
      array_model t (DfracOwn 1) vs ∗
      □ (
        ∀ i v,
        ⌜vs !! i = Some v⌝ -∗
        WP fn #i v {{ w,
          ▷ Ψ i w
        }}
      )
    }}}
      array_applyi t fn
    {{{ ws,
      RET ();
      ⌜length vs = length ws⌝ ∗
      array_model t (DfracOwn 1) ws ∗
      ( [∗ list] i ↦ w ∈ ws,
        Ψ i w
      )
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & #Hfn) HΦ".
    pose (Ψ' i vs_left ws := (
      [∗ list] j ↦ w ∈ ws, Ψ j w
    )%I).
    wp_apply (array_applyi_spec Ψ' with "[$Hmodel]"); last iSteps.
    rewrite /Ψ'. iSteps.
    rewrite big_sepL_snoc. iSteps.
  Qed.
  Lemma array_applyi_spec_disentangled' Ψ t vs fn :
    {{{
      array_model t (DfracOwn 1) vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        WP fn #i v {{ w,
          ▷ Ψ i w
        }}
      )
    }}}
      array_applyi t fn
    {{{ ws,
      RET ();
      array_model t (DfracOwn 1) ws ∗
      ( [∗ list] i ↦ w ∈ ws,
        Ψ i w
      )
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & Hfn) HΦ".
    pose (Ψ' i vs_left ws := (
      [∗ list] j ↦ w ∈ ws, Ψ j w
    )%I).
    wp_apply (array_applyi_spec' Ψ' with "[Hmodel Hfn]"); last iSteps.
    rewrite /Ψ'. iSteps.
    iApply (big_sepL_impl with "Hfn"). iSteps.
    rewrite big_sepL_snoc. iSteps.
  Qed.

  Lemma array_apply_spec_atomic Ψ t sz fn :
    {{{
      array_inv t sz ∗
      ▷ Ψ 0 [] None [] ∗
      □ (
        ∀ i vs (o : option (val + val * val)) ws,
        ⌜i < sz⌝ -∗
        ⌜i = length vs⌝ -∗
        ⌜length vs = length ws⌝ -∗
        Ψ i vs o ws -∗
        match o with
        | None =>
            au_load t i (λ v,
              ▷ Ψ i vs (Some $ inl v) ws
            )
        | Some (inl v) =>
            WP fn v {{ w,
              ▷ Ψ i vs (Some $ inr (v, w)) ws
            }}
        | Some (inr (v, w)) =>
            au_store t i w (
              ▷ Ψ (S i) (vs ++ [v]) None (ws ++ [w])
            )
        end
      )
    }}}
      array_apply t fn
    {{{ vs ws,
      RET ();
      ⌜length vs = sz⌝ ∗
      ⌜length vs = length ws⌝ ∗
      Ψ sz vs None ws
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & HΨ & #H) HΦ".
    wp_rec.
    wp_smart_apply (array_applyi_spec_atomic Ψ with "[$Hinv $HΨ H] HΦ") as "!> %i %vs %o %ws %Hi1 %Hi2 %Hws HΨ".
    repeat case_match; try wp_pures; iApply ("H" with "[//] [//] [//] HΨ").
  Qed.
  Lemma array_apply_spec Ψ t vs fn :
    {{{
      ▷ Ψ 0 [] [] ∗
      array_model t (DfracOwn 1) vs ∗
      □ (
        ∀ i v ws,
        ⌜i = length ws⌝ -∗
        ⌜vs !! i = Some v⌝ -∗
        Ψ i (take i vs) ws -∗
        WP fn v {{ w,
          ▷ Ψ (S i) (take i vs ++ [v]) (ws ++ [w])
        }}
      )
    }}}
      array_apply t fn
    {{{ ws,
      RET ();
      ⌜length vs = length ws⌝ ∗
      array_model t (DfracOwn 1) ws ∗
      Ψ (length vs) vs ws
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hmodel & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (array_applyi_spec Ψ with "[$HΨ $Hmodel] HΦ") as "!> %i %v %ws %Hi %Hlookup HΨ".
    iSteps.
  Qed.
  Lemma array_apply_spec' Ψ t vs fn :
    {{{
      ▷ Ψ 0 [] [] ∗
      array_model t (DfracOwn 1) vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        ∀ ws,
        ⌜i = length ws⌝ -∗
        Ψ i (take i vs) ws -∗
        WP fn v {{ w,
          ▷ Ψ (S i) (take i vs ++ [v]) (ws ++ [w])
        }}
      )
    }}}
      array_apply t fn
    {{{ ws,
      RET ();
      ⌜length vs = length ws⌝ ∗
      array_model t (DfracOwn 1) ws ∗
      Ψ (length vs) vs ws
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hmodel & Hfn) HΦ".
    wp_rec.
    wp_smart_apply (array_applyi_spec' Ψ with "[$HΨ $Hmodel Hfn] HΦ").
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.
  Lemma array_apply_spec_disentangled Ψ t vs fn :
    {{{
      array_model t (DfracOwn 1) vs ∗
      □ (
        ∀ i v,
        ⌜vs !! i = Some v⌝ -∗
        WP fn v {{ w,
          ▷ Ψ i w
        }}
      )
    }}}
      array_apply t fn
    {{{ ws,
      RET ();
      ⌜length vs = length ws⌝ ∗
      array_model t (DfracOwn 1) ws ∗
      ( [∗ list] i ↦ w ∈ ws,
        Ψ i w
      )
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (array_applyi_spec_disentangled Ψ with "[$Hmodel] HΦ").
    iSteps.
  Qed.
  Lemma array_apply_spec_disentangled' Ψ t vs fn :
    {{{
      array_model t (DfracOwn 1) vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        WP fn v {{ w,
          ▷ Ψ i w
        }}
      )
    }}}
      array_apply t fn
    {{{ ws,
      RET ();
      array_model t (DfracOwn 1) ws ∗
      ( [∗ list] i ↦ w ∈ ws,
        Ψ i w
      )
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & Hfn) HΦ".
    wp_rec.
    wp_smart_apply (array_applyi_spec_disentangled' Ψ with "[$Hmodel Hfn] HΦ");
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.

  Lemma array_unsafe_initi_spec Ψ sz fn :
    (0 ≤ sz)%Z →
    {{{
      ▷ Ψ 0 [] ∗
      □ (
        ∀ i vs,
        ⌜i < Z.to_nat sz⌝ -∗
        ⌜i = length vs⌝ -∗
        Ψ i vs -∗
        WP fn #i {{ v, ▷
          Ψ (S i) (vs ++ [v])
        }}
      )
    }}}
      array_unsafe_initi #sz fn
    {{{ t vs,
      RET t;
      ⌜length vs = Z.to_nat sz⌝ ∗
      array_model t (DfracOwn 1) vs ∗
      Ψ (Z.to_nat sz) vs
    }}}.
  Proof.
    iIntros "%Hsz %Φ (HΨ & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (array_unsafe_alloc_spec with "[//]") as (t) "Hmodel"; first done.
    wp_pures.
    pose Ψ' i (_ : list val) vs := (
      Ψ i vs
    )%I.
    wp_apply (array_applyi_spec Ψ' with "[$Hmodel $HΨ]").
    { iSteps. iPureIntro.
      erewrite <- (length_replicate (Z.to_nat sz)). eapply lookup_lt_Some. done.
    }
    iIntros "%vs (%Hvs & Hmodel & HΨ)".
    rewrite length_replicate in Hvs |- *.
    wp_pures.
    iApply ("HΦ" $! _ vs).
    iSteps.
  Qed.
  Lemma array_unsafe_initi_spec' Ψ sz fn :
    (0 ≤ sz)%Z →
    {{{
      ▷ Ψ 0 [] ∗
      ( [∗ list] i ∈ seq 0 (Z.to_nat sz),
        ∀ vs,
        ⌜i = length vs⌝ -∗
        Ψ i vs -∗
        WP fn #i {{ v, ▷
          Ψ (S i) (vs ++ [v])
        }}
      )
    }}}
      array_unsafe_initi #sz fn
    {{{ t vs,
      RET t;
      ⌜length vs = Z.to_nat sz⌝ ∗
      array_model t (DfracOwn 1) vs ∗
      Ψ (Z.to_nat sz) vs
    }}}.
  Proof.
    iIntros "%Hsz %Φ (HΨ & Hfn) HΦ".
    match goal with |- context [big_opL bi_sep (λ _, ?Ξ') _] => set Ξ := Ξ' end.
    pose (Ψ' i vs := (
      Ψ i vs ∗
      [∗ list] j ∈ seq i (Z.to_nat sz - i), Ξ j
    )%I).
    wp_apply (array_unsafe_initi_spec Ψ' with "[$HΨ Hfn]"); [done | | iSteps].
    rewrite Nat.sub_0_r. iFrame. iIntros "!> %i %vs %Hi1 %Hi2 (HΨ & HΞ)".
    destruct (Nat.lt_exists_pred 0 (Z.to_nat sz - i)) as (k & Hk & _); first lia. rewrite Hk.
    rewrite -cons_seq. iDestruct "HΞ" as "(Hfn & HΞ)".
    wp_apply (wp_wand with "(Hfn [//] HΨ)"). iSteps.
    rewrite Nat.sub_succ_r Hk //.
  Qed.
  Lemma array_unsafe_initi_spec_disentangled Ψ sz fn :
    (0 ≤ sz)%Z →
    {{{
      □ (
        ∀ i,
        ⌜i < Z.to_nat sz⌝ -∗
        WP fn #i {{ v, ▷
          Ψ i v
        }}
      )
    }}}
      array_unsafe_initi #sz fn
    {{{ t vs,
      RET t;
      ⌜length vs = Z.to_nat sz⌝ ∗
      array_model t (DfracOwn 1) vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Hsz %Φ #Hfn HΦ".
    pose (Ψ' i vs := (
      [∗ list] j ↦ v ∈ vs, Ψ j v
    )%I).
    wp_apply (array_unsafe_initi_spec Ψ'); [done | | iSteps].
    rewrite /Ψ'. iSteps.
    rewrite big_sepL_snoc. iSteps.
  Qed.
  Lemma array_unsafe_initi_spec_disentangled' Ψ sz fn :
    (0 ≤ sz)%Z →
    {{{
      ( [∗ list] i ∈ seq 0 (Z.to_nat sz),
        WP fn #i {{ v, ▷
          Ψ i v
        }}
      )
    }}}
      array_unsafe_initi #sz fn
    {{{ t vs,
      RET t;
      ⌜length vs = Z.to_nat sz⌝ ∗
      array_model t (DfracOwn 1) vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Hsz %Φ Hfn HΦ".
    pose (Ψ' i vs := (
      [∗ list] j ↦ v ∈ vs, Ψ j v
    )%I).
    wp_apply (array_unsafe_initi_spec' Ψ' with "[Hfn]"); [done | | iSteps].
    rewrite /Ψ'. iSteps.
    iApply (big_sepL_impl with "Hfn").
    iSteps. rewrite big_sepL_snoc. iSteps.
  Qed.

  Lemma array_initi_spec Ψ sz fn :
    {{{
      ▷ Ψ 0 [] ∗
      □ (
        ∀ i vs,
        ⌜i < Z.to_nat sz⌝ -∗
        ⌜i = length vs⌝ -∗
        Ψ i vs -∗
        WP fn #i {{ v, ▷
          Ψ (S i) (vs ++ [v])
        }}
      )
    }}}
      array_initi #sz fn
    {{{ t vs,
      RET t;
      ⌜0 ≤ sz⌝%Z ∗
      ⌜length vs = Z.to_nat sz⌝ ∗
      array_model t (DfracOwn 1) vs ∗
      Ψ (Z.to_nat sz) vs
    }}}.
  Proof.
    iIntros "%Φ (HΨ & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply assume_spec' as "%Hsz".
    wp_smart_apply (array_unsafe_initi_spec Ψ with "[$HΨ $Hfn]"); first done.
    iSteps.
  Qed.
  Lemma array_initi_spec' Ψ sz fn :
    {{{
      ▷ Ψ 0 [] ∗
      ( [∗ list] i ∈ seq 0 (Z.to_nat sz),
        ∀ vs,
        ⌜i = length vs⌝ -∗
        Ψ i vs -∗
        WP fn #i {{ v, ▷
          Ψ (S i) (vs ++ [v])
        }}
      )
    }}}
      array_initi #sz fn
    {{{ t vs,
      RET t;
      ⌜0 ≤ sz⌝%Z ∗
      ⌜length vs = Z.to_nat sz⌝ ∗
      array_model t (DfracOwn 1) vs ∗
      Ψ (Z.to_nat sz) vs
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hfn) HΦ".
    wp_rec.
    wp_smart_apply assume_spec' as "%Hsz".
    wp_smart_apply (array_unsafe_initi_spec' Ψ with "[$HΨ $Hfn]"); first done.
    iSteps.
  Qed.
  Lemma array_initi_spec_disentangled Ψ sz fn :
    {{{
      □ (
        ∀ i,
        ⌜i < Z.to_nat sz⌝ -∗
        WP fn #i {{ v, ▷
          Ψ i v
        }}
      )
    }}}
      array_initi #sz fn
    {{{ t vs,
      RET t;
      ⌜0 ≤ sz⌝%Z ∗
      ⌜length vs = Z.to_nat sz⌝ ∗
      array_model t (DfracOwn 1) vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Φ #Hfn HΦ".
    wp_rec.
    wp_smart_apply assume_spec' as "%Hsz".
    wp_smart_apply (array_unsafe_initi_spec_disentangled Ψ with "Hfn"); first done.
    iSteps.
  Qed.
  Lemma array_initi_spec_disentangled' Ψ sz fn :
    {{{
      ( [∗ list] i ∈ seq 0 (Z.to_nat sz),
        WP fn #i {{ v, ▷
          Ψ i v
        }}
      )
    }}}
      array_initi #sz fn
    {{{ t vs,
      RET t;
      ⌜0 ≤ sz⌝%Z ∗
      ⌜length vs = Z.to_nat sz⌝ ∗
      array_model t (DfracOwn 1) vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Φ Hfn HΦ".
    wp_rec.
    wp_smart_apply assume_spec' as "%Hsz".
    wp_smart_apply (array_unsafe_initi_spec_disentangled' Ψ with "Hfn"); first done.
    iSteps.
  Qed.

  Lemma array_unsafe_init_spec Ψ sz fn :
    (0 ≤ sz)%Z →
    {{{
      ▷ Ψ 0 [] ∗
      □ (
        ∀ i vs,
        ⌜i < Z.to_nat sz⌝ -∗
        ⌜i = length vs⌝ -∗
        Ψ i vs -∗
        WP fn () {{ v, ▷
          Ψ (S i) (vs ++ [v])
        }}
      )
    }}}
      array_unsafe_init #sz fn
    {{{ t vs,
      RET t;
      ⌜length vs = Z.to_nat sz⌝ ∗
      array_model t (DfracOwn 1) vs ∗
      Ψ (Z.to_nat sz) vs
    }}}.
  Proof.
    iIntros "%Hsz %Φ (HΨ & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (array_unsafe_initi_spec Ψ with "[$HΨ] HΦ"); first done.
    iSteps.
  Qed.
  Lemma array_unsafe_init_spec' Ψ sz fn :
    (0 ≤ sz)%Z →
    {{{
      ▷ Ψ 0 [] ∗
      ( [∗ list] i ∈ seq 0 (Z.to_nat sz),
        ∀ vs,
        ⌜i = length vs⌝ -∗
        Ψ i vs -∗
        WP fn () {{ v, ▷
          Ψ (S i) (vs ++ [v])
        }}
      )
    }}}
      array_unsafe_init #sz fn
    {{{ t vs,
      RET t;
      ⌜length vs = Z.to_nat sz⌝ ∗
      array_model t (DfracOwn 1) vs ∗
      Ψ (Z.to_nat sz) vs
    }}}.
  Proof.
    iIntros "%Hsz %Φ (HΨ & Hfn) HΦ".
    wp_rec.
    wp_smart_apply (array_unsafe_initi_spec' Ψ with "[$HΨ Hfn] HΦ"); first done.
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.
  Lemma array_unsafe_init_spec_disentangled Ψ sz fn :
    (0 ≤ sz)%Z →
    {{{
      □ (
        ∀ i,
        ⌜i < Z.to_nat sz⌝ -∗
        WP fn () {{ v, ▷
          Ψ i v
        }}
      )
    }}}
      array_unsafe_init #sz fn
    {{{ t vs,
      RET t;
      ⌜length vs = Z.to_nat sz⌝ ∗
      array_model t (DfracOwn 1) vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Hsz %Φ #Hfn HΦ".
    wp_rec.
    wp_smart_apply (array_unsafe_initi_spec_disentangled Ψ with "[] HΦ"); first done.
    iSteps.
  Qed.
  Lemma array_unsafe_init_spec_disentangled' Ψ sz fn :
    (0 ≤ sz)%Z →
    {{{
      ( [∗ list] i ∈ seq 0 (Z.to_nat sz),
        WP fn () {{ v, ▷
          Ψ i v
        }}
      )
    }}}
      array_unsafe_init #sz fn
    {{{ t vs,
      RET t;
      ⌜length vs = Z.to_nat sz⌝ ∗
      array_model t (DfracOwn 1) vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Hsz %Φ Hfn HΦ".
    wp_rec.
    wp_smart_apply (array_unsafe_initi_spec_disentangled' Ψ with "[Hfn] HΦ"); first done.
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.

  Lemma array_init_spec Ψ sz fn :
    {{{
      ▷ Ψ 0 [] ∗
      □ (
        ∀ i vs,
        ⌜i < Z.to_nat sz⌝ -∗
        ⌜i = length vs⌝ -∗
        Ψ i vs -∗
        WP fn () {{ v, ▷
          Ψ (S i) (vs ++ [v])
        }}
      )
    }}}
      array_init #sz fn
    {{{ t vs,
      RET t;
      ⌜0 ≤ sz⌝%Z ∗
      ⌜length vs = Z.to_nat sz⌝ ∗
      array_model t (DfracOwn 1) vs ∗
      Ψ (Z.to_nat sz) vs
    }}}.
  Proof.
    iIntros "%Φ (HΨ & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply assume_spec' as "%Hsz".
    wp_smart_apply (array_unsafe_init_spec Ψ with "[$HΨ $Hfn]"); first done.
    iSteps.
  Qed.
  Lemma array_init_spec' Ψ sz fn :
    {{{
      ▷ Ψ 0 [] ∗
      ( [∗ list] i ∈ seq 0 (Z.to_nat sz),
        ∀ vs,
        ⌜i = length vs⌝ -∗
        Ψ i vs -∗
        WP fn () {{ v, ▷
          Ψ (S i) (vs ++ [v])
        }}
      )
    }}}
      array_init #sz fn
    {{{ t vs,
      RET t;
      ⌜0 ≤ sz⌝%Z ∗
      ⌜length vs = Z.to_nat sz⌝ ∗
      array_model t (DfracOwn 1) vs ∗
      Ψ (Z.to_nat sz) vs
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hfn) HΦ".
    wp_rec.
    wp_smart_apply assume_spec' as "%Hsz".
    wp_smart_apply (array_unsafe_init_spec' Ψ with "[$HΨ $Hfn]"); first done.
    iSteps.
  Qed.
  Lemma array_init_spec_disentangled Ψ sz fn :
    {{{
      □ (
        ∀ i,
        ⌜i < Z.to_nat sz⌝ -∗
        WP fn () {{ v, ▷
          Ψ i v
        }}
      )
    }}}
      array_init #sz fn
    {{{ t vs,
      RET t;
      ⌜0 ≤ sz⌝%Z ∗
      ⌜length vs = Z.to_nat sz⌝ ∗
      array_model t (DfracOwn 1) vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Φ #Hfn HΦ".
    wp_rec.
    wp_smart_apply assume_spec' as "%Hsz".
    wp_smart_apply (array_unsafe_init_spec_disentangled Ψ with "Hfn"); first done.
    iSteps.
  Qed.
  Lemma array_init_spec_disentangled' Ψ sz fn :
    {{{
      ( [∗ list] i ∈ seq 0 (Z.to_nat sz),
        WP fn () {{ v, ▷
          Ψ i v
        }}
      )
    }}}
      array_init #sz fn
    {{{ t vs,
      RET t;
      ⌜0 ≤ sz⌝%Z ∗
      ⌜length vs = Z.to_nat sz⌝ ∗
      array_model t (DfracOwn 1) vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Φ Hfn HΦ".
    wp_rec.
    wp_smart_apply assume_spec' as "%Hsz".
    wp_smart_apply (array_unsafe_init_spec_disentangled' Ψ with "Hfn"); first done.
    iSteps.
  Qed.

  Lemma array_mapi_spec_atomic Ψ t sz fn :
    {{{
      array_inv t sz ∗
      ▷ Ψ 0 [] None [] ∗
      □ (
        ∀ i vs (o : option val) ws,
        ⌜i < sz⌝ -∗
        ⌜i = length vs⌝ -∗
        ⌜length vs = length ws⌝ -∗
        Ψ i vs o ws -∗
        match o with
        | None =>
            au_load t i (λ v,
              ▷ Ψ i vs (Some v) ws
            )
        | Some v =>
            WP fn #i v {{ w,
              ▷ Ψ (S i) (vs ++ [v]) None (ws ++ [w])
            }}
        end
      )
    }}}
      array_mapi t fn
    {{{ t' vs ws,
      RET t';
      ⌜length vs = sz⌝ ∗
      ⌜length vs = length ws⌝ ∗
      array_model t' (DfracOwn 1) ws ∗
      Ψ sz vs None ws
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & HΨ & #H) HΦ".
    wp_rec.
    pose Ψ' i ws := (
      ∃ vs,
      ⌜length vs = length ws⌝ ∗
      Ψ i vs None ws
    )%I.
    wp_smart_apply (array_size_spec_inv with "Hinv") as "_".
    wp_apply (array_unsafe_initi_spec Ψ' with "[HΨ]") as "%t' %ws (%Hws & Hmodel & (%vs & %Hvs & HΨ))"; first lia.
    { iSplit. { iExists []. iSteps. }
      iIntros "!> %i %ws %Hi1 %Hi2 (%vs & %Hvs & HΨ)".
      iDestruct ("H" with "[%] [%] [//] HΨ") as "H'"; [lia.. |].
      awp_smart_apply (array_unsafe_get_spec_atomic_cell with "[//]").
      iApply (aacc_aupd_commit with "H'"); first done. iIntros "%dq %v Hslice".
      rewrite /atomic_acc /= Nat2Z.id.
      iStep 2; first iSteps. iIntros "$ !> HΨ !> H£".
      iMod (lc_fupd_elim_later with "H£ HΨ") as "HΨ".
      wp_apply (wp_wand with "(H [%] [%] [//] HΨ)") as (w) "HΨ"; [lia.. |].
      iExists (vs ++ [v]). rewrite !length_app. iSteps.
    }
    rewrite Nat2Z.id.
    iApply ("HΦ" with "[$Hmodel $HΨ]").
    iSteps.
  Qed.
  Lemma array_mapi_spec Ψ t dq vs fn :
    {{{
      ▷ Ψ 0 [] [] ∗
      array_model t dq vs ∗
      □ (
        ∀ i v ws,
        ⌜vs !! i = Some v⌝ -∗
        ⌜i = length ws⌝ -∗
        Ψ i (take i vs) ws -∗
        WP fn #i v {{ w,
          ▷ Ψ (S i) (take i vs ++ [v]) (ws ++ [w])
        }}
      )
    }}}
      array_mapi t fn
    {{{ t' ws,
      RET t';
      ⌜length ws = length vs⌝ ∗
      array_model t dq vs ∗
      array_model t' (DfracOwn 1) ws ∗
      Ψ (length vs) vs ws
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hmodel & #Hfn) HΦ".
    iDestruct (array_model_to_inv with "Hmodel") as "#Hinv".
    pose (Ψ' i vs_left o ws := (
      ⌜vs_left = take i vs⌝ ∗
      array_model t dq vs ∗
      Ψ i vs_left ws ∗
      ⌜from_option (λ v, v = vs !!! i) True o⌝%I
    )%I).
    wp_apply (array_mapi_spec_atomic Ψ' with "[$Hinv $HΨ $Hmodel]") as "%t' %vs_left %ws (%Hvs_left & %Hws & Hmodel' & (-> & Hmodel & HΨ & _))".
    { iStep.
      iIntros "!> %i %vs_left %o %ws %Hi1 %Hi2 %Hws (-> & Hmodel & HΨ & %Ho)".
      opose proof* (list_lookup_lookup_total_lt vs i); first lia.
      destruct o as [v |].
      - rewrite Ho.
        wp_apply (wp_wand with "(Hfn [//] [] HΨ)") as "%w HΨ"; first iSteps. iFrame.
        erewrite take_S_r => //.
      - iDestruct (array_model_lookup_acc i with "Hmodel") as "(H↦ & Hmodel)"; first done.
        iAuIntro. iAaccIntro with "H↦"; iSteps.
    }
    rewrite /Ψ' firstn_all2 in Hws |- *; first lia.
    apply symmetry in Hws.
    iSteps.
  Qed.
  Lemma array_mapi_spec' Ψ t dq vs fn :
    {{{
      ▷ Ψ 0 [] [] ∗
      array_model t dq vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        ∀ ws,
        ⌜i = length ws⌝ -∗
        Ψ i (take i vs) ws -∗
        WP fn #i v {{ w,
          ▷ Ψ (S i) (take i vs ++ [v]) (ws ++ [w])
        }}
      )
    }}}
      array_mapi t fn
    {{{ t' ws,
      RET t';
      ⌜length ws = length vs⌝ ∗
      array_model t dq vs ∗
      array_model t' (DfracOwn 1) ws ∗
      Ψ (length vs) vs ws
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hmodel & Hfn) HΦ".
    match goal with |- context [big_opL bi_sep ?Ξ' _] => set Ξ := Ξ' end.
    pose (Ψ' i vs_left ws := (
      Ψ i vs_left ws ∗
      [∗ list] j ↦ v ∈ drop i vs, Ξ (i + j) v
    )%I).
    wp_apply (array_mapi_spec Ψ' with "[$HΨ $Hmodel $Hfn]"); last iSteps.
    iIntros "!> %i %v %ws %Hlookup %Hi (HΨ & HΞ)".
    erewrite drop_S => //.
    iDestruct "HΞ" as "(Hfn & HΞ)".
    rewrite Nat.add_0_r. setoid_rewrite Nat.add_succ_r. iSteps.
  Qed.
  Lemma array_mapi_spec_disentangled Ψ t dq vs fn :
    {{{
      array_model t dq vs ∗
      □ (
        ∀ i v,
        ⌜vs !! i = Some v⌝ -∗
        WP fn #i v {{ w,
          ▷ Ψ i v w
        }}
      )
    }}}
      array_mapi t fn
    {{{ t' ws,
      RET t';
      ⌜length ws = length vs⌝ ∗
      array_model t dq vs ∗
      array_model t' (DfracOwn 1) ws ∗
      ( [∗ list] i ↦ v; w ∈ vs; ws,
        Ψ i v w
      )
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & #Hfn) HΦ".
    pose Ψ' i vs_left ws := (
      [∗ list] j ↦ v; w ∈ vs_left; ws, Ψ j v w
    )%I.
    wp_apply (array_mapi_spec Ψ' with "[$Hmodel]"); last iSteps.
    rewrite /Ψ'. iSteps.
    rewrite big_sepL2_snoc length_take Nat.min_l; last iSteps.
    eapply Nat.lt_le_incl, lookup_lt_Some. done.
  Qed.
  Lemma array_mapi_spec_disentangled' Ψ t dq vs fn :
    {{{
      array_model t dq vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        WP fn #i v {{ w,
          ▷ Ψ i v w
        }}
      )
    }}}
      array_mapi t fn
    {{{ t' ws,
      RET t';
      ⌜length ws = length vs⌝ ∗
      array_model t dq vs ∗
      array_model t' (DfracOwn 1) ws ∗
      ( [∗ list] i ↦ v; w ∈ vs; ws,
        Ψ i v w
      )
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & Hfn) HΦ".
    pose Ψ' i vs_left ws := (
      [∗ list] j ↦ v; w ∈ vs_left; ws, Ψ j v w
    )%I.
    wp_apply (array_mapi_spec' Ψ' with "[$Hmodel Hfn]"); last iSteps.
    rewrite /Ψ'. iSteps.
    iApply (big_sepL_impl with "Hfn"). iSteps.
    rewrite big_sepL2_snoc length_take Nat.min_l; last iSteps.
    eapply Nat.lt_le_incl, lookup_lt_Some. done.
  Qed.

  Lemma array_map_spec_atomic Ψ t sz fn :
    {{{
      array_inv t sz ∗
      ▷ Ψ 0 [] None [] ∗
      □ (
        ∀ i vs (o : option val) ws,
        ⌜i < Z.to_nat sz⌝ -∗
        ⌜i = length vs⌝ -∗
        ⌜length vs = length ws⌝ -∗
        Ψ i vs o ws -∗
        match o with
        | None =>
            au_load t i (λ v,
              ▷ Ψ i vs (Some v) ws
            )
        | Some v =>
            WP fn v {{ w,
              ▷ Ψ (S i) (vs ++ [v]) None (ws ++ [w])
            }}
        end
      )
    }}}
      array_map t fn
    {{{ t' vs ws,
      RET t';
      ⌜length vs = sz⌝ ∗
      ⌜length vs = length ws⌝ ∗
      array_model t' (DfracOwn 1) ws ∗
      Ψ sz vs None ws
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & HΨ & #H) HΦ".
    wp_rec.
    wp_smart_apply (array_mapi_spec_atomic Ψ with "[$Hinv $HΨ H] HΦ") as "!> %i %vs %o %ws %Hi1 %Hi2 %Hws HΨ".
    case_match; try wp_pures; iApply ("H" with "[%] [%] [//] HΨ"); lia.
  Qed.
  Lemma array_map_spec Ψ t dq vs fn :
    {{{
      ▷ Ψ 0 [] [] ∗
      array_model t dq vs ∗
      □ (
        ∀ i v ws,
        ⌜vs !! i = Some v⌝ -∗
        ⌜i = length ws⌝ -∗
        Ψ i (take i vs) ws -∗
        WP fn v {{ w,
          ▷ Ψ (S i) (take i vs ++ [v]) (ws ++ [w])
        }}
      )
    }}}
      array_map t fn
    {{{ t' ws,
      RET t';
      ⌜length ws = length vs⌝ ∗
      array_model t dq vs ∗
      array_model t' (DfracOwn 1) ws ∗
      Ψ (length vs) vs ws
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hmodel & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (array_mapi_spec Ψ with "[$HΨ $Hmodel] HΦ").
    iSteps.
  Qed.
  Lemma array_map_spec' Ψ t dq vs fn :
    {{{
      ▷ Ψ 0 [] [] ∗
      array_model t dq vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        ∀ ws,
        ⌜i = length ws⌝ -∗
        Ψ i (take i vs) ws -∗
        WP fn v {{ w,
          ▷ Ψ (S i) (take i vs ++ [v]) (ws ++ [w])
        }}
      )
    }}}
      array_map t fn
    {{{ t' ws,
      RET t';
      ⌜length ws = length vs⌝ ∗
      array_model t dq vs ∗
      array_model t' (DfracOwn 1) ws ∗
      Ψ (length vs) vs ws
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hmodel & Hfn) HΦ".
    wp_rec.
    wp_smart_apply (array_mapi_spec' Ψ with "[$HΨ $Hmodel Hfn] HΦ").
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.
  Lemma array_map_spec_disentangled Ψ t dq vs fn :
    {{{
      array_model t dq vs ∗
      □ (
        ∀ i v,
        ⌜vs !! i = Some v⌝ -∗
        WP fn v {{ w,
          ▷ Ψ i v w
        }}
      )
    }}}
      array_map t fn
    {{{ t' ws,
      RET t';
      ⌜length ws = length vs⌝ ∗
      array_model t dq vs ∗
      array_model t' (DfracOwn 1) ws ∗
      ( [∗ list] i ↦ v; w ∈ vs; ws,
        Ψ i v w
      )
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (array_mapi_spec_disentangled Ψ with "[$Hmodel] HΦ").
    iSteps.
  Qed.
  Lemma array_map_spec_disentangled' Ψ t dq vs fn :
    {{{
      array_model t dq vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        WP fn v {{ w,
          ▷ Ψ i v w
        }}
      )
    }}}
      array_map t fn
    {{{ t' ws,
      RET t';
      ⌜length ws = length vs⌝ ∗
      array_model t dq vs ∗
      array_model t' (DfracOwn 1) ws ∗
      ( [∗ list] i ↦ v; w ∈ vs; ws,
        Ψ i v w
      )
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & Hfn) HΦ".
    wp_rec.
    wp_smart_apply (array_mapi_spec_disentangled' Ψ with "[$Hmodel Hfn] HΦ").
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.

  Lemma array_unsafe_copy_slice_spec_atomic Ψ t1 (i1 : Z) t2 (i2 n : Z) :
    (0 ≤ i1)%Z →
    (0 ≤ i2)%Z →
    (0 ≤ n)%Z →
    {{{
      ▷ Ψ 0 [] None ∗
      □ (
        ∀ k vs o,
        ⌜k < Z.to_nat n⌝ -∗
        ⌜k = length vs⌝ -∗
        Ψ k vs o -∗
        match o with
        | None =>
            au_load t1 (Z.to_nat i1 + k) (λ v,
              ▷ Ψ k vs (Some v)
            )
        | Some v =>
            au_store t2 (Z.to_nat i2 + k) v (
              ▷ Ψ (S k) (vs ++ [v]) None
            )
        end
      )
    }}}
      array_unsafe_copy_slice t1 #i1 t2 #i2 #n
    {{{ vs,
      RET ();
      ⌜length vs = Z.to_nat n⌝ ∗
      Ψ (Z.to_nat n) vs None
    }}}.
  Proof.
    iIntros "%Hi1 %Hi2 %Hn %Φ (HΨ & #H) HΦ".
    wp_rec.
    pose Ψ' (_ : Z) k := (
      ∃ vs,
      ⌜length vs = k⌝ ∗
      Ψ k vs None
    )%I.
    wp_smart_apply (for_spec_strong Ψ' with "[HΨ]").
    { iSplitL. { iExists []. iSteps. }
      iIntros "!> % %k -> %Hk (%vs & %Hvs & HΨ)".
      iDestruct ("H" with "[%] [//] HΨ") as "H'"; first lia.
      awp_smart_apply (array_unsafe_get_spec_atomic_cell with "[//]").
      iApply (aacc_aupd_commit with "H'"); first done. iIntros "%dq %v Hslice".
      rewrite /atomic_acc /=.
      repeat iExists _. iFrame. iStep 2; first iSteps. iIntros "Hslice !>".
      rewrite Z.add_0_l Z2Nat.inj_add; [lia.. |]. rewrite !Nat2Z.id. iFrame.
      iIntros "HΨ !> _".
      iDestruct ("H" with "[%] [//] HΨ") as "H'"; first lia.
      awp_smart_apply (array_unsafe_set_spec_atomic_cell with "[//]").
      iApply (aacc_aupd_commit with "H'"); first done. iIntros "%w Hslice".
      rewrite /atomic_acc /=.
      repeat iExists _. iFrame. iSteps.
      iExists (vs ++ [v]). rewrite length_app. iSteps.
    }
    rewrite Z.sub_0_r. iSteps.
  Qed.
  Lemma array_unsafe_copy_slice_spec_slice_fit t1 (i1 : Z) i1_ dq1 vs1 t2 (i2 : Z) i2_ vs2 (n : Z) :
    i1 = Z.of_nat i1_ →
    i2 = Z.of_nat i2_ →
    n = length vs1 →
    length vs1 = length vs2 →
    {{{
      array_slice t1 i1_ dq1 vs1 ∗
      array_slice t2 i2_ (DfracOwn 1) vs2
    }}}
      array_unsafe_copy_slice t1 #i1 t2 #i2 #n
    {{{
      RET ();
      array_slice t1 i1_ dq1 vs1 ∗
      array_slice t2 i2_ (DfracOwn 1) vs1
    }}}.
  Proof.
    iIntros (-> -> -> ?) "%Φ (Hslice1 & Hslice2) HΦ".
    pose (Ψ k vs1_done o := (
      ⌜vs1_done = take k vs1⌝ ∗
      array_slice t1 i1_ dq1 vs1 ∗
      array_slice t2 i2_ (DfracOwn 1) (vs1_done ++ drop k vs2) ∗
      ⌜from_option (λ v1, vs1 !! k = Some v1) True o⌝
    )%I).
    wp_apply (array_unsafe_copy_slice_spec_atomic Ψ with "[$Hslice1 $Hslice2]") as "%vs1_done (_ & (-> & Hslice1 & Hslice2 & _))"; [lia.. | |].
    { iStep.
      iIntros "!> %k %vs1_done %o %Hk _ (-> & Hslice1 & Hslice2 & %Hlookup)".
      rewrite !Nat2Z.id.
      opose proof* (list_lookup_lookup_total_lt vs2 k); first lia.
      destruct o as [v1 |].
      - opose proof* (list_lookup_lookup_total_lt vs2 k); first lia.
        iDestruct (array_slice_update with "Hslice2") as "(H↦2 & Hslice2)".
        { rewrite lookup_app_r length_take Nat.min_l //; try lia.
          rewrite Nat.sub_diag lookup_drop right_id list_lookup_lookup_total_lt //. lia.
        }
        iAuIntro. iAaccIntro with "H↦2"; first iSteps. iIntros "H↦2".
        iDestruct ("Hslice2" with "H↦2") as "Hslice2".
        iFrame. iSplitR. { erewrite take_S_r => //. }
        rewrite insert_app_r_alt length_take Nat.min_l //; try lia.
        rewrite Nat.sub_diag. erewrite drop_S => //. rewrite -(assoc (++)).
        iSteps.
      - opose proof* (list_lookup_lookup_total_lt vs1 k); first lia.
        iDestruct (array_slice_lookup_acc k with "Hslice1") as "(H↦1 & Hslice1)"; first done.
        iAuIntro. iAaccIntro with "H↦1"; iSteps.
    }
    iApply ("HΦ" with "[$Hslice1 Hslice2]").
    rewrite firstn_all2; first lia. rewrite skipn_all2; first lia. rewrite right_id //.
  Qed.
  Lemma array_unsafe_copy_slice_spec_slice t1 i1 (j1 : Z) dq1 vs1 t2 i2 (j2 : Z) vs2 (n : Z) :
    (i1 ≤ j1)%Z →
    (i2 ≤ j2)%Z →
    (0 ≤ n)%Z →
    (j1 + n ≤ i1 + length vs1)%Z →
    (j2 + n ≤ i2 + length vs2)%Z →
    {{{
      array_slice t1 i1 dq1 vs1 ∗
      array_slice t2 i2 (DfracOwn 1) vs2
    }}}
      array_unsafe_copy_slice t1 #j1 t2 #j2 #n
    {{{
      RET ();
      array_slice t1 i1 dq1 vs1 ∗
      array_slice t2 i2 (DfracOwn 1) (
        take (Z.to_nat j2 - i2) vs2 ++
        take (Z.to_nat n) (drop (Z.to_nat j1 - i1) vs1) ++
        drop (Z.to_nat j2 - i2 + Z.to_nat n) vs2
      )
    }}}.
  Proof.
    iIntros "% % % % % %Φ (Hslice1 & Hslice2) HΦ".
    Z_to_nat j1. Z_to_nat j2. Z_to_nat n. rewrite !Nat2Z.id.
    rewrite (Nat.le_add_sub i1 j1); first lia. set k1 := j1 - i1.
    rewrite (Nat.le_add_sub i2 j2); first lia. set k2 := j2 - i2.
    rewrite -{1 2}(take_drop k1 vs1) -(take_drop n (drop k1 vs1)).
    rewrite -{1}(take_drop k2 vs2) -(take_drop n (drop k2 vs2)).
    rewrite !drop_drop.
    iDestruct (array_slice_app3_2 with "Hslice1") as "(Hslice11 & Hslice12 & Hslice13)"; first done.
    iDestruct (array_slice_app3_2 with "Hslice2") as "(Hslice21 & Hslice22 & Hslice23)"; first done.
    rewrite !length_take !length_drop !Nat.min_l; [lia.. |].
    wp_apply (array_unsafe_copy_slice_spec_slice_fit with "[$Hslice12 $Hslice22]") as "(Hslice12 & Hslice22)"; try lia.
    { rewrite length_take length_drop. lia. }
    { rewrite !length_take !length_drop. lia. }
    iApply "HΦ".
    iDestruct (array_slice_app3_1 with "Hslice11 Hslice12 Hslice13") as "$"; [rewrite !length_take ?length_drop; lia.. |].
    iDestruct (array_slice_app3_1 with "Hslice21 Hslice22 Hslice23") as "Hslice2"; [rewrite !length_take ?length_drop; lia.. |].
    rewrite -!Nat.le_add_sub //; lia.
  Qed.
  Lemma array_unsafe_copy_slice_spec t1 (i1 : Z) dq1 vs1 t2 (i2 : Z) vs2 (n : Z) :
    (0 ≤ i1)%Z →
    (0 ≤ i2)%Z →
    (0 ≤ n)%Z →
    (i1 + n ≤ length vs1)%Z →
    (i2 + n ≤ length vs2)%Z →
    {{{
      array_model t1 dq1 vs1 ∗
      array_model t2 (DfracOwn 1) vs2
    }}}
      array_unsafe_copy_slice t1 #i1 t2 #i2 #n
    {{{
      RET ();
      array_model t1 dq1 vs1 ∗
      array_model t2 (DfracOwn 1) (
        take (Z.to_nat i2) vs2 ++
        take (Z.to_nat n) (drop (Z.to_nat i1) vs1) ++
        drop (Z.to_nat i2 + Z.to_nat n) vs2
      )
    }}}.
  Proof.
    iIntros "% % % % % %Φ (Hmodel1 & Hmodel2) HΦ".
    iDestruct (array_model_to_slice' with "Hmodel1") as "(Hslice1 & #?)".
    iDestruct (array_model_to_slice' with "Hmodel2") as "(Hslice2 & #?)".
    wp_apply (array_unsafe_copy_slice_spec_slice with "[$Hslice1 $Hslice2]") as "(Hslice1 & Hslice2)"; [lia.. |].
    rewrite !Nat.sub_0_r. iSteps. iPureIntro.
    rewrite !length_app !length_take !length_drop. lia.
  Qed.

  Lemma array_copy_slice_spec_slice_fit t1 sz1 (i1 : Z) i1_ dq1 vs1 t2 sz2 (i2 : Z) i2_ vs2 (n : Z) :
    i1_ = Z.to_nat i1 →
    i2_ = Z.to_nat i2 →
    {{{
      array_inv t1 sz1 ∗
      array_inv t2 sz2 ∗
      ( ⌜0 ≤ i1⌝%Z -∗
        ⌜0 ≤ i2⌝%Z -∗
        ⌜0 ≤ n⌝%Z -∗
        ⌜i1 + n ≤ sz1⌝%Z -∗
        ⌜i2 + n ≤ sz2⌝%Z -∗
          ⌜Z.to_nat n = length vs1⌝ ∗
          ⌜length vs1 = length vs2⌝ ∗
          array_slice t1 i1_ dq1 vs1 ∗
          array_slice t2 i2_ (DfracOwn 1) vs2
      )
    }}}
      array_copy_slice t1 #i1 t2 #i2 #n
    {{{
      RET ();
      ⌜0 ≤ i1⌝%Z ∗
      ⌜0 ≤ i2⌝%Z ∗
      ⌜0 ≤ n⌝%Z ∗
      ⌜i1 + n ≤ sz1⌝%Z ∗
      ⌜i2 + n ≤ sz2⌝%Z ∗
      array_slice t1 i1_ dq1 vs1 ∗
      array_slice t2 i2_ (DfracOwn 1) vs1
    }}}.
  Proof.
    iIntros (-> ->) "%Φ (#Hinv1 & #Hinv2 & H) HΦ".
    wp_rec.
    wp_smart_apply (array_size_spec_inv with "Hinv1") as "_".
    wp_smart_apply (array_size_spec_inv with "Hinv2") as "_".
    repeat (wp_smart_apply assume_spec' as "%").
    iDestruct ("H" with "[//] [//] [//] [//] [//]") as "(% & % & Hslice1 & Hslice2)".
    wp_smart_apply (array_unsafe_copy_slice_spec_slice_fit with "[$Hslice1 $Hslice2]"); [lia.. |].
    iSteps.
  Qed.
  Lemma array_copy_slice_spec_slice t1 sz1 i1 (j1 : Z) dq1 vs1 t2 sz2 i2 (j2 : Z) vs2 (n : Z) :
    {{{
      array_inv t1 sz1 ∗
      array_inv t2 sz2 ∗
      ( ⌜0 ≤ j1⌝%Z -∗
        ⌜0 ≤ j2⌝%Z -∗
        ⌜0 ≤ n⌝%Z -∗
        ⌜j1 + n ≤ sz1⌝%Z -∗
        ⌜j2 + n ≤ sz2⌝%Z -∗
          ⌜i1 ≤ Z.to_nat j1⌝ ∗
          ⌜i2 ≤ Z.to_nat j2⌝ ∗
          ⌜Z.to_nat j1 + n ≤ i1 + length vs1⌝%Z ∗
          ⌜Z.to_nat j2 + n ≤ i2 + length vs2⌝%Z ∗
          array_slice t1 i1 dq1 vs1 ∗
          array_slice t2 i2 (DfracOwn 1) vs2
      )
    }}}
      array_copy_slice t1 #j1 t2 #j2 #n
    {{{
      RET ();
      ⌜0 ≤ j1⌝%Z ∗
      ⌜0 ≤ j2⌝%Z ∗
      ⌜0 ≤ n⌝%Z ∗
      ⌜j1 + n ≤ sz1⌝%Z ∗
      ⌜j2 + n ≤ sz2⌝%Z ∗
      array_slice t1 i1 dq1 vs1 ∗
      array_slice t2 i2 (DfracOwn 1) (
        take (Z.to_nat j2 - i2) vs2 ++
        take (Z.to_nat n) (drop (Z.to_nat j1 - i1) vs1) ++
        drop (Z.to_nat j2 - i2 + Z.to_nat n) vs2
      )
    }}}.
  Proof.
    iIntros "%Φ (#Hinv1 & #Hinv2 & H) HΦ".
    wp_rec.
    wp_smart_apply (array_size_spec_inv with "Hinv1") as "_".
    wp_smart_apply (array_size_spec_inv with "Hinv2") as "_".
    repeat (wp_smart_apply assume_spec' as "%").
    iDestruct ("H" with "[//] [//] [//] [//] [//]") as "(% & % & % & % & Hslice1 & Hslice2)".
    wp_smart_apply (array_unsafe_copy_slice_spec_slice with "[$Hslice1 $Hslice2]"); [lia.. |].
    iSteps.
  Qed.
  Lemma array_copy_slice_spec t1 (i1 : Z) dq1 vs1 t2 (i2 : Z) vs2 (n : Z) :
    {{{
      array_model t1 dq1 vs1 ∗
      array_model t2 (DfracOwn 1) vs2
    }}}
      array_copy_slice t1 #i1 t2 #i2 #n
    {{{
      RET ();
      ⌜0 ≤ i1⌝%Z ∗
      ⌜0 ≤ i2⌝%Z ∗
      ⌜0 ≤ n⌝%Z ∗
      ⌜i1 + n ≤ length vs1⌝%Z ∗
      ⌜i2 + n ≤ length vs2⌝%Z ∗
      array_model t1 dq1 vs1 ∗
      array_model t2 (DfracOwn 1) (
        take (Z.to_nat i2) vs2 ++
        take (Z.to_nat n) (drop (Z.to_nat i1) vs1) ++
        drop (Z.to_nat i2 + Z.to_nat n) vs2
      )
    }}}.
  Proof.
    iIntros "%Φ (Hmodel1 & Hmodel2) HΦ".
    wp_rec.
    wp_smart_apply (array_size_spec with "Hmodel1") as "Hmodel1".
    wp_smart_apply (array_size_spec with "Hmodel2") as "Hmodel2".
    repeat (wp_smart_apply assume_spec' as "%").
    wp_smart_apply (array_unsafe_copy_slice_spec with "[$Hmodel1 $Hmodel2]"); [lia.. |].
    iSteps.
  Qed.

  Lemma array_unsafe_copy_spec_atomic Ψ t1 sz1 t2 sz2 (i2 : Z) :
    (0 ≤ i2)%Z →
    {{{
      array_inv t1 sz1 ∗
      array_inv t2 sz2 ∗
      ▷ Ψ 0 [] None ∗
      □ (
        ∀ k vs o,
        ⌜k < sz1⌝ -∗
        ⌜k = length vs⌝ -∗
        Ψ k vs o -∗
        match o with
        | None =>
            au_load t1 k (λ v,
              ▷ Ψ k vs (Some v)
            )
        | Some v =>
            au_store t2 (Z.to_nat i2 + k) v (
              ▷ Ψ (S k) (vs ++ [v]) None
            )
        end
      )
    }}}
      array_unsafe_copy t1 t2 #i2
    {{{ vs,
      RET ();
      ⌜length vs = sz1⌝ ∗
      Ψ sz1 vs None
    }}}.
  Proof.
    iIntros "% %Φ (#Hinv1 & #Hinv2 & HΨ & #H) HΦ".
    wp_rec.
    wp_smart_apply (array_size_spec_inv with "Hinv1") as "_".
    wp_apply (array_unsafe_copy_slice_spec_atomic Ψ with "[$HΨ]"); [lia.. | iSteps |].
    rewrite Nat2Z.id. iSteps.
  Qed.
  Lemma array_unsafe_copy_spec_slice_fit t1 dq1 vs1 t2 (i2 : Z) i2_ vs2 :
    i2 = Z.of_nat i2_ →
    length vs1 = length vs2 →
    {{{
      array_model t1 dq1 vs1 ∗
      array_slice t2 i2_ (DfracOwn 1) vs2
    }}}
      array_unsafe_copy t1 t2 #i2
    {{{
      RET ();
      array_model t1 dq1 vs1 ∗
      array_slice t2 i2_ (DfracOwn 1) vs1
    }}}.
  Proof.
    iIntros (-> ?) "%Φ (Hmodel1 & Hslice2) HΦ".
    wp_rec.
    wp_smart_apply (array_size_spec with "Hmodel1") as "Hmodel1".
    iDestruct (array_model_to_slice' with "Hmodel1") as "(Hslice1 & #?)".
    wp_apply (array_unsafe_copy_slice_spec_slice_fit with "[$Hslice1 $Hslice2]"); [done.. |].
    iSteps.
  Qed.
  Lemma array_unsafe_copy_spec_slice t1 dq1 vs1 t2 i2 (j2 : Z) vs2 :
    (i2 ≤ j2)%Z →
    (j2 + length vs1 ≤ i2 + length vs2)%Z →
    {{{
      array_model t1 dq1 vs1 ∗
      array_slice t2 i2 (DfracOwn 1) vs2
    }}}
      array_unsafe_copy t1 t2 #j2
    {{{
      RET ();
      array_model t1 dq1 vs1 ∗
      array_slice t2 i2 (DfracOwn 1) (
        take (Z.to_nat j2 - i2) vs2 ++
        vs1 ++
        drop (Z.to_nat j2 - i2 + length vs1) vs2
      )
    }}}.
  Proof.
    iIntros "% % %Φ (Hmodel1 & Hslice2) HΦ".
    wp_rec.
    wp_smart_apply (array_size_spec with "Hmodel1") as "Hmodel1".
    iDestruct (array_model_to_slice' with "Hmodel1") as "(Hslice1 & #?)".
    wp_apply (array_unsafe_copy_slice_spec_slice with "[$Hslice1 $Hslice2]"); [lia.. |].
    rewrite Nat2Z.id firstn_all /=. iSteps.
  Qed.
  Lemma array_unsafe_copy_spec t1 dq1 vs1 t2 (i2 : Z) vs2 :
    (0 ≤ i2)%Z →
    (i2 + length vs1 ≤ length vs2)%Z →
    {{{
      array_model t1 dq1 vs1 ∗
      array_model t2 (DfracOwn 1) vs2
    }}}
      array_unsafe_copy t1 t2 #i2
    {{{
      RET ();
      array_model t1 dq1 vs1 ∗
      array_model t2 (DfracOwn 1) (
        take (Z.to_nat i2) vs2 ++
        vs1 ++
        drop (Z.to_nat i2 + length vs1) vs2
      )
    }}}.
  Proof.
    iIntros "% % %Φ (Hmodel1 & Hmodel2) HΦ".
    wp_rec.
    wp_smart_apply (array_size_spec with "Hmodel1") as "Hmodel1".
    wp_apply (array_unsafe_copy_slice_spec with "[$Hmodel1 $Hmodel2]"); [lia.. |].
    rewrite Nat2Z.id firstn_all /=. iSteps.
  Qed.

  Lemma array_copy_spec_slice_fit t1 dq1 vs1 t2 sz2 (i2 : Z) i2_ vs2 :
    i2_ = Z.to_nat i2 →
    {{{
      array_model t1 dq1 vs1 ∗
      array_inv t2 sz2 ∗
      ( ⌜0 ≤ i2⌝%Z -∗
        ⌜i2 + length vs1 ≤ sz2⌝%Z -∗
          ⌜length vs1 = length vs2⌝ ∗
          array_slice t2 i2_ (DfracOwn 1) vs2
      )
    }}}
      array_copy t1 t2 #i2
    {{{
      RET ();
      ⌜0 ≤ i2⌝%Z ∗
      ⌜i2 + length vs1 ≤ sz2⌝%Z ∗
      array_model t1 dq1 vs1 ∗
      array_slice t2 i2_ (DfracOwn 1) vs1
    }}}.
  Proof.
    iIntros (->) "%Φ (Hmodel1 & #Hinv2 & H) HΦ".
    wp_rec.
    wp_smart_apply assume_spec' as "%".
    wp_smart_apply (array_size_spec_inv with "Hinv2") as "_".
    wp_smart_apply (array_size_spec with "Hmodel1") as "Hmodel1".
    wp_smart_apply assume_spec' as "%".
    iDestruct ("H" with "[//] [//]") as "(% & Hslice2)".
    wp_smart_apply (array_unsafe_copy_spec_slice_fit with "[$Hmodel1 $Hslice2]"); [lia.. |].
    iSteps.
  Qed.
  Lemma array_copy_spec_slice t1 dq1 vs1 t2 sz2 i2 (j2 : Z) vs2 :
    {{{
      array_model t1 dq1 vs1 ∗
      array_inv t2 sz2 ∗
      ( ⌜0 ≤ j2⌝%Z -∗
        ⌜j2 + length vs1 ≤ sz2⌝%Z -∗
          ⌜i2 ≤ j2⌝%Z ∗
          ⌜j2 + length vs1 ≤ i2 + length vs2⌝%Z ∗
          array_slice t2 i2 (DfracOwn 1) vs2
      )
    }}}
      array_copy t1 t2 #j2
    {{{
      RET ();
      ⌜0 ≤ i2⌝ ∗
      ⌜i2 + length vs1 ≤ sz2⌝ ∗
      array_model t1 dq1 vs1 ∗
      array_slice t2 i2 (DfracOwn 1) (
        take (Z.to_nat j2 - i2) vs2 ++
        vs1 ++
        drop (Z.to_nat j2 - i2 + length vs1) vs2
      )
    }}}.
  Proof.
    iIntros "%Φ (Hmodel1 & #Hinv2 & H) HΦ".
    wp_rec.
    wp_smart_apply assume_spec' as "%".
    wp_smart_apply (array_size_spec_inv with "Hinv2") as "_".
    wp_smart_apply (array_size_spec with "Hmodel1") as "Hmodel1".
    wp_smart_apply assume_spec' as "%".
    iDestruct ("H" with "[//] [//]") as "(% & % & Hslice2)".
    wp_smart_apply (array_unsafe_copy_spec_slice with "[$Hmodel1 $Hslice2]"); [lia.. |].
    iSteps.
  Qed.
  Lemma array_copy_spec t1 dq1 vs1 t2 (i2 : Z) vs2 :
    {{{
      array_model t1 dq1 vs1 ∗
      array_model t2 (DfracOwn 1) vs2
    }}}
      array_copy t1 t2 #i2
    {{{
      RET ();
      ⌜0 ≤ i2⌝%Z ∗
      ⌜i2 + length vs1 ≤ length vs2⌝%Z ∗
      array_model t1 dq1 vs1 ∗
      array_model t2 (DfracOwn 1) (
        take (Z.to_nat i2) vs2 ++
        vs1 ++
        drop (Z.to_nat i2 + length vs1) vs2
      )
    }}}.
  Proof.
    iIntros "%Φ (Hmodel1 & Hmodel2) HΦ".
    wp_rec.
    wp_smart_apply assume_spec' as "%".
    wp_smart_apply (array_size_spec with "Hmodel2") as "Hmodel2".
    wp_smart_apply (array_size_spec with "Hmodel1") as "Hmodel1".
    wp_smart_apply assume_spec' as "%".
    wp_smart_apply (array_unsafe_copy_spec with "[$Hmodel1 $Hmodel2]"); [lia.. |].
    iSteps.
  Qed.

  Lemma array_unsafe_grow_spec t dq vs sz' v' :
    (length vs ≤ sz')%Z →
    {{{
      array_model t dq vs
    }}}
      array_unsafe_grow t #sz' v'
    {{{ t',
      RET t';
      array_model t' (DfracOwn 1) (vs ++ replicate (Z.to_nat sz' - length vs) v')
    }}}.
  Proof.
    iIntros "%Hsz' %Φ Hmodel HΦ".
    wp_rec.
    wp_smart_apply (array_size_spec with "Hmodel") as "Hmodel".
    wp_smart_apply (array_unsafe_alloc_spec with "[//]") as "%t' Hmodel'"; first lia.
    iDestruct (array_model_to_slice' with "Hmodel'") as "(Hslice' & #?)".
    assert (Z.to_nat sz' = length vs + Z.to_nat (sz' - length vs)) as -> by lia.
    rewrite replicate_add.
    iDestruct (array_slice_app with "Hslice'") as "(Hslice1' & Hslice2')".
    wp_smart_apply (array_unsafe_copy_spec_slice with "[$Hmodel $Hslice1']") as "(Hmodel & Hslice1')"; first done.
    { rewrite length_replicate //. }
    wp_smart_apply (array_unsafe_fill_slice_spec with "Hslice2'") as "Hslice2'".
    { rewrite length_replicate //. }
    { rewrite length_replicate. lia. }
    iDestruct (array_slice_app_1' with "Hslice1' Hslice2'") as "Hslice'".
    { rewrite skipn_all2 length_replicate //= right_id //. }
    iSteps.
    - iPureIntro. rewrite !length_app !length_replicate. lia.
    - rewrite drop_replicate /= Nat.sub_diag right_id Nat.add_sub' //.
  Qed.

  Lemma array_grow_spec t dq vs sz' v' :
    {{{
      array_model t dq vs
    }}}
      array_grow t #sz' v'
    {{{ t',
      RET t';
      ⌜length vs ≤ sz'⌝%Z ∗
      array_model t' (DfracOwn 1) (vs ++ replicate (Z.to_nat sz' - length vs) v')
    }}}.
  Proof.
    iIntros "%Φ Hmodel HΦ".
    wp_rec.
    wp_smart_apply (array_size_spec with "Hmodel") as "Hmodel".
    wp_smart_apply assume_spec' as "%".
    wp_smart_apply (array_unsafe_grow_spec with "Hmodel"); first done.
    iSteps.
  Qed.

  Lemma array_unsafe_sub_spec_slice_fit t dq vs (i : Z) i_ (n : Z) :
    i = Z.of_nat i_ →
    n = length vs →
    {{{
      array_slice t i_ dq vs
    }}}
      array_unsafe_sub t #i #n
    {{{ t',
      RET t';
      array_slice t i_ dq vs ∗
      array_model t' (DfracOwn 1) (take (Z.to_nat n) vs)
    }}}.
  Proof.
    iIntros (-> ->) "%Φ Hslice HΦ".
    wp_rec.
    wp_smart_apply (array_unsafe_alloc_spec with "[//]") as (t') "Hmodel'"; first lia.
    iDestruct (array_model_to_slice' with "Hmodel'") as "(Hslice' & #?)".
    wp_smart_apply (array_unsafe_copy_slice_spec_slice_fit with "[$Hslice $Hslice']"); [done.. | |].
    { rewrite length_replicate. lia. }
    iSteps.
    - iPureIntro. rewrite length_replicate length_take. lia.
    - rewrite firstn_all2 //. lia.
  Qed.
  Lemma array_unsafe_sub_spec_slice t dq vs i (j n : Z) :
    (i ≤ j)%Z →
    (0 ≤ n)%Z →
    (j + n ≤ i + length vs)%Z →
    {{{
      array_slice t i dq vs
    }}}
      array_unsafe_sub t #j #n
    {{{ t',
      RET t';
      array_slice t i dq vs ∗
      array_model t' (DfracOwn 1) (take (Z.to_nat n) (drop (Z.to_nat j - Z.to_nat i) vs))
    }}}.
  Proof.
    iIntros "% % % %Φ Hslice HΦ".
    Z_to_nat j. Z_to_nat n. rewrite !Nat2Z.id.
    rewrite (Nat.le_add_sub i j); first lia. set k := j - i.
    rewrite -{1 2}(take_drop k vs) -(take_drop n (drop k vs)).
    rewrite !drop_drop.
    iDestruct (array_slice_app3_2 with "Hslice") as "(Hslice1 & Hslice2 & Hslice3)"; first done.
    rewrite !length_take !length_drop !Nat.min_l; [lia.. |].
    wp_apply (array_unsafe_sub_spec_slice_fit with "Hslice2") as "%t' (Hslice2 & Hmodel')"; try lia.
    { rewrite length_take length_drop. lia. }
    iApply "HΦ".
    iDestruct (array_slice_app3_1 with "Hslice1 Hslice2 Hslice3") as "$"; [rewrite !length_take ?length_drop; lia.. |].
    rewrite Nat2Z.id take_take Nat.min_id -Nat.le_add_sub //. lia.
  Qed.
  Lemma array_unsafe_sub_spec t dq vs (i n : Z) :
    (0 ≤ i)%Z →
    (0 ≤ n)%Z →
    (i + n ≤ length vs)%Z →
    {{{
      array_model t dq vs
    }}}
      array_unsafe_sub t #i #n
    {{{ t',
      RET t';
      array_model t dq vs ∗
      array_model t' (DfracOwn 1) (take (Z.to_nat n) (drop (Z.to_nat i) vs))
    }}}.
  Proof.
    iIntros "% % % %Φ Hmodel HΦ".
    iDestruct (array_model_to_slice' with "Hmodel") as "(Hslice & #?)".
    wp_apply (array_unsafe_sub_spec_slice with "Hslice"); [done.. |].
    rewrite Nat.sub_0_r. iSteps.
  Qed.

  Lemma array_sub_spec_slice_fit t sz dq vs (i : Z) i_ (n : Z) :
    i_ = Z.to_nat i →
    {{{
      array_inv t sz ∗
      ( ⌜0 ≤ i⌝%Z -∗
        ⌜0 ≤ n⌝%Z -∗
        ⌜i + n ≤ sz⌝%Z -∗
          ⌜Z.to_nat n = length vs⌝ ∗
          array_slice t i_ dq vs
      )
    }}}
      array_sub t #i #n
    {{{ t',
      RET t';
      ⌜0 ≤ i⌝%Z ∗
      ⌜0 ≤ n⌝%Z ∗
      ⌜i + n ≤ sz⌝%Z ∗
      array_slice t i_ dq vs ∗
      array_model t' (DfracOwn 1) (take (Z.to_nat n) vs)
    }}}.
  Proof.
    iIntros (->) "%Φ (#Hinv & H) HΦ".
    wp_rec.
    do 2 (wp_smart_apply assume_spec' as "%").
    wp_smart_apply (array_size_spec_inv with "Hinv") as "_".
    wp_smart_apply assume_spec' as "%".
    iDestruct ("H" with "[//] [//] [//]") as "(% & Hslice)".
    wp_smart_apply (array_unsafe_sub_spec_slice_fit with "Hslice"); [lia.. |].
    iSteps.
  Qed.
  Lemma array_sub_spec_slice t sz dq vs i (j n : Z) :
    {{{
      array_inv t sz ∗
      ( ⌜0 ≤ j⌝%Z -∗
        ⌜0 ≤ n⌝%Z -∗
        ⌜j + n ≤ sz⌝%Z -∗
          ⌜i ≤ Z.to_nat j⌝ ∗
          ⌜Z.to_nat j + Z.to_nat n ≤ i + length vs⌝ ∗
          array_slice t i dq vs
      )
    }}}
      array_sub t #j #n
    {{{ t',
      RET t';
      ⌜0 ≤ j⌝%Z ∗
      ⌜0 ≤ n⌝%Z ∗
      ⌜j + n ≤ sz⌝%Z ∗
      array_slice t i dq vs ∗
      array_model t' (DfracOwn 1) (take (Z.to_nat n) (drop (Z.to_nat j - Z.to_nat i) vs))
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & H) HΦ".
    wp_rec.
    do 2 (wp_smart_apply assume_spec' as "%").
    wp_smart_apply (array_size_spec_inv with "Hinv") as "_".
    wp_smart_apply assume_spec' as "%".
    iDestruct ("H" with "[//] [//] [//]") as "(% & % & Hslice)".
    wp_smart_apply (array_unsafe_sub_spec_slice with "Hslice"); [lia.. |].
    iSteps.
  Qed.
  Lemma array_sub_spec t dq vs (i n : Z) :
    {{{
      array_model t dq vs
    }}}
      array_sub t #i #n
    {{{ t',
      RET t';
      ⌜0 ≤ i⌝%Z ∗
      ⌜0 ≤ n⌝%Z ∗
      ⌜i + n ≤ length vs⌝%Z ∗
      array_model t dq vs ∗
      array_model t' (DfracOwn 1) (take (Z.to_nat n) (drop (Z.to_nat i) vs))
    }}}.
  Proof.
    iIntros "%Φ Hmodel HΦ".
    wp_rec.
    do 2 (wp_smart_apply assume_spec' as "%").
    wp_smart_apply (array_size_spec with "Hmodel") as "Hmodel".
    wp_smart_apply assume_spec' as "%".
    wp_smart_apply (array_unsafe_sub_spec with "Hmodel"); [done.. |].
    iSteps.
  Qed.

  Lemma array_unsafe_shrink_spec t dq vs (n : Z) :
    (0 ≤ n ≤ length vs)%Z →
    {{{
      array_model t dq vs
    }}}
      array_unsafe_shrink t #n
    {{{ t',
      RET t';
      array_model t dq vs ∗
      array_model t' (DfracOwn 1) (take (Z.to_nat n) vs)
    }}}.
  Proof.
    iIntros "%Hn %Φ Hmodel HΦ".
    wp_rec.
    wp_smart_apply (array_unsafe_sub_spec with "Hmodel"); [lia.. |].
    iSteps.
  Qed.

  Lemma array_shrink_spec t dq vs (n : Z) :
    {{{
      array_model t dq vs
    }}}
      array_shrink t #n
    {{{ t',
      RET t';
      ⌜0 ≤ n ≤ length vs⌝%Z ∗
      array_model t dq vs ∗
      array_model t' (DfracOwn 1) (take (Z.to_nat n) vs)
    }}}.
  Proof.
    iIntros "%Φ Hmodel HΦ".
    wp_rec.
    wp_smart_apply assume_spec' as "%".
    wp_smart_apply (array_size_spec with "Hmodel") as "Hmodel".
    wp_smart_apply assume_spec' as "%".
    wp_smart_apply (array_unsafe_shrink_spec with "Hmodel"); first done.
    iSteps.
  Qed.

  Lemma array_clone_spec t dq vs :
    {{{
      array_model t dq vs
    }}}
      array_clone t
    {{{ t',
      RET t';
      array_model t dq vs ∗
      array_model t' (DfracOwn 1) vs
    }}}.
  Proof.
    iIntros "%Φ Hmodel HΦ".
    wp_rec.
    wp_apply (array_size_spec with "Hmodel") as "Hmodel".
    wp_apply (array_unsafe_shrink_spec with "Hmodel") as "%t' (Hmodel & Hmodel')"; first lia.
    rewrite firstn_all2; first lia. iSteps.
  Qed.

  Lemma array_unsafe_cget_spec_atomic t sz (i : Z) :
    <<<
      True
    | ∀∀ i_ dq v,
      ⌜i = Z.of_nat i_⌝ ∗
      array_cslice t sz i_ dq [v]
    >>>
      array_unsafe_cget t #i
    <<<
      array_cslice t sz i_ dq [v]
    | RET v;
      £ 1
    >>>.
  Proof.
    iIntros "!> %Φ _ HΦ".
    wp_rec.
    awp_smart_apply (array_size_spec_atomic_cslice with "[//]").
    iApply (aacc_aupd_abort with "HΦ"); first done. iIntros "%i_ %dq %v (%Heq & Hcslice)".
    iAaccIntro with "Hcslice"; first iSteps. iIntros "$ !>". iStep. iIntros "HΦ !> H£". clear.
    wp_pures. wp_rec. wp_pures.
    rewrite /array_cslice.
    iMod "HΦ" as "(%i_ & %dq & %v & (-> & (%l & -> & #Hhdr & Hcslice)) & _ & HΦ)".
    rewrite -chunk_cslice_singleton Z_rem_mod; [lia.. |].
    wp_load.
    iApply ("HΦ" with "[Hcslice] H£").
    rewrite chunk_cslice_singleton. iSteps.
  Qed.
  Lemma array_unsafe_cget_spec t sz (i : Z) i_ dq v :
    i = Z.of_nat i_ →
    {{{
      array_cslice t sz i_ dq [v]
    }}}
      array_unsafe_cget t #i
    {{{
      RET v;
      array_cslice t sz i_ dq [v]
    }}}.
  Proof.
    iIntros (->) "%Φ Hcslice HΦ".
    iApply wp_fupd.
    awp_apply (array_unsafe_cget_spec_atomic with "[//]") without "HΦ".
    rewrite /atomic_acc /=.
    repeat iExists _.
    iApply fupd_mask_intro; first done. iIntros "Hclose".
    iSplitL "Hcslice"; first auto. iSplit; first iSteps. iIntros "Hcslice".
    iMod "Hclose" as "_". iIntros "!> H£ HΦ".
    iMod (lc_fupd_elim_later with "H£ HΦ") as "HΦ".
    iApply ("HΦ" with "Hcslice").
  Qed.

  Lemma array_cget_spec_atomic t sz (i : Z) i_ :
    i_ = Z.to_nat i →
    <<<
      array_inv t sz
    | ∀∀ dq v,
      ⌜0 < sz⌝ -∗
      ⌜0 ≤ i⌝%Z -∗
      array_cslice t sz i_ dq [v]
    >>>
      array_cget t #i
    <<<
      array_cslice t sz i_ dq [v]
    | RET v;
      ⌜0 < sz⌝ ∗
      ⌜0 ≤ i⌝%Z ∗
      £ 1
    >>>.
  Proof.
    iIntros (->) "!> %Φ #Hinv HΦ".
    wp_rec.
    wp_smart_apply assume_spec' as "%".
    wp_smart_apply (array_size_spec_inv with "Hinv") as "_".
    wp_smart_apply assume_spec' as "%".
    awp_smart_apply (array_unsafe_cget_spec_atomic with "[//]").
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%dq %v H".
    iDestruct ("H" with "[%] [//]") as "Hcslice"; first lia.
    rewrite /atomic_acc /=.
    repeat iExists _. iStep. iSplitL; last iSteps. iIntros "!> (-> & $)".
    iSteps.
  Qed.
  Lemma array_cget_spec t sz (i : Z) i_ dq v :
    i_ = Z.to_nat i →
    {{{
      array_inv t sz ∗
      ( ⌜0 < sz⌝ -∗
        ⌜0 ≤ i⌝%Z -∗
        array_cslice t sz i_ dq [v]
      )
    }}}
      array_cget t #i
    {{{
      RET v;
      ⌜0 < sz⌝ ∗
      ⌜0 ≤ i⌝%Z ∗
      array_cslice t sz i_ dq [v]
    }}}.
  Proof.
    iIntros (->) "%Φ (#Hinv & H) HΦ".
    wp_rec.
    wp_smart_apply assume_spec' as "%".
    wp_smart_apply (array_size_spec_inv with "Hinv") as "_".
    wp_smart_apply assume_spec' as "%".
    wp_smart_apply (array_unsafe_cget_spec with "(H [%] [//])"); [lia.. |].
    iSteps.
  Qed.

  Lemma array_unsafe_cset_spec_atomic t sz (i : Z) v :
    <<<
      True
    | ∀∀ i_ w,
      ⌜i = Z.of_nat i_⌝ ∗
      array_cslice t sz i_ (DfracOwn 1) [w]
    >>>
      array_unsafe_cset t #i v
    <<<
      array_cslice t sz i_ (DfracOwn 1) [v]
    | RET ();
      £ 1
    >>>.
  Proof.
    iIntros "!> %Φ _ HΦ".
    wp_rec.
    awp_smart_apply (array_size_spec_atomic_cslice with "[//]").
    iApply (aacc_aupd_abort with "HΦ"); first done. iIntros "%i_ %w (%Heq & Hcslice)".
    iAaccIntro with "Hcslice"; first iSteps. iIntros "$ !>". iStep. iIntros "HΦ !> H£". clear.
    wp_pures. wp_rec. wp_pures.
    rewrite /array_cslice.
    iMod "HΦ" as "(%i_ & %w & (-> & (%l & -> & #Hhdr & Hcslice)) & _ & HΦ)".
    rewrite -chunk_cslice_singleton Z_rem_mod; [lia.. |].
    wp_store.
    iApply ("HΦ" with "[Hcslice] H£").
    rewrite chunk_cslice_singleton. iSteps.
  Qed.
  Lemma array_unsafe_cset_spec t sz (i : Z) i_ w v :
    i = Z.of_nat i_ →
    {{{
      array_cslice t sz i_ (DfracOwn 1) [w]
    }}}
      array_unsafe_cset t #i v
    {{{
      RET ();
      array_cslice t sz i_ (DfracOwn 1) [v]
    }}}.
  Proof.
    iIntros (->) "%Φ Hcslice HΦ".
    iApply wp_fupd.
    awp_apply (array_unsafe_cset_spec_atomic with "[//]") without "HΦ".
    rewrite /atomic_acc /=. repeat iExists _.
    iApply fupd_mask_intro; first done. iIntros "Hclose".
    iSplitL "Hcslice"; first auto. iSplit; first iSteps.
    iIntros "Hcslice". iMod "Hclose" as "_". iIntros "!> H£ HΦ".
    iMod (lc_fupd_elim_later with "H£ HΦ") as "HΦ".
    iApply ("HΦ" with "Hcslice").
  Qed.

  Lemma array_cset_spec_atomic t sz (i : Z) i_ v :
    i_ = Z.to_nat i →
    <<<
      array_inv t sz
    | ∀∀ w,
      ⌜0 < sz⌝ -∗
      ⌜0 ≤ i⌝%Z -∗
      array_cslice t sz i_ (DfracOwn 1) [w]
    >>>
      array_cset t #i v
    <<<
      array_cslice t sz i_ (DfracOwn 1) [v]
    | RET ();
      ⌜0 < sz⌝ -∗
      ⌜0 ≤ i⌝%Z ∗
      £ 1
    >>>.
  Proof.
    iIntros (->) "!> %Φ #Hinv HΦ".
    wp_rec.
    wp_smart_apply assume_spec' as "%".
    wp_smart_apply (array_size_spec_inv with "Hinv") as "_".
    wp_smart_apply assume_spec' as "%".
    awp_smart_apply (array_unsafe_cset_spec_atomic with "[//]").
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%w H".
    iDestruct ("H" with "[%] [//]") as "Hcslice"; first lia.
    rewrite /atomic_acc /=.
    repeat iExists _. iStep. iSplitL; last iSteps. iIntros "!> (-> & $)".
    iSteps.
  Qed.
  Lemma array_cset_spec t sz (i : Z) i_ w v :
    i_ = Z.to_nat i →
    {{{
      array_inv t sz ∗
      ( ⌜0 < sz⌝ -∗
        ⌜0 ≤ i⌝%Z -∗
        array_cslice t sz i_ (DfracOwn 1) [w]
      )
    }}}
      array_cset t #i v
    {{{
      RET ();
      ⌜0 < sz⌝ ∗
      ⌜0 ≤ i⌝%Z ∗
      array_cslice t sz i_ (DfracOwn 1) [v]
    }}}.
  Proof.
    iIntros (->) "%Φ (#Hinv & H) HΦ".
    wp_rec.
    wp_smart_apply assume_spec' as "%".
    wp_smart_apply (array_size_spec_inv with "Hinv") as "_".
    wp_smart_apply assume_spec' as "%".
    wp_smart_apply (array_unsafe_cset_spec with "(H [%] [//])"); [lia.. |].
    iSteps.
  Qed.

  Lemma array_unsafe_ccopy_slice_spec_atomic Ψ t1 sz1 (i1 : Z) t2 sz2 (i2 : Z) (n : Z) :
    (0 ≤ i1)%Z →
    (0 ≤ i2)%Z →
    {{{
      ▷ Ψ 0 [] None ∗
      □ (
        ∀ k vs o,
        ⌜k < Z.to_nat n⌝ -∗
        ⌜k = length vs⌝ -∗
        Ψ k vs o -∗
        match o with
        | None =>
            au_cload t1 sz1 (Z.to_nat i1 + k) (λ v,
              ▷ Ψ k vs (Some v)
            )
        | Some v =>
            au_cstore t2 sz2 (Z.to_nat i2 + k) v (
              ▷ Ψ (S k) (vs ++ [v]) None
            )
        end
      )
    }}}
      array_unsafe_ccopy_slice t1 #i1 t2 #i2 #n
    {{{ vs,
      RET ();
      ⌜length vs = Z.to_nat n⌝ ∗
      Ψ (Z.to_nat n) vs None
    }}}.
  Proof.
    iIntros "%Hi1 %Hi2 %Φ (HΨ & #H) HΦ".
    wp_rec.
    pose Ψ' (_ : Z) k := (
      ∃ vs,
      ⌜length vs = k⌝ ∗
      Ψ k vs None
    )%I.
    wp_smart_apply (for_spec_strong Ψ' with "[HΨ]").
    { iSplitL. { iExists []. iSteps. }
      iIntros "!> % %k -> %Hk (%vs & %Hvs & HΨ)".
      iDestruct ("H" with "[%] [//] HΨ") as "H'"; first lia.
      awp_smart_apply (array_unsafe_cget_spec_atomic with "[//]").
      iApply (aacc_aupd_commit with "H'"); first done. iIntros "%dq %v Hcslice".
      rewrite /atomic_acc /=.
      repeat iExists _. iFrame. iStep 2; first iSteps. iIntros "$ !> HΨ !> _".
      iDestruct ("H" with "[%] [//] HΨ") as "H'"; first lia.
      awp_smart_apply (array_unsafe_cset_spec_atomic with "[//]").
      iApply (aacc_aupd_commit with "H'"); first done. iIntros "%w Hslice".
      rewrite /atomic_acc /=.
      repeat iExists _. iFrame. iSteps.
      iExists (vs ++ [v]). rewrite length_app. iSteps.
    }
    rewrite Z.sub_0_r. iSteps.
  Qed.
  Lemma array_unsafe_ccopy_slice_spec_fit t1 sz1 (i1 : Z) i1_ dq1 vs1 t2 sz2 (i2 : Z) i2_ vs2 (n : Z) :
    i1 = Z.of_nat i1_ →
    i2 = Z.of_nat i2_ →
    n = length vs1 →
    length vs1 = length vs2 →
    {{{
      array_cslice t1 sz1 i1_ dq1 vs1 ∗
      array_cslice t2 sz2 i2_ (DfracOwn 1) vs2
    }}}
      array_unsafe_ccopy_slice t1 #i1 t2 #i2 #n
    {{{
      RET ();
      array_cslice t1 sz1 i1_ dq1 vs1 ∗
      array_cslice t2 sz2 i2_ (DfracOwn 1) vs1
    }}}.
  Proof.
    iIntros (-> -> -> ?) "%Φ (Hcslice1 & Hcslice2) HΦ".
    pose (Ψ k vs1_done o := (
      ⌜vs1_done = take k vs1⌝ ∗
      array_cslice t1 sz1 i1_ dq1 vs1 ∗
      array_cslice t2 sz2 i2_ (DfracOwn 1) (vs1_done ++ drop k vs2) ∗
      ⌜from_option (λ v1, vs1 !! k = Some v1) True o⌝
    )%I).
    wp_apply (array_unsafe_ccopy_slice_spec_atomic Ψ with "[$Hcslice1 $Hcslice2]") as "%vs1_done (_ & (-> & Hcslice1 & Hcslice2 & _))"; [lia.. | |].
    { iStep.
      iIntros "!> %k %vs1_done %o %Hk _ (-> & Hslice1 & Hslice2 & %Hlookup)".
      rewrite !Nat2Z.id.
      opose proof* (list_lookup_lookup_total_lt vs2 k); first lia.
      destruct o as [v1 |].
      - opose proof* (list_lookup_lookup_total_lt vs2 k); first lia.
        iDestruct (array_cslice_update with "Hslice2") as "(H↦2 & Hslice2)".
        { rewrite lookup_app_r length_take Nat.min_l //; try lia.
          rewrite Nat.sub_diag lookup_drop right_id list_lookup_lookup_total_lt //. lia.
        }
        iAuIntro. iAaccIntro with "H↦2"; first iSteps. iIntros "H↦2".
        iDestruct ("Hslice2" with "H↦2") as "Hslice2".
        iFrame. iSplitR. { erewrite take_S_r => //. }
        rewrite insert_app_r_alt length_take Nat.min_l //; try lia.
        rewrite Nat.sub_diag. erewrite drop_S => //. rewrite -(assoc (++)).
        iSteps.
      - opose proof* (list_lookup_lookup_total_lt vs1 k); first lia.
        iDestruct (array_cslice_lookup_acc k with "Hslice1") as "(H↦1 & Hslice1)"; first done.
        iAuIntro. iAaccIntro with "H↦1"; iSteps.
    }
    iApply ("HΦ" with "[$Hcslice1 Hcslice2]").
    rewrite firstn_all2; first lia. rewrite skipn_all2; first lia. rewrite right_id //.
  Qed.
  Lemma array_unsafe_ccopy_slice_spec t1 sz1 i1 (j1 : Z) dq1 vs1 t2 sz2 i2 (j2 : Z) vs2 (n : Z) :
    (i1 ≤ j1)%Z →
    (i2 ≤ j2)%Z →
    (0 ≤ n)%Z →
    (j1 + n ≤ i1 + length vs1)%Z →
    (j2 + n ≤ i2 + length vs2)%Z →
    {{{
      array_cslice t1 sz1 i1 dq1 vs1 ∗
      array_cslice t2 sz2 i2 (DfracOwn 1) vs2
    }}}
      array_unsafe_ccopy_slice t1 #j1 t2 #j2 #n
    {{{
      RET ();
      array_cslice t1 sz1 i1 dq1 vs1 ∗
      array_cslice t2 sz2 i2 (DfracOwn 1) (
        take (Z.to_nat j2 - i2) vs2 ++
        take (Z.to_nat n) (drop (Z.to_nat j1 - i1) vs1) ++
        drop (Z.to_nat j2 - i2 + Z.to_nat n) vs2
      )
    }}}.
  Proof.
    iIntros "% % % % % %Φ (Hcslice1 & Hcslice2) HΦ".
    Z_to_nat j1. Z_to_nat j2. Z_to_nat n. rewrite !Nat2Z.id.
    rewrite (Nat.le_add_sub i1 j1); first lia. set k1 := j1 - i1.
    rewrite (Nat.le_add_sub i2 j2); first lia. set k2 := j2 - i2.
    rewrite -{1 2}(take_drop k1 vs1) -(take_drop n (drop k1 vs1)).
    rewrite -{1}(take_drop k2 vs2) -(take_drop n (drop k2 vs2)).
    rewrite !drop_drop.
    iDestruct (array_cslice_app3_2 with "Hcslice1") as "(Hcslice11 & Hcslice12 & Hcslice13)"; first done.
    iDestruct (array_cslice_app3_2 with "Hcslice2") as "(Hcslice21 & Hcslice22 & Hcslice23)"; first done.
    rewrite !length_take !length_drop !Nat.min_l; [lia.. |].
    wp_apply (array_unsafe_ccopy_slice_spec_fit with "[$Hcslice12 $Hcslice22]") as "(Hcslice12 & Hcslice22)"; try lia.
    { rewrite length_take length_drop. lia. }
    { rewrite !length_take !length_drop. lia. }
    iApply "HΦ".
    iDestruct (array_cslice_app3_1 with "Hcslice11 Hcslice12 Hcslice13") as "$"; [rewrite !length_take ?length_drop; lia.. |].
    iDestruct (array_cslice_app3_1 with "Hcslice21 Hcslice22 Hcslice23") as "Hcslice2"; [rewrite !length_take ?length_drop; lia.. |].
    rewrite -!Nat.le_add_sub //; lia.
  Qed.

  Lemma array_ccopy_slice_spec_fit t1 sz1 (i1 : Z) i1_ dq1 vs1 t2 sz2 (i2 : Z) i2_ vs2 (n : Z) :
    i1_ = Z.to_nat i1 →
    i2_ = Z.to_nat i2 →
    {{{
      array_inv t1 sz1 ∗
      array_inv t2 sz2 ∗
      ( ⌜0 < sz1⌝ -∗
        ⌜0 < sz2⌝ -∗
        ⌜0 ≤ i1⌝%Z -∗
        ⌜0 ≤ i2⌝%Z -∗
        ⌜0 ≤ n⌝%Z -∗
        ⌜n ≤ sz1⌝%Z -∗
        ⌜n ≤ sz2⌝%Z -∗
          ⌜Z.to_nat n = length vs1⌝ ∗
          ⌜length vs1 = length vs2⌝ ∗
          array_cslice t1 sz1 i1_ dq1 vs1 ∗
          array_cslice t2 sz2 i2_ (DfracOwn 1) vs2
      )
    }}}
      array_ccopy_slice t1 #i1 t2 #i2 #n
    {{{
      RET ();
      ⌜0 < sz1⌝ ∗
      ⌜0 < sz2⌝ ∗
      ⌜0 ≤ i1⌝%Z ∗
      ⌜0 ≤ i2⌝%Z ∗
      ⌜0 ≤ n⌝%Z ∗
      ⌜n ≤ sz1⌝%Z ∗
      ⌜n ≤ sz2⌝%Z ∗
      array_cslice t1 sz1 i1_ dq1 vs1 ∗
      array_cslice t2 sz2 i2_ (DfracOwn 1) vs1
    }}}.
  Proof.
    iIntros (-> ->) "%Φ (#Hinv1 & #Hinv2 & H) HΦ".
    wp_rec.
    do 3 wp_smart_apply assume_spec' as "%".
    wp_smart_apply (array_size_spec_inv with "Hinv1") as "_".
    wp_smart_apply (array_size_spec_inv with "Hinv2") as "_".
    do 4 (wp_smart_apply assume_spec' as "%").
    iDestruct ("H" with "[%] [%] [//] [//] [//] [//] [//]") as "(% & % & Hcslice1 & Hcslice2)"; [lia.. |].
    wp_smart_apply (array_unsafe_ccopy_slice_spec_fit with "[$Hcslice1 $Hcslice2]"); [lia.. |].
    iSteps.
  Qed.
  Lemma array_ccopy_slice_spec t1 sz1 i1 (j1 : Z) dq1 vs1 t2 sz2 i2 (j2 : Z) vs2 (n : Z) :
    {{{
      array_inv t1 sz1 ∗
      array_inv t2 sz2 ∗
      ( ⌜0 < sz1⌝ -∗
        ⌜0 < sz2⌝ -∗
        ⌜0 ≤ j1⌝%Z -∗
        ⌜0 ≤ j2⌝%Z -∗
        ⌜0 ≤ n⌝%Z -∗
        ⌜n ≤ sz1⌝%Z -∗
        ⌜n ≤ sz2⌝%Z -∗
          ⌜i1 ≤ Z.to_nat j1⌝ ∗
          ⌜i2 ≤ Z.to_nat j2⌝ ∗
          ⌜Z.to_nat j1 + n ≤ i1 + length vs1⌝%Z ∗
          ⌜Z.to_nat j2 + n ≤ i2 + length vs2⌝%Z ∗
          array_cslice t1 sz1 i1 dq1 vs1 ∗
          array_cslice t2 sz2 i2 (DfracOwn 1) vs2
      )
    }}}
      array_ccopy_slice t1 #j1 t2 #j2 #n
    {{{
      RET ();
      ⌜0 < sz1⌝ ∗
      ⌜0 < sz2⌝ ∗
      ⌜0 ≤ j1⌝%Z ∗
      ⌜0 ≤ j2⌝%Z ∗
      ⌜0 ≤ n⌝%Z ∗
      ⌜n ≤ sz1⌝%Z ∗
      ⌜n ≤ sz2⌝%Z ∗
      array_cslice t1 sz1 i1 dq1 vs1 ∗
      array_cslice t2 sz2 i2 (DfracOwn 1) (
        take (Z.to_nat j2 - i2) vs2 ++
        take (Z.to_nat n) (drop (Z.to_nat j1 - i1) vs1) ++
        drop (Z.to_nat j2 - i2 + Z.to_nat n) vs2
      )
    }}}.
  Proof.
    iIntros "%Φ (#Hinv1 & #Hinv2 & H) HΦ".
    wp_rec.
    do 3 wp_smart_apply assume_spec' as "%".
    wp_smart_apply (array_size_spec_inv with "Hinv1") as "_".
    wp_smart_apply (array_size_spec_inv with "Hinv2") as "_".
    do 4 (wp_smart_apply assume_spec' as "%").
    iDestruct ("H" with "[%] [%] [//] [//] [//] [//] [//]") as "(% & % & % & % & Hslice1 & Hslice2)"; [lia.. |].
    wp_smart_apply (array_unsafe_ccopy_slice_spec with "[$Hslice1 $Hslice2]"); [lia.. |].
    iSteps.
  Qed.

  Lemma array_unsafe_ccopy_spec_fit t1 sz1 (i1 : Z) i1_ dq1 vs1 t2 sz2 (i2 : Z) i2_ vs2 :
    i1 = Z.of_nat i1_ →
    i2 = Z.of_nat i2_ →
    length vs1 = sz1 →
    length vs1 = length vs2 →
    {{{
      array_cslice t1 sz1 i1_ dq1 vs1 ∗
      array_cslice t2 sz2 i2_ (DfracOwn 1) vs2
    }}}
      array_unsafe_ccopy t1 #i1 t2 #i2
    {{{
      RET ();
      array_cslice t1 sz1 i1_ dq1 vs1 ∗
      array_cslice t2 sz2 i2_ (DfracOwn 1) vs1
    }}}.
  Proof.
    iIntros (-> -> ? ?) "%Φ (Hcslice1 & Hcslice2) HΦ".
    wp_rec.
    wp_smart_apply (array_size_spec_cslice with "Hcslice1") as "Hcslice1".
    wp_apply (array_unsafe_ccopy_slice_spec_fit with "[$Hcslice1 $Hcslice2]"); [lia.. |].
    iSteps.
  Qed.
  Lemma array_unsafe_ccopy_spec t1 sz1 (i1 : Z) i1_ dq1 vs1 t2 sz2 i2 (j2 : Z) vs2 :
    i1 = Z.of_nat i1_ →
    length vs1 = sz1 →
    (i2 ≤ j2)%Z →
    (j2 + length vs1 ≤ i2 + length vs2)%Z →
    {{{
      array_cslice t1 sz1 i1_ dq1 vs1 ∗
      array_cslice t2 sz2 i2 (DfracOwn 1) vs2
    }}}
      array_unsafe_ccopy t1 #i1 t2 #j2
    {{{
      RET ();
      array_cslice t1 sz1 i1_ dq1 vs1 ∗
      array_cslice t2 sz2 i2 (DfracOwn 1) (
        take (Z.to_nat j2 - i2) vs2 ++
        vs1 ++
        drop (Z.to_nat j2 - i2 + length vs1) vs2
      )
    }}}.
  Proof.
    iIntros (-> Hvs1 ? ?) "%Φ (Hcslice1 & Hcslice2) HΦ".
    wp_rec.
    wp_smart_apply (array_size_spec_cslice with "Hcslice1") as "Hcslice1".
    wp_apply (array_unsafe_ccopy_slice_spec with "[$Hcslice1 $Hcslice2]"); [lia.. |].
    rewrite !Nat2Z.id Nat.sub_diag -Hvs1 firstn_all //.
  Qed.

  Lemma array_ccopy_spec_fit t1 sz1 (i1 : Z) i1_ dq1 vs1 t2 sz2 (i2 : Z) i2_ vs2 :
    i1_ = Z.to_nat i1 →
    i2_ = Z.to_nat i2 →
    length vs1 = sz1 →
    length vs1 = length vs2 →
    {{{
      array_inv t1 sz1 ∗
      array_inv t2 sz2 ∗
      ( ⌜0 < sz1⌝ -∗
        ⌜0 < sz2⌝ -∗
        ⌜0 ≤ i1⌝%Z -∗
        ⌜0 ≤ i2⌝%Z -∗
          array_cslice t1 sz1 i1_ dq1 vs1 ∗
          array_cslice t2 sz2 i2_ (DfracOwn 1) vs2
      )
    }}}
      array_ccopy t1 #i1 t2 #i2
    {{{
      RET ();
      ⌜0 < sz1⌝ ∗
      ⌜0 < sz2⌝ ∗
      ⌜0 ≤ i1⌝%Z ∗
      ⌜0 ≤ i2⌝%Z ∗
      array_cslice t1 sz1 i1_ dq1 vs1 ∗
      array_cslice t2 sz2 i2_ (DfracOwn 1) vs1
    }}}.
  Proof.
    iIntros (-> ->) "% % %Φ (#Hinv1 & #Hinv2 & H) HΦ".
    wp_rec.
    do 2 (wp_smart_apply assume_spec' as "%").
    wp_smart_apply (array_size_spec_inv with "Hinv1") as "_".
    wp_smart_apply (array_size_spec_inv with "Hinv2") as "_".
    do 2 (wp_smart_apply assume_spec' as "%").
    iDestruct ("H" with "[%] [%] [//] [//]") as "(Hcslice1 & Hcslice2)"; [lia.. |].
    wp_smart_apply (array_unsafe_ccopy_spec_fit with "[$Hcslice1 $Hcslice2]"); [lia.. |].
    iSteps.
  Qed.
  Lemma array_ccopy_spec t1 sz1 (i1 : Z) dq1 vs1 t2 sz2 i2 (j2 : Z) vs2 :
    length vs1 = sz1 →
    {{{
      array_inv t1 sz1 ∗
      array_inv t2 sz2 ∗
      ( ⌜0 < sz1⌝ -∗
        ⌜0 < sz2⌝ -∗
        ⌜0 ≤ i1⌝%Z -∗
        ⌜0 ≤ j2⌝%Z -∗
          ⌜i2 ≤ Z.to_nat j2⌝%Z ∗
          ⌜Z.to_nat j2 + length vs1 ≤ i2 + length vs2⌝%Z ∗
          array_cslice t1 sz1 (Z.to_nat i1) dq1 vs1 ∗
          array_cslice t2 sz2 i2 (DfracOwn 1) vs2
      )
    }}}
      array_ccopy t1 #i1 t2 #j2
    {{{
      RET ();
      ⌜0 < sz1⌝ ∗
      ⌜0 < sz2⌝ ∗
      ⌜0 ≤ i1⌝%Z ∗
      ⌜0 ≤ j2⌝%Z ∗
      array_cslice t1 sz1 (Z.to_nat i1) dq1 vs1 ∗
      array_cslice t2 sz2 i2 (DfracOwn 1) (
        take (Z.to_nat j2 - i2) vs2 ++
        vs1 ++
        drop (Z.to_nat j2 - i2 + length vs1) vs2
      )
    }}}.
  Proof.
    iIntros "% %Φ (#Hinv1 & #Hinv2 & H) HΦ".
    wp_rec.
    do 2 (wp_smart_apply assume_spec' as "%").
    wp_smart_apply (array_size_spec_inv with "Hinv1") as "_".
    wp_smart_apply (array_size_spec_inv with "Hinv2") as "_".
    do 2 (wp_smart_apply assume_spec' as "%").
    iDestruct ("H" with "[%] [%] [//] [//]") as "(% & % & Hcslice1 & Hcslice2)"; [lia.. |].
    wp_smart_apply (array_unsafe_ccopy_spec with "[$Hcslice1 $Hcslice2]"); [lia.. |].
    iSteps.
  Qed.

  Definition itype_array τ `{!iType _ τ} (sz : nat) t : iProp Σ :=
    ∃ l,
    ⌜t = #l⌝ ∗
    l ↦ₕ Header 0 sz ∗
    itype_chunk τ sz l.
  #[global] Instance itype_array_itype τ `{!iType _ τ} sz :
    iType _ (itype_array τ sz).
  Proof.
    split. apply _.
  Qed.

  Lemma itype_array_intro τ `{!iType _ τ} t sz vs :
    length vs = sz →
    array_inv t sz -∗
    array_slice t 0 (DfracOwn 1) vs -∗
    ([∗ list] v ∈ vs, τ v) ={⊤}=∗
    itype_array τ sz t.
  Proof.
    rewrite /array_inv /array_slice.
    iIntros "% (%l & -> & #Hhdr) (%_l & %Heq & Hmodel) #Hvs". injection Heq as <-.
    rewrite location_add_0.
    iSteps. iExists vs. iSteps.
  Qed.

  Lemma itype_array_to_inv τ `{!iType _ τ} sz t :
    itype_array τ sz t ⊢
    array_inv t sz.
  Proof.
    rewrite /array_inv. iSteps.
  Qed.

  Lemma array_create_type τ `{!iType _ τ} :
    {{{
      True
    }}}
      array_create ()
    {{{ t,
      RET t;
      itype_array τ 0 t
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    iApply wp_fupd.
    wp_apply (array_create_spec with "[//]") as (t) "Hmodel".
    rewrite /array_model.
    iDestruct "Hmodel" as "(%l & -> & #Hhdr & Hmodel)".
    iApply "HΦ". iStep 2. iApply itype_chunk_0.
  Qed.

  Lemma array_size_type τ `{!iType _ τ} t sz :
    {{{
      itype_array τ sz t
    }}}
      array_size t
    {{{
      RET #sz;
      True
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma array_unsafe_get_type τ `{!iType _ τ} t (sz : nat) (i : Z) :
    (0 ≤ i < sz)%Z →
    {{{
      itype_array τ sz t
    }}}
      array_unsafe_get t #i
    {{{ v,
      RET v;
      τ v
    }}}.
  Proof.
    iIntros "%Hi %Φ (%l & -> & #Hhdr & #Htype) HΦ".
    wp_rec. wp_pures.
    Z_to_nat i.
    iInv "Htype" as "(%vs & >%Hvs & Hmodel & #Hvs)".
    opose proof* (list_lookup_lookup_total_lt vs i); first lia.
    iDestruct (chunk_model_lookup_acc i with "Hmodel") as "(H↦ & Hmodel)"; [lia | done | lia |].
    wp_load.
    iDestruct (big_sepL_lookup with "Hvs") as "Hv"; first done.
    iSteps.
  Qed.

  Lemma array_get_type τ `{!iType _ τ} t sz (i : Z) :
    {{{
      itype_array τ sz t
    }}}
      array_get t #i
    {{{ v,
      RET v;
      ⌜0 ≤ i < sz⌝%Z ∗
      τ v
    }}}.
  Proof.
    iIntros "%Φ #Ht HΦ".
    wp_rec.
    wp_smart_apply assume_spec' as "%Hi".
    wp_smart_apply (array_size_type with "Ht") as "_".
    wp_smart_apply assume_spec' as "%Hi'".
    wp_smart_apply (array_unsafe_get_type with "Ht"); first lia.
    iSteps.
  Qed.

  Lemma array_unsafe_set_type τ `{!iType _ τ} t (sz : nat) (i : Z) v :
    (0 ≤ i < sz)%Z →
    {{{
      itype_array τ sz t ∗
      τ v
    }}}
      array_unsafe_set t #i v
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Hi %Φ ((%l & -> & #Hhdr & Htype) & #Hv) HΦ".
    wp_rec. wp_pures.
    Z_to_nat i.
    iInv "Htype" as "(%vs & >%Hvs & Hmodel & Hvs)".
    opose proof* (list_lookup_lookup_total_lt vs i); first lia.
    iDestruct (chunk_model_update i with "Hmodel") as "(H↦ & Hmodel)"; [lia | done | lia |].
    wp_store.
    iDestruct (big_sepL_insert_acc with "Hvs") as "(_ & Hvs)"; first done.
    iSplitR "HΦ"; last iSteps. iExists (<[i := v]> vs).
    rewrite length_insert. iSteps.
  Qed.

  Lemma array_set_type τ `{!iType _ τ} t sz (i : Z) v :
    {{{
      itype_array τ sz t ∗
      τ v
    }}}
      array_set t #i v
    {{{
      RET ();
      ⌜0 ≤ i < sz⌝%Z
    }}}.
  Proof.
    iIntros "%Φ (#Htype & #Hv) HΦ".
    wp_rec.
    wp_smart_apply assume_spec' as "%Hi".
    wp_smart_apply (array_size_type with "Htype") as "_".
    wp_smart_apply assume_spec' as "%Hi'".
    wp_smart_apply (array_unsafe_set_type with "[$Htype $Hv]"); first lia.
    iSteps.
  Qed.

  Lemma array_unsafe_fill_slice_type τ `{!iType _ τ} t (sz : nat) (i n : Z) v :
    (0 ≤ i)%Z →
    (0 ≤ n)%Z →
    (i + n ≤ sz)%Z →
    {{{
      itype_array τ sz t ∗
      τ v
    }}}
      array_unsafe_fill_slice t #i #n v
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "% % % %Φ (#Htype & #Hv) HΦ".
    wp_rec.
    wp_smart_apply for_type; last iSteps. iIntros "!> % (%k & -> & %Hk)".
    wp_smart_apply (array_unsafe_set_type with "[$Htype $Hv]"); first lia.
    iSteps.
  Qed.

  Lemma array_fill_slice_type τ `{!iType _ τ} t sz (i n : Z) v :
    {{{
      itype_array τ sz t ∗
      τ v
    }}}
      array_fill_slice t #i #n v
    {{{
      RET ();
      ⌜0 ≤ i⌝%Z ∗
      ⌜0 ≤ n⌝%Z ∗
      ⌜i + n ≤ sz⌝%Z
    }}}.
  Proof.
    iIntros "%Φ (#Htype & #Hv) HΦ".
    wp_rec.
    wp_smart_apply (array_size_type with "Htype") as "_".
    repeat (wp_smart_apply assume_spec' as "%").
    wp_pures.
    wp_smart_apply (array_unsafe_fill_slice_type with "[$Htype $Hv]"); [done.. |].
    iSteps.
  Qed.

  Lemma array_fill_type τ `{!iType _ τ} t sz v :
    {{{
      itype_array τ sz t ∗
      τ v
    }}}
      array_fill t v
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ (#Htype & #Hv) HΦ".
    wp_rec.
    wp_smart_apply (array_size_type with "Htype") as "_".
    wp_apply (array_unsafe_fill_slice_type with "[$Htype $Hv] HΦ"); lia.
  Qed.

  Lemma array_unsafe_make_type τ `{!iType _ τ} sz v :
    (0 ≤ sz)%Z →
    {{{
      τ v
    }}}
      array_unsafe_make #sz v
    {{{ t,
      RET t;
      ⌜0 ≤ sz⌝%Z ∗
      itype_array τ (Z.to_nat sz) t
    }}}.
  Proof.
    iIntros "% %Φ #Hv HΦ".
    wp_rec.
    wp_smart_apply (array_unsafe_alloc_spec with "[//]") as (t) "Hmodel"; first done.
    wp_smart_apply (array_fill_spec with "[Hmodel]") as "Hmodel"; first iSteps.
    rewrite /array_model !length_replicate.
    iDestruct "Hmodel" as "(%l & -> & #Hhdr & Hmodel)".
    iStep 7.
    iApply inv_alloc. iExists (replicate (Z.to_nat sz) v). iSteps.
    - rewrite length_replicate //.
    - iApply big_sepL_intro. iIntros "%k %_v" ((-> & Hk)%lookup_replicate).
      iSteps.
  Qed.

  Lemma array_make_type τ `{!iType _ τ} sz v :
    {{{
      τ v
    }}}
      array_make #sz v
    {{{ t,
      RET t;
      ⌜0 ≤ sz⌝%Z ∗
      itype_array τ (Z.to_nat sz) t
    }}}.
  Proof.
    iIntros "%Φ #Hv HΦ".
    wp_rec.
    wp_smart_apply assume_spec' as "%".
    wp_smart_apply (array_unsafe_make_type with "[//] HΦ"); first done.
  Qed.

  Lemma array_foldli_type τ `{!iType _ τ} υ `{!iType _ υ} t sz acc fn :
    {{{
      itype_array τ sz t ∗
      υ acc ∗
      (υ --> itype_nat_upto sz --> τ --> υ)%T fn
    }}}
      array_foldli t acc fn
    {{{ acc',
      RET acc';
      υ acc'
    }}}.
  Proof.
    iIntros "%Φ (Htype & Hacc & #Hfn) HΦ".
    iDestruct (itype_array_to_inv with "Htype") as "#Hinv".
    iDestruct "Htype" as "(%l & -> & #Hhdr & #Htype)".
    pose (Ψ i vs o acc := (
      from_option τ True o ∗
      υ acc
    )%I).
    wp_apply (array_foldli_spec_atomic Ψ with "[$Hinv $Hacc]"); last iSteps.
    clear acc. iIntros "!> %i %vs_left %o %acc %Hi1 %Hi2 (Ho & Hacc)".
    destruct o as [v |].
    - wp_apply (wp_wand with "(Hfn Hacc)"). iClear "Hfn". clear fn. iIntros "%fn Hfn".
      wp_apply (wp_wand with "(Hfn [])"); first iSteps. clear fn. iIntros "%fn Hfn".
      wp_apply (wp_wand with "(Hfn Ho)").
      iSteps.
    - iAuIntro.
      iInv "Htype" as "(%vs & >%Hvs & >Hmodel & #Hvs)".
      opose proof* (list_lookup_lookup_total_lt vs i); first lia.
      iDestruct (chunk_model_lookup_acc i with "Hmodel") as "(H↦ & Hmodel)"; [lia | done | lia |].
      iDestruct (big_sepL_lookup with "Hvs") as "Hv"; first done.
      rewrite /array_slice chunk_model_singleton /atomic_acc /=.
      iApply fupd_mask_intro; first solve_ndisj.
      iSteps.
  Qed.

  Lemma array_foldl_type τ `{!iType _ τ} υ `{!iType _ υ} t sz acc fn :
    {{{
      itype_array τ sz t ∗
      υ acc ∗
      (υ --> τ --> υ)%T fn
    }}}
      array_foldl t acc fn
    {{{ acc',
      RET acc';
      υ acc'
    }}}.
  Proof.
    iIntros "%Φ (#Htype & #Hacc & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (array_foldli_type τ υ with "[$Htype $Hacc] HΦ").
    iSteps.
  Qed.

  Lemma array_foldri_type τ `{!iType _ τ} υ `{!iType _ υ} t sz acc fn :
    {{{
      itype_array τ sz t ∗
      (itype_nat_upto sz --> τ --> υ --> υ)%T fn ∗
      υ acc
    }}}
      array_foldri t fn acc
    {{{ acc',
      RET acc';
      υ acc'
    }}}.
  Proof.
    iIntros "%Φ (#Htype & #Hfn & Hacc) HΦ".
    iDestruct (itype_array_to_inv with "Htype") as "#Hinv".
    iDestruct "Htype" as "(%l & -> & #Hhdr & #Htype)".
    pose (Ψ i acc o vs := (
      from_option τ True o ∗
      υ acc
    )%I).
    wp_apply (array_foldri_spec_atomic Ψ with "[$Hinv $Hacc]"); last iSteps.
    clear acc. iIntros "!> %i %acc %o %vs_right %Hi (Ho & Hacc)".
    destruct o as [v |].
    - wp_apply (wp_wand with "(Hfn [])"); first iSteps. iClear "Hfn". clear fn. iIntros "%fn Hfn".
      wp_apply (wp_wand with "(Hfn Ho)"). clear fn. iIntros "%fn Hfn".
      wp_apply (wp_wand with "(Hfn Hacc)").
      iSteps.
    - iAuIntro.
      iInv "Htype" as "(%vs & >%Hvs & >Hmodel & #Hvs)".
      opose proof* (list_lookup_lookup_total_lt vs i); first lia.
      iDestruct (chunk_model_lookup_acc i with "Hmodel") as "(H↦ & Hmodel)"; [lia | done | lia |].
      iDestruct (big_sepL_lookup with "Hvs") as "Hv"; first done.
      rewrite /array_slice chunk_model_singleton /atomic_acc /=.
      iApply fupd_mask_intro; first solve_ndisj.
      iSteps.
  Qed.

  Lemma array_foldr_type τ `{!iType _ τ} υ `{!iType _ υ} t sz acc fn :
    {{{
      itype_array τ sz t ∗
      (τ --> υ --> υ)%T fn ∗
      υ acc
    }}}
      array_foldr t fn acc
    {{{ acc',
      RET acc';
      υ acc'
    }}}.
  Proof.
    iIntros "%Φ (#Htype & #Hfn & #Hacc) HΦ".
    wp_rec.
    wp_smart_apply (array_foldri_type τ υ with "[$Htype $Hacc] HΦ").
    iSteps.
  Qed.

  Lemma array_iteri_type τ `{!iType _ τ} t sz fn :
    {{{
      itype_array τ sz t ∗
      (itype_nat_upto sz --> τ --> itype_unit)%T fn
    }}}
      array_iteri t fn
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ (#Htype & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (array_size_type with "Htype") as "_".
    wp_smart_apply (for_type with "[] HΦ"). iIntros "!> % (%i & -> & %Hi)".
    wp_smart_apply (array_unsafe_get_type with "Htype"); first done.
    iSteps.
  Qed.

  Lemma array_iter_type τ `{!iType _ τ} t sz fn :
    {{{
      itype_array τ sz t ∗
      (τ --> itype_unit)%T fn
    }}}
      array_iter t fn
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ (#Htype & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (array_iteri_type τ with "[$Htype] HΦ").
    iSteps.
  Qed.

  Lemma array_applyi_type τ `{!iType _ τ} t sz fn :
    {{{
      itype_array τ sz t ∗
      (itype_nat_upto sz --> τ --> τ)%T fn
    }}}
      array_applyi t fn
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ (#Htype & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (array_iteri_type τ with "[$Htype] HΦ").
    iIntros "!> % (%i & -> & %Hi)". wp_pures. iIntros "!> !> %v Hv".
    wp_smart_apply (wp_wand with "(Hfn [])"); first iSteps. iClear "Hfn". clear fn. iIntros "%fn Hfn".
    wp_apply (wp_wand with "(Hfn Hv)") as "%w Hw".
    wp_smart_apply (array_unsafe_set_type with "[$Htype $Hw]"); first lia.
    iSteps.
  Qed.

  Lemma array_apply_type τ `{!iType _ τ} t sz fn :
    {{{
      itype_array τ sz t ∗
      (τ --> τ)%T fn
    }}}
      array_apply t fn
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ (#Htype & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (array_applyi_type τ with "[$Htype] HΦ").
    iSteps.
  Qed.

  Lemma array_unsafe_initi_type τ `{!iType _ τ} sz sz_ fn :
    sz = Z.of_nat sz_ →
    {{{
      (itype_nat_upto sz_ --> τ)%T fn
    }}}
      array_unsafe_initi #sz fn
    {{{ t,
      RET t;
      itype_array τ sz_ t
    }}}.
  Proof.
    iIntros (->) "%Φ #Hfn HΦ".
    wp_rec.
    wp_smart_apply (array_unsafe_alloc_spec with "[//]") as (t) "Hmodel"; first lia.
    wp_smart_apply (array_applyi_spec_disentangled (λ _, τ) with "[$Hmodel]") as (vs) "(%Hvs & Hmodel & Hvs)".
    { iIntros "!> %i %v %Hlookup".
      wp_smart_apply (wp_wand with "(Hfn [])"); last iSteps.
      apply lookup_lt_Some in Hlookup. rewrite length_replicate in Hlookup. iSteps.
    }
    rewrite /array_model.
    iDestruct "Hmodel" as "(%l & -> & #Hhdr & Hmodel)".
    rewrite length_replicate Nat2Z.id in Hvs. rewrite -Hvs. iSteps.
  Qed.

  Lemma array_initi_type τ `{!iType _ τ} sz fn :
    {{{
      (itype_nat_upto (Z.to_nat sz) --> τ)%T fn
    }}}
      array_initi #sz fn
    {{{ t,
      RET t;
      ⌜0 ≤ sz⌝%Z ∗
      itype_array τ (Z.to_nat sz) t
    }}}.
  Proof.
    iIntros "%Φ #Hfn HΦ".
    wp_rec.
    wp_smart_apply assume_spec' as "%".
    wp_smart_apply (array_unsafe_initi_type with "Hfn"); first lia.
    iSteps.
  Qed.

  Lemma array_unsafe_init_type τ `{!iType _ τ} sz fn :
    (0 ≤ sz)%Z →
    {{{
      (itype_unit --> τ)%T fn
    }}}
      array_unsafe_init #sz fn
    {{{ t,
      RET t;
      itype_array τ (Z.to_nat sz) t
    }}}.
  Proof.
    iIntros "% %Φ #Hfn HΦ".
    wp_rec.
    wp_smart_apply (array_unsafe_initi_type with "[] HΦ"); first lia.
    iSteps.
  Qed.

  Lemma array_init_type τ `{!iType _ τ} sz fn :
    {{{
      (itype_unit --> τ)%T fn
    }}}
      array_init #sz fn
    {{{ t,
      RET t;
      ⌜0 ≤ sz⌝%Z ∗
      itype_array τ (Z.to_nat sz) t
    }}}.
  Proof.
    iIntros "%Φ #Hfn HΦ".
    wp_rec.
    wp_smart_apply assume_spec' as "%".
    wp_smart_apply (array_unsafe_init_type with "Hfn"); first done.
    iSteps.
  Qed.

  Lemma array_mapi_type τ `{!iType _ τ} υ `{!iType _ υ} t sz sz_ fn :
    sz_ = Z.of_nat sz →
    {{{
      itype_array τ sz t ∗
      (itype_nat_upto sz --> τ --> υ)%T fn
    }}}
      array_mapi t fn
    {{{ t',
      RET t';
      itype_array υ sz t'
    }}}.
  Proof.
    iIntros (->) "%Φ (#Htype & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (array_size_type with "Htype") as "_".
    wp_apply (array_unsafe_initi_type υ); first done.
    { iIntros "!> % (%i & -> & %Hi)".
      wp_smart_apply (array_unsafe_get_type with "Htype"); first lia.
      iSteps.
    }
    iSteps.
  Qed.

  Lemma array_map_type τ `{!iType _ τ} υ `{!iType _ υ} t sz sz_ fn :
    sz_ = Z.of_nat sz →
    {{{
      itype_array τ sz t ∗
      (τ --> υ)%T fn
    }}}
      array_map t fn
    {{{ t',
      RET t';
      itype_array υ sz t'
    }}}.
  Proof.
    iIntros (->) "%Φ (#Htype & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (array_mapi_type τ υ with "[] HΦ"); first done.
    iFrame "#∗". iSteps.
  Qed.

  Lemma array_unsafe_copy_slice_type τ `{!iType _ τ} t1 (sz1 : nat) (i1 : Z) t2 (sz2 : nat) (i2 n : Z) :
    (0 ≤ i1)%Z →
    (0 ≤ i2)%Z →
    (0 ≤ n)%Z →
    (i1 + n ≤ sz1)%Z →
    (i2 + n ≤ sz2)%Z →
    {{{
      itype_array τ sz1 t1 ∗
      itype_array τ sz2 t2
    }}}
      array_unsafe_copy_slice t1 #i1 t2 #i2 #n
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "% % % % % %Φ (#Htype1 & #Htype2) HΦ".
    wp_rec.
    wp_smart_apply (for_type with "[] HΦ"). iIntros "!> % (%k & -> & %Hk)".
    wp_smart_apply (array_unsafe_get_type with "Htype1") as (v) "#Hv"; first lia.
    wp_smart_apply (array_unsafe_set_type with "[$Htype2 $Hv]"); first lia.
    iSteps.
  Qed.
  Lemma array_unsafe_copy_slice_type' τ `{!iType _ τ} t1 (sz : nat) (i1 : Z) t2 (i2 : Z) i2_ vs (n : Z) :
    (0 ≤ i1)%Z →
    i2 = Z.of_nat i2_ →
    n = length vs →
    (i1 + n ≤ sz)%Z →
    {{{
      itype_array τ sz t1 ∗
      array_slice t2 i2_ (DfracOwn 1) vs
    }}}
      array_unsafe_copy_slice t1 #i1 t2 #i2 #n
    {{{ ws,
      RET ();
      ⌜length ws = length vs⌝ ∗
      array_slice t2 i2_ (DfracOwn 1) ws ∗
      [∗ list] w ∈ ws, τ w
    }}}.
  Proof.
    iIntros (? -> -> ?) "%Φ (#Htype1 & Hslice2) HΦ".
    wp_rec.
    pose (Ψ (_ : Z) k := (
      ∃ ws,
      ⌜length ws = k⌝ ∗
      array_slice t2 i2_ (DfracOwn 1) (ws ++ drop k vs) ∗
      [∗ list] w ∈ ws, τ w
    )%I).
    wp_smart_apply (for_spec_strong Ψ with "[Hslice2]").
    { iSplitL.
      - iSteps. iExists []. iSteps.
      - iIntros "!> % %k -> %Hk (%ws & %Hws & Hslice2 & Hws)".
        wp_smart_apply (array_unsafe_get_type with "Htype1") as (v) "Hv"; first lia.
        wp_smart_apply (array_unsafe_set_spec_slice with "Hslice2") as "Hslice2".
        { rewrite length_app length_drop. lia. }
        iStep 2. iExists (ws ++ [v]). iSplit; last iSplitL "Hslice2".
        + rewrite length_app. iSteps.
        + assert (Z.to_nat (i2_ + (0 + k)) - i2_ = k) as -> by lia.
          rewrite -assoc insert_app_r_alt; first lia.
          erewrite Hws, Nat.sub_diag, drop_S => //.
          apply list_lookup_lookup_total_lt. lia.
        + iApply big_sepL_snoc. iSteps.
    }
    rewrite right_id Nat2Z.id. iSteps.
    rewrite drop_all right_id. iSteps.
  Qed.

  Lemma array_copy_slice_type τ `{!iType _ τ} t1 sz1 (i1 : Z) t2 sz2 (i2 n : Z) :
    {{{
      itype_array τ sz1 t1 ∗
      itype_array τ sz2 t2
    }}}
      array_copy_slice t1 #i1 t2 #i2 #n
    {{{
      RET ();
      ⌜0 ≤ i1⌝%Z ∗
      ⌜0 ≤ i2⌝%Z ∗
      ⌜0 ≤ n⌝%Z ∗
      ⌜i1 + n ≤ sz1⌝%Z ∗
      ⌜i2 + n ≤ sz2⌝%Z
    }}}.
  Proof.
    iIntros "%Φ (#Htype1 & #Htype2) HΦ".
    wp_rec.
    wp_smart_apply (array_size_type with "Htype1") as "_".
    wp_smart_apply (array_size_type with "Htype2") as "_".
    repeat (wp_smart_apply assume_spec' as "%").
    wp_smart_apply array_unsafe_copy_slice_type; [done.. | iFrame "#" |].
    iSteps.
  Qed.

  Lemma array_unsafe_copy_type τ `{!iType _ τ} t1 (sz1 : nat) t2 (sz2 : nat) (i2 : Z) :
    (0 ≤ i2)%Z →
    (i2 + sz1 ≤ sz2)%Z →
    {{{
      itype_array τ sz1 t1 ∗
      itype_array τ sz2 t2
    }}}
      array_unsafe_copy t1 t2 #i2
    {{{
      RET ();
      ⌜i2 + sz1 ≤ sz2⌝%Z
    }}}.
  Proof.
    iIntros "% % %Φ (#Htype1 & #Htype2) HΦ".
    wp_rec.
    wp_smart_apply (array_size_type with "Htype1") as "_".
    wp_apply array_unsafe_copy_slice_type. 6: iFrame "#". all: try lia.
    iSteps.
  Qed.
  Lemma array_unsafe_copy_type' τ `{!iType _ τ} t1 sz t2 (i2 : Z) i2_ vs :
    i2 = Z.of_nat i2_ →
    sz = length vs →
    {{{
      itype_array τ sz t1 ∗
      array_slice t2 i2_ (DfracOwn 1) vs
    }}}
      array_unsafe_copy t1 t2 #i2
    {{{ ws,
      RET ();
      ⌜length ws = length vs⌝ ∗
      array_slice t2 i2_ (DfracOwn 1) ws ∗
      [∗ list] w ∈ ws, τ w
    }}}.
  Proof.
    iIntros (-> ->) "%Φ (#Htype1 & Hmodel2) HΦ".
    wp_rec.
    wp_smart_apply (array_size_type with "Htype1") as "_".
    wp_apply (array_unsafe_copy_slice_type' with "[$Htype1 $Hmodel2] HΦ"); done.
  Qed.

  Lemma array_copy_type τ `{!iType _ τ} t1 sz1 t2 sz2 (i2 : Z) :
    {{{
      itype_array τ sz1 t1 ∗
      itype_array τ sz2 t2
    }}}
      array_copy t1 t2 #i2
    {{{
      RET ();
      ⌜0 ≤ i2⌝%Z ∗
      ⌜i2 + sz1 ≤ sz2⌝%Z
    }}}.
  Proof.
    iIntros "%Φ (#Htype1 & #Htype2) HΦ".
    wp_rec.
    wp_smart_apply assume_spec' as "%".
    wp_smart_apply (array_size_type with "Htype2") as "_".
    wp_smart_apply (array_size_type with "Htype1") as "_".
    wp_smart_apply assume_spec' as "%".
    wp_smart_apply array_unsafe_copy_type. 3: iFrame "#". all: try done.
    iSteps.
  Qed.

  Lemma array_unsafe_grow_type τ `{!iType _ τ} t (sz : nat) sz' v' :
    (sz ≤ sz')%Z →
    {{{
      itype_array τ sz t ∗
      τ v'
    }}}
      array_unsafe_grow t #sz' v'
    {{{ t',
      RET t';
      itype_array τ (Z.to_nat sz') t'
    }}}.
  Proof.
    iIntros "% %Φ (#Htype & #Hv') HΦ".
    wp_rec.
    wp_smart_apply (array_size_type with "Htype") as "_".
    wp_smart_apply (array_unsafe_alloc_spec with "[//]") as (t') "Hmodel'"; first lia.
    iDestruct (array_model_to_slice with "Hmodel'") as "(Hinv' & Hslice')".
    replace (Z.to_nat sz') with (sz + (Z.to_nat sz' - sz)) at 2 by lia.
    rewrite replicate_add.
    iDestruct (array_slice_app with "Hslice'") as "(Hslice1' & Hslice2')".
    wp_smart_apply (array_unsafe_copy_type' with "[$Htype $Hslice1']") as (vs) "(%Hvs & Hslice1' & #Hvs)"; first done.
    { rewrite length_replicate //. }
    wp_smart_apply (array_unsafe_fill_slice_spec with "Hslice2'") as "Hslice2'".
    { rewrite length_replicate //. }
    { rewrite length_replicate. lia. }
    iDestruct (array_slice_app_1' with "Hslice1' Hslice2'") as "Hslice'"; first done.
    iStep 4.
    rewrite length_replicate.
    iApply (itype_array_intro with "Hinv' Hslice'").
    { rewrite length_app Hvs !length_replicate. lia. }
    iApply big_sepL_app. iSteps.
    iApply big_sepL_intro. iIntros "!>" (i _v' (-> & _)%lookup_replicate).
    iSteps.
  Qed.

  Lemma array_grow_type τ `{!iType _ τ} t sz sz' v' :
    {{{
      itype_array τ sz t ∗
      τ v'
    }}}
      array_grow t #sz' v'
    {{{ t',
      RET t';
      ⌜sz ≤ sz'⌝ ∗
      itype_array τ (Z.to_nat sz') t'
    }}}.
  Proof.
    iIntros "%Φ (#Htype & #Hv') HΦ".
    wp_rec.
    wp_smart_apply (array_size_type with "Htype") as "_".
    wp_smart_apply assume_spec' as "%".
    wp_smart_apply (array_unsafe_grow_type with "[$Htype $Hv']"); first done.
    iSteps.
  Qed.

  Lemma array_unsafe_sub_type τ `{!iType _ τ} t (sz : nat) (i n : Z) :
    (0 ≤ i)%Z →
    (0 ≤ n)%Z →
    (i + n ≤ sz)%Z →
    {{{
      itype_array τ sz t
    }}}
      array_unsafe_sub t #i #n
    {{{ t',
      RET t';
      itype_array τ (Z.to_nat n) t'
    }}}.
  Proof.
    iIntros "% % % %Φ #Htype HΦ".
    wp_rec.
    wp_smart_apply (array_unsafe_alloc_spec with "[//]") as (t') "Hmodel'"; first done.
    iDestruct (array_model_to_slice with "Hmodel'") as "(#Hinv' & Hslice')".
    wp_smart_apply (array_unsafe_copy_slice_type' with "[$Htype $Hslice']") as (vs) "(%Hvs & Hslice' & Hvs)"; try done.
    { rewrite length_replicate. lia. }
    iStep 4.
    rewrite length_replicate.
    iApply (itype_array_intro with "Hinv' Hslice' Hvs").
    { rewrite Hvs length_replicate //. }
  Qed.

  Lemma array_sub_type τ `{!iType _ τ} t sz (i n : Z) :
    {{{
      itype_array τ sz t
    }}}
      array_sub t #i #n
    {{{ t',
      RET t';
      ⌜0 ≤ i⌝%Z ∗
      ⌜0 ≤ n⌝%Z ∗
      ⌜i + n ≤ sz⌝%Z ∗
      itype_array τ (Z.to_nat n) t'
    }}}.
  Proof.
    iIntros "%Φ #Htype HΦ".
    wp_rec.
    do 2 (wp_smart_apply assume_spec' as "%").
    wp_smart_apply (array_size_type with "Htype") as "_".
    wp_smart_apply assume_spec' as "%".
    wp_smart_apply (array_unsafe_sub_type with "Htype"); [done.. |].
    iSteps.
  Qed.

  Lemma array_unsafe_shrink_type τ `{!iType _ τ} t (sz : nat) (n : Z) :
    (0 ≤ n ≤ sz)%Z →
    {{{
      itype_array τ sz t
    }}}
      array_unsafe_shrink t #n
    {{{ t',
      RET t';
      itype_array τ (Z.to_nat n) t'
    }}}.
  Proof.
    iIntros "% %Φ Htype HΦ".
    wp_rec.
    wp_smart_apply (array_unsafe_sub_type with "Htype"); [lia.. |].
    iSteps.
  Qed.

  Lemma array_shrink_type τ `{!iType _ τ} t sz (n : Z) :
    {{{
      itype_array τ sz t
    }}}
      array_shrink t #n
    {{{ t',
      RET t';
      ⌜0 ≤ n ≤ sz⌝%Z ∗
      itype_array τ (Z.to_nat n) t'
    }}}.
  Proof.
    iIntros "%Φ #Htype HΦ".
    wp_rec.
    wp_smart_apply assume_spec' as "%".
    wp_smart_apply (array_size_type with "Htype") as "_".
    wp_smart_apply assume_spec' as "%".
    wp_smart_apply (array_unsafe_shrink_type with "Htype"); first done.
    iSteps.
  Qed.

  Lemma array_clone_type τ `{!iType _ τ} t sz :
    {{{
      itype_array τ sz t
    }}}
      array_clone t
    {{{ t',
      RET t';
      itype_array τ sz t'
    }}}.
  Proof.
    iIntros "%Φ #Htype HΦ".
    wp_rec.
    wp_apply (array_size_type with "Htype") as "_".
    wp_apply (array_unsafe_shrink_type with "Htype"); first lia.
    rewrite Nat2Z.id. iSteps.
  Qed.

  Lemma array_unsafe_cget_type τ `{!iType _ τ} t sz (i : Z) :
    0 < sz →
    (0 ≤ i)%Z →
    {{{
      itype_array τ sz t
    }}}
      array_unsafe_cget t #i
    {{{ v,
      RET v;
      τ v
    }}}.
  Proof.
    iIntros "%Hsz %Hi %Φ #Htype HΦ".
    wp_rec.
    wp_smart_apply (array_size_type with "Htype") as "_".
    wp_smart_apply (array_unsafe_get_type with "Htype HΦ").
    { rewrite Z_rem_mod; lia. }
  Qed.

  Lemma array_cget_type τ `{!iType _ τ} t sz (i : Z) :
    {{{
      itype_array τ sz t
    }}}
      array_cget t #i
    {{{ v,
      RET v;
      ⌜0 < sz⌝ ∗
      ⌜0 ≤ i⌝%Z ∗
      τ v
    }}}.
  Proof.
    iIntros "%Φ #Htype HΦ".
    wp_rec.
    wp_smart_apply assume_spec' as "%".
    wp_smart_apply (array_size_type with "Htype") as "_".
    wp_smart_apply assume_spec' as "%".
    wp_smart_apply (array_unsafe_cget_type with "Htype"); [lia.. |].
    iSteps.
  Qed.

  Lemma array_unsafe_cset_type τ `{!iType _ τ} t sz (i : Z) v :
    0 < sz →
    (0 ≤ i)%Z →
    {{{
      itype_array τ sz t ∗
      τ v
    }}}
      array_unsafe_cset t #i v
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Hsz %Hi %Φ (#Htype & #Hv) HΦ".
    wp_rec.
    wp_smart_apply (array_size_type with "Htype") as "_".
    wp_smart_apply (array_unsafe_set_type with "[$Htype $Hv] HΦ").
    { rewrite Z_rem_mod; lia. }
  Qed.

  Lemma array_cset_type τ `{!iType _ τ} t sz (i : Z) v :
    {{{
      itype_array τ sz t ∗
      τ v
    }}}
      array_cset t #i v
    {{{
      RET ();
      ⌜0 < sz⌝ ∗
      ⌜0 ≤ i⌝%Z
    }}}.
  Proof.
    iIntros "%Φ (#Htype & #Hv) HΦ".
    wp_rec.
    wp_smart_apply assume_spec' as "%".
    wp_smart_apply (array_size_type with "Htype") as "_".
    wp_smart_apply assume_spec' as "%".
    wp_smart_apply (array_unsafe_cset_type with "[$Htype $Hv]"); [lia.. |].
    iSteps.
  Qed.

  Lemma array_unsafe_ccopy_slice_type τ `{!iType _ τ} t1 sz1 (i1 : Z) t2 sz2 (i2 n : Z) :
    0 < sz1 →
    0 < sz2 →
    (0 ≤ i1)%Z →
    (0 ≤ i2)%Z →
    (0 ≤ n)%Z →
    {{{
      itype_array τ sz1 t1 ∗
      itype_array τ sz2 t2
    }}}
      array_unsafe_ccopy_slice t1 #i1 t2 #i2 #n
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "% % % % % %Φ (#Htype1 & #Htype2) HΦ".
    wp_rec.
    wp_smart_apply (for_type with "[] HΦ"). iIntros "!> % (%k & -> & %Hk)".
    wp_smart_apply (array_unsafe_cget_type with "Htype1") as (v) "#Hv"; [lia.. |].
    wp_smart_apply (array_unsafe_cset_type with "[$Htype2 $Hv]"); [lia.. |].
    iSteps.
  Qed.

  Lemma array_ccopy_slice_type τ `{!iType _ τ} t1 sz1 (i1 : Z) t2 sz2 (i2 : Z) (n : Z) :
    {{{
      itype_array τ sz1 t1 ∗
      itype_array τ sz2 t2
    }}}
      array_ccopy_slice t1 #i1 t2 #i2 #n
    {{{
      RET ();
      ⌜0 < sz1⌝ ∗
      ⌜0 < sz2⌝ ∗
      ⌜0 ≤ i1⌝%Z ∗
      ⌜0 ≤ i2⌝%Z
    }}}.
  Proof.
    iIntros "%Φ (#Htype1 & #Htype2) HΦ".
    wp_rec.
    do 3 (wp_smart_apply assume_spec' as "%").
    wp_smart_apply (array_size_type with "Htype1") as "_".
    wp_smart_apply (array_size_type with "Htype2") as "_".
    do 4 (wp_smart_apply assume_spec' as "%").
    wp_smart_apply array_unsafe_ccopy_slice_type. 6: iFrame "#". all: try lia.
    iSteps.
  Qed.

  Lemma array_unsafe_ccopy_type τ `{!iType _ τ} t1 sz1 (i1 : Z) t2 sz2 (i2 : Z) :
    0 < sz1 →
    0 < sz2 →
    (0 ≤ i1)%Z →
    (0 ≤ i2)%Z →
    {{{
      itype_array τ sz1 t1 ∗
      itype_array τ sz2 t2
    }}}
      array_unsafe_ccopy t1 #i1 t2 #i2
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "% % % % %Φ (#Htype1 & #Htype2) HΦ".
    wp_rec.
    wp_smart_apply (array_size_type with "Htype1") as "_".
    wp_apply (array_unsafe_ccopy_slice_type with "[] HΦ"); last iFrame "#"; lia.
  Qed.

  Lemma array_ccopy_type τ `{!iType _ τ} t1 sz1 (i1 : Z) t2 sz2 (i2 : Z) :
    {{{
      itype_array τ sz1 t1 ∗
      itype_array τ sz2 t2
    }}}
      array_ccopy t1 #i1 t2 #i2
    {{{
      RET ();
      ⌜0 < sz1⌝ ∗
      ⌜0 < sz2⌝ ∗
      ⌜0 ≤ i1⌝%Z ∗
      ⌜0 ≤ i2⌝%Z
    }}}.
  Proof.
    iIntros "%Φ (#Htype1 & #Htype2) HΦ".
    wp_rec.
    do 2 (wp_smart_apply assume_spec' as "%").
    wp_smart_apply (array_size_type with "Htype1") as "_".
    wp_smart_apply (array_size_type with "Htype2") as "_".
    do 2 (wp_smart_apply assume_spec' as "%").
    wp_smart_apply array_unsafe_ccopy_type. 5: iFrame "#". all: try lia.
    iSteps.
  Qed.
End zoo_G.

#[global] Opaque array_unsafe_alloc.
#[global] Opaque array_alloc.
#[global] Opaque array_create.
#[global] Opaque array_size.
#[global] Opaque array_unsafe_get.
#[global] Opaque array_get.
#[global] Opaque array_unsafe_set.
#[global] Opaque array_set.
#[global] Opaque array_unsafe_fill_slice.
#[global] Opaque array_fill_slice.
#[global] Opaque array_fill.
#[global] Opaque array_unsafe_make.
#[global] Opaque array_make.
#[global] Opaque array_foldli.
#[global] Opaque array_foldl.
#[global] Opaque array_foldri.
#[global] Opaque array_foldr.
#[global] Opaque array_iteri.
#[global] Opaque array_iter.
#[global] Opaque array_applyi.
#[global] Opaque array_apply.
#[global] Opaque array_unsafe_initi.
#[global] Opaque array_initi.
#[global] Opaque array_unsafe_init.
#[global] Opaque array_init.
#[global] Opaque array_mapi.
#[global] Opaque array_map.
#[global] Opaque array_unsafe_copy_slice.
#[global] Opaque array_copy_slice.
#[global] Opaque array_unsafe_copy.
#[global] Opaque array_copy.
#[global] Opaque array_unsafe_grow.
#[global] Opaque array_grow.
#[global] Opaque array_unsafe_sub.
#[global] Opaque array_sub.
#[global] Opaque array_unsafe_shrink.
#[global] Opaque array_shrink.
#[global] Opaque array_clone.
#[global] Opaque array_unsafe_cget.
#[global] Opaque array_cget.
#[global] Opaque array_unsafe_cset.
#[global] Opaque array_cset.
#[global] Opaque array_unsafe_ccopy_slice.
#[global] Opaque array_ccopy_slice.
#[global] Opaque array_unsafe_ccopy.
#[global] Opaque array_ccopy.

#[global] Opaque array_inv.
#[global] Opaque array_slice.
#[global] Opaque array_model.
#[global] Opaque array_cslice.
#[global] Opaque itype_array.
