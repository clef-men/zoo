From Coq Require Import
  ZifyNat.

From zoo Require Import
  prelude.
From zoo.common Require Import
  list
  math.
From zoo.iris.bi Require Import
  big_op.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
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

Implicit Types b : bool.
Implicit Types i j k n : nat.
Implicit Types l : location.
Implicit Types v t fn acc : val.
Implicit Types vs vs_left vs_right ws : list val.

Definition array_unsafe_xchg : val :=
  fun: "t" "i" "v" =>
    Xchg ("t", "i") "v".

Definition array_unsafe_cas : val :=
  fun: "t" "i" "v1" "v2" =>
    CAS ("t", "i") "v1" "v2".

Definition array_unsafe_faa : val :=
  fun: "t" "i" "incr" =>
    FAA ("t", "i") "incr".

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
      iIntros "(%l & -> & #Hheader1) (%_l & %Heq & #Hheader2)". injection Heq as <-.
      iDestruct (has_header_agree with "Hheader1 Hheader2") as %[= ->]. done.
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
        ⌜✓ (dq1 ⋅ dq2)⌝ ∗
        ⌜vs1 = vs2⌝.
    Proof.
      iIntros "% % Hslice1 Hslice2".
      iDestruct (array_slice_combine with "Hslice1 Hslice2") as "($ & Hslice)"; first done.
      iApply (array_slice_valid with "Hslice"); first done.
    Qed.
    Lemma array_slice_agree t i dq1 vs1 dq2 vs2 :
      length vs1 = length vs2 →
      array_slice t i dq1 vs1 -∗
      array_slice t i dq2 vs2 -∗
      ⌜vs1 = vs2⌝.
    Proof.
      iIntros "% Hslice1 Hslice2".
      iDestruct (array_slice_combine with "Hslice1 Hslice2") as "($ & _)"; first done.
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
    Lemma array_slice_exclusive t i vs1 dq2 vs2 :
      0 < length vs1 →
      length vs1 = length vs2 →
      array_slice t i (DfracOwn 1) vs1 -∗
      array_slice t i dq2 vs2 -∗
      False.
    Proof.
      iIntros "% % Hslice1 Hslice2".
      iDestruct (array_slice_ne with "Hslice1 Hslice2") as %?; naive_solver.
    Qed.
    Lemma array_slice_persist t i dq vs :
      array_slice t i dq vs ⊢ |==>
      array_slice t i DfracDiscarded vs.
    Proof.
      iIntros "(%l & -> & Hmodel)".
      iMod (chunk_model_persist with "Hmodel") as "Hmodel".
      iSteps.
    Qed.

    Lemma array_slice_nil {t i1 dq1 vs1} i2 dq2 :
      array_slice t i1 dq1 vs1 ⊢
      array_slice t i2 dq2 [].
    Proof.
      iSteps.
      iApply chunk_model_nil.
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
      array_slice t i dq (v :: vs) ⊣⊢
        array_slice t i dq [v] ∗
        array_slice t (S i) dq vs.
    Proof.
      rewrite -Nat.add_1_r array_slice_app //.
    Qed.
    Lemma array_slice_cons_1 t i dq v vs :
      array_slice t i dq (v :: vs) ⊢
        array_slice t i dq [v] ∗
        array_slice t (S i) dq vs.
    Proof.
      rewrite array_slice_cons //.
    Qed.
    Lemma array_slice_cons_2 t i dq v vs :
      array_slice t i dq [v] -∗
      array_slice t (S i) dq vs -∗
      array_slice t i dq (v :: vs).
    Proof.
      setoid_rewrite array_slice_cons at 2. iSteps.
    Qed.
    Lemma array_slice_cons_2' t i1 dq v i2 vs :
      i2 = S i1 →
      array_slice t i1 dq [v] -∗
      array_slice t i2 dq vs -∗
      array_slice t i1 dq (v :: vs).
    Proof.
      intros ->.
      apply array_slice_cons_2.
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
      setoid_rewrite insert_app_r_alt; simpl_length; last lia.
      rewrite Nat.min_l; first lia. rewrite Nat.sub_diag /=.
      iFrame. iIntros "%w Hslice2".
      iApply (array_slice_app3_1 with "Hslice1 Hslice2 Hslice3"); simpl_length/=; lia.
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
      - iIntros "(%l & -> & #Hheader & Hmodel1 & Hmodel2)". iSteps.
      - iIntros "((%l & -> & #Hheader & Hmodel1) & (%_l & %Heq & _ & Hmodel2))". injection Heq as <-.
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
      iIntros "% (%l & -> & #Hheader & Hmodel)".
      iApply (chunk_model_valid with "Hmodel"); first done.
    Qed.
    Lemma array_model_combine t dq1 vs1 dq2 vs2 :
      array_model t dq1 vs1 -∗
      array_model t dq2 vs2 -∗
        ⌜vs1 = vs2⌝ ∗
        array_model t (dq1 ⋅ dq2) vs1.
    Proof.
      iIntros "(%l & -> & #Hheader1 & Hmodel1) (%_l & %Heq & #Hheader2 & Hmodel2)". injection Heq as <-.
      iDestruct (has_header_agree with "Hheader1 Hheader2") as %[= Hlength].
      iDestruct (chunk_model_combine with "Hmodel1 Hmodel2") as "(<- & Hmodel)"; first done.
      iSteps.
    Qed.
    Lemma array_model_valid_2 t dq1 vs1 dq2 vs2 :
      0 < length vs1 →
      array_model t dq1 vs1 -∗
      array_model t dq2 vs2 -∗
        ⌜✓ (dq1 ⋅ dq2)⌝ ∗
        ⌜vs1 = vs2⌝.
    Proof.
      iIntros "% Hmodel1 Hmodel2".
      iDestruct (array_model_combine with "Hmodel1 Hmodel2") as "($ & Hmodel)".
      iApply (array_model_valid with "Hmodel"); first done.
    Qed.
    Lemma array_model_agree t dq1 vs1 dq2 vs2 :
      array_model t dq1 vs1 -∗
      array_model t dq2 vs2 -∗
      ⌜vs1 = vs2⌝.
    Proof.
      iIntros "Hmodel1 Hmodel2".
      iDestruct (array_model_combine with "Hmodel1 Hmodel2") as "($ & _)".
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
      intros.
      iApply array_model_dfrac_ne; [done.. | intros []%(exclusive_l _)].
    Qed.
    Lemma array_model_exclusive t vs1 dq2 vs2 :
      0 < length vs1 →
      array_model t (DfracOwn 1) vs1 -∗
      array_model t dq2 vs2 -∗
      False.
    Proof.
      iIntros "% Hmodel1 Hmodel2".
      iDestruct (array_model_ne with "Hmodel1 Hmodel2") as %?; done.
    Qed.
    Lemma array_model_persist t dq vs :
      array_model t dq vs ⊢ |==>
      array_model t DfracDiscarded vs.
    Proof.
      iIntros "(%l & -> & #Hheader & Hmodel)".
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
      iSteps. simpl_length. iSteps.
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
    Lemma array_cslice_to_slice t sz i dq vs :
      0 < sz →
      length vs ≤ sz →
      array_cslice t sz i dq vs ⊣⊢
        array_inv t sz ∗
        array_slice t (i `mod` sz) dq (take (sz - i `mod` sz) vs) ∗
        array_slice t 0 dq (drop (sz - i `mod` sz) vs).
    Proof.
      intros Hsz Hvs.
      rewrite /array_cslice /array_slice.
      setoid_rewrite chunk_cslice_to_model; [| done..].
      setoid_rewrite location_add_0.
      iSteps.
    Qed.
    Lemma array_cslice_to_slice' t sz i dq vs :
      0 < sz →
      length vs ≤ sz →
      array_cslice t sz i dq vs ⊢
        array_slice t (i `mod` sz) dq (take (sz - i `mod` sz) vs) ∗
        array_slice t 0 dq (drop (sz - i `mod` sz) vs).
    Proof.
      intros Hsz Hvs.
      rewrite array_cslice_to_slice //.
      iSteps.
    Qed.
    Lemma array_cslice_to_model t sz i dq vs :
      0 < sz →
      length vs = sz →
      array_cslice t sz i dq vs ⊣⊢
      array_model t dq (rotation (sz - i `mod` sz) vs).
    Proof.
      intros Hsz Hvs.
      rewrite /array_cslice /array_model.
      setoid_rewrite chunk_cslice_to_model_full; [| done..].
      rewrite length_rotation Hvs //.
    Qed.
    Lemma array_cslice_to_slice_cell t sz i dq v :
      array_cslice t sz i dq [v] ⊣⊢
        array_inv t sz ∗
        array_slice t (i `mod` sz) dq [v].
    Proof.
      rewrite /array_slice Nat2Z.inj_mod.
      setoid_rewrite chunk_model_cslice_cell.
      iSteps.
    Qed.
    Lemma array_cslice_to_slice_cell' t sz i dq v :
      array_cslice t sz i dq [v] ⊢
      array_slice t (i `mod` sz) dq [v].
    Proof.
      rewrite array_cslice_to_slice_cell.
      iSteps.
    Qed.
    Lemma array_slice_to_cslice_cell t sz i dq v :
      array_inv t sz -∗
      array_slice t (i `mod` sz) dq [v] -∗
      array_cslice t sz i dq [v].
    Proof.
      rewrite array_cslice_to_slice_cell.
      iSteps.
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
      - iIntros "(%l & -> & #Hheader & (Hcslice1 & Hcslice2))".
        iSteps.
      - iIntros "((%l & -> & #Hheader & Hcslice1) & (%_l & %Heq & _ & Hcslice2))". injection Heq as <-.
        iCombine "Hcslice1 Hcslice2" as "Hcslice".
        iSteps.
    Qed.
    #[global] Instance array_cslice_as_fractionak t sz i q vs :
      AsFractional (array_cslice t sz i (DfracOwn q) vs) (λ q, array_cslice t sz i (DfracOwn q) vs) q.
    Proof.
      split; [done | apply _].
    Qed.

    Lemma array_inv_cslice_agree t sz1 sz2 i dq vs :
      array_inv t sz1 -∗
      array_cslice t sz2 i dq vs -∗
      ⌜sz1 = sz2⌝.
    Proof.
      rewrite array_cslice_to_inv.
      iIntros "#Hinv1 #Hinv2".
      iDestruct (array_inv_agree with "Hinv1 Hinv2") as %->. done.
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
      array_cslice t sz i dq (v :: vs) ⊣⊢
        array_cslice t sz i dq [v] ∗
        array_cslice t sz (S i) dq vs.
    Proof.
      rewrite -Nat.add_1_r array_cslice_app //.
    Qed.
    Lemma array_cslice_cons_1 t sz i dq v vs :
      array_cslice t sz i dq (v :: vs) ⊢
        array_cslice t sz i dq [v] ∗
        array_cslice t sz (S i) dq vs.
    Proof.
      rewrite array_cslice_cons //.
    Qed.
    Lemma array_cslice_cons_2 t sz i dq v vs :
      array_cslice t sz i dq [v] -∗
      array_cslice t sz (S i) dq vs -∗
      array_cslice t sz i dq (v :: vs).
    Proof.
      setoid_rewrite array_cslice_cons at 2. iSteps.
    Qed.
    Lemma array_cslice_cons_2' t sz i1 dq v i2 vs :
      i2 = S i1 →
      array_cslice t sz i1 dq [v] -∗
      array_cslice t sz i2 dq vs -∗
      array_cslice t sz i1 dq (v :: vs).
    Proof.
      intros ->.
      apply array_cslice_cons_2.
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
      array_cslice t sz i dq vs ⊣⊢
      array_cslice t sz (i + sz) dq vs.
    Proof.
      rewrite /array_cslice.
      setoid_rewrite chunk_cslice_shift at 1.
      done.
    Qed.

    Lemma array_cslice_shift_right t sz i dq vs :
      array_cslice t sz i dq vs ⊢
      array_cslice t sz (i + sz) dq vs.
    Proof.
      rewrite array_cslice_shift //.
    Qed.
    Lemma array_cslice_shift_right' {t sz i1 dq vs} i2 :
      i2 = i1 + sz →
      array_cslice t sz i1 dq vs ⊢
      array_cslice t sz i2 dq vs.
    Proof.
      intros ->.
      apply array_cslice_shift_right.
    Qed.

    Lemma array_cslice_shift_left t sz i dq vs :
      sz ≤ i →
      array_cslice t sz i dq vs ⊢
      array_cslice t sz (i - sz) dq vs.
    Proof.
      intros.
      setoid_rewrite array_cslice_shift at 2.
      replace (i - sz + sz) with i by lia. done.
    Qed.
    Lemma array_cslice_shift_left' {t sz i1 dq vs} i2 :
      sz ≤ i1 →
      i2 = i1 - sz →
      array_cslice t sz i1 dq vs ⊢
      array_cslice t sz i2 dq vs.
    Proof.
      intros ? ->.
      apply array_cslice_shift_left. done.
    Qed.

    Lemma array_cslice_rotation_right {t sz i dq vs} n :
      0 < sz →
      length vs = sz →
      array_cslice t sz i dq vs ⊣⊢
      array_cslice t sz (i + n) dq (rotation (n `mod` sz) vs).
    Proof.
      intros.
      rewrite /array_cslice.
      setoid_rewrite chunk_cslice_rotation_right at 1; done.
    Qed.
    Lemma array_cslice_rotation_right_1 {t sz i dq vs} n :
      0 < sz →
      length vs = sz →
      array_cslice t sz i dq vs ⊢
      array_cslice t sz (i + n) dq (rotation (n `mod` sz) vs).
    Proof.
      intros.
      rewrite array_cslice_rotation_right //.
    Qed.
    Lemma array_cslice_rotation_right_0 {t sz dq vs} i :
      0 < sz →
      length vs = sz →
      array_cslice t sz 0 dq vs ⊣⊢
      array_cslice t sz i dq (rotation (i `mod` sz) vs).
    Proof.
      intros.
      rewrite array_cslice_rotation_right //.
    Qed.

    Lemma array_cslice_rotation_right' {t sz i1 dq vs} i2 n :
      0 < sz →
      length vs = sz →
      i2 = i1 + n →
      array_cslice t sz i1 dq vs ⊣⊢
      array_cslice t sz i2 dq (rotation (n `mod` sz) vs).
    Proof.
      intros Hsz Hvs ->.
      rewrite array_cslice_rotation_right //.
    Qed.
    Lemma array_cslice_rotation_right_1' {t sz i1 dq vs} i2 n :
      0 < sz →
      length vs = sz →
      i2 = i1 + n →
      array_cslice t sz i1 dq vs ⊢
      array_cslice t sz i2 dq (rotation (n `mod` sz) vs).
    Proof.
      intros.
      rewrite array_cslice_rotation_right' //.
    Qed.

    Lemma array_cslice_rotation_right_small {t sz i dq vs} n :
      0 < sz →
      length vs = sz →
      n < sz →
      array_cslice t sz i dq vs ⊣⊢
      array_cslice t sz (i + n) dq (rotation n vs).
    Proof.
      intros.
      rewrite array_cslice_rotation_right // Nat.mod_small //.
    Qed.
    Lemma array_cslice_rotation_right_small_1 {t sz i dq vs} n :
      0 < sz →
      length vs = sz →
      n < sz →
      array_cslice t sz i dq vs ⊢
      array_cslice t sz (i + n) dq (rotation n vs).
    Proof.
      intros.
      rewrite array_cslice_rotation_right_small //.
    Qed.

    Lemma array_cslice_rotation_right_small' {t sz i1 dq vs} i2 n :
      0 < sz →
      length vs = sz →
      i2 = i1 + n →
      n < sz →
      array_cslice t sz i1 dq vs ⊣⊢
      array_cslice t sz i2 dq (rotation n vs).
    Proof.
      intros Hsz Hvs -> Hn.
      rewrite array_cslice_rotation_right_small //.
    Qed.
    Lemma array_cslice_rotation_right_small_1' {t sz i1 dq vs} i2 n :
      0 < sz →
      length vs = sz →
      i2 = i1 + n →
      n < sz →
      array_cslice t sz i1 dq vs ⊢
      array_cslice t sz i2 dq (rotation n vs).
    Proof.
      intros.
      rewrite array_cslice_rotation_right_small' //.
    Qed.

    Lemma array_cslice_rotation_left t sz i n dq vs :
      0 < sz →
      length vs = sz →
      array_cslice t sz (i + n) dq vs ⊣⊢
      array_cslice t sz i dq (rotation (sz - n `mod` sz) vs).
    Proof.
      intros.
      rewrite /array_cslice.
      setoid_rewrite chunk_cslice_rotation_left at 1; done.
    Qed.
    Lemma array_cslice_rotation_left_1 t sz i n dq vs :
      0 < sz →
      length vs = sz →
      array_cslice t sz (i + n) dq vs ⊢
      array_cslice t sz i dq (rotation (sz - n `mod` sz) vs).
    Proof.
      intros.
      rewrite array_cslice_rotation_left //.
    Qed.
    Lemma array_cslice_rotation_left_0 t sz i dq vs :
      0 < sz →
      length vs = sz →
      array_cslice t sz i dq vs ⊣⊢
      array_cslice t sz 0 dq (rotation (sz - i `mod` sz) vs).
    Proof.
      apply (array_cslice_rotation_left _ _ 0).
    Qed.

    Lemma array_cslice_rotation_left' {t sz i1 dq vs} i2 n :
      0 < sz →
      length vs = sz →
      i1 = i2 + n →
      array_cslice t sz i1 dq vs ⊣⊢
      array_cslice t sz i2 dq (rotation (sz - n `mod` sz) vs).
    Proof.
      intros Hsz Hvs ->.
      rewrite array_cslice_rotation_left //.
    Qed.
    Lemma array_cslice_rotation_left_1' {t sz i1 dq vs} i2 n :
      0 < sz →
      length vs = sz →
      i1 = i2 + n →
      array_cslice t sz i1 dq vs ⊢
      array_cslice t sz i2 dq (rotation (sz - n `mod` sz) vs).
    Proof.
      intros.
      rewrite array_cslice_rotation_left' //.
    Qed.

    Lemma array_cslice_rotation_left_small t sz i n dq vs :
      0 < sz →
      length vs = sz →
      n < sz →
      array_cslice t sz (i + n) dq vs ⊣⊢
      array_cslice t sz i dq (rotation (sz - n) vs).
    Proof.
      intros.
      rewrite array_cslice_rotation_left // Nat.mod_small //.
    Qed.
    Lemma array_cslice_rotation_left_small_1 t sz i n dq vs :
      0 < sz →
      length vs = sz →
      n < sz →
      array_cslice t sz (i + n) dq vs ⊢
      array_cslice t sz i dq (rotation (sz - n) vs).
    Proof.
      intros.
      rewrite array_cslice_rotation_left_small //.
    Qed.

    Lemma array_cslice_rotation_left_small' {t sz i1 dq vs} i2 n :
      0 < sz →
      length vs = sz →
      i1 = i2 + n →
      n < sz →
      array_cslice t sz i1 dq vs ⊣⊢
      array_cslice t sz i2 dq (rotation (sz - n) vs).
    Proof.
      intros Hsz Hvs -> Hn.
      rewrite array_cslice_rotation_left_small //.
    Qed.
    Lemma array_cslice_rotation_left_small_1' {t sz i1 dq vs} i2 n :
      0 < sz →
      length vs = sz →
      i1 = i2 + n →
      n < sz →
      array_cslice t sz i1 dq vs ⊢
      array_cslice t sz i2 dq (rotation (sz - n) vs).
    Proof.
      intros.
      rewrite array_cslice_rotation_left_small' //.
    Qed.

    Lemma array_cslice_rebase {t sz i1 dq vs1} i2 :
      0 < sz →
      length vs1 = sz →
      array_cslice t sz i1 dq vs1 ⊢
        ∃ vs2 n,
        ⌜vs2 = rotation n vs1⌝ ∗
        array_cslice t sz i2 dq vs2 ∗
        ( array_cslice t sz i2 dq vs2 -∗
          array_cslice t sz i1 dq vs1
        ).
    Proof.
      intros.
      rewrite /array_cslice.
      setoid_rewrite chunk_cslice_rebase at 1; [| done..].
      iSteps.
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
      iIntros "% (%l & -> & #Hheader & Hcslice1) (%_l & %Heq & _ & Hcslice2)". injection Heq as <-.
      iDestruct (chunk_cslice_combine with "Hcslice1 Hcslice2") as "($ & Hcslice)"; first done.
      iSteps.
    Qed.
    Lemma array_cslice_valid_2 t sz i dq1 vs1 dq2 vs2 :
      0 < length vs1 →
      length vs1 = length vs2 →
      array_cslice t sz i dq1 vs1 -∗
      array_cslice t sz i dq2 vs2 -∗
        ⌜✓ (dq1 ⋅ dq2)⌝ ∗
        ⌜vs1 = vs2⌝.
    Proof.
      iIntros "% % Hcslice1 Hcslice2".
      iDestruct (array_cslice_combine with "Hcslice1 Hcslice2") as "($ & Hcslice)"; first done.
      iApply (array_cslice_valid with "Hcslice"); first done.
    Qed.
    Lemma array_cslice_agree t sz i dq1 vs1 dq2 vs2 :
      length vs1 = length vs2 →
      array_cslice t sz i dq1 vs1 -∗
      array_cslice t sz i dq2 vs2 -∗
      ⌜vs1 = vs2⌝.
    Proof.
      iIntros "% Hcslice1 Hcslice2".
      iDestruct (array_cslice_combine with "Hcslice1 Hcslice2") as "($ & _)"; first done.
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
    Lemma array_cslice_exclusive t sz i vs1 dq2 vs2 :
      0 < length vs1 →
      length vs1 = length vs2 →
      array_cslice t sz i (DfracOwn 1) vs1 -∗
      array_cslice t sz i dq2 vs2 -∗
      False.
    Proof.
      iIntros "% % Hcslice1 Hcslice2".
      iDestruct (array_cslice_ne with "Hcslice1 Hcslice2") as %?; done.
    Qed.
    Lemma array_cslice_persist t sz i dq vs :
      array_cslice t sz i dq vs ⊢ |==>
      array_cslice t sz i DfracDiscarded vs.
    Proof.
      rewrite /array_cslice.
      setoid_rewrite chunk_cslice_persist at 1.
      iSteps.
    Qed.

    Lemma array_cslice_length t sz i vs :
      0 < sz →
      array_cslice t sz i (DfracOwn 1) vs ⊢
      ⌜length vs ≤ sz⌝.
    Proof.
      iIntros "%Hsz (%l & -> & _ & Hcslice)".
      iApply (chunk_cslice_length with "Hcslice"); first done.
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

  Lemma array_unsafe_alloc_spec sz :
    (0 ≤ sz)%Z →
    {{{
      True
    }}}
      array_unsafe_alloc #sz
    {{{ t,
      RET t;
      array_model t (DfracOwn 1) (replicate ₊sz ()%V)
    }}}.
  Proof.
    rewrite /array_model /array_slice.
    iIntros "%Hsz %Φ _ HΦ".
    wp_rec.
    wp_alloc l as "#Hheader" "_" "Hl"; [done.. |].
    iSteps. simpl_length. iSteps.
  Qed.

  Lemma array_alloc_spec sz :
    {{{
      True
    }}}
      array_alloc #sz
    {{{ t,
      RET t;
      ⌜0 ≤ sz⌝%Z ∗
      array_model t (DfracOwn 1) (replicate ₊sz ()%V)
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
      £ 1 ∗
      array_inv t (length vs)
    >>>.
  Proof.
    rewrite /array_model /array_inv.
    iIntros "%Φ _ HΦ".
    wp_rec credit:"H£".
    iMod "HΦ" as "(%dq & %vs & (%l & -> & #Hheader & Hmodel) & _ & HΦ)".
    wp_size.
    iApply ("HΦ" with "[$Hmodel]"); iSteps.
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
      £ 1 ∗
      array_inv t sz
    >>>.
  Proof.
    rewrite /array_cslice /array_inv.
    iIntros "%Φ _ HΦ".
    wp_rec credit:"H£".
    iMod "HΦ" as "(%sz & %i & %dq & %vs & (%l & -> & #Hheader & Hcslice) & _ & HΦ)".
    wp_size.
    iApply ("HΦ" with "[Hcslice]"); iSteps.
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
      ⌜vs !! (₊j - i) = Some v⌝ ∗
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
    iIntros "%Φ _ HΦ".
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
      ⌜i = ⁺i_⌝ ∗
      array_slice t i_ dq [v]
    >>>
      array_unsafe_get t #i
    <<<
      array_slice t ₊i dq [v]
    | RET v;
      £ 1
    >>>.
  Proof.
    iIntros "%Φ _ HΦ".
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
      ⌜vs !! ₊i = Some v⌝ ∗
      array_model t dq vs
    >>>
      array_unsafe_get t #i
    <<<
      array_model t dq vs
    | RET v;
      £ 1
    >>>.
  Proof.
    iIntros "%Hi %Φ _ HΦ".
    awp_apply (array_unsafe_get_spec_atomic_slice with "[//]").
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%dq %vs %v (%Hlookup & Hmodel)".
    iDestruct (array_model_to_slice' with "Hmodel") as "(Hslice & #?)".
    rewrite /atomic_acc /=.
    iExists dq, vs, 0, v. rewrite Nat.sub_0_r. iSteps.
  Qed.
  Lemma array_unsafe_get_spec_slice k t i dq vs (j : Z) v :
    (i ≤ j)%Z →
    vs !! k = Some v →
    k = ₊j - i →
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
    i = ₊i_ →
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
    i_ = ₊i →
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
        ⌜i ≤ ₊j⌝ ∗
        ⌜vs !! (₊j - i) = Some v⌝ ∗
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
    iIntros "%Φ #Hinv HΦ".
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
    i_ = ₊i →
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
    iIntros (->) "%Φ #Hinv HΦ".
    awp_apply (array_get_spec_atomic_slice with "Hinv").
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%dq %v H".
    rewrite /atomic_acc /=.
    iExists dq, [v], ₊i, v. rewrite Nat.sub_diag. iSplitL; first iSteps. iSplitR; last iSteps. iIntros "!> H". iSplitL; iSteps.
  Qed.
  Lemma array_get_spec_atomic t sz (i : Z) :
    <<<
      array_inv t sz
    | ∀∀ dq vs v,
      ⌜0 ≤ i < sz⌝%Z -∗
        ⌜vs !! ₊i = Some v⌝ ∗
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
    iIntros "%Φ #Hinv HΦ".
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
          ⌜i ≤ ₊j⌝ ∗
          ⌜vs !! k = Some v⌝ ∗
          ⌜k = ₊j - i⌝ ∗
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
    i_ = ₊i →
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
        ⌜vs !! ₊i = Some v⌝
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
      array_slice t i (DfracOwn 1) (<[₊j - i := v]> vs)
    | RET ();
      £ 1
    >>>.
  Proof.
    rewrite /array_model /array_slice.
    iIntros "%Φ _ HΦ".
    wp_rec credit:"H£". wp_pures.
    iMod "HΦ" as "(%vs & %i & (%Hj & (%l & -> & Hmodel)) & _ & HΦ)".
    iDestruct (chunk_model_update' j with "Hmodel") as "(H↦ & Hmodel)"; [lia | | done |].
    { destruct (nth_lookup_or_length vs (₊j - ₊i) inhabitant); [done | lia]. }
    wp_store.
    iApply ("HΦ" with "[H↦ Hmodel] H£").
    rewrite Nat2Z.id. iSteps.
  Qed.
  Lemma array_unsafe_set_spec_atomic_cell t (i : Z) v :
    <<<
      True
    | ∀∀ i_ w,
      ⌜i = ⁺i_⌝ ∗
      array_slice t i_ (DfracOwn 1) [w]
    >>>
      array_unsafe_set t #i v
    <<<
      array_slice t i_ (DfracOwn 1) [v]
    | RET ();
      £ 1
    >>>.
  Proof.
    iIntros "%Φ _ HΦ".
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
      array_model t (DfracOwn 1) (<[₊i := v]> vs)
    | RET ();
      £ 1
    >>>.
  Proof.
    iIntros "%Hi %Φ _ HΦ".
    awp_apply (array_unsafe_set_spec_atomic_slice with "[//]").
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs (%Hlookup & Hmodel)".
    iDestruct (array_model_to_slice' with "Hmodel") as "(Hslice & #?)".
    rewrite /atomic_acc /=.
    iExists vs, 0. rewrite Nat.sub_0_r. iSteps. simpl_length.
  Qed.
  Lemma array_unsafe_set_spec_atomic_inv t (sz : nat) (i : Z) v :
    (0 ≤ i < sz)%Z →
    <<<
      array_inv t sz
    | ∀∀ vs,
      array_model t (DfracOwn 1) vs
    >>>
      array_unsafe_set t #i v
    <<<
      array_model t (DfracOwn 1) (<[₊i := v]> vs)
    | RET ();
      £ 1
    >>>.
  Proof.
    iIntros "%Hi %Φ #Hinv HΦ".

    awp_apply (array_unsafe_set_spec_atomic with "[//]"); first lia.
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs Hmodel".
    iDestruct (array_inv_model_agree with "Hinv Hmodel") as %?.
    rewrite /atomic_acc /=.
    iFrameSteps.
  Qed.
  Lemma array_unsafe_set_spec_slice t i vs (j : Z) v :
    (i ≤ j < i + length vs)%Z →
    {{{
      array_slice t i (DfracOwn 1) vs
    }}}
      array_unsafe_set t #j v
    {{{
      RET ();
      array_slice t i (DfracOwn 1) (<[₊j - i := v]> vs)
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
    i = ⁺i_ →
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
      array_model t (DfracOwn 1) (<[₊i := v]> vs)
    }}}.
  Proof.
    setoid_rewrite array_model_to_slice' at 1.
    iIntros "%Hi %Φ (Hslice & #?) HΦ".
    wp_apply (array_unsafe_set_spec_slice with "Hslice"); [done.. | lia |].
    iSteps.
    - simpl_length.
    - rewrite Nat.sub_0_r //.
  Qed.

  Lemma array_set_spec_atomic_slice t sz (j : Z) v :
    <<<
      array_inv t sz
    | ∀∀ vs i,
      ⌜0 ≤ j < sz⌝%Z -∗
        ⌜i ≤ ₊j < i + length vs⌝ ∗
        array_slice t i (DfracOwn 1) vs
    >>>
      array_set t #j v
    <<<
      array_slice t i (DfracOwn 1) (<[₊j - i := v]> vs)
    | RET ();
      ⌜0 ≤ j < sz⌝%Z ∗
      £ 1
    >>>.
  Proof.
    iIntros "%Φ #Hinv HΦ".
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
    i_ = ₊i →
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
    iIntros (->) "%Φ #Hinv HΦ".
    awp_apply (array_set_spec_atomic_slice with "Hinv").
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%w Hslice".
    rewrite /atomic_acc /=.
    iExists [w], ₊i. rewrite Nat.sub_diag. iSplitL; first iSteps. iSplitR; last iSteps. iIntros "!> H". iSplitL; iSteps.
  Qed.
  Lemma array_set_spec_atomic t sz (i : Z) v :
    <<<
      array_inv t sz
    | ∀∀ vs,
      ⌜0 ≤ i < sz⌝%Z -∗
        ⌜(₊i < length vs)%Z⌝ ∗
        array_model t (DfracOwn 1) vs
    >>>
      array_set t #i v
    <<<
      array_model t (DfracOwn 1) (<[₊i := v]> vs)
    | RET ();
      ⌜0 ≤ i < sz⌝%Z ∗
      £ 1
    >>>.
  Proof.
    iIntros "%Φ #Hinv HΦ".
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
          ⌜i ≤ ₊j < i + length vs⌝ ∗
          array_slice t i (DfracOwn 1) vs
      )
    }}}
      array_set t #j v
    {{{
      RET ();
      ⌜0 ≤ j < sz⌝%Z ∗
      array_slice t i (DfracOwn 1) (<[₊j - i := v]> vs)
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
    i_ = ₊i →
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
    wp_apply (array_set_spec_slice _ _ ₊i [_] with "[$Hinv H]"); first iSteps.
    rewrite Nat.sub_diag //.
  Qed.
  Lemma array_set_spec t (i : Z) vs v :
    {{{
      array_model t (DfracOwn 1) vs
    }}}
      array_set t #i v
    {{{
      RET ();
      array_model t (DfracOwn 1) (<[₊i := v]> vs)
    }}}.
  Proof.
    iIntros "%Φ Hmodel HΦ".
    wp_rec.
    wp_smart_apply assume_spec' as "%Hi1".
    wp_smart_apply (array_size_spec with "Hmodel") as "Hmodel".
    wp_smart_apply assume_spec' as "%Hi2".
    wp_smart_apply (array_unsafe_set_spec with "Hmodel HΦ"); first done.
  Qed.

  Lemma array_unsafe_xchg_spec_atomic_slice t (j : Z) v :
    <<<
      True
    | ∀∀ vs i,
      ⌜i ≤ j < i + length vs⌝%Z ∗
      array_slice t i (DfracOwn 1) vs
    >>>
      array_unsafe_xchg t #j v
    <<<
      ∃∃ w,
      ⌜vs !! (₊j - i) = Some w⌝ ∗
      array_slice t i (DfracOwn 1) (<[₊j - i := v]> vs)
    | RET w;
      £ 1
    >>>.
  Proof.
    rewrite /array_model /array_slice.
    iIntros "%Φ _ HΦ".
    wp_rec credit:"H£". wp_pures.
    iMod "HΦ" as "(%vs & %i & (%Hj & (%l & -> & Hmodel)) & _ & HΦ)".
    destruct (lookup_lt_is_Some_2 vs (₊j - i)) as (w & Hlookup); first lia.
    iDestruct (chunk_model_update' j with "Hmodel") as "(H↦ & Hmodel)"; [lia | | done |].
    { rewrite Nat2Z.id //. }
    wp_xchg.
    iApply ("HΦ" with "[H↦ Hmodel] H£").
    rewrite Nat2Z.id. iSteps.
  Qed.
  Lemma array_unsafe_xchg_spec_atomic_cell t (i : Z) v :
    <<<
      True
    | ∀∀ i_ w,
      ⌜i = ⁺i_⌝ ∗
      array_slice t i_ (DfracOwn 1) [w]
    >>>
      array_unsafe_xchg t #i v
    <<<
      array_slice t i_ (DfracOwn 1) [v]
    | RET w;
      £ 1
    >>>.
  Proof.
    iIntros "%Φ _ HΦ".
    awp_apply (array_unsafe_xchg_spec_atomic_slice with "[//]").
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%i_ %w (-> & Hslice)".
    rewrite /atomic_acc /= Nat2Z.id.
    iExists [w], i_. rewrite Nat.sub_diag. iSteps.
  Qed.
  Lemma array_unsafe_xchg_spec_atomic t (i : Z) v :
    (0 ≤ i)%Z →
    <<<
      True
    | ∀∀ vs,
      ⌜i < length vs⌝%Z ∗
      array_model t (DfracOwn 1) vs
    >>>
      array_unsafe_xchg t #i v
    <<<
      ∃∃ w,
      ⌜vs !! ₊i = Some w⌝ ∗
      array_model t (DfracOwn 1) (<[₊i := v]> vs)
    | RET w;
      £ 1
    >>>.
  Proof.
    iIntros "%Hi %Φ _ HΦ".
    awp_apply (array_unsafe_xchg_spec_atomic_slice with "[//]").
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs (%Hlookup & Hmodel)".
    iDestruct (array_model_to_slice' with "Hmodel") as "(Hslice & #?)".
    rewrite /atomic_acc /=.
    iExists vs, 0. rewrite Nat.sub_0_r. iSteps. simpl_length.
  Qed.
  Lemma array_unsafe_xchg_spec_atomic_inv t (sz : nat) (i : Z) v :
    (0 ≤ i < sz)%Z →
    <<<
      array_inv t sz
    | ∀∀ vs,
      array_model t (DfracOwn 1) vs
    >>>
      array_unsafe_xchg t #i v
    <<<
      ∃∃ w,
      ⌜vs !! ₊i = Some w⌝ ∗
      array_model t (DfracOwn 1) (<[₊i := v]> vs)
    | RET w;
      £ 1
    >>>.
  Proof.
    iIntros "%Hi %Φ #Hinv HΦ".

    awp_apply (array_unsafe_xchg_spec_atomic with "[//]"); first lia.
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs Hmodel".
    iDestruct (array_inv_model_agree with "Hinv Hmodel") as %?.
    rewrite /atomic_acc /=.
    iFrameSteps.
  Qed.
  Lemma array_unsafe_xchg_spec_slice t i vs (j : Z) v :
    (i ≤ j < i + length vs)%Z →
    {{{
      array_slice t i (DfracOwn 1) vs
    }}}
      array_unsafe_xchg t #j v
    {{{ w,
      RET w;
      ⌜vs !! (₊j - i) = Some w⌝ ∗
      array_slice t i (DfracOwn 1) (<[₊j - i := v]> vs)
    }}}.
  Proof.
    iIntros "%Hj %Φ Hslice HΦ".
    iApply wp_fupd.
    awp_apply (array_unsafe_xchg_spec_atomic_slice with "[//]") without "HΦ".
    rewrite /atomic_acc /=.
    iExists vs, i.
    iApply fupd_mask_intro; first done. iIntros "Hclose".
    iSplitL "Hslice"; first auto. iSplit; first iSteps.
    iIntros "%w (%Hlookup & Hslice)". iMod "Hclose" as "_". iIntros "!> H£ HΦ".
    iMod (lc_fupd_elim_later with "H£ HΦ") as "HΦ".
    iSteps.
  Qed.
  Lemma array_unsafe_xchg_spec_cell t (i : Z) i_ w v :
    i = ⁺i_ →
    {{{
      array_slice t i_ (DfracOwn 1) [w]
    }}}
      array_unsafe_xchg t #i v
    {{{
      RET w;
      array_slice t i_ (DfracOwn 1) [v]
    }}}.
  Proof.
    iIntros (->) "%Φ Hslice HΦ".
    wp_apply (array_unsafe_xchg_spec_slice with "Hslice").
    { simpl. lia. }
    rewrite Nat2Z.id Nat.sub_diag. iSteps.
  Qed.
  Lemma array_unsafe_xchg_spec t (i : Z) vs v :
    (0 ≤ i < length vs)%Z →
    {{{
      array_model t (DfracOwn 1) vs
    }}}
      array_unsafe_xchg t #i v
    {{{ w,
      RET w;
      ⌜vs !! ₊i = Some w⌝ ∗
      array_model t (DfracOwn 1) (<[₊i := v]> vs)
    }}}.
  Proof.
    setoid_rewrite array_model_to_slice' at 1.
    iIntros "%Hi %Φ (Hslice & #?) HΦ".
    wp_apply (array_unsafe_xchg_spec_slice with "Hslice") as (w) "(%Hlookup & Hslice)"; [done.. | lia |].
    rewrite Nat.sub_0_r in Hlookup |- *. iSteps.
    simpl_length.
  Qed.

  Lemma array_unsafe_cas_spec_atomic_slice t (j : Z) v1 v2 :
    <<<
      True
    | ∀∀ vs i,
      ⌜i ≤ j < i + length vs⌝%Z ∗
      array_slice t i (DfracOwn 1) vs
    >>>
      array_unsafe_cas t #j v1 v2
    <<<
      ∃∃ b v,
      ⌜vs !! (₊j - i) = Some v⌝ ∗
      ⌜(if b then (≈) else (≉)) v v1⌝ ∗
      array_slice t i (DfracOwn 1) (if b then <[₊j - i := v2]> vs else vs)
    | RET #b;
      £ 1
    >>>.
  Proof.
    rewrite /array_model /array_slice.
    iIntros "%Φ _ HΦ".
    wp_rec credit:"H£". wp_pures.
    iMod "HΦ" as "(%vs & %i & (%Hj & (%l & -> & Hmodel)) & _ & HΦ)".
    destruct (lookup_lt_is_Some_2 vs (₊j - i)) as (v & Hlookup); first lia.
    iDestruct (chunk_model_update' j with "Hmodel") as "(H↦ & Hmodel)"; [lia | | done |].
    { rewrite Nat2Z.id //. }
    wp_cas.
    all: iApply ("HΦ" with "[H↦ Hmodel] H£").
    all: rewrite Nat2Z.id; iSteps.
    iDestruct ("Hmodel" with "H↦") as "Hmodel".
    rewrite list_insert_id //.
  Qed.
  Lemma array_unsafe_cas_spec_atomic_cell t (i : Z) v1 v2 :
    <<<
      True
    | ∀∀ i_ v,
      ⌜i = ⁺i_⌝ ∗
      array_slice t i_ (DfracOwn 1) [v]
    >>>
      array_unsafe_cas t #i v1 v2
    <<<
      ∃∃ b,
      ⌜(if b then (≈) else (≉)) v v1⌝ ∗
      array_slice t i_ (DfracOwn 1) [if b then v2 else v]
    | RET #b;
      £ 1
    >>>.
  Proof.
    iIntros "%Φ _ HΦ".
    awp_apply (array_unsafe_cas_spec_atomic_slice with "[//]").
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%i_ %v (-> & Hslice)".
    rewrite /atomic_acc /= Nat2Z.id.
    iExists [v], i_. rewrite Nat.sub_diag. iSteps as (v b ?) "Hslice".
    destruct b; iSteps.
  Qed.
  Lemma array_unsafe_cas_spec_atomic t (i : Z) v1 v2 :
    (0 ≤ i)%Z →
    <<<
      True
    | ∀∀ vs,
      ⌜i < length vs⌝%Z ∗
      array_model t (DfracOwn 1) vs
    >>>
      array_unsafe_cas t #i v1 v2
    <<<
      ∃∃ b v,
      ⌜vs !! ₊i = Some v⌝ ∗
      ⌜(if b then (≈) else (≉)) v v1⌝ ∗
      array_model t (DfracOwn 1) (if b then <[₊i := v2]> vs else vs)
    | RET #b;
      £ 1
    >>>.
  Proof.
    iIntros "%Hi %Φ _ HΦ".
    awp_apply (array_unsafe_cas_spec_atomic_slice with "[//]").
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs (%Hlookup & Hmodel)".
    iDestruct (array_model_to_slice' with "Hmodel") as "(Hslice & #?)".
    rewrite /atomic_acc /=.
    iExists vs, 0. rewrite Nat.sub_0_r. iSteps as (b) / --silent.
    iPureIntro. destruct b; simpl_length.
  Qed.
  Lemma array_unsafe_cas_spec_atomic_inv t (sz : nat) (i : Z) v1 v2 :
    (0 ≤ i < sz)%Z →
    <<<
      array_inv t sz
    | ∀∀ vs,
      array_model t (DfracOwn 1) vs
    >>>
      array_unsafe_cas t #i v1 v2
    <<<
      ∃∃ b v,
      ⌜vs !! ₊i = Some v⌝ ∗
      ⌜(if b then (≈) else (≉)) v v1⌝ ∗
      array_model t (DfracOwn 1) (if b then <[₊i := v2]> vs else vs)
    | RET #b;
      £ 1
    >>>.
  Proof.
    iIntros "%Hi %Φ #Hinv HΦ".

    awp_apply (array_unsafe_cas_spec_atomic with "[//]"); first lia.
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs Hmodel".
    iDestruct (array_inv_model_agree with "Hinv Hmodel") as %?.
    rewrite /atomic_acc /=.
    iFrameSteps.
  Qed.
  Lemma array_unsafe_cas_spec_slice t i vs (j : Z) v1 v2 :
    (i ≤ j < i + length vs)%Z →
    {{{
      array_slice t i (DfracOwn 1) vs
    }}}
      array_unsafe_cas t #j v1 v2
    {{{ b v,
      RET #b;
      ⌜vs !! (₊j - i) = Some v⌝ ∗
      ⌜(if b then (≈) else (≉)) v v1⌝ ∗
      array_slice t i (DfracOwn 1) (if b then <[₊j - i := v2]> vs else vs)
    }}}.
  Proof.
    iIntros "%Hj %Φ Hslice HΦ".
    iApply wp_fupd.
    awp_apply (array_unsafe_cas_spec_atomic_slice with "[//]") without "HΦ".
    rewrite /atomic_acc /=.
    iExists vs, i.
    iApply fupd_mask_intro; first done. iIntros "Hclose".
    iSplitL "Hslice"; first auto. iSplit; first iSteps.
    iIntros "%b %v (%Hlookup & % & Hslice)". iMod "Hclose" as "_". iIntros "!> H£ HΦ".
    iMod (lc_fupd_elim_later with "H£ HΦ") as "HΦ".
    iSteps.
  Qed.
  Lemma array_unsafe_cas_spec_cell t (i : Z) i_ v v1 v2 :
    i = ⁺i_ →
    {{{
      array_slice t i_ (DfracOwn 1) [v]
    }}}
      array_unsafe_cas t #i v1 v2
    {{{ b,
      RET #b;
      ⌜(if b then (≈) else (≉)) v v1⌝ ∗
      array_slice t i_ (DfracOwn 1) [if b then v2 else v]
    }}}.
  Proof.
    iIntros (->) "%Φ Hslice HΦ".
    wp_apply (array_unsafe_cas_spec_slice with "Hslice").
    { simpl. lia. }
    rewrite Nat2Z.id Nat.sub_diag. iSteps as (? b) / --silent.
    destruct b; iSteps.
  Qed.
  Lemma array_unsafe_cas_spec t (i : Z) vs v1 v2 :
    (0 ≤ i < length vs)%Z →
    {{{
      array_model t (DfracOwn 1) vs
    }}}
      array_unsafe_cas t #i v1 v2
    {{{ b v,
      RET #b;
      ⌜vs !! ₊i = Some v⌝ ∗
      ⌜(if b then (≈) else (≉)) v v1⌝ ∗
      array_model t (DfracOwn 1) (if b then <[₊i := v2]> vs else vs)
    }}}.
  Proof.
    setoid_rewrite array_model_to_slice' at 1.
    iIntros "%Hi %Φ (Hslice & #?) HΦ".
    wp_apply (array_unsafe_cas_spec_slice with "Hslice") as (b v) "(%Hlookup & % & Hslice)"; [done.. | lia |].
    rewrite Nat.sub_0_r in Hlookup |- *. iSteps.
    destruct b; simpl_length.
  Qed.

  Lemma array_unsafe_fill_slice_spec_atomic Ψ t (i n : Z) v :
    (0 ≤ i)%Z →
    {{{
      ▷ Ψ 0 ∗
      □ (
        ∀ j,
        ⌜j < ₊n⌝ -∗
        Ψ j -∗
        au_store t (₊i + j) v (
          ▷ Ψ (S j)
        )
      )
    }}}
      array_unsafe_fill_slice t #i #n v
    {{{
      RET ();
      Ψ ₊n
    }}}.
  Proof.
    iIntros "%Hi %Φ (HΨ & #H) HΦ".
    wp_rec.
    pose Ψ' (_ : Z) i :=
      Ψ i.
    wp_smart_apply (for_spec_strong Ψ' with "[$HΨ]"); last rewrite Z.sub_0_r //.
    iIntros "!> %j_ %j -> %Hj HΨ". rewrite Z.add_0_l in Hj |- *.
    iDestruct ("H" with "[%] HΨ") as "H'"; first lia.
    awp_smart_apply (array_unsafe_set_spec_atomic_cell with "[//]").
    iApply (aacc_aupd_commit with "H'"); first done. iIntros "%w H↦".
    rewrite /atomic_acc /=.
    repeat iExists _. iFrameSteps.
  Qed.
  Lemma array_unsafe_fill_slice_spec_slice_fit t vs (i : Z) i_ (n : Z) v :
    i = ⁺i_ →
    ₊n = length vs →
    {{{
      array_slice t i_ (DfracOwn 1) vs
    }}}
      array_unsafe_fill_slice t #i #n v
    {{{
      RET ();
      array_slice t i_ (DfracOwn 1) (replicate ₊n v)
    }}}.
  Proof.
    iIntros (-> Hn) "%Φ Hslice HΦ".
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
  Lemma array_unsafe_fill_slice_spec_slice t vs (i : Z) j (n : Z) v :
    (j ≤ i)%Z →
    ₊i + ₊n ≤ j + length vs →
    {{{
      array_slice t j (DfracOwn 1) vs
    }}}
      array_unsafe_fill_slice t #i #n v
    {{{
      RET ();
      array_slice t j (DfracOwn 1) (with_slice (₊i - j) ₊n vs (replicate ₊n v))
    }}}.
  Proof.
    iIntros "% % %Φ Hslice HΦ".
    iEval (setoid_rewrite <- (take_drop (₊i - j) vs)) in "Hslice".
    iEval (rewrite -(drop_take_drop _ _ (₊i - j + ₊n)); first lia) in "Hslice".
    iDestruct (array_slice_app_2 with "Hslice") as "(Hslice1 & Hslice2)"; first done.
    iDestruct (array_slice_app_2 with "Hslice2") as "(Hslice2 & Hslice3)"; first done.
    simpl_length. rewrite !Nat.min_l; [lia.. |].
    wp_apply (array_unsafe_fill_slice_spec_slice_fit with "Hslice2") as "Hslice2".
    { lia. }
    { simpl_length. lia. }
    iDestruct (array_slice_app_1' with "Hslice2 Hslice3") as "Hslice2".
    { simpl_length. lia. }
    iDestruct (array_slice_app_1' with "Hslice1 Hslice2") as "Hslice".
    { simpl_length. lia. }
    iSteps.
  Qed.
  Lemma array_unsafe_fill_slice_spec t vs (i : Z) (n : Z) v :
    (0 ≤ i)%Z →
    ₊i + ₊n ≤ length vs →
    {{{
      array_model t (DfracOwn 1) vs
    }}}
      array_unsafe_fill_slice t #i #n v
    {{{
      RET ();
      array_model t (DfracOwn 1) (with_slice ₊i ₊n vs (replicate ₊n v))
    }}}.
  Proof.
    iIntros "% % %Φ Hmodel HΦ".
    iDestruct (array_model_to_slice' with "Hmodel") as "(Hslice & Hmodel)".
    wp_apply (array_unsafe_fill_slice_spec_slice with "Hslice") as "Hslice"; [done.. |].
    iDestruct ("Hmodel" with "[%] Hslice") as "Hmodel".
    { simpl_length. lia. }
    rewrite Nat.sub_0_r. iSteps.
  Qed.

  Lemma array_fill_slice_spec t sz vs (i : Z) i_ (n : Z) v :
    i_ = ₊i →
    ₊n = length vs →
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
      array_slice t i_ (DfracOwn 1) (replicate ₊n v)
    }}}.
  Proof.
    iIntros (->) "%Hn %Φ (#Hinv & Hslice) HΦ".
    wp_rec.
    wp_smart_apply (array_size_spec_inv with "Hinv") as "_".
    repeat (wp_smart_apply assume_spec' as "%").
    wp_smart_apply (array_unsafe_fill_slice_spec_slice_fit with "Hslice"); [lia.. |].
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
    wp_apply (array_unsafe_fill_slice_spec_slice_fit with "Hslice") as "Hslice"; [lia.. |].
    iSteps.
    - simpl_length.
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
      array_model t (DfracOwn 1) (replicate ₊sz v)
    }}}.
  Proof.
    iIntros "% %Φ _ HΦ".
    wp_rec.
    wp_smart_apply (array_unsafe_alloc_spec with "[//]") as "%t Hmodel"; first done.
    wp_smart_apply (array_fill_spec with "Hmodel").
    simpl_length. iSteps.
  Qed.

  Lemma array_make_spec sz v :
    {{{
      True
    }}}
      array_make #sz v
    {{{ t,
      RET t;
      ⌜0 ≤ sz⌝%Z ∗
      array_model t (DfracOwn 1) (replicate ₊sz v)
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_rec.
    wp_smart_apply assume_spec' as "%Hsz".
    wp_smart_apply (array_unsafe_make_spec with "[//]"); first done.
    iSteps.
  Qed.

  #[local] Lemma array_foldli_aux_spec vs Ψ fn t sz i acc :
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
            WP fn #i acc v {{ acc,
              ▷ Ψ (S i) (vs ++ [v]) None acc
            }}
        end
      )
    }}}
      array_foldli_aux fn t #sz #i acc
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
      repeat iExists _. iFrameStep 2; first iSteps. iIntros "$ !> HΨ !> H£ HΦ".
      iMod (lc_fupd_elim_later with "H£ HΨ") as "HΨ".
      wp_smart_apply (wp_wand with "(H [%] [//] HΨ)") as "%acc' HΨ"; first lia.
      wp_pures.
      rewrite Z.add_1_r -Nat2Z.inj_succ.
      wp_apply ("IH" with "[%] [%] [%] HΨ [HΦ]"); simpl_length; [naive_solver lia.. |].
      clear acc. iIntros "!> %vs' %acc (<- & HΨ)".
      iApply ("HΦ" $! (v :: vs')).
      rewrite -(assoc (++)). iSteps.
  Qed.
  Lemma array_foldli_spec_atomic Ψ fn acc t sz :
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
            WP fn #i acc v {{ acc,
              ▷ Ψ (S i) (vs ++ [v]) None acc
            }}
        end
      )
    }}}
      array_foldli fn acc t
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
    wp_apply (array_foldli_aux_spec [] Ψ with "[$HΨ] HΦ"); [lia | done |].
    iSteps.
  Qed.
  Lemma array_foldli_spec Ψ fn acc t dq vs :
    {{{
      ▷ Ψ 0 [] acc ∗
      array_model t dq vs ∗
      □ (
        ∀ i v acc,
        ⌜vs !! i = Some v⌝ -∗
        Ψ i (take i vs) acc -∗
        WP fn #i acc v {{ acc,
          ▷ Ψ (S i) (take i vs ++ [v]) acc
        }}
      )
    }}}
      array_foldli fn acc t
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
  Lemma array_foldli_spec' Ψ fn acc t dq vs :
    {{{
      ▷ Ψ 0 [] acc ∗
      array_model t dq vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        ∀ acc,
        Ψ i (take i vs) acc -∗
        WP fn #i acc v {{ acc,
          ▷ Ψ (S i) (take i vs ++ [v]) acc
        }}
      )
    }}}
      array_foldli fn acc t
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

  Lemma array_foldl_spec_atomic Ψ fn acc t sz :
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
      array_foldl fn acc t
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
  Lemma array_foldl_spec Ψ fn acc t dq vs :
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
      array_foldl fn acc t
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
  Lemma array_foldl_spec' Ψ fn acc t dq vs :
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
      array_foldl fn acc t
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

  #[local] Lemma array_foldri_aux_spec sz vs Ψ fn t (i : Z) acc :
    ₊i + length vs = sz →
    {{{
      ▷ Ψ ₊i acc None vs ∗
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
      array_foldri_aux fn t #i acc
    {{{ acc vs',
      RET acc;
      ⌜(length vs' + length vs)%nat = sz⌝ ∗
      Ψ 0 acc None (vs' ++ vs)
    }}}.
  Proof.
    iIntros "%Hi %Φ (HΨ & #H) HΦ".
    remember ₊i as j eqn:Hj.
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
      repeat iExists _. iFrameStep 2; first iSteps. iIntros "$ !> HΨ !> H£ HΦ".
      iMod (lc_fupd_elim_later with "H£ HΨ") as "HΨ".
      wp_smart_apply (wp_wand with "(H [%] HΨ)") as "%acc' HΨ"; first lia.
      wp_apply ("IH" with "[] [] HΨ [HΦ]"); simpl_length; [iSteps.. |]. clear acc. iIntros "!> %acc %vs' (<- & HΨ)".
      iApply ("HΦ" $! _ (vs' ++ [v])).
      rewrite length_app -(assoc (++)). iSteps.
  Qed.
  Lemma array_foldri_spec_atomic Ψ fn t sz acc :
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
      array_foldri fn t acc
    {{{ acc vs,
      RET acc;
      ⌜length vs = sz⌝ ∗
      Ψ 0 acc None vs
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & HΨ & #H) HΦ".
    wp_rec.
    wp_smart_apply (array_size_spec_inv with "Hinv") as "_".
    wp_apply (array_foldri_aux_spec sz [] Ψ with "[HΨ $H]").
    { rewrite right_id. lia. }
    { rewrite Nat2Z.id //. }
    clear acc. iIntros "%acc %vs".
    rewrite !right_id. iSteps.
  Qed.
  Lemma array_foldri_spec Ψ fn t dq vs acc :
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
      array_foldri fn t acc
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
        iSteps; iPureIntro; simpl_length; f_equal; lia.
  Qed.
  Lemma array_foldri_spec' Ψ fn t dq vs acc :
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
      array_foldri fn t acc
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

  Lemma array_foldr_spec_atomic Ψ fn t sz acc :
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
      array_foldr fn t acc
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
  Lemma array_foldr_spec Ψ fn t dq vs acc :
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
      array_foldr fn t acc
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
  Lemma array_foldr_spec' Ψ fn t dq vs acc :
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
      array_foldr fn t acc
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

  Lemma array_unsafe_iteri_slice_spec_atomic Ψ fn t (sz : nat) (i n : Z) :
    (0 ≤ i ≤ sz)%Z →
    (0 ≤ n)%Z →
    (i + n ≤ sz)%Z →
    {{{
      array_inv t sz ∗
      ▷ Ψ 0 [] None ∗
      □ (
        ∀ k vs (o : option val),
        ⌜k < ₊n⌝ -∗
        ⌜k = length vs⌝ -∗
        Ψ k vs o -∗
        match o with
        | None =>
            au_load t (₊i + k) (λ v,
              ▷ Ψ k vs (Some v)
            )
        | Some v =>
            WP fn #k v {{ res,
              ⌜res = ()%V⌝ ∗
              ▷ Ψ (S k) (vs ++ [v]) None
            }}
        end
      )
    }}}
      array_unsafe_iteri_slice fn t #i #n
    {{{ vs,
      RET ();
      ⌜length vs = ₊n⌝ ∗
      Ψ ₊n vs None
    }}}.
  Proof.
    iIntros "% % % %Φ (#Hinv & HΨ & #H) HΦ".
    wp_rec.
    pose Ψ' (_ : Z) k := (
      ∃ vs,
      ⌜length vs = k⌝ ∗
      Ψ k vs None
    )%I.
    wp_smart_apply (for_spec_strong Ψ' with "[HΨ]").
    { iSplitL. { iExists []. iSteps. }
      iIntros "!> %k_ %k -> %Hk (%vs & %Hvs & HΨ)".
      iDestruct ("H" with "[%] [//] HΨ") as "H'"; first lia.
      awp_smart_apply (array_unsafe_get_spec_atomic_cell with "[//]").
      iApply (aacc_aupd_commit with "H'"); first done. iIntros "%dq %v H↦".
      rewrite /atomic_acc /=.
      repeat iExists _. iFrameStep 2; first iSteps. iIntros "H↦ !>".
      rewrite Z2Nat.inj_add; [lia.. |]. rewrite Nat2Z.id. iFrame.
      iIntros "HΨ !> H£".
      iMod (lc_fupd_elim_later with "H£ HΨ") as "HΨ".
      wp_smart_apply (wp_wand with "(H [%] [//] HΨ)") as "%acc' (-> & HΨ)"; first lia.
      iSteps. iExists (vs ++ [v]). simpl_length. iSteps.
    }
    rewrite right_id. iSteps.
  Qed.
  Lemma array_unsafe_iteri_slice_spec Ψ fn t dq vs (i n : Z) :
    (0 ≤ i ≤ length vs)%Z →
    (0 ≤ n)%Z →
    (i + n ≤ length vs)%Z →
    {{{
      ▷ Ψ 0 [] ∗
      array_model t dq vs ∗
      □ (
        ∀ k v,
        ⌜k < ₊n⌝ -∗
        ⌜vs !! (₊i + k)%nat = Some v⌝ -∗
        Ψ k (slice ₊i k vs) -∗
        WP fn #k v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ (S k) (slice ₊i k vs ++ [v])
        }}
      )
    }}}
      array_unsafe_iteri_slice fn t #i #n
    {{{
      RET ();
      array_model t dq vs ∗
      Ψ ₊n (slice ₊i ₊n vs)
    }}}.
  Proof.
    iIntros "% % % %Φ (HΨ & Hmodel & #Hfn) HΦ".
    iDestruct (array_model_to_inv with "Hmodel") as "#Hinv".
    pose (Ψ' k vs_left o := (
      ⌜vs_left = slice ₊i k vs⌝ ∗
      array_model t dq vs ∗
      Ψ k vs_left ∗
      ⌜from_option (λ v, vs !! (₊i + k)%nat = Some v) True o⌝%I
    )%I).
    wp_smart_apply (array_unsafe_iteri_slice_spec_atomic Ψ' with "[$Hinv $Hmodel $HΨ]"); [done.. | | iSteps].
    iStep. iIntros "!> %k %vs_left %o %Hk1 %Hk2 (-> & Hmodel & HΨ & %Ho)".
    destruct o as [v |].
    - wp_apply (wp_wand with "(Hfn [//] [//] HΨ)") as (res) "(-> & HΨ)".
      rewrite slice_snoc //. iSteps.
    - opose proof* (list_lookup_lookup_total_lt vs (₊i + k)); first lia.
      iDestruct (array_model_lookup_acc with "Hmodel") as "(H↦ & Hmodel)"; first done.
      iAuIntro. iAaccIntro with "H↦"; iSteps.
  Qed.
  Lemma array_unsafe_iteri_slice_spec' Ψ fn t dq vs (i n : Z) :
    (0 ≤ i ≤ length vs)%Z →
    (0 ≤ n)%Z →
    (i + n ≤ length vs)%Z →
    {{{
      ▷ Ψ 0 [] ∗
      array_model t dq vs ∗
      ( [∗ list] k ↦ v ∈ slice ₊i ₊n vs,
        Ψ k (slice ₊i k vs) -∗
        WP fn #k v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ (S k) (slice ₊i k vs ++ [v])
        }}
      )
    }}}
      array_unsafe_iteri_slice fn t #i #n
    {{{
      RET ();
      array_model t dq vs ∗
      Ψ ₊n (slice ₊i ₊n vs)
    }}}.
  Proof.
    iIntros "% % % %Φ (HΨ & Hmodel & Hfn) HΦ".
    match goal with |- context [big_opL bi_sep ?Ξ' _] => set Ξ := Ξ' end.
    pose (Ψ' k vs_left := (
      Ψ k vs_left ∗
      [∗ list] j ↦ v ∈ slice (₊i + k) (₊n - k) vs, Ξ (k + j) v
    )%I).
    wp_apply (array_unsafe_iteri_slice_spec Ψ' with "[$HΨ $Hmodel Hfn]"); [done.. | | iSteps].
    rewrite !right_id. iFrame.
    iIntros "!> %k %v %Hk %Hlookup (HΨ & HΞ)".
    rewrite -(slice_cons' (₊i + k) _ v) //; first lia.
    iDestruct "HΞ" as "(Hfn & HΞ)".
    setoid_rewrite Nat.add_succ_r.
    rewrite Nat.add_0_r -Nat.add_succ_r -Nat.sub_add_distr Nat.add_1_r.
    iSteps.
  Qed.
  Lemma array_unsafe_iteri_slice_spec_disentangled Ψ fn t dq vs (i n : Z) :
    (0 ≤ i ≤ length vs)%Z →
    (0 ≤ n)%Z →
    (i + n ≤ length vs)%Z →
    {{{
      array_model t dq vs ∗
      □ (
        ∀ k v,
        ⌜k < ₊n⌝ -∗
        ⌜vs !! (₊i + k)%nat = Some v⌝ -∗
        WP fn #k v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ k v
        }}
      )
    }}}
      array_unsafe_iteri_slice fn t #i #n
    {{{
      RET ();
      array_model t dq vs ∗
      ( [∗ list] k ↦ v ∈ slice ₊i ₊n vs,
        Ψ k v
      )
    }}}.
  Proof.
    iIntros "% % % %Φ (Hmodel & #Hfn) HΦ".
    pose (Ψ' k vs := (
      [∗ list] j ↦ v ∈ vs, Ψ j v
    )%I).
    wp_apply (array_unsafe_iteri_slice_spec Ψ' with "[$Hmodel]"); [done.. | | iSteps].
    rewrite /Ψ'. iSteps.
    rewrite big_sepL_snoc length_slice'; first lia. iSteps.
  Qed.
  Lemma array_unsafe_iteri_slice_spec_disentangled' Ψ fn t dq vs (i n : Z) :
    (0 ≤ i ≤ length vs)%Z →
    (0 ≤ n)%Z →
    (i + n ≤ length vs)%Z →
    {{{
      array_model t dq vs ∗
      ( [∗ list] k ↦ v ∈ slice ₊i ₊n vs,
        WP fn #k v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ k v
        }}
      )
    }}}
      array_unsafe_iteri_slice fn t #i #n
    {{{
      RET ();
      array_model t dq vs ∗
      ( [∗ list] k ↦ v ∈ slice ₊i ₊n vs,
        Ψ k v
      )
    }}}.
  Proof.
    iIntros "% % % %Φ (Hmodel & Hfn) HΦ".
    pose (Ψ' k vs := (
      [∗ list] j ↦ v ∈ vs, Ψ j v
    )%I).
    wp_apply (array_unsafe_iteri_slice_spec' Ψ' with "[$Hmodel Hfn]"); [done.. | | iSteps].
    rewrite /Ψ'. iSteps.
    iApply (big_sepL_impl with "Hfn").
    iSteps as (k v Hk%slice_lookup_Some_inv) / --silent.
    rewrite big_sepL_snoc length_slice'; first lia. iSteps.
  Qed.

  Lemma array_iteri_slice_spec_atomic Ψ fn t (sz : nat) (i n : Z) :
    {{{
      array_inv t sz ∗
      ▷ Ψ 0 [] None ∗
      □ (
        ∀ k vs (o : option val),
        ⌜k < ₊n⌝ -∗
        ⌜k = length vs⌝ -∗
        Ψ k vs o -∗
        match o with
        | None =>
            au_load t (₊i + k) (λ v,
              ▷ Ψ k vs (Some v)
            )
        | Some v =>
            WP fn #k v {{ res,
              ⌜res = ()%V⌝ ∗
              ▷ Ψ (S k) (vs ++ [v]) None
            }}
        end
      )
    }}}
      array_iteri_slice fn t #i #n
    {{{ vs,
      RET ();
      ⌜0 ≤ i ≤ sz⌝%Z ∗
      ⌜0 ≤ n⌝%Z ∗
      ⌜i + n ≤ sz⌝%Z ∗
      ⌜length vs = ₊n⌝ ∗
      Ψ ₊n vs None
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & HΨ & H) HΦ".
    wp_rec.
    do 2 (wp_smart_apply assume_spec' as "%").
    wp_smart_apply (array_size_spec_inv with "Hinv") as "_".
    do 2 (wp_smart_apply assume_spec' as "%").
    wp_smart_apply (array_unsafe_iteri_slice_spec_atomic Ψ with "[$Hinv $HΨ $H]"); [done.. |].
    iSteps.
  Qed.
  Lemma array_iteri_slice_spec Ψ fn t dq vs (i n : Z) :
    {{{
      ▷ Ψ 0 [] ∗
      array_model t dq vs ∗
      □ (
        ∀ k v,
        ⌜k < ₊n⌝ -∗
        ⌜vs !! (₊i + k)%nat = Some v⌝ -∗
        Ψ k (slice ₊i k vs) -∗
        WP fn #k v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ (S k) (slice ₊i k vs ++ [v])
        }}
      )
    }}}
      array_iteri_slice fn t #i #n
    {{{
      RET ();
      ⌜0 ≤ i ≤ length vs⌝%Z ∗
      ⌜0 ≤ n⌝%Z ∗
      ⌜i + n ≤ length vs⌝%Z ∗
      array_model t dq vs ∗
      Ψ ₊n (slice ₊i ₊n vs)
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hmodel & #Hfn) HΦ".
    wp_rec.
    do 2 (wp_smart_apply assume_spec' as "%").
    wp_smart_apply (array_size_spec with "Hmodel") as "Hmodel".
    do 2 (wp_smart_apply assume_spec' as "%").
    wp_smart_apply (array_unsafe_iteri_slice_spec Ψ with "[$HΨ $Hmodel $Hfn]"); [done.. |].
    iSteps.
  Qed.
  Lemma array_iteri_slice_spec' Ψ fn t dq vs (i n : Z) :
    {{{
      ▷ Ψ 0 [] ∗
      array_model t dq vs ∗
      ( [∗ list] k ↦ v ∈ slice ₊i ₊n vs,
        Ψ k (slice ₊i k vs) -∗
        WP fn #k v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ (S k) (slice ₊i k vs ++ [v])
        }}
      )
    }}}
      array_iteri_slice fn t #i #n
    {{{
      RET ();
      ⌜0 ≤ i ≤ length vs⌝%Z ∗
      ⌜0 ≤ n⌝%Z ∗
      ⌜i + n ≤ length vs⌝%Z ∗
      array_model t dq vs ∗
      Ψ ₊n (slice ₊i ₊n vs)
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hmodel & Hfn) HΦ".
    wp_rec.
    do 2 (wp_smart_apply assume_spec' as "%").
    wp_smart_apply (array_size_spec with "Hmodel") as "Hmodel".
    do 2 (wp_smart_apply assume_spec' as "%").
    wp_smart_apply (array_unsafe_iteri_slice_spec' Ψ with "[$HΨ $Hmodel Hfn]"); [done.. |].
    iSteps.
  Qed.
  Lemma array_iteri_slice_spec_disentangled Ψ fn t dq vs (i n : Z) :
    {{{
      array_model t dq vs ∗
      □ (
        ∀ k v,
        ⌜k < ₊n⌝ -∗
        ⌜vs !! (₊i + k)%nat = Some v⌝ -∗
        WP fn #k v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ k v
        }}
      )
    }}}
      array_iteri_slice fn t #i #n
    {{{
      RET ();
      ⌜0 ≤ i ≤ length vs⌝%Z ∗
      ⌜0 ≤ n⌝%Z ∗
      ⌜i + n ≤ length vs⌝%Z ∗
      array_model t dq vs ∗
      ( [∗ list] k ↦ v ∈ slice ₊i ₊n vs,
        Ψ k v
      )
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & #Hfn) HΦ".
    wp_rec.
    do 2 (wp_smart_apply assume_spec' as "%").
    wp_smart_apply (array_size_spec with "Hmodel") as "Hmodel".
    do 2 (wp_smart_apply assume_spec' as "%").
    wp_smart_apply (array_unsafe_iteri_slice_spec_disentangled Ψ with "[$Hmodel $Hfn]"); [done.. |].
    iSteps.
  Qed.
  Lemma array_iteri_slice_spec_disentangled' Ψ fn t dq vs (i n : Z) :
    {{{
      array_model t dq vs ∗
      ( [∗ list] k ↦ v ∈ slice ₊i ₊n vs,
        WP fn #k v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ k v
        }}
      )
    }}}
      array_iteri_slice fn t #i #n
    {{{
      RET ();
      ⌜0 ≤ i ≤ length vs⌝%Z ∗
      ⌜0 ≤ n⌝%Z ∗
      ⌜i + n ≤ length vs⌝%Z ∗
      array_model t dq vs ∗
      ( [∗ list] k ↦ v ∈ slice ₊i ₊n vs,
        Ψ k v
      )
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & Hfn) HΦ".
    wp_rec.
    do 2 (wp_smart_apply assume_spec' as "%").
    wp_smart_apply (array_size_spec with "Hmodel") as "Hmodel".
    do 2 (wp_smart_apply assume_spec' as "%").
    wp_smart_apply (array_unsafe_iteri_slice_spec_disentangled' Ψ with "[$Hmodel $Hfn]"); [done.. |].
    iSteps.
  Qed.

  Lemma array_unsafe_iter_slice_spec_atomic Ψ fn t (sz : nat) (i n : Z) :
    (0 ≤ i ≤ sz)%Z →
    (0 ≤ n)%Z →
    (i + n ≤ sz)%Z →
    {{{
      array_inv t sz ∗
      ▷ Ψ 0 [] None ∗
      □ (
        ∀ k vs (o : option val),
        ⌜k < ₊n⌝ -∗
        ⌜k = length vs⌝ -∗
        Ψ k vs o -∗
        match o with
        | None =>
            au_load t (₊i + k) (λ v,
              ▷ Ψ k vs (Some v)
            )
        | Some v =>
            WP fn v {{ res,
              ⌜res = ()%V⌝ ∗
              ▷ Ψ (S k) (vs ++ [v]) None
            }}
        end
      )
    }}}
      array_unsafe_iter_slice fn t #i #n
    {{{ vs,
      RET ();
      ⌜length vs = ₊n⌝ ∗
      Ψ ₊n vs None
    }}}.
  Proof.
    iIntros "% % % %Φ (Hinv & HΨ & #H) HΦ".
    wp_rec.
    wp_smart_apply (array_unsafe_iteri_slice_spec_atomic Ψ with "[$Hinv $HΨ]"); [done.. | | iSteps].
    iSteps.
    select (option val) (fun o => iSpecialize ("H" $! _ _ o)).
    case_match; iSteps.
  Qed.
  Lemma array_unsafe_iter_slice_spec Ψ fn t dq vs (i n : Z) :
    (0 ≤ i ≤ length vs)%Z →
    (0 ≤ n)%Z →
    (i + n ≤ length vs)%Z →
    {{{
      ▷ Ψ 0 [] ∗
      array_model t dq vs ∗
      □ (
        ∀ k v,
        ⌜k < ₊n⌝ -∗
        ⌜vs !! (₊i + k)%nat = Some v⌝ -∗
        Ψ k (slice ₊i k vs) -∗
        WP fn v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ (S k) (slice ₊i k vs ++ [v])
        }}
      )
    }}}
      array_unsafe_iter_slice fn t #i #n
    {{{
      RET ();
      array_model t dq vs ∗
      Ψ ₊n (slice ₊i ₊n vs)
    }}}.
  Proof.
    iIntros "% % % %Φ (HΨ & Hmodel & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (array_unsafe_iteri_slice_spec Ψ with "[$HΨ $Hmodel]"); [done.. | | iSteps].
    iSteps.
  Qed.
  Lemma array_unsafe_iter_slice_spec' Ψ fn t dq vs (i n : Z) :
    (0 ≤ i ≤ length vs)%Z →
    (0 ≤ n)%Z →
    (i + n ≤ length vs)%Z →
    {{{
      ▷ Ψ 0 [] ∗
      array_model t dq vs ∗
      ( [∗ list] k ↦ v ∈ slice ₊i ₊n vs,
        Ψ k (slice ₊i k vs) -∗
        WP fn v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ (S k) (slice ₊i k vs ++ [v])
        }}
      )
    }}}
      array_unsafe_iter_slice fn t #i #n
    {{{
      RET ();
      array_model t dq vs ∗
      Ψ ₊n (slice ₊i ₊n vs)
    }}}.
  Proof.
    iIntros "% % % %Φ (HΨ & Hmodel & Hfn) HΦ".
    wp_rec.
    wp_smart_apply (array_unsafe_iteri_slice_spec' Ψ with "[$HΨ $Hmodel Hfn]"); [done.. | | iSteps].
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.
  Lemma array_unsafe_iter_slice_spec_disentangled Ψ fn t dq vs (i n : Z) :
    (0 ≤ i ≤ length vs)%Z →
    (0 ≤ n)%Z →
    (i + n ≤ length vs)%Z →
    {{{
      array_model t dq vs ∗
      □ (
        ∀ k v,
        ⌜k < ₊n⌝ -∗
        ⌜vs !! (₊i + k)%nat = Some v⌝ -∗
        WP fn v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ k v
        }}
      )
    }}}
      array_unsafe_iter_slice fn t #i #n
    {{{
      RET ();
      array_model t dq vs ∗
      ( [∗ list] k ↦ v ∈ slice ₊i ₊n vs,
        Ψ k v
      )
    }}}.
  Proof.
    iIntros "% % % %Φ (Hmodel & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (array_unsafe_iteri_slice_spec_disentangled Ψ with "[$Hmodel]"); [done.. | | iSteps].
    iSteps.
  Qed.
  Lemma array_unsafe_iter_slice_spec_disentangled' Ψ fn t dq vs (i n : Z) :
    (0 ≤ i ≤ length vs)%Z →
    (0 ≤ n)%Z →
    (i + n ≤ length vs)%Z →
    {{{
      array_model t dq vs ∗
      ( [∗ list] k ↦ v ∈ slice ₊i ₊n vs,
        WP fn v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ k v
        }}
      )
    }}}
      array_unsafe_iter_slice fn t #i #n
    {{{
      RET ();
      array_model t dq vs ∗
      ( [∗ list] k ↦ v ∈ slice ₊i ₊n vs,
        Ψ k v
      )
    }}}.
  Proof.
    iIntros "% % % %Φ (Hmodel & Hfn) HΦ".
    wp_rec.
    wp_smart_apply (array_unsafe_iteri_slice_spec_disentangled' Ψ with "[$Hmodel Hfn]"); [done.. | | iSteps].
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.

  Lemma array_iter_slice_spec_atomic Ψ fn t (sz : nat) (i n : Z) :
    {{{
      array_inv t sz ∗
      ▷ Ψ 0 [] None ∗
      □ (
        ∀ k vs (o : option val),
        ⌜k < ₊n⌝ -∗
        ⌜k = length vs⌝ -∗
        Ψ k vs o -∗
        match o with
        | None =>
            au_load t (₊i + k) (λ v,
              ▷ Ψ k vs (Some v)
            )
        | Some v =>
            WP fn v {{ res,
              ⌜res = ()%V⌝ ∗
              ▷ Ψ (S k) (vs ++ [v]) None
            }}
        end
      )
    }}}
      array_iter_slice fn t #i #n
    {{{ vs,
      RET ();
      ⌜0 ≤ i ≤ sz⌝%Z ∗
      ⌜0 ≤ n⌝%Z ∗
      ⌜i + n ≤ sz⌝%Z ∗
      ⌜length vs = ₊n⌝ ∗
      Ψ ₊n vs None
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & HΨ & H) HΦ".
    wp_rec.
    do 2 (wp_smart_apply assume_spec' as "%").
    wp_smart_apply (array_size_spec_inv with "Hinv") as "_".
    do 2 (wp_smart_apply assume_spec' as "%").
    wp_smart_apply (array_unsafe_iter_slice_spec_atomic Ψ with "[$Hinv $HΨ $H]"); [done.. |].
    iSteps.
  Qed.
  Lemma array_iter_slice_spec Ψ fn t dq vs (i n : Z) :
    {{{
      ▷ Ψ 0 [] ∗
      array_model t dq vs ∗
      □ (
        ∀ k v,
        ⌜k < ₊n⌝ -∗
        ⌜vs !! (₊i + k)%nat = Some v⌝ -∗
        Ψ k (slice ₊i k vs) -∗
        WP fn v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ (S k) (slice ₊i k vs ++ [v])
        }}
      )
    }}}
      array_iter_slice fn t #i #n
    {{{
      RET ();
      ⌜0 ≤ i ≤ length vs⌝%Z ∗
      ⌜0 ≤ n⌝%Z ∗
      ⌜i + n ≤ length vs⌝%Z ∗
      array_model t dq vs ∗
      Ψ ₊n (slice ₊i ₊n vs)
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hmodel & #Hfn) HΦ".
    wp_rec.
    do 2 (wp_smart_apply assume_spec' as "%").
    wp_smart_apply (array_size_spec with "Hmodel") as "Hmodel".
    do 2 (wp_smart_apply assume_spec' as "%").
    wp_smart_apply (array_unsafe_iter_slice_spec Ψ with "[$HΨ $Hmodel $Hfn]"); [done.. |].
    iSteps.
  Qed.
  Lemma array_iter_slice_spec' Ψ fn t dq vs (i n : Z) :
    {{{
      ▷ Ψ 0 [] ∗
      array_model t dq vs ∗
      ( [∗ list] k ↦ v ∈ slice ₊i ₊n vs,
        Ψ k (slice ₊i k vs) -∗
        WP fn v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ (S k) (slice ₊i k vs ++ [v])
        }}
      )
    }}}
      array_iter_slice fn t #i #n
    {{{
      RET ();
      ⌜0 ≤ i ≤ length vs⌝%Z ∗
      ⌜0 ≤ n⌝%Z ∗
      ⌜i + n ≤ length vs⌝%Z ∗
      array_model t dq vs ∗
      Ψ ₊n (slice ₊i ₊n vs)
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hmodel & Hfn) HΦ".
    wp_rec.
    do 2 (wp_smart_apply assume_spec' as "%").
    wp_smart_apply (array_size_spec with "Hmodel") as "Hmodel".
    do 2 (wp_smart_apply assume_spec' as "%").
    wp_smart_apply (array_unsafe_iter_slice_spec' Ψ with "[$HΨ $Hmodel Hfn]"); [done.. |].
    iSteps.
  Qed.
  Lemma array_iter_slice_spec_disentangled Ψ fn t dq vs (i n : Z) :
    {{{
      array_model t dq vs ∗
      □ (
        ∀ k v,
        ⌜k < ₊n⌝ -∗
        ⌜vs !! (₊i + k)%nat = Some v⌝ -∗
        WP fn v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ k v
        }}
      )
    }}}
      array_iter_slice fn t #i #n
    {{{
      RET ();
      ⌜0 ≤ i ≤ length vs⌝%Z ∗
      ⌜0 ≤ n⌝%Z ∗
      ⌜i + n ≤ length vs⌝%Z ∗
      array_model t dq vs ∗
      ( [∗ list] k ↦ v ∈ slice ₊i ₊n vs,
        Ψ k v
      )
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & #Hfn) HΦ".
    wp_rec.
    do 2 (wp_smart_apply assume_spec' as "%").
    wp_smart_apply (array_size_spec with "Hmodel") as "Hmodel".
    do 2 (wp_smart_apply assume_spec' as "%").
    wp_smart_apply (array_unsafe_iter_slice_spec_disentangled Ψ with "[$Hmodel $Hfn]"); [done.. |].
    iSteps.
  Qed.
  Lemma array_iter_slice_spec_disentangled' Ψ fn t dq vs (i n : Z) :
    {{{
      array_model t dq vs ∗
      ( [∗ list] k ↦ v ∈ slice ₊i ₊n vs,
        WP fn v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ k v
        }}
      )
    }}}
      array_iter_slice fn t #i #n
    {{{
      RET ();
      ⌜0 ≤ i ≤ length vs⌝%Z ∗
      ⌜0 ≤ n⌝%Z ∗
      ⌜i + n ≤ length vs⌝%Z ∗
      array_model t dq vs ∗
      ( [∗ list] k ↦ v ∈ slice ₊i ₊n vs,
        Ψ k v
      )
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & Hfn) HΦ".
    wp_rec.
    do 2 (wp_smart_apply assume_spec' as "%").
    wp_smart_apply (array_size_spec with "Hmodel") as "Hmodel".
    do 2 (wp_smart_apply assume_spec' as "%").
    wp_smart_apply (array_unsafe_iter_slice_spec_disentangled' Ψ with "[$Hmodel $Hfn]"); [done.. |].
    iSteps.
  Qed.

  Lemma array_iteri_spec_atomic Ψ fn t sz :
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
      array_iteri fn t
    {{{ vs,
      RET ();
      ⌜length vs = sz⌝ ∗
      Ψ sz vs None
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & HΨ & #H) HΦ".
    wp_rec.
    wp_smart_apply (array_size_spec_inv with "Hinv") as "_".
    wp_apply (array_unsafe_iteri_slice_spec_atomic Ψ with "[$Hinv $HΨ]"); [lia.. | iSteps |].
    rewrite Nat2Z.id. iSteps.
  Qed.
  Lemma array_iteri_spec Ψ fn t dq vs :
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
      array_iteri fn t
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
  Lemma array_iteri_spec' Ψ fn t dq vs :
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
      array_iteri fn t
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
  Lemma array_iteri_spec_disentangled Ψ fn t dq vs :
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
      array_iteri fn t
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
  Lemma array_iteri_spec_disentangled' Ψ fn t dq vs :
    {{{
      array_model t dq vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        WP fn #i v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ i v
        }}
      )
    }}}
      array_iteri fn t
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

  Lemma array_iter_spec_atomic Ψ fn t sz :
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
      array_iter fn t
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
  Lemma array_iter_spec Ψ fn t dq vs :
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
      array_iter fn t
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
  Lemma array_iter_spec' Ψ fn t dq vs :
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
      array_iter fn t
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
  Lemma array_iter_spec_disentangled Ψ fn t dq vs :
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
      array_iter fn t
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
  Lemma array_iter_spec_disentangled' Ψ fn t dq vs :
    {{{
      array_model t dq vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        WP fn v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ i v
        }}
      )
    }}}
      array_iter fn t
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

  Lemma array_unsafe_applyi_slice_spec_atomic Ψ fn t (sz : nat) (i n : Z) :
    (0 ≤ i ≤ sz)%Z →
    (0 ≤ n)%Z →
    (i + n ≤ sz)%Z →
    {{{
      array_inv t sz ∗
      ▷ Ψ 0 [] None [] ∗
      □ (
        ∀ k vs (o : option (val + val * val)) ws,
        ⌜k < ₊n⌝ -∗
        ⌜k = length vs⌝ -∗
        ⌜length vs = length ws⌝ -∗
        Ψ k vs o ws -∗
        match o with
        | None =>
            au_load t (₊i + k) (λ v,
              ▷ Ψ k vs (Some $ inl v) ws
            )
        | Some (inl v) =>
            WP fn #k v {{ w,
              ▷ Ψ k vs (Some $ inr (v, w)) ws
            }}
        | Some (inr (v, w)) =>
            au_store t (₊i + k) w (
              ▷ Ψ (S k) (vs ++ [v]) None (ws ++ [w])
            )
        end
      )
    }}}
      array_unsafe_applyi_slice fn t #i #n
    {{{ vs ws,
      RET ();
      ⌜length vs = ₊n⌝ ∗
      ⌜length vs = length ws⌝ ∗
      Ψ ₊n vs None ws
    }}}.
  Proof.
    iIntros "% % % %Φ (#Hinv & HΨ & #H) HΦ".

    wp_rec credit:"H£".

    pose (Ψ' k vs o := (
      ∃ ws,
      ⌜length vs = length ws⌝ ∗
      Ψ k vs (inl <$> o) ws ∗
      £ 1
    )%I).
    wp_smart_apply (array_unsafe_iteri_slice_spec_atomic Ψ' with "[$Hinv $HΨ $H£]"); [done.. | | iSteps].
    iStep. iIntros "!> %k %vs %o % % (%ws & %Hws & HΨ & H£)".
    destruct o as [v |].
    - wp_smart_apply (wp_wand with "(H [//] [//] [//] HΨ)") as "%w HΨ".
      iMod (lc_fupd_elim_later with "H£ HΨ") as "HΨ".
      iDestruct ("H" with "[//] [//] [//] HΨ") as "H'".
      awp_smart_apply (array_unsafe_set_spec_atomic_cell with "[//]").
      iApply (aacc_aupd_commit with "H'"); first done. iIntros "%v' Hslice".
      rewrite /atomic_acc /=.
      repeat iExists _. iFrameStep 8. iFrame. simpl_length. iSteps.
    - iApply (atomic_update_wand with "(H [//] [//] [//] HΨ)").
      iSteps.
  Qed.
  Lemma array_unsafe_applyi_slice_spec Ψ fn t vs (i n : Z) :
    (0 ≤ i ≤ length vs)%Z →
    (0 ≤ n)%Z →
    (i + n ≤ length vs)%Z →
    {{{
      ▷ Ψ 0 [] [] ∗
      array_model t (DfracOwn 1) vs ∗
      □ (
        ∀ k v ws,
        ⌜k = length ws⌝ -∗
        ⌜k < ₊n⌝ -∗
        ⌜vs !! (₊i + k)%nat = Some v⌝ -∗
        Ψ k (slice ₊i k vs) ws -∗
        WP fn #k v {{ w,
          ▷ Ψ (S k) (slice ₊i k vs ++ [v]) (ws ++ [w])
        }}
      )
    }}}
      array_unsafe_applyi_slice fn t #i #n
    {{{ ws,
      RET ();
      ⌜length ws = ₊n⌝ ∗
      array_model t (DfracOwn 1) (with_slice ₊i ₊n vs ws) ∗
      Ψ ₊n (slice ₊i ₊n vs) ws
    }}}.
  Proof.
    iIntros "% % % %Φ (HΨ & Hmodel & #Hfn) HΦ".
    iDestruct (array_model_to_inv with "Hmodel") as "#Hinv".

    pose (Ψ' k vs_left o ws := (
      ⌜vs_left = slice ₊i k vs⌝ ∗
      array_model t (DfracOwn 1) (with_slice ₊i k vs ws) ∗
      match o with
      | None =>
          Ψ k vs_left ws
      | Some (inl v) =>
          ⌜vs !! (₊i + k)%nat = Some v⌝ ∗
          Ψ k vs_left ws
      | Some (inr (v, w)) =>
          ⌜vs !! (₊i + k)%nat = Some v⌝ ∗
          Ψ (S k) (vs_left ++ [v]) (ws ++ [w])
      end
    )%I).
    wp_apply (array_unsafe_applyi_slice_spec_atomic Ψ' with "[$Hinv Hmodel $HΨ]"); [done.. | |].
    { rewrite with_slice_slice_nil //. iStep.
      iIntros "!> %k %vs_left %o %ws % % % (-> & Hmodel & HΨ)".
      destruct (lookup_lt_is_Some_2 vs (₊i + k)) as (v & Hlookup); first lia.
      destruct o as [[v_ | (v_ & w)] |].
      - iDestruct "HΨ" as "(% & HΨ)". simplify.
        wp_apply (wp_wand with "(Hfn [%] [//] [//] HΨ)"); first lia.
        iSteps.
      - iDestruct "HΨ" as "(% & HΨ)". simplify.
        iDestruct (array_model_update (₊i + k) with "Hmodel") as "(_ & H↦ & Hmodel)".
        { apply with_slice_lookup_right; done || lia. }
        iAuIntro. iAaccIntro with "H↦"; first iSteps. iIntros "H↦ !>". iFrame.
        iSplit. { rewrite slice_snoc //. }
        iDestruct ("Hmodel" with "H↦") as "Hmodel".
        rewrite with_slice_slice_snoc //; lia.
      - iDestruct (array_model_lookup_acc (₊i + k) with "Hmodel") as "(H↦ & Hmodel)".
        { apply with_slice_lookup_right; done || lia. }
        iAuIntro. iAaccIntro with "H↦"; iSteps.
    }
    iIntros "%vs_left %ws (%Hvs_left_1 & %Hws & (-> & Hmodel & HΨ))".
    iApply ("HΦ" $! ws).
    iSteps.
  Qed.
  Lemma array_unsafe_applyi_slice_spec' Ψ fn t vs (i n : Z) :
    (0 ≤ i ≤ length vs)%Z →
    (0 ≤ n)%Z →
    (i + n ≤ length vs)%Z →
    {{{
      ▷ Ψ 0 [] [] ∗
      array_model t (DfracOwn 1) vs ∗
      ( [∗ list] k ↦ v ∈ slice ₊i ₊n vs,
        ∀ ws,
        ⌜k = length ws⌝ -∗
        Ψ k (slice ₊i k vs) ws -∗
        WP fn #k v {{ w,
          ▷ Ψ (S k) (slice ₊i k vs ++ [v]) (ws ++ [w])
        }}
      )
    }}}
      array_unsafe_applyi_slice fn t #i #n
    {{{ ws,
      RET ();
      ⌜length ws = ₊n⌝ ∗
      array_model t (DfracOwn 1) (with_slice ₊i ₊n vs ws) ∗
      Ψ ₊n (slice ₊i ₊n vs) ws
    }}}.
  Proof.
    iIntros "% % % %Φ (HΨ & Hmodel & Hfn) HΦ".

    match goal with |- context [big_opL bi_sep ?Ξ' _] => set Ξ := Ξ' end.
    pose (Ψ' k vs_left ws := (
      Ψ k vs_left ws ∗
      [∗ list] j ↦ v ∈ slice (₊i + k) (₊n - k) vs, Ξ (k + j) v
    )%I).

    wp_apply (array_unsafe_applyi_slice_spec Ψ' with "[$HΨ $Hmodel Hfn]"); [done.. | | iSteps].
    rewrite !right_id. iFrame.
    iIntros "!> %k %v %ws % % % (HΨ & HΞ)".
    rewrite -(slice_cons' (₊i + k) _ v) //; first lia.
    iDestruct "HΞ" as "(Hfn & HΞ)".
    setoid_rewrite Nat.add_succ_r.
    rewrite Nat.add_0_r -Nat.add_succ_r -Nat.sub_add_distr Nat.add_1_r.
    iSteps.
  Qed.
  Lemma array_unsafe_applyi_slice_spec_disentangled Ψ fn t vs (i n : Z) :
    (0 ≤ i ≤ length vs)%Z →
    (0 ≤ n)%Z →
    (i + n ≤ length vs)%Z →
    {{{
      array_model t (DfracOwn 1) vs ∗
      □ (
        ∀ k v,
        ⌜k < ₊n⌝ -∗
        ⌜vs !! (₊i + k)%nat = Some v⌝ -∗
        WP fn #k v {{ w,
          ▷ Ψ k w
        }}
      )
    }}}
      array_unsafe_applyi_slice fn t #i #n
    {{{ ws,
      RET ();
      ⌜length ws = ₊n⌝ ∗
      array_model t (DfracOwn 1) (with_slice ₊i ₊n vs ws) ∗
      ( [∗ list] i ↦ w ∈ ws,
        Ψ i w
      )
    }}}.
  Proof.
    iIntros "% % % %Φ (Hmodel & #Hfn) HΦ".

    pose (Ψ' k vs_left ws := (
      [∗ list] j ↦ w ∈ ws, Ψ j w
    )%I).
    wp_apply (array_unsafe_applyi_slice_spec Ψ' with "[$Hmodel]"); [done.. | | iSteps].
    rewrite /Ψ'. iSteps.
    rewrite big_sepL_snoc. iSteps.
  Qed.
  Lemma array_unsafe_applyi_slice_spec_disentangled' Ψ fn t vs (i n : Z) :
    (0 ≤ i ≤ length vs)%Z →
    (0 ≤ n)%Z →
    (i + n ≤ length vs)%Z →
    {{{
      array_model t (DfracOwn 1) vs ∗
      ( [∗ list] k ↦ v ∈ slice ₊i ₊n vs,
        WP fn #k v {{ w,
          ▷ Ψ k w
        }}
      )
    }}}
      array_unsafe_applyi_slice fn t #i #n
    {{{ ws,
      RET ();
      array_model t (DfracOwn 1) (with_slice ₊i ₊n vs ws) ∗
      ( [∗ list] i ↦ w ∈ ws,
        Ψ i w
      )
    }}}.
  Proof.
    iIntros "% % % %Φ (Hmodel & Hfn) HΦ".

    pose (Ψ' k vs_left ws := (
      [∗ list] j ↦ w ∈ ws, Ψ j w
    )%I).
    wp_apply (array_unsafe_applyi_slice_spec' Ψ' with "[Hmodel Hfn]"); [done.. | | iSteps].
    rewrite /Ψ'. iSteps.
    iApply (big_sepL_impl with "Hfn"). iSteps.
    rewrite big_sepL_snoc. iSteps.
  Qed.

  Lemma array_applyi_slice_spec_atomic Ψ fn t (sz : nat) (i n : Z) :
    {{{
      array_inv t sz ∗
      ▷ Ψ 0 [] None [] ∗
      □ (
        ∀ k vs (o : option (val + val * val)) ws,
        ⌜k < ₊n⌝ -∗
        ⌜k = length vs⌝ -∗
        ⌜length vs = length ws⌝ -∗
        Ψ k vs o ws -∗
        match o with
        | None =>
            au_load t (₊i + k) (λ v,
              ▷ Ψ k vs (Some $ inl v) ws
            )
        | Some (inl v) =>
            WP fn #k v {{ w,
              ▷ Ψ k vs (Some $ inr (v, w)) ws
            }}
        | Some (inr (v, w)) =>
            au_store t (₊i + k) w (
              ▷ Ψ (S k) (vs ++ [v]) None (ws ++ [w])
            )
        end
      )
    }}}
      array_applyi_slice fn t #i #n
    {{{ vs ws,
      RET ();
      ⌜0 ≤ i ≤ sz⌝%Z ∗
      ⌜0 ≤ n⌝%Z ∗
      ⌜i + n ≤ sz⌝%Z ∗
      ⌜length vs = ₊n⌝ ∗
      ⌜length vs = length ws⌝ ∗
      Ψ ₊n vs None ws
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & HΨ & #H) HΦ".

    wp_rec.
    do 2 (wp_smart_apply assume_spec' as "%").
    wp_smart_apply (array_size_spec_inv with "Hinv") as "_".
    do 2 (wp_smart_apply assume_spec' as "%").
    wp_smart_apply (array_unsafe_applyi_slice_spec_atomic Ψ with "[$Hinv $HΨ $H]"); [done.. |].
    iSteps.
  Qed.
  Lemma array_applyi_slice_spec Ψ fn t vs (i n : Z) :
    {{{
      ▷ Ψ 0 [] [] ∗
      array_model t (DfracOwn 1) vs ∗
      □ (
        ∀ k v ws,
        ⌜k = length ws⌝ -∗
        ⌜k < ₊n⌝ -∗
        ⌜vs !! (₊i + k)%nat = Some v⌝ -∗
        Ψ k (slice ₊i k vs) ws -∗
        WP fn #k v {{ w,
          ▷ Ψ (S k) (slice ₊i k vs ++ [v]) (ws ++ [w])
        }}
      )
    }}}
      array_applyi_slice fn t #i #n
    {{{ ws,
      RET ();
      ⌜0 ≤ i ≤ length vs⌝%Z ∗
      ⌜0 ≤ n⌝%Z ∗
      ⌜i + n ≤ length vs⌝%Z ∗
      ⌜length ws = ₊n⌝ ∗
      array_model t (DfracOwn 1) (with_slice ₊i ₊n vs ws) ∗
      Ψ ₊n (slice ₊i ₊n vs) ws
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hmodel & #Hfn) HΦ".

    wp_rec.
    do 2 (wp_smart_apply assume_spec' as "%").
    wp_smart_apply (array_size_spec with "Hmodel") as "Hmodel".
    do 2 (wp_smart_apply assume_spec' as "%").
    wp_smart_apply (array_unsafe_applyi_slice_spec Ψ with "[$HΨ $Hmodel $Hfn]"); [done.. |].
    iSteps.
  Qed.
  Lemma array_applyi_slice_spec' Ψ fn t vs (i n : Z) :
    {{{
      ▷ Ψ 0 [] [] ∗
      array_model t (DfracOwn 1) vs ∗
      ( [∗ list] k ↦ v ∈ slice ₊i ₊n vs,
        ∀ ws,
        ⌜k = length ws⌝ -∗
        Ψ k (slice ₊i k vs) ws -∗
        WP fn #k v {{ w,
          ▷ Ψ (S k) (slice ₊i k vs ++ [v]) (ws ++ [w])
        }}
      )
    }}}
      array_applyi_slice fn t #i #n
    {{{ ws,
      RET ();
      ⌜0 ≤ i ≤ length vs⌝%Z ∗
      ⌜0 ≤ n⌝%Z ∗
      ⌜i + n ≤ length vs⌝%Z ∗
      ⌜length ws = ₊n⌝ ∗
      array_model t (DfracOwn 1) (with_slice ₊i ₊n vs ws) ∗
      Ψ ₊n (slice ₊i ₊n vs) ws
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hmodel & Hfn) HΦ".

    wp_rec.
    do 2 (wp_smart_apply assume_spec' as "%").
    wp_smart_apply (array_size_spec with "Hmodel") as "Hmodel".
    do 2 (wp_smart_apply assume_spec' as "%").
    wp_smart_apply (array_unsafe_applyi_slice_spec' Ψ with "[$HΨ $Hmodel Hfn]"); [done.. |].
    iSteps.
  Qed.
  Lemma array_applyi_slice_spec_disentangled Ψ fn t vs (i n : Z) :
    {{{
      array_model t (DfracOwn 1) vs ∗
      □ (
        ∀ k v,
        ⌜k < ₊n⌝ -∗
        ⌜vs !! (₊i + k)%nat = Some v⌝ -∗
        WP fn #k v {{ w,
          ▷ Ψ k w
        }}
      )
    }}}
      array_applyi_slice fn t #i #n
    {{{ ws,
      RET ();
      ⌜0 ≤ i ≤ length vs⌝%Z ∗
      ⌜0 ≤ n⌝%Z ∗
      ⌜i + n ≤ length vs⌝%Z ∗
      ⌜length ws = ₊n⌝ ∗
      array_model t (DfracOwn 1) (with_slice ₊i ₊n vs ws) ∗
      ( [∗ list] i ↦ w ∈ ws,
        Ψ i w
      )
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & #Hfn) HΦ".

    wp_rec.
    do 2 (wp_smart_apply assume_spec' as "%").
    wp_smart_apply (array_size_spec with "Hmodel") as "Hmodel".
    do 2 (wp_smart_apply assume_spec' as "%").
    wp_smart_apply (array_unsafe_applyi_slice_spec_disentangled Ψ with "[$Hmodel $Hfn]"); [done.. |].
    iSteps.
  Qed.
  Lemma array_applyi_slice_spec_disentangled' Ψ fn t vs (i n : Z) :
    {{{
      array_model t (DfracOwn 1) vs ∗
      ( [∗ list] k ↦ v ∈ slice ₊i ₊n vs,
        WP fn #k v {{ w,
          ▷ Ψ k w
        }}
      )
    }}}
      array_applyi_slice fn t #i #n
    {{{ ws,
      RET ();
      ⌜0 ≤ i ≤ length vs⌝%Z ∗
      ⌜0 ≤ n⌝%Z ∗
      ⌜i + n ≤ length vs⌝%Z ∗
      array_model t (DfracOwn 1) (with_slice ₊i ₊n vs ws) ∗
      ( [∗ list] i ↦ w ∈ ws,
        Ψ i w
      )
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & Hfn) HΦ".

    wp_rec.
    do 2 (wp_smart_apply assume_spec' as "%").
    wp_smart_apply (array_size_spec with "Hmodel") as "Hmodel".
    do 2 (wp_smart_apply assume_spec' as "%").
    wp_smart_apply (array_unsafe_applyi_slice_spec_disentangled' Ψ with "[$Hmodel $Hfn]"); [done.. |].
    iSteps.
  Qed.

  Lemma array_unsafe_apply_slice_spec_atomic Ψ fn t (sz : nat) (i n : Z) :
    (0 ≤ i ≤ sz)%Z →
    (0 ≤ n)%Z →
    (i + n ≤ sz)%Z →
    {{{
      array_inv t sz ∗
      ▷ Ψ 0 [] None [] ∗
      □ (
        ∀ k vs (o : option (val + val * val)) ws,
        ⌜k < ₊n⌝ -∗
        ⌜k = length vs⌝ -∗
        ⌜length vs = length ws⌝ -∗
        Ψ k vs o ws -∗
        match o with
        | None =>
            au_load t (₊i + k) (λ v,
              ▷ Ψ k vs (Some $ inl v) ws
            )
        | Some (inl v) =>
            WP fn v {{ w,
              ▷ Ψ k vs (Some $ inr (v, w)) ws
            }}
        | Some (inr (v, w)) =>
            au_store t (₊i + k) w (
              ▷ Ψ (S k) (vs ++ [v]) None (ws ++ [w])
            )
        end
      )
    }}}
      array_unsafe_apply_slice fn t #i #n
    {{{ vs ws,
      RET ();
      ⌜length vs = ₊n⌝ ∗
      ⌜length vs = length ws⌝ ∗
      Ψ ₊n vs None ws
    }}}.
  Proof.
    iIntros "% % % %Φ (#Hinv & HΨ & #H) HΦ".

    wp_rec.
    wp_smart_apply (array_unsafe_applyi_slice_spec_atomic Ψ with "[$Hinv $HΨ] HΦ") as "!> %k %vs %o %ws % % % HΨ"; [done.. |].
    repeat case_match; try wp_pures; iApply ("H" with "[//] [//] [//] HΨ").
  Qed.
  Lemma array_unsafe_apply_slice_spec Ψ fn t vs (i n : Z) :
    (0 ≤ i ≤ length vs)%Z →
    (0 ≤ n)%Z →
    (i + n ≤ length vs)%Z →
    {{{
      ▷ Ψ 0 [] [] ∗
      array_model t (DfracOwn 1) vs ∗
      □ (
        ∀ k v ws,
        ⌜k = length ws⌝ -∗
        ⌜k < ₊n⌝ -∗
        ⌜vs !! (₊i + k)%nat = Some v⌝ -∗
        Ψ k (slice ₊i k vs) ws -∗
        WP fn v {{ w,
          ▷ Ψ (S k) (slice ₊i k vs ++ [v]) (ws ++ [w])
        }}
      )
    }}}
      array_unsafe_apply_slice fn t #i #n
    {{{ ws,
      RET ();
      ⌜length ws = ₊n⌝ ∗
      array_model t (DfracOwn 1) (with_slice ₊i ₊n vs ws) ∗
      Ψ ₊n (slice ₊i ₊n vs) ws
    }}}.
  Proof.
    iIntros "% % % %Φ (HΨ & Hmodel & #Hfn) HΦ".

    wp_rec.
    wp_smart_apply (array_unsafe_applyi_slice_spec Ψ with "[$HΨ $Hmodel] HΦ"); [done.. |].
    iSteps.
  Qed.
  Lemma array_unsafe_apply_slice_spec' Ψ fn t vs (i n : Z) :
    (0 ≤ i ≤ length vs)%Z →
    (0 ≤ n)%Z →
    (i + n ≤ length vs)%Z →
    {{{
      ▷ Ψ 0 [] [] ∗
      array_model t (DfracOwn 1) vs ∗
      ( [∗ list] k ↦ v ∈ slice ₊i ₊n vs,
        ∀ ws,
        ⌜k = length ws⌝ -∗
        Ψ k (slice ₊i k vs) ws -∗
        WP fn v {{ w,
          ▷ Ψ (S k) (slice ₊i k vs ++ [v]) (ws ++ [w])
        }}
      )
    }}}
      array_unsafe_apply_slice fn t #i #n
    {{{ ws,
      RET ();
      ⌜length ws = ₊n⌝ ∗
      array_model t (DfracOwn 1) (with_slice ₊i ₊n vs ws) ∗
      Ψ ₊n (slice ₊i ₊n vs) ws
    }}}.
  Proof.
    iIntros "% % % %Φ (HΨ & Hmodel & Hfn) HΦ".

    wp_rec.
    wp_smart_apply (array_unsafe_applyi_slice_spec' Ψ with "[$HΨ $Hmodel Hfn] HΦ"); [done.. |].
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.
  Lemma array_unsafe_apply_slice_spec_disentangled Ψ fn t vs (i n : Z) :
    (0 ≤ i ≤ length vs)%Z →
    (0 ≤ n)%Z →
    (i + n ≤ length vs)%Z →
    {{{
      array_model t (DfracOwn 1) vs ∗
      □ (
        ∀ k v,
        ⌜k < ₊n⌝ -∗
        ⌜vs !! (₊i + k)%nat = Some v⌝ -∗
        WP fn v {{ w,
          ▷ Ψ k w
        }}
      )
    }}}
      array_unsafe_apply_slice fn t #i #n
    {{{ ws,
      RET ();
      ⌜length ws = ₊n⌝ ∗
      array_model t (DfracOwn 1) (with_slice ₊i ₊n vs ws) ∗
      ( [∗ list] i ↦ w ∈ ws,
        Ψ i w
      )
    }}}.
  Proof.
    iIntros "% % % %Φ (Hmodel & #Hfn) HΦ".

    wp_rec.
    wp_smart_apply (array_unsafe_applyi_slice_spec_disentangled Ψ with "[$Hmodel] HΦ"); [done.. |].
    iSteps.
  Qed.
  Lemma array_unsafe_apply_slice_spec_disentangled' Ψ fn t vs (i n : Z) :
    (0 ≤ i ≤ length vs)%Z →
    (0 ≤ n)%Z →
    (i + n ≤ length vs)%Z →
    {{{
      array_model t (DfracOwn 1) vs ∗
      ( [∗ list] k ↦ v ∈ slice ₊i ₊n vs,
        WP fn v {{ w,
          ▷ Ψ k w
        }}
      )
    }}}
      array_unsafe_apply_slice fn t #i #n
    {{{ ws,
      RET ();
      array_model t (DfracOwn 1) (with_slice ₊i ₊n vs ws) ∗
      ( [∗ list] i ↦ w ∈ ws,
        Ψ i w
      )
    }}}.
  Proof.
    iIntros "% % % %Φ (Hmodel & Hfn) HΦ".

    wp_rec.
    wp_smart_apply (array_unsafe_applyi_slice_spec_disentangled' Ψ with "[$Hmodel Hfn] HΦ"); [done.. |].
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.

  Lemma array_apply_slice_spec_atomic Ψ fn t (sz : nat) (i n : Z) :
    {{{
      array_inv t sz ∗
      ▷ Ψ 0 [] None [] ∗
      □ (
        ∀ k vs (o : option (val + val * val)) ws,
        ⌜k < ₊n⌝ -∗
        ⌜k = length vs⌝ -∗
        ⌜length vs = length ws⌝ -∗
        Ψ k vs o ws -∗
        match o with
        | None =>
            au_load t (₊i + k) (λ v,
              ▷ Ψ k vs (Some $ inl v) ws
            )
        | Some (inl v) =>
            WP fn v {{ w,
              ▷ Ψ k vs (Some $ inr (v, w)) ws
            }}
        | Some (inr (v, w)) =>
            au_store t (₊i + k) w (
              ▷ Ψ (S k) (vs ++ [v]) None (ws ++ [w])
            )
        end
      )
    }}}
      array_apply_slice fn t #i #n
    {{{ vs ws,
      RET ();
      ⌜0 ≤ i ≤ sz⌝%Z ∗
      ⌜0 ≤ n⌝%Z ∗
      ⌜i + n ≤ sz⌝%Z ∗
      ⌜length vs = ₊n⌝ ∗
      ⌜length vs = length ws⌝ ∗
      Ψ ₊n vs None ws
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & HΨ & #H) HΦ".

    wp_rec.
    do 2 (wp_smart_apply assume_spec' as "%").
    wp_smart_apply (array_size_spec_inv with "Hinv") as "_".
    do 2 (wp_smart_apply assume_spec' as "%").
    wp_smart_apply (array_unsafe_apply_slice_spec_atomic Ψ with "[$Hinv $HΨ $H]"); [done.. |].
    iSteps.
  Qed.
  Lemma array_apply_slice_spec Ψ fn t vs (i n : Z) :
    {{{
      ▷ Ψ 0 [] [] ∗
      array_model t (DfracOwn 1) vs ∗
      □ (
        ∀ k v ws,
        ⌜k = length ws⌝ -∗
        ⌜k < ₊n⌝ -∗
        ⌜vs !! (₊i + k)%nat = Some v⌝ -∗
        Ψ k (slice ₊i k vs) ws -∗
        WP fn v {{ w,
          ▷ Ψ (S k) (slice ₊i k vs ++ [v]) (ws ++ [w])
        }}
      )
    }}}
      array_apply_slice fn t #i #n
    {{{ ws,
      RET ();
      ⌜0 ≤ i ≤ length vs⌝%Z ∗
      ⌜0 ≤ n⌝%Z ∗
      ⌜i + n ≤ length vs⌝%Z ∗
      ⌜length ws = ₊n⌝ ∗
      array_model t (DfracOwn 1) (with_slice ₊i ₊n vs ws) ∗
      Ψ ₊n (slice ₊i ₊n vs) ws
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hmodel & #Hfn) HΦ".

    wp_rec.
    do 2 (wp_smart_apply assume_spec' as "%").
    wp_smart_apply (array_size_spec with "Hmodel") as "Hmodel".
    do 2 (wp_smart_apply assume_spec' as "%").
    wp_smart_apply (array_unsafe_apply_slice_spec Ψ with "[$HΨ $Hmodel $Hfn]"); [done.. |].
    iSteps.
  Qed.
  Lemma array_apply_slice_spec' Ψ fn t vs (i n : Z) :
    {{{
      ▷ Ψ 0 [] [] ∗
      array_model t (DfracOwn 1) vs ∗
      ( [∗ list] k ↦ v ∈ slice ₊i ₊n vs,
        ∀ ws,
        ⌜k = length ws⌝ -∗
        Ψ k (slice ₊i k vs) ws -∗
        WP fn v {{ w,
          ▷ Ψ (S k) (slice ₊i k vs ++ [v]) (ws ++ [w])
        }}
      )
    }}}
      array_apply_slice fn t #i #n
    {{{ ws,
      RET ();
      ⌜0 ≤ i ≤ length vs⌝%Z ∗
      ⌜0 ≤ n⌝%Z ∗
      ⌜i + n ≤ length vs⌝%Z ∗
      ⌜length ws = ₊n⌝ ∗
      array_model t (DfracOwn 1) (with_slice ₊i ₊n vs ws) ∗
      Ψ ₊n (slice ₊i ₊n vs) ws
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hmodel & Hfn) HΦ".

    wp_rec.
    do 2 (wp_smart_apply assume_spec' as "%").
    wp_smart_apply (array_size_spec with "Hmodel") as "Hmodel".
    do 2 (wp_smart_apply assume_spec' as "%").
    wp_smart_apply (array_unsafe_apply_slice_spec' Ψ with "[$HΨ $Hmodel Hfn]"); [done.. |].
    iSteps.
  Qed.
  Lemma array_apply_slice_spec_disentangled Ψ fn t vs (i n : Z) :
    {{{
      array_model t (DfracOwn 1) vs ∗
      □ (
        ∀ k v,
        ⌜k < ₊n⌝ -∗
        ⌜vs !! (₊i + k)%nat = Some v⌝ -∗
        WP fn v {{ w,
          ▷ Ψ k w
        }}
      )
    }}}
      array_apply_slice fn t #i #n
    {{{ ws,
      RET ();
      ⌜0 ≤ i ≤ length vs⌝%Z ∗
      ⌜0 ≤ n⌝%Z ∗
      ⌜i + n ≤ length vs⌝%Z ∗
      ⌜length ws = ₊n⌝ ∗
      array_model t (DfracOwn 1) (with_slice ₊i ₊n vs ws) ∗
      ( [∗ list] i ↦ w ∈ ws,
        Ψ i w
      )
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & #Hfn) HΦ".

    wp_rec.
    do 2 (wp_smart_apply assume_spec' as "%").
    wp_smart_apply (array_size_spec with "Hmodel") as "Hmodel".
    do 2 (wp_smart_apply assume_spec' as "%").
    wp_smart_apply (array_unsafe_apply_slice_spec_disentangled Ψ with "[$Hmodel $Hfn]"); [done.. |].
    iSteps.
  Qed.
  Lemma array_apply_slice_spec_disentangled' Ψ fn t vs (i n : Z) :
    {{{
      array_model t (DfracOwn 1) vs ∗
      ( [∗ list] k ↦ v ∈ slice ₊i ₊n vs,
        WP fn v {{ w,
          ▷ Ψ k w
        }}
      )
    }}}
      array_apply_slice fn t #i #n
    {{{ ws,
      RET ();
      ⌜0 ≤ i ≤ length vs⌝%Z ∗
      ⌜0 ≤ n⌝%Z ∗
      ⌜i + n ≤ length vs⌝%Z ∗
      array_model t (DfracOwn 1) (with_slice ₊i ₊n vs ws) ∗
      ( [∗ list] i ↦ w ∈ ws,
        Ψ i w
      )
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & Hfn) HΦ".

    wp_rec.
    do 2 (wp_smart_apply assume_spec' as "%").
    wp_smart_apply (array_size_spec with "Hmodel") as "Hmodel".
    do 2 (wp_smart_apply assume_spec' as "%").
    wp_smart_apply (array_unsafe_apply_slice_spec_disentangled' Ψ with "[$Hmodel $Hfn]"); [done.. |].
    iSteps.
  Qed.

  Lemma array_applyi_spec_atomic Ψ fn t sz :
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
      array_applyi fn t
    {{{ vs ws,
      RET ();
      ⌜length vs = sz⌝ ∗
      ⌜length vs = length ws⌝ ∗
      Ψ sz vs None ws
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & HΨ & #H) HΦ".

    wp_rec.
    wp_smart_apply (array_size_spec_inv with "Hinv") as "_".
    wp_apply (array_unsafe_applyi_slice_spec_atomic Ψ with "[$Hinv $HΨ]"); [lia.. | iSteps |].
    rewrite Nat2Z.id. iSteps.
  Qed.
  Lemma array_applyi_spec Ψ fn t vs :
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
      array_applyi fn t
    {{{ ws,
      RET ();
      ⌜length vs = length ws⌝ ∗
      array_model t (DfracOwn 1) ws ∗
      Ψ (length vs) vs ws
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hmodel & #H) HΦ".

    wp_rec.
    wp_smart_apply (array_size_spec with "Hmodel") as "Hmodel".
    wp_apply (array_unsafe_applyi_slice_spec Ψ with "[$HΨ $Hmodel]"); [lia.. | iSteps |].
    iStep 3 as (ws) / --silent. iExists ws.
    rewrite Nat2Z.id with_slice_all // slice_0 firstn_all. iSteps.
  Qed.
  Lemma array_applyi_spec' Ψ fn t vs :
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
      array_applyi fn t
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
  Lemma array_applyi_spec_disentangled Ψ fn t vs :
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
      array_applyi fn t
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
  Lemma array_applyi_spec_disentangled' Ψ fn t vs :
    {{{
      array_model t (DfracOwn 1) vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        WP fn #i v {{ w,
          ▷ Ψ i w
        }}
      )
    }}}
      array_applyi fn t
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

  Lemma array_apply_spec_atomic Ψ fn t sz :
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
      array_apply fn t
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
  Lemma array_apply_spec Ψ fn t vs :
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
      array_apply fn t
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
  Lemma array_apply_spec' Ψ fn t vs :
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
      array_apply fn t
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
  Lemma array_apply_spec_disentangled Ψ fn t vs :
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
      array_apply fn t
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
  Lemma array_apply_spec_disentangled' Ψ fn t vs :
    {{{
      array_model t (DfracOwn 1) vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        WP fn v {{ w,
          ▷ Ψ i w
        }}
      )
    }}}
      array_apply fn t
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
    wp_smart_apply (array_applyi_spec_disentangled' Ψ with "[$Hmodel Hfn] HΦ").
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.

  Lemma array_unsafe_initi_spec Ψ sz fn :
    (0 ≤ sz)%Z →
    {{{
      ▷ Ψ 0 [] ∗
      □ (
        ∀ i vs,
        ⌜i < ₊sz⌝ -∗
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
      ⌜length vs = ₊sz⌝ ∗
      array_model t (DfracOwn 1) vs ∗
      Ψ ₊sz vs
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
      erewrite <- (length_replicate ₊sz). eapply lookup_lt_Some. done.
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
      ( [∗ list] i ∈ seq 0 ₊sz,
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
      ⌜length vs = ₊sz⌝ ∗
      array_model t (DfracOwn 1) vs ∗
      Ψ ₊sz vs
    }}}.
  Proof.
    iIntros "%Hsz %Φ (HΨ & Hfn) HΦ".
    match goal with |- context [big_opL bi_sep (λ _, ?Ξ') _] => set Ξ := Ξ' end.
    pose (Ψ' i vs := (
      Ψ i vs ∗
      [∗ list] j ∈ seq i (₊sz - i), Ξ j
    )%I).
    wp_apply (array_unsafe_initi_spec Ψ' with "[$HΨ Hfn]"); [done | | iSteps].
    rewrite Nat.sub_0_r. iFrame. iIntros "!> %i %vs %Hi1 %Hi2 (HΨ & HΞ)".
    destruct (Nat.lt_exists_pred 0 (₊sz - i)) as (k & Hk & _); first lia. rewrite Hk.
    rewrite -cons_seq. iDestruct "HΞ" as "(Hfn & HΞ)".
    wp_apply (wp_wand with "(Hfn [//] HΨ)"). iSteps.
    rewrite Nat.sub_succ_r Hk //.
  Qed.
  Lemma array_unsafe_initi_spec_disentangled Ψ sz fn :
    (0 ≤ sz)%Z →
    {{{
      □ (
        ∀ i,
        ⌜i < ₊sz⌝ -∗
        WP fn #i {{ v, ▷
          Ψ i v
        }}
      )
    }}}
      array_unsafe_initi #sz fn
    {{{ t vs,
      RET t;
      ⌜length vs = ₊sz⌝ ∗
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
      ( [∗ list] i ∈ seq 0 ₊sz,
        WP fn #i {{ v, ▷
          Ψ i v
        }}
      )
    }}}
      array_unsafe_initi #sz fn
    {{{ t vs,
      RET t;
      ⌜length vs = ₊sz⌝ ∗
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
        ⌜i < ₊sz⌝ -∗
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
      ⌜length vs = ₊sz⌝ ∗
      array_model t (DfracOwn 1) vs ∗
      Ψ ₊sz vs
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
      ( [∗ list] i ∈ seq 0 ₊sz,
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
      ⌜length vs = ₊sz⌝ ∗
      array_model t (DfracOwn 1) vs ∗
      Ψ ₊sz vs
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
        ⌜i < ₊sz⌝ -∗
        WP fn #i {{ v, ▷
          Ψ i v
        }}
      )
    }}}
      array_initi #sz fn
    {{{ t vs,
      RET t;
      ⌜0 ≤ sz⌝%Z ∗
      ⌜length vs = ₊sz⌝ ∗
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
      ( [∗ list] i ∈ seq 0 ₊sz,
        WP fn #i {{ v, ▷
          Ψ i v
        }}
      )
    }}}
      array_initi #sz fn
    {{{ t vs,
      RET t;
      ⌜0 ≤ sz⌝%Z ∗
      ⌜length vs = ₊sz⌝ ∗
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
        ⌜i < ₊sz⌝ -∗
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
      ⌜length vs = ₊sz⌝ ∗
      array_model t (DfracOwn 1) vs ∗
      Ψ ₊sz vs
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
      ( [∗ list] i ∈ seq 0 ₊sz,
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
      ⌜length vs = ₊sz⌝ ∗
      array_model t (DfracOwn 1) vs ∗
      Ψ ₊sz vs
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
        ⌜i < ₊sz⌝ -∗
        WP fn () {{ v, ▷
          Ψ i v
        }}
      )
    }}}
      array_unsafe_init #sz fn
    {{{ t vs,
      RET t;
      ⌜length vs = ₊sz⌝ ∗
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
      ( [∗ list] i ∈ seq 0 ₊sz,
        WP fn () {{ v, ▷
          Ψ i v
        }}
      )
    }}}
      array_unsafe_init #sz fn
    {{{ t vs,
      RET t;
      ⌜length vs = ₊sz⌝ ∗
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
        ⌜i < ₊sz⌝ -∗
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
      ⌜length vs = ₊sz⌝ ∗
      array_model t (DfracOwn 1) vs ∗
      Ψ ₊sz vs
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
      ( [∗ list] i ∈ seq 0 ₊sz,
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
      ⌜length vs = ₊sz⌝ ∗
      array_model t (DfracOwn 1) vs ∗
      Ψ ₊sz vs
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
        ⌜i < ₊sz⌝ -∗
        WP fn () {{ v, ▷
          Ψ i v
        }}
      )
    }}}
      array_init #sz fn
    {{{ t vs,
      RET t;
      ⌜0 ≤ sz⌝%Z ∗
      ⌜length vs = ₊sz⌝ ∗
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
      ( [∗ list] i ∈ seq 0 ₊sz,
        WP fn () {{ v, ▷
          Ψ i v
        }}
      )
    }}}
      array_init #sz fn
    {{{ t vs,
      RET t;
      ⌜0 ≤ sz⌝%Z ∗
      ⌜length vs = ₊sz⌝ ∗
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

  Lemma array_mapi_spec_atomic Ψ fn t sz :
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
      array_mapi fn t
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
      iExists (vs ++ [v]). simpl_length. iSteps.
    }
    rewrite Nat2Z.id.
    iApply ("HΦ" with "[$Hmodel $HΨ]").
    iSteps.
  Qed.
  Lemma array_mapi_spec Ψ fn t dq vs :
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
      array_mapi fn t
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
  Lemma array_mapi_spec' Ψ fn t dq vs :
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
      array_mapi fn t
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
  Lemma array_mapi_spec_disentangled Ψ fn t dq vs :
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
      array_mapi fn t
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
  Lemma array_mapi_spec_disentangled' Ψ fn t dq vs :
    {{{
      array_model t dq vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        WP fn #i v {{ w,
          ▷ Ψ i v w
        }}
      )
    }}}
      array_mapi fn t
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

  Lemma array_map_spec_atomic Ψ fn t sz :
    {{{
      array_inv t sz ∗
      ▷ Ψ 0 [] None [] ∗
      □ (
        ∀ i vs (o : option val) ws,
        ⌜i < ₊sz⌝ -∗
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
      array_map fn t
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
  Lemma array_map_spec Ψ fn t dq vs :
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
      array_map fn t
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
  Lemma array_map_spec' Ψ fn t dq vs :
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
      array_map fn t
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
  Lemma array_map_spec_disentangled Ψ fn t dq vs :
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
      array_map fn t
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
  Lemma array_map_spec_disentangled' Ψ fn t dq vs :
    {{{
      array_model t dq vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        WP fn v {{ w,
          ▷ Ψ i v w
        }}
      )
    }}}
      array_map fn t
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
        ⌜k < ₊n⌝ -∗
        ⌜k = length vs⌝ -∗
        Ψ k vs o -∗
        match o with
        | None =>
            au_load t1 (₊i1 + k) (λ v,
              ▷ Ψ k vs (Some v)
            )
        | Some v =>
            au_store t2 (₊i2 + k) v (
              ▷ Ψ (S k) (vs ++ [v]) None
            )
        end
      )
    }}}
      array_unsafe_copy_slice t1 #i1 t2 #i2 #n
    {{{ vs,
      RET ();
      ⌜length vs = ₊n⌝ ∗
      Ψ ₊n vs None
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
      repeat iExists _. iFrameStep 2; first iSteps. iIntros "Hslice !>".
      rewrite Z.add_0_l Z2Nat.inj_add; [lia.. |]. rewrite !Nat2Z.id. iFrame.
      iIntros "HΨ !> _".
      iDestruct ("H" with "[%] [//] HΨ") as "H'"; first lia.
      awp_smart_apply (array_unsafe_set_spec_atomic_cell with "[//]").
      iApply (aacc_aupd_commit with "H'"); first done. iIntros "%w Hslice".
      rewrite /atomic_acc /=.
      repeat iExists _. iFrameSteps.
      iExists (vs ++ [v]). simpl_length. iSteps.
    }
    rewrite Z.sub_0_r. iSteps.
  Qed.
  Lemma array_unsafe_copy_slice_spec_slice_fit t1 (i1 : Z) i1_ dq1 vs1 t2 (i2 : Z) i2_ vs2 (n : Z) :
    i1 = ⁺i1_ →
    i2 = ⁺i2_ →
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
  Lemma array_unsafe_copy_slice_spec_slice_fit_src t1 (i1 : Z) i1_ dq1 vs1 t2 i2 (j2 : Z) vs2 (n : Z) :
    i1 = ⁺i1_ →
    (i2 ≤ j2)%Z →
    n = length vs1 →
    (j2 + n ≤ i2 + length vs2)%Z →
    {{{
      array_slice t1 i1_ dq1 vs1 ∗
      array_slice t2 i2 (DfracOwn 1) vs2
    }}}
      array_unsafe_copy_slice t1 #i1 t2 #j2 #n
    {{{
      RET ();
      array_slice t1 i1_ dq1 vs1 ∗
      array_slice t2 i2 (DfracOwn 1) (with_slice (₊j2 - i2) ₊n vs2 vs1)
    }}}.
  Proof.
    iIntros (-> ? ? ?) "%Φ (Hslice1 & Hslice2) HΦ".
    Z_to_nat j2. rewrite Nat2Z.id.
    rewrite (Nat.le_add_sub i2 j2); first lia. set k2 := j2 - i2.
    rewrite -{1}(take_drop k2 vs2) -(take_drop ₊n (drop k2 vs2)) drop_drop.
    iDestruct (array_slice_app3_2 with "Hslice2") as "(Hslice21 & Hslice22 & Hslice23)"; first done.
    simpl_length. rewrite !Nat.min_l; [lia.. |].
    wp_apply (array_unsafe_copy_slice_spec_slice_fit with "[$Hslice1 $Hslice22]") as "(Hslice1 & Hslice22)"; [simpl_length; lia.. |].
    iApply "HΦ".
    iDestruct (array_slice_app3_1 with "Hslice21 Hslice22 Hslice23") as "Hslice2"; [simpl_length; lia.. |].
    rewrite -Nat.le_add_sub; first lia.
    iSteps.
  Qed.
  Lemma array_unsafe_copy_slice_spec_slice_fit_dst t1 i1 (j1 : Z) dq1 vs1 t2 (i2 : Z) i2_ vs2 (n : Z) :
    (i1 ≤ j1)%Z →
    i2 = ⁺i2_ →
    n = length vs2 →
    (j1 + n ≤ i1 + length vs1)%Z →
    {{{
      array_slice t1 i1 dq1 vs1 ∗
      array_slice t2 i2_ (DfracOwn 1) vs2
    }}}
      array_unsafe_copy_slice t1 #j1 t2 #i2 #n
    {{{
      RET ();
      array_slice t1 i1 dq1 vs1 ∗
      array_slice t2 i2_ (DfracOwn 1) (slice (₊j1 - i1) ₊n vs1)
    }}}.
  Proof.
    iIntros (? -> ? ?) "%Φ (Hslice1 & Hslice2) HΦ".
    Z_to_nat j1. rewrite Nat2Z.id.
    rewrite (Nat.le_add_sub i1 j1); first lia. set k1 := j1 - i1.
    rewrite -{1 2}(take_drop k1 vs1) -(take_drop ₊n (drop k1 vs1)) drop_drop.
    iDestruct (array_slice_app3_2 with "Hslice1") as "(Hslice11 & Hslice12 & Hslice13)"; first done.
    simpl_length. rewrite !Nat.min_l; [lia.. |].
    wp_apply (array_unsafe_copy_slice_spec_slice_fit with "[$Hslice12 $Hslice2]") as "(Hslice12 & Hslice2)"; [simpl_length; lia.. |].
    iApply "HΦ".
    iDestruct (array_slice_app3_1 with "Hslice11 Hslice12 Hslice13") as "$"; [simpl_length; lia.. |].
    rewrite -Nat.le_add_sub //; first lia.
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
      array_slice t2 i2 (DfracOwn 1) (with_slice (₊j2 - i2) ₊n vs2 (take ₊n (drop (₊j1 - i1) vs1)))
    }}}.
  Proof.
    iIntros "% % % % % %Φ (Hslice1 & Hslice2) HΦ".
    Z_to_nat j2. rewrite Nat2Z.id.
    rewrite (Nat.le_add_sub i2 j2); first lia. set k2 := j2 - i2.
    rewrite -{1}(take_drop k2 vs2) -(take_drop ₊n (drop k2 vs2)) drop_drop.
    iDestruct (array_slice_app3_2 with "Hslice2") as "(Hslice21 & Hslice22 & Hslice23)"; first done.
    simpl_length. rewrite !Nat.min_l; [lia.. |].
    wp_apply (array_unsafe_copy_slice_spec_slice_fit_dst with "[$Hslice1 $Hslice22]") as "(Hslice1 & Hslice22)"; [simpl_length; lia.. |].
    iApply "HΦ".
    iDestruct (array_slice_app3_1 with "Hslice21 Hslice22 Hslice23") as "Hslice2"; [simpl_length; lia.. |].
    rewrite -Nat.le_add_sub; first lia.
    iSteps.
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
      array_model t2 (DfracOwn 1) (with_slice ₊i2 ₊n vs2 (take ₊n (drop ₊i1 vs1)))
    }}}.
  Proof.
    iIntros "% % % % % %Φ (Hmodel1 & Hmodel2) HΦ".
    iDestruct (array_model_to_slice' with "Hmodel1") as "(Hslice1 & #?)".
    iDestruct (array_model_to_slice' with "Hmodel2") as "(Hslice2 & #?)".
    wp_apply (array_unsafe_copy_slice_spec_slice with "[$Hslice1 $Hslice2]") as "(Hslice1 & Hslice2)"; [lia.. |].
    rewrite !Nat.sub_0_r. iSteps. iPureIntro.
    simpl_length. lia.
  Qed.

  Lemma array_copy_slice_spec_slice_fit t1 sz1 (i1 : Z) i1_ dq1 vs1 t2 sz2 (i2 : Z) i2_ vs2 (n : Z) :
    i1_ = ₊i1 →
    i2_ = ₊i2 →
    {{{
      array_inv t1 sz1 ∗
      array_inv t2 sz2 ∗
      ( ⌜0 ≤ i1⌝%Z -∗
        ⌜0 ≤ i2⌝%Z -∗
        ⌜0 ≤ n⌝%Z -∗
        ⌜i1 + n ≤ sz1⌝%Z -∗
        ⌜i2 + n ≤ sz2⌝%Z -∗
          ⌜₊n = length vs1⌝ ∗
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
          ⌜i1 ≤ ₊j1⌝ ∗
          ⌜i2 ≤ ₊j2⌝ ∗
          ⌜₊j1 + n ≤ i1 + length vs1⌝%Z ∗
          ⌜₊j2 + n ≤ i2 + length vs2⌝%Z ∗
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
      array_slice t2 i2 (DfracOwn 1) (with_slice (₊j2 - i2) ₊n vs2 (take ₊n (drop (₊j1 - i1) vs1)))
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
      array_model t2 (DfracOwn 1) (with_slice ₊i2 ₊n vs2 (take ₊n (drop ₊i1 vs1)))
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
            au_store t2 (₊i2 + k) v (
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
    i2 = ⁺i2_ →
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
      array_slice t2 i2 (DfracOwn 1) (with_slice (₊j2 - i2) (length vs1) vs2 vs1)
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
      array_model t2 (DfracOwn 1) (with_slice ₊i2 (length vs1) vs2 vs1)
    }}}.
  Proof.
    iIntros "% % %Φ (Hmodel1 & Hmodel2) HΦ".
    wp_rec.
    wp_smart_apply (array_size_spec with "Hmodel1") as "Hmodel1".
    wp_apply (array_unsafe_copy_slice_spec with "[$Hmodel1 $Hmodel2]"); [lia.. |].
    rewrite Nat2Z.id firstn_all /=. iSteps.
  Qed.

  Lemma array_copy_spec_slice_fit t1 dq1 vs1 t2 sz2 (i2 : Z) i2_ vs2 :
    i2_ = ₊i2 →
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
      array_slice t2 i2 (DfracOwn 1) (with_slice (₊j2 - i2) (length vs1) vs2 vs1)
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
      array_model t2 (DfracOwn 1) (with_slice ₊i2 (length vs1) vs2 vs1)
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
      array_model t dq vs ∗
      array_model t' (DfracOwn 1) (vs ++ replicate (₊sz' - length vs) v')
    }}}.
  Proof.
    iIntros "%Hsz' %Φ Hmodel HΦ".
    wp_rec.
    wp_smart_apply (array_size_spec with "Hmodel") as "Hmodel".
    wp_smart_apply (array_unsafe_alloc_spec with "[//]") as "%t' Hmodel'"; first lia.
    iDestruct (array_model_to_slice' with "Hmodel'") as "(Hslice' & #?)".
    assert (₊sz' = length vs + ₊(sz' - length vs)) as -> by lia.
    rewrite replicate_add.
    iDestruct (array_slice_app with "Hslice'") as "(Hslice1' & Hslice2')".
    wp_smart_apply (array_unsafe_copy_spec_slice with "[$Hmodel $Hslice1']") as "(Hmodel & Hslice1')"; first done.
    { simpl_length. }
    wp_smart_apply (array_unsafe_fill_slice_spec_slice_fit with "Hslice2'") as "Hslice2'".
    { simpl_length. }
    { simpl_length. }
    iDestruct (array_slice_app_1' with "Hslice1' Hslice2'") as "Hslice'".
    { simpl_length. lia. }
    iSteps.
    - iPureIntro. simpl_length. lia.
    - rewrite with_slice_all; first simpl_length.
      rewrite Nat.add_sub' //.
  Qed.

  Lemma array_grow_spec t dq vs sz' v' :
    {{{
      array_model t dq vs
    }}}
      array_grow t #sz' v'
    {{{ t',
      RET t';
      ⌜length vs ≤ sz'⌝%Z ∗
      array_model t dq vs ∗
      array_model t' (DfracOwn 1) (vs ++ replicate (₊sz' - length vs) v')
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
    i = ⁺i_ →
    n = length vs →
    {{{
      array_slice t i_ dq vs
    }}}
      array_unsafe_sub t #i #n
    {{{ t',
      RET t';
      array_slice t i_ dq vs ∗
      array_model t' (DfracOwn 1) (take ₊n vs)
    }}}.
  Proof.
    iIntros (-> ->) "%Φ Hslice HΦ".
    wp_rec.
    wp_smart_apply (array_unsafe_alloc_spec with "[//]") as (t') "Hmodel'"; first lia.
    iDestruct (array_model_to_slice' with "Hmodel'") as "(Hslice' & #?)".
    wp_smart_apply (array_unsafe_copy_slice_spec_slice_fit with "[$Hslice $Hslice']"); [done.. | |].
    { simpl_length. lia. }
    iSteps.
    - iPureIntro. simpl_length. lia.
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
      array_model t' (DfracOwn 1) (take ₊n (drop (₊j - ₊i) vs))
    }}}.
  Proof.
    iIntros "% % % %Φ Hslice HΦ".
    Z_to_nat j. Z_to_nat n. rewrite !Nat2Z.id.
    rewrite (Nat.le_add_sub i j); first lia. set k := j - i.
    rewrite -{1 2}(take_drop k vs) -(take_drop n (drop k vs)).
    rewrite !drop_drop.
    iDestruct (array_slice_app3_2 with "Hslice") as "(Hslice1 & Hslice2 & Hslice3)"; first done.
    simpl_length. rewrite !Nat.min_l; [lia.. |].
    wp_apply (array_unsafe_sub_spec_slice_fit with "Hslice2") as "%t' (Hslice2 & Hmodel')"; [simpl_length; lia.. |].
    iApply "HΦ".
    iDestruct (array_slice_app3_1 with "Hslice1 Hslice2 Hslice3") as "$"; [simpl_length; lia.. |].
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
      array_model t' (DfracOwn 1) (take ₊n (drop ₊i vs))
    }}}.
  Proof.
    iIntros "% % % %Φ Hmodel HΦ".
    iDestruct (array_model_to_slice' with "Hmodel") as "(Hslice & #?)".
    wp_apply (array_unsafe_sub_spec_slice with "Hslice"); [done.. |].
    rewrite Nat.sub_0_r. iSteps.
  Qed.

  Lemma array_sub_spec_slice_fit t sz dq vs (i : Z) i_ (n : Z) :
    i_ = ₊i →
    {{{
      array_inv t sz ∗
      ( ⌜0 ≤ i⌝%Z -∗
        ⌜0 ≤ n⌝%Z -∗
        ⌜i + n ≤ sz⌝%Z -∗
          ⌜₊n = length vs⌝ ∗
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
      array_model t' (DfracOwn 1) (take ₊n vs)
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
          ⌜i ≤ ₊j⌝ ∗
          ⌜₊j + ₊n ≤ i + length vs⌝ ∗
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
      array_model t' (DfracOwn 1) (take ₊n (drop (₊j - ₊i) vs))
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
      array_model t' (DfracOwn 1) (take ₊n (drop ₊i vs))
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
      array_model t' (DfracOwn 1) (take ₊n vs)
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
      array_model t' (DfracOwn 1) (take ₊n vs)
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

  Lemma array_unsafe_cget_spec_atomic t (j : Z) :
    <<<
      True
    | ∀∀ sz i dq vs v,
      ⌜(i ≤ j)%Z⌝ ∗
      ⌜vs !! (₊j - i) = Some v⌝ ∗
      array_cslice t sz i dq vs
    >>>
      array_unsafe_cget t #j
    <<<
      array_cslice t sz i dq vs
    | RET v;
      £ 1
    >>>.
  Proof.
    iIntros "%Φ _ HΦ".

    wp_rec.

    awp_smart_apply (array_size_spec_atomic_cslice with "[//]").
    iApply (aacc_aupd_abort with "HΦ"); first done. iIntros "%sz %i %dq %vs %v (% & % & Hcslice)".
    iAaccIntro with "Hcslice"; first iSteps. iIntros "$ !>". iStep. iIntros "HΦ !> (H£ & #Hinv) {%}".

    wp_pures. wp_rec. wp_pures.

    iMod "HΦ" as "(%sz_ & %i & %dq & %vs & %v & (% & % & Hcslice) & _ & HΦ)".
    iDestruct (array_inv_cslice_agree with "Hinv Hcslice") as %<-.
    rewrite /array_cslice.
    iDestruct "Hcslice" as "(%l & -> & #Hheader & Hcslice)".
    iDestruct (chunk_cslice_lookup_acc' j with "Hcslice") as "(H↦ & Hcslice)"; [done.. |].
    rewrite Z_rem_mod; [lia.. |].
    wp_load.
    iApply ("HΦ" with "[H↦ Hcslice] H£").
    iSteps.
  Qed.
  Lemma array_unsafe_cget_spec_atomic_weak t (i : Z) :
    (0 ≤ i)%Z →
    <<<
      True
    | ∀∀ sz j dq vs,
      array_cslice t sz j dq vs ∗
      ⌜0 < sz⌝ ∗
      ⌜length vs = sz⌝
    >>>
      array_unsafe_cget t #i
    <<<
      array_cslice t sz j dq vs
    | v,
      RET v;
      £ 1
    >>>.
  Proof.
    iIntros "%Hi %Φ _ HΦ".

    awp_apply (array_unsafe_cget_spec_atomic with "[//]").
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%sz %j %dq %vs (Hcslice & %Hsz & %Hvs)".
    iDestruct (array_cslice_rebase with "Hcslice") as "(%ws & %n & %Hws & Hcslice)"; [done.. |].
    rewrite /atomic_acc /=.
    destruct (lookup_lt_is_Some_2 ws 0) as (v & Hlookup).
    { rewrite Hws. simpl_length. lia. }
    iExists sz, ₊i, dq, ws, v. iSteps. rewrite Nat.sub_diag //.
  Qed.
  Lemma array_unsafe_cget_spec_atomic_cell t sz (i : Z) :
    <<<
      True
    | ∀∀ i_ dq v,
      ⌜i = ⁺i_⌝ ∗
      array_cslice t sz i_ dq [v]
    >>>
      array_unsafe_cget t #i
    <<<
      array_cslice t sz i_ dq [v]
    | RET v;
      £ 1
    >>>.
  Proof.
    iIntros "%Φ _ HΦ".

    awp_apply (array_unsafe_cget_spec_atomic with "[//]").
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%i_ %dq %v (-> & Hcslice)".
    rewrite /atomic_acc /= Nat2Z.id.
    iExists sz, i_, dq, [v], v. rewrite Nat.sub_diag. iSteps.
  Qed.
  Lemma array_unsafe_cget_spec k v t sz i dq vs (j : Z) :
    (i ≤ j)%Z →
    vs !! k = Some v →
    k = ₊j - i →
    {{{
      array_cslice t sz i dq vs
    }}}
      array_unsafe_cget t #j
    {{{
      RET v;
      array_cslice t sz i dq vs
    }}}.
  Proof.
    iIntros (Hj Hlookup ->) "%Φ Hcslice HΦ".

    iApply wp_fupd.
    awp_apply (array_unsafe_cget_spec_atomic with "[//]") without "HΦ".
    rewrite /atomic_acc /=.
    iExists sz, i, dq, vs, v.
    iApply fupd_mask_intro; first done. iIntros "Hclose".
    iSplitL "Hcslice"; first auto. iSplit; first iSteps.
    iIntros "Hcslice". iMod "Hclose" as "_". iIntros "!> H£ HΦ".
    iMod (lc_fupd_elim_later with "H£ HΦ") as "HΦ".
    iSteps.
  Qed.
  Lemma array_unsafe_cget_spec_cell t sz (i : Z) i_ dq v :
    i = ⁺i_ →
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
    awp_apply (array_unsafe_cget_spec_atomic_cell with "[//]") without "HΦ".
    rewrite /atomic_acc /=.
    repeat iExists _.
    iApply fupd_mask_intro; first done. iIntros "Hclose".
    iSplitL "Hcslice"; first auto. iSplit; first iSteps. iIntros "Hcslice".
    iMod "Hclose" as "_". iIntros "!> H£ HΦ".
    iMod (lc_fupd_elim_later with "H£ HΦ") as "HΦ".
    iApply ("HΦ" with "Hcslice").
  Qed.
  Lemma array_unsafe_cget_spec_model v t dq vs (j : Z) :
    (0 ≤ j)%Z →
    vs !! (₊j `mod` length vs) = Some v →
    {{{
      array_model t dq vs
    }}}
      array_unsafe_cget t #j
    {{{
      RET v;
      array_model t dq vs
    }}}.
  Proof.
    iIntros "% %Hlookup %Φ Hmodel HΦ".

    iDestruct (array_model_to_inv with "Hmodel") as "#Hinv".
    iDestruct (array_model_lookup_acc with "Hmodel") as "(Hslice & Hmodel)"; first done.
    iDestruct (array_slice_to_cslice_cell with "Hinv Hslice") as "Hcslice".
    wp_apply (array_unsafe_cget_spec_cell with "Hcslice") as "Hcslice"; first lia.
    iDestruct (array_cslice_to_slice_cell' with "Hcslice") as "Hslice".
    iSteps.
  Qed.

  Lemma array_cget_spec_atomic t sz (j : Z) :
    <<<
      array_inv t sz
    | ∀∀ dq vs i v,
      ⌜0 ≤ j⌝%Z -∗
      ⌜0 < sz⌝%Z -∗
        ⌜i ≤ ₊j⌝ ∗
        ⌜vs !! (₊j - i) = Some v⌝ ∗
        array_cslice t sz i dq vs
    >>>
      array_cget t #j
    <<<
      array_cslice t sz i dq vs
    | RET v;
      ⌜0 ≤ j⌝%Z ∗
      ⌜0 < sz⌝%Z ∗
      £ 1
    >>>.
  Proof.
    iIntros "%Φ #Hinv HΦ".

    wp_rec.
    wp_smart_apply assume_spec' as "%".
    wp_smart_apply (array_size_spec_inv with "Hinv") as "_".
    wp_smart_apply assume_spec' as "%".

    awp_smart_apply (array_unsafe_cget_spec_atomic with "[//]").
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%dq %vs %i %v H".
    iDestruct ("H" with "[//] [//]") as "(% & %Hlookup & Hcslice)".
    rewrite /atomic_acc /=.
    repeat iExists _. iFrame. iSplitL; first iSteps. iSplitL; last iSteps. iIntros "!> (_ & _ & Hslice)". iSplitL; iSteps.
  Qed.
  Lemma array_cget_spec_atomic_weak t sz (i : Z) :
    <<<
      array_inv t sz
    | ∀∀ j dq vs,
      array_cslice t sz j dq vs ∗
      ⌜length vs = sz⌝
    >>>
      array_cget t #i
    <<<
      array_cslice t sz j dq vs
    | v,
      RET v;
      £ 1
    >>>.
  Proof.
    iIntros "%Φ #Hinv HΦ".

    wp_rec.
    wp_smart_apply assume_spec' as "%".
    wp_smart_apply (array_size_spec_inv with "Hinv") as "_".
    wp_smart_apply assume_spec' as "%".

    awp_smart_apply (array_unsafe_cget_spec_atomic_weak with "[//]"); [lia.. |].
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%j %dq %vs (Hcslice & %)".
    rewrite /atomic_acc /=.
    iSteps.
  Qed.
  Lemma array_cget_spec_atomic_cell t sz (i : Z) i_ :
    i_ = ₊i →
    <<<
      array_inv t sz
    | ∀∀ dq v,
      ⌜0 ≤ i⌝%Z -∗
      ⌜0 < sz⌝%Z -∗
      array_cslice t sz i_ dq [v]
    >>>
      array_cget t #i
    <<<
      array_cslice t sz i_ dq [v]
    | RET v;
      ⌜0 ≤ i⌝%Z ∗
      ⌜0 < sz⌝%Z ∗
      £ 1
    >>>.
  Proof.
    iIntros (->) "%Φ #Hinv HΦ".

    awp_apply (array_cget_spec_atomic with "Hinv").
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%dq %v H".
    rewrite /atomic_acc /=.
    iExists dq, [v], ₊i, v. rewrite Nat.sub_diag. iSplitL; first iSteps. iSplitR; last iSteps. iIntros "!> H". iSplitL; iSteps.
  Qed.
  Lemma array_cget_spec k v t sz i dq vs (j : Z) :
    {{{
      array_inv t sz ∗
      ( ⌜0 < sz⌝ -∗
        ⌜0 ≤ j⌝%Z -∗
          ⌜i ≤ ₊j⌝ ∗
          ⌜vs !! k = Some v⌝ ∗
          ⌜k = ₊j - i⌝ ∗
          array_cslice t sz i dq vs
      )
    }}}
      array_cget t #j
    {{{
      RET v;
      ⌜0 < sz⌝ ∗
      ⌜0 ≤ j⌝%Z ∗
      array_cslice t sz i dq vs
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & H) HΦ".

    wp_rec.
    wp_smart_apply assume_spec' as "%".
    wp_smart_apply (array_size_spec_inv with "Hinv") as "_".
    wp_smart_apply assume_spec' as "%".
    iDestruct ("H" with "[%] [//]") as "(% & %Hlookupk & -> & Hcslice)"; first lia.
    wp_smart_apply (array_unsafe_cget_spec with "Hcslice"); [lia | done.. |].
    iSteps.
  Qed.
  Lemma array_cget_spec_cell t sz (i : Z) i_ dq v :
    i_ = ₊i →
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

    wp_apply (array_cget_spec 0 _ _ _ ₊i _ [_] with "[$Hinv H]"); iSteps.
  Qed.
  Lemma array_cget_spec_model v t dq vs (j : Z) :
    vs !! (₊j `mod` length vs) = Some v →
    {{{
      array_model t dq vs
    }}}
      array_cget t #j
    {{{
      RET v;
      array_model t dq vs
    }}}.
  Proof.
    iIntros "%Hlookup %Φ Hmodel HΦ".

    wp_rec.
    wp_smart_apply assume_spec' as "%".
    wp_smart_apply (array_size_spec with "Hmodel") as "Hmodel".
    wp_smart_apply assume_spec' as "_".
    wp_smart_apply (array_unsafe_cget_spec_model with "Hmodel HΦ"); done.
  Qed.

  Lemma array_unsafe_cset_spec_atomic t (j : Z) v :
    <<<
      True
    | ∀∀ sz i vs,
      ⌜i ≤ j < i + length vs⌝%Z ∗
      array_cslice t sz i (DfracOwn 1) vs
    >>>
      array_unsafe_cset t #j v
    <<<
      array_cslice t sz i (DfracOwn 1) (<[₊j - i := v]> vs)
    | RET ();
      £ 1
    >>>.
  Proof.
    iIntros "%Φ _ HΦ".

    wp_rec.

    awp_smart_apply (array_size_spec_atomic_cslice with "[//]").
    iApply (aacc_aupd_abort with "HΦ"); first done. iIntros "%sz %i %vs (% & Hcslice)".
    iAaccIntro with "Hcslice"; first iSteps. iIntros "$ !>". iStep. iIntros "HΦ !> (H£ & #Hinv) {%}".

    wp_pures. wp_rec. wp_pures.

    iMod "HΦ" as "(%sz_ & %i & %vs & (% & Hcslice) & _ & HΦ)".
    iDestruct (array_inv_cslice_agree with "Hinv Hcslice") as %<-.
    rewrite /array_cslice.
    iDestruct "Hcslice" as "(%l & -> & #Hheader & Hcslice)".
    iDestruct (chunk_cslice_update' j with "Hcslice") as "(H↦ & Hcslice)"; [lia | | done |].
    { destruct (nth_lookup_or_length vs (₊j - i) inhabitant); [done | lia]. }
    rewrite Z_rem_mod; [lia.. |].
    wp_store.
    iApply ("HΦ" with "[H↦ Hcslice] H£").
    iSteps.
  Qed.
  Lemma array_unsafe_cset_spec_atomic_cell t sz (i : Z) v :
    <<<
      True
    | ∀∀ i_ w,
      ⌜i = ⁺i_⌝ ∗
      array_cslice t sz i_ (DfracOwn 1) [w]
    >>>
      array_unsafe_cset t #i v
    <<<
      array_cslice t sz i_ (DfracOwn 1) [v]
    | RET ();
      £ 1
    >>>.
  Proof.
    iIntros "%Φ _ HΦ".

    awp_apply (array_unsafe_cset_spec_atomic with "[//]").
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%i_ %w (-> & Hcslice)".
    rewrite /atomic_acc /= Nat2Z.id.
    iExists sz, i_, [w]. rewrite Nat.sub_diag. iSteps.
  Qed.
  Lemma array_unsafe_cset_spec t sz i vs (j : Z) v :
    (i ≤ j < i + length vs)%Z →
    {{{
      array_cslice t sz i (DfracOwn 1) vs
    }}}
      array_unsafe_cset t #j v
    {{{
      RET ();
      array_cslice t sz i (DfracOwn 1) (<[₊j - i := v]> vs)
    }}}.
  Proof.
    iIntros "%Hj %Φ Hcslice HΦ".

    iApply wp_fupd.
    awp_apply (array_unsafe_cset_spec_atomic with "[//]") without "HΦ".
    rewrite /atomic_acc /=.
    iExists sz, i, vs.
    iApply fupd_mask_intro; first done. iIntros "Hclose".
    iSplitL "Hcslice"; first auto. iSplit; first iSteps.
    iIntros "Hcslice". iMod "Hclose" as "_". iIntros "!> H£ HΦ".
    iMod (lc_fupd_elim_later with "H£ HΦ") as "HΦ".
    iSteps.
  Qed.
  Lemma array_unsafe_cset_spec_cell t sz (i : Z) i_ w v :
    i = ⁺i_ →
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
    awp_apply (array_unsafe_cset_spec_atomic_cell with "[//]") without "HΦ".
    rewrite /atomic_acc /=.
    repeat iExists _.
    iApply fupd_mask_intro; first done. iIntros "Hclose".
    iSplitL "Hcslice"; first auto. iSplit; first iSteps. iIntros "Hcslice".
    iMod "Hclose" as "_". iIntros "!> H£ HΦ".
    iMod (lc_fupd_elim_later with "H£ HΦ") as "HΦ".
    iApply ("HΦ" with "Hcslice").
  Qed.
  Lemma array_unsafe_cset_spec_model t vs (j : Z) v :
    0 < length vs →
    (0 ≤ j)%Z →
    {{{
      array_model t (DfracOwn 1) vs
    }}}
      array_unsafe_cset t #j v
    {{{
      RET ();
      array_model t (DfracOwn 1) (<[₊j `mod` length vs := v]> vs)
    }}}.
  Proof.
    iIntros "% % %Φ Hmodel HΦ".

    destruct (lookup_lt_is_Some_2 vs (₊j `mod` length vs)) as (w & Hlookup); first lia.
    iDestruct (array_model_update with "Hmodel") as "(#Hinv & Hslice & Hmodel)"; first done.
    iDestruct (array_slice_to_cslice_cell with "Hinv Hslice") as "Hcslice".
    wp_apply (array_unsafe_cset_spec_cell with "Hcslice") as "Hcslice"; first lia.
    iDestruct (array_cslice_to_slice_cell' with "Hcslice") as "Hslice".
    iSteps.
  Qed.

  Lemma array_cset_spec_atomic t sz (j : Z) v :
    <<<
      array_inv t sz
    | ∀∀ vs i,
      ⌜0 < sz⌝ -∗
      ⌜0 ≤ j⌝%Z -∗
        ⌜i ≤ ₊j < i + length vs⌝ ∗
        array_cslice t sz i (DfracOwn 1) vs
    >>>
      array_cset t #j v
    <<<
      array_cslice t sz i (DfracOwn 1) (<[₊j - i := v]> vs)
    | RET ();
      ⌜0 < sz⌝ ∗
      ⌜0 ≤ j⌝%Z ∗
      £ 1
    >>>.
  Proof.
    iIntros "%Φ #Hinv HΦ".

    wp_rec.
    wp_smart_apply assume_spec' as "%".
    wp_smart_apply (array_size_spec_inv with "Hinv") as "_".
    wp_smart_apply assume_spec' as "%".

    awp_smart_apply (array_unsafe_cset_spec_atomic with "[//]").
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs %i H".
    iDestruct ("H" with "[%] [//]") as "(% & Hcslice)"; first lia.
    rewrite /atomic_acc /=.
    repeat iExists _. iFrame. iSplitL; first iSteps. iSplitL; last iSteps. iIntros "!> (_ & Hcslice)". iSplitL; iSteps.
  Qed.
  Lemma array_cset_spec_atomic_cell t sz (i : Z) i_ v :
    i_ = ₊i →
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
      ⌜0 < sz⌝ ∗
      ⌜0 ≤ i⌝%Z ∗
      £ 1
    >>>.
  Proof.
    iIntros (->) "%Φ #Hinv HΦ".

    awp_apply (array_cset_spec_atomic with "Hinv").
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%w Hcslice".
    rewrite /atomic_acc /=.
    iExists [w], ₊i. rewrite Nat.sub_diag. iSplitL; first iSteps. iSplitR; last iSteps. iIntros "!> H". iSplitL; iSteps.
  Qed.
  Lemma array_cset_spec t sz i vs (j : Z) v :
    {{{
      array_inv t sz ∗
      ( ⌜0 < sz⌝ -∗
        ⌜0 ≤ j⌝%Z -∗
          ⌜i ≤ ₊j < i + length vs⌝ ∗
          array_cslice t sz i (DfracOwn 1) vs
      )
    }}}
      array_cset t #j v
    {{{
      RET ();
      ⌜0 < sz⌝ ∗
      ⌜0 ≤ j⌝%Z ∗
      array_cslice t sz i (DfracOwn 1) (<[₊j - i := v]> vs)
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & H) HΦ".

    wp_rec.
    wp_smart_apply assume_spec' as "%".
    wp_smart_apply (array_size_spec_inv with "Hinv") as "_".
    wp_smart_apply assume_spec' as "%".
    iDestruct ("H" with "[%] [//]") as "(% & Hcslice)"; first lia.
    wp_smart_apply (array_unsafe_cset_spec with "Hcslice"); first lia.
    iSteps.
  Qed.
  Lemma array_cset_spec_cell t sz (i : Z) i_ w v :
    i_ = ₊i →
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

    wp_apply (array_cset_spec _ _ ₊i [_] with "[$Hinv H]"); first iSteps.
    rewrite Nat.sub_diag //.
  Qed.
  Lemma array_cset_spec_model t vs (j : Z) v :
    {{{
      array_model t (DfracOwn 1) vs
    }}}
      array_cset t #j v
    {{{
      RET ();
      array_model t (DfracOwn 1) (<[₊j `mod` length vs := v]> vs)
    }}}.
  Proof.
    iIntros "%Φ Hmodel HΦ".

    wp_rec.
    wp_smart_apply assume_spec' as "%".
    wp_smart_apply (array_size_spec with "Hmodel") as "Hmodel".
    wp_smart_apply assume_spec' as "%".
    wp_smart_apply (array_unsafe_cset_spec_model with "Hmodel HΦ"); lia.
  Qed.

  #[local] Lemma array_unsafe_ccopy_slice_0_spec t1 (i1 : Z) i1_ dq1 vs1 t2 sz2 (i2 : Z) i2_ vs2 (n : Z) :
    0 < sz2 →
    i1 = ⁺i1_ →
    i2 = ⁺i2_ →
    n = length vs1 →
    length vs1 = length vs2 →
    {{{
      array_slice t1 i1_ dq1 vs1 ∗
      array_cslice t2 sz2 i2_ (DfracOwn 1) vs2
    }}}
      array_unsafe_ccopy_slice_0 t1 #i1 t2 #i2 #n
    {{{
      RET ();
      array_slice t1 i1_ dq1 vs1 ∗
      array_cslice t2 sz2 i2_ (DfracOwn 1) vs1
    }}}.
  Proof.
    iIntros (Hsz2 -> -> ? ?) "%Φ (Hslice1 & Hcslice2) HΦ".
    iDestruct (array_cslice_length with "Hcslice2") as %Hvs2; first done.

    wp_rec.
    wp_smart_apply (array_size_spec_cslice with "Hcslice2") as "Hcslice2".
    wp_pures.
    rewrite Z.rem_mod_nonneg; [lia.. |].
    rewrite !array_cslice_to_slice; [simpl_length; lia.. |].
    iDestruct "Hcslice2" as "(#Hinv2 & Hslice21 & Hslice22)".
    case_bool_decide as Hif; wp_pures.

    - wp_apply (array_unsafe_copy_slice_spec_slice_fit with "[$Hslice1 $Hslice21]") as "(Hslice1 & Hslice21)"; [simpl_length; lia.. |].
      rewrite firstn_all2; first lia.
      rewrite skipn_all2; first lia.
      iSteps.
      iApply (array_slice_nil with "Hslice22").

    - wp_apply (array_unsafe_copy_slice_spec_slice_fit_dst with "[$Hslice1 $Hslice21]") as "(Hslice1 & Hslice21)"; [simpl_length; lia.. |].
      iEval (rewrite Nat2Z.id Nat.sub_diag slice_0 -Nat2Z.inj_mod -Nat2Z.inj_sub; first lia) in "Hslice21".
      iEval (rewrite Nat2Z.id) in "Hslice21".
      wp_smart_apply (array_unsafe_copy_slice_spec_slice_fit_dst with "[$Hslice1 $Hslice22]") as "(Hslice1 & Hslice22)"; [simpl_length; lia.. |].
      iEval (rewrite -Nat2Z.inj_mod -Nat2Z.inj_sub; first lia) in "Hslice22".
      iEval (rewrite -Nat2Z.inj_add Nat2Z.id Nat.add_sub') in "Hslice22".
      iEval (rewrite /slice firstn_all2; first (simpl_length; lia)) in "Hslice22".
      iSteps.
  Qed.
  Lemma array_unsafe_ccopy_slice_spec_fit t1 sz1 (i1 : Z) i1_ dq1 vs1 t2 sz2 (i2 : Z) i2_ vs2 (n : Z) :
    0 < sz1 →
    length vs1 ≤ sz1 →
    0 < sz2 →
    i1 = ⁺i1_ →
    i2 = ⁺i2_ →
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
    iIntros (Hsz1 Hvs1 Hsz2 -> -> -> ?) "%Φ (Hcslice1 & Hcslice2) HΦ".

    wp_rec.
    wp_smart_apply (array_size_spec_cslice with "Hcslice1") as "Hcslice1".
    wp_pures.
    rewrite Z.rem_mod_nonneg; [lia.. |].
    rewrite (array_cslice_to_slice t1) //.
    iDestruct "Hcslice1" as "(#Hinv2 & Hslice11 & Hslice12)".
    case_bool_decide as Hif; wp_pures.

    - wp_apply (array_unsafe_ccopy_slice_0_spec with "[$Hslice11 $Hcslice2]") as "(Hslice11 & Hcslice2)"; [simpl_length; lia.. |].
      rewrite firstn_all2; first lia.
      iSteps.

    - rewrite -(take_drop (sz1 - i1_ `mod` sz1) vs2).
      iDestruct (array_cslice_app_2 with "Hcslice2") as "(Hcslice21 & Hcslice22)"; first done.
      wp_apply (array_unsafe_ccopy_slice_0_spec with "[$Hslice11 $Hcslice21]") as "(Hslice11 & Hcslice21)"; [simpl_length; lia.. |].
      wp_smart_apply (array_unsafe_ccopy_slice_0_spec with "[$Hslice12 $Hcslice22]") as "(Hslice12 & Hcslice22)"; [simpl_length; lia.. |].
      iDestruct (array_cslice_app_1 with "Hcslice21 Hcslice22") as "Hcslice2".
      { simpl_length. lia. }
      iEval (rewrite take_drop) in "Hcslice2".
      iSteps.
  Qed.
  Lemma array_unsafe_ccopy_slice_spec_fit_src t1 sz1 (i1 : Z) i1_ dq1 vs1 t2 sz2 i2 (j2 : Z) vs2 (n : Z) :
    0 < sz1 →
    length vs1 ≤ sz1 →
    0 < sz2 →
    i1 = ⁺i1_ →
    (i2 ≤ j2)%Z →
    n = length vs1 →
    (j2 + n ≤ i2 + length vs2)%Z →
    {{{
      array_cslice t1 sz1 i1_ dq1 vs1 ∗
      array_cslice t2 sz2 i2 (DfracOwn 1) vs2
    }}}
      array_unsafe_ccopy_slice t1 #i1 t2 #j2 #n
    {{{
      RET ();
      array_cslice t1 sz1 i1_ dq1 vs1 ∗
      array_cslice t2 sz2 i2 (DfracOwn 1) (with_slice (₊j2 - i2) ₊n vs2 vs1)
    }}}.
  Proof.
    iIntros (Hsz1 Hvs1 Hsz2 -> ? ? ?) "%Φ (Hcslice1 & Hcslice2) HΦ".
    Z_to_nat j2. rewrite Nat2Z.id.
    rewrite (Nat.le_add_sub i2 j2); first lia. set k2 := j2 - i2.
    rewrite -{1}(take_drop k2 vs2) -(take_drop ₊n (drop k2 vs2)) drop_drop.
    iDestruct (array_cslice_app3_2 with "Hcslice2") as "(Hcslice21 & Hcslice22 & Hcslice23)"; first done.
    simpl_length. rewrite !Nat.min_l; [lia.. |].
    wp_apply (array_unsafe_ccopy_slice_spec_fit with "[$Hcslice1 $Hcslice22]") as "(Hcslice1 & Hcslice22)"; [simpl_length; lia.. |].
    iApply "HΦ".
    iDestruct (array_cslice_app3_1 with "Hcslice21 Hcslice22 Hcslice23") as "Hcslice2"; [simpl_length; lia.. |].
    rewrite -Nat.le_add_sub; first lia.
    iSteps.
  Qed.
  Lemma array_unsafe_ccopy_slice_spec_fit_dst t1 sz1 i1 (j1 : Z) dq1 vs1 t2 sz2 (i2 : Z) i2_ vs2 (n : Z) :
    0 < sz1 →
    length vs1 ≤ sz1 →
    0 < sz2 →
    (i1 ≤ j1)%Z →
    i2 = ⁺i2_ →
    n = length vs2 →
    (j1 + n ≤ i1 + length vs1)%Z →
    {{{
      array_cslice t1 sz1 i1 dq1 vs1 ∗
      array_cslice t2 sz2 i2_ (DfracOwn 1) vs2
    }}}
      array_unsafe_ccopy_slice t1 #j1 t2 #i2 #n
    {{{
      RET ();
      array_cslice t1 sz1 i1 dq1 vs1 ∗
      array_cslice t2 sz2 i2_ (DfracOwn 1) (slice (₊j1 - i1) ₊n vs1)
    }}}.
  Proof.
    iIntros (Hsz1 Hvs1 Hsz2 ? -> ? ?) "%Φ (Hcslice1 & Hcslice2) HΦ".
    Z_to_nat j1. rewrite Nat2Z.id.
    rewrite (Nat.le_add_sub i1 j1); first lia. set k1 := j1 - i1.
    rewrite -{1 2}(take_drop k1 vs1) -(take_drop ₊n (drop k1 vs1)) drop_drop.
    iDestruct (array_cslice_app3_2 with "Hcslice1") as "(Hcslice11 & Hcslice12 & Hcslice13)"; first done.
    simpl_length. rewrite !Nat.min_l; [lia.. |].
    wp_apply (array_unsafe_ccopy_slice_spec_fit with "[$Hcslice12 $Hcslice2]") as "(Hcslice12 & Hcslice2)"; [simpl_length; lia.. |].
    iApply "HΦ".
    iDestruct (array_cslice_app3_1 with "Hcslice11 Hcslice12 Hcslice13") as "$"; [simpl_length; lia.. |].
    rewrite -Nat.le_add_sub //; first lia.
  Qed.
  Lemma array_unsafe_ccopy_slice_spec t1 sz1 i1 (j1 : Z) dq1 vs1 t2 sz2 i2 (j2 : Z) vs2 (n : Z) :
    0 < sz1 →
    length vs1 ≤ sz1 →
    0 < sz2 →
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
      array_cslice t2 sz2 i2 (DfracOwn 1) (with_slice (₊j2 - i2) ₊n vs2 (take ₊n (drop (₊j1 - i1) vs1)))
    }}}.
  Proof.
    iIntros "%Hsz1 %Hvs1 %Hsz2 % % %Hn % % %Φ (Hcslice1 & Hcslice2) HΦ".
    Z_to_nat j2. rewrite Nat2Z.id.
    rewrite (Nat.le_add_sub i2 j2); first lia. set k2 := j2 - i2.
    rewrite -{1}(take_drop k2 vs2) -(take_drop ₊n (drop k2 vs2)) drop_drop.
    iDestruct (array_cslice_app3_2 with "Hcslice2") as "(Hcslice21 & Hcslice22 & Hcslice23)"; first done.
    simpl_length. rewrite !Nat.min_l; [lia.. |].
    wp_apply (array_unsafe_ccopy_slice_spec_fit_dst with "[$Hcslice1 $Hcslice22]") as "(Hcslice1 & Hcslice22)"; [simpl_length; lia.. |].
    iApply "HΦ".
    iDestruct (array_cslice_app3_1 with "Hcslice21 Hcslice22 Hcslice23") as "Hcslice2"; [simpl_length; lia.. |].
    rewrite -Nat.le_add_sub; first lia.
    iSteps.
  Qed.

  Lemma array_ccopy_slice_spec_fit t1 sz1 (i1 : Z) i1_ dq1 vs1 t2 sz2 (i2 : Z) i2_ vs2 (n : Z) :
    i1_ = ₊i1 →
    i2_ = ₊i2 →
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
          ⌜₊n = length vs1⌝ ∗
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
          ⌜length vs1 ≤ sz1⌝ ∗
          ⌜i1 ≤ ₊j1⌝ ∗
          ⌜i2 ≤ ₊j2⌝ ∗
          ⌜₊j1 + n ≤ i1 + length vs1⌝%Z ∗
          ⌜₊j2 + n ≤ i2 + length vs2⌝%Z ∗
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
      array_cslice t2 sz2 i2 (DfracOwn 1) (with_slice (₊j2 - i2) ₊n vs2 (take ₊n (drop (₊j1 - i1) vs1)))
    }}}.
  Proof.
    iIntros "%Φ (#Hinv1 & #Hinv2 & H) HΦ".
    wp_rec.
    do 3 wp_smart_apply assume_spec' as "%".
    wp_smart_apply (array_size_spec_inv with "Hinv1") as "_".
    wp_smart_apply (array_size_spec_inv with "Hinv2") as "_".
    do 4 (wp_smart_apply assume_spec' as "%").
    iDestruct ("H" with "[%] [%] [//] [//] [//] [//] [//]") as "(% & % & % & % & % & Hslice1 & Hslice2)"; [lia.. |].
    wp_smart_apply (array_unsafe_ccopy_slice_spec with "[$Hslice1 $Hslice2]"); [lia.. |].
    iSteps.
  Qed.

  Lemma array_unsafe_ccopy_spec_fit t1 sz1 (i1 : Z) i1_ dq1 vs1 t2 sz2 (i2 : Z) i2_ vs2 :
    0 < sz1 →
    0 < sz2 →
    i1 = ⁺i1_ →
    i2 = ⁺i2_ →
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
    iIntros (Hsz1 Hsz2 -> -> ? ?) "%Φ (Hcslice1 & Hcslice2) HΦ".
    wp_rec.
    wp_smart_apply (array_size_spec_cslice with "Hcslice1") as "Hcslice1".
    wp_apply (array_unsafe_ccopy_slice_spec_fit with "[$Hcslice1 $Hcslice2]"); [lia.. |].
    iSteps.
  Qed.
  Lemma array_unsafe_ccopy_spec t1 sz1 (i1 : Z) i1_ dq1 vs1 t2 sz2 i2 (j2 : Z) vs2 :
    0 < sz1 →
    0 < sz2 →
    i1 = ⁺i1_ →
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
      array_cslice t2 sz2 i2 (DfracOwn 1) (with_slice (₊j2 - i2) (length vs1) vs2 vs1)
    }}}.
  Proof.
    iIntros (Hsz1 Hsz2 -> Hvs1 ? ?) "%Φ (Hcslice1 & Hcslice2) HΦ".
    wp_rec.
    wp_smart_apply (array_size_spec_cslice with "Hcslice1") as "Hcslice1".
    wp_apply (array_unsafe_ccopy_slice_spec with "[$Hcslice1 $Hcslice2]"); [lia.. |].
    rewrite !Nat2Z.id Nat.sub_diag -Hvs1 firstn_all //.
  Qed.

  Lemma array_ccopy_spec_fit t1 sz1 (i1 : Z) i1_ dq1 vs1 t2 sz2 (i2 : Z) i2_ vs2 :
    i1_ = ₊i1 →
    i2_ = ₊i2 →
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
          ⌜i2 ≤ ₊j2⌝%Z ∗
          ⌜₊j2 + length vs1 ≤ i2 + length vs2⌝%Z ∗
          array_cslice t1 sz1 ₊i1 dq1 vs1 ∗
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
      array_cslice t1 sz1 ₊i1 dq1 vs1 ∗
      array_cslice t2 sz2 i2 (DfracOwn 1) (with_slice (₊j2 - i2) (length vs1) vs2 vs1)
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

  Lemma array_unsafe_cgrow_slice_spec t sz (i : Z) i_ dq vs (n : Z) sz' v :
    0 < sz →
    length vs ≤ sz →
    i = ⁺i_ →
    n = ⁺(length vs) →
    (0 < sz')%Z →
    (n ≤ sz')%Z →
    {{{
      array_cslice t sz i_ dq vs
    }}}
      array_unsafe_cgrow_slice t #i #n #sz' v
    {{{ t',
      RET t';
      array_cslice t sz i_ dq vs ∗
      array_cslice t' ₊sz' i_ (DfracOwn 1) (vs ++ replicate (₊sz' - ₊n) v)
    }}}.
  Proof.
    iIntros (Hsz Hvs -> -> Hsz' ?) "%Φ Hcslice HΦ".

    wp_rec.
    wp_smart_apply (array_unsafe_make_spec with "[//]") as (t') "Hmodel'"; first lia.
    iDestruct (array_model_to_cslice with "Hmodel'") as "Hcslice'". simpl_length.
    iDestruct (array_cslice_rotation_right_0 i_ with "Hcslice'") as "Hcslice'"; [lia | simpl_length |].
    rewrite rotation_replicate.
    wp_smart_apply (array_unsafe_ccopy_slice_spec with "[$Hcslice $Hcslice']") as "(Hcslice & Hcslice')"; [simpl_length; lia.. |].
    rewrite !Nat2Z.id Nat.sub_diag firstn_all with_slice_0 drop_replicate.
    iSteps.
  Qed.

  Lemma array_unsafe_cgrow_spec t (sz : nat) (i : Z) i_ dq vs sz' v :
    0 < sz →
    i = ⁺i_ →
    length vs = sz →
    (0 < sz')%Z →
    (sz ≤ sz')%Z →
    {{{
      array_cslice t sz i_ dq vs
    }}}
      array_unsafe_cgrow t #i #sz' v
    {{{ t',
      RET t';
      array_cslice t sz i_ dq vs ∗
      array_cslice t' ₊sz' i_ (DfracOwn 1) (vs ++ replicate (₊sz' - sz) v)
    }}}.
  Proof.
    iIntros (Hsz -> Hvs Hsz' ?) "%Φ Hcslice HΦ".

    wp_rec.
    wp_smart_apply (array_size_spec_cslice with "Hcslice") as "Hcslice".
    wp_apply (array_unsafe_cgrow_slice_spec with "Hcslice") as (t') "(Hcslice & Hcslice')"; [lia.. |].
    rewrite Nat2Z.id. iSteps.
  Qed.

  Lemma array_unsafe_cshrink_slice_spec_fit t sz (i : Z) i_ dq vs sz' :
    0 < sz →
    length vs ≤ sz →
    i = ⁺i_ →
    (0 < sz' ≤ length vs)%Z →
    {{{
      array_cslice t sz i_ dq vs
    }}}
      array_unsafe_cshrink_slice t #i #sz'
    {{{ t',
      RET t';
      array_cslice t sz i_ dq vs ∗
      array_cslice t' ₊sz' i_ (DfracOwn 1) (take ₊sz' vs)
    }}}.
  Proof.
    iIntros (Hsz Hvs -> ?) "%Φ Hcslice HΦ".

    wp_rec.
    wp_smart_apply (array_unsafe_alloc_spec with "[//]") as (t') "Hmodel'"; first lia.
    iDestruct (array_model_to_cslice with "Hmodel'") as "Hcslice'". simpl_length.
    iDestruct (array_cslice_rotation_right_0 i_ with "Hcslice'") as "Hcslice'"; [lia | simpl_length |].
    rewrite rotation_replicate.
    wp_smart_apply (array_unsafe_ccopy_slice_spec with "[$Hcslice $Hcslice']") as "(Hcslice & Hcslice')"; [simpl_length; lia.. |].
    rewrite Nat2Z.id Nat.sub_diag with_slice_0 drop_replicate Nat.sub_diag right_id.
    iSteps.
  Qed.
  Lemma array_unsafe_cshrink_slice_spec t sz i dq vs (j : Z) sz' :
    0 < sz →
    length vs ≤ sz →
    (i ≤ j)%Z →
    (0 < sz')%Z →
    (j + sz' ≤ i + length vs)%Z →
    {{{
      array_cslice t sz i dq vs
    }}}
      array_unsafe_cshrink_slice t #j #sz'
    {{{ t',
      RET t';
      array_cslice t sz i dq vs ∗
      array_cslice t' ₊sz' ₊j (DfracOwn 1) (slice (₊j - i) ₊sz' vs)
    }}}.
  Proof.
    iIntros "%Hsz %Hvs % %Hsz' % %Φ Hcslice HΦ".

    rewrite (Nat.le_add_sub i ₊j); first lia. set k := ₊j - i.
    rewrite -{1 2}(take_drop k vs) -(take_drop ₊sz' (drop k vs)).
    rewrite !drop_drop.
    iDestruct (array_cslice_app3_2 with "Hcslice") as "(Hcslice1 & Hcslice2 & Hcslice3)"; first done.
    simpl_length. rewrite !Nat.min_l; [lia.. |].
    wp_apply (array_unsafe_cshrink_slice_spec_fit with "Hcslice2") as (t') "(Hcslice2 & Hcslice')"; [simpl_length; lia.. |].
    iApply "HΦ".
    iDestruct (array_cslice_app3_1 with "Hcslice1 Hcslice2 Hcslice3") as "$"; [simpl_length; lia.. |].
    rewrite take_idemp -!Nat.le_add_sub //; first lia.
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

  Lemma itype_array_intro τ `{!iType _ τ} t vs :
    array_model t (DfracOwn 1) vs -∗
    ([∗ list] v ∈ vs, τ v) ={⊤}=∗
    itype_array τ (length vs) t.
  Proof.
    rewrite /array_model.
    iSteps.
  Qed.
  Lemma itype_array_intro_slice τ `{!iType _ τ} t sz vs :
    length vs = sz →
    array_inv t sz -∗
    array_slice t 0 (DfracOwn 1) vs -∗
    ([∗ list] v ∈ vs, τ v) ={⊤}=∗
    itype_array τ sz t.
  Proof.
    iIntros "%Hvs #Hinv Hslice".
    iDestruct (array_slice_to_model with "Hinv Hslice") as "Hmodel"; first done.
    rewrite -Hvs.
    iApply (itype_array_intro with "Hmodel").
  Qed.
  Lemma itype_array_intro_cslice τ `{!iType _ τ} t sz i vs :
    0 < sz →
    length vs = sz →
    array_cslice t sz i (DfracOwn 1) vs -∗
    ([∗ list] v ∈ vs, τ v) ={⊤}=∗
    itype_array τ sz t.
  Proof.
    iIntros "% %Hvs Hcslice #Hvs".
    iDestruct (array_cslice_to_model with "Hcslice") as "Hmodel"; [done.. |].
    iMod (itype_array_intro τ with "Hmodel []") as "Htype".
    { rewrite big_sepL_app comm -big_sepL_app take_drop //. }
    rewrite length_rotation Hvs //.
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
    iDestruct "Hmodel" as "(%l & -> & #Hheader & Hmodel)".
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
    iIntros "%Hi %Φ (%l & -> & #Hheader & #Htype) HΦ".
    wp_rec. wp_pures.
    Z_to_nat i.
    iInv "Htype" as "(%vs & >%Hvs & Hmodel & #Hvs)".
    destruct (lookup_lt_is_Some_2 vs i) as (w & Hlookup); first lia.
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
    iIntros "%Hi %Φ ((%l & -> & #Hheader & Htype) & #Hv) HΦ".
    wp_rec. wp_pures.
    Z_to_nat i.
    iInv "Htype" as "(%vs & >%Hvs & Hmodel & Hvs)".
    destruct (lookup_lt_is_Some_2 vs i) as (w & Hlookup); first lia.
    iDestruct (chunk_model_update i with "Hmodel") as "(H↦ & Hmodel)"; [lia | done | lia |].
    wp_store.
    iDestruct (big_sepL_insert_acc with "Hvs") as "(_ & Hvs)"; first done.
    iSplitR "HΦ"; last iSteps.
    iExists (<[i := v]> vs). simpl_length. iSteps.
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

  Lemma array_unsafe_xchg_type τ `{!iType _ τ} t (sz : nat) (i : Z) v :
    (0 ≤ i < sz)%Z →
    {{{
      itype_array τ sz t ∗
      τ v
    }}}
      array_unsafe_xchg t #i v
    {{{ w,
      RET w;
      τ w
    }}}.
  Proof.
    iIntros "%Hi %Φ ((%l & -> & #Hheader & Htype) & #Hv) HΦ".
    wp_rec. wp_pures.
    Z_to_nat i.
    iInv "Htype" as "(%vs & >%Hvs & Hmodel & Hvs)".
    destruct (lookup_lt_is_Some_2 vs i) as (w & Hlookup); first lia.
    iDestruct (chunk_model_update i with "Hmodel") as "(H↦ & Hmodel)"; [lia | done | lia |].
    wp_xchg.
    iDestruct (big_sepL_insert_acc with "Hvs") as "(#Hw & Hvs)"; first done.
    iSplitR "HΦ"; last iSteps.
    iExists (<[i := v]> vs). simpl_length. iSteps.
  Qed.

  Lemma array_unsafe_cas_type τ `{!iType _ τ} t (sz : nat) (i : Z) v1 v2 :
    (0 ≤ i < sz)%Z →
    {{{
      itype_array τ sz t ∗
      τ v1 ∗
      τ v2
    }}}
      array_unsafe_cas t #i v1 v2
    {{{ b,
      RET #b;
      True
    }}}.
  Proof.
    iIntros "%Hi %Φ ((%l & -> & #Hheader & Htype) & #Hv1 & #Hv2) HΦ".
    wp_rec. wp_pures.
    Z_to_nat i.
    iInv "Htype" as "(%vs & >%Hvs & Hmodel & Hvs)".
    destruct (lookup_lt_is_Some_2 vs i) as (v & Hlookup); first lia.
    iDestruct (chunk_model_update i with "Hmodel") as "(H↦ & Hmodel)"; [lia | done | lia |].
    wp_apply (wp_cas_nobranch' with "H↦") as (b) "_ H↦ !>".
    iDestruct (big_sepL_insert_acc with "Hvs") as "(#Hv & Hvs)"; first done.
    iSplitR "HΦ"; last iSteps.
    iExists (<[i := if b then v2 else v]> vs). simpl_length. destruct b; iSteps.
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
      itype_array τ ₊sz t
    }}}.
  Proof.
    iIntros "% %Φ #Hv HΦ".
    wp_rec.
    wp_smart_apply (array_unsafe_alloc_spec with "[//]") as (t) "Hmodel"; first done.
    wp_smart_apply (array_fill_spec with "[Hmodel]") as "Hmodel"; first iSteps.
    iStep 5.
    iMod (itype_array_intro with "Hmodel []") as "#Htype"; simpl_length.
    iApply big_sepL_intro. iIntros "%k %_v" ((-> & Hk)%lookup_replicate) "//".
  Qed.

  Lemma array_make_type τ `{!iType _ τ} sz v :
    {{{
      τ v
    }}}
      array_make #sz v
    {{{ t,
      RET t;
      ⌜0 ≤ sz⌝%Z ∗
      itype_array τ ₊sz t
    }}}.
  Proof.
    iIntros "%Φ #Hv HΦ".
    wp_rec.
    wp_smart_apply assume_spec' as "%".
    wp_smart_apply (array_unsafe_make_type with "[//]"); first done.
    iSteps.
  Qed.

  Lemma array_foldli_type τ `{!iType _ τ} υ `{!iType _ υ} fn acc t sz :
    {{{
      itype_array τ sz t ∗
      υ acc ∗
      (itype_nat_upto sz --> υ --> τ --> υ)%T fn
    }}}
      array_foldli fn acc t
    {{{ acc',
      RET acc';
      υ acc'
    }}}.
  Proof.
    iIntros "%Φ (Htype & Hacc & #Hfn) HΦ".
    iDestruct (itype_array_to_inv with "Htype") as "#Hinv".
    iDestruct "Htype" as "(%l & -> & #Hheader & #Htype)".
    pose (Ψ i vs o acc := (
      from_option τ True o ∗
      υ acc
    )%I).
    wp_apply (array_foldli_spec_atomic Ψ with "[$Hinv $Hacc]"); last iSteps.
    clear acc. iIntros "!> %i %vs_left %o %acc %Hi1 %Hi2 (Ho & Hacc)".
    destruct o as [v |].
    - wp_apply (wp_wand with "(Hfn [])"); first iSteps. iClear (fn) "Hfn". iIntros "%fn Hfn".
      wp_apply (wp_wand with "(Hfn Hacc)"). clear fn. iIntros "%fn Hfn".
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

  Lemma array_foldl_type τ `{!iType _ τ} υ `{!iType _ υ} fn acc t sz :
    {{{
      itype_array τ sz t ∗
      υ acc ∗
      (υ --> τ --> υ)%T fn
    }}}
      array_foldl fn acc t
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

  Lemma array_foldri_type τ `{!iType _ τ} υ `{!iType _ υ} fn acc t sz :
    {{{
      itype_array τ sz t ∗
      (itype_nat_upto sz --> τ --> υ --> υ)%T fn ∗
      υ acc
    }}}
      array_foldri fn t acc
    {{{ acc',
      RET acc';
      υ acc'
    }}}.
  Proof.
    iIntros "%Φ (#Htype & #Hfn & Hacc) HΦ".
    iDestruct (itype_array_to_inv with "Htype") as "#Hinv".
    iDestruct "Htype" as "(%l & -> & #Hheader & #Htype)".
    pose (Ψ i acc o vs := (
      from_option τ True o ∗
      υ acc
    )%I).
    wp_apply (array_foldri_spec_atomic Ψ with "[$Hinv $Hacc]"); last iSteps.
    clear acc. iIntros "!> %i %acc %o %vs_right %Hi (Ho & Hacc)".
    destruct o as [v |].
    - wp_apply (wp_wand with "(Hfn [])"); first iSteps. iClear (fn) "Hfn". iIntros "%fn Hfn".
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

  Lemma array_foldr_type τ `{!iType _ τ} υ `{!iType _ υ} fn t sz acc :
    {{{
      itype_array τ sz t ∗
      (τ --> υ --> υ)%T fn ∗
      υ acc
    }}}
      array_foldr fn t acc
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

  Lemma array_unsafe_iteri_slice_type τ `{!iType _ τ} fn t (sz : nat) (i n : Z) :
    (0 ≤ i ≤ sz)%Z →
    (0 ≤ n)%Z →
    (i + n ≤ sz)%Z →
    {{{
      itype_array τ sz t ∗
      (itype_nat_upto ₊n --> τ --> itype_unit)%T fn
    }}}
      array_unsafe_iteri_slice fn t #i #n
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "% % % %Φ (#Htype & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (for_type with "[] HΦ"). iIntros "!> % (%k & -> & %Hk)".
    wp_smart_apply (array_unsafe_get_type with "Htype"); first lia.
    iSteps.
  Qed.

  Lemma array_iteri_slice_type τ `{!iType _ τ} fn t (sz : nat) (i n : Z) :
    {{{
      itype_array τ sz t ∗
      (itype_nat_upto ₊n --> τ --> itype_unit)%T fn
    }}}
      array_iteri_slice fn t #i #n
    {{{
      RET ();
      ⌜0 ≤ i ≤ sz⌝%Z ∗
      ⌜0 ≤ n⌝%Z ∗
      ⌜i + n ≤ sz⌝%Z
    }}}.
  Proof.
    iIntros "%Φ (#Htype & #Hfn) HΦ".
    wp_rec.
    do 2 (wp_smart_apply assume_spec' as "%").
    wp_smart_apply (array_size_type with "Htype") as "_".
    do 2 (wp_smart_apply assume_spec' as "%").
    wp_smart_apply (array_unsafe_iteri_slice_type with "[$Htype $Hfn]"); [done.. |].
    iSteps.
  Qed.

  Lemma array_unsafe_iter_slice_type τ `{!iType _ τ} fn t (sz : nat) (i n : Z) :
    (0 ≤ i ≤ sz)%Z →
    (0 ≤ n)%Z →
    (i + n ≤ sz)%Z →
    {{{
      itype_array τ sz t ∗
      (τ --> itype_unit)%T fn
    }}}
      array_unsafe_iter_slice fn t #i #n
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "% % % %Φ (#Htype & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (array_unsafe_iteri_slice_type with "[$Htype] HΦ"); [done.. |].
    iSteps.
  Qed.

  Lemma array_iter_slice_type τ `{!iType _ τ} fn t (sz : nat) (i n : Z) :
    {{{
      itype_array τ sz t ∗
      (τ --> itype_unit)%T fn
    }}}
      array_iter_slice fn t #i #n
    {{{
      RET ();
      ⌜0 ≤ i ≤ sz⌝%Z ∗
      ⌜0 ≤ n⌝%Z ∗
      ⌜i + n ≤ sz⌝%Z
    }}}.
  Proof.
    iIntros "%Φ (#Htype & #Hfn) HΦ".
    wp_rec.
    do 2 (wp_smart_apply assume_spec' as "%").
    wp_smart_apply (array_size_type with "Htype") as "_".
    do 2 (wp_smart_apply assume_spec' as "%").
    wp_smart_apply (array_unsafe_iter_slice_type with "[$Htype $Hfn]"); [done.. |].
    iSteps.
  Qed.

  Lemma array_iteri_type τ `{!iType _ τ} fn t sz :
    {{{
      itype_array τ sz t ∗
      (itype_nat_upto sz --> τ --> itype_unit)%T fn
    }}}
      array_iteri fn t
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ (#Htype & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (array_size_type with "Htype") as "_".
    wp_smart_apply (array_unsafe_iteri_slice_type with "[$Htype Hfn] HΦ"); [lia.. | iSteps].
  Qed.

  Lemma array_iter_type τ `{!iType _ τ} fn t sz :
    {{{
      itype_array τ sz t ∗
      (τ --> itype_unit)%T fn
    }}}
      array_iter fn t
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

  Lemma array_unsafe_applyi_slice_type τ `{!iType _ τ} fn t (sz : nat) (i n : Z) :
    (0 ≤ i ≤ sz)%Z →
    (0 ≤ n)%Z →
    (i + n ≤ sz)%Z →
    {{{
      itype_array τ sz t ∗
      (itype_nat_upto ₊n --> τ --> τ)%T fn
    }}}
      array_unsafe_applyi_slice fn t #i #n
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "% % % %Φ (#Htype & #Hfn) HΦ".

    wp_rec.
    wp_smart_apply (array_unsafe_iteri_slice_type τ with "[$Htype] HΦ"); [done.. |].
    iIntros "!> % (%k & -> & %Hk)". wp_pures. iIntros "!> !> %v Hv".
    wp_smart_apply (wp_wand with "(Hfn [])"); first iSteps. iClear "Hfn". clear fn. iIntros "%fn Hfn".
    wp_apply (wp_wand with "(Hfn Hv)") as "%w Hw".
    wp_smart_apply (array_unsafe_set_type with "[$Htype $Hw]"); first lia.
    iSteps.
  Qed.

  Lemma array_applyi_slice_type τ `{!iType _ τ} fn t (sz : nat) (i n : Z) :
    {{{
      itype_array τ sz t ∗
      (itype_nat_upto ₊n --> τ --> τ)%T fn
    }}}
      array_applyi_slice fn t #i #n
    {{{
      RET ();
      ⌜0 ≤ i ≤ sz⌝%Z ∗
      ⌜0 ≤ n⌝%Z ∗
      ⌜i + n ≤ sz⌝%Z
    }}}.
  Proof.
    iIntros "%Φ (#Htype & #Hfn) HΦ".

    wp_rec.
    do 2 (wp_smart_apply assume_spec' as "%").
    wp_smart_apply (array_size_type with "Htype") as "_".
    do 2 (wp_smart_apply assume_spec' as "%").
    wp_smart_apply (array_unsafe_applyi_slice_type with "[$Htype $Hfn]"); [done.. |].
    iSteps.
  Qed.

  Lemma array_unsafe_apply_slice_type τ `{!iType _ τ} fn t (sz : nat) (i n : Z) :
    (0 ≤ i ≤ sz)%Z →
    (0 ≤ n)%Z →
    (i + n ≤ sz)%Z →
    {{{
      itype_array τ sz t ∗
      (τ --> τ)%T fn
    }}}
      array_unsafe_apply_slice fn t #i #n
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "% % % %Φ (#Htype & #Hfn) HΦ".

    wp_rec.
    wp_smart_apply (array_unsafe_applyi_slice_type τ with "[$Htype] HΦ"); [done.. |].
    iSteps.
  Qed.

  Lemma array_apply_slice_type τ `{!iType _ τ} fn t (sz : nat) (i n : Z) :
    {{{
      itype_array τ sz t ∗
      (τ --> τ)%T fn
    }}}
      array_apply_slice fn t #i #n
    {{{
      RET ();
      ⌜0 ≤ i ≤ sz⌝%Z ∗
      ⌜0 ≤ n⌝%Z ∗
      ⌜i + n ≤ sz⌝%Z
    }}}.
  Proof.
    iIntros "%Φ (#Htype & #Hfn) HΦ".

    wp_rec.
    do 2 (wp_smart_apply assume_spec' as "%").
    wp_smart_apply (array_size_type with "Htype") as "_".
    do 2 (wp_smart_apply assume_spec' as "%").
    wp_smart_apply (array_unsafe_apply_slice_type with "[$Htype $Hfn]"); [done.. |].
    iSteps.
  Qed.

  Lemma array_applyi_type τ `{!iType _ τ} fn t sz :
    {{{
      itype_array τ sz t ∗
      (itype_nat_upto sz --> τ --> τ)%T fn
    }}}
      array_applyi fn t
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ (#Htype & #Hfn) HΦ".

    wp_rec.
    wp_smart_apply (array_size_type with "Htype") as "_".
    wp_apply (array_unsafe_applyi_slice_type τ with "[$Htype] HΦ"); [lia.. | iSteps].
  Qed.

  Lemma array_apply_type τ `{!iType _ τ} fn t sz :
    {{{
      itype_array τ sz t ∗
      (τ --> τ)%T fn
    }}}
      array_apply fn t
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
    sz = ⁺sz_ →
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
      apply lookup_lt_Some in Hlookup. simpl_length in Hlookup. iSteps.
    }
    rewrite /array_model.
    iDestruct "Hmodel" as "(%l & -> & #Hheader & Hmodel)".
    rewrite length_replicate Nat2Z.id in Hvs. rewrite -Hvs. iSteps.
  Qed.

  Lemma array_initi_type τ `{!iType _ τ} sz fn :
    {{{
      (itype_nat_upto ₊sz --> τ)%T fn
    }}}
      array_initi #sz fn
    {{{ t,
      RET t;
      ⌜0 ≤ sz⌝%Z ∗
      itype_array τ ₊sz t
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
      itype_array τ ₊sz t
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
      itype_array τ ₊sz t
    }}}.
  Proof.
    iIntros "%Φ #Hfn HΦ".
    wp_rec.
    wp_smart_apply assume_spec' as "%".
    wp_smart_apply (array_unsafe_init_type with "Hfn"); first done.
    iSteps.
  Qed.

  Lemma array_mapi_type τ `{!iType _ τ} υ `{!iType _ υ} fn t sz sz_ :
    sz_ = ⁺sz →
    {{{
      itype_array τ sz t ∗
      (itype_nat_upto sz --> τ --> υ)%T fn
    }}}
      array_mapi fn t
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

  Lemma array_map_type τ `{!iType _ τ} υ `{!iType _ υ} fn t sz sz_ :
    sz_ = ⁺sz →
    {{{
      itype_array τ sz t ∗
      (τ --> υ)%T fn
    }}}
      array_map fn t
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
    i2 = ⁺i2_ →
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
      - iExists []. iSteps.
      - iIntros "!> % %k -> %Hk (%ws & %Hws & Hslice2 & Hws)".
        wp_smart_apply (array_unsafe_get_type with "Htype1") as (v) "Hv"; first lia.
        wp_smart_apply (array_unsafe_set_spec_slice with "Hslice2") as "Hslice2".
        { simpl_length. lia. }
        iStep 2. iExists (ws ++ [v]). iSplit; last iSplitL "Hslice2".
        + simpl_length. iSteps.
        + assert (₊(i2_ + (0 + k)) - i2_ = k) as -> by lia.
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
    wp_apply (array_unsafe_copy_slice_type τ t1 with "[$]"); [lia.. |].
    iSteps.
  Qed.
  Lemma array_unsafe_copy_type' τ `{!iType _ τ} t1 sz t2 (i2 : Z) i2_ vs :
    i2 = ⁺i2_ →
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
      itype_array τ ₊sz' t'
    }}}.
  Proof.
    iIntros "% %Φ (#Htype & #Hv') HΦ".
    wp_rec.
    wp_smart_apply (array_size_type with "Htype") as "_".
    wp_smart_apply (array_unsafe_alloc_spec with "[//]") as (t') "Hmodel'"; first lia.
    iDestruct (array_model_to_slice with "Hmodel'") as "(Hinv' & Hslice')".
    replace ₊sz' with (sz + (₊sz' - sz)) at 2 by lia.
    rewrite replicate_add.
    iDestruct (array_slice_app with "Hslice'") as "(Hslice1' & Hslice2')".
    wp_smart_apply (array_unsafe_copy_type' with "[$Htype $Hslice1']") as (vs) "(%Hvs & Hslice1' & #Hvs)"; first done.
    { simpl_length. }
    wp_smart_apply (array_unsafe_fill_slice_spec_slice_fit with "Hslice2'") as "Hslice2'".
    { simpl_length. }
    { simpl_length. lia. }
    iDestruct (array_slice_app_1' with "Hslice1' Hslice2'") as "Hslice'"; first done.
    iStep 5. simpl_length.
    iApply (itype_array_intro_slice with "Hinv' Hslice'").
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
      itype_array τ ₊sz' t'
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
      itype_array τ ₊n t'
    }}}.
  Proof.
    iIntros "% % % %Φ #Htype HΦ".
    wp_rec.
    wp_smart_apply (array_unsafe_alloc_spec with "[//]") as (t') "Hmodel'"; first done.
    iDestruct (array_model_to_slice with "Hmodel'") as "(#Hinv' & Hslice')".
    wp_smart_apply (array_unsafe_copy_slice_type' with "[$Htype $Hslice']") as (vs) "(%Hvs & Hslice' & Hvs)"; try done.
    { simpl_length. lia. }
    iStep 5. simpl_length.
    iApply (itype_array_intro_slice with "Hinv' Hslice' Hvs").
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
      itype_array τ ₊n t'
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
      itype_array τ ₊n t'
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
      itype_array τ ₊n t'
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

  #[local] Lemma array_unsafe_ccopy_slice_0_type τ `{!iType _ τ} t1 sz1 (i1 : Z) t2 sz2 (i2 n : Z) :
    0 < sz1 →
    0 < sz2 →
    (0 ≤ i1)%Z →
    (0 ≤ i2)%Z →
    (0 ≤ n)%Z →
    (i1 + n ≤ sz1)%Z →
    (n ≤ sz2)%Z →
    {{{
      itype_array τ sz1 t1 ∗
      itype_array τ sz2 t2
    }}}
      array_unsafe_ccopy_slice_0 t1 #i1 t2 #i2 #n
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "% % % % % % % %Φ (#Htype1 & #Htype2) HΦ".

    wp_rec.
    wp_smart_apply (array_size_type with "Htype2") as "_".
    wp_pures.
    rewrite Z.rem_mod_nonneg; [lia.. |].
    case_bool_decide; wp_pures.

    - wp_apply (array_unsafe_copy_slice_type τ t1 with "[$]") as "_"; [lia.. |].
      iSteps.

    - wp_apply (array_unsafe_copy_slice_type τ t1 with "[$]") as "_"; [lia.. |].
      wp_smart_apply (array_unsafe_copy_slice_type τ t1 with "[$]") as "_"; [lia.. |].
      iSteps.
  Qed.
  Lemma array_unsafe_ccopy_slice_type τ `{!iType _ τ} t1 sz1 (i1 : Z) t2 sz2 (i2 n : Z) :
    0 < sz1 →
    0 < sz2 →
    (0 ≤ i1)%Z →
    (0 ≤ i2)%Z →
    (0 ≤ n)%Z →
    (n ≤ sz1)%Z →
    (n ≤ sz2)%Z →
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
    iIntros "% % % % % % % %Φ (#Htype1 & #Htype2) HΦ".

    wp_rec.
    wp_smart_apply (array_size_type with "Htype1") as "_".
    wp_pures.
    rewrite Z.rem_mod_nonneg; [lia.. |].
    case_bool_decide; wp_pures.

    - wp_apply (array_unsafe_ccopy_slice_0_type τ t1 with "[$]") as "_"; [lia.. |].
      iSteps.

    - wp_apply (array_unsafe_ccopy_slice_0_type τ t1 with "[$]") as "_"; [lia.. |].
      wp_smart_apply (array_unsafe_ccopy_slice_0_type τ t1 with "[$]") as "_"; [lia.. |].
      iSteps.
  Qed.
  #[local] Lemma array_unsafe_ccopy_slice_0_type' τ `{!iType _ τ} t1 sz1 (i1 : Z) t2 sz2 (i2 : Z) i2_ vs (n : Z) :
    0 < sz1 →
    0 < sz2 →
    length vs ≤ sz2 →
    (0 ≤ i1)%Z →
    (i1 + length vs ≤ sz1)%Z →
    i2 = ⁺i2_ →
    n = length vs →
    {{{
      itype_array τ sz1 t1 ∗
      array_cslice t2 sz2 i2_ (DfracOwn 1) vs
    }}}
      array_unsafe_ccopy_slice_0 t1 #i1 t2 #i2 #n
    {{{ ws,
      RET ();
      ⌜length ws = length vs⌝ ∗
      array_cslice t2 sz2 i2_ (DfracOwn 1) ws ∗
      [∗ list] w ∈ ws, τ w
    }}}.
  Proof.
    iIntros (Hsz1 Hsz2 ? ? ? -> ->) "%Φ (#Htype1 & Hcslice2) HΦ".

    wp_rec.
    wp_smart_apply (array_size_spec_cslice with "Hcslice2") as "Hcslice2".
    wp_pures.
    rewrite Z.rem_mod_nonneg; [lia.. |].
    rewrite array_cslice_to_slice //.
    iDestruct "Hcslice2" as "(#Hinv2 & Hslice21 & Hslice22)".
    case_bool_decide as Hif; wp_pures.

    - wp_apply (array_unsafe_copy_slice_type' with "[$Htype1 $Hslice21]") as (ws) "(%Hws & Hslice21 & #Hws)"; [simpl_length; lia.. |].
      simpl_length in Hws.
      iApply ("HΦ" with "[- $Hws]").
      iSteps.
      iEval (rewrite array_cslice_to_slice; [lia.. |]).
      iEval (rewrite firstn_all2; first lia).
      iEval (rewrite !skipn_all2; [lia.. |]).
      iSteps.
      iApply (array_slice_nil with "Hslice22").

    - wp_apply (array_unsafe_copy_slice_type' with "[$Htype1 $Hslice21]") as (ws1) "(%Hws1 & Hslice21 & #Hws1)"; [simpl_length; lia.. |].
      wp_smart_apply (array_unsafe_copy_slice_type' with "[$Htype1 $Hslice22]") as (ws2) "(%Hws2 & Hslice22 & #Hws2)"; [simpl_length; lia.. |].
      iDestruct (big_sepL_app_2 with "Hws1 Hws2") as "Hws".
      iApply ("HΦ" with "[- $Hws]").
      simpl_length in *. iSteps.
      iEval (rewrite array_cslice_to_slice; [simpl_length; lia.. |]).
      iEval (rewrite take_app_length'; first lia).
      iEval (rewrite drop_app_length'; first lia).
      iSteps.
  Qed.
  Lemma array_unsafe_ccopy_slice_type' τ `{!iType _ τ} t1 sz1 (i1 : Z) t2 sz2 (i2 : Z) i2_ vs (n : Z) :
    0 < sz1 →
    length vs ≤ sz1 →
    0 < sz2 →
    length vs ≤ sz2 →
    (0 ≤ i1)%Z →
    i2 = ⁺i2_ →
    n = length vs →
    {{{
      itype_array τ sz1 t1 ∗
      array_cslice t2 sz2 i2_ (DfracOwn 1) vs
    }}}
      array_unsafe_ccopy_slice t1 #i1 t2 #i2 #n
    {{{ ws,
      RET ();
      ⌜length ws = length vs⌝ ∗
      array_cslice t2 sz2 i2_ (DfracOwn 1) ws ∗
      [∗ list] w ∈ ws, τ w
    }}}.
  Proof.
    iIntros (Hsz1 ? Hsz2 ? Hi1 -> ?) "%Φ (#Htype1 & Hcslice2) HΦ".

    wp_rec.
    wp_smart_apply (array_size_type with "Htype1") as "_".
    wp_pures.
    rewrite Z.rem_mod_nonneg; [lia.. |].
    case_bool_decide as Hif; wp_pures.

    - wp_apply (array_unsafe_ccopy_slice_0_type' with "[$Htype1 $Hcslice2]") as (ws) "(%Hws & Hcslice2 & Hws)"; [simpl_length; lia.. |].
      iSteps.

    - rewrite -(take_drop (sz1 - ₊i1 `mod` sz1) vs).
      iDestruct (array_cslice_app_2 with "Hcslice2") as "(Hcslice21 & Hcslice22)"; first done.
      assert (i1 `mod` sz1 = ⁺(₊i1 `mod` sz1))%Z.
      { rewrite Nat2Z.inj_mod Z2Nat.id //. }
      wp_apply (array_unsafe_ccopy_slice_0_type' with "[$Htype1 $Hcslice21]") as (ws1) "(%Hws1 & Hcslice21 & Hws1)"; [simpl_length; lia.. |].
      wp_smart_apply (array_unsafe_ccopy_slice_0_type' with "[$Htype1 $Hcslice22]") as (ws2) "(%Hws2 & Hcslice22 & Hws2)"; [simpl_length; lia.. |].
      iDestruct (big_sepL_app_2 with "Hws1 Hws2") as "Hws".
      iApply ("HΦ" with "[- $Hws]").
      simpl_length in *. iSteps.
      iApply (array_cslice_app_1 with "Hcslice21 Hcslice22"); first lia.
  Qed.

  Lemma array_ccopy_slice_type τ `{!iType _ τ} t1 sz1 (i1 : Z) t2 sz2 (i2 : Z) (n : Z) :
    0 < sz1 →
    0 < sz2 →
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
    iIntros "% % %Φ (#Htype1 & #Htype2) HΦ".
    wp_rec.
    do 3 (wp_smart_apply assume_spec' as "%").
    wp_smart_apply (array_size_type with "Htype1") as "_".
    wp_smart_apply (array_size_type with "Htype2") as "_".
    do 4 (wp_smart_apply assume_spec' as "%").
    wp_smart_apply (array_unsafe_ccopy_slice_type τ t1 with "[$]"); [lia.. |].
    iSteps.
  Qed.

  Lemma array_unsafe_ccopy_type τ `{!iType _ τ} t1 sz1 (i1 : Z) t2 sz2 (i2 : Z) :
    0 < sz1 →
    0 < sz2 →
    sz1 ≤ sz2 →
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
    iIntros "% % % % % %Φ (#Htype1 & #Htype2) HΦ".
    wp_rec.
    wp_smart_apply (array_size_type with "Htype1") as "_".
    wp_apply (array_unsafe_ccopy_slice_type τ t1 with "[$]"); [lia.. |].
    iSteps.
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
    wp_smart_apply (array_unsafe_ccopy_type τ t1 with "[$]"); [lia.. |].
    iSteps.
  Qed.

  Lemma array_unsafe_cgrow_slice_type τ `{!iType _ τ} sz t (i n : Z) sz' v :
    0 < sz →
    (0 ≤ i)%Z →
    (0 ≤ n)%Z →
    (0 < sz')%Z →
    (n ≤ sz)%Z →
    (n ≤ sz')%Z →
    {{{
      itype_array τ sz t ∗
      τ v
    }}}
      array_unsafe_cgrow_slice t #i #n #sz' v
    {{{ t',
      RET t';
      itype_array τ ₊sz' t'
    }}}.
  Proof.
    iIntros "% % % % % % %Φ (#Htype & #Hv) HΦ".

    wp_rec.
    wp_smart_apply (array_unsafe_make_type with "Hv") as (t') "#Htype'"; first lia.
    wp_smart_apply (array_unsafe_ccopy_slice_type τ t with "[$]") as "_"; [lia.. |].
    wp_pures.
    iApply ("HΦ" with "Htype'").
  Qed.

  Lemma array_unsafe_cgrow_type τ `{!iType _ τ} sz t (i n : Z) sz' v :
    0 < sz →
    (0 ≤ i)%Z →
    (0 < sz')%Z →
    (sz ≤ sz')%Z →
    {{{
      itype_array τ sz t ∗
      τ v
    }}}
      array_unsafe_cgrow t #i #sz' v
    {{{ t',
      RET t';
      itype_array τ ₊sz' t'
    }}}.
  Proof.
    iIntros "% % % % %Φ (#Htype & #Hv) HΦ".

    wp_rec.
    wp_smart_apply (array_size_type with "Htype") as "_".
    wp_apply (array_unsafe_cgrow_slice_type with "[$Htype $Hv]"); [lia.. |].
    iSteps.
  Qed.

  Lemma array_unsafe_cshrink_slice_type τ `{!iType _ τ} sz t (i : Z) sz' :
    0 < sz →
    (0 ≤ i)%Z →
    (0 < sz')%Z →
    (sz' ≤ sz)%Z →
    {{{
      itype_array τ sz t
    }}}
      array_unsafe_cshrink_slice t #i #sz'
    {{{ t',
      RET t';
      itype_array τ ₊sz' t'
    }}}.
  Proof.
    iIntros "% % % % %Φ #Htype HΦ".

    wp_rec.
    wp_smart_apply (array_unsafe_alloc_spec with "[//]") as (t') "Hmodel'"; first lia.
    iDestruct (array_model_to_cslice with "Hmodel'") as "Hcslice'".
    iDestruct (array_cslice_rotation_right_0 ₊i with "Hcslice'") as "Hcslice'"; simpl_length; [lia.. |].
    rewrite rotation_replicate.
    wp_smart_apply (array_unsafe_ccopy_slice_type' with "[$Htype $Hcslice']") as (vs') "(%Hvs' & Hcslice' & Hvs')"; simpl_length; [lia.. |].
    simpl_length in Hvs'.
    iStep 5.
    iApply (itype_array_intro_cslice with "Hcslice' Hvs'"); lia.
  Qed.
End zoo_G.

From zoo_std Require
  array__opaque.
#[global] Opaque array_unsafe_xchg.
#[global] Opaque array_unsafe_cas.
#[global] Opaque array_unsafe_faa.

#[global] Opaque array_inv.
#[global] Opaque array_slice.
#[global] Opaque array_model.
#[global] Opaque array_cslice.
#[global] Opaque itype_array.
