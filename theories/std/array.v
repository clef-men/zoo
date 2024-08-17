From zoo Require Import
  prelude.
From zoo.language Require Import
  notations
  diaframe.
From zoo.std Require Export
  base.
From zoo.std Require Import
  for_upto
  assume
  chunk.
From zoo Require Import
  options.

Implicit Types i j n : nat.
Implicit Types l : location.
Implicit Types v t fn acc : val.
Implicit Types vs : list val.

Definition array_unsafe_alloc : val :=
  fun: "sz" =>
    Alloc #0 "sz".
Definition array_alloc : val :=
  fun: "sz" =>
    assume (#0 ≤ "sz") ;;
    array_unsafe_alloc "sz".

Definition array_create : val :=
  fun: <> =>
    array_unsafe_alloc #0.

Definition array_size : val :=
  fun: "t" =>
    GetSize "t".

Definition array_unsafe_get : val :=
  fun: "t" "i" =>
    Load "t" "i".
Definition array_get : val :=
  fun: "t" "i" =>
    assume (#0 ≤ "i") ;;
    assume ("i" < array_size "t") ;;
    array_unsafe_get "t" "i".

Definition array_unsafe_set : val :=
  fun: "t" "i" "v" =>
    Store "t" "i" "v".
Definition array_set : val :=
  fun: "t" "i" "v" =>
    assume (#0 ≤ "i") ;;
    assume ("i" < array_size "t") ;;
    array_unsafe_set "t" "i" "v".

Definition array_unsafe_fill_slice : val :=
  fun: "t" "i" "n" "v" =>
    for: "j" := #0 to "n" begin
      array_unsafe_set "t" ("i" + "j") "v"
    end.
Definition array_fill_slice : val :=
  fun: "t" "i" "n" "v" =>
    let: "sz" := array_size "t" in
    assume (#0 ≤ "i") ;;
    assume (#0 ≤ "n") ;;
    assume ("i" + "n" ≤ "sz") ;;
    array_unsafe_fill_slice "t" "i" "n" "v".
Definition array_fill : val :=
  fun: "t" "v" =>
    array_unsafe_fill_slice "t" #0 (array_size "t") "v".

Definition array_unsafe_make : val :=
  fun: "sz" "v" =>
    let: "t" := array_unsafe_alloc "sz" in
    array_fill "t" "v" ;;
    "t".
Definition array_make : val :=
  fun: "sz" "v" =>
    assume (#0 ≤ "sz") ;;
    array_unsafe_make "sz" "v".

#[local] Definition array_foldli_aux : val :=
  rec: "array_foldli_aux" "t" "sz" "acc" "fn" "i" =>
    if: "sz" ≤ "i" then (
      "acc"
    ) else (
      let: "v" := array_unsafe_get "t" "i" in
      "array_foldli_aux" "t" "sz" ("fn" "acc" "i" "v") "fn" (#1 + "i")
    ).
Definition array_foldli : val :=
  fun: "t" "acc" "fn" =>
    array_foldli_aux "t" (array_size "t") "acc" "fn" #0.
Definition array_foldl : val :=
  fun: "t" "acc" "fn" =>
    array_foldli "t" "acc" (fun: "acc" <> "v" => "fn" "acc" "v").

#[local] Definition array_foldri_aux : val :=
  rec: "array_foldri_aux" "t" "fn" "acc" "i" =>
    if: "i" ≤ #0 then (
      "acc"
    ) else (
      let: "i" := "i" - #1 in
      let: "v" := array_unsafe_get "t" "i" in
      "array_foldri_aux" "t" "fn" ("fn" "i" "v" "acc") "i"
    ).
Definition array_foldri : val :=
  fun: "t" "fn" "acc" =>
    array_foldri_aux "t" "fn" "acc" (array_size "t").
Definition array_foldr : val :=
  fun: "t" "fn" "acc" =>
    array_foldri "t" (fun: <> => "fn") "acc".

Definition array_iteri : val :=
  fun: "t" "fn" =>
    for: "i" := #0 to array_size "t" begin
      "fn" "i" (array_unsafe_get "t" "i")
    end.
Definition array_iter : val :=
  fun: "t" "fn" =>
    array_iteri "t" (fun: <> => "fn").

Definition array_applyi : val :=
  fun: "t" "fn" =>
    array_iteri "t" (fun: "i" "v" => array_unsafe_set "t" "i" ("fn" "i" "v")).
Definition array_apply : val :=
  fun: "t" "fn" =>
    array_applyi "t" (fun: <> => "fn").

Definition array_unsafe_initi : val :=
  fun: "sz" "fn" =>
    let: "t" := array_unsafe_alloc "sz" in
    array_applyi "t" (fun: "i" <> => "fn" "i") ;;
    "t".
Definition array_initi : val :=
  fun: "sz" "fn" =>
    assume (#0 ≤ "sz") ;;
    array_unsafe_initi "sz" "fn".
Definition array_unsafe_init : val :=
  fun: "sz" "fn" =>
    array_unsafe_initi "sz" (fun: <> => "fn" ()).
Definition array_init : val :=
  fun: "sz" "fn" =>
    assume (#0 ≤ "sz") ;;
    array_initi "sz" "fn".

Definition array_mapi : val :=
  fun: "t" "fn" =>
    array_unsafe_initi (array_size "t") (fun: "i" => "fn" "i" (array_unsafe_get "i")).
Definition array_map : val :=
  fun: "t" "fn" =>
    array_mapi "t" (fun: <> => "fn").

Definition array_unsafe_copy_slice : val :=
  fun: "t1" "i1" "t2" "i2" "n" =>
    for: "i" := #0 to "n" begin
      let: "v" := array_unsafe_get "t1" ("i1" + "n") in
      array_unsafe_set "t2" ("i2" + "n") "v"
    end.
Definition array_copy_slice : val :=
  fun: "t1" "i1" "t2" "i2" "n" =>
    let: "sz1" := array_size "t1" in
    let: "sz2" := array_size "t2" in
    assume (#0 ≤ "i1") ;;
    assume (#0 ≤ "i2") ;;
    assume (#0 ≤ "n") ;;
    assume ("i1" + "n" ≤ "sz1") ;;
    assume ("i2" + "n" ≤ "sz2") ;;
    array_unsafe_copy_slice "t1" "i1" "t2" "i2" "n".
Definition array_unsafe_copy : val :=
  fun: "t1" "t2" "i2" =>
    array_unsafe_copy_slice "t1" #0 "t2" "i2" (array_size "t1").
Definition array_copy : val :=
  fun: "t1" "t2" "i2" =>
    assume (#0 ≤ "i2") ;;
    assume ("i2" + array_size "t1" ≤ array_size "t2") ;;
    array_unsafe_copy_slice "t1" "t2" "i2".

Definition array_unsafe_grow : val :=
  fun: "t" "sz'" "v'" =>
    let: "sz" := array_size "t" in
    let: "t'" := array_unsafe_alloc "sz'" in
    array_unsafe_copy "t" "t'" #0 ;;
    array_unsafe_fill_slice "t'" "sz" ("sz'" - "sz") "v'" ;;
    "t'".
Definition array_grow : val :=
  fun: "t" "sz'" "v'" =>
    assume (array_size "t" ≤ "sz'") ;;
    array_unsafe_grow "t" "sz'" "v'".

Definition array_unsafe_sub : val :=
  fun: "t" "i" "n" =>
    let: "t'" := array_unsafe_alloc "n" in
    array_unsafe_copy_slice "t" "i" "t'" #0 "n" ;;
    "t'".
Definition array_sub : val :=
  fun: "t" "i" "n" =>
    assume (#0 ≤ "i") ;;
    assume (#0 ≤ "n") ;;
    assume ("i" + "n" ≤ array_size "t") ;;
    array_unsafe_sub "t" "i" "n".

Definition array_unsafe_shrink : val :=
  fun: "t" "sz'" =>
    array_unsafe_sub "t" #0 "sz'".
Definition array_shrink : val :=
  fun: "t" "sz'" =>
    assume (#0 ≤ "sz'") ;;
    assume ("sz'" ≤ array_size "t") ;;
    array_unsafe_shrink "t" "sz'".

Definition array_clone : val :=
  fun: "t" =>
    array_unsafe_shrink "t" (array_size "t").

Definition array_unsafe_cget : val :=
  fun: "t" "i" =>
    array_unsafe_get "t" ("i" `rem` array_size "t").
Definition array_cget : val :=
  fun: "t" "i" =>
    assume (#0 ≤ "i") ;;
    array_unsafe_cget "t" "i".

Definition array_unsafe_cset : val :=
  fun: "t" "i" "v" =>
    array_unsafe_set "t" ("i" `rem` array_size "t") "v".
Definition array_cset : val :=
  fun: "t" "i" "v" =>
    assume (#0 ≤ "i") ;;
    array_unsafe_cset "t" "i" "v".

Definition array_unsafe_ccopy_slice : val :=
  fun: "t1" "i1" "t2" "i2" "n" =>
    let: "sz1" := array_size "t1" in
    let: "sz2" := array_size "t2" in
    for: "j" := #0 to "n" begin
      let: "v" := array_unsafe_get "t1" (("i1" + "j") `rem` "sz1") in
      array_unsafe_set "t2" (("i2" + "j") `rem` "sz2") "v"
    end.
Definition array_ccopy_slice : val :=
  fun: "t1" "i1" "t2" "i2" "n" =>
    assume (#0 ≤ "i1") ;;
    assume (#0 ≤ "i2") ;;
    assume (#0 ≤ "n") ;;
    assume ("n" ≤ array_size "t1") ;;
    assume ("n" ≤ array_size "t2") ;;
    array_unsafe_ccopy_slice "t1" "i1" "t2" "i2" "n".

Definition array_unsafe_ccopy : val :=
  fun: "t1" "i1" "t2" "i2" =>
    array_unsafe_ccopy_slice "t1" "i1" "t2" "i2" (array_size "t1").
Definition array_ccopy : val :=
  fun: "t1" "i1" "t2" "i2" =>
    assume (#0 ≤ "i1") ;;
    assume (#0 ≤ "i2") ;;
    assume (array_size "t1" ≤ array_size "t2") ;;
    array_unsafe_ccopy "t1" "i1" "t2" "i2".

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
      setoid_rewrite insert_app_r_alt; rewrite take_length; last lia.
      rewrite Nat.min_l; first lia. rewrite Nat.sub_diag /=.
      iFrame. iIntros "%w Hslice2".
      iApply (array_slice_app3_1 with "Hslice1 Hslice2 Hslice3"); rewrite take_length /=; lia.
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
        □ (array_slice t 0 dq vs -∗ array_model t dq vs).
    Proof.
      rewrite array_model_to_slice. iSteps.
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
      iSteps. rewrite insert_length. iSteps.
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

    Lemma array_cslice_update {t sz i dq vs} k v :
      vs !! k = Some v →
      array_cslice t sz i dq vs ⊢
        array_cslice t sz (i + k) dq [v] ∗
        ( ∀ w,
          array_cslice t sz (i + k) dq [w] -∗
          array_cslice t sz i dq (<[k := w]> vs)
        ).
    Proof.
      intros.
      rewrite /array_cslice.
      setoid_rewrite <- chunk_cslice_singleton.
      setoid_rewrite chunk_cslice_update at 1; last done.
      iSteps.
    Qed.
    Lemma array_cslice_lookup_acc {t sz i dq vs} k v :
      vs !! k = Some v →
      array_cslice t sz i dq vs ⊢
        array_cslice t sz (i + k) dq [v] ∗
        ( array_cslice t sz (i + k) dq [v] -∗
          array_cslice t sz i dq vs
        ).
    Proof.
      intros.
      rewrite /array_cslice.
      setoid_rewrite <- chunk_cslice_singleton.
      setoid_rewrite chunk_cslice_lookup_acc at 1; last done.
      iSteps.
    Qed.
    Lemma array_cslice_lookup {t sz i dq vs} k v :
      vs !! k = Some v →
      array_cslice t sz i dq vs ⊢
      array_cslice t sz (i + k) dq [v].
    Proof.
      intros.
      rewrite /array_cslice.
      setoid_rewrite <- chunk_cslice_singleton.
      setoid_rewrite chunk_cslice_lookup at 1; last done.
      iSteps.
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

  #[local] Typeclasses Opaque array_slice array_model.

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
    {{{ True }}}
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
    iSteps. rewrite replicate_length. iSteps.
  Qed.
  Lemma array_alloc_spec sz :
    {{{ True }}}
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
    {{{ True }}}
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
      RET #sz; True
    }}}.
  Proof.
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
    iSteps.
  Qed.

  Lemma array_unsafe_get_spec_atomic_slice t (j : Z) :
    <<<
      True
    | ∀∀ dq vs i v,
      ⌜(i ≤ j)%Z ∧ vs !! (Z.to_nat j - i) = Some v⌝ ∗
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
    iMod "HΦ" as "(%dq & %vs & %i & %v & ((%Hi & %Hlookup) & (%l & -> & Hmodel)) & _ & HΦ)".
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
    iIntros (Hi Hlookup ->) "%Φ Hmodel HΦ".
    iApply wp_fupd.
    awp_apply (array_unsafe_get_spec_atomic with "[//]") without "HΦ"; first done.
    rewrite /atomic_acc /=.
    iExists dq, vs, v.
    iApply fupd_mask_intro; first done. iIntros "Hclose".
    iSplitL "Hmodel"; first auto. iSplit; first iSteps.
    iIntros "Hmodel". iMod "Hclose" as "_". iIntros "!> H£ HΦ".
    iMod (lc_fupd_elim_later with "H£ HΦ") as "HΦ".
    iSteps.
  Qed.

  Lemma array_get_spec_atomic_slice t sz (j : Z) :
    <<<
      array_inv t sz
    | ∀∀ dq vs i v,
      ⌜(i ≤ j)%Z ∧ vs !! (Z.to_nat j - i) = Some v⌝ ∗
      array_slice t i dq vs
    >>>
      array_get t #j
    <<<
      array_slice t i dq vs
    | RET v;
      £ 1
    >>>.
  Proof.
    iIntros "!> %Φ #Hinv HΦ".
    wp_rec.
    wp_smart_apply assume_spec' as "_".
    wp_smart_apply (array_size_spec_inv with "Hinv") as "_".
    wp_smart_apply assume_spec' as "_".
    wp_smart_apply (array_unsafe_get_spec_atomic_slice with "[//] HΦ").
  Qed.
  Lemma array_get_spec_atomic_cell t sz (i : Z) i_ :
    i = Z.of_nat i_ →
    <<<
      array_inv t sz
    | ∀∀ dq v,
      array_slice t i_ dq [v]
    >>>
      array_get t #i
    <<<
      array_slice t i_ dq [v]
    | RET v;
      £ 1
    >>>.
  Proof.
    iIntros (->) "!> %Φ #Hinv HΦ".
    awp_apply (array_get_spec_atomic_slice with "Hinv").
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%dq %v Hslice".
    rewrite /atomic_acc /= Nat2Z.id.
    iExists dq, [v], i_, v. rewrite Nat.sub_diag. iSteps.
  Qed.
  Lemma array_get_spec_atomic t (i : Z) :
    (0 ≤ i)%Z →
    <<<
      True
    | ∀∀ dq vs v,
      ⌜vs !! Z.to_nat i = Some v⌝ ∗
      array_model t dq vs
    >>>
      array_get t #i
    <<<
      array_model t dq vs
    | RET v;
      £ 1
    >>>.
  Proof.
    iIntros "%Hi !> %Φ _ HΦ".
    wp_rec.
    wp_smart_apply assume_spec' as "_".
    awp_smart_apply (array_size_spec_atomic with "[//]").
    iApply (aacc_aupd_abort with "HΦ"); first done. iIntros "%dq %vs %v (% & Hmodel)".
    iAaccIntro with "Hmodel"; first iSteps.
    iIntros "Hmodel !>". iSplitL; first auto. iIntros "HΦ !> _".
    wp_smart_apply assume_spec' as "_".
    wp_smart_apply (array_unsafe_get_spec_atomic with "[//] HΦ"); first done.
  Qed.
  Lemma array_get_spec_slice k t sz i dq vs (j : Z) v :
    (i ≤ j)%Z →
    vs !! k = Some v →
    k = Z.to_nat j - i →
    {{{
      array_inv t sz ∗
      array_slice t i dq vs
    }}}
      array_get t #j
    {{{
      RET v;
      array_slice t i dq vs
    }}}.
  Proof.
    iIntros (Hi Hlookup ->) "%Φ (#Hinv & Hslice) HΦ".
    wp_rec.
    wp_smart_apply assume_spec' as "_".
    wp_smart_apply (array_size_spec_inv with "Hinv") as "_".
    wp_smart_apply assume_spec' as "_".
    wp_smart_apply (array_unsafe_get_spec_slice with "Hslice"); done.
  Qed.
  Lemma array_get_spec_cell t sz (i : Z) i_ dq v :
    i = Z.of_nat i_ →
    {{{
      array_inv t sz ∗
      array_slice t i_ dq [v]
    }}}
      array_get t #i
    {{{
      RET v;
      array_slice t i_ dq [v]
    }}}.
  Proof.
    intros.
    eapply (array_get_spec_slice 0); [lia | done | lia].
  Qed.
  Lemma array_get_spec i_ t (i : Z) dq vs v :
    (0 ≤ i)%Z →
    vs !! i_ = Some v →
    i_ = Z.to_nat i →
    {{{
      array_model t dq vs
    }}}
      array_get t #i
    {{{
      RET v;
      array_model t dq vs
    }}}.
  Proof.
    iIntros (Hi Hlookup ->) "%Φ Hmodel HΦ".
    wp_rec.
    wp_smart_apply assume_spec' as "_".
    wp_smart_apply (array_size_spec with "Hmodel") as "Hmodel".
    wp_smart_apply assume_spec' as "_".
    wp_smart_apply (array_unsafe_get_spec with "Hmodel"); done.
  Qed.

  Lemma array_unsafe_set_spec_atomic_slice t (j : Z) v :
    <<<
      True
    | ∀∀ sz vs i,
      ⌜i ≤ j < i + length vs⌝%Z ∗
      array_slice t sz i (DfracOwn 1) vs
    >>>
      array_unsafe_set t #j v
    <<<
      array_slice t sz i (DfracOwn 1) (<[Z.to_nat j - i := v]> vs)
    | RET ();
      £ 1
    >>>.
  Proof.
    rewrite /array_model /array_slice.
    iIntros "!> %Φ _ HΦ".
    wp_rec credit:"H£". wp_pures.
    iMod "HΦ" as "(%sz & %vs & %i & (%Hj & (%l & -> & #Hhdr & Hmodel)) & _ & HΦ)".
    iDestruct (chunk_model_update' j with "Hmodel") as "(H↦ & Hmodel)"; [lia | | done |].
    { destruct (nth_lookup_or_length vs (Z.to_nat j - Z.to_nat i) inhabitant); [done | lia]. }
    wp_store.
    iApply ("HΦ" with "[H↦ Hmodel] [H£]"); last iSteps.
    rewrite Nat2Z.id. iSteps.
  Qed.
  Lemma array_unsafe_set_spec_atomic_cell t (i : Z) v :
    <<<
      True
    | ∀∀ sz i_ w,
      ⌜i = Z.of_nat i_⌝ ∗
      array_slice t sz i_ (DfracOwn 1) [w]
    >>>
      array_unsafe_set t #i v
    <<<
      array_slice t sz i_ (DfracOwn 1) [v]
    | RET ();
      £ 1
    >>>.
  Proof.
    iIntros "!> %Φ _ HΦ".
    awp_apply (array_unsafe_set_spec_atomic_slice with "[//]").
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%sz %i_ %w (-> & Hslice)".
    rewrite /atomic_acc /= Nat2Z.id.
    iExists sz, [w], i_. rewrite Nat.sub_diag. iSteps.
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
    rewrite /array_model.
    iIntros "%Hi !> %Φ _ HΦ".
    awp_apply (array_unsafe_set_spec_atomic_slice with "[//]").
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs (%Hlookup & Hmodel)".
    rewrite /atomic_acc /=.
    iExists (length vs), vs, 0. rewrite Nat.sub_0_r insert_length. iSteps.
  Qed.
  Lemma array_unsafe_set_spec_slice t sz i vs (j : Z) v :
    (i ≤ j < i + length vs)%Z →
    {{{
      array_slice t sz i (DfracOwn 1) vs
    }}}
      array_unsafe_set t #j v
    {{{
      RET ();
      array_slice t sz i (DfracOwn 1) (<[Z.to_nat j - i := v]> vs)
    }}}.
  Proof.
    iIntros "%Hj %Φ Hslice HΦ".
    iApply wp_fupd.
    awp_apply (array_unsafe_set_spec_atomic_slice with "[//]") without "HΦ".
    rewrite /atomic_acc /=.
    iExists sz, vs, i.
    iApply fupd_mask_intro; first done. iIntros "Hclose".
    iSplitL "Hslice"; first auto. iSplit; first iSteps.
    iIntros "Hslice". iMod "Hclose" as "_". iIntros "!> H£ HΦ".
    iMod (lc_fupd_elim_later with "H£ HΦ") as "HΦ".
    iSteps.
  Qed.
  Lemma array_unsafe_set_spec_cell t sz (i : Z) i_ w v :
    i = Z.of_nat i_ →
    {{{
      array_slice t sz i_ (DfracOwn 1) [w]
    }}}
      array_unsafe_set t #i v
    {{{
      RET ();
      array_slice t sz i_ (DfracOwn 1) [v]
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
    iIntros "%Hi %Φ Hmodel HΦ".
    wp_apply (array_unsafe_set_spec_slice with "Hmodel"); first done.
    rewrite Nat.sub_0_r /array_model insert_length //.
  Qed.

  Lemma array_set_spec_atomic_slice t (j : Z) v :
    <<<
      True
    | ∀∀ sz vs i,
      ⌜(i ≤ j < i + length vs)%Z⌝ ∗
      array_slice t sz i (DfracOwn 1) vs
    >>>
      array_set t #j v
    <<<
      array_slice t sz i (DfracOwn 1) (<[Z.to_nat j - i := v]> vs)
    | RET ();
      £ 1
    >>>.
  Proof.
    iIntros "!> %Φ _ HΦ".
    wp_rec.
    wp_smart_apply assume_spec' as "_".
    awp_smart_apply (array_size_spec_atomic_slice with "[//]").
    iApply (aacc_aupd_abort with "HΦ"); first done. iIntros "%sz %vs %i (%Hj & Hslice)".
    iAaccIntro with "Hslice"; first iSteps.
    iIntros "Hslice !>". iSplitL; first auto. iIntros "HΦ !> _".
    wp_smart_apply assume_spec' as "_".
    wp_smart_apply (array_unsafe_set_spec_atomic_slice with "[//] HΦ").
  Qed.
  Lemma array_set_spec_atomic_cell t (i : Z) v :
    <<<
      True
    | ∀∀ sz i_ w,
      ⌜i = Z.of_nat i_⌝ ∗
      array_slice t sz i_ (DfracOwn 1) [w]
    >>>
      array_set t #i v
    <<<
      array_slice t sz i_ (DfracOwn 1) [v]
    | RET ();
      £ 1
    >>>.
  Proof.
    iIntros "!> %Φ _ HΦ".
    awp_apply (array_set_spec_atomic_slice with "[//]").
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%sz %i_ %w (-> & Hslice)".
    rewrite /atomic_acc /= Nat2Z.id.
    iExists sz, [w], i_. rewrite Nat.sub_diag. iSteps.
  Qed.
  Lemma array_set_spec_atomic t (i : Z) v :
    (0 ≤ i)%Z →
    <<<
      True
    | ∀∀ vs,
      ⌜(i < length vs)%Z⌝ ∗
      array_model t (DfracOwn 1) vs
    >>>
      array_set t #i v
    <<<
      array_model t (DfracOwn 1) (<[Z.to_nat i := v]> vs)
    | RET ();
      £ 1
    >>>.
  Proof.
    rewrite /array_model.
    iIntros "%Hi !> %Φ _ HΦ".
    awp_apply (array_set_spec_atomic_slice with "[//]").
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs (%Hi'  & Hmodel)".
    rewrite /atomic_acc /=.
    iExists (length vs), vs, 0. rewrite Nat.sub_0_r insert_length. iSteps.
  Qed.
  Lemma array_set_spec_slice t sz i vs (j : Z) v :
    (i ≤ j < i + length vs)%Z →
    {{{
      array_slice t sz i (DfracOwn 1) vs
    }}}
      array_set t #j v
    {{{
      RET ();
      array_slice t sz i (DfracOwn 1) (<[Z.to_nat j - i := v]> vs)
    }}}.
  Proof.
    iIntros "%Hj %Φ Hslice HΦ".
    wp_rec.
    wp_smart_apply assume_spec' as "_".
    wp_smart_apply (array_size_spec_slice with "Hslice") as "Hslice".
    wp_smart_apply assume_spec' as "_".
    wp_smart_apply (array_unsafe_set_spec_slice with "Hslice"); done.
  Qed.
  Lemma array_set_spec_cell t sz (i : Z) i_ w v :
    i = Z.of_nat i_ →
    {{{
      array_slice t sz i_ (DfracOwn 1) [w]
    }}}
      array_set t #i v
    {{{
      RET ();
      array_slice t sz i_ (DfracOwn 1) [v]
    }}}.
  Proof.
    iIntros (->) "%Φ Hslice HΦ".
    wp_apply (array_set_spec_slice with "Hslice").
    { simpl. lia. }
    rewrite Nat2Z.id Nat.sub_diag //.
  Qed.
  Lemma array_set_spec t (i : Z) vs v :
    (0 ≤ i < length vs)%Z →
    {{{
      array_model t (DfracOwn 1) vs
    }}}
      array_set t #i v
    {{{
      RET ();
      array_model t (DfracOwn 1) (<[Z.to_nat i := v]> vs)
    }}}.
  Proof.
    iIntros "%Hi %Φ Hmodel HΦ".
    wp_apply (array_set_spec_slice with "Hmodel"); first done.
    rewrite Nat.sub_0_r /array_model insert_length //.
  Qed.

  Lemma array_unsafe_fill_slice_spec_atomic Ψ t sz (i n : Z) v :
    (0 ≤ i)%Z →
    (0 ≤ n)%Z →
    {{{
      ▷ Ψ 0 ∗
      □ (
        ∀ j,
        ⌜j < Z.to_nat n⌝ -∗
        Ψ j -∗
        au_store t sz (Z.to_nat i + j) v (
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
    wp_smart_apply (for_upto_spec_strong Ψ' with "[$HΨ]"); last rewrite Z.sub_0_r //.
    iIntros "!> %j_ %j (-> & %Hj) HΨ". rewrite Z.add_0_l in Hj |- *.
    iDestruct ("H" with "[%] HΨ") as "H'"; first lia.
    awp_smart_apply (array_unsafe_set_spec_atomic_cell with "[//]").
    iApply (aacc_aupd_commit with "H'"); first done. iIntros "%w H↦".
    rewrite /atomic_acc /=.
    repeat iExists _. iFrame. iSteps.
  Qed.
  Lemma array_unsafe_fill_slice_spec t sz vs (i : Z) i_ (n : Z) v :
    i = Z.of_nat i_ →
    n = length vs →
    {{{
      array_slice t sz i_ (DfracOwn 1) vs
    }}}
      array_unsafe_fill_slice t #i #n v
    {{{
      RET ();
      array_slice t sz i_ (DfracOwn 1) (replicate (Z.to_nat n) v)
    }}}.
  Proof.
    iIntros (-> ->) "%Φ Hslice HΦ".
    pose Ψ j :=
      array_slice t sz i_ (DfracOwn 1) (replicate j v ++ drop j vs).
    wp_apply (array_unsafe_fill_slice_spec_atomic Ψ with "[$Hslice]"); [lia.. | |]; last first.
    { rewrite /Ψ skipn_all2; first lia. rewrite right_id //. }
    iIntros "!> %j %Hj Hslice". rewrite Nat2Z.id.
    opose proof* (list_lookup_lookup_total_lt vs j) as Hlookup; first lia.
    iDestruct (array_slice_update j with "Hslice") as "(H↦ & Hslice)".
    { rewrite lookup_app_r replicate_length // lookup_drop Nat.sub_diag right_id //. }
    iAuIntro. iAaccIntro with "H↦"; first auto with iFrame. iIntros "H↦".
    iDestruct ("Hslice" with "H↦") as "Hslice".
    rewrite /Ψ replicate_S_end -assoc insert_app_r_alt replicate_length // Nat.sub_diag.
    erewrite drop_S; done.
  Qed.

  Lemma array_fill_slice_spec t sz vs (i : Z) i_ (n : Z) v :

    i = Z.of_nat i_ →
    n = length vs →
    {{{
      array_slice t sz i_ (DfracOwn 1) vs
    }}}
      array_fill_slice t #i #n v
    {{{
      RET ();
      array_slice t sz i_ (DfracOwn 1) (replicate (Z.to_nat n) v)
    }}}.
  Proof.
    iIntros (-> ->) "%Φ Hslice HΦ".
    wp_rec.
    wp_smart_apply (array_size_spec_slice with "Hslice") as "Hslice".
    repeat (wp_smart_apply assume_spec' as "_").
    wp_smart_apply (array_unsafe_fill_slice_spec with "Hslice"); [done.. |].
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
    wp_apply (array_unsafe_fill_slice_spec with "Hmodel") as "model"; [done.. |].
    iApply "HΦ".
    rewrite Nat2Z.id -{1}(replicate_length (length vs) v) //.
  Qed.

  Lemma array_unsafe_make_spec sz v :
    (0 ≤ sz)%Z →
    {{{ True }}}
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
    rewrite replicate_length . iSteps.
  Qed.
  Lemma array_make_spec sz v :
    (0 ≤ sz)%Z →
    {{{ True }}}
      array_make #sz v
    {{{ t,
      RET t;
      array_model t (DfracOwn 1) (replicate (Z.to_nat sz) v)
    }}}.
  Proof.
    iIntros "% %Φ _ HΦ".
    wp_rec.
    wp_smart_apply assume_spec' as "_".
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
        ⌜i < sz ∧ i = length vs⌝ -∗
        Ψ i vs o acc -∗
        match o with
        | None =>
            au_load t sz i (λ v,
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
      iDestruct ("H" with "[%] HΨ") as "H'"; first lia.
      awp_smart_apply (array_unsafe_get_spec_atomic_cell with "[//]") without "HΦ".
      iApply (aacc_aupd_commit with "H'"); first done. iIntros "%dq %v H↦".
      rewrite /atomic_acc /= Nat2Z.id.
      repeat iExists _. iFrame. iStep 2; first iSteps. iIntros "$ !> HΨ !> H£ HΦ".
      iMod (lc_fupd_elim_later with "H£ HΨ") as "HΨ".
      wp_smart_apply (wp_wand with "(H [%] HΨ)") as "%acc' HΨ"; first lia.
      rewrite Z.add_1_l -Nat2Z.inj_succ.
      wp_apply ("IH" with "[%] [%] [%] HΨ [HΦ]"); rewrite ?app_length; [naive_solver lia.. |].
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
        ⌜i < sz ∧ i = length vs⌝ -∗
        Ψ i vs o acc -∗
        match o with
        | None =>
            au_load t sz i (λ v,
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
    iStep. clear acc. iIntros "!> %i %vs_left %o %acc (%Hi1 & %Hi2) (-> & Hmodel & HΨ & %Ho)".
    opose proof* (list_lookup_lookup_total_lt vs i); first lia.
    destruct o as [v |].
    - rewrite Ho.
      wp_apply (wp_wand with "(Hfn [] HΨ)"); first iSteps. clear acc. iIntros "%acc HΨ". iFrame.
      erewrite take_S_r; done.
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
    erewrite drop_S; last done.
    iDestruct "HΞ" as "(Hfn & HΞ)".
    rewrite Nat.add_0_r. setoid_rewrite Nat.add_succ_r. iSteps.
  Qed.

  Lemma array_foldl_spec_atomic Ψ t sz acc fn :
    {{{
      array_inv t sz ∗
      ▷ Ψ 0 [] None acc ∗
      □ (
        ∀ i vs (o : option val) acc,
        ⌜i < sz ∧ i = length vs⌝ -∗
        Ψ i vs o acc -∗
        match o with
        | None =>
            au_load t sz i (λ v,
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
    wp_smart_apply (array_foldli_spec_atomic Ψ with "[$Hinv $HΨ] HΦ"). clear acc. iIntros "!> %i %vs %o %acc %Hi HΨ".
    case_match; try wp_pures; iApply ("H" with "[//] HΨ").
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
            au_load t sz i (λ v,
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
      wp_apply ("IH" with "[] [] HΨ [HΦ]"); rewrite ?app_length; [iSteps.. |]. clear acc. iIntros "!> %acc %vs' (<- & HΨ)".
      iApply ("HΦ" $! _ (vs' ++ [v])).
      rewrite app_length -(assoc (++)). iSteps.
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
            au_load t sz i (λ v,
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
        iSteps; iPureIntro; rewrite drop_length; f_equal; lia.
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
    erewrite take_S_r; last done.
    iDestruct "HΞ" as "(HΞ & Hfn & _)".
    rewrite Nat.add_0_r take_length Nat.min_l; first lia. iSteps.
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
            au_load t sz i (λ v,
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
        ⌜i < sz ∧ i = length vs⌝ -∗
        Ψ i vs o -∗
        match o with
        | None =>
            au_load t sz i (λ v,
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
    wp_smart_apply (for_upto_spec_strong Ψ' with "[HΨ]").
    { iSplitL. { iExists []. iSteps. }
      iIntros "!> %i_ %i (-> & %Hi) (%vs & %Hvs & HΨ)". rewrite Z.add_0_l in Hi |- *.
      iDestruct ("H" with "[%] HΨ") as "H'"; first lia.
      awp_smart_apply (array_unsafe_get_spec_atomic_cell with "[//]").
      iApply (aacc_aupd_commit with "H'"); first done. iIntros "%dq %v H↦".
      rewrite /atomic_acc /= Nat2Z.id.
      repeat iExists _. iStep 2; first iSteps. iIntros "$ !> HΨ !> H£".
      iMod (lc_fupd_elim_later with "H£ HΨ") as "HΨ".
      wp_smart_apply (wp_wand with "(H [%] HΨ)") as "%acc' (-> & HΨ)"; first lia.
      iSteps. iExists (vs ++ [v]). rewrite app_length. iSteps.
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
    iStep. iIntros "!> %i %vs_left %o (%Hi1 & %Hi2) (-> & Hmodel & HΨ & %Ho)".
    opose proof* (list_lookup_lookup_total_lt vs i); first lia.
    destruct o as [v |].
    - rewrite Ho.
      wp_apply (wp_wand with "(Hfn [] HΨ)") as (res) "(-> & HΨ)"; first iSteps.
      iSteps. erewrite take_S_r; done.
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
    erewrite drop_S; last done.
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
    rewrite big_sepL_snoc take_length Nat.min_l; last iSteps.
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
    rewrite big_sepL_snoc take_length Nat.min_l; last iSteps.
    eapply Nat.lt_le_incl, lookup_lt_Some. done.
  Qed.

  Lemma array_iter_spec_atomic Ψ t sz fn :
    {{{
      array_inv t sz ∗
      ▷ Ψ 0 [] None ∗
      □ (
        ∀ i vs (o : option val),
        ⌜i < sz ∧ i = length vs⌝ -∗
        Ψ i vs o -∗
        match o with
        | None =>
            au_load t sz i (λ v,
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
    wp_smart_apply (array_iteri_spec_atomic Ψ with "[$Hinv $HΨ] HΦ") as "!> %i %vs %o %Hi HΨ".
    case_match; try wp_pures; iApply ("H" with "[//] HΨ").
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
        ⌜i < sz ∧ i = length vs ∧ length vs = length ws⌝ -∗
        Ψ i vs o ws -∗
        match o with
        | None =>
            au_load t sz i (λ v,
              ▷ Ψ i vs (Some $ inl v) ws
            )
        | Some (inl v) =>
            WP fn #i v {{ w,
              ▷ Ψ i vs (Some $ inr (v, w)) ws
            }}
        | Some (inr (v, w)) =>
            au_store t sz i w (
              ▷ Ψ (S i) (vs ++ [v]) None (ws ++ [w])
            )
        end
      )
    }}}
      array_applyi t fn
    {{{ vs ws,
      RET ();
      ⌜length vs = sz ∧ length vs = length ws⌝ ∗
      Ψ sz vs None ws
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & HΨ & #H) HΦ".
    wp_rec.
    pose (Ψ' i vs o := (
      ∃ ws,
      ⌜length vs = length ws⌝ ∗
      Ψ i vs (inl <$> o) ws
    )%I).
    wp_smart_apply (array_iteri_spec_atomic Ψ' with "[$Hinv HΨ]"); last iSteps.
    iSplitL "HΨ". { iExists []. iSteps. }
    iIntros "!> %i %vs %o (%Hi1 & %Hi2) (%ws & %Hws & HΨ)".
    destruct o as [v |].
    - wp_smart_apply (wp_wand with "(H [//] HΨ)") as "%w HΨ".
      wp_rec. wp_pures.
      iMod ("H" with "[//] HΨ") as "(%v' & H↦ & _ & H')".
      rewrite /array_slice. setoid_rewrite <- chunk_model_singleton.
      iDestruct "H↦" as "(%l & -> & #Hhdr & H↦)".
      wp_store.
      iStep. iExists (ws ++ [w]).
      iMod ("H'" with "[H↦]") as "$"; first iSteps.
      rewrite !app_length. iSteps.
    - iApply (atomic_update_wand with "(H [//] HΨ)").
      iSteps.
  Qed.
  Lemma array_applyi_spec Ψ t vs fn :
    {{{
      ▷ Ψ 0 [] [] ∗
      array_model t (DfracOwn 1) vs ∗
      □ (
        ∀ i v ws,
        ⌜i = length ws ∧ vs !! i = Some v⌝ -∗
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
    { iIntros "%vs_left %ws ((%Hvs_left_1 & %Hws) & (-> & Hmodel & HΨ))".
      rewrite firstn_all2; first lia. rewrite skipn_all2; first lia. rewrite right_id.
      iApply ("HΦ" $! ws). iSteps.
    }
    iStep. iIntros "!> %i %vs_left %o %ws (%Hvs_left & %Hi & %Hws) (-> & Hmodel & HΨ)".
    opose proof* (list_lookup_lookup_total_lt vs i); first lia.
    destruct o as [[v | (v & w)] |].
    - iDestruct "HΨ" as "(-> & HΨ)".
      wp_apply (wp_wand with "(Hfn [] HΨ)"); iSteps.
    - iDestruct "HΨ" as "(-> & HΨ)".
      assert ((ws ++ drop i vs) !! i = Some (vs !!! i)).
      { rewrite lookup_app_r; first lia.
        rewrite lookup_drop list_lookup_lookup_total_lt; first lia.
        repeat f_equal. lia.
      }
      iDestruct (array_model_update i with "Hmodel") as "(H↦ & Hmodel)"; first done.
      iAuIntro. iAaccIntro with "H↦"; first iSteps. iIntros "H↦ !>". iFrame.
      iSplit; first rewrite -take_S_r //.
      iDestruct ("Hmodel" with "H↦") as "Hmodel".
      rewrite insert_app_r_alt; first lia.
      erewrite drop_S; last done.
      rewrite Hi Hws Nat.sub_diag -assoc //.
    - assert ((ws ++ drop i vs) !! i = Some (vs !!! i)).
      { rewrite lookup_app_r; first lia.
        rewrite lookup_drop list_lookup_lookup_total_lt; first lia.
        repeat f_equal. lia.
      }
      iDestruct (chunk_model_lookup_acc i with "Hmodel") as "(H↦ & Hmodel)"; [lia | done | lia |].
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
    iIntros "%Hsz %Φ (HΨ & Hmodel & Hfn) HΦ".
    match goal with |- context [big_opL bi_sep ?Ξ' _] => set Ξ := Ξ' end.
    pose (Ψ' i vs_left ws := (
      Ψ i vs_left ws ∗
      [∗ list] j ↦ v ∈ drop i vs, Ξ (i + j) v
    )%I).
    wp_apply (chunk_applyi_spec Ψ' with "[HΨ $Hmodel Hfn]"); [done | | iSteps].
    iFrame. iIntros "!> %i %v %ws (%Hi & %Hlookup) (HΨ & HΞ)".
    erewrite drop_S; last done.
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
    iIntros "%Hsz %Φ (Hmodel & #Hfn) HΦ".
    pose (Ψ' i vs_left ws := (
      [∗ list] j ↦ w ∈ ws, Ψ j w
    )%I).
    wp_apply (chunk_applyi_spec Ψ' with "[$Hmodel]"); [done | | iSteps].
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
    iIntros "%Hsz %Φ (Hmodel & Hfn) HΦ".
    pose (Ψ' i vs_left ws := (
      [∗ list] j ↦ w ∈ ws, Ψ j w
    )%I).
    wp_apply (chunk_applyi_spec' Ψ' with "[Hmodel Hfn]"); [done | | iSteps].
    rewrite /Ψ'. iSteps.
    iApply (big_sepL_impl with "Hfn"). iSteps.
    rewrite big_sepL_snoc. iSteps.
  Qed.

  Proof.
    iIntros "%Φ (HΨ & (%l & -> & #Hhdr & Hmodel) & Hfn) HΦ".
    wp_rec. rewrite /array_data /array_size. wp_load.
    rewrite !location_add_0.
    wp_smart_apply (chunk_applyi_spec Ψ with "[$HΨ $Hmodel $Hfn]") as (ws) "(-> & Hmodel & HΨ)"; first lia.
    iSteps. rewrite Nat2Z.id !location_add_0. iSteps.
  Qed.
  Proof.
    iIntros "%Φ (HΨ & (%l & -> & #Hhdr & Hmodel) & Hfn) HΦ".
    wp_rec. rewrite /array_data /array_size. wp_load.
    rewrite !location_add_0.
    wp_smart_apply (chunk_applyi_spec' Ψ with "[$HΨ $Hmodel $Hfn]") as (ws) "(-> & Hmodel & HΨ)"; first lia.
    iSteps. rewrite Nat2Z.id !location_add_0. iSteps.
  Qed.
  Proof.
    iIntros "%Φ ((%l & -> & #Hhdr & Hmodel) & Hfn) HΦ".
    wp_rec. rewrite /array_data /array_size. wp_load.
    rewrite !location_add_0.
    wp_smart_apply (chunk_applyi_spec_disentangled Ψ with "[$Hmodel $Hfn]") as (ws) "(-> & Hmodel & HΨ)"; first lia.
    iSteps. rewrite !location_add_0. iSteps.
  Qed.
  Proof.
    iIntros "%Φ ((%l & -> & #Hhdr & Hmodel) & Hfn) HΦ".
    wp_rec. rewrite /array_data /array_size. wp_load.
    rewrite !location_add_0.
    wp_smart_apply (chunk_applyi_spec_disentangled' Ψ with "[$Hmodel $Hfn]") as (ws) "(-> & Hmodel & HΨ)"; first lia.
    iSteps. rewrite !location_add_0. iSteps.
  Qed.

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

  Lemma array_initi_spec Ψ sz fn :
    (0 ≤ sz)%Z →
    {{{
      ▷ Ψ 0 [] ∗
      □ (
        ∀ i vs,
        ⌜i < Z.to_nat sz ∧ i = length vs⌝ -∗
        Ψ i vs -∗
        WP fn #i {{ v, ▷
          Ψ (S i) (vs ++ [v])
        }}
      )
    }}}
      array_initi #sz fn
    {{{ t vs,
      RET t;
      ⌜length vs = Z.to_nat sz⌝ ∗
      array_model t (DfracOwn 1) vs ∗
      Ψ (Z.to_nat sz) vs
    }}}.
  Proof.
    iIntros "%Hsz %Φ (HΨ & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply assume_spec' as "_".
    wp_smart_apply (chunk_make_spec with "[//]") as "%l (Hmodel & _)".
    wp_pures.
    rewrite Z.add_1_l Z2Nat.inj_succ //.
    iDestruct (chunk_model_cons with "Hmodel") as "(Hhdr & Hmodel)".
    iMod (pointsto_persist with "Hhdr") as "#Hhdr".
    pose Ψ' i (_ : list val) vs := (
      Ψ i vs
    )%I.
    wp_smart_apply (chunk_applyi_spec Ψ' with "[$Hmodel $HΨ]"); rewrite ?replicate_length; first lia.
    { iSteps. iPureIntro.
      erewrite <- (replicate_length (Z.to_nat sz)). eapply lookup_lt_Some. done.
    }
    iIntros "%vs (%Hvs & Hmodel & HΨ)".
    wp_pures.
    iApply ("HΦ" $! #l vs). iFrame. iSteps.
    rewrite !location_add_0 -Hvs Z2Nat.id //. iSteps.
  Qed.
  Lemma array_initi_spec' Ψ sz fn :
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
      array_initi #sz fn
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
    wp_apply (array_initi_spec Ψ' with "[$HΨ Hfn]"); [done | | iSteps].
    rewrite Nat.sub_0_r. iFrame. iIntros "!> %i %vs (%Hi1 & %Hi2) (HΨ & HΞ)".
    destruct (Nat.lt_exists_pred 0 (Z.to_nat sz - i)) as (k & Hk & _); first lia. rewrite Hk.
    rewrite -cons_seq. iDestruct "HΞ" as "(Hfn & HΞ)".
    wp_apply (wp_wand with "(Hfn [//] HΨ)"). iSteps.
    rewrite Nat.sub_succ_r Hk //.
  Qed.
  Lemma array_initi_spec_disentangled Ψ sz fn :
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
      array_initi #sz fn
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
    wp_apply (array_initi_spec Ψ'); [done | | iSteps].
    rewrite /Ψ'. iSteps.
    rewrite big_sepL_snoc. iSteps.
  Qed.
  Lemma array_initi_spec_disentangled' Ψ sz fn :
    (0 ≤ sz)%Z →
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
    wp_apply (array_initi_spec' Ψ' with "[Hfn]"); [done | | iSteps].
    rewrite /Ψ'. iSteps.
    iApply (big_sepL_impl with "Hfn"). iSteps.
    rewrite big_sepL_snoc. iSteps.
  Qed.

  Lemma array_init_spec Ψ sz fn :
    (0 ≤ sz)%Z →
    {{{
      ▷ Ψ 0 [] ∗
      □ (
        ∀ i vs,
        ⌜i < Z.to_nat sz ∧ i = length vs⌝ -∗
        Ψ i vs -∗
        WP fn () {{ v, ▷
          Ψ (S i) (vs ++ [v])
        }}
      )
    }}}
      array_init #sz fn
    {{{ t vs,
      RET t;
      ⌜length vs = Z.to_nat sz⌝ ∗
      array_model t (DfracOwn 1) vs ∗
      Ψ (Z.to_nat sz) vs
    }}}.
  Proof.
    iIntros "%Hsz %Φ (HΨ & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (array_initi_spec Ψ with "[$HΨ] HΦ"); first done.
    iSteps.
  Qed.
  Lemma array_init_spec' Ψ sz fn :
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
      array_init #sz fn
    {{{ t vs,
      RET t;
      ⌜length vs = Z.to_nat sz⌝ ∗
      array_model t (DfracOwn 1) vs ∗
      Ψ (Z.to_nat sz) vs
    }}}.
  Proof.
    iIntros "%Hsz %Φ (HΨ & Hfn) HΦ".
    wp_rec.
    wp_smart_apply (array_initi_spec' Ψ with "[$HΨ Hfn] HΦ"); first done.
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.
  Lemma array_init_spec_disentangled Ψ sz fn :
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
      array_init #sz fn
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
    wp_smart_apply (array_initi_spec_disentangled Ψ with "[] HΦ"); first done.
    iSteps.
  Qed.
  Lemma array_init_spec_disentangled' Ψ sz fn :
    (0 ≤ sz)%Z →
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
      ⌜length vs = Z.to_nat sz⌝ ∗
      array_model t (DfracOwn 1) vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Hsz %Φ Hfn HΦ".
    wp_rec.
    wp_smart_apply (array_initi_spec_disentangled' Ψ with "[Hfn] HΦ"); first done.
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.

  Lemma array_apply_spec Ψ t vs fn :
    {{{
      ▷ Ψ 0 [] [] ∗
      array_model t (DfracOwn 1) vs ∗
      □ (
        ∀ i v ws,
        ⌜i = length ws ∧ vs !! i = Some v⌝ -∗
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
    iIntros "%Φ (HΨ & (%l & -> & #Hhdr & Hmodel) & Hfn) HΦ".
    wp_rec. rewrite /array_data /array_size. wp_load.
    rewrite !location_add_0.
    wp_smart_apply (chunk_apply_spec Ψ with "[$HΨ $Hmodel $Hfn]") as (ws) "(-> & Hmodel & HΨ)"; first lia.
    iSteps. rewrite Nat2Z.id !location_add_0. iSteps.
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
    iIntros "%Φ (HΨ & (%l & -> & #Hhdr & Hmodel) & Hfn) HΦ".
    wp_rec. rewrite /array_data /array_size. wp_load.
    rewrite !location_add_0.
    wp_smart_apply (chunk_apply_spec' Ψ with "[$HΨ $Hmodel $Hfn]") as (ws) "(-> & Hmodel & HΨ)"; first lia.
    iSteps. rewrite Nat2Z.id !location_add_0. iSteps.
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
    iIntros "%Φ ((%l & -> & #Hhdr & Hmodel) & Hfn) HΦ".
    wp_rec. rewrite /array_data /array_size. wp_load.
    rewrite !location_add_0.
    wp_smart_apply (chunk_apply_spec_disentangled Ψ with "[$Hmodel $Hfn]") as (ws) "(-> & Hmodel & HΨ)"; first lia.
    iSteps. rewrite !location_add_0. iSteps.
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
    iIntros "%Φ ((%l & -> & #Hhdr & Hmodel) & Hfn) HΦ".
    wp_rec. rewrite /array_data /array_size. wp_load.
    rewrite !location_add_0.
    wp_smart_apply (chunk_apply_spec_disentangled' Ψ with "[$Hmodel $Hfn]") as (ws) "(-> & Hmodel & HΨ)"; first lia.
    iSteps. rewrite !location_add_0. iSteps.
  Qed.

  Lemma array_blit_spec_slice_fit t1 sz1 i1 (i1_ : Z) dq1 vs1 t2 sz2 i2 (i2_ : Z) vs2 (n : Z) :
    i1_ = Z.of_nat i1 →
    i2_ = Z.of_nat i2 →
    n = length vs1 →
    length vs1 = length vs2 →
    {{{
      array_slice t1 sz1 i1 dq1 vs1 ∗
      array_slice t2 sz2 i2 (DfracOwn 1) vs2
    }}}
      array_blit t1 #i1_ t2 #i2_ #n
    {{{
      RET ();
      array_slice t1 sz1 i1 dq1 vs1 ∗
      array_slice t2 sz2 i2 (DfracOwn 1) vs1
    }}}.
  Proof.
    iIntros (-> -> -> ?) "%Φ (Hslice1 & Hslice2) HΦ".
    wp_rec. rewrite /array_data.
    wp_smart_apply (array_size_spec_slice with "Hslice1") as "Hslice1".
    wp_smart_apply (array_size_spec_slice with "Hslice2") as "Hslice2".
    repeat (wp_smart_apply assume_spec' as "_").
    iDestruct "Hslice1" as "(%l1 & -> & #Hhdr1 & Hmodel1)".
    iDestruct "Hslice2" as "(%l2 & -> & #Hhdr2 & Hmodel2)".
    wp_smart_apply (chunk_copy_spec with "[$Hmodel1 $Hmodel2]"); [lia.. |].
    iSteps.
  Qed.
  Lemma array_blit_spec_slice t1 sz1 i1 (j1 : Z) dq1 vs1 t2 sz2 i2 (j2 : Z) vs2 (n : Z) :
    (i1 ≤ j1)%Z →
    (i2 ≤ j2)%Z →
    (0 ≤ n)%Z →
    (j1 + n ≤ i1 + length vs1)%Z →
    (j2 + n ≤ i2 + length vs2)%Z →
    {{{
      array_slice t1 sz1 i1 dq1 vs1 ∗
      array_slice t2 sz2 i2 (DfracOwn 1) vs2
    }}}
      array_blit t1 #j1 t2 #j2 #n
    {{{
      RET ();
      let j1 := Z.to_nat j1 in
      let j2 := Z.to_nat j2 in
      let n := Z.to_nat n in
      array_slice t1 sz1 i1 dq1 vs1 ∗
      array_slice t2 sz2 i2 (DfracOwn 1) (
        take (j2 - i2) vs2 ++
        take n (drop (j1 - i1) vs1) ++
        drop (j2 - i2 + n) vs2
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
    rewrite !take_length !drop_length !Nat.min_l; [lia.. |].
    wp_apply (array_blit_spec_slice_fit with "[$Hslice12 $Hslice22]") as "(Hslice12 & Hslice22)"; try lia.
    { rewrite take_length drop_length. lia. }
    { rewrite !take_length !drop_length. lia. }
    iApply "HΦ".
    iDestruct (array_slice_app3_1 with "Hslice11 Hslice12 Hslice13") as "$"; [rewrite !take_length ?drop_length; lia.. |].
    iDestruct (array_slice_app3_1 with "Hslice21 Hslice22 Hslice23") as "Hslice2"; [rewrite !take_length ?drop_length; lia.. |].
    rewrite -!Nat.le_add_sub //; lia.
  Qed.
  Lemma array_blit_spec t1 (i1 : Z) dq1 vs1 t2 (i2 : Z) vs2 (n : Z) :
    (0 ≤ i1)%Z →
    (0 ≤ i2)%Z →
    (0 ≤ n)%Z →
    (i1 + n ≤ length vs1)%Z →
    (i2 + n ≤ length vs2)%Z →
    {{{
      array_model t1 dq1 vs1 ∗
      array_model t2 (DfracOwn 1) vs2
    }}}
      array_blit t1 #i1 t2 #i2 #n
    {{{
      RET ();
      let i1 := Z.to_nat i1 in
      let i2 := Z.to_nat i2 in
      let n := Z.to_nat n in
      array_model t1 dq1 vs1 ∗
      array_model t2 (DfracOwn 1) (
        take i2 vs2 ++
        take n (drop i1 vs1) ++
        drop (i2 + n) vs2
      )
    }}}.
  Proof.
    iIntros "% % % % % %Φ (Hmodel1 & Hmodel2) HΦ".
    iDestruct (array_model_slice with "Hmodel1") as "Hslice1".
    iDestruct (array_model_slice with "Hmodel2") as "Hslice2".
    wp_apply (array_blit_spec_slice with "[$Hslice1 $Hslice2]") as "(Hslice1 & Hslice2)"; [lia.. |].
    rewrite !Nat.sub_0_r.
    iApply "HΦ".
    iDestruct (array_slice_model with "Hslice1") as "$"; first done.
    iDestruct (array_slice_model with "Hslice2") as "$".
    rewrite !app_length !take_length !drop_length. lia.
  Qed.

  Lemma array_copy_spec_slice_fit t1 dq1 vs1 t2 sz2 i2 (i2_ : Z) vs2 :
    i2_ = Z.of_nat i2 →
    length vs1 = length vs2 →
    {{{
      array_model t1 dq1 vs1 ∗
      array_slice t2 sz2 i2 (DfracOwn 1) vs2
    }}}
      array_copy t1 t2 #i2_
    {{{
      RET ();
      array_model t1 dq1 vs1 ∗
      array_slice t2 sz2 i2 (DfracOwn 1) vs1
    }}}.
  Proof.
    iIntros (-> ?) "%Φ (Hmodel1 & Hslice2) HΦ".
    wp_rec.
    wp_smart_apply (array_size_spec with "Hmodel1") as "Hmodel1".
    wp_apply (array_blit_spec_slice_fit with "[$Hmodel1 $Hslice2]"); [done.. |].
    iSteps.
  Qed.
  Lemma array_copy_spec_slice t1 dq1 vs1 t2 sz2 i2 (j2 : Z) vs2 :
    (i2 ≤ j2)%Z →
    (j2 + length vs1 ≤ i2 + length vs2)%Z →
    {{{
      array_model t1 dq1 vs1 ∗
      array_slice t2 sz2 i2 (DfracOwn 1) vs2
    }}}
      array_copy t1 t2 #j2
    {{{
      RET ();
      array_model t1 dq1 vs1 ∗
      array_slice t2 sz2 i2 (DfracOwn 1) (
        take (Z.to_nat j2 - i2) vs2 ++
        vs1 ++
        drop (Z.to_nat j2 - i2 + length vs1) vs2
      )
    }}}.
  Proof.
    iIntros "% % %Φ (Hmodel1 & Hslice2) HΦ".
    wp_rec.
    wp_smart_apply (array_size_spec with "Hmodel1") as "Hmodel1".
    wp_apply (array_blit_spec_slice with "[$Hmodel1 $Hslice2]"); [lia.. |].
    rewrite Nat2Z.id firstn_all /=. iSteps.
  Qed.
  Lemma array_copy_spec t1 dq1 vs1 t2 (i2 : Z) vs2 :
    (0 ≤ i2)%Z →
    (i2 + length vs1 ≤ length vs2)%Z →
    {{{
      array_model t1 dq1 vs1 ∗
      array_model t2 (DfracOwn 1) vs2
    }}}
      array_copy t1 t2 #i2
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
    wp_apply (array_blit_spec with "[$Hmodel1 $Hmodel2]"); [lia.. |].
    rewrite Nat2Z.id firstn_all /=. iSteps.
  Qed.

  Lemma array_grow_spec t dq vs sz' v' :
    (length vs ≤ sz')%Z →
    {{{
      array_model t dq vs
    }}}
      array_grow t #sz' v'
    {{{ t',
      RET t';
      array_model t' (DfracOwn 1) (vs ++ replicate (Z.to_nat sz' - length vs) v')
    }}}.
  Proof.
    iIntros "%Hsz' %Φ Hmodel HΦ".
    wp_rec.
    wp_smart_apply (array_make_spec with "[//]") as "%t' Hmodel'"; first lia.
    wp_smart_apply (array_copy_spec with "[$Hmodel $Hmodel']"); first done.
    { rewrite replicate_length. lia. }
    rewrite drop_replicate. iSteps.
  Qed.

  Lemma array_sub_spec_slice_fit t sz dq vs i (i_ n : Z) :
    i_ = Z.of_nat i →
    n = length vs →
    {{{
      array_slice t sz i dq vs
    }}}
      array_sub t #i_ #n
    {{{ t',
      RET t';
      array_slice t sz i dq vs ∗
      array_model t' (DfracOwn 1) (take (Z.to_nat n) vs)
    }}}.
  Proof.
    iIntros (-> ->) "%Φ (%l & -> & #Hhdr & Hmodel) HΦ".
    wp_rec. rewrite /array_size /array_data. wp_load.
    repeat (wp_smart_apply assume_spec' as "_").
    wp_smart_apply (array_make_spec with "[//]") as "%t' (%l' & -> & #Hhdr' & Hmodel')"; first lia.
    iEval (rewrite location_add_0) in "Hmodel'".
    wp_smart_apply (chunk_copy_spec with "[$Hmodel $Hmodel']") as "(Hmodel & Hmodel')"; first lia.
    { rewrite replicate_length //. }
    wp_pures.
    iApply "HΦ". iSplitL "Hmodel"; first iSteps. iExists l'.
    rewrite replicate_length take_length Nat2Z.id Nat.min_id !location_add_0 firstn_all. iSteps.
  Qed.
  Lemma array_sub_spec_slice t sz dq vs i (j n : Z) :
    (i ≤ j)%Z →
    (0 ≤ n)%Z →
    (j + n ≤ i + length vs)%Z →
    {{{
      array_slice t sz i dq vs
    }}}
      array_sub t #j #n
    {{{ t',
      RET t';
      array_slice t sz i dq vs ∗
      array_model t' (DfracOwn 1) (take (Z.to_nat n) (drop (Z.to_nat j - Z.to_nat i) vs))
    }}}.
  Proof.
    iIntros "% % % %Φ Hslice HΦ".
    Z_to_nat j. Z_to_nat n. rewrite !Nat2Z.id.
    rewrite (Nat.le_add_sub i j); first lia. set k := j - i.
    rewrite -{1 2}(take_drop k vs) -(take_drop n (drop k vs)).
    rewrite !drop_drop.
    iDestruct (array_slice_app3_2 with "Hslice") as "(Hslice1 & Hslice2 & Hslice3)"; first done.
    rewrite !take_length !drop_length !Nat.min_l; [lia.. |].
    wp_apply (array_sub_spec_slice_fit with "Hslice2") as "%t' (Hslice2 & Hmodel')"; try lia.
    { rewrite take_length drop_length. lia. }
    iApply "HΦ".
    iDestruct (array_slice_app3_1 with "Hslice1 Hslice2 Hslice3") as "$"; [rewrite !take_length ?drop_length; lia.. |].
    rewrite Nat2Z.id take_take Nat.min_id -Nat.le_add_sub //. lia.
  Qed.
  Lemma array_sub_spec t dq vs (i n : Z) :
    (0 ≤ i)%Z →
    (0 ≤ n)%Z →
    (i + n ≤ length vs)%Z →
    {{{
      array_model t dq vs
    }}}
      array_sub t #i #n
    {{{ t',
      RET t';
      array_model t dq vs ∗
      array_model t' (DfracOwn 1) (take (Z.to_nat n) (drop (Z.to_nat i) vs))
    }}}.
  Proof.
    iIntros "% % % %Φ Hmodel HΦ".
    wp_apply (array_sub_spec_slice with "Hmodel"); [done.. |].
    rewrite Nat.sub_0_r. iSteps.
  Qed.

  Lemma array_shrink_spec t dq vs (n : Z) :
    (0 ≤ n ≤ length vs)%Z →
    {{{
      array_model t dq vs
    }}}
      array_shrink t #n
    {{{ t',
      RET t';
      array_model t dq vs ∗
      array_model t' (DfracOwn 1) (take (Z.to_nat n) vs)
    }}}.
  Proof.
    iIntros "%Hn %Φ Hmodel HΦ".
    wp_rec.
    wp_smart_apply (array_sub_spec with "Hmodel"); [lia.. |].
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
    wp_apply (array_shrink_spec with "Hmodel") as "%t' (Hmodel & Hmodel')"; first lia.
    rewrite firstn_all2; first lia.
    iApply ("HΦ" with "[$Hmodel $Hmodel']").
  Qed.

  Lemma array_cget_spec_atomic t (i : Z) :
    <<<
      True
    | ∀∀ sz i_ dq v,
      ⌜i = Z.of_nat i_⌝ ∗
      array_cslice t sz i_ dq [v]
    >>>
      array_cget t #i
    <<<
      array_cslice t sz i_ dq [v]
    | RET v;
      £ 1
    >>>.
  Proof.
    iIntros "!> %Φ _ HΦ".
    wp_rec.
    awp_smart_apply (array_size_spec_atomic_cslice with "[//]").
    iApply (aacc_aupd_abort with "HΦ"); first done. iIntros "%sz %i_ %dq %v (-> & Hcslice)".
    iAaccIntro with "Hcslice"; first iSteps. iSteps as (l) "Hhdr HΦ H£". clear.
    awp_apply (chunk_cget_spec_atomic with "[//]").
    iApply (aacc_aupd_commit with "HΦ"); first done. iSteps as (i l dq v) "Hhdr Hcslice".
    rewrite /atomic_acc /=. iSteps.
  Qed.
  Lemma array_cget_spec t sz (i : Z) i_ dq v :
    i = Z.of_nat i_ →
    {{{
      array_cslice t sz i_ dq [v]
    }}}
      array_cget t #i
    {{{
      RET v;
      array_cslice t sz i_ dq [v]
    }}}.
  Proof.
    iIntros (->) "%Φ Hcslice HΦ".
    iApply wp_fupd.
    awp_apply (array_cget_spec_atomic with "[//]") without "HΦ".
    rewrite /atomic_acc /=. repeat iExists _.
    iApply fupd_mask_intro; first done. iIntros "Hclose".
    iSplitL "Hcslice"; first auto. iSplit; first iSteps.
    iIntros "Hcslice". iMod "Hclose" as "_". iIntros "!> H£ HΦ".
    iMod (lc_fupd_elim_later with "H£ HΦ") as "HΦ".
    iApply ("HΦ" with "Hcslice").
  Qed.

  Lemma array_cset_spec_atomic t (i : Z) v :
    <<<
      True
    | ∀∀ sz i_ w,
      ⌜i = Z.of_nat i_⌝ ∗
      array_cslice t sz i_ (DfracOwn 1) [w]
    >>>
      array_cset t #i v
    <<<
      array_cslice t sz i_ (DfracOwn 1) [v]
    | RET ();
      £ 1
    >>>.
  Proof.
    iIntros "!> %Φ _ HΦ".
    wp_rec.
    awp_smart_apply (array_size_spec_atomic_cslice with "[//]").
    iApply (aacc_aupd_abort with "HΦ"); first done. iIntros "%sz %i_ %w (-> & Hcslice)".
    iAaccIntro with "Hcslice"; first iSteps. iSteps as (l) "Hhdr HΦ H£". clear.
    awp_apply (chunk_cset_spec_atomic with "[//]").
    iApply (aacc_aupd_commit with "HΦ"); first done. iSteps as (i l w) "Hhdr Hcslice".
    rewrite /atomic_acc /=. iSteps.
  Qed.
  Lemma array_cset_spec t sz (i : Z) i_ w v :
    i = Z.of_nat i_ →
    {{{
      array_cslice t sz i_ (DfracOwn 1) [w]
    }}}
      array_cset t #i v
    {{{
      RET ();
      array_cslice t sz i_ (DfracOwn 1) [v]
    }}}.
  Proof.
    iIntros (->) "%Φ Hcslice HΦ".
    iApply wp_fupd.
    awp_apply (array_cset_spec_atomic with "[//]") without "HΦ".
    rewrite /atomic_acc /=. repeat iExists _.
    iApply fupd_mask_intro; first done. iIntros "Hclose".
    iSplitL "Hcslice"; first auto. iSplit; first iSteps.
    iIntros "Hcslice". iMod "Hclose" as "_". iIntros "!> H£ HΦ".
    iMod (lc_fupd_elim_later with "H£ HΦ") as "HΦ".
    iApply ("HΦ" with "Hcslice").
  Qed.

  Lemma array_cblit_spec t1 sz1 (i1 : Z) i1_ dq1 vs1 t2 sz2 (i2 : Z) i2_ vs2 (n : Z) :
    let n_ := Z.to_nat n in
    i1 = Z.of_nat i1_ →
    i2 = Z.of_nat i2_ →
    (0 ≤ n ≤ length vs1 ≤ length vs2)%Z →
    {{{
      array_cslice t1 sz1 i1_ dq1 vs1 ∗
      array_cslice t2 sz2 i2_ (DfracOwn 1) vs2
    }}}
      array_cblit t1 #i1 t2 #i2 #n
    {{{
      RET ();
      array_cslice t1 sz1 i1_ dq1 vs1 ∗
      array_cslice t2 sz2 i2_ (DfracOwn 1) (take n_ vs1 ++ drop n_ vs2)
    }}}.
  Proof.
    iIntros (n_ -> -> Hn) "%Φ ((%l1 & -> & #Hhdr1 & Hcslice1) & (%l2 & -> & #Hhdr2 & Hcslice2)) HΦ".
    wp_rec. rewrite /array_size /array_data. do 2 wp_load.
    wp_smart_apply (chunk_cblit_spec with "[$Hcslice1 $Hcslice2]"); [done.. |].
    iSteps.
  Qed.

  Lemma array_ccopy_spec t1 sz1 (i1 : Z) i1_ dq1 vs1 t2 sz2 (i2 : Z) i2_ vs2 :
    i1 = Z.of_nat i1_ →
    i2 = Z.of_nat i2_ →
    length vs1 = sz1 →
    sz1 ≤ length vs2 →
    {{{
      array_cslice t1 sz1 i1_ dq1 vs1 ∗
      array_cslice t2 sz2 i2_ (DfracOwn 1) vs2
    }}}
      array_ccopy t1 #i1 t2 #i2
    {{{
      RET ();
      array_cslice t1 sz1 i1_ dq1 vs1 ∗
      array_cslice t2 sz2 i2_ (DfracOwn 1) (vs1 ++ drop (length vs1) vs2)
    }}}.
  Proof.
    iIntros (-> -> Hvs1 Hsz1) "%Φ (Hcslice1 & Hcslice2) HΦ".
    wp_rec.
    wp_smart_apply (array_size_spec_cslice with "Hcslice1") as "Hcslice1".
    wp_apply (array_cblit_spec with "[$Hcslice1 $Hcslice2]"); [lia.. |].
    rewrite Nat2Z.id -Hvs1 firstn_all. iSteps.
  Qed.

  Definition itype_array τ `{!iType _ τ} (sz : nat) t : iProp Σ :=
    ∃ l,
    ⌜t = #l⌝ ∗
    l.[size] ↦□ #sz ∗
    itype_chunk τ sz l.[data].
  #[global] Instance itype_array_itype τ `{!iType _ τ} sz :
    iType _ (itype_array τ sz).
  Proof.
    split. apply _.
  Qed.

  Lemma array_create_type τ `{!iType _ τ} :
    {{{ True }}}
      array_create ()
    {{{ t,
      RET t;
      itype_array τ 0 t
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_rec.
    iApply wp_fupd.
    wp_apply (chunk_make_spec with "[//]") as "%l (Hl & _)".
    iDestruct (chunk_model_cons_2 with "Hl") as "(Hhdr & _)".
    rewrite -{1}(location_add_0 l). iMod (pointsto_persist with "Hhdr") as "#Hhdr".
    iApply "HΦ". iExists l. repeat iSplitR; [iSteps.. |].
    iApply itype_chunk_0.
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
    wp_smart_apply assume_spec' as "%Hsz".
    Z_to_nat sz. rewrite Nat2Z.id.
    wp_smart_apply (chunk_make_spec with "[//]") as "%l (Hl & _)".
    rewrite Z.add_1_l Z2Nat.inj_succ; first lia. rewrite Nat2Z.id.
    iDestruct (chunk_model_cons_2 with "Hl") as "(Hhdr & Hdata)".
    rewrite -{1}(location_add_0 l).
    wp_store. wp_pures.
    iMod (pointsto_persist with "Hhdr") as "#Hhdr".
    iApply "HΦ". iStep. iExists l. repeat iSplitR; [iSteps.. |].
    iApply inv_alloc. iExists _. iFrame. rewrite replicate_length. iSteps.
    iApply big_sepL_intro. iIntros "%k %_v" ((-> & Hk)%lookup_replicate). iSteps.
  Qed.

  Lemma array_initi_type τ `{!iType _ τ} sz fn :
    {{{
      (itype_nat --> τ)%T fn
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
    wp_smart_apply assume_spec' as "%Hsz".
    wp_smart_apply (chunk_make_spec with "[//]") as "%l (Hmodel & _)".
    rewrite Z.add_1_l Z2Nat.inj_succ //.
    iDestruct (chunk_model_cons with "Hmodel") as "(Hhdr & Hmodel)".
    iMod (pointsto_persist with "Hhdr") as "#Hhdr".
    wp_smart_apply (chunk_applyi_spec_disentangled (λ _, τ) with "[$Hmodel]"); rewrite ?replicate_length; [lia | iSteps |].
    iIntros "%vs (%Hvs & Hmodel & #Hτ)".
    wp_pures.
    iApply "HΦ". iStep. iExists l. repeat iSplitR; try iSteps.
    rewrite location_add_0 Z2Nat.id //.
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
    wp_smart_apply (array_initi_type with "[] HΦ").
    iSteps.
  Qed.

  Lemma array_size_type τ `{!iType _ τ} t sz :
    {{{
      itype_array τ sz t
    }}}
      array_size t
    {{{
      RET #sz; True
    }}}.
  Proof.
    iSteps.
  Qed.

  #[local] Lemma array_data_type τ `{!iType _ τ} t sz :
    {{{
      itype_array τ sz t
    }}}
      array_data t
    {{{ l,
      RET #l;
      itype_chunk τ sz l
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
    iIntros "%Hi %Φ #Ht HΦ".
    wp_rec.
    wp_smart_apply (array_data_type with "Ht") as "%data #Hdata".
    wp_smart_apply (chunk_get_type with "Hdata"); first done.
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
      RET (); True
    }}}.
  Proof.
    iIntros "%Hi %Φ (#Ht & #Hv) HΦ".
    wp_rec.
    wp_smart_apply (array_data_type with "Ht") as "%data #Hdata".
    wp_smart_apply (chunk_set_type with "[$Hdata $Hv]"); first done.
    iSteps.
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
    iIntros "%Φ (#Ht & #Hv) HΦ".
    wp_rec.
    wp_smart_apply assume_spec' as "%Hi".
    wp_smart_apply (array_size_type with "Ht") as "_".
    wp_smart_apply assume_spec' as "%Hi'".
    wp_smart_apply (array_unsafe_set_type with "[$Ht $Hv]"); first lia.
    iSteps.
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
    iIntros "%Φ (#Ht & Hacc & Hfn) HΦ".
    wp_rec.
    wp_smart_apply (array_size_type with "Ht") as "_".
    wp_apply (array_data_type with "Ht") as (l) "#Hl".
    wp_apply (chunk_foldli_type with "[$Hl Hacc $Hfn //] HΦ"); first done.
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
    iIntros "%Φ (#Ht & Hacc & Hfn) HΦ".
    wp_rec.
    wp_smart_apply (array_size_type with "Ht") as "_".
    wp_apply (array_data_type with "Ht") as (l) "#Hl".
    wp_apply (chunk_foldl_type with "[$Hl Hacc $Hfn //] HΦ"); first done.
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
    iIntros "%Φ (#Ht & Hfn & Hacc) HΦ".
    wp_rec.
    wp_smart_apply (array_size_type with "Ht") as "_".
    wp_apply (array_data_type with "Ht") as (l) "#Hl".
    wp_apply (chunk_foldri_type with "[$Hl $Hfn Hacc //] HΦ"); first done.
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
    iIntros "%Φ (#Ht & Hfn & Hacc) HΦ".
    wp_rec.
    wp_smart_apply (array_size_type with "Ht") as "_".
    wp_apply (array_data_type with "Ht") as (l) "#Hl".
    wp_apply (chunk_foldr_type with "[$Hl $Hfn Hacc //] HΦ"); first done.
  Qed.

  Lemma array_iteri_type τ `{!iType _ τ} t sz fn :
    {{{
      itype_array τ sz t ∗
      (itype_nat_upto sz --> τ --> itype_unit)%T fn
    }}}
      array_iteri t fn
    {{{
      RET (); True
    }}}.
  Proof.
    iIntros "%Φ (#Ht & Hfn) HΦ".
    wp_rec.
    wp_smart_apply (array_size_type with "Ht") as "_".
    wp_apply (array_data_type with "Ht") as (l) "#Hl".
    wp_apply (chunk_iteri_type with "[$Hl $Hfn] HΦ"); first done.
  Qed.

  Lemma array_iter_type τ `{!iType _ τ} t sz fn :
    {{{
      itype_array τ sz t ∗
      (τ --> itype_unit)%T fn
    }}}
      array_iter t fn
    {{{
      RET (); True
    }}}.
  Proof.
    iIntros "%Φ (#Ht & Hfn) HΦ".
    wp_rec.
    wp_smart_apply (array_size_type with "Ht") as "_".
    wp_apply (array_data_type with "Ht") as (l) "#Hl".
    wp_apply (chunk_iter_type with "[$Hl $Hfn] HΦ"); first done.
  Qed.

  Lemma array_applyi_type τ `{!iType _ τ} t sz fn :
    {{{
      itype_array τ sz t ∗
      (itype_nat_upto sz --> τ --> τ)%T fn
    }}}
      array_applyi t fn
    {{{
      RET (); True
    }}}.
  Proof.
    iIntros "%Φ (#Ht & Hfn) HΦ".
    wp_rec.
    wp_smart_apply (array_size_type with "Ht") as "_".
    wp_apply (array_data_type with "Ht") as (l) "#Hl".
    wp_apply (chunk_applyi_type with "[$Hl $Hfn] HΦ"); first done.
  Qed.

  Lemma array_apply_type τ `{!iType _ τ} t sz fn :
    {{{
      itype_array τ sz t ∗
      (τ --> τ)%T fn
    }}}
      array_apply t fn
    {{{
      RET (); True
    }}}.
  Proof.
    iIntros "%Φ (#Ht & Hfn) HΦ".
    wp_rec.
    wp_smart_apply (array_size_type with "Ht") as "_".
    wp_apply (array_data_type with "Ht") as (l) "#Hl".
    wp_apply (chunk_apply_type with "[$Hl $Hfn] HΦ"); first done.
  Qed.

  Lemma array_blit_type τ `{!iType _ τ} t1 sz1 (i1 : Z) t2 sz2 (i2 n : Z) :
    {{{
      itype_array τ sz1 t1 ∗
      itype_array τ sz2 t2
    }}}
      array_blit t1 #i1 t2 #i2 #n
    {{{
      RET ();
      ⌜0 ≤ i1 ∧ 0 ≤ i2 ∧ 0 ≤ n ∧ i1 + n ≤ sz1 ∧ i2 + n ≤ sz2⌝%Z
    }}}.
  Proof.
    iIntros "%Φ (#Ht1 & #Ht2) HΦ".
    wp_rec.
    wp_smart_apply (array_size_type with "Ht1") as "_".
    wp_smart_apply (array_size_type with "Ht2") as "_".
    repeat (wp_smart_apply assume_spec' as "%").
    wp_smart_apply (array_data_type with "Ht2") as "%data2 Hdata2".
    wp_smart_apply (array_data_type with "Ht1") as "%data1 Hdata1".
    iDestruct (itype_chunk_shift i1 with "Hdata1") as "Hdata1"; first lia.
    iDestruct (itype_chunk_shift i2 with "Hdata2") as "Hdata2"; first lia.
    iDestruct (itype_chunk_le (Z.to_nat n) with "Hdata1") as "Hdata1"; first lia.
    wp_smart_apply (chunk_copy_type with "[$Hdata1 $Hdata2]"); [lia.. |].
    iSteps.
  Qed.

  Lemma array_copy_type τ `{!iType _ τ} t1 sz1 t2 sz2 (i2 : Z) :
    {{{
      itype_array τ sz1 t1 ∗
      itype_array τ sz2 t2
    }}}
      array_copy t1 t2 #i2
    {{{
      RET ();
      ⌜0 ≤ i2 ∧ i2 + sz1 ≤ sz2⌝%Z
    }}}.
  Proof.
    iIntros "%Φ (#Ht1 & #Ht2) HΦ".
    wp_rec.
    wp_smart_apply (array_size_type with "Ht1") as "_".
    wp_apply array_blit_type; first iFrame "#∗".
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
    iIntros "%Φ (#Ht & #Hv') HΦ".
    wp_rec.
    wp_smart_apply (array_make_type with "Hv'") as "%t' (_ & #Ht')".
    wp_smart_apply (array_copy_type with "[]") as "(_ & %Hsz')"; first iFrame "#∗".
    wp_pures.
    iApply ("HΦ" with "[$Ht']").
    iSteps.
  Qed.

  Lemma array_sub_type τ `{!iType _ τ} t sz (i n : Z) :
    {{{
      itype_array τ sz t
    }}}
      array_sub t #i #n
    {{{ t',
      RET t';
      ⌜0 ≤ i ∧ 0 ≤ n ∧ i + n ≤ sz⌝%Z ∗
      itype_array τ (Z.to_nat n) t'
    }}}.
  Proof.
    iIntros "%Φ #Ht HΦ".
    wp_rec. rewrite {2}/array_data.
    wp_smart_apply (array_size_type with "Ht") as "_".
    repeat (wp_smart_apply assume_spec' as "%").
    wp_smart_apply (array_make_spec with "[//]") as "%t' (%l' & -> & #Hhdr' & Hdata')"; first done.
    wp_smart_apply (array_data_type with "Ht") as "%data Hdata".
    iDestruct (itype_chunk_shift i with "Hdata") as "Hdata"; first lia.
    iDestruct (itype_chunk_le (Z.to_nat n) with "Hdata") as "Hdata"; first lia.
    iEval (rewrite location_add_0) in "Hdata'".
    wp_smart_apply (chunk_copy_type' with "[$Hdata $Hdata']"); first lia.
    { rewrite replicate_length //. }
    rewrite replicate_length. iSteps.
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
    iIntros "%Φ Ht HΦ".
    wp_rec.
    wp_smart_apply (array_sub_type with "Ht").
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
    iIntros "%Φ #Ht HΦ".
    wp_rec.
    wp_apply (array_size_type with "Ht") as "_".
    wp_smart_apply (array_shrink_type with "Ht").
    rewrite Nat2Z.id. iSteps.
  Qed.

  Lemma array_fill_slice_type τ `{!iType _ τ} t sz (i n : val) v :
    {{{
      itype_array τ sz t ∗
      itype_int i ∗
      itype_int n ∗
      τ v
    }}}
      array_fill_slice t i n v
    {{{
      RET (); True
    }}}.
  Proof.
    iIntros "%Φ (#Ht & (%i_ & ->) & (%n_ & ->) & #Hv) HΦ".
    wp_rec.
    wp_smart_apply (array_size_type with "Ht") as "_".
    repeat (wp_smart_apply assume_spec' as "%").
    wp_smart_apply (array_data_type with "Ht") as "%l Hl".
    iDestruct (itype_chunk_shift i_ with "Hl") as "Hl"; first lia.
    iDestruct (itype_chunk_le (Z.to_nat n_) with "Hl") as "Hl"; first lia.
    wp_smart_apply (chunk_fill_type with "[$Hl $Hv] HΦ"); first lia.
  Qed.

  Lemma array_fill_type τ `{!iType _ τ} t sz v :
    {{{
      itype_array τ sz t ∗
      τ v
    }}}
      array_fill t v
    {{{
      RET (); True
    }}}.
  Proof.
    iIntros "%Φ (#Ht & #Hv) HΦ".
    wp_rec.
    wp_smart_apply (array_size_type with "Ht") as "_".
    wp_apply (array_fill_slice_type with "[$Ht] HΦ"); first iSteps.
  Qed.

  Lemma array_cget_type τ `{!iType _ τ} t sz (i : Z) :
    0 < sz →
    (0 ≤ i)%Z →
    {{{
      itype_array τ sz t
    }}}
      array_cget t #i
    {{{ v,
      RET v;
      τ v
    }}}.
  Proof.
    iIntros "%Hsz %Hi %Φ #Ht HΦ".
    wp_rec.
    wp_smart_apply (array_size_type with "Ht") as "_".
    wp_smart_apply (array_data_type with "Ht") as "%data #Hdata".
    wp_smart_apply (chunk_cget_type with "Hdata HΦ"); lia.
  Qed.

  Lemma array_cset_type τ `{!iType _ τ} t sz (i : Z) v :
    0 < sz →
    (0 ≤ i)%Z →
    {{{
      itype_array τ sz t ∗
      τ v
    }}}
      array_cset t #i v
    {{{
      RET (); True
    }}}.
  Proof.
    iIntros "%Hsz %Hi %Φ (#Ht & #Hv) HΦ".
    wp_rec.
    wp_smart_apply (array_size_type with "Ht") as "_".
    wp_smart_apply (array_data_type with "Ht") as "%data #Hdata".
    wp_smart_apply (chunk_cset_type with "[$Hdata $Hv] HΦ"); lia.
  Qed.

  Lemma array_cblit_type τ `{!iType _ τ} t1 sz1 (i1 : Z) t2 sz2 (i2 : Z) (n : Z) :
    0 < sz1 →
    0 < sz2 →
    (0 ≤ i1)%Z →
    (0 ≤ i2)%Z →
    {{{
      itype_array τ sz1 t1 ∗
      itype_array τ sz2 t2
    }}}
      array_cblit t1 #i1 t2 #i2 #n
    {{{
      RET (); True
    }}}.
  Proof.
    iIntros "%Hsz1 %Hsz2 %Hi1 %Hi2 %Φ (#Ht1 & #Ht2) HΦ".
    wp_rec.
    wp_smart_apply (array_size_type with "Ht2") as "_".
    wp_apply (array_data_type with "Ht2") as (l2) "#Hl2".
    wp_smart_apply (array_size_type with "Ht1") as "_".
    wp_apply (array_data_type with "Ht1") as (l1) "#Hl1".
    wp_apply chunk_cblit_type; [naive_solver lia.. | iSteps |].
    iSteps.
  Qed.

  Lemma array_ccopy_type τ `{!iType _ τ} t1 sz1 (i1 : Z) t2 sz2 (i2 : Z) :
    0 < sz1 →
    0 < sz2 →
    (0 ≤ i1)%Z →
    (0 ≤ i2)%Z →
    {{{
      itype_array τ sz1 t1 ∗
      itype_array τ sz2 t2
    }}}
      array_ccopy t1 #i1 t2 #i2
    {{{
      RET (); True
    }}}.
  Proof.
    iIntros "%Hsz1 %Hsz2 %Hi1 %Hi2 %Φ (#Ht1 & #Ht2) HΦ".
    wp_rec.
    wp_smart_apply (array_size_type with "Ht1") as "_".
    wp_apply (array_cblit_type _ _ sz1 _ _ sz2); [done.. | iFrame "#∗" |].
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
