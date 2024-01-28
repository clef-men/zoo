From Coq Require Import
  ZifyNat.

From zebre Require Import
  prelude.
From zebre.common Require Import
  math.
From zebre.iris.bi Require Import
  big_op.
From zebre.language Require Import
  notations
  diaframe.
From zebre.std Require Export
  base.
From zebre.std Require Import
  for_upto.
From zebre Require Import
  options.

Implicit Types i j n : nat.
Implicit Types l : loc.
Implicit Types v t fn acc : val.
Implicit Types vs vs_left vs_right ws : list val.

Definition chunk_make : val :=
  λ: "sz" "v",
    if: #0 < "sz" then (
      Alloc "sz" "v"
    ) else (
      #(inhabitant : loc)
    ).

#[local] Definition chunk_foldli_aux : val :=
  rec: "chunk_foldli_aux" "t" "sz" "acc" "fn" "i" :=
    if: "sz" ≤ "i" then (
      "acc"
    ) else (
      "chunk_foldli_aux" "t" "sz" ("fn" "acc" "i" !("t" +ₗ "i")) "fn" (#1 + "i")
    ).
Definition chunk_foldli : val :=
  λ: "t" "sz" "acc" "fn",
    chunk_foldli_aux "t" "sz" "acc" "fn" #0.
Definition chunk_foldl : val :=
  λ: "t" "sz" "acc" "fn",
    chunk_foldli "t" "sz" "acc" (λ: "acc" <> "v", "fn" "acc" "v").

#[local] Definition chunk_foldri_aux : val :=
  rec: "chunk_foldri_aux" "t" "fn" "acc" "i" :=
    if: "i" ≤ #0 then (
      "acc"
    ) else (
      let: "i" := "i" - #1 in
      "chunk_foldri_aux" "t" "fn" ("fn" "i" !("t" +ₗ "i") "acc") "i"
    ).
Definition chunk_foldri : val :=
  λ: "t" "sz" "fn" "acc",
    chunk_foldri_aux "t" "fn" "acc" "sz".
Definition chunk_foldr : val :=
  λ: "t" "sz" "fn" "acc",
    chunk_foldri "t" "sz" (λ: <> "v" "acc", "fn" "v" "acc") "acc".

Definition chunk_iteri : val :=
  λ: "t" "sz" "fn",
    chunk_foldli "t" "sz" () (λ: <>, "fn").
Definition chunk_iter : val :=
  λ: "t" "sz" "fn",
    chunk_iteri "t" "sz" (λ: <>, "fn").

Definition chunk_applyi : val :=
  λ: "t" "sz" "fn",
    chunk_iteri "t" "sz" (λ: "i" "v", "t" +ₗ "i" <- "fn" "i" "v").
Definition chunk_apply : val :=
  λ: "t" "sz" "fn",
    chunk_applyi "t" "sz" (λ: <>, "fn").

Definition chunk_initi : val :=
  λ: "sz" "fn",
    let: "t" := chunk_make "sz" () in
    chunk_applyi "t" "sz" (λ: "i" <>, "fn" "i") ;;
    "t".
Definition chunk_init : val :=
  λ: "sz" "fn",
    chunk_initi "sz" (λ: <>, "fn" ()).

Definition chunk_mapi : val :=
  λ: "t" "sz" "fn",
    chunk_initi "sz" (λ: "i", "fn" "i" !("t" +ₗ "i")).
Definition chunk_map : val :=
  λ: "t" "sz" "fn",
    chunk_mapi "t" "sz" (λ: <>, "fn").

Definition chunk_copy : val :=
  λ: "t" "sz" "t'",
    chunk_iteri "t" "sz" (λ: "i" "v", "t'" +ₗ "i" <- "v").

Definition chunk_resize : val :=
  λ: "t" "sz" "sz'" "n" "v'",
    let: "t'" := chunk_make "sz'" "v'" in
    chunk_copy "t" "n" "t'" ;;
    "t'".
Definition chunk_grow : val :=
  λ: "t" "sz" "sz'" "v'",
    chunk_resize "t" "sz" "sz'" "sz" "v'".
Definition chunk_shrink : val :=
  λ: "t" "sz" "sz'",
    chunk_resize "t" "sz" "sz'" "sz'" (inhabitant : val).
Definition chunk_clone : val :=
  λ: "t" "sz",
    chunk_shrink "t" "sz" "sz".

Definition chunk_fill : val :=
  λ: "t" "sz" "v",
    for: "i" = #0 to "sz" begin
      "t" +ₗ "i" <- "v"
    end.

Definition chunk_cget : val :=
  λ: "t" "sz" "i",
    !("t" +ₗ "i" `rem` "sz").
Definition chunk_cset : val :=
  λ: "t" "sz" "i" "v",
    "t" +ₗ "i" `rem` "sz" <- "v".

Section zebre_G.
  Context `{zebre_G : !ZebreG Σ}.

  Section chunk_model.
    Definition chunk_model l dq vs : iProp Σ :=
      [∗ list] i ↦ v ∈ vs, (l +ₗ i) ↦{dq} v.

    #[global] Instance chunk_model_timeless l dq vs :
      Timeless (chunk_model l dq vs).
    Proof.
      apply _.
    Qed.
    #[global] Instance chunk_model_persistent l vs :
      Persistent (chunk_model l DfracDiscarded vs).
    Proof.
      apply _.
    Qed.

    #[global] Instance chunk_model_fractional l vs :
      Fractional (λ q, chunk_model l (DfracOwn q) vs).
    Proof.
      apply _.
    Qed.
    #[global] Instance chunk_model_as_fractional l q vs :
      AsFractional (chunk_model l (DfracOwn q) vs) (λ q, chunk_model l (DfracOwn q) vs) q.
    Proof.
      split; [done | apply _].
    Qed.

    Lemma chunk_model_nil l dq :
      ⊢ chunk_model l dq [].
    Proof.
      rewrite /chunk_model //.
    Qed.

    Lemma chunk_model_singleton l dq v :
      l ↦{dq} v ⊣⊢
      chunk_model l dq [v].
    Proof.
      setoid_rewrite big_sepL_singleton. rewrite loc_add_0 //.
    Qed.
    Lemma chunk_model_singleton_1 l dq v :
      l ↦{dq} v ⊢
      chunk_model l dq [v].
    Proof.
      rewrite chunk_model_singleton //.
    Qed.
    Lemma chunk_model_singleton_2 l dq v :
      chunk_model l dq [v] ⊢
      l ↦{dq} v.
    Proof.
      rewrite chunk_model_singleton //.
    Qed.

    Lemma chunk_model_app l dq vs1 vs2 :
      chunk_model l dq vs1 ∗
      chunk_model (l +ₗ length vs1) dq vs2 ⊣⊢
      chunk_model l dq (vs1 ++ vs2).
    Proof.
      setoid_rewrite big_sepL_app.
      setoid_rewrite Nat2Z.inj_add.
      setoid_rewrite <- loc_add_assoc. done.
    Qed.
    Lemma chunk_model_app_1 dq l1 vs1 l2 vs2 :
      l2 = l1 +ₗ length vs1 →
      chunk_model l1 dq vs1 -∗
      chunk_model l2 dq vs2 -∗
      chunk_model l1 dq (vs1 ++ vs2).
    Proof.
      rewrite -chunk_model_app. iSteps.
    Qed.
    Lemma chunk_model_app_2 {l dq vs} vs1 vs2 :
      vs = vs1 ++ vs2 →
      chunk_model l dq vs ⊢
        chunk_model l dq vs1 ∗
        chunk_model (l +ₗ length vs1) dq vs2.
    Proof.
      rewrite chunk_model_app. iSteps.
    Qed.

    Lemma chunk_model_app3 l dq vs1 vs2 vs3 :
      chunk_model l dq vs1 ∗
      chunk_model (l +ₗ length vs1) dq vs2 ∗
      chunk_model (l +ₗ (length vs1 + length vs2)%nat) dq vs3 ⊣⊢
      chunk_model l dq (vs1 ++ vs2 ++ vs3).
    Proof.
      rewrite -!chunk_model_app loc_add_assoc Nat2Z.inj_add //.
    Qed.
    Lemma chunk_model_app3_1 dq l1 vs1 l2 vs2 l3 vs3 :
      l2 = l1 +ₗ length vs1 →
      l3 = l1 +ₗ (length vs1 + length vs2)%nat →
      chunk_model l1 dq vs1 -∗
      chunk_model l2 dq vs2 -∗
      chunk_model l3 dq vs3 -∗
      chunk_model l1 dq (vs1 ++ vs2 ++ vs3).
    Proof.
      intros -> ->. rewrite -chunk_model_app3. iSteps.
    Qed.
    Lemma chunk_model_app3_2 {l dq vs} vs1 vs2 vs3 :
      vs = vs1 ++ vs2 ++ vs3 →
      chunk_model l dq vs ⊢
        chunk_model l dq vs1 ∗
        chunk_model (l +ₗ length vs1) dq vs2 ∗
        chunk_model (l +ₗ (length vs1 + length vs2)%nat) dq vs3.
    Proof.
      intros ->. rewrite chunk_model_app3 //.
    Qed.

    Lemma chunk_model_cons l dq v vs :
      l ↦{dq} v ∗
      chunk_model (l +ₗ 1) dq vs ⊣⊢
      chunk_model l dq (v :: vs).
    Proof.
      assert (v :: vs = [v] ++ vs) as -> by done.
      rewrite -chunk_model_app chunk_model_singleton //.
    Qed.
    Lemma chunk_model_cons_1 l dq v vs :
      l ↦{dq} v -∗
      chunk_model (l +ₗ 1) dq vs -∗
      chunk_model l dq (v :: vs).
    Proof.
      rewrite -chunk_model_cons. iSteps.
    Qed.
    Lemma chunk_model_cons_2 l dq v vs :
      chunk_model l dq (v :: vs) ⊢
        l ↦{dq} v ∗
        chunk_model (l +ₗ 1) dq vs.
    Proof.
      rewrite chunk_model_cons //.
    Qed.
    #[global] Instance chunk_model_cons_frame l dq v vs R Q :
      Frame false R (l ↦{dq} v ∗ chunk_model (l +ₗ 1) dq vs) Q →
      Frame false R (chunk_model l dq (v :: vs)) Q
    | 2.
    Proof.
      rewrite /Frame chunk_model_cons //.
    Qed.

    Lemma chunk_model_update {l dq vs} (i : Z) i_ v :
      (0 ≤ i)%Z →
      vs !! i_ = Some v →
      i_ = Z.to_nat i →
      chunk_model l dq vs ⊢
        (l +ₗ i) ↦{dq} v ∗
        ( ∀ w,
          (l +ₗ i) ↦{dq} w -∗
          chunk_model l dq (<[i_ := w]> vs)
        ).
    Proof.
      intros Hi Hlookup ->.
      Z_to_nat i. rewrite Nat2Z.id in Hlookup |- *.
      iApply big_sepL_insert_acc. done.
    Qed.
    Lemma chunk_model_lookup_acc {l dq vs} (i : Z) i_ v :
      (0 ≤ i)%Z →
      vs !! i_ = Some v →
      i_ = Z.to_nat i →
      chunk_model l dq vs ⊢
        (l +ₗ i) ↦{dq} v ∗
        ( (l +ₗ i) ↦{dq} v -∗
          chunk_model l dq vs
        ).
    Proof.
      intros Hi Hlookup ->.
      Z_to_nat i. rewrite Nat2Z.id in Hlookup |- *.
      iApply big_sepL_lookup_acc. done.
    Qed.
    Lemma chunk_model_lookup {l dq vs} (i : Z) i_ v :
      (0 ≤ i)%Z →
      vs !! i_ = Some v →
      i_ = Z.to_nat i →
      chunk_model l dq vs ⊢
      (l +ₗ i) ↦{dq} v.
    Proof.
      intros Hi Hlookup ->.
      Z_to_nat i. rewrite Nat2Z.id in Hlookup |- *.
      iApply big_sepL_lookup. done.
    Qed.

    Lemma chunk_model_update' {l} {i : Z} {dq vs} (j : Z) k v :
      (0 ≤ i ≤ j)%Z →
      vs !! k = Some v →
      k = Z.to_nat j - Z.to_nat i →
      chunk_model (l +ₗ i) dq vs ⊢
        (l +ₗ j) ↦{dq} v ∗
        ( ∀ w,
          (l +ₗ j) ↦{dq} w -∗
          chunk_model (l +ₗ i) dq (<[k := w]> vs)
        ).
    Proof.
      intros Hij Hlookup ->.
      Z_to_nat i. Z_to_nat j. rewrite !Nat2Z.id in Hlookup |- *. remember (j - i) as k eqn:Hk.
      rewrite {1}(chunk_model_update k); [lia | done | lia |].
      rewrite loc_add_assoc -Nat2Z.inj_add Hk -Nat.le_add_sub //. lia.
    Qed.
    Lemma chunk_model_lookup_acc' {l} {i : Z} {dq vs} (j : Z) k v :
      (0 ≤ i ≤ j)%Z →
      vs !! k = Some v →
      k = Z.to_nat j - Z.to_nat i →
      chunk_model (l +ₗ i) dq vs ⊢
        (l +ₗ j) ↦{dq} v ∗
        ( (l +ₗ j) ↦{dq} v -∗
          chunk_model (l +ₗ i) dq vs
        ).
    Proof.
      intros Hij Hlookup ->.
      Z_to_nat i. Z_to_nat j. rewrite !Nat2Z.id in Hlookup |- *. remember (j - i) as k eqn:Hk.
      rewrite {1}(chunk_model_lookup_acc k); [lia | done | lia |].
      rewrite loc_add_assoc -Nat2Z.inj_add Hk -Nat.le_add_sub //. lia.
    Qed.
    Lemma chunk_model_lookup' {l} {i : Z} {dq vs} (j : Z) k v :
      (0 ≤ i ≤ j)%Z →
      vs !! k = Some v →
      k = Z.to_nat j - Z.to_nat i →
      chunk_model (l +ₗ i) dq vs ⊢
      (l +ₗ j) ↦{dq} v.
    Proof.
      intros Hij Hlookup ->.
      Z_to_nat i. Z_to_nat j. rewrite !Nat2Z.id in Hlookup |- *. remember (j - i) as k eqn:Hk.
      rewrite {1}(chunk_model_lookup k); [lia | done | lia |].
      rewrite loc_add_assoc -Nat2Z.inj_add Hk -Nat.le_add_sub //. lia.
    Qed.

    Lemma chunk_model_valid l dq vs :
      0 < length vs →
      chunk_model l dq vs ⊢
      ⌜✓ dq⌝.
    Proof.
      intros Hvs. destruct vs as [| v vs]; first naive_solver lia.
      iIntros "(H↦ & _)".
      iApply (mapsto_valid with "H↦").
    Qed.
    Lemma chunk_model_combine l dq1 vs1 dq2 vs2 :
      length vs1 = length vs2 →
      chunk_model l dq1 vs1 -∗
      chunk_model l dq2 vs2 -∗
        ⌜vs1 = vs2⌝ ∗
        chunk_model l (dq1 ⋅ dq2) vs1.
    Proof.
      iInduction vs1 as [| v1 vs1] "IH" forall (l vs2); iIntros "% Hmodel1 Hmodel2".
      - rewrite (nil_length_inv vs2) //. naive_solver.
      - destruct vs2 as [| v2 vs2]; first iSteps.
        iDestruct (chunk_model_cons_2 with "Hmodel1") as "(H↦1 & Hmodel1)".
        iDestruct (chunk_model_cons_2 with "Hmodel2") as "(H↦2 & Hmodel2)".
        iDestruct (mapsto_combine with "H↦1 H↦2") as "(H↦ & ->)".
        iDestruct ("IH" with "[] Hmodel1 Hmodel2") as "(-> & Hmodel)"; first iSteps. iSplit; first iSteps.
        iApply (chunk_model_cons_1 with "H↦ Hmodel").
    Qed.
    Lemma chunk_model_valid_2 l dq1 vs1 dq2 vs2 :
      0 < length vs1 →
      length vs1 = length vs2 →
      chunk_model l dq1 vs1 -∗
      chunk_model l dq2 vs2 -∗
      ⌜✓ (dq1 ⋅ dq2) ∧ vs1 = vs2⌝.
    Proof.
      iIntros "% % Hmodel1 Hmodel2".
      iDestruct (chunk_model_combine with "Hmodel1 Hmodel2") as "(-> & Hmodel)"; first done.
      iDestruct (chunk_model_valid with "Hmodel") as %?; first done.
      iSteps.
    Qed.
    Lemma chunk_model_agree l dq1 vs1 dq2 vs2 :
      length vs1 = length vs2 →
      chunk_model l dq1 vs1 -∗
      chunk_model l dq2 vs2 -∗
      ⌜vs1 = vs2⌝.
    Proof.
      iIntros "% Hmodel1 Hmodel2".
      iDestruct (chunk_model_combine with "Hmodel1 Hmodel2") as "(-> & _)"; first done.
      iSteps.
    Qed.
    Lemma chunk_model_dfrac_ne l1 dq1 vs1 l2 dq2 vs2 :
      0 < length vs1 →
      length vs1 = length vs2 →
      ¬ ✓ (dq1 ⋅ dq2) →
      chunk_model l1 dq1 vs1 -∗
      chunk_model l2 dq2 vs2 -∗
      ⌜l1 ≠ l2⌝.
    Proof.
      iIntros "% % % Hmodel1 Hmodel2" (->).
      iDestruct (chunk_model_valid_2 with "Hmodel1 Hmodel2") as %?; naive_solver.
    Qed.
    Lemma chunk_model_ne l1 vs1 l2 dq2 vs2 :
      0 < length vs1 →
      length vs1 = length vs2 →
      chunk_model l1 (DfracOwn 1) vs1 -∗
      chunk_model l2 dq2 vs2 -∗
      ⌜l1 ≠ l2⌝.
    Proof.
      intros.
      iApply chunk_model_dfrac_ne; [done.. | intros []%(exclusive_l _)].
    Qed.
    Lemma chunk_model_exclusive l vs1 vs2 :
      0 < length vs1 →
      length vs1 = length vs2 →
      chunk_model l (DfracOwn 1) vs1 -∗
      chunk_model l (DfracOwn 1) vs2 -∗
      False.
    Proof.
      iIntros "% % Hmodel1 Hmodel2".
      iDestruct (chunk_model_valid_2 with "Hmodel1 Hmodel2") as %?; naive_solver.
    Qed.
    Lemma chunk_model_persist l dq vs :
      chunk_model l dq vs ⊢ |==>
      chunk_model l DfracDiscarded vs.
    Proof.
      iIntros "Hmodel".
      iApply big_sepL_bupd. iApply (big_sepL_impl with "Hmodel").
      iSteps.
    Qed.
  End chunk_model.

  Section chunk_span.
    Definition chunk_span l dq n : iProp Σ :=
      ∃ vs,
      ⌜length vs = n⌝ ∗
      chunk_model l dq vs.

    #[global] Instance chunk_span_timeless l dq n :
      Timeless (chunk_span l dq n).
    Proof.
      apply _.
    Qed.
    #[global] Instance chunk_span_persistent l n :
      Persistent (chunk_span l DfracDiscarded n).
    Proof.
      apply _.
    Qed.

    #[global] Instance chunk_span_fractional l n :
      Fractional (λ q, chunk_span l (DfracOwn q) n).
    Proof.
      intros q1 q2. rewrite /chunk_span. setoid_rewrite chunk_model_fractional. iSplit; first iSteps.
      iIntros "((%vs & % & Hmodel1) & (%_vs & % & Hmodel2))".
      iDestruct (chunk_model_agree with "Hmodel1 Hmodel2") as %<-; first naive_solver.
      iSteps.
    Qed.
    #[global] Instance chunk_span_as_fractional l q n :
      AsFractional (chunk_span l (DfracOwn q) n) (λ q, chunk_span l (DfracOwn q) n) q.
    Proof.
      split; [done | apply _].
    Qed.

    Lemma chunk_span_singleton l dq :
      ( ∃ v,
        l ↦{dq} v
      ) ⊣⊢
      chunk_span l dq 1.
    Proof.
      setoid_rewrite chunk_model_singleton. iSplit.
      - iIntros "(%v & Hmodel)".
        iExists [v]. iSteps.
      - iIntros "(%vs & % & Hmodel)".
        destruct vs as [| v vs]; first iSteps. destruct vs; iSteps.
    Qed.
    Lemma chunk_span_singleton_1 l dq v :
      l ↦{dq} v ⊢
      chunk_span l dq 1.
    Proof.
      rewrite -chunk_span_singleton. iSteps.
    Qed.
    Lemma chunk_span_singleton_2 l dq :
      chunk_span l dq 1 ⊢
        ∃ v,
        l ↦{dq} v.
    Proof.
      rewrite chunk_span_singleton. iSteps.
    Qed.

    Lemma chunk_span_cons l dq n :
      ( ∃ v,
        l ↦{dq} v ∗
        chunk_span (l +ₗ 1) dq n
      ) ⊣⊢
      chunk_span l dq (S n).
    Proof.
      iSplit.
      - iIntros "(%v & H↦ & (%vs & % & Hmodel))".
        iExists (v :: vs). iSplit; first iSteps.
        iApply (chunk_model_cons_1 with "H↦ Hmodel").
      - iIntros "(%vs & % & Hmodel)".
        destruct vs as [| v vs]; first iSteps.
        iDestruct (chunk_model_cons_2 with "Hmodel") as "(H↦ & Hmodel)".
        iExists v. iFrame. iExists vs. auto.
    Qed.
    Lemma chunk_span_cons_1 l dq v n :
      l ↦{dq} v -∗
      chunk_span (l +ₗ 1) dq n -∗
      chunk_span l dq (S n).
    Proof.
      rewrite -chunk_span_cons. iSteps.
    Qed.
    Lemma chunk_span_cons_2 l dq n :
      chunk_span l dq (S n) ⊢
        ∃ v,
        l ↦{dq} v ∗
        chunk_span (l +ₗ 1) dq n.
    Proof.
      rewrite chunk_span_cons //.
    Qed.
    #[global] Instance chunk_span_cons_frame l dq v n R Q :
      Frame false R (l ↦{dq} v ∗ chunk_span (l +ₗ 1) dq n) Q →
      Frame false R (chunk_span l dq (S n)) Q
    | 2.
    Proof.
      rewrite /Frame. setoid_rewrite <- chunk_span_cons. intros H.
      iPoseProof H as "H". iSteps.
    Qed.

    Lemma chunk_span_app l dq n1 n2 :
      chunk_span l dq n1 ∗
      chunk_span (l +ₗ n1) dq n2 ⊣⊢
      chunk_span l dq (n1 + n2).
    Proof.
      iSplit.
      - iIntros "((%vs1 & % & Hmodel1) & (%vs2 & % & Hmodel2))".
        iExists (vs1 ++ vs2). iSplit; first (rewrite app_length; naive_solver).
        iApply (chunk_model_app_1 with "Hmodel1 Hmodel2"); first congruence.
      - iIntros "(%vs & % & Hmodel)".
        iDestruct (chunk_model_app_2 (take n1 vs) (drop n1 vs) with "Hmodel") as "(Hmodel1 & Hmodel2)"; first rewrite take_drop //.
        iSplitL "Hmodel1".
        + iExists (take n1 vs). iFrame. rewrite take_length_le //. lia.
        + iExists (drop n1 vs). rewrite take_length_le; first lia. iFrame.
          rewrite drop_length. iSteps.
    Qed.
    Lemma chunk_span_app_1 dq l1 (n1 : nat) l2 n2 :
      l2 = l1 +ₗ n1 →
      chunk_span l1 dq n1 -∗
      chunk_span l2 dq n2 -∗
      chunk_span l1 dq (n1 + n2).
    Proof.
      intros ->. rewrite -chunk_span_app. iSteps.
    Qed.
    Lemma chunk_span_app_2 {l dq n} n1 n2 :
      n = n1 + n2 →
      chunk_span l dq n ⊢
        chunk_span l dq n1 ∗
        chunk_span (l +ₗ n1) dq n2.
    Proof.
      intros ->. rewrite chunk_span_app //.
    Qed.

    Lemma chunk_span_app3 l dq n1 (n2 : nat) n3 :
      chunk_span l dq n1 ∗
      chunk_span (l +ₗ n1) dq n2 ∗
      chunk_span (l +ₗ (n1 + n2)%nat) dq n3 ⊣⊢
      chunk_span l dq (n1 + n2 + n3).
    Proof.
      rewrite -!chunk_span_app. iSteps.
    Qed.
    Lemma chunk_span_app3_1 dq l1 n1 l2 n2 l3 n3 :
      l2 = l1 +ₗ n1 →
      l3 = l1 +ₗ (n1 + n2)%nat →
      chunk_span l1 dq n1 -∗
      chunk_span l2 dq n2 -∗
      chunk_span l3 dq n3 -∗
      chunk_span l1 dq (n1 + n2 + n3).
    Proof.
      intros -> ->. rewrite -chunk_span_app3. iSteps.
    Qed.
    Lemma chunk_span_app3_2 {l dq n} n1 n2 n3 :
      n = n1 + n2 + n3 →
      chunk_span l dq n ⊢
        chunk_span l dq n1 ∗
        chunk_span (l +ₗ n1) dq n2 ∗
        chunk_span (l +ₗ (n1 + n2)%nat) dq n3.
    Proof.
      intros ->. rewrite chunk_span_app3 //.
    Qed.

    Lemma chunk_span_update {l dq n} (i : Z) :
      (0 ≤ i < n)%Z →
      chunk_span l dq n ⊢
        ∃ v,
        (l +ₗ i) ↦{dq} v ∗
        ( ∀ w,
          (l +ₗ i) ↦{dq} w -∗
          chunk_span l dq n
        ).
    Proof.
      iIntros "%Hi (%vs & %Hvs & Hmodel)".
      iDestruct (chunk_model_update i with "Hmodel") as "(H↦ & Hmodel)"; [lia | | done |].
      { rewrite list_lookup_lookup_total_lt; naive_solver lia. }
      iExists (vs !!! Z.to_nat i). iFrame. iIntros "%v H↦".
      iExists (<[Z.to_nat i := v]> vs). iSplit; first rewrite insert_length //.
      iSteps.
    Qed.
    Lemma chunk_span_lookup_acc {l dq n} (i : Z) :
      (0 ≤ i < n)%Z →
      chunk_span l dq n ⊢
        ∃ v,
        (l +ₗ i) ↦{dq} v ∗
        ( (l +ₗ i) ↦{dq} v -∗
          chunk_span l dq n
        ).
    Proof.
      iIntros "%Hi Hspan".
      iDestruct (chunk_span_update with "Hspan") as "(%v & H↦ & Hspan)"; first done.
      auto with iFrame.
    Qed.
    Lemma chunk_span_lookup {l dq n} (i : Z) :
      (0 ≤ i < n)%Z →
      chunk_span l dq n ⊢
        ∃ v,
        (l +ₗ i) ↦{dq} v.
    Proof.
      iIntros "%Hi Hspan".
      iDestruct (chunk_span_lookup_acc with "Hspan") as "(%v & H↦ & _)"; first done.
      iSteps.
    Qed.

    Lemma chunk_span_update' {l} {i : Z} {dq n} (j : Z) :
      (0 ≤ i ≤ j ∧ j < i + n)%Z →
      chunk_span (l +ₗ i) dq n ⊢
        ∃ v,
        (l +ₗ j) ↦{dq} v ∗
        ( ∀ w,
          (l +ₗ j) ↦{dq} w -∗
          chunk_span (l +ₗ i) dq n
        ).
    Proof.
      intros Hij.
      Z_to_nat i. Z_to_nat j. remember (j - i) as k eqn:Hk.
      rewrite {1}(chunk_span_update k); first lia.
      rewrite loc_add_assoc -Nat2Z.inj_add Hk -Nat.le_add_sub //. lia.
    Qed.
    Lemma chunk_span_lookup_acc' {l} {i : Z} {dq n} (j : Z) :
      (0 ≤ i ≤ j ∧ j < i + n)%Z →
      chunk_span (l +ₗ i) dq n ⊢
        ∃ v,
        (l +ₗ j) ↦{dq} v ∗
        ( (l +ₗ j) ↦{dq} v -∗
          chunk_span (l +ₗ i) dq n
        ).
    Proof.
      intros Hij.
      Z_to_nat i. Z_to_nat j. remember (j - i) as k eqn:Hk.
      rewrite {1}(chunk_span_lookup_acc k); first lia.
      rewrite loc_add_assoc -Nat2Z.inj_add Hk -Nat.le_add_sub //. lia.
    Qed.
    Lemma chunk_span_lookup' {l} {i : Z} {dq n} (j : Z) :
      (0 ≤ i ≤ j ∧ j < i + n)%Z →
      chunk_span (l +ₗ i) dq n ⊢
        ∃ v,
        (l +ₗ j) ↦{dq} v.
    Proof.
      intros Hij.
      Z_to_nat i. Z_to_nat j. remember (j - i) as k eqn:Hk.
      rewrite {1}(chunk_span_lookup k); first lia.
      rewrite loc_add_assoc -Nat2Z.inj_add Hk -Nat.le_add_sub //. lia.
    Qed.

    Lemma chunk_span_valid l dq n :
      0 < n →
      chunk_span l dq n ⊢
      ⌜✓ dq⌝.
    Proof.
      iIntros "% (%vs & % & Hmodel)".
      iApply (chunk_model_valid with "Hmodel"); first naive_solver.
    Qed.
    Lemma chunk_span_combine l dq1 n1 dq2 n2 :
      n1 = n2 →
      chunk_span l dq1 n1 -∗
      chunk_span l dq2 n2 -∗
      chunk_span l (dq1 ⋅ dq2) n1.
    Proof.
      iIntros (<-) "(%vs1 & % & Hmodel1) (%vs2 & % & Hmodel2)".
      iDestruct (chunk_model_combine with "Hmodel1 Hmodel2") as "(<- & Hmodel)"; first naive_solver.
      iSteps.
    Qed.
    Lemma chunk_span_valid_2 l dq1 n1 dq2 n2 :
      n1 = n2 →
      0 < n1 →
      chunk_span l dq1 n1 -∗
      chunk_span l dq2 n2 -∗
      ⌜✓ (dq1 ⋅ dq2)⌝.
    Proof.
      iIntros "% % Hspan1 Hspan2".
      iDestruct (chunk_span_combine with "Hspan1 Hspan2") as "Hspan"; first done.
      iDestruct (chunk_span_valid with "Hspan") as %?; first done.
      iSteps.
    Qed.
    Lemma chunk_span_dfrac_ne l1 dq1 n1 l2 dq2 n2 :
      n1 = n2 →
      0 < n1 →
      ¬ ✓ (dq1 ⋅ dq2) →
      chunk_span l1 dq1 n1 -∗
      chunk_span l2 dq2 n2 -∗
      ⌜l1 ≠ l2⌝.
    Proof.
      iIntros "% % % Hspan1 Hspan2" (->).
      iDestruct (chunk_span_valid_2 with "Hspan1 Hspan2") as %?; done.
    Qed.
    Lemma chunk_span_ne l1 n1 l2 dq2 n2 :
      n1 = n2 →
      0 < n1 →
      chunk_span l1 (DfracOwn 1) n1 -∗
      chunk_span l2 dq2 n2 -∗
      ⌜l1 ≠ l2⌝.
    Proof.
      intros.
      iApply chunk_span_dfrac_ne; [done.. | intros []%(exclusive_l _)].
    Qed.
    Lemma chunk_span_exclusive l n1 n2 :
      n1 = n2 →
      0 < n1 →
      chunk_span l (DfracOwn 1) n1 -∗
      chunk_span l (DfracOwn 1) n2 -∗
      False.
    Proof.
      iIntros "% % Hspan1 Hspan2".
      iDestruct (chunk_span_valid_2 with "Hspan1 Hspan2") as %?; done.
    Qed.
    Lemma chunk_span_persist l dq n :
      chunk_span l dq n ⊢ |==>
      chunk_span l DfracDiscarded n.
    Proof.
      iIntros "(%vs & % & Hmodel)".
      iMod (chunk_model_persist with "Hmodel") as "Hmodel".
      iSteps.
    Qed.
  End chunk_span.

  Section chunk_cslice.
    Implicit Types sz : nat.

    Definition chunk_cslice l sz i dq vs : iProp Σ :=
      [∗ list] k ↦ v ∈ vs, (l +ₗ (i + k) `mod` sz) ↦{dq} v.

    (* Lemma chunk_cslice_eq l sz i dq vs : *)
    (*   chunk_cslice l sz i dq vs ⊣⊢ *)
    (*     let j := i `mod` sz in *)
    (*     chunk_model (l +ₗ j) dq (take (sz - j) vs) ∗ *)
    (*     chunk_model l dq (drop (sz - j) vs). *)
    (* Proof. *)
    (* Admitted. *)

    #[global] Instance chunk_cslice_timeless l sz i dq vs :
      Timeless (chunk_cslice l sz i dq vs).
    Proof.
      apply _.
    Qed.
    #[global] Instance chunk_cslice_persistent l sz i vs :
      Persistent (chunk_cslice l sz i DfracDiscarded vs).
    Proof.
      apply _.
    Qed.

    #[global] Instance chunk_cslice_fractional l sz i vs :
      Fractional (λ q, chunk_cslice l sz i (DfracOwn q) vs).
    Proof.
      apply _.
    Qed.
    #[global] Instance chunk_cslice_as_fractionak l sz i q vs :
      AsFractional (chunk_cslice l sz i (DfracOwn q) vs) (λ q, chunk_cslice l sz i (DfracOwn q) vs) q.
    Proof.
      split; [done | apply _].
    Qed.

    Lemma chunk_model_to_cslice l dq vs :
      chunk_model l dq vs ⊢
      chunk_cslice l (length vs) 0 dq vs.
    Proof.
      iIntros "Hmodel".
      iApply (big_sepL_impl with "Hmodel"). iIntros (k v Hk%lookup_lt_Some) "!> H↦".
      rewrite left_id Z.mod_small //; first lia.
    Qed.

    Lemma chunk_cslice_nil l sz i dq :
      ⊢ chunk_cslice l sz i dq [].
    Proof.
      rewrite /chunk_cslice //.
    Qed.

    Lemma chunk_cslice_singleton l sz i dq v :
      (l +ₗ i `mod` sz) ↦{dq} v ⊣⊢
      chunk_cslice l sz i dq [v].
    Proof.
      setoid_rewrite big_sepL_singleton. rewrite right_id //.
    Qed.
    Lemma chunk_cslice_singleton_1 l sz i dq v :
      (l +ₗ i `mod` sz) ↦{dq} v ⊢
      chunk_cslice l sz i dq [v].
    Proof.
      rewrite chunk_cslice_singleton //.
    Qed.
    Lemma chunk_cslice_singleton_2 l sz i dq v :
      chunk_cslice l sz i dq [v] ⊢
      (l +ₗ i `mod` sz) ↦{dq} v.
    Proof.
      rewrite chunk_cslice_singleton //.
    Qed.

    Lemma chunk_cslice_app l sz i dq vs1 vs2 :
      chunk_cslice l sz i dq vs1 ∗
      chunk_cslice l sz (i + length vs1) dq vs2 ⊣⊢
      chunk_cslice l sz i dq (vs1 ++ vs2).
    Proof.
      rewrite /chunk_cslice Nat2Z.inj_add.
      setoid_rewrite <- (assoc Z.add).
      setoid_rewrite <- Nat2Z.inj_add at 2.
      rewrite big_sepL_app //.
    Qed.
    Lemma chunk_cslice_app_1 l sz dq i1 vs1 i2 vs2 :
      i2 = i1 + length vs1 →
      chunk_cslice l sz i1 dq vs1 -∗
      chunk_cslice l sz i2 dq vs2 -∗
      chunk_cslice l sz i1 dq (vs1 ++ vs2).
    Proof.
      rewrite -chunk_cslice_app. iSteps.
    Qed.
    Lemma chunk_cslice_app_2 {l sz i dq vs} vs1 vs2 :
      vs = vs1 ++ vs2 →
      chunk_cslice l sz i dq vs ⊢
        chunk_cslice l sz i dq vs1 ∗
        chunk_cslice l sz (i + length vs1) dq vs2.
    Proof.
      rewrite chunk_cslice_app. iSteps.
    Qed.

    Lemma chunk_cslice_cons l sz i dq v vs :
      (l +ₗ i `mod` sz) ↦{dq} v ∗
      chunk_cslice l sz (S i) dq vs ⊣⊢
      chunk_cslice l sz i dq (v :: vs).
    Proof.
      assert (v :: vs = [v] ++ vs) as -> by done.
      rewrite -chunk_cslice_app chunk_cslice_singleton Nat.add_1_r //.
    Qed.
    Lemma chunk_cslice_cons_1 l sz i dq v vs :
      (l +ₗ i `mod` sz) ↦{dq} v -∗
      chunk_cslice l sz (S i) dq vs -∗
      chunk_cslice l sz i dq (v :: vs).
    Proof.
      rewrite -chunk_cslice_cons. iSteps.
    Qed.
    Lemma chunk_cslice_cons_2 l sz i dq v vs :
      chunk_cslice l sz i dq (v :: vs) ⊢
        (l +ₗ i `mod` sz) ↦{dq} v ∗
        chunk_cslice l sz (S i) dq vs.
    Proof.
      rewrite chunk_cslice_cons //.
    Qed.

    Lemma chunk_cslice_update {l sz i dq vs} k v :
      vs !! k = Some v →
      chunk_cslice l sz i dq vs ⊢
        (l +ₗ (i + k)%nat `mod` sz) ↦{dq} v ∗
        ( ∀ w,
          (l +ₗ (i + k)%nat `mod` sz) ↦{dq} w -∗
          chunk_cslice l sz i dq (<[k := w]> vs)
        ).
    Proof.
      rewrite Nat2Z.inj_add. apply: big_sepL_insert_acc.
    Qed.
    Lemma chunk_cslice_lookup_acc {l sz i dq vs} k v :
      vs !! k = Some v →
      chunk_cslice l sz i dq vs ⊢
        (l +ₗ (i + k)%nat `mod` sz) ↦{dq} v ∗
        ( (l +ₗ (i + k)%nat `mod` sz) ↦{dq} v -∗
          chunk_cslice l sz i dq vs
        ).
    Proof.
      rewrite Nat2Z.inj_add. apply: big_sepL_lookup_acc.
    Qed.
    Lemma chunk_cslice_lookup {l sz i dq vs} k v :
      vs !! k = Some v →
      chunk_cslice l sz i dq vs ⊢
      (l +ₗ (i + k)%nat `mod` sz) ↦{dq} v.
    Proof.
      rewrite Nat2Z.inj_add. apply: big_sepL_lookup.
    Qed.

    Lemma chunk_cslice_shift l sz i dq vs :
      chunk_cslice l sz i dq vs ⊢
      chunk_cslice l sz (i + sz) dq vs.
    Proof.
      rewrite /chunk_cslice.
      setoid_rewrite <- Nat2Z.inj_add at 2.
      setoid_rewrite (comm Nat.add) at 2.
      setoid_rewrite <- (assoc Nat.add).
      do 2 setoid_rewrite Nat2Z.inj_add.
      setoid_rewrite <- Zplus_mod_idemp_l at 2.
      setoid_rewrite Z_mod_same_full.
      setoid_rewrite Z.add_0_l at 7.
      done.
    Qed.

    Lemma chunk_cslice_valid l sz i dq vs :
      0 < length vs →
      chunk_cslice l sz i dq vs ⊢
      ⌜✓ dq⌝.
    Proof.
      intros Hvs. destruct vs as [| v vs]; first naive_solver lia.
      iIntros "(H↦ & _)".
      iApply (mapsto_valid with "H↦").
    Qed.
    Lemma chunk_cslice_combine l sz i dq1 vs1 dq2 vs2 :
      length vs1 = length vs2 →
      chunk_cslice l sz i dq1 vs1 -∗
      chunk_cslice l sz i dq2 vs2 -∗
        ⌜vs1 = vs2⌝ ∗
        chunk_cslice l sz i (dq1 ⋅ dq2) vs1.
    Proof.
      iInduction vs1 as [| v1 vs1] "IH" forall (i vs2); iIntros "% Hcslice1 Hcslice2".
      - rewrite (nil_length_inv vs2) //. naive_solver.
      - destruct vs2 as [| v2 vs2]; first iSteps.
        iDestruct (chunk_cslice_cons_2 with "Hcslice1") as "(H↦1 & Hcslice1)".
        iDestruct (chunk_cslice_cons_2 with "Hcslice2") as "(H↦2 & Hcslice2)".
        iDestruct (mapsto_combine with "H↦1 H↦2") as "(H↦ & ->)".
        iDestruct ("IH" with "[] Hcslice1 Hcslice2") as "(-> & Hcslice)"; first iSteps. iSplit; first iSteps.
        iApply (chunk_cslice_cons_1 with "H↦ Hcslice").
    Qed.
    Lemma chunk_cslice_valid_2 l sz i dq1 vs1 dq2 vs2 :
      0 < length vs1 →
      length vs1 = length vs2 →
      chunk_cslice l sz i dq1 vs1 -∗
      chunk_cslice l sz i dq2 vs2 -∗
      ⌜✓ (dq1 ⋅ dq2) ∧ vs1 = vs2⌝.
    Proof.
      iIntros "% % Hcslice1 Hcslice2".
      iDestruct (chunk_cslice_combine with "Hcslice1 Hcslice2") as "(-> & Hcslice)"; first done.
      iDestruct (chunk_cslice_valid with "Hcslice") as %?; first done.
      iSteps.
    Qed.
    Lemma chunk_cslice_agree l sz i dq1 vs1 dq2 vs2 :
      length vs1 = length vs2 →
      chunk_cslice l sz i dq1 vs1 -∗
      chunk_cslice l sz i dq2 vs2 -∗
      ⌜vs1 = vs2⌝.
    Proof.
      iIntros "% Hcslice1 Hcslice2".
      iDestruct (chunk_cslice_combine with "Hcslice1 Hcslice2") as "(-> & _)"; first done.
      iSteps.
    Qed.
    Lemma chunk_cslice_dfrac_ne l sz i1 dq1 vs1 i2 dq2 vs2 :
      0 < length vs1 →
      length vs1 = length vs2 →
      ¬ ✓ (dq1 ⋅ dq2) →
      chunk_cslice l sz i1 dq1 vs1 -∗
      chunk_cslice l sz i2 dq2 vs2 -∗
      ⌜i1 ≠ i2⌝.
    Proof.
      iIntros "% % % Hcslice1 Hcslice2" (->).
      iDestruct (chunk_cslice_valid_2 with "Hcslice1 Hcslice2") as %?; naive_solver.
    Qed.
    Lemma chunk_cslice_ne l sz i1 vs1 i2 dq2 vs2 :
      0 < length vs1 →
      length vs1 = length vs2 →
      chunk_cslice l sz i1 (DfracOwn 1) vs1 -∗
      chunk_cslice l sz i2 dq2 vs2 -∗
      ⌜i1 ≠ i2⌝.
    Proof.
      intros.
      iApply chunk_cslice_dfrac_ne; [done.. | intros []%(exclusive_l _)].
    Qed.
    Lemma chunk_cslice_exclusive l sz i vs1 vs2 :
      0 < length vs1 →
      length vs1 = length vs2 →
      chunk_cslice l sz i (DfracOwn 1) vs1 -∗
      chunk_cslice l sz i (DfracOwn 1) vs2 -∗
      False.
    Proof.
      iIntros "% % Hcslice1 Hcslice2".
      iDestruct (chunk_cslice_valid_2 with "Hcslice1 Hcslice2") as %?; naive_solver.
    Qed.
    Lemma chunk_cslice_persist l sz i dq vs :
      chunk_cslice l sz i dq vs ⊢ |==>
      chunk_cslice l sz i DfracDiscarded vs.
    Proof.
      iIntros "Hcslice".
      iApply big_sepL_bupd. iApply (big_sepL_impl with "Hcslice").
      iSteps.
    Qed.
  End chunk_cslice.

  Notation chunk_au_load l i Φ := (
    AU << ∃∃ dq v,
      (l +ₗ i) ↦{dq} v
    >> @ ⊤, ∅ <<
      (l +ₗ i) ↦{dq} v,
    COMM
      Φ v
    >>
  )%I.
  Notation chunk_au_store l i v P := (
    AU << ∃∃ v',
      (l +ₗ i) ↦ v'
    >> @ ⊤, ∅ <<
      (l +ₗ i) ↦ v,
    COMM
      P
    >>
  )%I.

  Lemma chunk_make_spec sz v :
    {{{ True }}}
      chunk_make #sz v
    {{{ l,
      RET #l;
      chunk_model l (DfracOwn 1) (replicate (Z.to_nat sz) v) ∗
      if decide (0 < sz)%Z then meta_token l ⊤ else True
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_rec. wp_pures.
    case_bool_decide; wp_pures.
    - setoid_rewrite decide_True; [| done..].
      iSteps.
    - iApply "HΦ".
      rewrite Z2Nat.nonpos; first lia. rewrite decide_False; first lia. rewrite right_id.
      iApply chunk_model_nil.
  Qed.

  Lemma chunk_get_spec i_ v l (i : Z) dq vs E :
    (0 ≤ i)%Z →
    vs !! i_ = Some v →
    i_ = Z.to_nat i →
    {{{
      chunk_model l dq vs
    }}}
      !#(l +ₗ i) @ E
    {{{
      RET v;
      chunk_model l dq vs
    }}}.
  Proof.
    iIntros (Hi Hlookup ->) "%Φ Hmodel HΦ".
    iDestruct (chunk_model_lookup_acc with "Hmodel") as "(H↦ & Hmodel)"; [done.. |].
    iSteps.
  Qed.
  Lemma chunk_get_spec' k v l (i j : Z) dq vs E :
    (0 ≤ i ≤ j)%Z →
    vs !! k = Some v →
    k = Z.to_nat j - Z.to_nat i →
    {{{
      chunk_model (l +ₗ i) dq vs
    }}}
      !#(l +ₗ j) @ E
    {{{
      RET v;
      chunk_model (l +ₗ i) dq vs
    }}}.
  Proof.
    iIntros (Hj Hlookup ->) "%Φ Hmodel HΦ".
    iDestruct (chunk_model_lookup_acc' with "Hmodel") as "(H↦ & Hmodel)"; [done.. |].
    iSteps.
  Qed.

  Lemma chunk_set_spec l (i : Z) vs v E :
    (0 ≤ i < length vs)%Z →
    {{{
      chunk_model l (DfracOwn 1) vs
    }}}
      #(l +ₗ i) <- v @ E
    {{{
      RET ();
      chunk_model l (DfracOwn 1) (<[Z.to_nat i := v]> vs)
    }}}.
  Proof.
    iIntros "%Hi %Φ Hmodel HΦ".
    iDestruct (chunk_model_update i with "Hmodel") as "(H↦ & Hmodel)"; [lia | | done |].
    { destruct (nth_lookup_or_length vs (Z.to_nat i) inhabitant); [done | lia]. }
    iSteps.
  Qed.
  Lemma chunk_set_spec' l (i j : Z) vs v E :
    (0 ≤ i ≤ j ∧ j < i + length vs)%Z →
    {{{
      chunk_model (l +ₗ i) (DfracOwn 1) vs
    }}}
      #(l +ₗ j) <- v @ E
    {{{
      RET ();
      chunk_model (l +ₗ i) (DfracOwn 1) (<[Z.to_nat j - Z.to_nat i := v]> vs)
    }}}.
  Proof.
    iIntros "%Hi %Φ Hmodel HΦ".
    iDestruct (chunk_model_update' j with "Hmodel") as "(H↦ & Hmodel)"; [lia | | done |].
    { destruct (nth_lookup_or_length vs (Z.to_nat j - Z.to_nat i) inhabitant); [done | lia]. }
    iSteps.
  Qed.

  #[local] Lemma chunk_foldli_aux_spec i vs Ψ l (sz : Z) acc fn :
    i ≤ Z.to_nat sz →
    i = length vs →
    {{{
      ▷ Ψ i vs None acc ∗
      □ (
        ∀ i vs (o : option val) acc,
        ⌜i < Z.to_nat sz ∧ i = length vs⌝ -∗
        Ψ i vs o acc -∗
        match o with
        | None =>
            chunk_au_load l i (λ v,
              ▷ Ψ i vs (Some v) acc
            )
        | Some v =>
            WP fn acc #i v {{ acc,
              ▷ Ψ (S i) (vs ++ [v]) None acc
            }}
        end
      )
    }}}
      chunk_foldli_aux #l #sz acc fn #i
    {{{ vs' acc,
      RET acc;
      ⌜(length vs + length vs')%nat = Z.to_nat sz⌝ ∗
      Ψ (Z.to_nat sz) (vs ++ vs') None acc
    }}}.
  Proof.
    iIntros "%Hi1 %Hi2 %Φ (HΨ & #H) HΦ".
    remember (Z.to_nat sz - i) as j eqn:Hj.
    iInduction j as [| j] "IH" forall (i vs acc Hi1 Hi2 Hj);
      wp_rec; wp_pures credit:"H£".
    - rewrite bool_decide_eq_true_2; first (repeat f_equal; lia). wp_pures.
      iApply ("HΦ" $! []).
      rewrite !right_id. assert (Z.to_nat sz = i) as -> by lia. iSteps.
    - rewrite bool_decide_eq_false_2; first naive_solver lia. wp_pures.
      wp_bind (!_)%E.
      iMod ("H" $! i with "[] HΨ") as "(%dq & %v & H↦ & _ & HΨ)"; first iSteps.
      wp_load.
      iMod ("HΨ" with "H↦") as "HΨ". iModIntro.
      iMod (lc_fupd_elim_later with "H£ HΨ") as "HΨ".
      wp_apply (wp_wand with "(H [] HΨ)") as "%acc' HΨ"; first iSteps.
      rewrite Z.add_1_l -Nat2Z.inj_succ.
      wp_apply ("IH" with "[] [] [] HΨ [HΦ]"); rewrite ?app_length; [iSteps.. |].
      clear acc. iIntros "!> %vs' %acc (<- & HΨ)".
      iApply ("HΦ" $! (v :: vs')).
      rewrite -(assoc (++)). iSteps.
  Qed.
  Lemma chunk_foldli_spec_atomic Ψ l sz acc fn :
    {{{
      ▷ Ψ 0 [] None acc ∗
      □ (
        ∀ i vs (o : option val) acc,
        ⌜i < Z.to_nat sz ∧ i = length vs⌝ -∗
        Ψ i vs o acc -∗
        match o with
        | None =>
            chunk_au_load l i (λ v,
              ▷ Ψ i vs (Some v) acc
            )
        | Some v =>
            WP fn acc #i v {{ acc,
              ▷ Ψ (S i) (vs ++ [v]) None acc
            }}
        end
      )
    }}}
      chunk_foldli #l #sz acc fn
    {{{ vs acc,
      RET acc;
      ⌜length vs = Z.to_nat sz⌝ ∗
      Ψ (Z.to_nat sz) vs None acc
    }}}.
  Proof.
    iIntros "%Φ (HΨ & #H) HΦ".
    wp_rec.
    wp_smart_apply (chunk_foldli_aux_spec 0 [] Ψ with "[$HΨ] HΦ"); [lia | done |].
    auto with iFrame.
  Qed.
  Lemma chunk_foldli_spec Ψ l dq vs (sz : Z) acc fn :
    Z.to_nat sz = length vs →
    {{{
      ▷ Ψ 0 [] acc ∗
      chunk_model l dq vs ∗
      □ (
        ∀ i v acc,
        ⌜vs !! i = Some v⌝ -∗
        Ψ i (take i vs) acc -∗
        WP fn acc #i v {{ acc,
          ▷ Ψ (S i) (take i vs ++ [v]) acc
        }}
      )
    }}}
      chunk_foldli #l #sz acc fn
    {{{ acc,
      RET acc;
      chunk_model l dq vs ∗
      Ψ (Z.to_nat sz) vs acc
    }}}.
  Proof.
    iIntros "%Hvs %Φ (HΨ & Hmodel & #Hfn) HΦ".
    pose (Ψ' i vs_left o acc := (
      ⌜vs_left = take i vs⌝ ∗
      chunk_model l dq vs ∗
      Ψ i vs_left acc ∗
      ⌜from_option (λ v, v = vs !!! i) True o⌝%I
    )%I).
    wp_apply (chunk_foldli_spec_atomic Ψ' with "[$HΨ $Hmodel]"); last first.
    { clear acc. iIntros "%vs_left %acc (%Hvs_left & (-> & Hmodel & HΨ))".
      rewrite /Ψ' firstn_all2; first lia. iSteps.
    }
    iSplitR; first iSteps.
    clear acc. iIntros "!> %i %vs_left %o %acc (%Hi1 & %Hi2) (-> & Hmodel & HΨ & %Ho)".
    feed pose proof (list_lookup_lookup_total_lt vs i); first lia.
    destruct o as [v |].
    - rewrite Ho.
      wp_apply (wp_wand with "(Hfn [] HΨ)"); first iSteps. clear acc. iIntros "%acc HΨ". iFrame.
      erewrite take_S_r; done.
    - iDestruct (chunk_model_lookup_acc i with "Hmodel") as "(H↦ & Hmodel)"; [lia | done | lia |].
      iAuIntro. iAaccIntro with "H↦"; iSteps.
  Qed.
  Lemma chunk_foldli_spec' Ψ l dq vs (sz : Z) acc fn :
    Z.to_nat sz = length vs →
    {{{
      ▷ Ψ 0 [] acc ∗
      chunk_model l dq vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        ∀ acc,
        Ψ i (take i vs) acc -∗
        WP fn acc #i v {{ acc,
          ▷ Ψ (S i) (take i vs ++ [v]) acc
        }}
      )
    }}}
      chunk_foldli #l #sz acc fn
    {{{ acc,
      RET acc;
      chunk_model l dq vs ∗
      Ψ (Z.to_nat sz) vs acc
    }}}.
  Proof.
    iIntros "%Hsz %Φ (HΨ & Hmodel & Hfn) HΦ".
    match goal with |- context [big_opL bi_sep ?Ξ' _] => set Ξ := Ξ' end.
    pose (Ψ' i vs_left acc := (
      Ψ i vs_left acc ∗
      [∗ list] j ↦ v ∈ drop i vs, Ξ (i + j) v
    )%I).
    wp_apply (chunk_foldli_spec Ψ' with "[$HΨ $Hmodel $Hfn]"); [done | | iSteps].
    clear acc. iIntros "!> %i %v %acc %Hlookup (HΨ & HΞ)".
    erewrite drop_S; last done.
    iDestruct "HΞ" as "(Hfn & HΞ)".
    rewrite Nat.add_0_r. setoid_rewrite Nat.add_succ_r. iSteps.
  Qed.

  Lemma chunk_foldl_spec_atomic Ψ l sz acc fn :
    {{{
      ▷ Ψ 0 [] None acc ∗
      □ (
        ∀ i vs (o : option val) acc,
        ⌜i < Z.to_nat sz ∧ i = length vs⌝ -∗
        Ψ i vs o acc -∗
        match o with
        | None =>
            chunk_au_load l i (λ v,
              ▷ Ψ i vs (Some v) acc
            )
        | Some v =>
            WP fn acc v {{ acc,
              ▷ Ψ (S i) (vs ++ [v]) None acc
            }}
        end
      )
    }}}
      chunk_foldl #l #sz acc fn
    {{{ vs acc,
      RET acc;
      ⌜length vs = Z.to_nat sz⌝ ∗
      Ψ (Z.to_nat sz) vs None acc
    }}}.
  Proof.
    iIntros "%Φ (HΨ & #H) HΦ".
    wp_rec.
    wp_smart_apply (chunk_foldli_spec_atomic Ψ with "[$HΨ] HΦ"). clear acc. iIntros "!> %i %vs %o %acc %Hi HΨ".
    case_match; try wp_pures; iApply ("H" with "[//] HΨ").
  Qed.
  Lemma chunk_foldl_spec Ψ l dq vs (sz : Z) acc fn :
    Z.to_nat sz = length vs →
    {{{
      ▷ Ψ 0 [] acc ∗
      chunk_model l dq vs ∗
      □ (
        ∀ i v acc,
        ⌜vs !! i = Some v⌝ -∗
        Ψ i (take i vs) acc -∗
        WP fn acc v {{ acc,
          ▷ Ψ (S i) (take i vs ++ [v]) acc
        }}
      )
    }}}
      chunk_foldl #l #sz acc fn
    {{{ acc,
      RET acc;
      chunk_model l dq vs ∗
      Ψ (Z.to_nat sz) vs acc
    }}}.
  Proof.
    iIntros "%Hsz %Φ (HΨ & Hmodel & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (chunk_foldli_spec Ψ with "[$HΨ $Hmodel] HΦ"); first done.
    iSteps.
  Qed.
  Lemma chunk_foldl_spec' Ψ l dq vs (sz : Z) acc fn :
    Z.to_nat sz = length vs →
    {{{
      ▷ Ψ 0 [] acc ∗
      chunk_model l dq vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        ∀ acc,
        Ψ i (take i vs) acc -∗
        WP fn acc v {{ acc,
          ▷ Ψ (S i) (take i vs ++ [v]) acc
        }}
      )
    }}}
      chunk_foldl #l #sz acc fn
    {{{ acc,
      RET acc;
      chunk_model l dq vs ∗
      Ψ (Z.to_nat sz) vs acc
    }}}.
  Proof.
    iIntros "%Hsz %Φ (HΨ & Hmodel & Hfn) HΦ".
    wp_rec.
    wp_smart_apply (chunk_foldli_spec' Ψ with "[$HΨ $Hmodel Hfn] HΦ"); first done.
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.

  #[local] Lemma chunk_foldri_aux_spec (sz i : Z) vs Ψ l fn acc :
    Z.to_nat i + length vs = Z.to_nat sz →
    {{{
      ▷ Ψ (Z.to_nat i) acc None vs ∗
      □ (
        ∀ i acc (o : option val) vs,
        ⌜(S i + length vs)%nat = Z.to_nat sz⌝ -∗
        Ψ (S i) acc o vs -∗
        match o with
        | None =>
            chunk_au_load l i (λ v,
              ▷ Ψ (S i) acc (Some v) vs
            )
        | Some v =>
            WP fn #i v acc {{ acc,
              ▷ Ψ i acc None (v :: vs)
            }}
        end
      )
    }}}
      chunk_foldri_aux #l fn acc #i
    {{{ acc vs',
      RET acc;
      ⌜(length vs' + length vs)%nat = Z.to_nat sz⌝ ∗
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
      wp_bind (!_)%E.
      iMod ("H" $! j with "[] HΨ") as "(%dq & %v & H↦ & _ & HΨ)"; first iSteps.
      wp_load.
      iMod ("HΨ" with "H↦") as "HΨ". iModIntro.
      iMod (lc_fupd_elim_later with "H£ HΨ") as "HΨ".
      wp_apply (wp_wand with "(H [] HΨ)") as "%acc' HΨ"; first iSteps.
      wp_apply ("IH" with "[] [] HΨ [HΦ]"); rewrite ?app_length; [iSteps.. |]. clear acc. iIntros "!> %acc %vs' (<- & HΨ)".
      iApply ("HΦ" $! _ (vs' ++ [v])).
      rewrite app_length -(assoc (++)). iSteps.
  Qed.
  Lemma chunk_foldri_spec_atomic Ψ l sz fn acc :
    {{{
      ▷ Ψ (Z.to_nat sz) acc None [] ∗
      □ (
        ∀ i acc (o : option val) vs,
        ⌜(S i + length vs)%nat = Z.to_nat sz⌝ -∗
        Ψ (S i) acc o vs -∗
        match o with
        | None =>
            chunk_au_load l i (λ v,
              ▷ Ψ (S i) acc (Some v) vs
            )
        | Some v =>
            WP fn #i v acc {{ acc,
              ▷ Ψ i acc None (v :: vs)
            }}
        end
      )
    }}}
      chunk_foldri #l #sz fn acc
    {{{ acc vs,
      RET acc;
      ⌜length vs = Z.to_nat sz⌝ ∗
      Ψ 0 acc None vs
    }}}.
  Proof.
    iIntros "%Φ (HΨ & #H) HΦ".
    wp_rec.
    wp_smart_apply (chunk_foldri_aux_spec sz sz [] Ψ with "[$HΨ $H] [HΦ]").
    { rewrite right_id. lia. }
    clear acc. iIntros "!> %acc %vs".
    rewrite !right_id. iSteps.
  Qed.
  Lemma chunk_foldri_spec Ψ l dq vs (sz : Z) fn acc :
    Z.to_nat sz = length vs →
    {{{
      chunk_model l dq vs ∗
      ▷ Ψ (Z.to_nat sz) acc [] ∗
      □ (
        ∀ i v acc,
        ⌜vs !! i = Some v⌝ -∗
        Ψ (S i) acc (drop (S i) vs) -∗
        WP fn #i v acc {{ acc,
          ▷ Ψ i acc (v :: drop (S i) vs)
        }}
      )
    }}}
      chunk_foldri #l #sz fn acc
    {{{ acc,
      RET acc;
      Ψ 0 acc vs ∗
      chunk_model l dq vs
    }}}.
  Proof.
    iIntros "%Hsz %Φ (Hmodel & HΨ & #Hfn) HΦ".
    pose (Ψ' i acc o vs_right := (
      ⌜vs_right = drop i vs⌝ ∗
      chunk_model l dq vs ∗
      Ψ i acc vs_right ∗
      ⌜from_option (λ v, v = vs !!! (i - 1)) True o⌝%I
    )%I).
    wp_apply (chunk_foldri_spec_atomic Ψ' with "[$Hmodel $HΨ]"); last iSteps.
    iSplitR.
    - rewrite Hsz drop_all. iSteps.
    - clear acc. iIntros "!> %i %acc %o %vs_right %Hi (-> & Hmodel & HΨ & %Ho)".
      feed pose proof (list_lookup_lookup_total_lt vs i) as Hlookup; first lia.
      destruct o as [v |].
      + rewrite Ho.
        wp_apply (wp_wand with "(Hfn [] HΨ)").
        { iPureIntro. rewrite Hlookup. repeat f_equal. lia. }
        clear acc. iIntros "%acc HΨ". iFrame.
        iPureIntro. rewrite -drop_S ?Hlookup; repeat f_equal; lia.
      + iDestruct (chunk_model_lookup_acc i with "Hmodel") as "(H↦ & Hmodel)"; [lia | done | lia |].
        iAuIntro. iAaccIntro with "H↦"; first iSteps. iIntros "H↦ !>".
        iSteps; iPureIntro; rewrite drop_length; f_equal; lia.
  Qed.
  Lemma chunk_foldri_spec' Ψ l dq vs (sz : Z) fn acc :
    Z.to_nat sz = length vs →
    {{{
      chunk_model l dq vs ∗
      ▷ Ψ (Z.to_nat sz) acc [] ∗
      ( [∗ list] i ↦ v ∈ vs,
        ∀ acc,
        Ψ (S i) acc (drop (S i) vs) -∗
        WP fn #i v acc {{ acc,
          ▷ Ψ i acc (v :: drop (S i) vs)
        }}
      )
    }}}
      chunk_foldri #l #sz fn acc
    {{{ acc,
      RET acc;
      Ψ 0 acc vs ∗
      chunk_model l dq vs
    }}}.
  Proof.
    iIntros "%Hsz %Φ (Hmodel & HΨ & Hfn) HΦ".
    match goal with |- context [big_opL bi_sep ?Ξ' _] => set Ξ := Ξ' end.
    pose (Ψ' i acc vs_right := (
      Ψ i acc vs_right ∗
      [∗ list] j ↦ v ∈ take i vs, Ξ j v
    )%I).
    wp_apply (chunk_foldri_spec Ψ' with "[$Hmodel HΨ Hfn]"); [done | | iSteps].
    iFrame. rewrite firstn_all2; first lia. iFrame.
    clear acc. iIntros "!> %i %v %acc %Hlookup (HΨ & HΞ)".
    pose proof Hlookup as Hi%lookup_lt_Some.
    erewrite take_S_r; last done.
    iDestruct "HΞ" as "(HΞ & Hfn & _)".
    rewrite Nat.add_0_r take_length Nat.min_l; first lia. iSteps.
  Qed.

  Lemma chunk_foldr_spec_atomic Ψ l sz fn acc :
    {{{
      ▷ Ψ (Z.to_nat sz) acc None [] ∗
      □ (
        ∀ i acc (o : option val) vs,
        ⌜(S i + length vs)%nat = Z.to_nat sz⌝ -∗
        Ψ (S i) acc o vs -∗
        match o with
        | None =>
            chunk_au_load l i (λ v,
              ▷ Ψ (S i) acc (Some v) vs
            )
        | Some v =>
            WP fn v acc {{ acc,
              ▷ Ψ i acc None (v :: vs)
            }}
        end
      )
    }}}
      chunk_foldr #l #sz fn acc
    {{{ acc vs,
      RET acc;
      ⌜length vs = Z.to_nat sz⌝ ∗
      Ψ 0 acc None vs
    }}}.
  Proof.
    iIntros "%Φ (HΨ & #H) HΦ".
    wp_rec.
    wp_smart_apply (chunk_foldri_spec_atomic Ψ with "[$HΨ] HΦ"). clear acc. iIntros "!> %i %acc %o %vs %Hi HΨ".
    case_match; try wp_pures; iApply ("H" with "[//] HΨ").
  Qed.
  Lemma chunk_foldr_spec Ψ l dq vs (sz : Z) fn acc :
    Z.to_nat sz = length vs →
    {{{
      chunk_model l dq vs ∗
      ▷ Ψ (Z.to_nat sz) acc [] ∗
      □ (
        ∀ i v acc,
        ⌜vs !! i = Some v⌝ -∗
        Ψ (S i) acc (drop (S i) vs) -∗
        WP fn v acc {{ acc,
          ▷ Ψ i acc (v :: drop (S i) vs)
        }}
      )
    }}}
      chunk_foldr #l #sz fn acc
    {{{ acc,
      RET acc;
      Ψ 0 acc vs ∗
      chunk_model l dq vs
    }}}.
  Proof.
    iIntros "%Hsz %Φ (Hmodel & HΨ & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (chunk_foldri_spec Ψ with "[$Hmodel $HΨ] HΦ"); first done.
    iSteps.
  Qed.
  Lemma chunk_foldr_spec' Ψ l dq vs (sz : Z) fn acc :
    Z.to_nat sz = length vs →
    {{{
      chunk_model l dq vs ∗
      ▷ Ψ (Z.to_nat sz) acc [] ∗
      ( [∗ list] i ↦ v ∈ vs,
        ∀ acc,
        Ψ (S i) acc (drop (S i) vs) -∗
        WP fn v acc {{ acc,
          ▷ Ψ i acc (v :: drop (S i) vs)
        }}
      )
    }}}
      chunk_foldr #l #sz fn acc
    {{{ acc,
      RET acc;
      Ψ 0 acc vs ∗
      chunk_model l dq vs
    }}}.
  Proof.
    iIntros "%Hsz %Φ (Hmodel & HΨ & Hfn) HΦ".
    wp_rec.
    wp_smart_apply (chunk_foldri_spec' Ψ with "[$Hmodel $HΨ Hfn] HΦ"); first done.
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.

  Lemma chunk_iteri_spec_atomic Ψ l sz fn :
    {{{
      ▷ Ψ 0 [] None ∗
      □ (
        ∀ i vs (o : option val),
        ⌜i < Z.to_nat sz ∧ i = length vs⌝ -∗
        Ψ i vs o -∗
        match o with
        | None =>
            chunk_au_load l i (λ v,
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
      chunk_iteri #l #sz fn
    {{{ vs,
      RET ();
      ⌜length vs = Z.to_nat sz⌝ ∗
      Ψ (Z.to_nat sz) vs None
    }}}.
  Proof.
    iIntros "%Φ (HΨ & #H) HΦ".
    wp_rec.
    pose Ψ' i vs o acc := (
      ⌜acc = ()%V⌝ ∗
      Ψ i vs o
    )%I.
    wp_smart_apply (chunk_foldli_spec_atomic Ψ' with "[$HΨ]"); last iSteps.
    iStep. iIntros "!> %i %vs %o %acc %Hi (-> & HΨ)".
    destruct o as [v |].
    - wp_smart_apply (wp_wand with "(H [//] HΨ)").
      iSteps.
    - iApply (atomic_update_wand with "(H [//] HΨ)").
      iSteps.
  Qed.
  Lemma chunk_iteri_spec Ψ l dq vs (sz : Z) fn :
    Z.to_nat sz = length vs →
    {{{
      ▷ Ψ 0 [] ∗
      chunk_model l dq vs ∗
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
      chunk_iteri #l #sz fn
    {{{
      RET ();
      chunk_model l dq vs ∗
      Ψ (Z.to_nat sz) vs
    }}}.
  Proof.
    iIntros "%Hsz %Φ (HΨ & Hmodel & #Hfn) HΦ".
    wp_rec.
    pose Ψ' i vs acc := (
      ⌜acc = ()%V⌝ ∗
      Ψ i vs
    )%I.
    wp_smart_apply (chunk_foldli_spec Ψ' with "[$HΨ $Hmodel]"); [done | iSteps..].
  Qed.
  Lemma chunk_iteri_spec' Ψ l dq vs (sz : Z) fn :
    Z.to_nat sz = length vs →
    {{{
      ▷ Ψ 0 [] ∗
      chunk_model l dq vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i (take i vs) -∗
        WP fn #i v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ (S i) (take i vs ++ [v])
        }}
      )
    }}}
      chunk_iteri #l #sz fn
    {{{
      RET ();
      chunk_model l dq vs ∗
      Ψ (Z.to_nat sz) vs
    }}}.
  Proof.
    iIntros "%Hsz %Φ (HΨ & Hmodel & Hfn) HΦ".
    wp_rec.
    pose Ψ' i vs acc := (
      ⌜acc = ()%V⌝ ∗
      Ψ i vs
    )%I.
    wp_smart_apply (chunk_foldli_spec' Ψ' with "[$HΨ $Hmodel Hfn]"); [done | iSteps..].
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.
  Lemma chunk_iteri_spec_disentangled Ψ l dq vs (sz : Z) fn :
    Z.to_nat sz = length vs →
    {{{
      chunk_model l dq vs ∗
      □ (
        ∀ i v,
        ⌜vs !! i = Some v⌝ -∗
        WP fn #i v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ i v
        }}
      )
    }}}
      chunk_iteri #l #sz fn
    {{{
      RET ();
      chunk_model l dq vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Hsz %Φ (Hmodel & #Hfn) HΦ".
    pose (Ψ' i vs := (
      [∗ list] j ↦ v ∈ vs, Ψ j v
    )%I).
    wp_apply (chunk_iteri_spec Ψ' with "[$Hmodel]"); [done | | iSteps].
    rewrite /Ψ'. iSteps.
    rewrite big_sepL_snoc take_length Nat.min_l; last iSteps.
    eapply Nat.lt_le_incl, lookup_lt_Some. done.
  Qed.
  Lemma chunk_iteri_spec_disentangled' Ψ l dq vs (sz : Z) fn :
    Z.to_nat sz = length vs →
    {{{
      chunk_model l dq vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        WP fn #i v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ i v
        }}
      )
    }}}
      chunk_iteri #l #sz fn
    {{{
      RET ();
      chunk_model l dq vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Hsz %Φ (Hmodel & Hfn) HΦ".
    pose (Ψ' i vs := (
      [∗ list] j ↦ v ∈ vs, Ψ j v
    )%I).
    wp_apply (chunk_iteri_spec' Ψ' with "[$Hmodel Hfn]"); [done | | iSteps].
    rewrite /Ψ'. iSteps.
    iApply (big_sepL_impl with "Hfn"). iSteps.
    rewrite big_sepL_snoc take_length Nat.min_l; last iSteps.
    eapply Nat.lt_le_incl, lookup_lt_Some. done.
  Qed.

  Lemma chunk_iter_spec_atomic Ψ l sz fn :
    {{{
      ▷ Ψ 0 [] None ∗
      □ (
        ∀ i vs (o : option val),
        ⌜i < Z.to_nat sz ∧ i = length vs⌝ -∗
        Ψ i vs o -∗
        match o with
        | None =>
            chunk_au_load l i (λ v,
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
      chunk_iter #l #sz fn
    {{{ vs,
      RET ();
      ⌜length vs = Z.to_nat sz⌝ ∗
      Ψ (Z.to_nat sz) vs None
    }}}.
  Proof.
    iIntros "%Φ (HΨ & #H) HΦ".
    wp_rec.
    wp_smart_apply (chunk_iteri_spec_atomic Ψ with "[$HΨ] HΦ") as "!> %i %vs %o %Hi HΨ".
    case_match; try wp_pures; iApply ("H" with "[//] HΨ").
  Qed.
  Lemma chunk_iter_spec Ψ l dq vs (sz : Z) fn :
    Z.to_nat sz = length vs →
    {{{
      ▷ Ψ 0 [] ∗
      chunk_model l dq vs ∗
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
      chunk_iter #l #sz fn
    {{{
      RET ();
      chunk_model l dq vs ∗
      Ψ (Z.to_nat sz) vs
    }}}.
  Proof.
    iIntros "%Hsz %Φ (HΨ & Hmodel & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (chunk_iteri_spec Ψ with "[$HΨ $Hmodel] HΦ"); first done.
    iSteps.
  Qed.
  Lemma chunk_iter_spec' Ψ l dq vs (sz : Z) fn :
    Z.to_nat sz = length vs →
    {{{
      ▷ Ψ 0 [] ∗
      chunk_model l dq vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i (take i vs) -∗
        WP fn v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ (S i) (take i vs ++ [v])
        }}
      )
    }}}
      chunk_iter #l #sz fn
    {{{
      RET ();
      chunk_model l dq vs ∗
      Ψ (Z.to_nat sz) vs
    }}}.
  Proof.
    iIntros "%Hsz %Φ (HΨ & Hmodel & Hfn) HΦ".
    wp_rec.
    wp_smart_apply (chunk_iteri_spec' Ψ with "[$HΨ $Hmodel Hfn] HΦ"); first done.
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.
  Lemma chunk_iter_spec_disentangled Ψ l dq vs (sz : Z) fn :
    Z.to_nat sz = length vs →
    {{{
      chunk_model l dq vs ∗
      □ (
        ∀ i v,
        ⌜vs !! i = Some v⌝ -∗
        WP fn v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ i v
        }}
      )
    }}}
      chunk_iter #l #sz fn
    {{{
      RET ();
      chunk_model l dq vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Hsz %Φ (Hmodel & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (chunk_iteri_spec_disentangled Ψ with "[$Hmodel] HΦ"); first done.
    iSteps.
  Qed.
  Lemma chunk_iter_spec_disentangled' Ψ l dq vs (sz : Z) fn :
    Z.to_nat sz = length vs →
    {{{
      chunk_model l dq vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        WP fn v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ i v
        }}
      )
    }}}
      chunk_iter #l #sz fn
    {{{
      RET ();
      chunk_model l dq vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Hsz %Φ (Hmodel & Hfn) HΦ".
    wp_rec.
    wp_smart_apply (chunk_iteri_spec_disentangled' Ψ with "[$Hmodel Hfn] HΦ"); first done.
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.

  Lemma chunk_applyi_spec_atomic Ψ l sz fn :
    {{{
      ▷ Ψ 0 [] None [] ∗
      □ (
        ∀ i vs (o : option (val + val * val)) ws,
        ⌜i < Z.to_nat sz ∧ i = length vs ∧ length vs = length ws⌝ -∗
        Ψ i vs o ws -∗
        match o with
        | None =>
            chunk_au_load l i (λ v,
              ▷ Ψ i vs (Some $ inl v) ws
            )
        | Some (inl v) =>
            WP fn #i v {{ w,
              ▷ Ψ i vs (Some $ inr (v, w)) ws
            }}
        | Some (inr (v, w)) =>
            chunk_au_store l i w (
              ▷ Ψ (S i) (vs ++ [v]) None (ws ++ [w])
            )
        end
      )
    }}}
      chunk_applyi #l #sz fn
    {{{ vs ws,
      RET ();
      ⌜length vs = Z.to_nat sz ∧ length vs = length ws⌝ ∗
      Ψ (Z.to_nat sz) vs None ws
    }}}.
  Proof.
    iIntros "%Φ (HΨ & #H) HΦ".
    wp_rec.
    pose (Ψ' i vs o := (
      ∃ ws,
      ⌜length vs = length ws⌝ ∗
      Ψ i vs (inl <$> o) ws
    )%I).
    wp_smart_apply (chunk_iteri_spec_atomic Ψ' with "[HΨ]"); last iSteps.
    iSplitL "HΨ". { iExists []. iSteps. }
    iIntros "!> %i %vs %o (%Hi1 & %Hi2) (%ws & %Hws & HΨ)".
    destruct o as [v |].
    - wp_smart_apply (wp_wand with "(H [//] HΨ)") as "%w HΨ".
      wp_pures.
      iMod ("H" with "[//] HΨ") as "(%v' & H↦ & _ & H')".
      wp_store.
      iStep. iExists (ws ++ [w]).
      iMod ("H'" with "H↦") as "$".
      rewrite !app_length. iSteps.
    - iApply (atomic_update_wand with "(H [//] HΨ)").
      iSteps.
  Qed.
  Lemma chunk_applyi_spec Ψ l vs (sz : Z) fn :
    Z.to_nat sz = length vs →
    {{{
      ▷ Ψ 0 [] [] ∗
      chunk_model l (DfracOwn 1) vs ∗
      □ (
        ∀ i v ws,
        ⌜i = length ws ∧ vs !! i = Some v⌝ -∗
        Ψ i (take i vs) ws -∗
        WP fn #i v {{ w,
          ▷ Ψ (S i) (take i vs ++ [v]) (ws ++ [w])
        }}
      )
    }}}
      chunk_applyi #l #sz fn
    {{{ ws,
      RET ();
      ⌜length vs = length ws⌝ ∗
      chunk_model l (DfracOwn 1) ws ∗
      Ψ (Z.to_nat sz) vs ws
    }}}.
  Proof.
    iIntros "%Hsz %Φ (HΨ & Hmodel & #Hfn) HΦ".
    pose (Ψ' i vs_left o ws := (
      ⌜vs_left = take i vs⌝ ∗
      chunk_model l (DfracOwn 1) (ws ++ drop i vs) ∗
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
    wp_apply (chunk_applyi_spec_atomic Ψ' with "[$HΨ $Hmodel]"); last first.
    { iIntros "%vs_left %ws ((%Hvs_left_1 & %Hws) & (-> & Hmodel & HΨ))".
      rewrite Hsz firstn_all2; first lia. rewrite skipn_all2; first lia. rewrite right_id.
      iApply ("HΦ" $! ws). iSteps.
    }
    iSplit; first iSteps. repeat iSplit.
    iIntros "!> %i %vs_left %o %ws (%Hvs_left & %Hi & %Hws) (-> & Hmodel & HΨ)".
    feed pose proof (list_lookup_lookup_total_lt vs i); first lia.
    destruct o as [[v | (v & w)] |].
    - iDestruct "HΨ" as "(-> & HΨ)".
      wp_apply (wp_wand with "(Hfn [] HΨ)"); iSteps.
    - iDestruct "HΨ" as "(-> & HΨ)".
      assert ((ws ++ drop i vs) !! i = Some (vs !!! i)).
      { rewrite lookup_app_r; first lia.
        rewrite lookup_drop list_lookup_lookup_total_lt; first lia.
        repeat f_equal. lia.
      }
      iDestruct (chunk_model_update i with "Hmodel") as "(H↦ & Hmodel)"; [lia | done | lia |].
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
  Lemma chunk_applyi_spec' Ψ l vs (sz : Z) fn :
    Z.to_nat sz = length vs →
    {{{
      ▷ Ψ 0 [] [] ∗
      chunk_model l (DfracOwn 1) vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        ∀ ws,
        ⌜i = length ws⌝ -∗
        Ψ i (take i vs) ws -∗
        WP fn #i v {{ w,
          ▷ Ψ (S i) (take i vs ++ [v]) (ws ++ [w])
        }}
      )
    }}}
      chunk_applyi #l #sz fn
    {{{ ws,
      RET ();
      ⌜length vs = length ws⌝ ∗
      chunk_model l (DfracOwn 1) ws ∗
      Ψ (Z.to_nat sz) vs ws
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
  Lemma chunk_applyi_spec_disentangled Ψ l vs (sz : Z) fn :
    Z.to_nat sz = length vs →
    {{{
      chunk_model l (DfracOwn 1) vs ∗
      □ (
        ∀ i v,
        ⌜vs !! i = Some v⌝ -∗
        WP fn #i v {{ w,
          ▷ Ψ i w
        }}
      )
    }}}
      chunk_applyi #l #sz fn
    {{{ ws,
      RET ();
      ⌜length vs = length ws⌝ ∗
      chunk_model l (DfracOwn 1) ws ∗
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
  Lemma chunk_applyi_spec_disentangled' Ψ l vs (sz : Z) fn :
    Z.to_nat sz = length vs →
    {{{
      chunk_model l (DfracOwn 1) vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        WP fn #i v {{ w,
          ▷ Ψ i w
        }}
      )
    }}}
      chunk_applyi #l #sz fn
    {{{ ws,
      RET ();
      chunk_model l (DfracOwn 1) ws ∗
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

  Lemma chunk_apply_spec_atomic Ψ l sz fn :
    {{{
      ▷ Ψ 0 [] None [] ∗
      □ (
        ∀ i vs (o : option (val + val * val)) ws,
        ⌜i < Z.to_nat sz ∧ i = length vs ∧ length vs = length ws⌝ -∗
        Ψ i vs o ws -∗
        match o with
        | None =>
            chunk_au_load l i (λ v,
              ▷ Ψ i vs (Some $ inl v) ws
            )
        | Some (inl v) =>
            WP fn v {{ w,
              ▷ Ψ i vs (Some $ inr (v, w)) ws
            }}
        | Some (inr (v, w)) =>
            chunk_au_store l i w (
              ▷ Ψ (S i) (vs ++ [v]) None (ws ++ [w])
            )
        end
      )
    }}}
      chunk_apply #l #sz fn
    {{{ vs ws,
      RET ();
      ⌜length vs = Z.to_nat sz ∧ length vs = length ws⌝ ∗
      Ψ (Z.to_nat sz) vs None ws
    }}}.
  Proof.
    iIntros "%Φ (HΨ & #H) HΦ".
    wp_rec.
    wp_smart_apply (chunk_applyi_spec_atomic Ψ with "[$HΨ H] HΦ") as "!> %i %vs %o %ws (%Hi1 & %Hi2 & %Hws) HΨ".
    repeat case_match; try wp_pures; iApply ("H" with "[//] HΨ").
  Qed.
  Lemma chunk_apply_spec Ψ l vs (sz : Z) fn :
    Z.to_nat sz = length vs →
    {{{
      ▷ Ψ 0 [] [] ∗
      chunk_model l (DfracOwn 1) vs ∗
      □ (
        ∀ i v ws,
        ⌜i = length ws ∧ vs !! i = Some v⌝ -∗
        Ψ i (take i vs) ws -∗
        WP fn v {{ w,
          ▷ Ψ (S i) (take i vs ++ [v]) (ws ++ [w])
        }}
      )
    }}}
      chunk_apply #l #sz fn
    {{{ ws,
      RET ();
      ⌜length vs = length ws⌝ ∗
      chunk_model l (DfracOwn 1) ws ∗
      Ψ (Z.to_nat sz) vs ws
    }}}.
  Proof.
    iIntros "%Hsz %Φ (HΨ & Hmodel & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (chunk_applyi_spec Ψ with "[$HΨ $Hmodel] HΦ") as "!> %i %v %ws (%Hi & %Hlookup) HΨ"; first done.
    wp_smart_apply ("Hfn" with "[//] HΨ").
  Qed.
  Lemma chunk_apply_spec' Ψ l vs (sz : Z) fn :
    Z.to_nat sz = length vs →
    {{{
      ▷ Ψ 0 [] [] ∗
      chunk_model l (DfracOwn 1) vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        ∀ ws,
        ⌜i = length ws⌝ -∗
        Ψ i (take i vs) ws -∗
        WP fn v {{ w,
          ▷ Ψ (S i) (take i vs ++ [v]) (ws ++ [w])
        }}
      )
    }}}
      chunk_apply #l #sz fn
    {{{ ws,
      RET ();
      ⌜length vs = length ws⌝ ∗
      chunk_model l (DfracOwn 1) ws ∗
      Ψ (Z.to_nat sz) vs ws
    }}}.
  Proof.
    iIntros "%Hsz %Φ (HΨ & Hmodel & Hfn) HΦ".
    wp_rec.
    wp_smart_apply (chunk_applyi_spec' Ψ with "[$HΨ $Hmodel Hfn] HΦ"); first done.
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.
  Lemma chunk_apply_spec_disentangled Ψ l vs (sz : Z) fn :
    Z.to_nat sz = length vs →
    {{{
      chunk_model l (DfracOwn 1) vs ∗
      □ (
        ∀ i v,
        ⌜vs !! i = Some v⌝ -∗
        WP fn v {{ w,
          ▷ Ψ i w
        }}
      )
    }}}
      chunk_apply #l #sz fn
    {{{ ws,
      RET ();
      ⌜length vs = length ws⌝ ∗
      chunk_model l (DfracOwn 1) ws ∗
      ( [∗ list] i ↦ w ∈ ws,
        Ψ i w
      )
    }}}.
  Proof.
    iIntros "%Hsz %Φ (Hmodel & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (chunk_applyi_spec_disentangled Ψ with "[$Hmodel] HΦ"); first done.
    iSteps.
  Qed.
  Lemma chunk_apply_spec_disentangled' Ψ l vs (sz : Z) fn :
    Z.to_nat sz = length vs →
    {{{
      chunk_model l (DfracOwn 1) vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        WP fn v {{ w,
          ▷ Ψ i w
        }}
      )
    }}}
      chunk_apply #l #sz fn
    {{{ ws,
      RET ();
      chunk_model l (DfracOwn 1) ws ∗
      ( [∗ list] i ↦ w ∈ ws,
        Ψ i w
      )
    }}}.
  Proof.
    iIntros "%Hsz %Φ (Hmodel & Hfn) HΦ".
    wp_rec.
    wp_smart_apply (chunk_applyi_spec_disentangled' Ψ with "[$Hmodel Hfn] HΦ"); first done.
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.

  Lemma chunk_initi_spec Ψ sz fn :
    {{{
      ▷ Ψ 0 [] ∗
      □ (
        ∀ i vs,
        ⌜i < Z.to_nat sz ∧ i = length vs⌝ -∗
        Ψ i vs -∗
        WP fn #i {{ v,
          ▷ Ψ (S i) (vs ++ [v])
        }}
      )
    }}}
      chunk_initi #sz fn
    {{{ l vs,
      RET #l;
      ⌜length vs = Z.to_nat sz⌝ ∗
      chunk_model l (DfracOwn 1) vs ∗
      Ψ (Z.to_nat sz) vs ∗
      if decide (0 < sz)%Z then meta_token l ⊤ else True
    }}}.
  Proof.
    iIntros "%Φ (HΨ & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (chunk_make_spec with "[//]") as "%l (Hmodel & Hmeta)".
    pose Ψ' i vs' vs := (
      Ψ i vs
    )%I.
    wp_smart_apply (chunk_applyi_spec Ψ' with "[$HΨ $Hmodel]") as "%vs (%Hvs & Hmodel & HΨ)"; last 1 first.
    { wp_pures.
      iApply ("HΦ" $! _ vs).
      rewrite replicate_length in Hvs. iSteps.
    } {
      rewrite replicate_length. lia.
    }
    iIntros "!> %i %v %vs (%Hi & %Hv) HΨ". apply lookup_replicate in Hv.
    iSteps.
  Qed.
  Lemma chunk_initi_spec' Ψ sz fn :
    {{{
      ▷ Ψ 0 [] ∗
      ( [∗ list] i ∈ seq 0 (Z.to_nat sz),
        ∀ vs,
        ⌜i = length vs⌝ -∗
        Ψ i vs -∗
        WP fn #i {{ v,
          ▷ Ψ (S i) (vs ++ [v])
        }}
      )
    }}}
      chunk_initi #sz fn
    {{{ l vs,
      RET #l;
      ⌜length vs = Z.to_nat sz⌝ ∗
      chunk_model l (DfracOwn 1) vs ∗
      Ψ (Z.to_nat sz) vs ∗
      if decide (0 < sz)%Z then meta_token l ⊤ else True
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hfn) HΦ".
    match goal with |- context [big_opL bi_sep (λ _, ?Ξ') _] => set Ξ := Ξ' end.
    pose (Ψ' i vs := (
      Ψ i vs ∗
      [∗ list] j ∈ seq i (Z.to_nat sz - i), Ξ j
    )%I).
    wp_apply (chunk_initi_spec Ψ' with "[$HΨ Hfn]"); last iSteps.
    rewrite Nat.sub_0_r. iFrame. iIntros "!> %i %vs (%Hi1 & %Hi2) (HΨ & HΞ)".
    destruct (Nat.lt_exists_pred 0 (Z.to_nat sz - i)) as (k & Hk & _); first lia. rewrite Hk.
    rewrite -cons_seq. iDestruct "HΞ" as "(Hfn & HΞ)".
    wp_apply (wp_wand with "(Hfn [//] HΨ)"). iSteps.
    rewrite Nat.sub_succ_r Hk //.
  Qed.
  Lemma chunk_initi_spec_disentangled Ψ sz fn :
    {{{
      □ (
        ∀ i,
        ⌜i < Z.to_nat sz⌝ -∗
        WP fn #i {{ v,
          ▷ Ψ i v
        }}
      )
    }}}
      chunk_initi #sz fn
    {{{ l vs,
      RET #l;
      ⌜length vs = Z.to_nat sz⌝ ∗
      chunk_model l (DfracOwn 1) vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      ) ∗
      if decide (0 < sz)%Z then meta_token l ⊤ else True
    }}}.
  Proof.
    iIntros "%Φ #Hfn HΦ".
    pose (Ψ' i vs := (
      [∗ list] j ↦ v ∈ vs, Ψ j v
    )%I).
    wp_apply (chunk_initi_spec Ψ'); last iSteps.
    rewrite /Ψ'. iSteps.
    rewrite big_sepL_snoc. iSteps.
  Qed.
  Lemma chunk_initi_spec_disentangled' Ψ sz fn :
    {{{
      ( [∗ list] i ∈ seq 0 (Z.to_nat sz),
        WP fn #i {{ v,
          ▷ Ψ i v
        }}
      )
    }}}
      chunk_initi #sz fn
    {{{ l vs,
      RET #l;
      ⌜length vs = Z.to_nat sz⌝ ∗
      chunk_model l (DfracOwn 1) vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      ) ∗
      if decide (0 < sz)%Z then meta_token l ⊤ else True
    }}}.
  Proof.
    iIntros "%Φ Hfn HΦ".
    pose (Ψ' i vs := (
      [∗ list] j ↦ v ∈ vs, Ψ j v
    )%I).
    wp_apply (chunk_initi_spec' Ψ' with "[Hfn]"); last iSteps.
    rewrite /Ψ'. iSteps.
    iApply (big_sepL_impl with "Hfn"). iSteps.
    rewrite big_sepL_snoc. iSteps.
  Qed.

  Lemma chunk_init_spec Ψ sz fn :
    {{{
      ▷ Ψ 0 [] ∗
      □ (
        ∀ i vs,
        ⌜i < Z.to_nat sz ∧ i = length vs⌝ -∗
        Ψ i vs -∗
        WP fn () {{ v,
          ▷ Ψ (S i) (vs ++ [v])
        }}
      )
    }}}
      chunk_init #sz fn
    {{{ l vs,
      RET #l;
      ⌜length vs = Z.to_nat sz⌝ ∗
      chunk_model l (DfracOwn 1) vs ∗
      Ψ (Z.to_nat sz) vs ∗
      if decide (0 < sz)%Z then meta_token l ⊤ else True
    }}}.
  Proof.
    iIntros "%Φ (HΨ & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (chunk_initi_spec Ψ with "[$HΨ] HΦ").
    iSteps.
  Qed.
  Lemma chunk_init_spec' Ψ sz fn :
    {{{
      ▷ Ψ 0 [] ∗
      ( [∗ list] i ∈ seq 0 (Z.to_nat sz),
        ∀ vs,
        ⌜i = length vs⌝ -∗
        Ψ i vs -∗
        WP fn () {{ v,
          ▷ Ψ (S i) (vs ++ [v])
        }}
      )
    }}}
      chunk_init #sz fn
    {{{ l vs,
      RET #l;
      ⌜length vs = Z.to_nat sz⌝ ∗
      chunk_model l (DfracOwn 1) vs ∗
      Ψ (Z.to_nat sz) vs ∗
      if decide (0 < sz)%Z then meta_token l ⊤ else True
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hfn) HΦ".
    wp_rec.
    wp_smart_apply (chunk_initi_spec' Ψ with "[$HΨ Hfn] HΦ").
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.
  Lemma chunk_init_spec_disentangled Ψ sz fn :
    {{{
      □ (
        ∀ i,
        ⌜i < Z.to_nat sz⌝ -∗
        WP fn () {{ v,
          ▷ Ψ i v
        }}
      )
    }}}
      chunk_init #sz fn
    {{{ l vs,
      RET #l;
      ⌜length vs = Z.to_nat sz⌝ ∗
      chunk_model l (DfracOwn 1) vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      ) ∗
      if decide (0 < sz)%Z then meta_token l ⊤ else True
    }}}.
  Proof.
    iIntros "%Φ #Hfn HΦ".
    wp_rec.
    wp_smart_apply (chunk_initi_spec_disentangled Ψ with "[] HΦ").
    iSteps.
  Qed.
  Lemma chunk_init_spec_disentangled' Ψ sz fn :
    {{{
      ( [∗ list] i ∈ seq 0 (Z.to_nat sz),
        WP fn () {{ v,
          ▷ Ψ i v
        }}
      )
    }}}
      chunk_init #sz fn
    {{{ l vs,
      RET #l;
      ⌜length vs = Z.to_nat sz⌝ ∗
      chunk_model l (DfracOwn 1) vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      ) ∗
      if decide (0 < sz)%Z then meta_token l ⊤ else True
    }}}.
  Proof.
    iIntros "%Φ Hfn HΦ".
    wp_rec.
    wp_smart_apply (chunk_initi_spec_disentangled' Ψ with "[Hfn] HΦ").
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.

  Lemma chunk_mapi_spec_atomic Ψ l sz fn :
    {{{
      ▷ Ψ 0 [] None [] ∗
      □ (
        ∀ i vs (o : option val) ws,
        ⌜i < Z.to_nat sz ∧ i = length vs ∧ length vs = length ws⌝ -∗
        Ψ i vs o ws -∗
        match o with
        | None =>
            chunk_au_load l i (λ v,
              ▷ Ψ i vs (Some v) ws
            )
        | Some v =>
            WP fn #i v {{ w,
              ▷ Ψ (S i) (vs ++ [v]) None (ws ++ [w])
            }}
        end
      )
    }}}
      chunk_mapi #l #sz fn
    {{{ l' vs ws,
      RET #l';
      ⌜length vs = Z.to_nat sz ∧ length vs = length ws⌝ ∗
      chunk_model l' (DfracOwn 1) ws ∗
      Ψ (Z.to_nat sz) vs None ws ∗
      if decide (0 < sz)%Z then meta_token l' ⊤ else True
    }}}.
  Proof.
    iIntros "%Φ (HΨ & #H) HΦ".
    wp_rec.
    pose Ψ' i ws := (
      ∃ vs,
      ⌜length vs = length ws⌝ ∗
      Ψ i vs None ws
    )%I.
    wp_smart_apply (chunk_initi_spec Ψ' with "[HΨ]") as "%l' %ws (%Hws & Hmodel & (%vs & %Hvs & HΨ) & Hmeta)"; last first.
    { iApply ("HΦ" with "[$Hmodel $HΨ $Hmeta]").
      iSteps.
    }
    iSplit. { iExists []. iSteps. }
    iIntros "!> %i %ws (%Hi1 & %Hi2) (%vs & %Hvs & HΨ)".
    wp_pures credit:"H£". wp_bind (!_)%E.
    iMod ("H" with "[] HΨ") as "(%dq & %v & H↦ & _ & HΨ)"; first iSteps.
    wp_load.
    iMod ("HΨ" with "H↦") as "HΨ". iModIntro.
    iMod (lc_fupd_elim_later with "H£ HΨ") as "HΨ".
    wp_apply (wp_wand with "(H [] HΨ)") as "%w HΨ"; first iSteps.
    iExists (vs ++ [v]). iFrame. rewrite !app_length. iSteps.
  Qed.
  Lemma chunk_mapi_spec Ψ l dq vs (sz : Z) fn :
    Z.to_nat sz = length vs →
    {{{
      ▷ Ψ 0 [] [] ∗
      chunk_model l dq vs ∗
      □ (
        ∀ i v ws,
        ⌜vs !! i = Some v ∧ i = length ws⌝ -∗
        Ψ i (take i vs) ws -∗
        WP fn #i v {{ w,
          ▷ Ψ (S i) (take i vs ++ [v]) (ws ++ [w])
        }}
      )
    }}}
      chunk_mapi #l #sz fn
    {{{ l' ws,
      RET #l';
      ⌜length ws = Z.to_nat sz⌝ ∗
      chunk_model l dq vs ∗
      chunk_model l' (DfracOwn 1) ws ∗
      Ψ (Z.to_nat sz) vs ws ∗
      if decide (0 < sz)%Z then meta_token l' ⊤ else True
    }}}.
  Proof.
    iIntros "%Hsz %Φ (HΨ & Hmodel & #Hfn) HΦ".
    pose (Ψ' i vs_left o ws := (
      ⌜vs_left = take i vs⌝ ∗
      chunk_model l dq vs ∗
      Ψ i vs_left ws ∗
      ⌜from_option (λ v, v = vs !!! i) True o⌝%I
    )%I).
    wp_apply (chunk_mapi_spec_atomic Ψ' with "[$HΨ $Hmodel]") as "%l' %vs_left %ws ((%Hvs_left & %Hws) & Hmodel' & (-> & Hmodel & HΨ & _) & Hmeta)"; last first.
    { rewrite /Ψ' firstn_all2 in Hws |- *; first lia.
      rewrite -Hsz in Hws. apply symmetry in Hws.
      iSteps.
    }
    iSplitR; first iSteps.
    iIntros "!> %i %vs_left %o %ws (%Hi1 & %Hi2 & %Hws) (-> & Hmodel & HΨ & %Ho)".
    feed pose proof (list_lookup_lookup_total_lt vs i); first lia.
    destruct o as [v |].
    - rewrite Ho.
      wp_apply (wp_wand with "(Hfn [] HΨ)") as "%w HΨ"; first iSteps. iFrame.
      erewrite take_S_r; done.
    - iDestruct (chunk_model_lookup_acc i with "Hmodel") as "(H↦ & Hmodel)"; [lia | done | lia |].
      iAuIntro. iAaccIntro with "H↦"; iSteps.
  Qed.
  Lemma chunk_mapi_spec' Ψ l dq vs (sz : Z) fn :
    Z.to_nat sz = length vs →
    {{{
      ▷ Ψ 0 [] [] ∗
      chunk_model l dq vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        ∀ ws,
        ⌜i = length ws⌝ -∗
        Ψ i (take i vs) ws -∗
        WP fn #i v {{ w,
          ▷ Ψ (S i) (take i vs ++ [v]) (ws ++ [w])
        }}
      )
    }}}
      chunk_mapi #l #sz fn
    {{{ l' ws,
      RET #l';
      ⌜length ws = Z.to_nat sz⌝ ∗
      chunk_model l dq vs ∗
      chunk_model l' (DfracOwn 1) ws ∗
      Ψ (Z.to_nat sz) vs ws ∗
      if decide (0 < sz)%Z then meta_token l' ⊤ else True
    }}}.
  Proof.
    iIntros "%Hsz %Φ (HΨ & Hmodel & Hfn) HΦ".
    match goal with |- context [big_opL bi_sep ?Ξ' _] => set Ξ := Ξ' end.
    pose (Ψ' i vs_left ws := (
      Ψ i vs_left ws ∗
      [∗ list] j ↦ v ∈ drop i vs, Ξ (i + j) v
    )%I).
    wp_apply (chunk_mapi_spec Ψ' with "[$HΨ $Hmodel $Hfn]"); [done | | iSteps].
    iIntros "!> %i %v %ws (%Hlookup & %Hi) (HΨ & HΞ)".
    erewrite drop_S; last done.
    iDestruct "HΞ" as "(Hfn & HΞ)".
    rewrite Nat.add_0_r. setoid_rewrite Nat.add_succ_r. iSteps.
  Qed.
  Lemma chunk_mapi_spec_disentangled Ψ l dq vs (sz : Z) fn :
    Z.to_nat sz = length vs →
    {{{
      chunk_model l dq vs ∗
      □ (
        ∀ i v,
        ⌜vs !! i = Some v⌝ -∗
        WP fn #i v {{ w,
          ▷ Ψ i v w
        }}
      )
    }}}
      chunk_mapi #l #sz fn
    {{{ l' ws,
      RET #l';
      ⌜length ws = Z.to_nat sz⌝ ∗
      chunk_model l dq vs ∗
      chunk_model l' (DfracOwn 1) ws ∗
      ( [∗ list] i ↦ v; w ∈ vs; ws,
        Ψ i v w
      ) ∗
      if decide (0 < sz)%Z then meta_token l' ⊤ else True
    }}}.
  Proof.
    iIntros "%Hsz %Φ (Hmodel & #Hfn) HΦ".
    pose Ψ' i vs_left ws := (
      [∗ list] j ↦ v; w ∈ vs_left; ws, Ψ j v w
    )%I.
    wp_apply (chunk_mapi_spec Ψ' with "[$Hmodel]"); [done | | iSteps].
    rewrite /Ψ'. iSteps.
    rewrite big_sepL2_snoc take_length Nat.min_l; last iSteps.
    eapply Nat.lt_le_incl, lookup_lt_Some. done.
  Qed.
  Lemma chunk_mapi_spec_disentangled' Ψ l dq vs (sz : Z) fn :
    Z.to_nat sz = length vs →
    {{{
      chunk_model l dq vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        WP fn #i v {{ w,
          ▷ Ψ i v w
        }}
      )
    }}}
      chunk_mapi #l #sz fn
    {{{ l' ws,
      RET #l';
      ⌜length ws = Z.to_nat sz⌝ ∗
      chunk_model l dq vs ∗
      chunk_model l' (DfracOwn 1) ws ∗
      ( [∗ list] i ↦ v; w ∈ vs; ws,
        Ψ i v w
      ) ∗
      if decide (0 < sz)%Z then meta_token l' ⊤ else True
    }}}.
  Proof.
    iIntros "%Hsz %Φ (Hmodel & Hfn) HΦ".
    pose Ψ' i vs_left ws := (
      [∗ list] j ↦ v; w ∈ vs_left; ws, Ψ j v w
    )%I.
    wp_apply (chunk_mapi_spec' Ψ' with "[$Hmodel Hfn]"); [done | | iSteps].
    rewrite /Ψ'. iSteps.
    iApply (big_sepL_impl with "Hfn"). iSteps.
    rewrite big_sepL2_snoc take_length Nat.min_l; last iSteps.
    eapply Nat.lt_le_incl, lookup_lt_Some. done.
  Qed.

  Lemma chunk_map_spec_atomic Ψ l sz fn :
    {{{
      ▷ Ψ 0 [] None [] ∗
      □ (
        ∀ i vs (o : option val) ws,
        ⌜i < Z.to_nat sz ∧ i = length vs ∧ length vs = length ws⌝ -∗
        Ψ i vs o ws -∗
        match o with
        | None =>
            chunk_au_load l i (λ v,
              ▷ Ψ i vs (Some v) ws
            )
        | Some v =>
            WP fn v {{ w,
              ▷ Ψ (S i) (vs ++ [v]) None (ws ++ [w])
            }}
        end
      )
    }}}
      chunk_map #l #sz fn
    {{{ l' vs ws,
      RET #l';
      ⌜length vs = Z.to_nat sz ∧ length vs = length ws⌝ ∗
      chunk_model l' (DfracOwn 1) ws ∗
      Ψ (Z.to_nat sz) vs None ws ∗
      if decide (0 < sz)%Z then meta_token l' ⊤ else True
    }}}.
  Proof.
    iIntros "%Φ (HΨ & #H) HΦ".
    wp_rec.
    wp_smart_apply (chunk_mapi_spec_atomic Ψ with "[$HΨ H] HΦ") as "!> %i %vs %o %ws (%Hi1 & %Hi2 & %Hws) HΨ".
    case_match; try wp_pures; iApply ("H" with "[//] HΨ").
  Qed.
  Lemma chunk_map_spec Ψ l dq vs (sz : Z) fn :
    Z.to_nat sz = length vs →
    {{{
      ▷ Ψ 0 [] [] ∗
      chunk_model l dq vs ∗
      □ (
        ∀ i v ws,
        ⌜vs !! i = Some v ∧ i = length ws⌝ -∗
        Ψ i (take i vs) ws -∗
        WP fn v {{ w,
          ▷ Ψ (S i) (take i vs ++ [v]) (ws ++ [w])
        }}
      )
    }}}
      chunk_map #l #sz fn
    {{{ l' ws,
      RET #l';
      ⌜length ws = Z.to_nat sz⌝ ∗
      chunk_model l dq vs ∗
      chunk_model l' (DfracOwn 1) ws ∗
      Ψ (Z.to_nat sz) vs ws ∗
      if decide (0 < sz)%Z then meta_token l' ⊤ else True
    }}}.
  Proof.
    iIntros "%Hsz %Φ (HΨ & Hmodel & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (chunk_mapi_spec Ψ with "[$HΨ $Hmodel] HΦ"); first done.
    iSteps.
  Qed.
  Lemma chunk_map_spec' Ψ l dq vs (sz : Z) fn :
    Z.to_nat sz = length vs →
    {{{
      ▷ Ψ 0 [] [] ∗
      chunk_model l dq vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        ∀ ws,
        ⌜i = length ws⌝ -∗
        Ψ i (take i vs) ws -∗
        WP fn v {{ w,
          ▷ Ψ (S i) (take i vs ++ [v]) (ws ++ [w])
        }}
      )
    }}}
      chunk_map #l #sz fn
    {{{ l' ws,
      RET #l';
      ⌜length ws = Z.to_nat sz⌝ ∗
      chunk_model l dq vs ∗
      chunk_model l' (DfracOwn 1) ws ∗
      Ψ (Z.to_nat sz) vs ws ∗
      if decide (0 < sz)%Z then meta_token l' ⊤ else True
    }}}.
  Proof.
    iIntros "%Hsz %Φ (HΨ & Hmodel & Hfn) HΦ".
    wp_rec.
    wp_smart_apply (chunk_mapi_spec' Ψ with "[$HΨ $Hmodel Hfn] HΦ"); first done.
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.
  Lemma chunk_map_spec_disentangled Ψ l dq vs (sz : Z) fn :
    Z.to_nat sz = length vs →
    {{{
      chunk_model l dq vs ∗
      □ (
        ∀ i v,
        ⌜vs !! i = Some v⌝ -∗
        WP fn v {{ w,
          ▷ Ψ i v w
        }}
      )
    }}}
      chunk_map #l #sz fn
    {{{ l' ws,
      RET #l';
      ⌜length ws = Z.to_nat sz⌝ ∗
      chunk_model l dq vs ∗
      chunk_model l' (DfracOwn 1) ws ∗
      ( [∗ list] i ↦ v; w ∈ vs; ws,
        Ψ i v w
      ) ∗
      if decide (0 < sz)%Z then meta_token l' ⊤ else True
    }}}.
  Proof.
    iIntros "%Hsz %Φ (Hmodel & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (chunk_mapi_spec_disentangled Ψ with "[$Hmodel] HΦ"); first done.
    iSteps.
  Qed.
  Lemma chunk_map_spec_disentangled' Ψ l dq vs (sz : Z) fn :
    Z.to_nat sz = length vs →
    {{{
      chunk_model l dq vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        WP fn v {{ w,
          ▷ Ψ i v w
        }}
      )
    }}}
      chunk_map #l #sz fn
    {{{ l' ws,
      RET #l';
      ⌜length ws = Z.to_nat sz⌝ ∗
      chunk_model l dq vs ∗
      chunk_model l' (DfracOwn 1) ws ∗
      ( [∗ list] i ↦ v; w ∈ vs; ws,
        Ψ i v w
      ) ∗
      if decide (0 < sz)%Z then meta_token l' ⊤ else True
    }}}.
  Proof.
    iIntros "%Hsz %Φ (Hmodel & Hfn) HΦ".
    wp_rec.
    wp_smart_apply (chunk_mapi_spec_disentangled' Ψ with "[$Hmodel Hfn] HΦ"); first done.
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.

  Lemma chunk_copy_spec_atomic Ψ l1 l2 sz :
    {{{
      ▷ Ψ 0 [] None ∗
      □ (
        ∀ i vs o,
        ⌜i < Z.to_nat sz ∧ i = length vs⌝ -∗
        Ψ i vs o -∗
        match o with
        | None =>
            chunk_au_load l1 i (λ v,
              ▷ Ψ i vs (Some v)
            )
        | Some v =>
            chunk_au_store l2 i v (
              ▷ Ψ (S i) (vs ++ [v]) None
            )
        end
      )
    }}}
      chunk_copy #l1 #sz #l2
    {{{ vs,
      RET ();
      ⌜length vs = Z.to_nat sz⌝ ∗
      Ψ (Z.to_nat sz) vs None
    }}}.
  Proof.
    iIntros "%Φ (HΨ & #H) HΦ".
    wp_rec.
    wp_smart_apply (chunk_iteri_spec_atomic Ψ with "[$HΨ]"); last iSteps. iIntros "!> %i %vs %o (%Hi1 & %Hi2) HΨ".
    destruct o as [v |].
    - wp_pures.
      iMod ("H" with "[] HΨ") as "(%v' & H↦ & _ & HΨ)"; first iSteps.
      wp_store.
      iStep. iApply ("HΨ" with "H↦").
    - iApply ("H" with "[//] HΨ").
  Qed.
  Lemma chunk_copy_spec l1 dq1 vs1 (sz : Z) l2 vs2 :
    Z.to_nat sz = length vs1 →
    Z.to_nat sz = length vs2 →
    {{{
      chunk_model l1 dq1 vs1 ∗
      chunk_model l2 (DfracOwn 1) vs2
    }}}
      chunk_copy #l1 #sz #l2
    {{{
      RET ();
      chunk_model l1 dq1 vs1 ∗
      chunk_model l2 (DfracOwn 1) vs1
    }}}.
  Proof.
    iIntros "%Hvs1 %Hvs2 %Φ (Hmodel1 & Hmodel2) HΦ".
    pose (Ψ i vs1_done o := (
      ⌜vs1_done = take i vs1⌝ ∗
      chunk_model l1 dq1 vs1 ∗
      chunk_model l2 (DfracOwn 1) (vs1_done ++ drop i vs2) ∗
      ⌜from_option (λ v1, vs1 !! i = Some v1) True o⌝
    )%I).
    wp_apply (chunk_copy_spec_atomic Ψ with "[$Hmodel1 $Hmodel2]") as "%vs1_done (_ & (-> & Hmodel1 & Hmodel2 & _))"; last first.
    { iApply ("HΦ" with "[$Hmodel1 Hmodel2]").
      rewrite firstn_all2; first lia. rewrite skipn_all2; first lia. rewrite right_id //.
    }
    iSplit; first iSteps.
    iIntros "!> %i %vs1_done %o (%Hi & _) (-> & Hmodel1 & Hmodel2 & %Hlookup)".
    feed pose proof (list_lookup_lookup_total_lt vs2 i); first lia.
    destruct o as [v1 |].
    - feed pose proof (list_lookup_lookup_total_lt vs2 i); first lia.
      iDestruct (chunk_model_update i i with "Hmodel2") as "(H↦2 & Hmodel2)"; [lia | | lia |].
      { rewrite lookup_app_r take_length Nat.min_l //; try lia.
        rewrite Nat.sub_diag lookup_drop right_id list_lookup_lookup_total_lt //. lia.
      }
      iAuIntro. iAaccIntro with "H↦2"; first iSteps. iIntros "H↦2".
      iDestruct ("Hmodel2" with "H↦2") as "Hmodel2".
      iFrame. iSplitR. { erewrite take_S_r; done. }
      rewrite insert_app_r_alt take_length Nat.min_l //; try lia.
      rewrite Nat.sub_diag. erewrite drop_S; last done. rewrite -(assoc (++)).
      iSteps.
    - feed pose proof (list_lookup_lookup_total_lt vs1 i); first lia.
      iDestruct (chunk_model_lookup_acc i with "Hmodel1") as "(H↦1 & Hmodel1)"; [lia | done | lia |].
      iAuIntro. iAaccIntro with "H↦1"; iSteps.
  Qed.

  Lemma chunk_resize_spec_atomic Ψ l sz sz' (n : Z) v' :
    Z.to_nat n ≤ Z.to_nat sz →
    Z.to_nat n ≤ Z.to_nat sz' →
    {{{
      ▷ Ψ 0 [] ∗
      □ (
        ∀ i vs,
        ⌜i < Z.to_nat n ∧ i = length vs⌝ -∗
        Ψ i vs -∗
        chunk_au_load l i (λ v,
          ▷ Ψ (S i) (vs ++ [v])
        )
      )
    }}}
      chunk_resize #l #sz #sz' #n v'
    {{{ l' vs,
      RET #l';
      ⌜length vs = Z.to_nat n⌝ ∗
      chunk_model l' (DfracOwn 1) (vs ++ replicate (Z.to_nat sz' - Z.to_nat n) v') ∗
      Ψ (Z.to_nat n) vs ∗
      if decide (0 < sz')%Z then meta_token l' ⊤ else True
    }}}.
  Proof.
    iIntros "%Hn1 %Hn2 %Φ (HΨ & #H) HΦ".
    wp_rec.
    wp_smart_apply (chunk_make_spec with "[//]") as "%l' (Hmodel' & Hmeta)".
    pose Ψ' i vs o := (
      chunk_model l' (DfracOwn 1) (vs ++ replicate (Z.to_nat sz' - i) v') ∗
      from_option (λ v, Ψ (S i) (vs ++ [v])) (Ψ i vs) o
    )%I.
    wp_smart_apply (chunk_copy_spec_atomic Ψ' with "[Hmodel' $HΨ]"); last iSteps.
    iSplit.
    - rewrite Nat.sub_0_r. iSteps.
    - iIntros "!> %i %vs %o (%Hi1 & %Hi2) (Hmodel' & HΨ)".
      destruct o as [v |].
      + iDestruct (chunk_model_update i i with "Hmodel'") as "(H↦ & Hmodel')"; [lia | | lia |].
        { rewrite lookup_app_r; first lia. rewrite lookup_replicate. naive_solver lia. }
        iAuIntro. iAaccIntro with "H↦"; first iSteps. iIntros "H↦ !>". iFrame.
        iDestruct ("Hmodel'" with "H↦") as "Hmodel'".
        rewrite insert_app_r_alt; first lia. rewrite insert_replicate_lt; first lia.
        rewrite Hi2 Nat.sub_diag /= Nat.sub_1_r -Nat.sub_succ_r -(assoc (++)).
        iSteps.
      + iApply (atomic_update_wand with "(H [//] HΨ)").
        iSteps.
  Qed.
  Lemma chunk_resize_spec l dq vs (sz : Z) sz' (n : Z) v' :
    Z.to_nat sz = length vs →
    Z.to_nat n ≤ Z.to_nat sz →
    Z.to_nat n ≤ Z.to_nat sz' →
    {{{
      chunk_model l dq vs
    }}}
      chunk_resize #l #sz #sz' #n v'
    {{{ l',
      RET #l';
      chunk_model l dq vs ∗
      chunk_model l' (DfracOwn 1) (take (Z.to_nat n) vs ++ replicate (Z.to_nat sz' - Z.to_nat n) v') ∗
      if decide (0 < sz')%Z then meta_token l' ⊤ else True
    }}}.
  Proof.
    iIntros "%Hsz %Hn1 %Hn2 %Φ Hmodel HΦ".
    pose Ψ i vs_left := (
      ⌜vs_left = take i vs⌝ ∗
      chunk_model l dq vs
    )%I.
    wp_apply (chunk_resize_spec_atomic Ψ with "[$Hmodel]"); [done.. | | iSteps].
    iStep. iIntros "!> %i %vs_left (%Hi1 & %Hi2) (-> & Hmodel)".
    feed pose proof (list_lookup_lookup_total_lt vs i); first lia.
    iDestruct (chunk_model_lookup_acc i with "Hmodel") as "(H↦ & Hmodel)"; [lia | done | lia |].
    iAuIntro. iAaccIntro with "H↦"; first iSteps.
    rewrite -take_S_r //. iSteps.
  Qed.

  Lemma chunk_grow_spec_atomic Ψ l sz sz' v' :
    Z.to_nat sz ≤ Z.to_nat sz' →
    {{{
      ▷ Ψ 0 [] ∗
      □ (
        ∀ i vs,
        ⌜i < Z.to_nat sz ∧ i = length vs⌝ -∗
        Ψ i vs -∗
        chunk_au_load l i (λ v,
          ▷ Ψ (S i) (vs ++ [v])
        )
      )
    }}}
      chunk_grow #l #sz #sz' v'
    {{{ l' vs,
      RET #l';
      ⌜length vs = Z.to_nat sz⌝ ∗
      chunk_model l' (DfracOwn 1) (vs ++ replicate (Z.to_nat sz' - Z.to_nat sz) v') ∗
      Ψ (Z.to_nat sz) vs ∗
      if decide (0 < sz')%Z then meta_token l' ⊤ else True
    }}}.
  Proof.
    iIntros "%Hsz %Φ (HΨ & #H) HΦ".
    wp_rec.
    wp_smart_apply (chunk_resize_spec_atomic Ψ with "[$HΨ $H]"); [done.. | iSteps].
  Qed.
  Lemma chunk_grow_spec l dq vs (sz : Z) sz' v' :
    Z.to_nat sz = length vs →
    Z.to_nat sz ≤ Z.to_nat sz' →
    {{{
      chunk_model l dq vs
    }}}
      chunk_grow #l #sz #sz' v'
    {{{ l',
      RET #l';
      chunk_model l dq vs ∗
      chunk_model l' (DfracOwn 1) (vs ++ replicate (Z.to_nat sz' - Z.to_nat sz) v') ∗
      if decide (0 < sz')%Z then meta_token l' ⊤ else True
    }}}.
  Proof.
    iIntros "%Hsz %Hsz' %Φ Hmodel HΦ".
    wp_rec.
    wp_smart_apply (chunk_resize_spec with "Hmodel"); [done.. |].
    iSteps. rewrite firstn_all2; first lia. iSteps.
  Qed.

  Lemma chunk_shrink_spec_atomic Ψ l sz sz' :
    Z.to_nat sz' ≤ Z.to_nat sz →
    {{{
      ▷ Ψ 0 [] ∗
      □ (
        ∀ i vs,
        ⌜i < Z.to_nat sz' ∧ i = length vs⌝ -∗
        Ψ i vs -∗
        chunk_au_load l i (λ v,
          ▷ Ψ (S i) (vs ++ [v])
        )
      )
    }}}
      chunk_shrink #l #sz #sz'
    {{{ l' vs,
      RET #l';
      ⌜length vs = Z.to_nat sz'⌝ ∗
      chunk_model l' (DfracOwn 1) vs ∗
      Ψ (Z.to_nat sz') vs ∗
      if decide (0 < sz')%Z then meta_token l' ⊤ else True
    }}}.
  Proof.
    iIntros "%Hsz %Φ (HΨ & #H) HΦ".
    wp_rec.
    wp_smart_apply (chunk_resize_spec_atomic Ψ with "[$HΨ $H]"); [done.. |].
    iSteps. rewrite Nat.sub_diag right_id. iSteps.
  Qed.
  Lemma chunk_shrink_spec l dq vs (sz : Z) sz' :
    Z.to_nat sz = length vs →
    Z.to_nat sz' ≤ Z.to_nat sz →
    {{{
      chunk_model l dq vs
    }}}
      chunk_shrink #l #sz #sz'
    {{{ l',
      RET #l';
      chunk_model l dq vs ∗
      chunk_model l' (DfracOwn 1) (take (Z.to_nat sz') vs) ∗
      if decide (0 < sz')%Z then meta_token l' ⊤ else True
    }}}.
  Proof.
    iIntros "%Hsz %Hsz' %Φ Hmodel HΦ".
    wp_rec.
    wp_smart_apply (chunk_resize_spec with "Hmodel"); [done.. |].
    iSteps. rewrite Nat.sub_diag right_id. iSteps.
  Qed.

  Lemma chunk_clone_spec_atomic Ψ l sz :
    {{{
      ▷ Ψ 0 [] ∗
      □ (
        ∀ i vs,
        ⌜i < Z.to_nat sz ∧ i = length vs⌝ -∗
        Ψ i vs -∗
        chunk_au_load l i (λ v,
          ▷ Ψ (S i) (vs ++ [v])
        )
      )
    }}}
      chunk_clone #l #sz
    {{{ l' vs,
      RET #l';
      ⌜length vs = Z.to_nat sz⌝ ∗
      chunk_model l' (DfracOwn 1) vs ∗
      Ψ (Z.to_nat sz) vs ∗
      if decide (0 < sz)%Z then meta_token l' ⊤ else True
    }}}.
  Proof.
    iIntros "%Φ (HΨ & #H) HΦ".
    wp_rec.
    wp_smart_apply (chunk_shrink_spec_atomic Ψ with "[$HΨ $H]"); [done | iSteps].
  Qed.
  Lemma chunk_clone_spec l dq vs (sz : Z) :
    Z.to_nat sz = length vs →
    {{{
      chunk_model l dq vs
    }}}
      chunk_clone #l #sz
    {{{ l',
      RET #l';
      chunk_model l dq vs ∗
      chunk_model l' (DfracOwn 1) vs ∗
      if decide (0 < sz)%Z then meta_token l' ⊤ else True
    }}}.
  Proof.
    iIntros "%Hsz %Φ Hmodel HΦ".
    wp_rec.
    wp_smart_apply (chunk_shrink_spec with "Hmodel") as "%l' (Hmodel & Hmodel' & Hmeta)"; [lia.. |].
    iApply "HΦ".
    rewrite Hsz firstn_all. iSteps.
  Qed.

  Lemma chunk_fill_spec_atomic Ψ l sz v :
    {{{
      ▷ Ψ 0 ∗
      □ (
        ∀ i,
        ⌜i < Z.to_nat sz⌝ -∗
        Ψ i -∗
        chunk_au_store l i v (
          ▷ Ψ (S i)
        )
      )
    }}}
      chunk_fill #l #sz v
    {{{
      RET ();
      Ψ (Z.to_nat sz)
    }}}.
  Proof.
    iIntros "%Φ (HΨ & #H) HΦ".
    wp_rec.
    pose Ψ' (_ : Z) i :=
      Ψ i.
    wp_smart_apply (for_upto_spec_strong Ψ' with "[$HΨ]"); last rewrite Z.sub_0_r //.
    iIntros "!> %i_ %i (-> & %Hi) HΨ". rewrite Z.add_0_l in Hi |- *.
    wp_pures.
    iMod ("H" with "[] HΨ") as "(%v' & H↦ & _ & H')"; first iSteps.
    wp_store.
    iMod ("H'" with "H↦") as "HΨ".
    iSteps.
  Qed.
  Lemma chunk_fill_spec l vs (sz : Z) v :
    Z.to_nat sz = length vs →
    {{{
      chunk_model l (DfracOwn 1) vs
    }}}
      chunk_fill #l #sz v
    {{{
      RET ();
      chunk_model l (DfracOwn 1) (replicate (Z.to_nat sz) v)
    }}}.
  Proof.
    iIntros "%Hsz %Φ Hmodel HΦ".
    pose Ψ i :=
      chunk_model l (DfracOwn 1) (replicate i v ++ drop i vs).
    wp_apply (chunk_fill_spec_atomic Ψ with "[$Hmodel]"); last first.
    { rewrite /Ψ skipn_all2; first lia. rewrite right_id //. }
    iIntros "!> %i %Hi Hmodel".
    efeed pose proof (list_lookup_lookup_total_lt vs i) as Hlookup; first lia.
    iDestruct (chunk_model_update i i with "Hmodel") as "(H↦ & Hmodel)"; [lia | | lia |].
    { rewrite lookup_app_r replicate_length // lookup_drop Nat.sub_diag right_id //. }
    iAuIntro. iAaccIntro with "H↦"; first iSteps. iIntros "H↦".
    iDestruct ("Hmodel" with "H↦") as "Hmodel".
    rewrite /Ψ replicate_S_end -assoc insert_app_r_alt replicate_length // Nat.sub_diag.
    erewrite drop_S; done.
  Qed.

  Lemma chunk_cget_spec_atomic l (sz_ i_ : Z) :
    <<<
      True
    | ∀∀ sz i dq v,
      ⌜sz_ = Z.of_nat sz ∧ i_ = Z.of_nat i⌝ ∗
      chunk_cslice l sz i dq [v]
    >>>
      chunk_cget #l #sz_ #i_
    <<<
      chunk_cslice l sz i dq [v]
    | RET v; £ 1
    >>>.
  Proof.
    iIntros "!> %Φ _ HΦ".
    wp_rec. wp_pures credit:"H£".
    iMod "HΦ" as "(%sz & %i & %dq & %v & ((-> & ->) & Hcslice) & _ & HΦ)".
    rewrite -chunk_cslice_singleton Z_rem_mod; [lia.. |].
    wp_load.
    iMod ("HΦ" with "Hcslice") as "HΦ".
    iSteps.
  Qed.
  Lemma chunk_cget_spec l sz i dq v (sz_ i_ : Z) :
    sz_ = Z.of_nat sz →
    i_ = Z.of_nat i →
    {{{
      chunk_cslice l sz i dq [v]
    }}}
      chunk_cget #l #sz_ #i_
    {{{
      RET v;
      chunk_cslice l sz i dq [v]
    }}}.
  Proof.
    iIntros (-> ->) "%Φ Hcslice HΦ".
    iApply wp_fupd.
    awp_apply (chunk_cget_spec_atomic with "[//]") without "HΦ".
    rewrite /atomic_acc /=. repeat iExists _.
    iApply fupd_mask_intro; first done. iIntros "Hclose".
    iSplitL "Hcslice". { iFrame. iSteps. } iSplit; first iSteps. iIntros "Hslice".
    iMod "Hclose" as "_". iIntros "!> H£ HΦ".
    iMod (lc_fupd_elim_later with "H£ HΦ") as "HΦ".
    iApply ("HΦ" with "Hslice").
  Qed.

  Lemma chunk_cset_spec_atomic l (sz_ i_ : Z) v :
    <<<
      True
    | ∀∀ sz i w,
      ⌜sz_ = Z.of_nat sz ∧ i_ = Z.of_nat i⌝ ∗
      chunk_cslice l sz i (DfracOwn 1) [w]
    >>>
      chunk_cset #l #sz_ #i_ v
    <<<
      chunk_cslice l sz i (DfracOwn 1) [v]
    | RET (); £ 1
    >>>.
  Proof.
    iIntros "!> %Φ _ HΦ".
    wp_rec. wp_pures credit:"H£".
    iMod "HΦ" as "(%sz & %i & %w & ((-> & ->) & Hcslice) & _ & HΦ)".
    rewrite -!chunk_cslice_singleton Z_rem_mod; [lia.. |].
    wp_store.
    iMod ("HΦ" with "Hcslice") as "HΦ".
    iSteps.
  Qed.
  Lemma chunk_cset_spec l sz i w (sz_ i_ : Z) v :
    sz_ = Z.of_nat sz →
    i_ = Z.of_nat i →
    {{{
      chunk_cslice l sz i (DfracOwn 1) [w]
    }}}
      chunk_cset #l #sz_ #i_ v
    {{{
      RET ();
      chunk_cslice l sz i (DfracOwn 1) [v]
    }}}.
  Proof.
    iIntros (-> ->) "%Φ Hcslice HΦ".
    iApply wp_fupd.
    awp_apply (chunk_cset_spec_atomic with "[//]") without "HΦ".
    rewrite /atomic_acc /=. repeat iExists _.
    iApply fupd_mask_intro; first done. iIntros "Hclose".
    iSplitL "Hcslice"; first iSteps. iSplit; first iSteps. iIntros "Hslice".
    iMod "Hclose" as "_". iIntros "!> H£ HΦ".
    iMod (lc_fupd_elim_later with "H£ HΦ") as "HΦ".
    iApply ("HΦ" with "Hslice").
  Qed.

  Definition itype_chunk τ `{!iType _ τ} (sz : nat) l : iProp Σ :=
    inv nroot (
      ∃ vs,
      ⌜sz = length vs⌝ ∗
      chunk_model l (DfracOwn 1) vs ∗ [∗ list] v ∈ vs, τ v
    ).
  #[global] Instance itype_chunk_persistent τ `{!iType _ τ} sz l :
    Persistent (itype_chunk τ sz l).
  Proof.
    apply _.
  Qed.

  Lemma itype_chunk_0 τ `{!iType _ τ} l :
    ⊢ |={⊤}=>
      itype_chunk τ 0 l.
  Proof.
    iApply inv_alloc. iExists []. iSteps.
  Qed.

  Lemma itype_chunk_shift (i : Z) τ `{!iType _ τ} (sz : nat) l :
    (0 ≤ i ≤ sz)%Z →
    itype_chunk τ sz l ⊢
    itype_chunk τ (sz - Z.to_nat i) (l +ₗ i).
  Proof.
    iIntros "%Hi #Hl".
    Z_to_nat i. rewrite Nat2Z.id.
    iApply (inv_alter with "Hl"). iIntros "!> !> (%vs & %Hvs & Hmodel & Hvs)".
    rewrite -(take_drop i vs).
    iDestruct (chunk_model_app_2 with "Hmodel") as "(Hmodel1 & Hmodel2)"; first done.
    iDestruct (big_sepL_app with "Hvs") as "(Hvs1 & Hvs2)".
    iSplitL "Hmodel2 Hvs2".
    - iExists (drop i vs). iFrame.
      rewrite take_length drop_length Nat.min_l; first lia. iSteps.
    - iIntros "(%vs2 & %Hvs2 & Hmodel2 & Hvs2)".
      iDestruct (chunk_model_app_1 with "Hmodel1 Hmodel2") as "Hmodel".
      { f_equal. rewrite take_length. lia. }
      iExists (take i vs ++ vs2). iFrame.
      rewrite app_length take_length Nat.min_l; first lia. iSteps.
  Qed.

  Lemma itype_chunk_le sz' τ `{!iType _ τ} sz l :
    (sz' ≤ sz) →
    itype_chunk τ sz l ⊢
    itype_chunk τ sz' l.
  Proof.
    iIntros "%Hsz #Hl".
    iApply (inv_alter with "Hl"). iIntros "!> !> (%vs & %Hvs & Hmodel & Hvs)".
    rewrite -(take_drop sz' vs).
    iDestruct (chunk_model_app_2 with "Hmodel") as "(Hmodel1 & Hmodel2)"; first done.
    iDestruct (big_sepL_app with "Hvs") as "(Hvs1 & Hvs2)".
    iSplitL "Hmodel1 Hvs1".
    - iExists (take sz' vs). iFrame.
      rewrite take_length. iSteps.
    - iIntros "(%vs1 & %Hvs1 & Hmodel1 & Hvs1)".
      iDestruct (chunk_model_app_1 with "Hmodel1 Hmodel2") as "Hmodel".
      { f_equal. rewrite take_length. lia. }
      iExists (vs1 ++ drop sz' vs). iFrame.
      rewrite app_length drop_length. iSteps.
  Qed.

  Lemma chunk_make_type τ `{!iType _ τ} (sz : Z) v :
    {{{
      τ v
    }}}
      chunk_make #sz v
    {{{ l,
      RET #l;
      itype_chunk τ (Z.to_nat sz) l
    }}}.
  Proof.
    iIntros "%Φ #Hv HΦ".
    wp_rec. wp_pures.
    case_bool_decide; wp_pures.
    - wp_alloc l as "Hl"; first done.
      iApply "HΦ".
      iApply inv_alloc. iExists (replicate (Z.to_nat sz) v).
      iSplit; first rewrite replicate_length //.
      iSplitL; first iSteps.
      iApply big_sepL_intro. iIntros "!> %i %_v" ((-> & Hi)%lookup_replicate).
      iSteps.
    - iApply "HΦ".
      iApply inv_alloc. iExists []. iSteps.
  Qed.

  Lemma chunk_get_type τ `{!iType _ τ} (sz : nat) l (i : Z) :
    (0 ≤ i < sz)%Z →
    {{{
      itype_chunk τ sz l
    }}}
      !#(l +ₗ i)
    {{{ v,
      RET v;
      τ v
    }}}.
  Proof.
    iIntros "%Hi %Φ #Hl HΦ".
    Z_to_nat i.
    iInv "Hl" as "(%vs & >%Hvs & Hmodel & #Hvs)".
    feed pose proof (list_lookup_lookup_total_lt vs i); first lia.
    iDestruct (chunk_model_lookup_acc i with "Hmodel") as "(H↦ & Hmodel)"; [lia | done | lia |].
    wp_load.
    iDestruct (big_sepL_lookup with "Hvs") as "Hv"; first done.
    iSteps.
  Qed.

  Lemma chunk_set_type τ `{!iType _ τ} (sz : nat) l (i : Z) v :
    (0 ≤ i < sz)%Z →
    {{{
      itype_chunk τ sz l ∗
      τ v
    }}}
      #(l +ₗ i) <- v
    {{{
      RET (); True
    }}}.
  Proof.
    iIntros "%Hi %Φ (#Hl & #Hv) HΦ".
    Z_to_nat i.
    iInv "Hl" as "(%vs & >%Hvs & Hmodel & Hvs)".
    feed pose proof (list_lookup_lookup_total_lt vs i); first lia.
    iDestruct (chunk_model_update i with "Hmodel") as "(H↦ & Hmodel)"; [lia | done | lia |].
    wp_store.
    iDestruct (big_sepL_insert_acc with "Hvs") as "(_ & Hvs)"; first done.
    iModIntro. iSplitR "HΦ"; last iSteps. iExists (<[i := v]> vs).
    iSteps. rewrite insert_length //.
  Qed.

  Lemma chunk_foldli_type τ `{!iType _ τ} υ `{!iType _ υ} l sz sz_ acc fn :
    sz_ = Z.of_nat sz →
    {{{
      itype_chunk τ sz l ∗
      υ acc ∗
      (υ --> itype_nat_upto sz --> τ --> υ)%T fn
    }}}
      chunk_foldli #l #sz_ acc fn
    {{{ acc',
      RET acc';
      υ acc'
    }}}.
  Proof.
    iIntros (->) "%Φ (#Hl & Hacc & #Hfn) HΦ".
    pose (Ψ i vs o acc := (
      from_option τ True o ∗
      υ acc
    )%I).
    wp_apply (chunk_foldli_spec_atomic Ψ with "[$Hacc]"); last iSteps.
    clear acc. iIntros "!> %i %vs_left %o %acc (%Hi1 & %Hi2) (Ho & Hacc)".
    destruct o as [v |].
    - wp_apply (wp_wand with "(Hfn Hacc)"). iClear "Hfn". clear fn. iIntros "%fn Hfn".
      wp_apply (wp_wand with "(Hfn [])"); first iSteps. clear fn. iIntros "%fn Hfn".
      wp_apply (wp_wand with "(Hfn Ho)").
      iSteps.
    - iAuIntro.
      iInv "Hl" as "(%vs & >%Hvs & >Hmodel & #Hvs)".
      feed pose proof (list_lookup_lookup_total_lt vs i); first lia.
      iDestruct (chunk_model_lookup_acc i with "Hmodel") as "(H↦ & Hmodel)"; [lia | done | lia |].
      iAaccIntro with "H↦"; first iSteps.
      iDestruct (big_sepL_lookup with "Hvs") as "Hv"; first done.
      iSteps.
  Qed.

  Lemma chunk_foldl_type τ `{!iType _ τ} υ `{!iType _ υ} l sz sz_ acc fn :
    sz_ = Z.of_nat sz →
    {{{
      itype_chunk τ sz l ∗
      υ acc ∗
      (υ --> τ --> υ)%T fn
    }}}
      chunk_foldl #l #sz_ acc fn
    {{{ acc',
      RET acc';
      υ acc'
    }}}.
  Proof.
    iIntros (->) "%Φ (#Hl & #Hacc & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (chunk_foldli_type τ υ with "[$Hl $Hacc]"); [done | iSteps..].
  Qed.

  Lemma chunk_foldri_type τ `{!iType _ τ} υ `{!iType _ υ} l sz sz_ acc fn :
    sz_ = Z.of_nat sz →
    {{{
      itype_chunk τ sz l ∗
      υ acc ∗
      (itype_nat_upto sz --> τ --> υ --> υ)%T fn
    }}}
      chunk_foldri #l #sz_ fn acc
    {{{ acc',
      RET acc';
      υ acc'
    }}}.
  Proof.
    iIntros (->) "%Φ (#Hl & Hacc & #Hfn) HΦ".
    pose (Ψ i acc o vs := (
      from_option τ True o ∗
      υ acc
    )%I).
    wp_apply (chunk_foldri_spec_atomic Ψ with "[$Hacc]"); last iSteps.
    clear acc. iIntros "!> %i %acc %o %vs_right %Hi (Ho & Hacc)".
    destruct o as [v |].
    - wp_apply (wp_wand with "(Hfn [])"); first iSteps. iClear "Hfn". clear fn. iIntros "%fn Hfn".
      wp_apply (wp_wand with "(Hfn Ho)"). clear fn. iIntros "%fn Hfn".
      wp_apply (wp_wand with "(Hfn Hacc)").
      iSteps.
    - iAuIntro.
      iInv "Hl" as "(%vs & >%Hvs & >Hmodel & #Hvs)".
      feed pose proof (list_lookup_lookup_total_lt vs i); first lia.
      iDestruct (chunk_model_lookup_acc i with "Hmodel") as "(H↦ & Hmodel)"; [lia | done | lia |].
      iAaccIntro with "H↦"; first iSteps.
      iDestruct (big_sepL_lookup with "Hvs") as "Hv"; first done.
      iSteps.
  Qed.

  Lemma chunk_foldr_type τ `{!iType _ τ} υ `{!iType _ υ} l sz sz_ acc fn :
    sz_ = Z.of_nat sz →
    {{{
      itype_chunk τ sz l ∗
      υ acc ∗
      (τ --> υ --> υ)%T fn
    }}}
      chunk_foldr #l #sz_ fn acc
    {{{ acc',
      RET acc';
      υ acc'
    }}}.
  Proof.
    iIntros (->) "%Φ (#Hl & #Hacc & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (chunk_foldri_type τ υ with "[$Hl $Hacc]"); [done | iSteps..].
  Qed.

  Lemma chunk_iteri_type τ `{!iType _ τ} l sz sz_ fn :
    sz_ = Z.of_nat sz →
    {{{
      itype_chunk τ sz l ∗
      (itype_nat_upto sz --> τ --> itype_unit)%T fn
    }}}
      chunk_iteri #l #sz_ fn
    {{{
      RET (); True
    }}}.
  Proof.
    iIntros (->) "%Φ (#Hl & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (chunk_foldli_type τ itype_unit with "[$Hl]"); [done | iSteps..].
  Qed.

  Lemma chunk_iter_type τ `{!iType _ τ} l sz sz_ fn :
    sz_ = Z.of_nat sz →
    {{{
      itype_chunk τ sz l ∗
      (τ --> itype_unit)%T fn
    }}}
      chunk_iter #l #sz_ fn
    {{{
      RET (); True
    }}}.
  Proof.
    iIntros (->) "%Φ (#Hl & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (chunk_iteri_type τ with "[$Hl]"); [done | iSteps..].
  Qed.

  Lemma chunk_applyi_type τ `{!iType _ τ} l sz sz_ fn :
    sz_ = Z.of_nat sz →
    {{{
      itype_chunk τ sz l ∗
      (itype_nat_upto sz --> τ --> τ)%T fn
    }}}
      chunk_applyi #l #sz_ fn
    {{{
      RET (); True
    }}}.
  Proof.
    iIntros (->) "%Φ (#Hl & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (chunk_iteri_type τ with "[$Hl]"); [done | | iSteps].
    iIntros "!> % (%i & -> & %Hi)". wp_pures. iIntros "!> !> %v Hv".
    wp_smart_apply (wp_wand with "(Hfn [])"); first iSteps. iClear "Hfn". clear fn. iIntros "%fn Hfn".
    wp_apply (wp_wand with "(Hfn Hv)") as "%w Hw".
    wp_smart_apply (chunk_set_type with "[$Hl $Hw]"); first lia.
    iSteps.
  Qed.

  Lemma chunk_apply_type τ `{!iType _ τ} l sz sz_ fn :
    sz_ = Z.of_nat sz →
    {{{
      itype_chunk τ sz l ∗
      (τ --> τ)%T fn
    }}}
      chunk_apply #l #sz_ fn
    {{{
      RET (); True
    }}}.
  Proof.
    iIntros (->) "%Φ (#Hl & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (chunk_applyi_type τ with "[$Hl]"); [done | iSteps..].
  Qed.

  Lemma chunk_initi_type τ `{!iType _ τ} (sz : Z) fn :
    {{{
      (itype_nat_upto (Z.to_nat sz) --> τ)%T fn
    }}}
      chunk_initi #sz fn
    {{{ l,
      RET #l;
      itype_chunk τ (Z.to_nat sz) l
    }}}.
  Proof.
    iIntros "%Φ #Hfn HΦ".
    wp_rec.
    wp_smart_apply (chunk_make_spec with "[//]") as "%l (Hmodel & _)".
    wp_smart_apply (chunk_applyi_spec_disentangled (λ _, τ) with "[$Hmodel]").
    { rewrite replicate_length. lia. }
    { iIntros "!> %i %v %Hlookup".
      wp_smart_apply (wp_wand with "(Hfn [])"); last iSteps.
      apply lookup_lt_Some in Hlookup. rewrite replicate_length in Hlookup. iSteps.
    }
    iIntros "%vs (%Hvs & Hmodel & Hvs)". rewrite replicate_length in Hvs.
    iSteps.
  Qed.

  Lemma chunk_init_type τ `{!iType _ τ} (sz : Z) fn :
    {{{
      (itype_unit --> τ)%T fn
    }}}
      chunk_init #sz fn
    {{{ l,
      RET #l;
      itype_chunk τ (Z.to_nat sz) l
    }}}.
  Proof.
    iIntros "%Φ #Hfn HΦ".
    wp_rec.
    wp_smart_apply (chunk_initi_type τ with "[] HΦ").
    iSteps.
  Qed.

  Lemma chunk_mapi_type τ `{!iType _ τ} υ `{!iType _ υ} l sz sz_ fn :
    sz_ = Z.of_nat sz →
    {{{
      itype_chunk τ sz l ∗
      (itype_nat_upto sz --> τ --> υ)%T fn
    }}}
      chunk_mapi #l #sz_ fn
    {{{ l',
      RET #l';
      itype_chunk υ sz l'
    }}}.
  Proof.
    iIntros (->) "%Φ (#Hl & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (chunk_initi_type υ).
    { iIntros "!> % (%i & -> & %Hi)".
      wp_smart_apply (chunk_get_type with "Hl"); first lia.
      iSteps.
    }
    rewrite Nat2Z.id. iSteps.
  Qed.

  Lemma chunk_map_type τ `{!iType _ τ} υ `{!iType _ υ} l sz sz_ fn :
    sz_ = Z.of_nat sz →
    {{{
      itype_chunk τ sz l ∗
      (τ --> υ)%T fn
    }}}
      chunk_map #l #sz_ fn
    {{{ l',
      RET #l';
      itype_chunk υ sz l'
    }}}.
  Proof.
    iIntros (->) "%Φ (#Hl & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (chunk_mapi_type τ υ with "[] HΦ"); first done.
    iFrame "#∗". iSteps.
  Qed.

  Lemma chunk_copy_type τ `{!iType _ τ} l1 sz1 sz1_ l2 sz2 :
    sz1_ = Z.of_nat sz1 →
    sz1 ≤ sz2 →
    {{{
      itype_chunk τ sz1 l1 ∗
      itype_chunk τ sz2 l2
    }}}
      chunk_copy #l1 #sz1_ #l2
    {{{
      RET (); True
    }}}.
  Proof.
    iIntros (->) "%Hsz %Φ (#Hl1 & #Hl2) HΦ".
    wp_rec.
    wp_smart_apply (chunk_iteri_type τ with "[] HΦ"); first done.
    iFrame "#∗". iIntros "!> % (%i & -> & %Hi)". wp_pures. iIntros "!> !> %v Hv".
    wp_smart_apply (chunk_set_type with "[$Hl2 $Hv]"); first lia.
    iSteps.
  Qed.
  Lemma chunk_copy_type' τ `{!iType _ τ} l1 sz1 sz1_ l2 vs2 :
    sz1_ = Z.of_nat sz1 →
    sz1 = length vs2 →
    {{{
      itype_chunk τ sz1 l1 ∗
      chunk_model l2 (DfracOwn 1) vs2
    }}}
      chunk_copy #l1 #sz1_ #l2
    {{{
      RET ();
      itype_chunk τ sz1 l2
    }}}.
  Proof.
    iIntros (-> ->) "%Φ (#Hl1 & Hmodel2) HΦ".
    wp_rec.
    pose (Ψ i vs o := (
      chunk_model l2 (DfracOwn 1) (vs ++ drop i vs2) ∗
      ([∗ list] v ∈ vs, τ v) ∗
      from_option τ True o
    )%I).
    iApply wp_fupd.
    wp_smart_apply (chunk_iteri_spec_atomic Ψ with "[$Hmodel2]"); last first.
    { iIntros "%vs (%Hvs & (Hmodel2 & Hvs & _))".
      iApply "HΦ".
      iApply inv_alloc. iExists vs.
      rewrite Nat2Z.id drop_all right_id. iSteps.
    }
    iStep. iIntros "!> %i %vs %o (%Hi1 & %Hi2) (Hmodel2 & Hvs & Ho)".
    destruct o as [v |].
    - iDestruct (chunk_model_update i i with "Hmodel2") as "(H↦2 & Hmodel2)"; [lia | | lia |].
      { apply list_lookup_lookup_total_lt. rewrite app_length drop_length. lia. }
      wp_store.
      iDestruct ("Hmodel2" with "H↦2") as "Hmodel2".
      iStep. iFrame.
      rewrite /= right_id insert_app_r_alt; first lia.
      rewrite Nat.sub_diag insert_take_drop; first (rewrite drop_length; lia).
      rewrite drop_drop Nat.add_1_r -(assoc (++)) //.
    - iAuIntro.
      iInv "Hl1" as "(%vs1 & >%Hvs1 & >Hmodel1 & #Hvs1)".
      feed pose proof (list_lookup_lookup_total_lt vs1 i); first lia.
      iDestruct (chunk_model_lookup_acc i with "Hmodel1") as "(H↦1 & Hmodel1)"; [lia | done | lia |].
      iAaccIntro with "H↦1"; first iSteps.
      iDestruct (big_sepL_lookup with "Hvs1") as "Hv1"; first done.
      iSteps.
  Qed.

  Lemma chunk_resize_type τ `{!iType _ τ} l sz sz_ sz' (n : Z) v' :
    sz_ = Z.of_nat sz →
    (n ≤ sz)%Z →
    (n ≤ sz')%Z →
    {{{
      itype_chunk τ sz l ∗
      if decide (n < sz')%Z then τ v' else True
    }}}
      chunk_resize #l #sz_ #sz' #n v'
    {{{ l',
      RET #l';
      itype_chunk τ (Z.to_nat sz') l'
    }}}.
  Proof.
    iIntros (->) "%Hn1 %Hn2 %Φ (#Hl & Hv') HΦ".
    wp_rec.
    wp_smart_apply (chunk_make_spec with "[//]") as "%l' (Hmodel' & _)".
    pose (Ψ i vs' o := (
      chunk_model l' (DfracOwn 1) (vs' ++ replicate (Z.to_nat sz' - i) v') ∗
      ([∗ list] v' ∈ vs', τ v') ∗
      from_option τ True o
    )%I).
    wp_smart_apply (chunk_copy_spec_atomic Ψ with "[Hmodel']"); last first.
    { iIntros "%vs' (%Hvs' & (Hmodel' & Hvs' & _))".
      wp_pures.
      iApply "HΦ".
      iApply inv_alloc. iExists _. iFrame "Hmodel'".
      iSplit. { rewrite app_length replicate_length. iSteps. }
      iSplit; first iSteps.
      iApply big_sepL_replicate_2.
      case_decide.
      - iDestruct "Hv'" as "#Hv'".
        iApply big_sepL_intro. auto.
      - assert (n = sz') as -> by lia. rewrite Nat.sub_diag //.
    }
    iSplit.
    - iSteps. rewrite Nat.sub_0_r. iSteps.
    - iIntros "!> %i %vs' %o (%Hi1 & %Hi2) (Hmodel' & Hvs' & Ho)".
      destruct o as [v |].
      + iDestruct (chunk_model_update i i with "Hmodel'") as "(H↦' & Hmodel')"; [lia | | lia |].
        { rewrite lookup_app_r; first lia. rewrite lookup_replicate. naive_solver lia. }
        iAuIntro. iAaccIntro with "H↦'"; first iSteps. iIntros "H↦' !> !>". iFrame. rewrite /= right_id.
        iDestruct ("Hmodel'" with "H↦'") as "Hmodel'".
        rewrite insert_app_r_alt; first lia. rewrite insert_replicate_lt; first lia.
        rewrite Hi2 Nat.sub_diag /= Nat.sub_1_r -Nat.sub_succ_r -(assoc (++)).
        iSteps.
      + iAuIntro.
        iInv "Hl" as "(%vs & >%Hvs & >Hmodel & #Hvs)".
        feed pose proof (list_lookup_lookup_total_lt vs i); first lia.
        iDestruct (chunk_model_lookup_acc i with "Hmodel") as "(H↦ & Hmodel)"; [lia | done | lia |].
        iDestruct (big_sepL_lookup with "Hvs") as "Hv"; first done.
        iAaccIntro with "H↦"; iSteps.
  Qed.

  Lemma chunk_grow_type τ `{!iType _ τ} l sz sz_ sz' v' :
    sz_ = Z.of_nat sz →
    (sz ≤ sz')%Z →
    {{{
      itype_chunk τ sz l ∗
      τ v'
    }}}
      chunk_grow #l #sz_ #sz' v'
    {{{ l',
      RET #l';
      itype_chunk τ (Z.to_nat sz') l'
    }}}.
  Proof.
    iIntros (->) "%Hsz %Φ (#Hl & #Hv') HΦ".
    wp_rec.
    wp_smart_apply (chunk_resize_type with "[$Hl] HΦ"); [done.. |].
    case_decide; iSteps.
  Qed.

  Lemma chunk_shrink_type τ `{!iType _ τ} l sz sz_ sz' :
    sz_ = Z.of_nat sz →
    (sz' ≤ sz)%Z →
    {{{
      itype_chunk τ sz l
    }}}
      chunk_shrink #l #sz_ #sz'
    {{{ l',
      RET #l';
      itype_chunk τ (Z.to_nat sz') l'
    }}}.
  Proof.
    iIntros (->) "%Hsz %Φ #Hl HΦ".
    wp_rec.
    wp_smart_apply (chunk_resize_type with "[$Hl] HΦ"); [done.. |].
    rewrite decide_False //. lia.
  Qed.

  Lemma chunk_clone_type τ `{!iType _ τ} l sz sz_ :
    sz_ = Z.of_nat sz →
    {{{
      itype_chunk τ sz l
    }}}
      chunk_clone #l #sz_
    {{{ l',
      RET #l';
      itype_chunk τ sz l'
    }}}.
  Proof.
    iIntros (->) "%Φ #Hl HΦ".
    wp_rec.
    wp_smart_apply (chunk_shrink_type with "Hl"); [done.. |].
    rewrite Nat2Z.id. iSteps.
  Qed.

  Lemma chunk_fill_type τ `{!iType _ τ} l sz sz_ v :
    sz_ = Z.of_nat sz →
    {{{
      itype_chunk τ sz l ∗
      τ v
    }}}
      chunk_fill #l #sz_ v
    {{{
      RET (); True
    }}}.
  Proof.
    iIntros (->) "%Φ (#Hl & #Hv) HΦ".
    pose Ψ i : iProp Σ :=
      True%I.
    wp_apply (chunk_fill_spec_atomic Ψ); last iSteps.
    iStep. iIntros "!> %i %Hi _". iAuIntro.
    iInv "Hl" as "(%vs & >%Hvs & >Hmodel & #Hvs)".
    feed pose proof (list_lookup_lookup_total_lt vs i) as Hlookup; first lia.
    iDestruct (chunk_model_update i i with "Hmodel") as "(H↦ & Hmodel)"; [lia | | lia |].
    { apply list_lookup_lookup_total_lt. lia. }
    iAaccIntro with "H↦"; iIntros "H↦ !>".
    - iDestruct ("Hmodel" with "H↦") as "Hmodel".
      rewrite list_insert_id //. iSteps.
    - iSplit; last iSteps.
      iDestruct (big_sepL_insert_acc with "Hvs") as "(_ & Hvs')"; first done.
      iExists (<[i := v]> vs). iSteps. rewrite insert_length //.
  Qed.

  Lemma chunk_cget_type τ `{!iType _ τ} (sz : nat) l (i : Z) :
    0 < sz →
    (0 ≤ i)%Z →
    {{{
      itype_chunk τ sz l
    }}}
      chunk_cget #l #sz #i
    {{{ v,
      RET v;
      τ v
    }}}.
  Proof.
    iIntros "%Hsz %Hi %Φ #Hl HΦ".
    Z_to_nat i.
    wp_rec. wp_pures.
    iInv "Hl" as "(%vs & >%Hvs & Hmodel & #Hvs)".
    feed pose proof (list_lookup_lookup_total_lt vs (i `mod` sz)); first lia.
    iDestruct (chunk_model_lookup_acc (i `rem` sz) with "Hmodel") as "(H↦ & Hmodel)"; [lia | done | rewrite Z_rem_mod; lia |].
    wp_load.
    iDestruct (big_sepL_lookup with "Hvs") as "Hv"; first done.
    iSteps.
  Qed.

  Lemma chunk_cset_type τ `{!iType _ τ} (sz : nat) l (i : Z) v :
    0 < sz →
    (0 ≤ i)%Z →
    {{{
      itype_chunk τ sz l ∗
      τ v
    }}}
      chunk_cset #l #sz #i v
    {{{
      RET (); True
    }}}.
  Proof.
    iIntros "%Hsz %Hi %Φ (#Hl & #Hv) HΦ".
    Z_to_nat i.
    wp_rec. wp_pures.
    iInv "Hl" as "(%vs & >%Hvs & Hmodel & Hvs)".
    feed pose proof (list_lookup_lookup_total_lt vs (i `mod` sz)); first lia.
    iDestruct (chunk_model_update (i `rem` sz) with "Hmodel") as "(H↦ & Hmodel)"; [lia | done | rewrite Z_rem_mod; lia |].
    wp_store.
    iDestruct (big_sepL_insert_acc with "Hvs") as "(_ & Hvs)"; first done.
    iModIntro. iSplitR "HΦ"; last iSteps. iExists (<[i `mod` sz := v]> vs).
    iSteps. rewrite insert_length //.
  Qed.
End zebre_G.

#[global] Opaque chunk_make.
#[global] Opaque chunk_foldli.
#[global] Opaque chunk_foldl.
#[global] Opaque chunk_foldri.
#[global] Opaque chunk_foldr.
#[global] Opaque chunk_iteri.
#[global] Opaque chunk_iter.
#[global] Opaque chunk_applyi.
#[global] Opaque chunk_apply.
#[global] Opaque chunk_initi.
#[global] Opaque chunk_init.
#[global] Opaque chunk_mapi.
#[global] Opaque chunk_map.
#[global] Opaque chunk_copy.
#[global] Opaque chunk_resize.
#[global] Opaque chunk_grow.
#[global] Opaque chunk_shrink.
#[global] Opaque chunk_clone.
#[global] Opaque chunk_fill.
#[global] Opaque chunk_cget.
#[global] Opaque chunk_cset.

#[global] Opaque chunk_model.
#[global] Opaque chunk_span.
#[global] Opaque chunk_cslice.
