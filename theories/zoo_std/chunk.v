From zoo Require Import
  prelude.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Export
  base.
From zoo Require Import
  options.

Implicit Types i n : nat.
Implicit Types l : location.
Implicit Types v : val.
Implicit Types vs : list val.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Section chunk_model.
    Definition chunk_model l dq vs : iProp Σ :=
      l ↦∗{dq} vs.

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
      setoid_rewrite big_sepL_singleton. rewrite location_add_0 //.
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
      setoid_rewrite <- location_add_assoc. done.
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
      rewrite -!chunk_model_app location_add_assoc Nat2Z.inj_add //.
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
      i_ = ₊i →
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
      i_ = ₊i →
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
      i_ = ₊i →
      chunk_model l dq vs ⊢
      (l +ₗ i) ↦{dq} v.
    Proof.
      intros Hi Hlookup ->.
      Z_to_nat i. rewrite Nat2Z.id in Hlookup |- *.
      iApply big_sepL_lookup. done.
    Qed.

    Lemma chunk_model_update' {l} {i : Z} {dq vs} j k v :
      (0 ≤ i ≤ j)%Z →
      vs !! k = Some v →
      k = ₊j - ₊i →
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
      rewrite location_add_assoc -Nat2Z.inj_add Hk -Nat.le_add_sub //. lia.
    Qed.
    Lemma chunk_model_lookup_acc' {l} {i : Z} {dq vs} j k v :
      (0 ≤ i ≤ j)%Z →
      vs !! k = Some v →
      k = ₊j - ₊i →
      chunk_model (l +ₗ i) dq vs ⊢
        (l +ₗ j) ↦{dq} v ∗
        ( (l +ₗ j) ↦{dq} v -∗
          chunk_model (l +ₗ i) dq vs
        ).
    Proof.
      intros Hij Hlookup ->.
      Z_to_nat i. Z_to_nat j. rewrite !Nat2Z.id in Hlookup |- *. remember (j - i) as k eqn:Hk.
      rewrite {1}(chunk_model_lookup_acc k); [lia | done | lia |].
      rewrite location_add_assoc -Nat2Z.inj_add Hk -Nat.le_add_sub //. lia.
    Qed.
    Lemma chunk_model_lookup' {l} {i : Z} {dq vs} j k v :
      (0 ≤ i ≤ j)%Z →
      vs !! k = Some v →
      k = ₊j - ₊i →
      chunk_model (l +ₗ i) dq vs ⊢
      (l +ₗ j) ↦{dq} v.
    Proof.
      intros Hij Hlookup ->.
      Z_to_nat i. Z_to_nat j. rewrite !Nat2Z.id in Hlookup |- *. remember (j - i) as k eqn:Hk.
      rewrite {1}(chunk_model_lookup k); [lia | done | lia |].
      rewrite location_add_assoc -Nat2Z.inj_add Hk -Nat.le_add_sub //. lia.
    Qed.

    Lemma chunk_model_valid l dq vs :
      0 < length vs →
      chunk_model l dq vs ⊢
      ⌜✓ dq⌝.
    Proof.
      intros Hvs. destruct vs as [| v vs]; first naive_solver lia.
      iIntros "(H↦ & _)".
      iApply (pointsto_valid with "H↦").
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
      - destruct vs2 as [| v2 vs2]; first done.
        iDestruct (chunk_model_cons_2 with "Hmodel1") as "(H↦1 & Hmodel1)".
        iDestruct (chunk_model_cons_2 with "Hmodel2") as "(H↦2 & Hmodel2)".
        iDestruct (pointsto_combine with "H↦1 H↦2") as "(-> & H↦)".
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
        destruct vs as [| v []]; try done. iSteps.
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
        destruct vs as [| v vs]; first done.
        iDestruct (chunk_model_cons_2 with "Hmodel") as "(H↦ & Hmodel)".
        iExists v. iFrame. iSteps.
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
        iExists (vs1 ++ vs2). iSplit; first (rewrite length_app; naive_solver).
        iApply (chunk_model_app_1 with "Hmodel1 Hmodel2"); first congruence.
      - iIntros "(%vs & % & Hmodel)".
        iDestruct (chunk_model_app_2 (take n1 vs) (drop n1 vs) with "Hmodel") as "(Hmodel1 & Hmodel2)"; first rewrite take_drop //.
        iSplitL "Hmodel1".
        + iExists (take n1 vs). iFrame. rewrite length_take_le //. lia.
        + iExists (drop n1 vs). rewrite length_take_le; first lia. iFrame.
          rewrite length_drop. iSteps.
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
      iExists (vs !!! ₊i). iFrame. iIntros "%v H↦".
      iExists (<[₊i := v]> vs). iSplit; first rewrite length_insert //.
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

    Lemma chunk_span_update' {l} {i : Z} {dq n} j :
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
      rewrite location_add_assoc -Nat2Z.inj_add Hk -Nat.le_add_sub //. lia.
    Qed.
    Lemma chunk_span_lookup_acc' {l} {i : Z} {dq n} j :
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
      rewrite location_add_assoc -Nat2Z.inj_add Hk -Nat.le_add_sub //. lia.
    Qed.
    Lemma chunk_span_lookup' {l} {i : Z} {dq n} j :
      (0 ≤ i ≤ j ∧ j < i + n)%Z →
      chunk_span (l +ₗ i) dq n ⊢
        ∃ v,
        (l +ₗ j) ↦{dq} v.
    Proof.
      intros Hij.
      Z_to_nat i. Z_to_nat j. remember (j - i) as k eqn:Hk.
      rewrite {1}(chunk_span_lookup k); first lia.
      rewrite location_add_assoc -Nat2Z.inj_add Hk -Nat.le_add_sub //. lia.
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
      iApply (pointsto_valid with "H↦").
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
      - destruct vs2 as [| v2 vs2]; first done.
        iDestruct (chunk_cslice_cons_2 with "Hcslice1") as "(H↦1 & Hcslice1)".
        iDestruct (chunk_cslice_cons_2 with "Hcslice2") as "(H↦2 & Hcslice2)".
        iDestruct (pointsto_combine with "H↦1 H↦2") as "(-> & H↦)".
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

  Section itype_chunk.
    Definition itype_chunk τ `{!iType _ τ} sz l : iProp Σ :=
      inv nroot (
        ∃ vs,
        ⌜sz = length vs⌝ ∗
        chunk_model l (DfracOwn 1) vs ∗
        [∗ list] v ∈ vs, τ v
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
      itype_chunk τ (sz - ₊i) (l +ₗ i).
    Proof.
      iIntros "%Hi #Hl".
      Z_to_nat i. rewrite Nat2Z.id.
      iApply (inv_alter with "Hl"). iIntros "!> !> (%vs & %Hvs & Hmodel & Hvs)".
      rewrite -(take_drop i vs).
      iDestruct (chunk_model_app_2 with "Hmodel") as "(Hmodel1 & Hmodel2)"; first done.
      iDestruct (big_sepL_app with "Hvs") as "(Hvs1 & Hvs2)".
      iSplitL "Hmodel2 Hvs2".
      - iExists (drop i vs). iFrame.
        rewrite length_take length_drop Nat.min_l; first lia. iSteps.
      - iIntros "(%vs2 & %Hvs2 & Hmodel2 & Hvs2)".
        iDestruct (chunk_model_app_1 with "Hmodel1 Hmodel2") as "Hmodel".
        { f_equal. rewrite length_take. lia. }
        iExists (take i vs ++ vs2). iFrame.
        rewrite length_app length_take Nat.min_l; first lia. iSteps.
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
        rewrite length_take. iSteps.
      - iIntros "(%vs1 & %Hvs1 & Hmodel1 & Hvs1)".
        iDestruct (chunk_model_app_1 with "Hmodel1 Hmodel2") as "Hmodel".
        { f_equal. rewrite length_take. lia. }
        iExists (vs1 ++ drop sz' vs). iFrame.
        rewrite length_app length_drop. iSteps.
    Qed.
  End itype_chunk.
End zoo_G.

#[global] Opaque chunk_model.
#[global] Opaque chunk_span.
#[global] Opaque chunk_cslice.
