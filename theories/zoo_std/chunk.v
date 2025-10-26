From zoo Require Import
  prelude.
From zoo.common Require Import
  list
  math.
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
      chunk_model (l +ₗ ⁺(length vs1 + length vs2)) dq vs3 ⊣⊢
      chunk_model l dq (vs1 ++ vs2 ++ vs3).
    Proof.
      rewrite -!chunk_model_app location_add_assoc Nat2Z.inj_add //.
    Qed.
    Lemma chunk_model_app3_1 dq l1 vs1 l2 vs2 l3 vs3 :
      l2 = l1 +ₗ length vs1 →
      l3 = l1 +ₗ ⁺(length vs1 + length vs2) →
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
        chunk_model (l +ₗ ⁺(length vs1 + length vs2)) dq vs3.
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
        ⌜✓ (dq1 ⋅ dq2)⌝ ∗
        ⌜vs1 = vs2⌝.
    Proof.
      iIntros "% % Hmodel1 Hmodel2".
      iDestruct (chunk_model_combine with "Hmodel1 Hmodel2") as "(-> & Hmodel)"; first done.
      iDestruct (chunk_model_valid with "Hmodel") as "$"; first done.
      iSteps.
    Qed.
    Lemma chunk_model_agree l dq1 vs1 dq2 vs2 :
      length vs1 = length vs2 →
      chunk_model l dq1 vs1 -∗
      chunk_model l dq2 vs2 -∗
      ⌜vs1 = vs2⌝.
    Proof.
      iIntros "% Hmodel1 Hmodel2".
      iDestruct (chunk_model_combine with "Hmodel1 Hmodel2") as "($ & _)"; first done.
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
    Lemma chunk_model_exclusive l vs1 dq2 vs2 :
      0 < length vs1 →
      length vs1 = length vs2 →
      chunk_model l (DfracOwn 1) vs1 -∗
      chunk_model l dq2 vs2 -∗
      False.
    Proof.
      iIntros "% % Hmodel1 Hmodel2".
      iDestruct (chunk_model_ne with "Hmodel1 Hmodel2") as %?; done.
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
        iExists v. iFrameSteps.
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
        iExists (vs1 ++ vs2). iSplit; first (simpl_length; naive_solver).
        iApply (chunk_model_app_1 with "Hmodel1 Hmodel2"); first congruence.
      - iIntros "(%vs & % & Hmodel)".
        iDestruct (chunk_model_app_2 (take n1 vs) (drop n1 vs) with "Hmodel") as "(Hmodel1 & Hmodel2)"; first rewrite take_drop //.
        iSplitL "Hmodel1".
        + iExists (take n1 vs). simpl_length. iSteps.
        + iExists (drop n1 vs). simpl_length. rewrite Nat.min_l; first lia. iSteps.
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
      chunk_span (l +ₗ ⁺(n1 + n2)) dq n3 ⊣⊢
      chunk_span l dq (n1 + n2 + n3).
    Proof.
      rewrite -!chunk_span_app. iSteps.
    Qed.
    Lemma chunk_span_app3_1 dq l1 n1 l2 n2 l3 n3 :
      l2 = l1 +ₗ n1 →
      l3 = l1 +ₗ ⁺(n1 + n2) →
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
        chunk_span (l +ₗ ⁺(n1 + n2)) dq n3.
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
      iExists (<[₊i := v]> vs). iSplit; first simpl_length.
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
      iDestruct (chunk_span_valid with "Hspan") as "$"; first done.
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
    Lemma chunk_span_exclusive l n1 dq2 n2 :
      n1 = n2 →
      0 < n1 →
      chunk_span l (DfracOwn 1) n1 -∗
      chunk_span l dq2 n2 -∗
      False.
    Proof.
      iIntros "% % Hspan1 Hspan2".
      iDestruct (chunk_span_ne with "Hspan1 Hspan2") as %?; done.
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
      rewrite Z.add_0_l Z.mod_small //; first lia.
    Qed.
    Lemma chunk_model_cslice_cell l i sz dq v :
      chunk_model (l +ₗ i `mod` sz) dq [v] ⊣⊢
      chunk_cslice l sz i dq [v].
    Proof.
      rewrite /chunk_model /chunk_cslice.
      rewrite !big_sepL_singleton location_add_0 right_id //.
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

    Lemma chunk_cslice_app3 {l sz i dq vs} n1 i1 n2 i2 :
      i1 = i + n1 →
      i2 = i1 + n2 →
      n1 ≤ length vs →
      n1 + n2 ≤ length vs →
      chunk_cslice l sz i dq vs ⊣⊢
        chunk_cslice l sz i dq (take n1 vs) ∗
        chunk_cslice l sz i1 dq (take n2 $ drop n1 vs) ∗
        chunk_cslice l sz i2 dq (drop (n1 + n2) vs).
    Proof.
      intros -> -> ? ?.
      rewrite -{1}(take_drop n1 vs).
      rewrite -{1}(take_drop n2 (drop n1 vs)) drop_drop.
      rewrite -!chunk_cslice_app. simpl_length.
      rewrite !Nat.min_l //; first lia.
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
        (l +ₗ ⁺(i + k) `mod` sz) ↦{dq} v ∗
        ( ∀ w,
          (l +ₗ ⁺(i + k) `mod` sz) ↦{dq} w -∗
          chunk_cslice l sz i dq (<[k := w]> vs)
        ).
    Proof.
      rewrite Nat2Z.inj_add. apply: big_sepL_insert_acc.
    Qed.
    Lemma chunk_cslice_lookup_acc {l sz i dq vs} k v :
      vs !! k = Some v →
      chunk_cslice l sz i dq vs ⊢
        (l +ₗ ⁺(i + k) `mod` sz) ↦{dq} v ∗
        ( (l +ₗ ⁺(i + k) `mod` sz) ↦{dq} v -∗
          chunk_cslice l sz i dq vs
        ).
    Proof.
      rewrite Nat2Z.inj_add. apply: big_sepL_lookup_acc.
    Qed.
    Lemma chunk_cslice_lookup {l sz i dq vs} k v :
      vs !! k = Some v →
      chunk_cslice l sz i dq vs ⊢
      (l +ₗ ⁺(i + k) `mod` sz) ↦{dq} v.
    Proof.
      rewrite Nat2Z.inj_add. apply: big_sepL_lookup.
    Qed.

    Lemma chunk_cslice_update' {l sz i dq vs} j k v :
      (i ≤ j)%Z →
      vs !! k = Some v →
      k = ₊j - i →
      chunk_cslice l sz i dq vs ⊢
        (l +ₗ j `mod` sz) ↦{dq} v ∗
        ( ∀ w,
          (l +ₗ j `mod` sz) ↦{dq} w -∗
          chunk_cslice l sz i dq (<[k := w]> vs)
        ).
    Proof.
      intros Hij Hlookup ->.
      remember (₊j - i) as k eqn:Hk.
      rewrite {1}(chunk_cslice_update k) //.
      replace ⁺(i + k) with j by lia. done.
    Qed.
    Lemma chunk_cslice_lookup_acc' {l sz i dq vs} j k v :
      (i ≤ j)%Z →
      vs !! k = Some v →
      k = ₊j - i →
      chunk_cslice l sz i dq vs ⊢
        (l +ₗ j `mod` sz) ↦{dq} v ∗
        ( (l +ₗ j `mod` sz) ↦{dq} v -∗
          chunk_cslice l sz i dq vs
        ).
    Proof.
      intros Hij Hlookup ->.
      remember (₊j - i) as k eqn:Hk.
      rewrite {1}(chunk_cslice_lookup_acc k) //.
      replace ⁺(i + k) with j by lia. done.
    Qed.
    Lemma chunk_cslice_lookup' {l sz i dq vs} j k v :
      (i ≤ j)%Z →
      vs !! k = Some v →
      k = ₊j - i →
      chunk_cslice l sz i dq vs ⊢
      (l +ₗ j `mod` sz) ↦{dq} v.
    Proof.
      intros Hij Hlookup ->.
      remember (₊j - i) as k eqn:Hk.
      rewrite {1}(chunk_cslice_lookup k) //.
      replace ⁺(i + k) with j by lia. done.
    Qed.

    Lemma chunk_cslice_shift l sz i dq vs :
      chunk_cslice l sz i dq vs ⊣⊢
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

    Lemma chunk_cslice_shift_right l sz i dq vs :
      chunk_cslice l sz i dq vs ⊣⊢
      chunk_cslice l sz (i + sz) dq vs.
    Proof.
      rewrite chunk_cslice_shift //.
    Qed.

    Lemma chunk_cslice_shift_left l sz i dq vs :
      sz ≤ i →
      chunk_cslice l sz i dq vs ⊣⊢
      chunk_cslice l sz (i - sz) dq vs.
    Proof.
      intros.
      setoid_rewrite chunk_cslice_shift at 2.
      replace (i - sz + sz) with i by lia. done.
    Qed.

    Lemma chunk_cslice_mod l sz i dq vs :
      0 < sz →
      chunk_cslice l sz i dq vs ⊣⊢
      chunk_cslice l sz (i `mod` sz) dq vs.
    Proof.
      intros.
      rewrite /chunk_cslice Nat2Z.inj_mod.
      setoid_rewrite Z.add_mod_idemp_l; last lia.
      done.
    Qed.

    #[local] Lemma chunk_cslice_to_model_aux l sz i dq vs :
      0 < sz →
      i + length vs ≤ sz →
      chunk_cslice l sz i dq vs ⊣⊢
      chunk_model (l +ₗ i) dq vs.
    Proof.
      intros.
      iSplit.
      all: iIntros "H".
      all: iApply (big_sepL_impl with "H"); iIntros "!>" (k v Hk%lookup_lt_Some) "H↦".
      all: rewrite location_add_assoc Z.mod_small //; first lia.
    Qed.
    Lemma chunk_cslice_to_model l sz i dq vs :
      0 < sz →
      length vs ≤ sz →
      chunk_cslice l sz i dq vs ⊣⊢
        chunk_model (l +ₗ ⁺(i `mod` sz)) dq (take (sz - i `mod` sz) vs) ∗
        chunk_model l dq (drop (sz - i `mod` sz) vs).
    Proof.
      intros Hsz Hvs.
      rewrite chunk_cslice_mod //.
      destruct_decide (i `mod` sz + length vs ≤ sz).
      - rewrite firstn_all2; first lia.
        rewrite skipn_all2; first lia.
        rewrite chunk_cslice_to_model_aux //.
        iSteps.
        iApply chunk_model_nil.
      - rewrite -{1}(take_drop (sz - i `mod` sz) vs) -chunk_cslice_app.
        rewrite length_take Nat.min_l; first lia.
        rewrite -Nat.le_add_sub; first lia.
        setoid_rewrite chunk_cslice_mod at 2; last done.
        rewrite Nat.Div0.mod_same.
        rewrite chunk_cslice_to_model_aux //.
        { simpl_length. lia. }
        rewrite chunk_cslice_to_model_aux //.
        { simpl_length. lia. }
        rewrite location_add_0 //.
    Qed.
    Lemma chunk_cslice_to_model_full l sz i dq vs :
      0 < sz →
      length vs = sz →
      chunk_cslice l sz i dq vs ⊣⊢
      chunk_model l dq (rotation (sz - i `mod` sz) vs).
    Proof.
      intros.
      rewrite chunk_cslice_to_model; [lia.. |].
      rewrite -chunk_model_app length_drop.
      replace (length vs - (sz - i `mod` sz)) with (i `mod` sz) by lia.
      iSteps.
    Qed.

    #[local] Lemma chunk_cslice_rotation_right_aux {l sz} i1 i2 dq vs :
      0 < sz →
      length vs = sz →
      i1 `mod` sz ≤ i2 `mod` sz →
      chunk_cslice l sz i1 dq vs ⊣⊢
      chunk_cslice l sz i2 dq (rotation (i2 `mod` sz - i1 `mod` sz) vs).
    Proof.
      intros.

      pose j1 := i1 `mod` sz.
      pose j2 := i2 `mod` sz.

      setoid_rewrite chunk_cslice_mod; [| done..].

      setoid_rewrite (chunk_cslice_app3 (j2 - j1) j2 (sz - j2) sz) at 1; [| lia..].
      setoid_rewrite (chunk_cslice_app3 (sz - j2) sz j1 (j1 + sz)) at 4; [| simpl_length; lia..].

      rewrite (chunk_cslice_shift_left _ _ (j1 + sz)); first lia.
      rewrite Nat.add_sub.
      rewrite (drop_app_length' _ _ (sz - j2 + j1)).
      { simpl_length. lia. }

      rewrite (take_app_le _ _ (sz - j2)).
      { simpl_length. lia. }
      rewrite (take_drop_commute _ j1 (sz - j2)) take_app_length'.
      { simpl_length. lia. }
      rewrite drop_drop.

      iSteps.
    Qed.
    Lemma chunk_cslice_rotation_right {l sz i dq vs} n :
      0 < sz →
      length vs = sz →
      chunk_cslice l sz i dq vs ⊣⊢
      chunk_cslice l sz (i + n) dq (rotation (n `mod` sz) vs).
    Proof.
      intros.

      pose i1 := i.
      pose i2 := i + n.

      pose j1 := i1 `mod` sz.
      pose j2 := i2 `mod` sz.

      destruct (Nat.le_ge_cases j1 j2).

      - rewrite chunk_cslice_rotation_right_aux // minus_mod_1'' //; first lia.

      - rewrite (chunk_cslice_rotation_right_aux i2 i1) //; first  simpl_length.
        rewrite minus_mod_2; [lia.. |].
        rewrite Nat.add_sub'.
        destruct_decide (n `mod` sz = 0) as -> | ?.
        + rewrite Nat.sub_0_r Nat.Div0.mod_same !rotation_0 //.
        + rewrite Nat.mod_small; first lia.
          rewrite /rotation drop_app_length'.
          { simpl_length. lia. }
          rewrite take_app_length'.
          { simpl_length. lia. }
          rewrite take_drop //.
    Qed.
    Lemma chunk_cslice_rotation_right_1 {l sz i dq vs} n :
      0 < sz →
      length vs = sz →
      chunk_cslice l sz i dq vs ⊢
      chunk_cslice l sz (i + n) dq (rotation (n `mod` sz) vs).
    Proof.
      intros.
      rewrite chunk_cslice_rotation_right //.
    Qed.
    Lemma chunk_cslice_rotation_right_0 {l sz dq vs} i :
      0 < sz →
      length vs = sz →
      chunk_cslice l sz 0 dq vs ⊣⊢
      chunk_cslice l sz i dq (rotation (i `mod` sz) vs).
    Proof.
      intros.
      rewrite chunk_cslice_rotation_right //.
    Qed.

    Lemma chunk_cslice_rotation_right' {l sz i1 dq vs} i2 n :
      0 < sz →
      length vs = sz →
      i2 = i1 + n →
      chunk_cslice l sz i1 dq vs ⊣⊢
      chunk_cslice l sz i2 dq (rotation (n `mod` sz) vs).
    Proof.
      intros Hsz Hvs ->.
      rewrite chunk_cslice_rotation_right //.
    Qed.
    Lemma chunk_cslice_rotation_right_1' {l sz i1 dq vs} i2 n :
      0 < sz →
      length vs = sz →
      i2 = i1 + n →
      chunk_cslice l sz i1 dq vs ⊢
      chunk_cslice l sz i2 dq (rotation (n `mod` sz) vs).
    Proof.
      intros.
      rewrite chunk_cslice_rotation_right' //.
    Qed.

    Lemma chunk_cslice_rotation_left l sz i n dq vs :
      0 < sz →
      length vs = sz →
      chunk_cslice l sz (i + n) dq vs ⊣⊢
      chunk_cslice l sz i dq (rotation (sz - n `mod` sz) vs).
    Proof.
      intros.
      pose ws := (rotation (sz - n `mod` sz) vs).
      replace vs with (rotation (n `mod` sz) ws) at 1; first last.
      { rewrite -(take_drop (sz - n `mod` sz) vs) /ws.
        rewrite /rotation drop_app_length'.
        { simpl_length. lia. }
        rewrite take_app_length' //.
        { simpl_length. lia. }
      }
      rewrite -chunk_cslice_rotation_right //.
      { rewrite /ws. simpl_length. }
    Qed.
    Lemma chunk_cslice_rotation_left_1 l sz i n dq vs :
      0 < sz →
      length vs = sz →
      chunk_cslice l sz (i + n) dq vs ⊢
      chunk_cslice l sz i dq (rotation (sz - n `mod` sz) vs).
    Proof.
      intros.
      rewrite chunk_cslice_rotation_left //.
    Qed.
    Lemma chunk_cslice_rotation_left_0 l sz i dq vs :
      0 < sz →
      length vs = sz →
      chunk_cslice l sz i dq vs ⊣⊢
      chunk_cslice l sz 0 dq (rotation (sz - i `mod` sz) vs).
    Proof.
      apply (chunk_cslice_rotation_left _ _ 0).
    Qed.

    Lemma chunk_cslice_rotation_left' {l sz i1 dq vs} i2 n :
      0 < sz →
      length vs = sz →
      i1 = i2 + n →
      chunk_cslice l sz i1 dq vs ⊣⊢
      chunk_cslice l sz i2 dq (rotation (sz - n `mod` sz) vs).
    Proof.
      intros Hsz Hvs ->.
      rewrite chunk_cslice_rotation_left //.
    Qed.
    Lemma chunk_cslice_rotation_left_1' {l sz i1 dq vs} i2 n :
      0 < sz →
      length vs = sz →
      i1 = i2 + n →
      chunk_cslice l sz i1 dq vs ⊢
      chunk_cslice l sz i2 dq (rotation (sz - n `mod` sz) vs).
    Proof.
      intros.
      rewrite chunk_cslice_rotation_left' //.
    Qed.

    Lemma chunk_cslice_rebase {l sz i1 dq vs1} i2 :
      0 < sz →
      length vs1 = sz →
      chunk_cslice l sz i1 dq vs1 ⊢
        ∃ vs2 n,
        ⌜vs2 = rotation n vs1⌝ ∗
        chunk_cslice l sz i2 dq vs2 ∗
        ( chunk_cslice l sz i2 dq vs2 -∗
          chunk_cslice l sz i1 dq vs1
        ).
    Proof.
      iIntros "%Hsz %Hvs Hcslice".
      destruct_decide (i1 ≤ i2).
      1: iDestruct (chunk_cslice_rotation_right_1' i2 (i2 - i1) with "Hcslice") as "$"; [lia.. |].
      2: iDestruct (chunk_cslice_rotation_left_1' i2 (i1 - i2) with "Hcslice") as "$"; [lia.. |].
      all: iStep.
      all: iIntros "Hcslice".
      1: iDestruct (chunk_cslice_rotation_left_1' i1 (i2 - i1) with "Hcslice") as "Hcslice"; [done | simpl_length | lia |].
      2: iDestruct (chunk_cslice_rotation_right_1' i1 (i1 - i2) with "Hcslice") as "Hcslice"; [done | simpl_length | lia |].
      all: rewrite rotation_add; first lia.
      all: rewrite rotation_length //; first lia.
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
        ⌜✓ (dq1 ⋅ dq2)⌝ ∗
        ⌜vs1 = vs2⌝.
    Proof.
      iIntros "% % Hcslice1 Hcslice2".
      iDestruct (chunk_cslice_combine with "Hcslice1 Hcslice2") as "(-> & Hcslice)"; first done.
      iDestruct (chunk_cslice_valid with "Hcslice") as "$"; first done.
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
    Lemma chunk_cslice_exclusive l sz i vs1 dq2 vs2 :
      0 < length vs1 →
      length vs1 = length vs2 →
      chunk_cslice l sz i (DfracOwn 1) vs1 -∗
      chunk_cslice l sz i dq2 vs2 -∗
      False.
    Proof.
      iIntros "% % Hcslice1 Hcslice2".
      iDestruct (chunk_cslice_ne with "Hcslice1 Hcslice2") as %?; done.
    Qed.
    Lemma chunk_cslice_persist l sz i dq vs :
      chunk_cslice l sz i dq vs ⊢ |==>
      chunk_cslice l sz i DfracDiscarded vs.
    Proof.
      iIntros "Hcslice".
      iApply big_sepL_bupd. iApply (big_sepL_impl with "Hcslice").
      iSteps.
    Qed.

    Lemma chunk_cslice_length l sz i vs :
      0 < sz →
      chunk_cslice l sz i (DfracOwn 1) vs ⊢
      ⌜length vs ≤ sz⌝.
    Proof.
      rewrite Nat.le_ngt.
      iIntros "%Hsz Hcslice %Hvs".
      destruct vs as [| v1 vs]; simpl in Hvs; first lia.
      iDestruct (chunk_cslice_cons with "Hcslice") as "(H↦1 & Hcslice)".
      destruct (lookup_lt_is_Some_2 vs (sz - 1)) as (v2 & Hlookup2); first lia.
      iDestruct (chunk_cslice_lookup with "Hcslice") as "H↦2"; first done.
      replace (S i + (sz - 1)) with (i + sz) by lia.
      rewrite -!Nat2Z.inj_mod -Nat.Div0.add_mod_idemp_r Nat.Div0.mod_same Nat.add_0_r.
      iApply (pointsto_exclusive with "H↦1 H↦2").
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
      - iExists (drop i vs). simpl_length. rewrite Nat.min_l; first lia. iSteps.
      - iIntros "(%vs2 & %Hvs2 & Hmodel2 & Hvs2)".
        iDestruct (chunk_model_app_1 with "Hmodel1 Hmodel2") as "Hmodel".
        { f_equal. simpl_length. lia. }
        iExists (take i vs ++ vs2). simpl_length. rewrite Nat.min_l; first lia. iFrameSteps.
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
      - iExists (take sz' vs). simpl_length. iSteps.
      - iIntros "(%vs1 & %Hvs1 & Hmodel1 & Hvs1)".
        iDestruct (chunk_model_app_1 with "Hmodel1 Hmodel2") as "Hmodel".
        { f_equal. simpl_length. lia. }
        iExists (vs1 ++ drop sz' vs). simpl_length. iFrameSteps.
    Qed.
  End itype_chunk.
End zoo_G.

#[global] Opaque chunk_model.
#[global] Opaque chunk_span.
#[global] Opaque chunk_cslice.
