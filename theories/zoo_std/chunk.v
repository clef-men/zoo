Require Import zoo.prelude.
Require Import zoo.common.list.
Require Import zoo.common.math.
Require Import zoo.base.
Require Import zoo.options.

Implicit Type i n : nat.
Implicit Type l : location.
Implicit Type v : val.
Implicit Type vs : list val.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  Section chunk۰model.
    Definition chunk۰model l dq vs : iProp Σ :=
      l ↦∗{dq} vs.

    #[global] Instance chunk۰modelｰtimeless l dq vs :
      Timeless (chunk۰model l dq vs).
    Proof.
      apply _.
    Qed.

    #[global] Instance chunk۰modelｰpersistent l vs :
      Persistent (chunk۰model l DfracDiscarded vs).
    Proof.
      apply _.
    Qed.

    #[global] Instance chunk۰modelｰfractional l vs :
      Fractional (λ q, chunk۰model l (DfracOwn q) vs).
    Proof.
      apply _.
    Qed.
    #[global] Instance chunk۰modelｰas_fractional l q vs :
      AsFractional (chunk۰model l (DfracOwn q) vs) (λ q, chunk۰model l (DfracOwn q) vs) q.
    Proof.
      split; [done | apply _].
    Qed.

    Lemma chunk۰modelｰnil l dq :
      ⊢ chunk۰model l dq [].
    Proof.
      rewrite /chunk۰model //.
    Qed.

    Lemma chunk۰modelｰsingleton l dq v :
      l ↦{dq} v ⊣⊢
      chunk۰model l dq [v].
    Proof.
      setoid_rewrite big_sepL_singleton. rewrite location۰addｰ0 //.
    Qed.
    Lemma chunk۰modelｰsingleton₁ l dq v :
      l ↦{dq} v ⊢
      chunk۰model l dq [v].
    Proof.
      rewrite chunk۰modelｰsingleton //.
    Qed.
    Lemma chunk۰modelｰsingleton₂ l dq v :
      chunk۰model l dq [v] ⊢
      l ↦{dq} v.
    Proof.
      rewrite chunk۰modelｰsingleton //.
    Qed.

    Lemma chunk۰modelｰapp l dq vs1 vs2 :
      chunk۰model l dq vs1 ∗
      chunk۰model (l +ₗ length vs1) dq vs2 ⊣⊢
      chunk۰model l dq (vs1 ++ vs2).
    Proof.
      setoid_rewrite big_sepL_app.
      setoid_rewrite Nat2Z.inj_add.
      setoid_rewrite <- location۰addｰassoc. done.
    Qed.
    Lemma chunk۰modelｰapp₁ dq l1 vs1 l2 vs2 :
      l2 = l1 +ₗ length vs1 →
      chunk۰model l1 dq vs1 -∗
      chunk۰model l2 dq vs2 -∗
      chunk۰model l1 dq (vs1 ++ vs2).
    Proof.
      rewrite -chunk۰modelｰapp. iSteps.
    Qed.
    Lemma chunk۰modelｰapp₂ {l dq vs} vs1 vs2 :
      vs = vs1 ++ vs2 →
      chunk۰model l dq vs ⊢
        chunk۰model l dq vs1 ∗
        chunk۰model (l +ₗ length vs1) dq vs2.
    Proof.
      rewrite chunk۰modelｰapp. iSteps.
    Qed.

    Lemma chunk۰modelｰappｰ3 l dq vs1 vs2 vs3 :
      chunk۰model l dq vs1 ∗
      chunk۰model (l +ₗ length vs1) dq vs2 ∗
      chunk۰model (l +ₗ ⁺(length vs1 + length vs2)) dq vs3 ⊣⊢
      chunk۰model l dq (vs1 ++ vs2 ++ vs3).
    Proof.
      rewrite -!chunk۰modelｰapp location۰addｰassoc Nat2Z.inj_add //.
    Qed.
    Lemma chunk۰modelｰappｰ3₁ dq l1 vs1 l2 vs2 l3 vs3 :
      l2 = l1 +ₗ length vs1 →
      l3 = l1 +ₗ ⁺(length vs1 + length vs2) →
      chunk۰model l1 dq vs1 -∗
      chunk۰model l2 dq vs2 -∗
      chunk۰model l3 dq vs3 -∗
      chunk۰model l1 dq (vs1 ++ vs2 ++ vs3).
    Proof.
      intros -> ->. rewrite -chunk۰modelｰappｰ3. iSteps.
    Qed.
    Lemma chunk۰modelｰappｰ3₂ {l dq vs} vs1 vs2 vs3 :
      vs = vs1 ++ vs2 ++ vs3 →
      chunk۰model l dq vs ⊢
        chunk۰model l dq vs1 ∗
        chunk۰model (l +ₗ length vs1) dq vs2 ∗
        chunk۰model (l +ₗ ⁺(length vs1 + length vs2)) dq vs3.
    Proof.
      intros ->. rewrite chunk۰modelｰappｰ3 //.
    Qed.

    Lemma chunk۰modelｰcons l dq v vs :
      l ↦{dq} v ∗
      chunk۰model (l +ₗ 1) dq vs ⊣⊢
      chunk۰model l dq (v :: vs).
    Proof.
      assert (v :: vs = [v] ++ vs) as -> by done.
      rewrite -chunk۰modelｰapp chunk۰modelｰsingleton //.
    Qed.
    Lemma chunk۰modelｰcons₁ l dq v vs :
      l ↦{dq} v -∗
      chunk۰model (l +ₗ 1) dq vs -∗
      chunk۰model l dq (v :: vs).
    Proof.
      rewrite -chunk۰modelｰcons. iSteps.
    Qed.
    Lemma chunk۰modelｰcons₂ l dq v vs :
      chunk۰model l dq (v :: vs) ⊢
        l ↦{dq} v ∗
        chunk۰model (l +ₗ 1) dq vs.
    Proof.
      rewrite chunk۰modelｰcons //.
    Qed.
    #[global] Instance chunk۰modelｰconsｰframe l dq v vs R Q :
      Frame false R (l ↦{dq} v ∗ chunk۰model (l +ₗ 1) dq vs) Q →
      Frame false R (chunk۰model l dq (v :: vs)) Q
    | 2.
    Proof.
      rewrite /Frame chunk۰modelｰcons //.
    Qed.

    Lemma chunk۰modelｰupdate {l dq vs} (i : Z) i_ v :
      (0 ≤ i)%Z →
      vs !! i_ = Some v →
      i_ = ₊i →
      chunk۰model l dq vs ⊢
        (l +ₗ i) ↦{dq} v ∗
        ( ∀ w,
          (l +ₗ i) ↦{dq} w -∗
          chunk۰model l dq (<[i_ := w]> vs)
        ).
    Proof.
      intros Hi Hlookup ->.
      Z_to_nat i. rewrite Nat2Z.id in Hlookup |- *.
      iApply big_sepL_insert_acc. done.
    Qed.
    Lemma chunk۰modelｰlookupｰacc {l dq vs} (i : Z) i_ v :
      (0 ≤ i)%Z →
      vs !! i_ = Some v →
      i_ = ₊i →
      chunk۰model l dq vs ⊢
        (l +ₗ i) ↦{dq} v ∗
        ( (l +ₗ i) ↦{dq} v -∗
          chunk۰model l dq vs
        ).
    Proof.
      intros Hi Hlookup ->.
      Z_to_nat i. rewrite Nat2Z.id in Hlookup |- *.
      iApply big_sepL_lookup_acc. done.
    Qed.
    Lemma chunk۰modelｰlookup {l dq vs} (i : Z) i_ v :
      (0 ≤ i)%Z →
      vs !! i_ = Some v →
      i_ = ₊i →
      chunk۰model l dq vs ⊢
      (l +ₗ i) ↦{dq} v.
    Proof.
      intros Hi Hlookup ->.
      Z_to_nat i. rewrite Nat2Z.id in Hlookup |- *.
      iApply big_sepL_lookup. done.
    Qed.

    Lemma chunk۰modelｰupdate' {l} {i : Z} {dq vs} j k v :
      (0 ≤ i ≤ j)%Z →
      vs !! k = Some v →
      k = ₊j - ₊i →
      chunk۰model (l +ₗ i) dq vs ⊢
        (l +ₗ j) ↦{dq} v ∗
        ( ∀ w,
          (l +ₗ j) ↦{dq} w -∗
          chunk۰model (l +ₗ i) dq (<[k := w]> vs)
        ).
    Proof.
      intros Hij Hlookup ->.
      Z_to_nat i. Z_to_nat j. rewrite !Nat2Z.id in Hlookup |- *. remember (j - i) as k eqn:Hk.
      rewrite {1}(chunk۰modelｰupdate k); [lia | done | lia |].
      rewrite location۰addｰassoc -Nat2Z.inj_add Hk -Nat.le_add_sub //. lia.
    Qed.
    Lemma chunk۰modelｰlookupｰacc' {l} {i : Z} {dq vs} j k v :
      (0 ≤ i ≤ j)%Z →
      vs !! k = Some v →
      k = ₊j - ₊i →
      chunk۰model (l +ₗ i) dq vs ⊢
        (l +ₗ j) ↦{dq} v ∗
        ( (l +ₗ j) ↦{dq} v -∗
          chunk۰model (l +ₗ i) dq vs
        ).
    Proof.
      intros Hij Hlookup ->.
      Z_to_nat i. Z_to_nat j. rewrite !Nat2Z.id in Hlookup |- *. remember (j - i) as k eqn:Hk.
      rewrite {1}(chunk۰modelｰlookupｰacc k); [lia | done | lia |].
      rewrite location۰addｰassoc -Nat2Z.inj_add Hk -Nat.le_add_sub //. lia.
    Qed.
    Lemma chunk۰modelｰlookup' {l} {i : Z} {dq vs} j k v :
      (0 ≤ i ≤ j)%Z →
      vs !! k = Some v →
      k = ₊j - ₊i →
      chunk۰model (l +ₗ i) dq vs ⊢
      (l +ₗ j) ↦{dq} v.
    Proof.
      intros Hij Hlookup ->.
      Z_to_nat i. Z_to_nat j. rewrite !Nat2Z.id in Hlookup |- *. remember (j - i) as k eqn:Hk.
      rewrite {1}(chunk۰modelｰlookup k); [lia | done | lia |].
      rewrite location۰addｰassoc -Nat2Z.inj_add Hk -Nat.le_add_sub //. lia.
    Qed.

    Lemma chunk۰modelｰvalid l dq vs :
      0 < length vs →
      chunk۰model l dq vs ⊢
      ⌜✓ dq⌝.
    Proof.
      intros Hvs. destruct vs as [| v vs]; first naive_solver lia.
      iIntros "(H↦ & _)".
      iApply (pointstoｰvalid with "H↦").
    Qed.
    Lemma chunk۰modelｰcombine l dq1 vs1 dq2 vs2 :
      length vs1 = length vs2 →
      chunk۰model l dq1 vs1 -∗
      chunk۰model l dq2 vs2 -∗
        ⌜vs1 = vs2⌝ ∗
        chunk۰model l (dq1 ⋅ dq2) vs1.
    Proof.
      iInduction vs1 as [| v1 vs1] "IH" forall (l vs2); iIntros "% Hmodel1 Hmodel2".
      - rewrite (nil_length_inv vs2) //. naive_solver.
      - destruct vs2 as [| v2 vs2]; first done.
        iDestruct (chunk۰modelｰcons₂ with "Hmodel1") as "(H↦1 & Hmodel1)".
        iDestruct (chunk۰modelｰcons₂ with "Hmodel2") as "(H↦2 & Hmodel2)".
        iDestruct (pointstoｰcombine with "H↦1 H↦2") as "(-> & H↦)".
        iDestruct ("IH" with "[] Hmodel1 Hmodel2") as "(-> & Hmodel)"; first iSteps. iSplit; first iSteps.
        iApply (chunk۰modelｰcons₁ with "H↦ Hmodel").
    Qed.
    Lemma chunk۰modelｰvalidｰ2 l dq1 vs1 dq2 vs2 :
      0 < length vs1 →
      length vs1 = length vs2 →
      chunk۰model l dq1 vs1 -∗
      chunk۰model l dq2 vs2 -∗
        ⌜✓ (dq1 ⋅ dq2)⌝ ∗
        ⌜vs1 = vs2⌝.
    Proof.
      iIntros "% % Hmodel1 Hmodel2".
      iDestruct (chunk۰modelｰcombine with "Hmodel1 Hmodel2") as "(-> & Hmodel)"; first done.
      iDestruct (chunk۰modelｰvalid with "Hmodel") as "$"; first done.
      iSteps.
    Qed.
    Lemma chunk۰modelｰagree l dq1 vs1 dq2 vs2 :
      length vs1 = length vs2 →
      chunk۰model l dq1 vs1 -∗
      chunk۰model l dq2 vs2 -∗
      ⌜vs1 = vs2⌝.
    Proof.
      iIntros "% Hmodel1 Hmodel2".
      iDestruct (chunk۰modelｰcombine with "Hmodel1 Hmodel2") as "($ & _)"; first done.
    Qed.
    Lemma chunk۰modelｰdfracｰne l1 dq1 vs1 l2 dq2 vs2 :
      0 < length vs1 →
      length vs1 = length vs2 →
      ¬ ✓ (dq1 ⋅ dq2) →
      chunk۰model l1 dq1 vs1 -∗
      chunk۰model l2 dq2 vs2 -∗
      ⌜l1 ≠ l2⌝.
    Proof.
      iIntros "% % % Hmodel1 Hmodel2" (->).
      iDestruct (chunk۰modelｰvalidｰ2 with "Hmodel1 Hmodel2") as %?; naive_solver.
    Qed.
    Lemma chunk۰modelｰne l1 vs1 l2 dq2 vs2 :
      0 < length vs1 →
      length vs1 = length vs2 →
      chunk۰model l1 (DfracOwn 1) vs1 -∗
      chunk۰model l2 dq2 vs2 -∗
      ⌜l1 ≠ l2⌝.
    Proof.
      intros.
      iApply chunk۰modelｰdfracｰne; [done.. | intros []%(exclusive_l _)].
    Qed.
    Lemma chunk۰modelｰexclusive l vs1 dq2 vs2 :
      0 < length vs1 →
      length vs1 = length vs2 →
      chunk۰model l (DfracOwn 1) vs1 -∗
      chunk۰model l dq2 vs2 -∗
      False.
    Proof.
      iIntros "% % Hmodel1 Hmodel2".
      iDestruct (chunk۰modelｰne with "Hmodel1 Hmodel2") as %?; done.
    Qed.
    Lemma chunk۰modelｰpersist l dq vs :
      chunk۰model l dq vs ⊢ |==>
      chunk۰model l DfracDiscarded vs.
    Proof.
      iIntros "Hmodel".
      iApply big_sepL_bupd. iApply (big_sepL_impl with "Hmodel").
      iSteps.
    Qed.
  End chunk۰model.

  Section chunk۰span.
    Definition chunk۰span l dq n : iProp Σ :=
      ∃ vs,
      ⌜length vs = n⌝ ∗
      chunk۰model l dq vs.

    #[global] Instance chunk۰spanｰtimeless l dq n :
      Timeless (chunk۰span l dq n).
    Proof.
      apply _.
    Qed.

    #[global] Instance chunk۰spanｰpersistent l n :
      Persistent (chunk۰span l DfracDiscarded n).
    Proof.
      apply _.
    Qed.

    #[global] Instance chunk۰spanｰfractional l n :
      Fractional (λ q, chunk۰span l (DfracOwn q) n).
    Proof.
      intros q1 q2. rewrite /chunk۰span. setoid_rewrite chunk۰modelｰfractional. iSplit; first iSteps.
      iIntros "((%vs & % & Hmodel1) & (%_vs & % & Hmodel2))".
      iDestruct (chunk۰modelｰagree with "Hmodel1 Hmodel2") as %<-; first naive_solver.
      iSteps.
    Qed.
    #[global] Instance chunk۰spanｰas_fractional l q n :
      AsFractional (chunk۰span l (DfracOwn q) n) (λ q, chunk۰span l (DfracOwn q) n) q.
    Proof.
      split; [done | apply _].
    Qed.

    Lemma chunk۰spanｰsingleton l dq :
      ( ∃ v,
        l ↦{dq} v
      ) ⊣⊢
      chunk۰span l dq 1.
    Proof.
      setoid_rewrite chunk۰modelｰsingleton. iSplit.
      - iIntros "(%v & Hmodel)".
        iExists [v]. iSteps.
      - iIntros "(%vs & % & Hmodel)".
        destruct vs as [| v []]; try done. iSteps.
    Qed.
    Lemma chunk۰spanｰsingleton₁ l dq v :
      l ↦{dq} v ⊢
      chunk۰span l dq 1.
    Proof.
      rewrite -chunk۰spanｰsingleton. iSteps.
    Qed.
    Lemma chunk۰spanｰsingleton₂ l dq :
      chunk۰span l dq 1 ⊢
        ∃ v,
        l ↦{dq} v.
    Proof.
      rewrite chunk۰spanｰsingleton. iSteps.
    Qed.

    Lemma chunk۰spanｰcons l dq n :
      ( ∃ v,
        l ↦{dq} v ∗
        chunk۰span (l +ₗ 1) dq n
      ) ⊣⊢
      chunk۰span l dq ˖n.
    Proof.
      iSplit.
      - iIntros "(%v & H↦ & (%vs & % & Hmodel))".
        iExists (v :: vs). iSplit; first iSteps.
        iApply (chunk۰modelｰcons₁ with "H↦ Hmodel").
      - iIntros "(%vs & % & Hmodel)".
        destruct vs as [| v vs]; first done.
        iDestruct (chunk۰modelｰcons₂ with "Hmodel") as "(H↦ & Hmodel)".
        iExists v. iFrameSteps.
    Qed.
    Lemma chunk۰spanｰcons₁ l dq v n :
      l ↦{dq} v -∗
      chunk۰span (l +ₗ 1) dq n -∗
      chunk۰span l dq ˖n.
    Proof.
      rewrite -chunk۰spanｰcons. iSteps.
    Qed.
    Lemma chunk۰spanｰcons₂ l dq n :
      chunk۰span l dq ˖n ⊢
        ∃ v,
        l ↦{dq} v ∗
        chunk۰span (l +ₗ 1) dq n.
    Proof.
      rewrite chunk۰spanｰcons //.
    Qed.
    #[global] Instance chunk۰spanｰconsｰframe l dq v n R Q :
      Frame false R (l ↦{dq} v ∗ chunk۰span (l +ₗ 1) dq n) Q →
      Frame false R (chunk۰span l dq ˖n) Q
    | 2.
    Proof.
      rewrite /Frame. setoid_rewrite <- chunk۰spanｰcons. intros H.
      iPoseProof H as "H". iSteps.
    Qed.

    Lemma chunk۰spanｰapp l dq n1 n2 :
      chunk۰span l dq n1 ∗
      chunk۰span (l +ₗ n1) dq n2 ⊣⊢
      chunk۰span l dq (n1 + n2).
    Proof.
      iSplit.
      - iIntros "((%vs1 & % & Hmodel1) & (%vs2 & % & Hmodel2))".
        iExists (vs1 ++ vs2). iSplit; first (simp_length; naive_solver).
        iApply (chunk۰modelｰapp₁ with "Hmodel1 Hmodel2"); first congruence.
      - iIntros "(%vs & % & Hmodel)".
        iDestruct (chunk۰modelｰapp₂ (take n1 vs) (drop n1 vs) with "Hmodel") as "(Hmodel1 & Hmodel2)"; first rewrite take_drop //.
        iSplitL "Hmodel1".
        + iExists (take n1 vs). simp_length. iSteps.
        + iExists (drop n1 vs). simp_length. rewrite Nat.min_l; first lia. iSteps.
    Qed.
    Lemma chunk۰spanｰapp₁ dq l1 (n1 : nat) l2 n2 :
      l2 = l1 +ₗ n1 →
      chunk۰span l1 dq n1 -∗
      chunk۰span l2 dq n2 -∗
      chunk۰span l1 dq (n1 + n2).
    Proof.
      intros ->. rewrite -chunk۰spanｰapp. iSteps.
    Qed.
    Lemma chunk۰spanｰapp₂ {l dq n} n1 n2 :
      n = n1 + n2 →
      chunk۰span l dq n ⊢
        chunk۰span l dq n1 ∗
        chunk۰span (l +ₗ n1) dq n2.
    Proof.
      intros ->. rewrite chunk۰spanｰapp //.
    Qed.

    Lemma chunk۰spanｰappｰ3 l dq n1 (n2 : nat) n3 :
      chunk۰span l dq n1 ∗
      chunk۰span (l +ₗ n1) dq n2 ∗
      chunk۰span (l +ₗ ⁺(n1 + n2)) dq n3 ⊣⊢
      chunk۰span l dq (n1 + n2 + n3).
    Proof.
      rewrite -!chunk۰spanｰapp. iSteps.
    Qed.
    Lemma chunk۰spanｰappｰ3₁ dq l1 n1 l2 n2 l3 n3 :
      l2 = l1 +ₗ n1 →
      l3 = l1 +ₗ ⁺(n1 + n2) →
      chunk۰span l1 dq n1 -∗
      chunk۰span l2 dq n2 -∗
      chunk۰span l3 dq n3 -∗
      chunk۰span l1 dq (n1 + n2 + n3).
    Proof.
      intros -> ->. rewrite -chunk۰spanｰappｰ3. iSteps.
    Qed.
    Lemma chunk۰spanｰappｰ3₂ {l dq n} n1 n2 n3 :
      n = n1 + n2 + n3 →
      chunk۰span l dq n ⊢
        chunk۰span l dq n1 ∗
        chunk۰span (l +ₗ n1) dq n2 ∗
        chunk۰span (l +ₗ ⁺(n1 + n2)) dq n3.
    Proof.
      intros ->. rewrite chunk۰spanｰappｰ3 //.
    Qed.

    Lemma chunk۰spanｰupdate {l dq n} (i : Z) :
      (0 ≤ i < n)%Z →
      chunk۰span l dq n ⊢
        ∃ v,
        (l +ₗ i) ↦{dq} v ∗
        ( ∀ w,
          (l +ₗ i) ↦{dq} w -∗
          chunk۰span l dq n
        ).
    Proof.
      iIntros "%Hi (%vs & %Hvs & Hmodel)".
      iDestruct (chunk۰modelｰupdate i with "Hmodel") as "(H↦ & Hmodel)"; [lia | | done |].
      { rewrite list_lookup_lookup_total_lt; naive_solver lia. }
      iExists (vs !!! ₊i). iFrame. iIntros "%v H↦".
      iExists (<[₊i := v]> vs). iSplit; first simp_length.
      iSteps.
    Qed.
    Lemma chunk۰spanｰlookupｰacc {l dq n} (i : Z) :
      (0 ≤ i < n)%Z →
      chunk۰span l dq n ⊢
        ∃ v,
        (l +ₗ i) ↦{dq} v ∗
        ( (l +ₗ i) ↦{dq} v -∗
          chunk۰span l dq n
        ).
    Proof.
      iIntros "%Hi Hspan".
      iDestruct (chunk۰spanｰupdate with "Hspan") as "(%v & H↦ & Hspan)"; first done.
      auto with iFrame.
    Qed.
    Lemma chunk۰spanｰlookup {l dq n} (i : Z) :
      (0 ≤ i < n)%Z →
      chunk۰span l dq n ⊢
        ∃ v,
        (l +ₗ i) ↦{dq} v.
    Proof.
      iIntros "%Hi Hspan".
      iDestruct (chunk۰spanｰlookupｰacc with "Hspan") as "(%v & H↦ & _)"; first done.
      iSteps.
    Qed.

    Lemma chunk۰spanｰupdate' {l} {i : Z} {dq n} j :
      (0 ≤ i ≤ j ∧ j < i + n)%Z →
      chunk۰span (l +ₗ i) dq n ⊢
        ∃ v,
        (l +ₗ j) ↦{dq} v ∗
        ( ∀ w,
          (l +ₗ j) ↦{dq} w -∗
          chunk۰span (l +ₗ i) dq n
        ).
    Proof.
      intros Hij.
      Z_to_nat i. Z_to_nat j. remember (j - i) as k eqn:Hk.
      rewrite {1}(chunk۰spanｰupdate k); first lia.
      rewrite location۰addｰassoc -Nat2Z.inj_add Hk -Nat.le_add_sub //. lia.
    Qed.
    Lemma chunk۰spanｰlookupｰacc' {l} {i : Z} {dq n} j :
      (0 ≤ i ≤ j ∧ j < i + n)%Z →
      chunk۰span (l +ₗ i) dq n ⊢
        ∃ v,
        (l +ₗ j) ↦{dq} v ∗
        ( (l +ₗ j) ↦{dq} v -∗
          chunk۰span (l +ₗ i) dq n
        ).
    Proof.
      intros Hij.
      Z_to_nat i. Z_to_nat j. remember (j - i) as k eqn:Hk.
      rewrite {1}(chunk۰spanｰlookupｰacc k); first lia.
      rewrite location۰addｰassoc -Nat2Z.inj_add Hk -Nat.le_add_sub //. lia.
    Qed.
    Lemma chunk۰spanｰlookup' {l} {i : Z} {dq n} j :
      (0 ≤ i ≤ j ∧ j < i + n)%Z →
      chunk۰span (l +ₗ i) dq n ⊢
        ∃ v,
        (l +ₗ j) ↦{dq} v.
    Proof.
      intros Hij.
      Z_to_nat i. Z_to_nat j. remember (j - i) as k eqn:Hk.
      rewrite {1}(chunk۰spanｰlookup k); first lia.
      rewrite location۰addｰassoc -Nat2Z.inj_add Hk -Nat.le_add_sub //. lia.
    Qed.

    Lemma chunk۰spanｰvalid l dq n :
      0 < n →
      chunk۰span l dq n ⊢
      ⌜✓ dq⌝.
    Proof.
      iIntros "% (%vs & % & Hmodel)".
      iApply (chunk۰modelｰvalid with "Hmodel"); first naive_solver.
    Qed.
    Lemma chunk۰spanｰcombine l dq1 n1 dq2 n2 :
      n1 = n2 →
      chunk۰span l dq1 n1 -∗
      chunk۰span l dq2 n2 -∗
      chunk۰span l (dq1 ⋅ dq2) n1.
    Proof.
      iIntros (<-) "(%vs1 & % & Hmodel1) (%vs2 & % & Hmodel2)".
      iDestruct (chunk۰modelｰcombine with "Hmodel1 Hmodel2") as "(<- & Hmodel)"; first naive_solver.
      iSteps.
    Qed.
    Lemma chunk۰spanｰvalidｰ2 l dq1 n1 dq2 n2 :
      n1 = n2 →
      0 < n1 →
      chunk۰span l dq1 n1 -∗
      chunk۰span l dq2 n2 -∗
      ⌜✓ (dq1 ⋅ dq2)⌝.
    Proof.
      iIntros "% % Hspan1 Hspan2".
      iDestruct (chunk۰spanｰcombine with "Hspan1 Hspan2") as "Hspan"; first done.
      iDestruct (chunk۰spanｰvalid with "Hspan") as "$"; first done.
    Qed.
    Lemma chunk۰spanｰdfracｰne l1 dq1 n1 l2 dq2 n2 :
      n1 = n2 →
      0 < n1 →
      ¬ ✓ (dq1 ⋅ dq2) →
      chunk۰span l1 dq1 n1 -∗
      chunk۰span l2 dq2 n2 -∗
      ⌜l1 ≠ l2⌝.
    Proof.
      iIntros "% % % Hspan1 Hspan2" (->).
      iDestruct (chunk۰spanｰvalidｰ2 with "Hspan1 Hspan2") as %?; done.
    Qed.
    Lemma chunk۰spanｰne l1 n1 l2 dq2 n2 :
      n1 = n2 →
      0 < n1 →
      chunk۰span l1 (DfracOwn 1) n1 -∗
      chunk۰span l2 dq2 n2 -∗
      ⌜l1 ≠ l2⌝.
    Proof.
      intros.
      iApply chunk۰spanｰdfracｰne; [done.. | intros []%(exclusive_l _)].
    Qed.
    Lemma chunk۰spanｰexclusive l n1 dq2 n2 :
      n1 = n2 →
      0 < n1 →
      chunk۰span l (DfracOwn 1) n1 -∗
      chunk۰span l dq2 n2 -∗
      False.
    Proof.
      iIntros "% % Hspan1 Hspan2".
      iDestruct (chunk۰spanｰne with "Hspan1 Hspan2") as %?; done.
    Qed.
    Lemma chunk۰spanｰpersist l dq n :
      chunk۰span l dq n ⊢ |==>
      chunk۰span l DfracDiscarded n.
    Proof.
      iIntros "(%vs & % & Hmodel)".
      iMod (chunk۰modelｰpersist with "Hmodel") as "Hmodel".
      iSteps.
    Qed.
  End chunk۰span.

  Section chunk۰cslice.
    Implicit Type sz : nat.

    Definition chunk۰cslice l sz i dq vs : iProp Σ :=
      [∗ list] k ↦ v ∈ vs, (l +ₗ (i + k) `mod` sz) ↦{dq} v.

    #[global] Instance chunk۰csliceｰtimeless l sz i dq vs :
      Timeless (chunk۰cslice l sz i dq vs).
    Proof.
      apply _.
    Qed.

    #[global] Instance chunk۰csliceｰpersistent l sz i vs :
      Persistent (chunk۰cslice l sz i DfracDiscarded vs).
    Proof.
      apply _.
    Qed.

    #[global] Instance chunk۰csliceｰfractional l sz i vs :
      Fractional (λ q, chunk۰cslice l sz i (DfracOwn q) vs).
    Proof.
      apply _.
    Qed.
    #[global] Instance chunk۰csliceｰas_fractionak l sz i q vs :
      AsFractional (chunk۰cslice l sz i (DfracOwn q) vs) (λ q, chunk۰cslice l sz i (DfracOwn q) vs) q.
    Proof.
      split; [done | apply _].
    Qed.

    Lemma chunk۰modelｰtoｰcslice l dq vs :
      chunk۰model l dq vs ⊢
      chunk۰cslice l (length vs) 0 dq vs.
    Proof.
      iIntros "Hmodel".
      iApply (big_sepL_impl with "Hmodel"). iIntros (k v Hk%lookup_lt_Some) "!> H↦".
      rewrite Z.add_0_l Z.mod_small //; first lia.
    Qed.
    Lemma chunkｰmodelｰcsliceｰcell l i sz dq v :
      chunk۰model (l +ₗ i `mod` sz) dq [v] ⊣⊢
      chunk۰cslice l sz i dq [v].
    Proof.
      rewrite /chunk۰model /chunk۰cslice.
      rewrite !big_sepL_singleton location۰addｰ0 right_id //.
    Qed.

    Lemma chunk۰csliceｰnil l sz i dq :
      ⊢ chunk۰cslice l sz i dq [].
    Proof.
      rewrite /chunk۰cslice //.
    Qed.

    Lemma chunk۰csliceｰsingleton l sz i dq v :
      (l +ₗ i `mod` sz) ↦{dq} v ⊣⊢
      chunk۰cslice l sz i dq [v].
    Proof.
      setoid_rewrite big_sepL_singleton. rewrite right_id //.
    Qed.
    Lemma chunk۰csliceｰsingleton₁ l sz i dq v :
      (l +ₗ i `mod` sz) ↦{dq} v ⊢
      chunk۰cslice l sz i dq [v].
    Proof.
      rewrite chunk۰csliceｰsingleton //.
    Qed.
    Lemma chunk۰csliceｰsingleton₂ l sz i dq v :
      chunk۰cslice l sz i dq [v] ⊢
      (l +ₗ i `mod` sz) ↦{dq} v.
    Proof.
      rewrite chunk۰csliceｰsingleton //.
    Qed.

    Lemma chunk۰csliceｰapp l sz i dq vs1 vs2 :
      chunk۰cslice l sz i dq vs1 ∗
      chunk۰cslice l sz (i + length vs1) dq vs2 ⊣⊢
      chunk۰cslice l sz i dq (vs1 ++ vs2).
    Proof.
      rewrite /chunk۰cslice Nat2Z.inj_add.
      setoid_rewrite <- (assoc Z.add).
      setoid_rewrite <- Nat2Z.inj_add at 2.
      rewrite big_sepL_app //.
    Qed.
    Lemma chunk۰csliceｰapp₁ l sz dq i1 vs1 i2 vs2 :
      i2 = i1 + length vs1 →
      chunk۰cslice l sz i1 dq vs1 -∗
      chunk۰cslice l sz i2 dq vs2 -∗
      chunk۰cslice l sz i1 dq (vs1 ++ vs2).
    Proof.
      rewrite -chunk۰csliceｰapp. iSteps.
    Qed.
    Lemma chunk۰csliceｰapp₂ {l sz i dq vs} vs1 vs2 :
      vs = vs1 ++ vs2 →
      chunk۰cslice l sz i dq vs ⊢
        chunk۰cslice l sz i dq vs1 ∗
        chunk۰cslice l sz (i + length vs1) dq vs2.
    Proof.
      rewrite chunk۰csliceｰapp. iSteps.
    Qed.

    Lemma chunk۰csliceｰappｰ3 {l sz i dq vs} n1 i1 n2 i2 :
      i1 = i + n1 →
      i2 = i1 + n2 →
      n1 ≤ length vs →
      n1 + n2 ≤ length vs →
      chunk۰cslice l sz i dq vs ⊣⊢
        chunk۰cslice l sz i dq (take n1 vs) ∗
        chunk۰cslice l sz i1 dq (take n2 $ drop n1 vs) ∗
        chunk۰cslice l sz i2 dq (drop (n1 + n2) vs).
    Proof.
      intros -> -> ? ?.
      rewrite -{1}(take_drop n1 vs).
      rewrite -{1}(take_drop n2 (drop n1 vs)) drop_drop.
      rewrite -!chunk۰csliceｰapp. simp_length.
      rewrite !Nat.min_l //; first lia.
    Qed.

    Lemma chunk۰csliceｰcons l sz i dq v vs :
      (l +ₗ i `mod` sz) ↦{dq} v ∗
      chunk۰cslice l sz ˖i dq vs ⊣⊢
      chunk۰cslice l sz i dq (v :: vs).
    Proof.
      assert (v :: vs = [v] ++ vs) as -> by done.
      rewrite -chunk۰csliceｰapp chunk۰csliceｰsingleton Nat.add_1_r //.
    Qed.
    Lemma chunk۰csliceｰcons₁ l sz i dq v vs :
      (l +ₗ i `mod` sz) ↦{dq} v -∗
      chunk۰cslice l sz ˖i dq vs -∗
      chunk۰cslice l sz i dq (v :: vs).
    Proof.
      rewrite -chunk۰csliceｰcons. iSteps.
    Qed.
    Lemma chunk۰csliceｰcons₂ l sz i dq v vs :
      chunk۰cslice l sz i dq (v :: vs) ⊢
        (l +ₗ i `mod` sz) ↦{dq} v ∗
        chunk۰cslice l sz ˖i dq vs.
    Proof.
      rewrite chunk۰csliceｰcons //.
    Qed.

    Lemma chunk۰csliceｰupdate {l sz i dq vs} k v :
      vs !! k = Some v →
      chunk۰cslice l sz i dq vs ⊢
        (l +ₗ ⁺(i + k) `mod` sz) ↦{dq} v ∗
        ( ∀ w,
          (l +ₗ ⁺(i + k) `mod` sz) ↦{dq} w -∗
          chunk۰cslice l sz i dq (<[k := w]> vs)
        ).
    Proof.
      rewrite Nat2Z.inj_add. apply: big_sepL_insert_acc.
    Qed.
    Lemma chunk۰csliceｰlookupｰacc {l sz i dq vs} k v :
      vs !! k = Some v →
      chunk۰cslice l sz i dq vs ⊢
        (l +ₗ ⁺(i + k) `mod` sz) ↦{dq} v ∗
        ( (l +ₗ ⁺(i + k) `mod` sz) ↦{dq} v -∗
          chunk۰cslice l sz i dq vs
        ).
    Proof.
      rewrite Nat2Z.inj_add. apply: big_sepL_lookup_acc.
    Qed.
    Lemma chunk۰csliceｰlookup {l sz i dq vs} k v :
      vs !! k = Some v →
      chunk۰cslice l sz i dq vs ⊢
      (l +ₗ ⁺(i + k) `mod` sz) ↦{dq} v.
    Proof.
      rewrite Nat2Z.inj_add. apply: big_sepL_lookup.
    Qed.

    Lemma chunk۰csliceｰupdate' {l sz i dq vs} j k v :
      (i ≤ j)%Z →
      vs !! k = Some v →
      k = ₊j - i →
      chunk۰cslice l sz i dq vs ⊢
        (l +ₗ j `mod` sz) ↦{dq} v ∗
        ( ∀ w,
          (l +ₗ j `mod` sz) ↦{dq} w -∗
          chunk۰cslice l sz i dq (<[k := w]> vs)
        ).
    Proof.
      intros Hij Hlookup ->.
      remember (₊j - i) as k eqn:Hk.
      rewrite {1}(chunk۰csliceｰupdate k) //.
      replace ⁺(i + k) with j by lia. done.
    Qed.
    Lemma chunk۰csliceｰlookupｰacc' {l sz i dq vs} j k v :
      (i ≤ j)%Z →
      vs !! k = Some v →
      k = ₊j - i →
      chunk۰cslice l sz i dq vs ⊢
        (l +ₗ j `mod` sz) ↦{dq} v ∗
        ( (l +ₗ j `mod` sz) ↦{dq} v -∗
          chunk۰cslice l sz i dq vs
        ).
    Proof.
      intros Hij Hlookup ->.
      remember (₊j - i) as k eqn:Hk.
      rewrite {1}(chunk۰csliceｰlookupｰacc k) //.
      replace ⁺(i + k) with j by lia. done.
    Qed.
    Lemma chunk۰csliceｰlookup' {l sz i dq vs} j k v :
      (i ≤ j)%Z →
      vs !! k = Some v →
      k = ₊j - i →
      chunk۰cslice l sz i dq vs ⊢
      (l +ₗ j `mod` sz) ↦{dq} v.
    Proof.
      intros Hij Hlookup ->.
      remember (₊j - i) as k eqn:Hk.
      rewrite {1}(chunk۰csliceｰlookup k) //.
      replace ⁺(i + k) with j by lia. done.
    Qed.

    Lemma chunk۰csliceｰshift l sz i dq vs :
      chunk۰cslice l sz i dq vs ⊣⊢
      chunk۰cslice l sz (i + sz) dq vs.
    Proof.
      rewrite /chunk۰cslice.
      setoid_rewrite <- Nat2Z.inj_add at 2.
      setoid_rewrite (comm Nat.add) at 2.
      setoid_rewrite <- (assoc Nat.add).
      do 2 setoid_rewrite Nat2Z.inj_add.
      setoid_rewrite <- Zplus_mod_idemp_l at 2.
      setoid_rewrite Z_mod_same_full.
      setoid_rewrite Z.add_0_l at 7.
      done.
    Qed.

    Lemma chunk۰csliceｰshiftｰright l sz i dq vs :
      chunk۰cslice l sz i dq vs ⊣⊢
      chunk۰cslice l sz (i + sz) dq vs.
    Proof.
      rewrite chunk۰csliceｰshift //.
    Qed.

    Lemma chunk۰csliceｰshiftｰleft l sz i dq vs :
      sz ≤ i →
      chunk۰cslice l sz i dq vs ⊣⊢
      chunk۰cslice l sz (i - sz) dq vs.
    Proof.
      intros.
      setoid_rewrite chunk۰csliceｰshift at 2.
      replace (i - sz + sz) with i by lia. done.
    Qed.

    Lemma chunk۰csliceｰmod l sz i dq vs :
      0 < sz →
      chunk۰cslice l sz i dq vs ⊣⊢
      chunk۰cslice l sz (i `mod` sz) dq vs.
    Proof.
      intros.
      rewrite /chunk۰cslice Nat2Z.inj_mod.
      setoid_rewrite Z.add_mod_idemp_l; last lia.
      done.
    Qed.

    #[local] Lemma chunk۰csliceｰtoｰmodelｰaux l sz i dq vs :
      0 < sz →
      i + length vs ≤ sz →
      chunk۰cslice l sz i dq vs ⊣⊢
      chunk۰model (l +ₗ i) dq vs.
    Proof.
      intros.
      iSplit.
      all: iIntros "H".
      all: iApply (big_sepL_impl with "H"); iIntros "!>" (k v Hk%lookup_lt_Some) "H↦".
      all: rewrite location۰addｰassoc Z.mod_small //; first lia.
    Qed.
    Lemma chunk۰csliceｰtoｰmodel l sz i dq vs :
      0 < sz →
      length vs ≤ sz →
      chunk۰cslice l sz i dq vs ⊣⊢
        chunk۰model (l +ₗ ⁺(i `mod` sz)) dq (take (sz - i `mod` sz) vs) ∗
        chunk۰model l dq (drop (sz - i `mod` sz) vs).
    Proof.
      intros Hsz Hvs.
      rewrite chunk۰csliceｰmod //.
      destruct_decide (i `mod` sz + length vs ≤ sz).
      - rewrite firstn_all2; first lia.
        rewrite skipn_all2; first lia.
        rewrite chunk۰csliceｰtoｰmodelｰaux //.
        iSteps.
        iApply chunk۰modelｰnil.
      - rewrite -{1}(take_drop (sz - i `mod` sz) vs) -chunk۰csliceｰapp.
        rewrite length_take Nat.min_l; first lia.
        rewrite -Nat.le_add_sub; first lia.
        setoid_rewrite chunk۰csliceｰmod at 2; last done.
        rewrite Nat.Div0.mod_same.
        rewrite chunk۰csliceｰtoｰmodelｰaux //.
        { simp_length. lia. }
        rewrite chunk۰csliceｰtoｰmodelｰaux //.
        { simp_length. lia. }
        rewrite location۰addｰ0 //.
    Qed.
    Lemma chunk۰csliceｰtoｰmodelｰfull l sz i dq vs :
      0 < sz →
      length vs = sz →
      chunk۰cslice l sz i dq vs ⊣⊢
      chunk۰model l dq (rotation (sz - i `mod` sz) vs).
    Proof.
      intros.
      rewrite chunk۰csliceｰtoｰmodel; [lia.. |].
      rewrite -chunk۰modelｰapp length_drop.
      replace (length vs - (sz - i `mod` sz)) with (i `mod` sz) by lia.
      iSteps.
    Qed.

    #[local] Lemma chunk۰csliceｰrotationｰrightｰaux {l sz} i1 i2 dq vs :
      0 < sz →
      length vs = sz →
      i1 `mod` sz ≤ i2 `mod` sz →
      chunk۰cslice l sz i1 dq vs ⊣⊢
      chunk۰cslice l sz i2 dq (rotation (i2 `mod` sz - i1 `mod` sz) vs).
    Proof.
      intros.

      pose j1 := i1 `mod` sz.
      pose j2 := i2 `mod` sz.

      setoid_rewrite chunk۰csliceｰmod; [| done..].

      setoid_rewrite (chunk۰csliceｰappｰ3 (j2 - j1) j2 (sz - j2) sz) at 1; [| lia..].
      setoid_rewrite (chunk۰csliceｰappｰ3 (sz - j2) sz j1 (j1 + sz)) at 4; [| simp_length; lia..].

      rewrite (chunk۰csliceｰshiftｰleft _ _ (j1 + sz)); first lia.
      rewrite Nat.add_sub.
      rewrite (drop_app_length' _ _ (sz - j2 + j1)).
      { simp_length. lia. }

      rewrite (take_app_le _ _ (sz - j2)).
      { simp_length. lia. }
      rewrite (take_drop_commute _ j1 (sz - j2)) take_app_length'.
      { simp_length. lia. }
      rewrite drop_drop.

      iSteps.
    Qed.
    Lemma chunk۰csliceｰrotationｰright {l sz i dq vs} n :
      0 < sz →
      length vs = sz →
      chunk۰cslice l sz i dq vs ⊣⊢
      chunk۰cslice l sz (i + n) dq (rotation (n `mod` sz) vs).
    Proof.
      intros.

      pose i1 := i.
      pose i2 := i + n.

      pose j1 := i1 `mod` sz.
      pose j2 := i2 `mod` sz.

      destruct (Nat.le_ge_cases j1 j2).

      - rewrite chunk۰csliceｰrotationｰrightｰaux // minusｰmod₁'' //; first lia.

      - rewrite (chunk۰csliceｰrotationｰrightｰaux i2 i1) //; first  simp_length.
        rewrite minusｰmod₂; [lia.. |].
        rewrite Nat.add_sub'.
        destruct_decide (n `mod` sz = 0) as -> | ?.
        + rewrite Nat.sub_0_r Nat.Div0.mod_same !rotationｰ0 //.
        + rewrite Nat.mod_small; first lia.
          rewrite /rotation drop_app_length'.
          { simp_length. lia. }
          rewrite take_app_length'.
          { simp_length. lia. }
          rewrite take_drop //.
    Qed.
    Lemma chunk۰csliceｰrotationｰright₁ {l sz i dq vs} n :
      0 < sz →
      length vs = sz →
      chunk۰cslice l sz i dq vs ⊢
      chunk۰cslice l sz (i + n) dq (rotation (n `mod` sz) vs).
    Proof.
      intros.
      rewrite chunk۰csliceｰrotationｰright //.
    Qed.
    Lemma chunk۰csliceｰrotationｰrightｰ0 {l sz dq vs} i :
      0 < sz →
      length vs = sz →
      chunk۰cslice l sz 0 dq vs ⊣⊢
      chunk۰cslice l sz i dq (rotation (i `mod` sz) vs).
    Proof.
      intros.
      rewrite chunk۰csliceｰrotationｰright //.
    Qed.

    Lemma chunk۰csliceｰrotationｰright' {l sz i1 dq vs} i2 n :
      0 < sz →
      length vs = sz →
      i2 = i1 + n →
      chunk۰cslice l sz i1 dq vs ⊣⊢
      chunk۰cslice l sz i2 dq (rotation (n `mod` sz) vs).
    Proof.
      intros Hsz Hvs ->.
      rewrite chunk۰csliceｰrotationｰright //.
    Qed.
    Lemma chunk۰csliceｰrotationｰright₁' {l sz i1 dq vs} i2 n :
      0 < sz →
      length vs = sz →
      i2 = i1 + n →
      chunk۰cslice l sz i1 dq vs ⊢
      chunk۰cslice l sz i2 dq (rotation (n `mod` sz) vs).
    Proof.
      intros.
      rewrite chunk۰csliceｰrotationｰright' //.
    Qed.

    Lemma chunk۰csliceｰrotationｰleft l sz i n dq vs :
      0 < sz →
      length vs = sz →
      chunk۰cslice l sz (i + n) dq vs ⊣⊢
      chunk۰cslice l sz i dq (rotation (sz - n `mod` sz) vs).
    Proof.
      intros.
      pose ws := (rotation (sz - n `mod` sz) vs).
      replace vs with (rotation (n `mod` sz) ws) at 1; first last.
      { rewrite -(take_drop (sz - n `mod` sz) vs) /ws.
        rewrite /rotation drop_app_length'.
        { simp_length. lia. }
        rewrite take_app_length' //.
        { simp_length. lia. }
      }
      rewrite -chunk۰csliceｰrotationｰright //.
      { rewrite /ws. simp_length. }
    Qed.
    Lemma chunk۰csliceｰrotationｰleft₁ l sz i n dq vs :
      0 < sz →
      length vs = sz →
      chunk۰cslice l sz (i + n) dq vs ⊢
      chunk۰cslice l sz i dq (rotation (sz - n `mod` sz) vs).
    Proof.
      intros.
      rewrite chunk۰csliceｰrotationｰleft //.
    Qed.
    Lemma chunk۰csliceｰrotationｰleftｰ0 l sz i dq vs :
      0 < sz →
      length vs = sz →
      chunk۰cslice l sz i dq vs ⊣⊢
      chunk۰cslice l sz 0 dq (rotation (sz - i `mod` sz) vs).
    Proof.
      apply (chunk۰csliceｰrotationｰleft _ _ 0).
    Qed.

    Lemma chunk۰csliceｰrotationｰleft' {l sz i1 dq vs} i2 n :
      0 < sz →
      length vs = sz →
      i1 = i2 + n →
      chunk۰cslice l sz i1 dq vs ⊣⊢
      chunk۰cslice l sz i2 dq (rotation (sz - n `mod` sz) vs).
    Proof.
      intros Hsz Hvs ->.
      rewrite chunk۰csliceｰrotationｰleft //.
    Qed.
    Lemma chunk۰csliceｰrotationｰleft₁' {l sz i1 dq vs} i2 n :
      0 < sz →
      length vs = sz →
      i1 = i2 + n →
      chunk۰cslice l sz i1 dq vs ⊢
      chunk۰cslice l sz i2 dq (rotation (sz - n `mod` sz) vs).
    Proof.
      intros.
      rewrite chunk۰csliceｰrotationｰleft' //.
    Qed.

    Lemma chunk۰csliceｰrebase {l sz i1 dq vs1} i2 :
      0 < sz →
      length vs1 = sz →
      chunk۰cslice l sz i1 dq vs1 ⊢
        ∃ vs2 n,
        ⌜vs2 = rotation n vs1⌝ ∗
        chunk۰cslice l sz i2 dq vs2 ∗
        ( chunk۰cslice l sz i2 dq vs2 -∗
          chunk۰cslice l sz i1 dq vs1
        ).
    Proof.
      iIntros "%Hsz %Hvs Hcslice".
      destruct_decide (i1 ≤ i2).
      1: iDestruct (chunk۰csliceｰrotationｰright₁' i2 (i2 - i1) with "Hcslice") as "$"; [lia.. |].
      2: iDestruct (chunk۰csliceｰrotationｰleft₁' i2 (i1 - i2) with "Hcslice") as "$"; [lia.. |].
      all: iStep.
      all: iIntros "Hcslice".
      1: iDestruct (chunk۰csliceｰrotationｰleft₁' i1 (i2 - i1) with "Hcslice") as "Hcslice"; [done | simp_length | lia |].
      2: iDestruct (chunk۰csliceｰrotationｰright₁' i1 (i1 - i2) with "Hcslice") as "Hcslice"; [done | simp_length | lia |].
      all: rewrite rotationｰadd; first lia.
      all: rewrite rotationｰlength //; first lia.
    Qed.

    Lemma chunk۰csliceｰvalid l sz i dq vs :
      0 < length vs →
      chunk۰cslice l sz i dq vs ⊢
      ⌜✓ dq⌝.
    Proof.
      intros Hvs. destruct vs as [| v vs]; first naive_solver lia.
      iIntros "(H↦ & _)".
      iApply (pointstoｰvalid with "H↦").
    Qed.
    Lemma chunk۰csliceｰcombine l sz i dq1 vs1 dq2 vs2 :
      length vs1 = length vs2 →
      chunk۰cslice l sz i dq1 vs1 -∗
      chunk۰cslice l sz i dq2 vs2 -∗
        ⌜vs1 = vs2⌝ ∗
        chunk۰cslice l sz i (dq1 ⋅ dq2) vs1.
    Proof.
      iInduction vs1 as [| v1 vs1] "IH" forall (i vs2); iIntros "% Hcslice1 Hcslice2".
      - rewrite (nil_length_inv vs2) //. naive_solver.
      - destruct vs2 as [| v2 vs2]; first done.
        iDestruct (chunk۰csliceｰcons₂ with "Hcslice1") as "(H↦1 & Hcslice1)".
        iDestruct (chunk۰csliceｰcons₂ with "Hcslice2") as "(H↦2 & Hcslice2)".
        iDestruct (pointstoｰcombine with "H↦1 H↦2") as "(-> & H↦)".
        iDestruct ("IH" with "[] Hcslice1 Hcslice2") as "(-> & Hcslice)"; first iSteps. iSplit; first iSteps.
        iApply (chunk۰csliceｰcons₁ with "H↦ Hcslice").
    Qed.
    Lemma chunk۰csliceｰvalidｰ2 l sz i dq1 vs1 dq2 vs2 :
      0 < length vs1 →
      length vs1 = length vs2 →
      chunk۰cslice l sz i dq1 vs1 -∗
      chunk۰cslice l sz i dq2 vs2 -∗
        ⌜✓ (dq1 ⋅ dq2)⌝ ∗
        ⌜vs1 = vs2⌝.
    Proof.
      iIntros "% % Hcslice1 Hcslice2".
      iDestruct (chunk۰csliceｰcombine with "Hcslice1 Hcslice2") as "(-> & Hcslice)"; first done.
      iDestruct (chunk۰csliceｰvalid with "Hcslice") as "$"; first done.
      iSteps.
    Qed.
    Lemma chunk۰csliceｰagree l sz i dq1 vs1 dq2 vs2 :
      length vs1 = length vs2 →
      chunk۰cslice l sz i dq1 vs1 -∗
      chunk۰cslice l sz i dq2 vs2 -∗
      ⌜vs1 = vs2⌝.
    Proof.
      iIntros "% Hcslice1 Hcslice2".
      iDestruct (chunk۰csliceｰcombine with "Hcslice1 Hcslice2") as "(-> & _)"; first done.
      iSteps.
    Qed.
    Lemma chunk۰csliceｰdfracｰne l sz i1 dq1 vs1 i2 dq2 vs2 :
      0 < length vs1 →
      length vs1 = length vs2 →
      ¬ ✓ (dq1 ⋅ dq2) →
      chunk۰cslice l sz i1 dq1 vs1 -∗
      chunk۰cslice l sz i2 dq2 vs2 -∗
      ⌜i1 ≠ i2⌝.
    Proof.
      iIntros "% % % Hcslice1 Hcslice2" (->).
      iDestruct (chunk۰csliceｰvalidｰ2 with "Hcslice1 Hcslice2") as %?; naive_solver.
    Qed.
    Lemma chunk۰csliceｰne l sz i1 vs1 i2 dq2 vs2 :
      0 < length vs1 →
      length vs1 = length vs2 →
      chunk۰cslice l sz i1 (DfracOwn 1) vs1 -∗
      chunk۰cslice l sz i2 dq2 vs2 -∗
      ⌜i1 ≠ i2⌝.
    Proof.
      intros.
      iApply chunk۰csliceｰdfracｰne; [done.. | intros []%(exclusive_l _)].
    Qed.
    Lemma chunk۰csliceｰexclusive l sz i vs1 dq2 vs2 :
      0 < length vs1 →
      length vs1 = length vs2 →
      chunk۰cslice l sz i (DfracOwn 1) vs1 -∗
      chunk۰cslice l sz i dq2 vs2 -∗
      False.
    Proof.
      iIntros "% % Hcslice1 Hcslice2".
      iDestruct (chunk۰csliceｰne with "Hcslice1 Hcslice2") as %?; done.
    Qed.
    Lemma chunk۰csliceｰpersist l sz i dq vs :
      chunk۰cslice l sz i dq vs ⊢ |==>
      chunk۰cslice l sz i DfracDiscarded vs.
    Proof.
      iIntros "Hcslice".
      iApply big_sepL_bupd. iApply (big_sepL_impl with "Hcslice").
      iSteps.
    Qed.

    Lemma chunk۰csliceｰlength l sz i vs :
      0 < sz →
      chunk۰cslice l sz i (DfracOwn 1) vs ⊢
      ⌜length vs ≤ sz⌝.
    Proof.
      rewrite Nat.le_ngt.
      iIntros "%Hsz Hcslice %Hvs".
      destruct vs as [| v1 vs]; simpl in Hvs; first lia.
      iDestruct (chunk۰csliceｰcons with "Hcslice") as "(H↦1 & Hcslice)".
      destruct (lookup_lt_is_Some_2 vs (sz - 1)) as (v2 & Hlookup2); first lia.
      iDestruct (chunk۰csliceｰlookup with "Hcslice") as "H↦2"; first done.
      replace (˖i + (sz - 1)) with (i + sz) by lia.
      rewrite -!Nat2Z.inj_mod -Nat.Div0.add_mod_idemp_r Nat.Div0.mod_same Nat.add_0_r.
      iApply (pointstoｰexclusive with "H↦1 H↦2").
    Qed.
  End chunk۰cslice.

  Section itype۰chunk.
    Definition itype۰chunk τ `{!iType _ τ} sz l : iProp Σ :=
      inv nroot (
        ∃ vs,
        ⌜sz = length vs⌝ ∗
        chunk۰model l (DfracOwn 1) vs ∗
        [∗ list] v ∈ vs, τ v
      ).

    #[global] Instance itype۰chunkｰpersistent τ `{!iType _ τ} sz l :
      Persistent (itype۰chunk τ sz l).
    Proof.
      apply _.
    Qed.

    Lemma itype۰chunkｰ0 τ `{!iType _ τ} l :
      ⊢ |={⊤}=>
        itype۰chunk τ 0 l.
    Proof.
      iApply inv_alloc. iExists []. iSteps.
    Qed.

    Lemma itype۰chunkｰshift (i : Z) τ `{!iType _ τ} (sz : nat) l :
      (0 ≤ i ≤ sz)%Z →
      itype۰chunk τ sz l ⊢
      itype۰chunk τ (sz - ₊i) (l +ₗ i).
    Proof.
      iIntros "%Hi #Hl".
      Z_to_nat i. rewrite Nat2Z.id.
      iApply (inv_alter with "Hl"). iIntros "!> !> (%vs & %Hvs & Hmodel & Hvs)".
      rewrite -(take_drop i vs).
      iDestruct (chunk۰modelｰapp₂ with "Hmodel") as "(Hmodel1 & Hmodel2)"; first done.
      iDestruct (big_sepL_app with "Hvs") as "(Hvs1 & Hvs2)".
      iSplitL "Hmodel2 Hvs2".
      - iExists (drop i vs). simp_length. rewrite Nat.min_l; first lia. iSteps.
      - iIntros "(%vs2 & %Hvs2 & Hmodel2 & Hvs2)".
        iDestruct (chunk۰modelｰapp₁ with "Hmodel1 Hmodel2") as "Hmodel".
        { f_equal. simp_length. lia. }
        iExists (take i vs ++ vs2). simp_length. rewrite Nat.min_l; first lia. iFrameSteps.
    Qed.

    Lemma itype۰chunkｰle sz' τ `{!iType _ τ} sz l :
      (sz' ≤ sz) →
      itype۰chunk τ sz l ⊢
      itype۰chunk τ sz' l.
    Proof.
      iIntros "%Hsz #Hl".
      iApply (inv_alter with "Hl"). iIntros "!> !> (%vs & %Hvs & Hmodel & Hvs)".
      rewrite -(take_drop sz' vs).
      iDestruct (chunk۰modelｰapp₂ with "Hmodel") as "(Hmodel1 & Hmodel2)"; first done.
      iDestruct (big_sepL_app with "Hvs") as "(Hvs1 & Hvs2)".
      iSplitL "Hmodel1 Hvs1".
      - iExists (take sz' vs). simp_length. iSteps.
      - iIntros "(%vs1 & %Hvs1 & Hmodel1 & Hvs1)".
        iDestruct (chunk۰modelｰapp₁ with "Hmodel1 Hmodel2") as "Hmodel".
        { f_equal. simp_length. lia. }
        iExists (vs1 ++ drop sz' vs). simp_length. iFrameSteps.
    Qed.
  End itype۰chunk.
End zoo۰G.

#[global] Opaque chunk۰model.
#[global] Opaque chunk۰span.
#[global] Opaque chunk۰cslice.
