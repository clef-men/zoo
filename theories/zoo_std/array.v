Require Import Stdlib.micromega.ZifyNat.

Require Import zoo.prelude.
Require Import zoo.common.list.
Require Import zoo.common.math.
Require Import zoo.iris.bi.big_op.
Require Import zoo.base.
Require Export zoo_std.array__code.
Require Import zoo_std.for_.
Require Import zoo_std.assume.
Require Import zoo_std.chunk.
Require Import zoo.options.

Implicit Types b : bool.
Implicit Types i j k n : nat.
Implicit Types l : location.
Implicit Types v t fn acc : val.
Implicit Types vs vs_left vs_right ws : list val.

Definition array٠unsafe_xchg : val :=
  fun: "t" "i" "v" =>
    Xchg ("t", "i") "v".

Definition array٠unsafe_cas : val :=
  fun: "t" "i" "v1" "v2" =>
    CAS ("t", "i") "v1" "v2".

Definition array٠unsafe_faa : val :=
  fun: "t" "i" "incr" =>
    FAA ("t", "i") "incr".

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  Section array۰inv.
    Definition array۰inv t (sz : nat) : iProp Σ :=
      ∃ l,
      ⌜t = #l⌝ ∗
      l ↦ₕ Header 0 sz.

    #[global] Instance array۰inv𑁒timeless t sz :
      Timeless (array۰inv t sz).
    Proof.
      apply _.
    Qed.

    #[global] Instance array۰inv𑁒persistent t sz :
      Persistent (array۰inv t sz).
    Proof.
      apply _.
    Qed.

    Lemma array۰inv𑁒agree t sz1 sz2 :
      array۰inv t sz1 -∗
      array۰inv t sz2 -∗
      ⌜sz1 = sz2⌝.
    Proof.
      iIntros "(%l & -> & #Hheader1) (%_l & %Heq & #Hheader2)". injection Heq as <-.
      iDestruct (headers۰at𑁒agree with "Hheader1 Hheader2") as %[= ->]. done.
    Qed.
  End array۰inv.

  Section array۰slice.
    Definition array۰slice t i dq vs : iProp Σ :=
      ∃ l,
      ⌜t = #l⌝ ∗
      chunk۰model (l +ₗ i) dq vs.

    #[global] Instance array۰slice𑁒timeless t i dq vs :
      Timeless (array۰slice t i dq vs).
    Proof.
      apply _.
    Qed.

    #[global] Instance array۰slice𑁒persistent t i vs :
      Persistent (array۰slice t i DfracDiscarded vs).
    Proof.
      apply _.
    Qed.

    #[global] Instance array۰slice𑁒fractional t i vs :
      Fractional (λ q, array۰slice t i (DfracOwn q) vs).
    Proof.
      intros q1 q2. iSplit.
      - iIntros "(%l & -> & Hmodel1 & Hmodel2)". iSteps.
      - iIntros "((%l & -> & Hmodel1) & (%_l & %Heq & Hmodel2))". injection Heq as <-.
        iExists l. iSteps.
        iApply chunk۰model𑁒fractional. iSteps.
    Qed.
    #[global] Instance array۰slice𑁒as_fractional t i q vs :
      AsFractional (array۰slice t i (DfracOwn q) vs) (λ q, array۰slice t i (DfracOwn q) vs) q.
    Proof.
      split; [done | apply _].
    Qed.

    Lemma array۰slice𑁒valid t i dq vs :
      0 < length vs →
      array۰slice t i dq vs ⊢
      ⌜✓ dq⌝.
    Proof.
      iIntros "% (%l & -> & Hmodel)".
      iApply (chunk۰model𑁒valid with "Hmodel"); first done.
    Qed.
    Lemma array۰slice𑁒combine t i dq1 vs1 dq2 vs2 :
      length vs1 = length vs2 →
      array۰slice t i dq1 vs1 -∗
      array۰slice t i dq2 vs2 -∗
        ⌜vs1 = vs2⌝ ∗
        array۰slice t i (dq1 ⋅ dq2) vs1.
    Proof.
      iIntros "% (%l & -> & Hmodel1) (%_l & %Heq & Hmodel2)". injection Heq as <-.
      iDestruct (chunk۰model𑁒combine with "Hmodel1 Hmodel2") as "(<- & Hmodel)"; first done.
      iSteps.
    Qed.
    Lemma array۰slice𑁒valid𑁒2 t i dq1 vs1 dq2 vs2 :
      0 < length vs1 →
      length vs1 = length vs2 →
      array۰slice t i dq1 vs1 -∗
      array۰slice t i dq2 vs2 -∗
        ⌜✓ (dq1 ⋅ dq2)⌝ ∗
        ⌜vs1 = vs2⌝.
    Proof.
      iIntros "% % Hslice1 Hslice2".
      iDestruct (array۰slice𑁒combine with "Hslice1 Hslice2") as "($ & Hslice)"; first done.
      iApply (array۰slice𑁒valid with "Hslice"); first done.
    Qed.
    Lemma array۰slice𑁒agree t i dq1 vs1 dq2 vs2 :
      length vs1 = length vs2 →
      array۰slice t i dq1 vs1 -∗
      array۰slice t i dq2 vs2 -∗
      ⌜vs1 = vs2⌝.
    Proof.
      iIntros "% Hslice1 Hslice2".
      iDestruct (array۰slice𑁒combine with "Hslice1 Hslice2") as "($ & _)"; first done.
    Qed.
    Lemma array۰slice𑁒dfrac𑁒ne t1 i1 dq1 vs1 t2 i2 dq2 vs2 :
      0 < length vs1 →
      length vs1 = length vs2 →
      ¬ ✓ (dq1 ⋅ dq2) →
      array۰slice t1 i1 dq1 vs1 -∗
      array۰slice t2 i2 dq2 vs2 -∗
      ⌜t1 ≠ t2 ∨ i1 ≠ i2⌝.
    Proof.
      rewrite -not_and_r. iIntros "% % % Hslice1 Hslice2" ((-> & ->)).
      iDestruct (array۰slice𑁒valid𑁒2 with "Hslice1 Hslice2") as %?; naive_solver.
    Qed.
    Lemma array۰slice𑁒ne t1 i1 vs1 t2 i2 dq2 vs2 :
      0 < length vs1 →
      length vs1 = length vs2 →
      array۰slice t1 i1 (DfracOwn 1) vs1 -∗
      array۰slice t2 i2 dq2 vs2 -∗
      ⌜t1 ≠ t2 ∨ i1 ≠ i2⌝.
    Proof.
      intros.
      iApply array۰slice𑁒dfrac𑁒ne; [done.. | intros []%(exclusive_l _)].
    Qed.
    Lemma array۰slice𑁒exclusive t i vs1 dq2 vs2 :
      0 < length vs1 →
      length vs1 = length vs2 →
      array۰slice t i (DfracOwn 1) vs1 -∗
      array۰slice t i dq2 vs2 -∗
      False.
    Proof.
      iIntros "% % Hslice1 Hslice2".
      iDestruct (array۰slice𑁒ne with "Hslice1 Hslice2") as %?; naive_solver.
    Qed.
    Lemma array۰slice𑁒persist t i dq vs :
      array۰slice t i dq vs ⊢ |==>
      array۰slice t i DfracDiscarded vs.
    Proof.
      iIntros "(%l & -> & Hmodel)".
      iMod (chunk۰model𑁒persist with "Hmodel") as "Hmodel".
      iSteps.
    Qed.

    Lemma array۰slice𑁒nil {t i1 dq1 vs1} i2 dq2 :
      array۰slice t i1 dq1 vs1 ⊢
      array۰slice t i2 dq2 [].
    Proof.
      iSteps.
      iApply chunk۰model𑁒nil.
    Qed.

    Lemma array۰slice𑁒app t i dq vs1 vs2 :
      array۰slice t i dq vs1 ∗
      array۰slice t (i + length vs1) dq vs2 ⊣⊢
      array۰slice t i dq (vs1 ++ vs2).
    Proof.
      iSplit.
      - iIntros "((%l & -> & Hmodel1) & (%_l & %Heq & Hmodel2))". injection Heq as <-.
        rewrite Nat2Z.inj_add -location۰add𑁒assoc.
        iDestruct (chunk۰model𑁒app₁ with "Hmodel1 Hmodel2") as "Hmodel"; first done.
        iSteps.
      - iIntros "(%l & -> & Hmodel)".
        iDestruct (chunk۰model𑁒app with "Hmodel") as "(Hmodel1 & Hmodel2)".
        iSplitL "Hmodel1"; iExists l; first iSteps.
        rewrite location۰add𑁒assoc -Nat2Z.inj_add. iSteps.
    Qed.
    Lemma array۰slice𑁒app₁ t i dq vs1 vs2 :
      array۰slice t i dq vs1 -∗
      array۰slice t (i + length vs1) dq vs2 -∗
      array۰slice t i dq (vs1 ++ vs2).
    Proof.
      rewrite -array۰slice𑁒app. iSteps.
    Qed.
    Lemma array۰slice𑁒app₁' {t dq i1 vs1} i2 vs2 :
      i2 = i1 + length vs1 →
      array۰slice t i1 dq vs1 -∗
      array۰slice t i2 dq vs2 -∗
      array۰slice t i1 dq (vs1 ++ vs2).
    Proof.
      intros ->. apply array۰slice𑁒app₁.
    Qed.
    Lemma array۰slice𑁒app₂ {t i dq vs} vs1 vs2 :
      vs = vs1 ++ vs2 →
      array۰slice t i dq vs ⊢
        array۰slice t i dq vs1 ∗
        array۰slice t (i + length vs1) dq vs2.
    Proof.
      intros ->. rewrite array۰slice𑁒app //.
    Qed.

    Lemma array۰slice𑁒app𑁒3 {t i dq} vs1 vs2 vs3 :
      array۰slice t i dq vs1 ∗
      array۰slice t (i + length vs1) dq vs2 ∗
      array۰slice t (i + length vs1 + length vs2) dq vs3 ⊣⊢
      array۰slice t i dq (vs1 ++ vs2 ++ vs3).
    Proof.
      rewrite !array۰slice𑁒app //.
    Qed.
    Lemma array۰slice𑁒app𑁒3₁ t dq i1 vs1 i2 vs2 i3 vs3 :
      i2 = i1 + length vs1 →
      i3 = i1 + length vs1 + length vs2 →
      array۰slice t i1 dq vs1 -∗
      array۰slice t i2 dq vs2 -∗
      array۰slice t i3 dq vs3 -∗
      array۰slice t i1 dq (vs1 ++ vs2 ++ vs3).
    Proof.
      intros -> ->. rewrite -array۰slice𑁒app𑁒3. iSteps.
    Qed.
    Lemma array۰slice𑁒app𑁒3₂ {t i dq vs} vs1 vs2 vs3 :
      vs = vs1 ++ vs2 ++ vs3 →
      array۰slice t i dq vs ⊢
        array۰slice t i dq vs1 ∗
        array۰slice t (i + length vs1) dq vs2 ∗
        array۰slice t (i + length vs1 + length vs2) dq vs3.
    Proof.
      intros ->. rewrite array۰slice𑁒app𑁒3 //.
    Qed.

    Lemma array۰slice𑁒cons t i dq v vs :
      array۰slice t i dq (v :: vs) ⊣⊢
        array۰slice t i dq [v] ∗
        array۰slice t ˖i dq vs.
    Proof.
      rewrite -Nat.add_1_r array۰slice𑁒app //.
    Qed.
    Lemma array۰slice𑁒cons₁ t i dq v vs :
      array۰slice t i dq (v :: vs) ⊢
        array۰slice t i dq [v] ∗
        array۰slice t ˖i dq vs.
    Proof.
      rewrite array۰slice𑁒cons //.
    Qed.
    Lemma array۰slice𑁒cons₂ t i dq v vs :
      array۰slice t i dq [v] -∗
      array۰slice t ˖i dq vs -∗
      array۰slice t i dq (v :: vs).
    Proof.
      setoid_rewrite array۰slice𑁒cons at 2. iSteps.
    Qed.
    Lemma array۰slice𑁒cons₂' t i1 dq v i2 vs :
      i2 = ˖i1 →
      array۰slice t i1 dq [v] -∗
      array۰slice t i2 dq vs -∗
      array۰slice t i1 dq (v :: vs).
    Proof.
      intros ->.
      apply array۰slice𑁒cons₂.
    Qed.

    Lemma array۰slice𑁒atomize t i dq vs :
      array۰slice t i dq vs ⊢
      [∗ list] j ↦ v ∈ vs,
        array۰slice t (i + j) dq [v].
    Proof.
      iInduction vs as [| v vs] "IH" forall (i); first iSteps.
      iIntros "Hvs".
      iDestruct (array۰slice𑁒cons with "Hvs") as "(Hv & Hvs)".
      rewrite /= Nat.add_0_r. iFrame.
      iDestruct ("IH" with "Hvs") as "Hvs".
      setoid_rewrite Nat.add_succ_comm. iSteps.
    Qed.

    Lemma array۰slice𑁒update {t i dq vs} j v :
      vs !! j = Some v →
      array۰slice t i dq vs ⊢
        array۰slice t (i + j) dq [v] ∗
        ( ∀ w,
          array۰slice t (i + j) dq [w] -∗
          array۰slice t i dq (<[j := w]> vs)
        ).
    Proof.
      iIntros "%Hlookup Hslice".
      pose proof Hlookup as Hj%lookup_lt_Some.
      pose proof Hlookup as <-%take_drop_middle.
      iDestruct (array۰slice𑁒app𑁒3₂ _ [v] with "Hslice") as "(Hslice1 & Hslice2 & Hslice3)"; first done.
      setoid_rewrite insert_app_r_alt; simpl_length; last lia.
      rewrite Nat.min_l; first lia. rewrite Nat.sub_diag /=.
      iFrame. iIntros "%w Hslice2".
      iApply (array۰slice𑁒app𑁒3₁ with "Hslice1 Hslice2 Hslice3"); simpl_length/=; lia.
    Qed.
    Lemma array۰slice𑁒lookup𑁒acc {t i dq vs} j v :
      vs !! j = Some v →
      array۰slice t i dq vs ⊢
        array۰slice t (i + j) dq [v] ∗
        ( array۰slice t (i + j) dq [v] -∗
          array۰slice t i dq vs
        ).
    Proof.
      iIntros "%Hlookup Hslice".
      iDestruct (array۰slice𑁒update with "Hslice") as "(Hv & Hslice)"; first done.
      iSpecialize ("Hslice" $! v). rewrite list_insert_id //. iFrame.
    Qed.
    Lemma array۰slice𑁒lookup {t i dq vs} j v :
      vs !! j = Some v →
      array۰slice t i dq vs ⊢
      array۰slice t (i + j) dq [v].
    Proof.
      intros. rewrite array۰slice𑁒lookup𑁒acc //. iSteps.
    Qed.
  End array۰slice.

  Section array۰model.
    Definition array۰model t dq vs : iProp Σ :=
      ∃ l,
      ⌜t = #l⌝ ∗
      l ↦ₕ Header 0 (length vs) ∗
      chunk۰model l dq vs.

    Lemma array۰model𑁒to𑁒inv t dq vs :
      array۰model t dq vs ⊢
      array۰inv t (length vs).
    Proof.
      iSteps.
    Qed.
    Lemma array۰slice𑁒to𑁒model t sz dq vs :
      sz = length vs →
      array۰inv t sz -∗
      array۰slice t 0 dq vs -∗
      array۰model t dq vs.
    Proof.
      iSteps. rewrite location۰add𑁒0 //.
    Qed.
    Lemma array۰model𑁒to𑁒slice t dq vs :
      array۰model t dq vs ⊣⊢
        array۰inv t (length vs) ∗
        array۰slice t 0 dq vs.
    Proof.
      iSteps; rewrite location۰add𑁒0 //.
    Qed.
    Lemma array۰model𑁒to𑁒slice' t dq vs :
      array۰model t dq vs ⊢
        array۰slice t 0 dq vs ∗
        □ (
          ∀ vs',
          ⌜length vs' = length vs⌝ -∗
          array۰slice t 0 dq vs' -∗
          array۰model t dq vs'
        ).
    Proof.
      setoid_rewrite array۰model𑁒to𑁒slice.
      iIntros "(#Hinv & $) !> %vs' %Hvs' $".
      rewrite -Hvs' //.
    Qed.

    #[global] Instance array۰model𑁒timeless t dq vs :
      Timeless (array۰model t dq vs).
    Proof.
      apply _.
    Qed.

    #[global] Instance array۰model𑁒persistent t vs :
      Persistent (array۰model t DfracDiscarded vs).
    Proof.
      apply _.
    Qed.

    #[global] Instance array۰model𑁒fractional t vs :
      Fractional (λ q, array۰model t (DfracOwn q) vs).
    Proof.
      intros q1 q2. iSplit.
      - iIntros "(%l & -> & #Hheader & Hmodel1 & Hmodel2)". iSteps.
      - iIntros "((%l & -> & #Hheader & Hmodel1) & (%_l & %Heq & _ & Hmodel2))". injection Heq as <-.
        iExists l. iSteps.
        iApply chunk۰model𑁒fractional. iSteps.
    Qed.
    #[global] Instance array۰model𑁒as_fractional t q vs :
      AsFractional (array۰model t (DfracOwn q) vs) (λ q, array۰model t (DfracOwn q) vs) q.
    Proof.
      split; [done | apply _].
    Qed.

    Lemma array𑁒inv𑁒model𑁒agree t sz dq vs :
      array۰inv t sz -∗
      array۰model t dq vs -∗
      ⌜length vs = sz⌝.
    Proof.
      rewrite array۰model𑁒to𑁒inv.
      iIntros "#Hinv1 #Hinv2".
      iDestruct (array۰inv𑁒agree with "Hinv1 Hinv2") as %->. done.
    Qed.

    Lemma array۰model𑁒valid t dq vs :
      0 < length vs →
      array۰model t dq vs ⊢
      ⌜✓ dq⌝.
    Proof.
      iIntros "% (%l & -> & #Hheader & Hmodel)".
      iApply (chunk۰model𑁒valid with "Hmodel"); first done.
    Qed.
    Lemma array۰model𑁒combine t dq1 vs1 dq2 vs2 :
      array۰model t dq1 vs1 -∗
      array۰model t dq2 vs2 -∗
        ⌜vs1 = vs2⌝ ∗
        array۰model t (dq1 ⋅ dq2) vs1.
    Proof.
      iIntros "(%l & -> & #Hheader1 & Hmodel1) (%_l & %Heq & #Hheader2 & Hmodel2)". injection Heq as <-.
      iDestruct (headers۰at𑁒agree with "Hheader1 Hheader2") as %[= Hlength].
      iDestruct (chunk۰model𑁒combine with "Hmodel1 Hmodel2") as "(<- & Hmodel)"; first done.
      iSteps.
    Qed.
    Lemma array۰model𑁒valid𑁒2 t dq1 vs1 dq2 vs2 :
      0 < length vs1 →
      array۰model t dq1 vs1 -∗
      array۰model t dq2 vs2 -∗
        ⌜✓ (dq1 ⋅ dq2)⌝ ∗
        ⌜vs1 = vs2⌝.
    Proof.
      iIntros "% Hmodel1 Hmodel2".
      iDestruct (array۰model𑁒combine with "Hmodel1 Hmodel2") as "($ & Hmodel)".
      iApply (array۰model𑁒valid with "Hmodel"); first done.
    Qed.
    Lemma array۰model𑁒agree t dq1 vs1 dq2 vs2 :
      array۰model t dq1 vs1 -∗
      array۰model t dq2 vs2 -∗
      ⌜vs1 = vs2⌝.
    Proof.
      iIntros "Hmodel1 Hmodel2".
      iDestruct (array۰model𑁒combine with "Hmodel1 Hmodel2") as "($ & _)".
    Qed.
    Lemma array۰model𑁒dfrac𑁒ne t1 dq1 vs1 t2 dq2 vs2 :
      0 < length vs1 →
      ¬ ✓ (dq1 ⋅ dq2) →
      array۰model t1 dq1 vs1 -∗
      array۰model t2 dq2 vs2 -∗
      ⌜t1 ≠ t2⌝.
    Proof.
      iIntros "% % Hmodel1 Hmodel2" (->).
      iDestruct (array۰model𑁒valid𑁒2 with "Hmodel1 Hmodel2") as %?; naive_solver.
    Qed.
    Lemma array۰model𑁒ne t1 vs1 t2 dq2 vs2 :
      0 < length vs1 →
      array۰model t1 (DfracOwn 1) vs1 -∗
      array۰model t2 dq2 vs2 -∗
      ⌜t1 ≠ t2⌝.
    Proof.
      intros.
      iApply array۰model𑁒dfrac𑁒ne; [done.. | intros []%(exclusive_l _)].
    Qed.
    Lemma array۰model𑁒exclusive t vs1 dq2 vs2 :
      0 < length vs1 →
      array۰model t (DfracOwn 1) vs1 -∗
      array۰model t dq2 vs2 -∗
      False.
    Proof.
      iIntros "% Hmodel1 Hmodel2".
      iDestruct (array۰model𑁒ne with "Hmodel1 Hmodel2") as %?; done.
    Qed.
    Lemma array۰model𑁒persist t dq vs :
      array۰model t dq vs ⊢ |==>
      array۰model t DfracDiscarded vs.
    Proof.
      iIntros "(%l & -> & #Hheader & Hmodel)".
      iMod (chunk۰model𑁒persist with "Hmodel") as "Hmodel".
      iSteps.
    Qed.

    Lemma array۰model𑁒atomize t dq vs :
      array۰model t dq vs ⊢
        array۰inv t (length vs) ∗
        [∗ list] i ↦ v ∈ vs,
          array۰slice t i dq [v].
    Proof.
      rewrite array۰model𑁒to𑁒slice array۰slice𑁒atomize.
      iSteps.
    Qed.

    #[local] Typeclasses Opaque array۰slice.
    Lemma array۰model𑁒update {t dq vs} i v :
      vs !! i = Some v →
      array۰model t dq vs ⊢
        array۰inv t (length vs) ∗
        array۰slice t i dq [v] ∗
        ( ∀ w,
          array۰slice t i dq [w] -∗
          array۰model t dq (<[i := w]> vs)
        ).
    Proof.
      intros.
      setoid_rewrite array۰model𑁒to𑁒slice.
      rewrite array۰slice𑁒update //.
      iSteps. simpl_length. iSteps.
    Qed.
    Lemma array۰model𑁒lookup𑁒acc {t dq vs} i v :
      vs !! i = Some v →
      array۰model t dq vs ⊢
        array۰slice t i dq [v] ∗
        ( array۰slice t i dq [v] -∗
          array۰model t dq vs
        ).
    Proof.
      intros.
      rewrite array۰model𑁒to𑁒slice {1}array۰slice𑁒lookup𑁒acc //.
      iSteps.
    Qed.
    Lemma array۰model𑁒lookup {t dq vs} i v :
      vs !! i = Some v →
      array۰model t dq vs ⊢
      array۰slice t i dq [v].
    Proof.
      intros.
      rewrite array۰model𑁒to𑁒slice {1}array۰slice𑁒lookup //.
      iSteps.
    Qed.
  End array۰model.

  Section array۰cslice.
    Definition array۰cslice t (sz : nat) i dq vs : iProp Σ :=
      ∃ l,
      ⌜t = #l⌝ ∗
      l ↦ₕ Header 0 sz ∗
      chunk۰cslice l sz i dq vs.

    Lemma array۰cslice𑁒to𑁒inv t sz i dq vs :
      array۰cslice t sz i dq vs ⊢
      array۰inv t sz.
    Proof.
      iSteps.
    Qed.
    Lemma array۰model𑁒to𑁒cslice t dq vs :
      array۰model t dq vs ⊢
      array۰cslice t (length vs) 0 dq vs.
    Proof.
      rewrite /array۰model /array۰slice /array۰cslice.
      setoid_rewrite chunk۰model𑁒to𑁒cslice. done.
    Qed.
    Lemma array۰cslice𑁒to𑁒slice t sz i dq vs :
      0 < sz →
      length vs ≤ sz →
      array۰cslice t sz i dq vs ⊣⊢
        array۰inv t sz ∗
        array۰slice t (i `mod` sz) dq (take (sz - i `mod` sz) vs) ∗
        array۰slice t 0 dq (drop (sz - i `mod` sz) vs).
    Proof.
      intros Hsz Hvs.
      rewrite /array۰cslice /array۰slice.
      setoid_rewrite chunk۰cslice𑁒to𑁒model; [| done..].
      setoid_rewrite location۰add𑁒0.
      iSteps.
    Qed.
    Lemma array۰cslice𑁒to𑁒slice' t sz i dq vs :
      0 < sz →
      length vs ≤ sz →
      array۰cslice t sz i dq vs ⊢
        array۰slice t (i `mod` sz) dq (take (sz - i `mod` sz) vs) ∗
        array۰slice t 0 dq (drop (sz - i `mod` sz) vs).
    Proof.
      intros Hsz Hvs.
      rewrite array۰cslice𑁒to𑁒slice //.
      iSteps.
    Qed.
    Lemma array۰cslice𑁒to𑁒model t sz i dq vs :
      0 < sz →
      length vs = sz →
      array۰cslice t sz i dq vs ⊣⊢
      array۰model t dq (rotation (sz - i `mod` sz) vs).
    Proof.
      intros Hsz Hvs.
      rewrite /array۰cslice /array۰model.
      setoid_rewrite chunk۰cslice𑁒to𑁒model𑁒full; [| done..].
      rewrite length𑁒rotation Hvs //.
    Qed.
    Lemma array۰cslice𑁒to𑁒slice𑁒cell t sz i dq v :
      array۰cslice t sz i dq [v] ⊣⊢
        array۰inv t sz ∗
        array۰slice t (i `mod` sz) dq [v].
    Proof.
      rewrite /array۰slice Nat2Z.inj_mod.
      setoid_rewrite chunk𑁒model𑁒cslice𑁒cell.
      iSteps.
    Qed.
    Lemma array۰cslice𑁒to𑁒slice𑁒cell' t sz i dq v :
      array۰cslice t sz i dq [v] ⊢
      array۰slice t (i `mod` sz) dq [v].
    Proof.
      rewrite array۰cslice𑁒to𑁒slice𑁒cell.
      iSteps.
    Qed.
    Lemma array۰slice𑁒to𑁒cslice𑁒cell t sz i dq v :
      array۰inv t sz -∗
      array۰slice t (i `mod` sz) dq [v] -∗
      array۰cslice t sz i dq [v].
    Proof.
      rewrite array۰cslice𑁒to𑁒slice𑁒cell.
      iSteps.
    Qed.

    #[global] Instance array۰cslice𑁒timeless t sz i dq vs :
      Timeless (array۰cslice t sz i dq vs).
    Proof.
      apply _.
    Qed.

    #[global] Instance array۰cslice𑁒persistent t sz i vs :
      Persistent (array۰cslice t sz i DfracDiscarded vs).
    Proof.
      apply _.
    Qed.

    #[global] Instance array۰cslice𑁒fractional t sz i vs :
      Fractional (λ q, array۰cslice t sz i (DfracOwn q) vs).
    Proof.
      intros q1 q2. iSplit.
      - iIntros "(%l & -> & #Hheader & (Hcslice1 & Hcslice2))".
        iSteps.
      - iIntros "((%l & -> & #Hheader & Hcslice1) & (%_l & %Heq & _ & Hcslice2))". injection Heq as <-.
        iCombine "Hcslice1 Hcslice2" as "Hcslice".
        iSteps.
    Qed.
    #[global] Instance array۰cslice𑁒as_fractional t sz i q vs :
      AsFractional (array۰cslice t sz i (DfracOwn q) vs) (λ q, array۰cslice t sz i (DfracOwn q) vs) q.
    Proof.
      split; [done | apply _].
    Qed.

    Lemma array𑁒inv𑁒cslice𑁒agree t sz1 sz2 i dq vs :
      array۰inv t sz1 -∗
      array۰cslice t sz2 i dq vs -∗
      ⌜sz1 = sz2⌝.
    Proof.
      rewrite array۰cslice𑁒to𑁒inv.
      iIntros "#Hinv1 #Hinv2".
      iDestruct (array۰inv𑁒agree with "Hinv1 Hinv2") as %->. done.
    Qed.

    Lemma array۰cslice𑁒nil t sz i dq :
      array۰inv t sz ⊢
      array۰cslice t sz i dq [].
    Proof.
      iSteps.
      iApply chunk۰cslice𑁒nil.
    Qed.

    Lemma array۰cslice𑁒app t sz i dq vs1 vs2 :
      array۰cslice t sz i dq vs1 ∗
      array۰cslice t sz (i + length vs1) dq vs2 ⊣⊢
      array۰cslice t sz i dq (vs1 ++ vs2).
    Proof.
      rewrite /array۰cslice. setoid_rewrite <- chunk۰cslice𑁒app. iSteps.
    Qed.
    Lemma array۰cslice𑁒app₁ t sz dq i1 vs1 i2 vs2 :
      i2 = i1 + length vs1 →
      array۰cslice t sz i1 dq vs1 -∗
      array۰cslice t sz i2 dq vs2 -∗
      array۰cslice t sz i1 dq (vs1 ++ vs2).
    Proof.
      rewrite -array۰cslice𑁒app. iSteps.
    Qed.
    Lemma array۰cslice𑁒app₂ {t sz i dq vs} vs1 vs2 :
      vs = vs1 ++ vs2 →
      array۰cslice t sz i dq vs ⊢
        array۰cslice t sz i dq vs1 ∗
        array۰cslice t sz (i + length vs1) dq vs2.
    Proof.
      rewrite array۰cslice𑁒app. iSteps.
    Qed.

    Lemma array۰cslice𑁒app𑁒3 t sz i dq vs1 vs2 vs3 :
      array۰cslice t sz i dq vs1 ∗
      array۰cslice t sz (i + length vs1) dq vs2 ∗
      array۰cslice t sz (i + length vs1 + length vs2) dq vs3 ⊣⊢
      array۰cslice t sz i dq (vs1 ++ vs2 ++ vs3).
    Proof.
      rewrite !array۰cslice𑁒app //.
    Qed.
    Lemma array۰cslice𑁒app𑁒3₁ t sz dq i1 vs1 i2 vs2 i3 vs3 :
      i2 = i1 + length vs1 →
      i3 = i1 + length vs1 + length vs2 →
      array۰cslice t sz i1 dq vs1 -∗
      array۰cslice t sz i2 dq vs2 -∗
      array۰cslice t sz i3 dq vs3 -∗
      array۰cslice t sz i1 dq (vs1 ++ vs2 ++ vs3).
    Proof.
      intros -> ->. rewrite -array۰cslice𑁒app𑁒3. iSteps.
    Qed.
    Lemma array۰cslice𑁒app𑁒3₂ {t sz i dq vs} vs1 vs2 vs3 :
      vs = vs1 ++ vs2 ++ vs3 →
      array۰cslice t sz i dq vs ⊢
        array۰cslice t sz i dq vs1 ∗
        array۰cslice t sz (i + length vs1) dq vs2 ∗
        array۰cslice t sz (i + length vs1 + length vs2) dq vs3.
    Proof.
      intros ->. rewrite array۰cslice𑁒app𑁒3 //.
    Qed.

    Lemma array۰cslice𑁒cons t sz i dq v vs :
      array۰cslice t sz i dq (v :: vs) ⊣⊢
        array۰cslice t sz i dq [v] ∗
        array۰cslice t sz ˖i dq vs.
    Proof.
      rewrite -Nat.add_1_r array۰cslice𑁒app //.
    Qed.
    Lemma array۰cslice𑁒cons₁ t sz i dq v vs :
      array۰cslice t sz i dq (v :: vs) ⊢
        array۰cslice t sz i dq [v] ∗
        array۰cslice t sz ˖i dq vs.
    Proof.
      rewrite array۰cslice𑁒cons //.
    Qed.
    Lemma array۰cslice𑁒cons₂ t sz i dq v vs :
      array۰cslice t sz i dq [v] -∗
      array۰cslice t sz ˖i dq vs -∗
      array۰cslice t sz i dq (v :: vs).
    Proof.
      setoid_rewrite array۰cslice𑁒cons at 2. iSteps.
    Qed.
    Lemma array۰cslice𑁒cons₂' t sz i1 dq v i2 vs :
      i2 = ˖i1 →
      array۰cslice t sz i1 dq [v] -∗
      array۰cslice t sz i2 dq vs -∗
      array۰cslice t sz i1 dq (v :: vs).
    Proof.
      intros ->.
      apply array۰cslice𑁒cons₂.
    Qed.

    Lemma array۰cslice𑁒atomize sz t i dq vs :
      array۰cslice t sz i dq vs ⊢
      [∗ list] j ↦ v ∈ vs,
        array۰cslice t sz (i + j) dq [v].
    Proof.
      iInduction vs as [| v vs] "IH" forall (i); first iSteps.
      iIntros "Hvs".
      iDestruct (array۰cslice𑁒cons with "Hvs") as "(Hv & Hvs)".
      rewrite /= Nat.add_0_r. iFrame.
      iDestruct ("IH" with "Hvs") as "Hvs".
      setoid_rewrite Nat.add_succ_comm. iSteps.
    Qed.

    Lemma array۰cslice𑁒update {t sz i dq vs} j v :
      vs !! j = Some v →
      array۰cslice t sz i dq vs ⊢
        array۰cslice t sz (i + j) dq [v] ∗
        ( ∀ w,
          array۰cslice t sz (i + j) dq [w] -∗
          array۰cslice t sz i dq (<[j := w]> vs)
        ).
    Proof.
      intros.
      rewrite /array۰cslice.
      setoid_rewrite <- chunk۰cslice𑁒singleton.
      setoid_rewrite chunk۰cslice𑁒update at 1; last done.
      iSteps.
    Qed.
    Lemma array۰cslice𑁒lookup𑁒acc {t sz i dq vs} j v :
      vs !! j = Some v →
      array۰cslice t sz i dq vs ⊢
        array۰cslice t sz (i + j) dq [v] ∗
        ( array۰cslice t sz (i + j) dq [v] -∗
          array۰cslice t sz i dq vs
        ).
    Proof.
      iIntros "%Hlookup Hslice".
      iDestruct (array۰cslice𑁒update with "Hslice") as "(Hv & Hslice)"; first done.
      iSpecialize ("Hslice" $! v). rewrite list_insert_id //. iFrame.
    Qed.
    Lemma array۰cslice𑁒lookup {t sz i dq vs} j v :
      vs !! j = Some v →
      array۰cslice t sz i dq vs ⊢
      array۰cslice t sz (i + j) dq [v].
    Proof.
      intros. rewrite array۰cslice𑁒lookup𑁒acc //. iSteps.
    Qed.

    Lemma array۰cslice𑁒shift t sz i dq vs :
      array۰cslice t sz i dq vs ⊣⊢
      array۰cslice t sz (i + sz) dq vs.
    Proof.
      rewrite /array۰cslice.
      setoid_rewrite chunk۰cslice𑁒shift at 1.
      done.
    Qed.

    Lemma array۰cslice𑁒shift𑁒right t sz i dq vs :
      array۰cslice t sz i dq vs ⊢
      array۰cslice t sz (i + sz) dq vs.
    Proof.
      rewrite array۰cslice𑁒shift //.
    Qed.
    Lemma array۰cslice𑁒shift𑁒right' {t sz i1 dq vs} i2 :
      i2 = i1 + sz →
      array۰cslice t sz i1 dq vs ⊢
      array۰cslice t sz i2 dq vs.
    Proof.
      intros ->.
      apply array۰cslice𑁒shift𑁒right.
    Qed.

    Lemma array۰cslice𑁒shift𑁒left t sz i dq vs :
      sz ≤ i →
      array۰cslice t sz i dq vs ⊢
      array۰cslice t sz (i - sz) dq vs.
    Proof.
      intros.
      setoid_rewrite array۰cslice𑁒shift at 2.
      replace (i - sz + sz) with i by lia. done.
    Qed.
    Lemma array۰cslice𑁒shift𑁒left' {t sz i1 dq vs} i2 :
      sz ≤ i1 →
      i2 = i1 - sz →
      array۰cslice t sz i1 dq vs ⊢
      array۰cslice t sz i2 dq vs.
    Proof.
      intros ? ->.
      apply array۰cslice𑁒shift𑁒left. done.
    Qed.

    Lemma array۰cslice𑁒rotation𑁒right {t sz i dq vs} n :
      0 < sz →
      length vs = sz →
      array۰cslice t sz i dq vs ⊣⊢
      array۰cslice t sz (i + n) dq (rotation (n `mod` sz) vs).
    Proof.
      intros.
      rewrite /array۰cslice.
      setoid_rewrite chunk۰cslice𑁒rotation𑁒right at 1; done.
    Qed.
    Lemma array۰cslice𑁒rotation𑁒right₁ {t sz i dq vs} n :
      0 < sz →
      length vs = sz →
      array۰cslice t sz i dq vs ⊢
      array۰cslice t sz (i + n) dq (rotation (n `mod` sz) vs).
    Proof.
      intros.
      rewrite array۰cslice𑁒rotation𑁒right //.
    Qed.
    Lemma array۰cslice𑁒rotation𑁒right𑁒0 {t sz dq vs} i :
      0 < sz →
      length vs = sz →
      array۰cslice t sz 0 dq vs ⊣⊢
      array۰cslice t sz i dq (rotation (i `mod` sz) vs).
    Proof.
      intros.
      rewrite array۰cslice𑁒rotation𑁒right //.
    Qed.

    Lemma array۰cslice𑁒rotation𑁒right' {t sz i1 dq vs} i2 n :
      0 < sz →
      length vs = sz →
      i2 = i1 + n →
      array۰cslice t sz i1 dq vs ⊣⊢
      array۰cslice t sz i2 dq (rotation (n `mod` sz) vs).
    Proof.
      intros Hsz Hvs ->.
      rewrite array۰cslice𑁒rotation𑁒right //.
    Qed.
    Lemma array۰cslice𑁒rotation𑁒right₁' {t sz i1 dq vs} i2 n :
      0 < sz →
      length vs = sz →
      i2 = i1 + n →
      array۰cslice t sz i1 dq vs ⊢
      array۰cslice t sz i2 dq (rotation (n `mod` sz) vs).
    Proof.
      intros.
      rewrite array۰cslice𑁒rotation𑁒right' //.
    Qed.

    Lemma array۰cslice𑁒rotation𑁒right𑁒small {t sz i dq vs} n :
      0 < sz →
      length vs = sz →
      n < sz →
      array۰cslice t sz i dq vs ⊣⊢
      array۰cslice t sz (i + n) dq (rotation n vs).
    Proof.
      intros.
      rewrite array۰cslice𑁒rotation𑁒right // Nat.mod_small //.
    Qed.
    Lemma array۰cslice𑁒rotation𑁒right𑁒small₁ {t sz i dq vs} n :
      0 < sz →
      length vs = sz →
      n < sz →
      array۰cslice t sz i dq vs ⊢
      array۰cslice t sz (i + n) dq (rotation n vs).
    Proof.
      intros.
      rewrite array۰cslice𑁒rotation𑁒right𑁒small //.
    Qed.

    Lemma array۰cslice𑁒rotation𑁒right𑁒small' {t sz i1 dq vs} i2 n :
      0 < sz →
      length vs = sz →
      i2 = i1 + n →
      n < sz →
      array۰cslice t sz i1 dq vs ⊣⊢
      array۰cslice t sz i2 dq (rotation n vs).
    Proof.
      intros Hsz Hvs -> Hn.
      rewrite array۰cslice𑁒rotation𑁒right𑁒small //.
    Qed.
    Lemma array۰cslice𑁒rotation𑁒right𑁒small₁' {t sz i1 dq vs} i2 n :
      0 < sz →
      length vs = sz →
      i2 = i1 + n →
      n < sz →
      array۰cslice t sz i1 dq vs ⊢
      array۰cslice t sz i2 dq (rotation n vs).
    Proof.
      intros.
      rewrite array۰cslice𑁒rotation𑁒right𑁒small' //.
    Qed.

    Lemma array۰cslice𑁒rotation𑁒left t sz i n dq vs :
      0 < sz →
      length vs = sz →
      array۰cslice t sz (i + n) dq vs ⊣⊢
      array۰cslice t sz i dq (rotation (sz - n `mod` sz) vs).
    Proof.
      intros.
      rewrite /array۰cslice.
      setoid_rewrite chunk۰cslice𑁒rotation𑁒left at 1; done.
    Qed.
    Lemma array۰cslice𑁒rotation𑁒left₁ t sz i n dq vs :
      0 < sz →
      length vs = sz →
      array۰cslice t sz (i + n) dq vs ⊢
      array۰cslice t sz i dq (rotation (sz - n `mod` sz) vs).
    Proof.
      intros.
      rewrite array۰cslice𑁒rotation𑁒left //.
    Qed.
    Lemma array۰cslice𑁒rotation𑁒left𑁒0 t sz i dq vs :
      0 < sz →
      length vs = sz →
      array۰cslice t sz i dq vs ⊣⊢
      array۰cslice t sz 0 dq (rotation (sz - i `mod` sz) vs).
    Proof.
      apply (array۰cslice𑁒rotation𑁒left _ _ 0).
    Qed.

    Lemma array۰cslice𑁒rotation𑁒left' {t sz i1 dq vs} i2 n :
      0 < sz →
      length vs = sz →
      i1 = i2 + n →
      array۰cslice t sz i1 dq vs ⊣⊢
      array۰cslice t sz i2 dq (rotation (sz - n `mod` sz) vs).
    Proof.
      intros Hsz Hvs ->.
      rewrite array۰cslice𑁒rotation𑁒left //.
    Qed.
    Lemma array۰cslice𑁒rotation𑁒left₁' {t sz i1 dq vs} i2 n :
      0 < sz →
      length vs = sz →
      i1 = i2 + n →
      array۰cslice t sz i1 dq vs ⊢
      array۰cslice t sz i2 dq (rotation (sz - n `mod` sz) vs).
    Proof.
      intros.
      rewrite array۰cslice𑁒rotation𑁒left' //.
    Qed.

    Lemma array۰cslice𑁒rotation𑁒left𑁒small t sz i n dq vs :
      0 < sz →
      length vs = sz →
      n < sz →
      array۰cslice t sz (i + n) dq vs ⊣⊢
      array۰cslice t sz i dq (rotation (sz - n) vs).
    Proof.
      intros.
      rewrite array۰cslice𑁒rotation𑁒left // Nat.mod_small //.
    Qed.
    Lemma array۰cslice𑁒rotation𑁒left𑁒small₁ t sz i n dq vs :
      0 < sz →
      length vs = sz →
      n < sz →
      array۰cslice t sz (i + n) dq vs ⊢
      array۰cslice t sz i dq (rotation (sz - n) vs).
    Proof.
      intros.
      rewrite array۰cslice𑁒rotation𑁒left𑁒small //.
    Qed.

    Lemma array۰cslice𑁒rotation𑁒left𑁒small' {t sz i1 dq vs} i2 n :
      0 < sz →
      length vs = sz →
      i1 = i2 + n →
      n < sz →
      array۰cslice t sz i1 dq vs ⊣⊢
      array۰cslice t sz i2 dq (rotation (sz - n) vs).
    Proof.
      intros Hsz Hvs -> Hn.
      rewrite array۰cslice𑁒rotation𑁒left𑁒small //.
    Qed.
    Lemma array۰cslice𑁒rotation𑁒left𑁒small₁' {t sz i1 dq vs} i2 n :
      0 < sz →
      length vs = sz →
      i1 = i2 + n →
      n < sz →
      array۰cslice t sz i1 dq vs ⊢
      array۰cslice t sz i2 dq (rotation (sz - n) vs).
    Proof.
      intros.
      rewrite array۰cslice𑁒rotation𑁒left𑁒small' //.
    Qed.

    Lemma array۰cslice𑁒rebase {t sz i1 dq vs1} i2 :
      0 < sz →
      length vs1 = sz →
      array۰cslice t sz i1 dq vs1 ⊢
        ∃ vs2 n,
        ⌜vs2 = rotation n vs1⌝ ∗
        array۰cslice t sz i2 dq vs2 ∗
        ( array۰cslice t sz i2 dq vs2 -∗
          array۰cslice t sz i1 dq vs1
        ).
    Proof.
      intros.
      rewrite /array۰cslice.
      setoid_rewrite chunk۰cslice𑁒rebase at 1; [| done..].
      iSteps.
    Qed.

    Lemma array۰cslice𑁒valid t sz i dq vs :
      0 < length vs →
      array۰cslice t sz i dq vs ⊢
      ⌜✓ dq⌝.
    Proof.
      intros.
      rewrite /array۰cslice.
      setoid_rewrite chunk۰cslice𑁒valid; last done.
      iSteps.
    Qed.
    Lemma array۰cslice𑁒combine t sz i dq1 vs1 dq2 vs2 :
      length vs1 = length vs2 →
      array۰cslice t sz i dq1 vs1 -∗
      array۰cslice t sz i dq2 vs2 -∗
        ⌜vs1 = vs2⌝ ∗
        array۰cslice t sz i (dq1 ⋅ dq2) vs1.
    Proof.
      iIntros "% (%l & -> & #Hheader & Hcslice1) (%_l & %Heq & _ & Hcslice2)". injection Heq as <-.
      iDestruct (chunk۰cslice𑁒combine with "Hcslice1 Hcslice2") as "($ & Hcslice)"; first done.
      iSteps.
    Qed.
    Lemma array۰cslice𑁒valid𑁒2 t sz i dq1 vs1 dq2 vs2 :
      0 < length vs1 →
      length vs1 = length vs2 →
      array۰cslice t sz i dq1 vs1 -∗
      array۰cslice t sz i dq2 vs2 -∗
        ⌜✓ (dq1 ⋅ dq2)⌝ ∗
        ⌜vs1 = vs2⌝.
    Proof.
      iIntros "% % Hcslice1 Hcslice2".
      iDestruct (array۰cslice𑁒combine with "Hcslice1 Hcslice2") as "($ & Hcslice)"; first done.
      iApply (array۰cslice𑁒valid with "Hcslice"); first done.
    Qed.
    Lemma array۰cslice𑁒agree t sz i dq1 vs1 dq2 vs2 :
      length vs1 = length vs2 →
      array۰cslice t sz i dq1 vs1 -∗
      array۰cslice t sz i dq2 vs2 -∗
      ⌜vs1 = vs2⌝.
    Proof.
      iIntros "% Hcslice1 Hcslice2".
      iDestruct (array۰cslice𑁒combine with "Hcslice1 Hcslice2") as "($ & _)"; first done.
    Qed.
    Lemma array۰cslice𑁒dfrac𑁒ne t sz i1 dq1 vs1 i2 dq2 vs2 :
      0 < length vs1 →
      length vs1 = length vs2 →
      ¬ ✓ (dq1 ⋅ dq2) →
      array۰cslice t sz i1 dq1 vs1 -∗
      array۰cslice t sz i2 dq2 vs2 -∗
      ⌜i1 ≠ i2⌝.
    Proof.
      iIntros "% % % Hcslice1 Hcslice2" (->).
      iDestruct (array۰cslice𑁒valid𑁒2 with "Hcslice1 Hcslice2") as %?; naive_solver.
    Qed.
    Lemma array۰cslice𑁒ne t sz i1 vs1 i2 dq2 vs2 :
      0 < length vs1 →
      length vs1 = length vs2 →
      array۰cslice t sz i1 (DfracOwn 1) vs1 -∗
      array۰cslice t sz i2 dq2 vs2 -∗
      ⌜i1 ≠ i2⌝.
    Proof.
      intros.
      iApply array۰cslice𑁒dfrac𑁒ne; [done.. | intros []%(exclusive_l _)].
    Qed.
    Lemma array۰cslice𑁒exclusive t sz i vs1 dq2 vs2 :
      0 < length vs1 →
      length vs1 = length vs2 →
      array۰cslice t sz i (DfracOwn 1) vs1 -∗
      array۰cslice t sz i dq2 vs2 -∗
      False.
    Proof.
      iIntros "% % Hcslice1 Hcslice2".
      iDestruct (array۰cslice𑁒ne with "Hcslice1 Hcslice2") as %?; done.
    Qed.
    Lemma array۰cslice𑁒persist t sz i dq vs :
      array۰cslice t sz i dq vs ⊢ |==>
      array۰cslice t sz i DfracDiscarded vs.
    Proof.
      rewrite /array۰cslice.
      setoid_rewrite chunk۰cslice𑁒persist at 1.
      iSteps.
    Qed.

    Lemma array۰cslice𑁒length t sz i vs :
      0 < sz →
      array۰cslice t sz i (DfracOwn 1) vs ⊢
      ⌜length vs ≤ sz⌝.
    Proof.
      iIntros "%Hsz (%l & -> & _ & Hcslice)".
      iApply (chunk۰cslice𑁒length with "Hcslice"); first done.
    Qed.
  End array۰cslice.

  #[local] Typeclasses Opaque
    array۰inv
    array۰slice
    array۰model
    array۰cslice.

  Notation au_load t i Φ := (
    AU <{
      ∃∃ dq v,
      array۰slice t i dq [v]
    }> @ ⊤, ∅ <{
      array۰slice t i dq [v],
    COMM
      Φ v
    }>
  )%I.
  Notation au_store t i v P := (
    AU <{
      ∃∃ w,
      array۰slice t i (DfracOwn 1) [w]
    }> @ ⊤, ∅ <{
      array۰slice t i (DfracOwn 1) [v],
    COMM
      P
    }>
  )%I.

  Lemma array٠unsafe_alloc𑁒spec sz :
    (0 ≤ sz)%Z →
    {{{
      True
    }}}
      array٠unsafe_alloc #sz
    {{{
      t
    , RET t;
      array۰model t (DfracOwn 1) (replicate ₊sz ()%V)
    }}}.
  Proof.
    rewrite /array۰model /array۰slice.
    iIntros "%Hsz %Φ _ HΦ".
    wp۰rec.
    wp۰alloc l as "#Hheader" "_" "Hl"; [done.. |].
    iSteps. simpl_length. iSteps.
  Qed.

  Lemma array٠alloc𑁒spec sz :
    {{{
      True
    }}}
      array٠alloc #sz
    {{{
      t
    , RET t;
      ⌜0 ≤ sz⌝%Z ∗
      array۰model t (DfracOwn 1) (replicate ₊sz ()%V)
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp۰rec.
    wp۰apply+ assume𑁒spec' as "%Hsz".
    wp۰apply+ (array٠unsafe_alloc𑁒spec with "[//]"); first done.
    iSteps.
  Qed.

  Lemma array٠create𑁒spec :
    {{{
      True
    }}}
      array٠create ()
    {{{
      t
    , RET t;
      array۰model t (DfracOwn 1) []
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp۰rec.
    wp۰apply (array٠unsafe_alloc𑁒spec with "[//]"); first done.
    iSteps.
  Qed.

  Lemma array٠size𑁒spec𑁒inv t sz :
    {{{
      array۰inv t sz
    }}}
      array٠size t
    {{{
      RET #sz;
      True
    }}}.
  Proof.
    rewrite /array۰inv.
    iSteps.
  Qed.
  Lemma array٠size𑁒spec𑁒atomic t :
    <<<
      True
    | ∀∀ dq vs,
      array۰model t dq vs
    >>>
      array٠size t
    <<<
      array۰model t dq vs
    | RET #(length vs);
      £ 1 ∗
      array۰inv t (length vs)
    >>>.
  Proof.
    rewrite /array۰model /array۰inv.
    iIntros "%Φ _ HΦ".
    wp۰rec credit:"H£".
    iMod "HΦ" as "(%dq & %vs & (%l & -> & #Hheader & Hmodel) & _ & HΦ)".
    wp۰size.
    iApply ("HΦ" with "[$Hmodel]"); iSteps.
  Qed.
  Lemma array٠size𑁒spec𑁒atomic𑁒cslice t :
    <<<
      True
    | ∀∀ sz i dq vs,
      array۰cslice t sz i dq vs
    >>>
      array٠size t
    <<<
      array۰cslice t sz i dq vs
    | RET #sz;
      £ 1 ∗
      array۰inv t sz
    >>>.
  Proof.
    rewrite /array۰cslice /array۰inv.
    iIntros "%Φ _ HΦ".
    wp۰rec credit:"H£".
    iMod "HΦ" as "(%sz & %i & %dq & %vs & (%l & -> & #Hheader & Hcslice) & _ & HΦ)".
    wp۰size.
    iApply ("HΦ" with "[Hcslice]"); iSteps.
  Qed.
  Lemma array٠size𑁒spec t dq vs :
    {{{
      array۰model t dq vs
    }}}
      array٠size t
    {{{
      RET #(length vs);
      array۰model t dq vs
    }}}.
  Proof.
    rewrite /array۰model. iSteps.
  Qed.
  Lemma array٠size𑁒spec𑁒cslice t sz i dq vs :
    {{{
      array۰cslice t sz i dq vs
    }}}
      array٠size t
    {{{
      RET #sz;
      array۰cslice t sz i dq vs
    }}}.
  Proof.
    rewrite /array۰cslice. iSteps.
  Qed.

  Lemma array٠unsafe_get𑁒spec𑁒atomic𑁒slice t (j : Z) :
    <<<
      True
    | ∀∀ dq vs i v,
      ⌜(i ≤ j)%Z⌝ ∗
      ⌜vs !! (₊j - i) = Some v⌝ ∗
      array۰slice t i dq vs
    >>>
      array٠unsafe_get t #j
    <<<
      array۰slice t i dq vs
    | RET v;
      £ 1
    >>>.
  Proof.
    rewrite /array۰slice.
    iIntros "%Φ _ HΦ".
    wp۰rec credit:"H£". wp۰pures.
    iMod "HΦ" as "(%dq & %vs & %i & %v & (%Hi & %Hlookup & (%l & -> & Hmodel)) & _ & HΦ)".
    iDestruct (chunk۰model𑁒lookup𑁒acc' j with "Hmodel") as "(H↦ & Hmodel)"; [lia | done | lia |].
    wp۰load.
    iApply ("HΦ" with "[H↦ Hmodel] H£").
    iSteps.
  Qed.
  Lemma array٠unsafe_get𑁒spec𑁒atomic𑁒cell t (i : Z) :
    <<<
      True
    | ∀∀ i_ dq v,
      ⌜i = ⁺i_⌝ ∗
      array۰slice t i_ dq [v]
    >>>
      array٠unsafe_get t #i
    <<<
      array۰slice t ₊i dq [v]
    | RET v;
      £ 1
    >>>.
  Proof.
    iIntros "%Φ _ HΦ".
    awp۰apply (array٠unsafe_get𑁒spec𑁒atomic𑁒slice with "[//]").
    iApply (aacc𑁒aupd𑁒commit with "HΦ"); first done. iIntros "%i_ %dq %v (-> & Hslice)".
    rewrite Nat2Z.id.
    iAaccIntro with "[$Hslice]".
    { rewrite Nat.sub_diag. iSteps. }
    all: iSteps.
  Qed.
  Lemma array٠unsafe_get𑁒spec𑁒atomic t (i : Z) :
    (0 ≤ i)%Z →
    <<<
      True
    | ∀∀ dq vs v,
      ⌜vs !! ₊i = Some v⌝ ∗
      array۰model t dq vs
    >>>
      array٠unsafe_get t #i
    <<<
      array۰model t dq vs
    | RET v;
      £ 1
    >>>.
  Proof.
    iIntros "%Hi %Φ _ HΦ".
    awp۰apply (array٠unsafe_get𑁒spec𑁒atomic𑁒slice with "[//]").
    iApply (aacc𑁒aupd𑁒commit with "HΦ"); first done. iIntros "%dq %vs %v (%Hlookup & Hmodel)".
    iDestruct (array۰model𑁒to𑁒slice' with "Hmodel") as "(Hslice & #?)".
    iAaccIntro with "[$Hslice]".
    { rewrite Nat.sub_0_r. iSteps. }
    all: iSteps.
  Qed.
  Lemma array٠unsafe_get𑁒spec𑁒atomic𑁒inv t (sz : nat) (i : Z) :
    (0 ≤ i < sz)%Z →
    <<<
      array۰inv t sz
    | ∀∀ vs,
      array۰model t (DfracOwn 1) vs
    >>>
      array٠unsafe_get t #i
    <<<
      ∃∃ v,
      ⌜vs !! ₊i = Some v⌝ ∗
      array۰model t (DfracOwn 1) vs
    | RET v;
      £ 1
    >>>.
  Proof.
    iIntros "%Hi %Φ #Hinv HΦ".

    awp۰apply (array٠unsafe_get𑁒spec𑁒atomic with "[//]"); first lia.
    iApply (aacc𑁒aupd𑁒commit with "HΦ"); first done. iIntros "%vs Hmodel".
    iDestruct (array𑁒inv𑁒model𑁒agree with "Hinv Hmodel") as %?.
    destruct (lookup_lt_is_Some_2 vs ₊i) as (v & Hlookup); first lia.
    iAaccIntro with "[$Hmodel]"; iSteps.
  Qed.
  Lemma array٠unsafe_get𑁒spec𑁒slice k t i dq vs (j : Z) v :
    (i ≤ j)%Z →
    vs !! k = Some v →
    k = ₊j - i →
    {{{
      array۰slice t i dq vs
    }}}
      array٠unsafe_get t #j
    {{{
      RET v;
      array۰slice t i dq vs
    }}}.
  Proof.
    iIntros (Hj Hlookup ->) "%Φ Hslice HΦ".
    iApply wp𑁒fupd.
    awp۰apply (array٠unsafe_get𑁒spec𑁒atomic𑁒slice with "[//]") without "HΦ".
    iAaccIntro with "[$Hslice]". 1,2: iSteps. iIntros "Hslice !> H£ HΦ".
    iApply (lc_fupd_elim_later with "H£ HΦ Hslice").
  Qed.
  Lemma array٠unsafe_get𑁒spec𑁒cell t (i : Z) i_ dq v :
    i = ₊i_ →
    {{{
      array۰slice t i_ dq [v]
    }}}
      array٠unsafe_get t #i
    {{{
      RET v;
      array۰slice t i_ dq [v]
    }}}.
  Proof.
    intros.
    eapply (array٠unsafe_get𑁒spec𑁒slice 0); [lia | done | lia].
  Qed.
  Lemma array٠unsafe_get𑁒spec i_ t (i : Z) dq vs v :
    (0 ≤ i)%Z →
    vs !! i_ = Some v →
    i_ = ₊i →
    {{{
      array۰model t dq vs
    }}}
      array٠unsafe_get t #i
    {{{
      RET v;
      array۰model t dq vs
    }}}.
  Proof.
    setoid_rewrite array۰model𑁒to𑁒slice' at 1.
    iIntros (Hi Hlookup ->) "%Φ (Hslice & #?) HΦ".
    wp۰apply (array٠unsafe_get𑁒spec𑁒slice with "Hslice"); [done.. | lia |].
    iSteps.
  Qed.

  Lemma array٠get𑁒spec𑁒atomic𑁒slice t sz (j : Z) :
    <<<
      array۰inv t sz
    | ∀∀ dq vs i v,
      ⌜0 ≤ j < sz⌝%Z -∗
        ⌜i ≤ ₊j⌝ ∗
        ⌜vs !! (₊j - i) = Some v⌝ ∗
        array۰slice t i dq vs
    >>>
      array٠get t #j
    <<<
      array۰slice t i dq vs
    | RET v;
      ⌜0 ≤ j < sz⌝%Z ∗
      £ 1
    >>>.
  Proof.
    iIntros "%Φ #Hinv HΦ".
    wp۰rec.
    wp۰apply+ assume𑁒spec' as "%Hj1".
    wp۰apply+ (array٠size𑁒spec𑁒inv with "Hinv") as "_".
    wp۰apply+ assume𑁒spec' as "%Hj2".
    awp۰apply+ (array٠unsafe_get𑁒spec𑁒atomic𑁒slice with "[//]").
    iApply (aacc𑁒aupd𑁒commit with "HΦ"); first done. iIntros "%dq %vs %i %v H".
    iDestruct ("H" with "[//]") as "(%Hj3 & %Hlookup & Hslice)".
    iAaccIntro with "[$Hslice]". 1,3: iSteps.
    iIntros "(_ & _ & $)". iSteps.
  Qed.
  Lemma array٠get𑁒spec𑁒atomic𑁒cell t sz (i : Z) i_ :
    i_ = ₊i →
    <<<
      array۰inv t sz
    | ∀∀ dq v,
      ⌜0 ≤ i < sz⌝%Z -∗
      array۰slice t i_ dq [v]
    >>>
      array٠get t #i
    <<<
      array۰slice t i_ dq [v]
    | RET v;
      ⌜0 ≤ i < sz⌝%Z ∗
      £ 1
    >>>.
  Proof.
    iIntros (->) "%Φ #Hinv HΦ".
    awp۰apply (array٠get𑁒spec𑁒atomic𑁒slice with "Hinv").
    iApply (aacc𑁒aupd𑁒commit with "HΦ"); first done. iIntros "%dq %v Hslice".
    iAaccIntro _, [v], ₊i with "[Hslice]".
    { rewrite Nat.sub_diag. iSteps. }
    { iIntros "Hslice !>". iSplitL; iSteps. }
    iSteps.
  Qed.
  Lemma array٠get𑁒spec𑁒atomic t sz (i : Z) :
    <<<
      array۰inv t sz
    | ∀∀ dq vs v,
      ⌜0 ≤ i < sz⌝%Z -∗
        ⌜vs !! ₊i = Some v⌝ ∗
        array۰model t dq vs
    >>>
      array٠get t #i
    <<<
      array۰model t dq vs
    | RET v;
      ⌜0 ≤ i < sz⌝%Z ∗
      £ 1
    >>>.
  Proof.
    iIntros "%Φ #Hinv HΦ".
    wp۰rec.
    wp۰apply+ assume𑁒spec' as "%Hi1".
    wp۰apply+ (array٠size𑁒spec𑁒inv with "Hinv") as "_".
    wp۰apply+ assume𑁒spec' as "%Hi2".
    awp۰apply+ (array٠unsafe_get𑁒spec𑁒atomic with "[//]"); first done.
    iApply (aacc𑁒aupd𑁒commit with "HΦ"); first done. iIntros "%dq %vs %v H".
    iDestruct ("H" with "[//]") as "(%Hlookup & Hmodel)".
    iAaccIntro with "[$Hmodel]". 1,3: iSteps.
    iIntros "(_ & $)". iSteps.
  Qed.
  Lemma array٠get𑁒spec𑁒slice k t sz i dq vs (j : Z) v :
    {{{
      array۰inv t sz ∗
      ( ⌜0 ≤ j < sz⌝%Z -∗
          ⌜i ≤ ₊j⌝ ∗
          ⌜vs !! k = Some v⌝ ∗
          ⌜k = ₊j - i⌝ ∗
          array۰slice t i dq vs
      )
    }}}
      array٠get t #j
    {{{
      RET v;
      ⌜0 ≤ j < sz⌝%Z ∗
      array۰slice t i dq vs
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & H) HΦ".
    wp۰rec.
    wp۰apply+ assume𑁒spec' as "%Hj1".
    wp۰apply+ (array٠size𑁒spec𑁒inv with "Hinv") as "_".
    wp۰apply+ assume𑁒spec' as "%Hj2".
    iDestruct ("H" with "[//]") as "(%Hj3 & %Hlookupk & -> & Hslice)".
    wp۰apply+ (array٠unsafe_get𑁒spec𑁒slice with "Hslice"); [lia | done.. |].
    iSteps.
  Qed.
  Lemma array٠get𑁒spec𑁒cell t sz (i : Z) i_ dq v :
    i_ = ₊i →
    {{{
      array۰inv t sz ∗
      ( ⌜0 ≤ i < sz⌝%Z -∗
        array۰slice t i_ dq [v]
      )
    }}}
      array٠get t #i
    {{{
      RET v;
      ⌜0 ≤ i < sz⌝%Z ∗
      array۰slice t i_ dq [v]
    }}}.
  Proof.
    iIntros (->) "%Φ (#Hinv & H) HΦ".
    wp۰apply (array٠get𑁒spec𑁒slice 0 with "[$Hinv H] HΦ").
    iSteps.
  Qed.
  Lemma array٠get𑁒spec t (i : Z) dq vs v :
    {{{
      array۰model t dq vs ∗
      ( ⌜0 ≤ i < length vs⌝%Z -∗
        ⌜vs !! ₊i = Some v⌝
      )
    }}}
      array٠get t #i
    {{{
      RET v;
      ⌜0 ≤ i < length vs⌝%Z ∗
      array۰model t dq vs
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & H) HΦ".
    wp۰rec.
    wp۰apply+ assume𑁒spec' as "%Hi1".
    wp۰apply+ (array٠size𑁒spec with "Hmodel") as "Hmodel".
    wp۰apply+ assume𑁒spec' as "%Hi2".
    iDestruct ("H" with "[//]") as "%Hlookup".
    wp۰apply+ (array٠unsafe_get𑁒spec with "Hmodel"); [done.. |].
    iSteps.
  Qed.

  Lemma array٠unsafe_set𑁒spec𑁒atomic𑁒slice t (j : Z) v :
    <<<
      True
    | ∀∀ vs i,
      ⌜i ≤ j < i + length vs⌝%Z ∗
      array۰slice t i (DfracOwn 1) vs
    >>>
      array٠unsafe_set t #j v
    <<<
      ∃∃ w,
      ⌜vs !! (₊j - i) = Some w⌝ ∗
      array۰slice t i (DfracOwn 1) (<[₊j - i := v]> vs)
    | RET ();
      £ 1
    >>>.
  Proof.
    rewrite /array۰model /array۰slice.
    iIntros "%Φ _ HΦ".
    wp۰rec credit:"H£". wp۰pures.
    iMod "HΦ" as "(%vs & %i & (%Hj & (%l & -> & Hmodel)) & _ & HΦ)".
    destruct (lookup_lt_is_Some_2 vs (₊j - i)) as (w & Hlookup); first lia.
    iDestruct (chunk۰model𑁒update' j with "Hmodel") as "(H↦ & Hmodel)"; [lia | | done |].
    { rewrite Nat2Z.id //. }
    wp۰store.
    iApply ("HΦ" with "[H↦ Hmodel] H£").
    rewrite Nat2Z.id. iSteps.
  Qed.
  Lemma array٠unsafe_set𑁒spec𑁒atomic𑁒cell t (i : Z) v :
    <<<
      True
    | ∀∀ i_ w,
      ⌜i = ⁺i_⌝ ∗
      array۰slice t i_ (DfracOwn 1) [w]
    >>>
      array٠unsafe_set t #i v
    <<<
      array۰slice t i_ (DfracOwn 1) [v]
    | RET ();
      £ 1
    >>>.
  Proof.
    iIntros "%Φ _ HΦ".
    awp۰apply (array٠unsafe_set𑁒spec𑁒atomic𑁒slice with "[//]").
    iApply (aacc𑁒aupd𑁒commit with "HΦ"); first done. iIntros "%i_ %w (-> & Hslice)".
    iAaccIntro with "[$Hslice]". 1,2: iSteps.
    rewrite Nat2Z.id Nat.sub_diag. iSteps.
  Qed.
  Lemma array٠unsafe_set𑁒spec𑁒atomic t (i : Z) v :
    (0 ≤ i)%Z →
    <<<
      True
    | ∀∀ vs,
      ⌜i < length vs⌝%Z ∗
      array۰model t (DfracOwn 1) vs
    >>>
      array٠unsafe_set t #i v
    <<<
      ∃∃ w,
      ⌜vs !! ₊i = Some w⌝ ∗
      array۰model t (DfracOwn 1) (<[₊i := v]> vs)
    | RET ();
      £ 1
    >>>.
  Proof.
    iIntros "%Hi %Φ _ HΦ".
    awp۰apply (array٠unsafe_set𑁒spec𑁒atomic𑁒slice with "[//]").
    iApply (aacc𑁒aupd𑁒commit with "HΦ"); first done. iIntros "%vs (%Hlookup & Hmodel)".
    iDestruct (array۰model𑁒to𑁒slice' with "Hmodel") as "(Hslice & #?)".
    iAaccIntro with "[$Hslice]". 1,2: iSteps.
    rewrite Nat.sub_0_r. iSteps. simpl_length.
  Qed.
  Lemma array٠unsafe_set𑁒spec𑁒atomic𑁒inv t (sz : nat) (i : Z) v :
    (0 ≤ i < sz)%Z →
    <<<
      array۰inv t sz
    | ∀∀ vs,
      array۰model t (DfracOwn 1) vs
    >>>
      array٠unsafe_set t #i v
    <<<
      ∃∃ w,
      ⌜vs !! ₊i = Some w⌝ ∗
      array۰model t (DfracOwn 1) (<[₊i := v]> vs)
    | RET ();
      £ 1
    >>>.
  Proof.
    iIntros "%Hi %Φ #Hinv HΦ".

    awp۰apply (array٠unsafe_set𑁒spec𑁒atomic with "[//]"); first lia.
    iApply (aacc𑁒aupd𑁒commit with "HΦ"); first done. iIntros "%vs Hmodel".
    iDestruct (array𑁒inv𑁒model𑁒agree with "Hinv Hmodel") as %?.
    iAaccIntro with "[$Hmodel]"; iSteps.
  Qed.
  Lemma array٠unsafe_set𑁒spec𑁒slice t i vs (j : Z) v :
    (i ≤ j < i + length vs)%Z →
    {{{
      array۰slice t i (DfracOwn 1) vs
    }}}
      array٠unsafe_set t #j v
    {{{
      RET ();
      array۰slice t i (DfracOwn 1) (<[₊j - i := v]> vs)
    }}}.
  Proof.
    iIntros "%Hj %Φ Hslice HΦ".
    iApply wp𑁒fupd.
    awp۰apply (array٠unsafe_set𑁒spec𑁒atomic𑁒slice with "[//]") without "HΦ".
    iAaccIntro with "[$Hslice]". 1,2: iSteps. iIntros "%w (_ & Hslice) !> H£ HΦ".
    iApply (lc_fupd_elim_later with "H£ HΦ Hslice").
  Qed.
  Lemma array٠unsafe_set𑁒spec𑁒cell t (i : Z) i_ w v :
    i = ⁺i_ →
    {{{
      array۰slice t i_ (DfracOwn 1) [w]
    }}}
      array٠unsafe_set t #i v
    {{{
      RET ();
      array۰slice t i_ (DfracOwn 1) [v]
    }}}.
  Proof.
    iIntros (->) "%Φ Hslice HΦ".
    wp۰apply (array٠unsafe_set𑁒spec𑁒slice with "Hslice").
    { simpl. lia. }
    rewrite Nat2Z.id Nat.sub_diag //.
  Qed.
  Lemma array٠unsafe_set𑁒spec t (i : Z) vs v :
    (0 ≤ i < length vs)%Z →
    {{{
      array۰model t (DfracOwn 1) vs
    }}}
      array٠unsafe_set t #i v
    {{{
      RET ();
      array۰model t (DfracOwn 1) (<[₊i := v]> vs)
    }}}.
  Proof.
    setoid_rewrite array۰model𑁒to𑁒slice' at 1.
    iIntros "%Hi %Φ (Hslice & #?) HΦ".
    wp۰apply (array٠unsafe_set𑁒spec𑁒slice with "Hslice"); [done.. | lia |].
    iSteps.
    - simpl_length.
    - rewrite Nat.sub_0_r //.
  Qed.

  Lemma array٠set𑁒spec𑁒atomic𑁒slice t sz (j : Z) v :
    <<<
      array۰inv t sz
    | ∀∀ vs i,
      ⌜0 ≤ j < sz⌝%Z -∗
        ⌜i ≤ ₊j < i + length vs⌝ ∗
        array۰slice t i (DfracOwn 1) vs
    >>>
      array٠set t #j v
    <<<
      array۰slice t i (DfracOwn 1) (<[₊j - i := v]> vs)
    | RET ();
      ⌜0 ≤ j < sz⌝%Z ∗
      £ 1
    >>>.
  Proof.
    iIntros "%Φ #Hinv HΦ".
    wp۰rec.
    wp۰apply+ assume𑁒spec' as "%Hj1".
    wp۰apply+ (array٠size𑁒spec𑁒inv with "Hinv") as "_".
    wp۰apply+ assume𑁒spec' as "%Hj2".
    awp۰apply+ (array٠unsafe_set𑁒spec𑁒atomic𑁒slice with "[//]").
    iApply (aacc𑁒aupd𑁒commit with "HΦ"); first done. iIntros "%vs %i H".
    iDestruct ("H" with "[//]") as "(%Hj3 & Hslice)".
    iAaccIntro with "[$Hslice]". 1,3: iSteps.
    iIntros "(_ & $)". iSteps.
  Qed.
  Lemma array٠set𑁒spec𑁒atomic𑁒cell t sz (i : Z) i_ v :
    i_ = ₊i →
    <<<
      array۰inv t sz
    | ∀∀ w,
      ⌜0 ≤ i < sz⌝%Z -∗
      array۰slice t i_ (DfracOwn 1) [w]
    >>>
      array٠set t #i v
    <<<
      array۰slice t i_ (DfracOwn 1) [v]
    | RET ();
      ⌜0 ≤ i < sz⌝%Z ∗
      £ 1
    >>>.
  Proof.
    iIntros (->) "%Φ #Hinv HΦ".
    awp۰apply (array٠set𑁒spec𑁒atomic𑁒slice with "Hinv").
    iApply (aacc𑁒aupd𑁒commit with "HΦ"); first done. iIntros "%w Hslice".
    iAaccIntro [w], ₊i with "[Hslice]".
    { iSteps. }
    { iIntros "Hslice !>". iSplitL; iSteps. }
    rewrite Nat.sub_diag. iSteps.
  Qed.
  Lemma array٠set𑁒spec𑁒atomic t sz (i : Z) v :
    <<<
      array۰inv t sz
    | ∀∀ vs,
      ⌜0 ≤ i < sz⌝%Z -∗
        ⌜(₊i < length vs)%Z⌝ ∗
        array۰model t (DfracOwn 1) vs
    >>>
      array٠set t #i v
    <<<
      array۰model t (DfracOwn 1) (<[₊i := v]> vs)
    | RET ();
      ⌜0 ≤ i < sz⌝%Z ∗
      £ 1
    >>>.
  Proof.
    iIntros "%Φ #Hinv HΦ".
    wp۰rec.
    wp۰apply+ assume𑁒spec' as "%Hi1".
    wp۰apply+ (array٠size𑁒spec𑁒inv with "Hinv") as "_".
    wp۰apply+ assume𑁒spec' as "%Hi2".
    awp۰apply+ (array٠unsafe_set𑁒spec𑁒atomic with "[//]"); first done.
    iApply (aacc𑁒aupd𑁒commit with "HΦ"); first done. iIntros "%vs H".
    iDestruct ("H" with "[//]") as "(%Hi3 & Hmodel)".
    iAaccIntro with "[$Hmodel]". 1,3: iSteps.
    iIntros "(_ & $)". iSteps.
  Qed.
  Lemma array٠set𑁒spec𑁒slice t sz i vs (j : Z) v :
    {{{
      array۰inv t sz ∗
      ( ⌜0 ≤ j < sz⌝%Z -∗
          ⌜i ≤ ₊j < i + length vs⌝ ∗
          array۰slice t i (DfracOwn 1) vs
      )
    }}}
      array٠set t #j v
    {{{
      RET ();
      ⌜0 ≤ j < sz⌝%Z ∗
      array۰slice t i (DfracOwn 1) (<[₊j - i := v]> vs)
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & H) HΦ".
    wp۰rec.
    wp۰apply+ assume𑁒spec' as "%Hj1".
    wp۰apply+ (array٠size𑁒spec𑁒inv with "Hinv") as "_".
    wp۰apply+ assume𑁒spec' as "%Hj2".
    iDestruct ("H" with "[//]") as "(%Hi3 & Hslice)".
    wp۰apply+ (array٠unsafe_set𑁒spec𑁒slice with "Hslice"); first lia.
    iSteps.
  Qed.
  Lemma array٠set𑁒spec𑁒cell t sz (i : Z) i_ w v :
    i_ = ₊i →
    {{{
      array۰inv t sz ∗
      ( ⌜0 ≤ i < sz⌝%Z -∗
        array۰slice t i_ (DfracOwn 1) [w]
      )
    }}}
      array٠set t #i v
    {{{
      RET ();
      ⌜0 ≤ i < sz⌝%Z ∗
      array۰slice t i_ (DfracOwn 1) [v]
    }}}.
  Proof.
    iIntros (->) "%Φ (#Hinv & H) HΦ".
    wp۰apply (array٠set𑁒spec𑁒slice _ _ ₊i [_] with "[$Hinv H]"); first iSteps.
    rewrite Nat.sub_diag //.
  Qed.
  Lemma array٠set𑁒spec t (i : Z) vs v :
    {{{
      array۰model t (DfracOwn 1) vs
    }}}
      array٠set t #i v
    {{{
      RET ();
      array۰model t (DfracOwn 1) (<[₊i := v]> vs)
    }}}.
  Proof.
    iIntros "%Φ Hmodel HΦ".
    wp۰rec.
    wp۰apply+ assume𑁒spec' as "%Hi1".
    wp۰apply+ (array٠size𑁒spec with "Hmodel") as "Hmodel".
    wp۰apply+ assume𑁒spec' as "%Hi2".
    wp۰apply+ (array٠unsafe_set𑁒spec with "Hmodel HΦ"); first done.
  Qed.

  Lemma array٠unsafe_xchg𑁒spec𑁒atomic𑁒slice t (j : Z) v :
    <<<
      True
    | ∀∀ vs i,
      ⌜i ≤ j < i + length vs⌝%Z ∗
      array۰slice t i (DfracOwn 1) vs
    >>>
      array٠unsafe_xchg t #j v
    <<<
      ∃∃ w,
      ⌜vs !! (₊j - i) = Some w⌝ ∗
      array۰slice t i (DfracOwn 1) (<[₊j - i := v]> vs)
    | RET w;
      £ 1
    >>>.
  Proof.
    rewrite /array۰model /array۰slice.
    iIntros "%Φ _ HΦ".
    wp۰rec credit:"H£". wp۰pures.
    iMod "HΦ" as "(%vs & %i & (%Hj & (%l & -> & Hmodel)) & _ & HΦ)".
    destruct (lookup_lt_is_Some_2 vs (₊j - i)) as (w & Hlookup); first lia.
    iDestruct (chunk۰model𑁒update' j with "Hmodel") as "(H↦ & Hmodel)"; [lia | | done |].
    { rewrite Nat2Z.id //. }
    wp۰xchg.
    iApply ("HΦ" with "[H↦ Hmodel] H£").
    rewrite Nat2Z.id. iSteps.
  Qed.
  Lemma array٠unsafe_xchg𑁒spec𑁒atomic𑁒cell t (i : Z) v :
    <<<
      True
    | ∀∀ i_ w,
      ⌜i = ⁺i_⌝ ∗
      array۰slice t i_ (DfracOwn 1) [w]
    >>>
      array٠unsafe_xchg t #i v
    <<<
      array۰slice t i_ (DfracOwn 1) [v]
    | RET w;
      £ 1
    >>>.
  Proof.
    iIntros "%Φ _ HΦ".
    awp۰apply (array٠unsafe_xchg𑁒spec𑁒atomic𑁒slice with "[//]").
    iApply (aacc𑁒aupd𑁒commit with "HΦ"); first done. iIntros "%i_ %w (-> & Hslice)".
    iAaccIntro with "[$Hslice]". 1,2: iSteps.
    rewrite Nat2Z.id Nat.sub_diag. iSteps.
  Qed.
  Lemma array٠unsafe_xchg𑁒spec𑁒atomic t (i : Z) v :
    (0 ≤ i)%Z →
    <<<
      True
    | ∀∀ vs,
      ⌜i < length vs⌝%Z ∗
      array۰model t (DfracOwn 1) vs
    >>>
      array٠unsafe_xchg t #i v
    <<<
      ∃∃ w,
      ⌜vs !! ₊i = Some w⌝ ∗
      array۰model t (DfracOwn 1) (<[₊i := v]> vs)
    | RET w;
      £ 1
    >>>.
  Proof.
    iIntros "%Hi %Φ _ HΦ".
    awp۰apply (array٠unsafe_xchg𑁒spec𑁒atomic𑁒slice with "[//]").
    iApply (aacc𑁒aupd𑁒commit with "HΦ"); first done. iIntros "%vs (%Hlookup & Hmodel)".
    iDestruct (array۰model𑁒to𑁒slice' with "Hmodel") as "(Hslice & #?)".
    iAaccIntro with "[$Hslice]". 1,2: iSteps.
    rewrite Nat.sub_0_r. iSteps. simpl_length.
  Qed.
  Lemma array٠unsafe_xchg𑁒spec𑁒atomic𑁒inv t (sz : nat) (i : Z) v :
    (0 ≤ i < sz)%Z →
    <<<
      array۰inv t sz
    | ∀∀ vs,
      array۰model t (DfracOwn 1) vs
    >>>
      array٠unsafe_xchg t #i v
    <<<
      ∃∃ w,
      ⌜vs !! ₊i = Some w⌝ ∗
      array۰model t (DfracOwn 1) (<[₊i := v]> vs)
    | RET w;
      £ 1
    >>>.
  Proof.
    iIntros "%Hi %Φ #Hinv HΦ".

    awp۰apply (array٠unsafe_xchg𑁒spec𑁒atomic with "[//]"); first lia.
    iApply (aacc𑁒aupd𑁒commit with "HΦ"); first done. iIntros "%vs Hmodel".
    iDestruct (array𑁒inv𑁒model𑁒agree with "Hinv Hmodel") as %?.
    iAaccIntro with "[$Hmodel]"; iSteps.
  Qed.
  Lemma array٠unsafe_xchg𑁒spec𑁒slice t i vs (j : Z) v :
    (i ≤ j < i + length vs)%Z →
    {{{
      array۰slice t i (DfracOwn 1) vs
    }}}
      array٠unsafe_xchg t #j v
    {{{
      w
    , RET w;
      ⌜vs !! (₊j - i) = Some w⌝ ∗
      array۰slice t i (DfracOwn 1) (<[₊j - i := v]> vs)
    }}}.
  Proof.
    iIntros "%Hj %Φ Hslice HΦ".
    iApply wp𑁒fupd.
    awp۰apply (array٠unsafe_xchg𑁒spec𑁒atomic𑁒slice with "[//]") without "HΦ".
    iAaccIntro with "[$Hslice]". 1,2: iSteps. iIntros "%w (%Hlookup & Hslice) !> H£ HΦ".
    iApply (lc_fupd_elim_later with "H£ HΦ [$Hslice //]").
  Qed.
  Lemma array٠unsafe_xchg𑁒spec𑁒cell t (i : Z) i_ w v :
    i = ⁺i_ →
    {{{
      array۰slice t i_ (DfracOwn 1) [w]
    }}}
      array٠unsafe_xchg t #i v
    {{{
      RET w;
      array۰slice t i_ (DfracOwn 1) [v]
    }}}.
  Proof.
    iIntros (->) "%Φ Hslice HΦ".
    wp۰apply (array٠unsafe_xchg𑁒spec𑁒slice with "Hslice").
    { simpl. lia. }
    rewrite Nat2Z.id Nat.sub_diag. iSteps.
  Qed.
  Lemma array٠unsafe_xchg𑁒spec t (i : Z) vs v :
    (0 ≤ i < length vs)%Z →
    {{{
      array۰model t (DfracOwn 1) vs
    }}}
      array٠unsafe_xchg t #i v
    {{{
      w
    , RET w;
      ⌜vs !! ₊i = Some w⌝ ∗
      array۰model t (DfracOwn 1) (<[₊i := v]> vs)
    }}}.
  Proof.
    setoid_rewrite array۰model𑁒to𑁒slice' at 1.
    iIntros "%Hi %Φ (Hslice & #?) HΦ".
    wp۰apply (array٠unsafe_xchg𑁒spec𑁒slice with "Hslice") as (w) "(%Hlookup & Hslice)"; [done.. | lia |].
    rewrite Nat.sub_0_r in Hlookup |- *. iSteps.
    simpl_length.
  Qed.

  Lemma array٠unsafe_cas𑁒spec𑁒atomic𑁒slice t (j : Z) v1 v2 :
    <<<
      True
    | ∀∀ vs i,
      ⌜i ≤ j < i + length vs⌝%Z ∗
      array۰slice t i (DfracOwn 1) vs
    >>>
      array٠unsafe_cas t #j v1 v2
    <<<
      ∃∃ b v,
      ⌜vs !! (₊j - i) = Some v⌝ ∗
      ⌜(if b then (≈) else (≉)) v v1⌝ ∗
      array۰slice t i (DfracOwn 1) (if b then <[₊j - i := v2]> vs else vs)
    | RET #b;
      £ 1
    >>>.
  Proof.
    rewrite /array۰model /array۰slice.
    iIntros "%Φ _ HΦ".
    wp۰rec credit:"H£". wp۰pures.
    iMod "HΦ" as "(%vs & %i & (%Hj & (%l & -> & Hmodel)) & _ & HΦ)".
    destruct (lookup_lt_is_Some_2 vs (₊j - i)) as (v & Hlookup); first lia.
    iDestruct (chunk۰model𑁒update' j with "Hmodel") as "(H↦ & Hmodel)"; [lia | | done |].
    { rewrite Nat2Z.id //. }
    wp۰cas.
    all: iApply ("HΦ" with "[H↦ Hmodel] H£").
    all: rewrite Nat2Z.id; iSteps.
    iDestruct ("Hmodel" with "H↦") as "Hmodel".
    rewrite list_insert_id //.
  Qed.
  Lemma array٠unsafe_cas𑁒spec𑁒atomic𑁒cell t (i : Z) v1 v2 :
    <<<
      True
    | ∀∀ i_ v,
      ⌜i = ⁺i_⌝ ∗
      array۰slice t i_ (DfracOwn 1) [v]
    >>>
      array٠unsafe_cas t #i v1 v2
    <<<
      ∃∃ b,
      ⌜(if b then (≈) else (≉)) v v1⌝ ∗
      array۰slice t i_ (DfracOwn 1) [if b then v2 else v]
    | RET #b;
      £ 1
    >>>.
  Proof.
    iIntros "%Φ _ HΦ".
    awp۰apply (array٠unsafe_cas𑁒spec𑁒atomic𑁒slice with "[//]").
    iApply (aacc𑁒aupd𑁒commit with "HΦ"); first done. iIntros "%i_ %v (-> & Hslice)".
    iAaccIntro with "[$Hslice]". 1,2: iSteps.
    rewrite Nat2Z.id Nat.sub_diag.
    iSteps as (v b ?) "Hslice". destruct b; iSteps.
  Qed.
  Lemma array٠unsafe_cas𑁒spec𑁒atomic t (i : Z) v1 v2 :
    (0 ≤ i)%Z →
    <<<
      True
    | ∀∀ vs,
      ⌜i < length vs⌝%Z ∗
      array۰model t (DfracOwn 1) vs
    >>>
      array٠unsafe_cas t #i v1 v2
    <<<
      ∃∃ b v,
      ⌜vs !! ₊i = Some v⌝ ∗
      ⌜(if b then (≈) else (≉)) v v1⌝ ∗
      array۰model t (DfracOwn 1) (if b then <[₊i := v2]> vs else vs)
    | RET #b;
      £ 1
    >>>.
  Proof.
    iIntros "%Hi %Φ _ HΦ".
    awp۰apply (array٠unsafe_cas𑁒spec𑁒atomic𑁒slice with "[//]").
    iApply (aacc𑁒aupd𑁒commit with "HΦ"); first done. iIntros "%vs (%Hlookup & Hmodel)".
    iDestruct (array۰model𑁒to𑁒slice' with "Hmodel") as "(Hslice & #?)".
    iAaccIntro with "[$Hslice]". 1,2: iSteps.
    rewrite Nat.sub_0_r. iSteps as (b) / --silent.
    iPureIntro. destruct b; simpl_length.
  Qed.
  Lemma array٠unsafe_cas𑁒spec𑁒atomic𑁒inv t (sz : nat) (i : Z) v1 v2 :
    (0 ≤ i < sz)%Z →
    <<<
      array۰inv t sz
    | ∀∀ vs,
      array۰model t (DfracOwn 1) vs
    >>>
      array٠unsafe_cas t #i v1 v2
    <<<
      ∃∃ b v,
      ⌜vs !! ₊i = Some v⌝ ∗
      ⌜(if b then (≈) else (≉)) v v1⌝ ∗
      array۰model t (DfracOwn 1) (if b then <[₊i := v2]> vs else vs)
    | RET #b;
      £ 1
    >>>.
  Proof.
    iIntros "%Hi %Φ #Hinv HΦ".

    awp۰apply (array٠unsafe_cas𑁒spec𑁒atomic with "[//]"); first lia.
    iApply (aacc𑁒aupd𑁒commit with "HΦ"); first done. iIntros "%vs Hmodel".
    iDestruct (array𑁒inv𑁒model𑁒agree with "Hinv Hmodel") as %?.
    iAaccIntro with "[$Hmodel]"; iSteps.
  Qed.
  Lemma array٠unsafe_cas𑁒spec𑁒slice t i vs (j : Z) v1 v2 :
    (i ≤ j < i + length vs)%Z →
    {{{
      array۰slice t i (DfracOwn 1) vs
    }}}
      array٠unsafe_cas t #j v1 v2
    {{{
      b v
    , RET #b;
      ⌜vs !! (₊j - i) = Some v⌝ ∗
      ⌜(if b then (≈) else (≉)) v v1⌝ ∗
      array۰slice t i (DfracOwn 1) (if b then <[₊j - i := v2]> vs else vs)
    }}}.
  Proof.
    iIntros "%Hj %Φ Hslice HΦ".
    iApply wp𑁒fupd.
    awp۰apply (array٠unsafe_cas𑁒spec𑁒atomic𑁒slice with "[//]") without "HΦ".
    iAaccIntro with "[$Hslice]". 1,2: iSteps. iIntros "%b %v (%Hlookup & % & Hslice) !> H£ HΦ".
    iApply (lc_fupd_elim_later with "H£ HΦ [$Hslice //]").
  Qed.
  Lemma array٠unsafe_cas𑁒spec𑁒cell t (i : Z) i_ v v1 v2 :
    i = ⁺i_ →
    {{{
      array۰slice t i_ (DfracOwn 1) [v]
    }}}
      array٠unsafe_cas t #i v1 v2
    {{{
      b
    , RET #b;
      ⌜(if b then (≈) else (≉)) v v1⌝ ∗
      array۰slice t i_ (DfracOwn 1) [if b then v2 else v]
    }}}.
  Proof.
    iIntros (->) "%Φ Hslice HΦ".
    wp۰apply (array٠unsafe_cas𑁒spec𑁒slice with "Hslice").
    { simpl. lia. }
    rewrite Nat2Z.id Nat.sub_diag. iSteps as (? b) / --silent.
    destruct b; iSteps.
  Qed.
  Lemma array٠unsafe_cas𑁒spec t (i : Z) vs v1 v2 :
    (0 ≤ i < length vs)%Z →
    {{{
      array۰model t (DfracOwn 1) vs
    }}}
      array٠unsafe_cas t #i v1 v2
    {{{
      b v
    , RET #b;
      ⌜vs !! ₊i = Some v⌝ ∗
      ⌜(if b then (≈) else (≉)) v v1⌝ ∗
      array۰model t (DfracOwn 1) (if b then <[₊i := v2]> vs else vs)
    }}}.
  Proof.
    setoid_rewrite array۰model𑁒to𑁒slice' at 1.
    iIntros "%Hi %Φ (Hslice & #?) HΦ".
    wp۰apply (array٠unsafe_cas𑁒spec𑁒slice with "Hslice") as (b v) "(%Hlookup & % & Hslice)"; [done.. | lia |].
    rewrite Nat.sub_0_r in Hlookup |- *. iSteps.
    destruct b; simpl_length.
  Qed.

  Lemma array٠unsafe_swap𑁒spec𑁒slice {t i vs} {i1 : Z} k1 {v1} {i2 : Z} k2 v2 :
    (i ≤ i1)%Z →
    (i ≤ i2)%Z →
    vs !! k1 = Some v1 →
    k1 = ₊i1 - i →
    vs !! k2 = Some v2 →
    k2 = ₊i2 - i →
    {{{
      array۰slice t i (DfracOwn 1) vs
    }}}
      array٠unsafe_swap t #i1 #i2
    {{{
      RET ();
      array۰slice t i (DfracOwn 1) (<[k2 := v1]> $ <[k1 := v2]> vs)
    }}}.
  Proof.
    iIntros "%Hi1 %Hi2 %Hlookup_1 %Hk1 %Hlookup_2 %Hk2 %Φ Hslice HΦ".

    wp۰rec.
    wp۰apply+ (array٠unsafe_get𑁒spec𑁒slice k1 with "Hslice") as "Hslice". 1-3: done.
    wp۰apply+ (array٠unsafe_get𑁒spec𑁒slice k2 with "Hslice") as "Hslice". 1-3: done.
    wp۰apply+ (array٠unsafe_set𑁒spec𑁒slice with "Hslice") as "Hslice".
    { apply lookup_lt_Some in Hlookup_1. lia. }
    wp۰apply+ (array٠unsafe_set𑁒spec𑁒slice with "Hslice") as "Hslice".
    { apply lookup_lt_Some in Hlookup_2. simpl_length. lia. }
    rewrite Hk1 Hk2. iSteps.
  Qed.
  Lemma array٠unsafe_swap𑁒spec𑁒slice𑁒id t i vs (i1 i2 : Z) :
    i1 = i2 →
    (i ≤ i1 < i + length vs)%Z →
    {{{
      array۰slice t i (DfracOwn 1) vs
    }}}
      array٠unsafe_swap t #i1 #i2
    {{{
      RET ();
      array۰slice t i (DfracOwn 1) vs
    }}}.
  Proof.
    iIntros (<- Hi1) "%Φ Hslice HΦ".

    destruct (lookup_lt_is_Some_2 vs ₊(i1 - i)) as (v & Hlookup). 1: lia.
    wp۰apply (array٠unsafe_swap𑁒spec𑁒slice with "Hslice") as "Hslice". 1-6: done || lia.
    iEval (rewrite list_insert_insert_eq list_insert_id //) in "Hslice".
    iSteps.
  Qed.
  Lemma array٠unsafe_swap𑁒spec {t vs} {i1 : Z} i1_ {v1} {i2 : Z} i2_ v2 :
    (0 ≤ i1)%Z →
    (0 ≤ i2)%Z →
    vs !! i1_ = Some v1 →
    i1_ = ₊i1 →
    vs !! i2_ = Some v2 →
    i2_ = ₊i2 →
    {{{
      array۰model t (DfracOwn 1) vs
    }}}
      array٠unsafe_swap t #i1 #i2
    {{{
      RET ();
      array۰model t (DfracOwn 1) (<[i2_ := v1]> $ <[i1_ := v2]> vs)
    }}}.
  Proof.
    iIntros "%Hi1 %Hi2 %Hlookup_1 %Hi1_ %Hlookup_2 %Hi2_ %Φ Hmodel HΦ".
    iDestruct (array۰model𑁒to𑁒slice' with "Hmodel") as "(Hslice & #?)".

    wp۰apply (array٠unsafe_swap𑁒spec𑁒slice i1_ i2_ with "Hslice"). 1-6: done || lia.
    iSteps. iPureIntro. simpl_length.
  Qed.

  Lemma array٠unsafe_fill_slice𑁒spec𑁒atomic Ψ t (i n : Z) v :
    (0 ≤ i)%Z →
    {{{
      ▷ Ψ 0 ∗
      □ (
        ∀ j,
        ⌜j < ₊n⌝ -∗
        Ψ j -∗
        au_store t (₊i + j) v (
          ▷ Ψ ˖j
        )
      )
    }}}
      array٠unsafe_fill_slice t #i #n v
    {{{
      RET ();
      Ψ ₊n
    }}}.
  Proof.
    iIntros "%Hi %Φ (HΨ & #H) HΦ".
    wp۰rec.
    pose Ψ' (_ : Z) i :=
      Ψ i.
    wp۰apply+ (for𑁒spec𑁒strong Ψ' with "[$HΨ]"); last rewrite Z.sub_0_r //.
    iIntros "!> %j_ %j -> %Hj HΨ". rewrite Z.add_0_l in Hj |- *.
    iDestruct ("H" with "[%] HΨ") as "H'"; first lia.
    awp۰apply+ (array٠unsafe_set𑁒spec𑁒atomic𑁒cell with "[//]").
    iApply (aacc𑁒aupd𑁒commit with "H'"); first done. iIntros "%w H↦".
    iAaccIntro with "[$H↦]"; iSteps.
  Qed.
  Lemma array٠unsafe_fill_slice𑁒spec𑁒slice𑁒fit t vs (i : Z) i_ (n : Z) v :
    i = ⁺i_ →
    ₊n = length vs →
    {{{
      array۰slice t i_ (DfracOwn 1) vs
    }}}
      array٠unsafe_fill_slice t #i #n v
    {{{
      RET ();
      array۰slice t i_ (DfracOwn 1) (replicate ₊n v)
    }}}.
  Proof.
    iIntros (-> Hn) "%Φ Hslice HΦ".
    pose Ψ j :=
      array۰slice t i_ (DfracOwn 1) (replicate j v ++ drop j vs).
    wp۰apply (array٠unsafe_fill_slice𑁒spec𑁒atomic Ψ with "[$Hslice]"); [lia.. | |]; last first.
    { rewrite /Ψ skipn_all2; first lia. rewrite right_id //. }
    iIntros "!> %j %Hj Hslice". rewrite Nat2Z.id.
    opose proof* (list_lookup_lookup_total_lt vs j) as Hlookup; first lia.
    iDestruct (array۰slice𑁒update j with "Hslice") as "(H↦ & Hslice)".
    { rewrite lookup_app_r length_replicate // lookup_drop Nat.sub_diag right_id //. }
    iAuIntro. iAaccIntro with "H↦"; first auto with iFrame. iIntros "H↦".
    iDestruct ("Hslice" with "H↦") as "Hslice".
    rewrite /Ψ replicate_S_end -assoc insert_app_r_alt length_replicate // Nat.sub_diag.
    erewrite drop_S => //.
  Qed.
  Lemma array٠unsafe_fill_slice𑁒spec𑁒slice t vs (i : Z) j (n : Z) v :
    (j ≤ i)%Z →
    ₊i + ₊n ≤ j + length vs →
    {{{
      array۰slice t j (DfracOwn 1) vs
    }}}
      array٠unsafe_fill_slice t #i #n v
    {{{
      RET ();
      array۰slice t j (DfracOwn 1) (with_slice (₊i - j) ₊n vs (replicate ₊n v))
    }}}.
  Proof.
    iIntros "% % %Φ Hslice HΦ".
    iEval (setoid_rewrite <- (take_drop (₊i - j) vs)) in "Hslice".
    iEval (rewrite -(drop_take_drop _ _ (₊i - j + ₊n)); first lia) in "Hslice".
    iDestruct (array۰slice𑁒app₂ with "Hslice") as "(Hslice1 & Hslice2)"; first done.
    iDestruct (array۰slice𑁒app₂ with "Hslice2") as "(Hslice2 & Hslice3)"; first done.
    simpl_length. rewrite !Nat.min_l; [lia.. |].
    wp۰apply (array٠unsafe_fill_slice𑁒spec𑁒slice𑁒fit with "Hslice2") as "Hslice2".
    { lia. }
    { simpl_length. lia. }
    iDestruct (array۰slice𑁒app₁' with "Hslice2 Hslice3") as "Hslice2".
    { simpl_length. lia. }
    iDestruct (array۰slice𑁒app₁' with "Hslice1 Hslice2") as "Hslice".
    { simpl_length. lia. }
    iSteps.
  Qed.
  Lemma array٠unsafe_fill_slice𑁒spec t vs (i : Z) (n : Z) v :
    (0 ≤ i)%Z →
    ₊i + ₊n ≤ length vs →
    {{{
      array۰model t (DfracOwn 1) vs
    }}}
      array٠unsafe_fill_slice t #i #n v
    {{{
      RET ();
      array۰model t (DfracOwn 1) (with_slice ₊i ₊n vs (replicate ₊n v))
    }}}.
  Proof.
    iIntros "% % %Φ Hmodel HΦ".
    iDestruct (array۰model𑁒to𑁒slice' with "Hmodel") as "(Hslice & Hmodel)".
    wp۰apply (array٠unsafe_fill_slice𑁒spec𑁒slice with "Hslice") as "Hslice"; [done.. |].
    iDestruct ("Hmodel" with "[%] Hslice") as "Hmodel".
    { simpl_length. lia. }
    rewrite Nat.sub_0_r. iSteps.
  Qed.

  Lemma array٠fill_slice𑁒spec t sz vs (i : Z) i_ (n : Z) v :
    i_ = ₊i →
    ₊n = length vs →
    {{{
      array۰inv t sz ∗
      array۰slice t i_ (DfracOwn 1) vs
    }}}
      array٠fill_slice t #i #n v
    {{{
      RET ();
      ⌜0 ≤ i⌝%Z ∗
      ⌜0 ≤ n⌝%Z ∗
      ⌜i + n ≤ sz⌝%Z ∗
      array۰slice t i_ (DfracOwn 1) (replicate ₊n v)
    }}}.
  Proof.
    iIntros (->) "%Hn %Φ (#Hinv & Hslice) HΦ".
    wp۰rec.
    wp۰apply+ (array٠size𑁒spec𑁒inv with "Hinv") as "_".
    repeat (wp۰apply+ assume𑁒spec' as "%").
    wp۰apply+ (array٠unsafe_fill_slice𑁒spec𑁒slice𑁒fit with "Hslice"); [lia.. |].
    iSteps.
  Qed.

  Lemma array٠fill𑁒spec t vs v :
    {{{
      array۰model t (DfracOwn 1) vs
    }}}
      array٠fill t v
    {{{
      RET ();
      array۰model t (DfracOwn 1) (replicate (length vs) v)
    }}}.
  Proof.
    iIntros "%Φ Hmodel HΦ".
    wp۰rec.
    wp۰apply+ (array٠size𑁒spec with "Hmodel") as "Hmodel".
    iDestruct (array۰model𑁒to𑁒slice' with "Hmodel") as "(Hslice & #?)".
    wp۰apply (array٠unsafe_fill_slice𑁒spec𑁒slice𑁒fit with "Hslice") as "Hslice"; [lia.. |].
    iSteps.
    - simpl_length.
    - rewrite Nat2Z.id //.
  Qed.

  Lemma array٠unsafe_make𑁒spec sz v :
    (0 ≤ sz)%Z →
    {{{
      True
    }}}
      array٠unsafe_make #sz v
    {{{
      t
    , RET t;
      array۰model t (DfracOwn 1) (replicate ₊sz v)
    }}}.
  Proof.
    iIntros "% %Φ _ HΦ".
    wp۰rec.
    wp۰apply+ (array٠unsafe_alloc𑁒spec with "[//]") as "%t Hmodel"; first done.
    wp۰apply+ (array٠fill𑁒spec with "Hmodel").
    simpl_length. iSteps.
  Qed.

  Lemma array٠make𑁒spec sz v :
    {{{
      True
    }}}
      array٠make #sz v
    {{{
      t
    , RET t;
      ⌜0 ≤ sz⌝%Z ∗
      array۰model t (DfracOwn 1) (replicate ₊sz v)
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp۰rec.
    wp۰apply+ assume𑁒spec' as "%Hsz".
    wp۰apply+ (array٠unsafe_make𑁒spec with "[//]"); first done.
    iSteps.
  Qed.

  #[local] Lemma array٠foldli_aux𑁒spec vs Ψ fn t sz i acc :
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
              ▷ Ψ ˖i (vs ++ [v]) None acc
            }}
        end
      )
    }}}
      array٠foldli_aux fn t #sz #i acc
    {{{
      vs' acc
    , RET acc;
      ⌜(length vs + length vs')%nat = sz⌝ ∗
      Ψ sz (vs ++ vs') None acc
    }}}.
  Proof.
    iIntros "%Hi1 %Hi2 %Φ (HΨ & #H) HΦ".
    remember (sz - i) as j eqn:Hj.
    iInduction j as [| j] "IH" forall (i vs acc Hi1 Hi2 Hj).
    all: wp۰rec; wp۰pures.
    - rewrite bool_decide_eq_true_2; first (repeat f_equal; lia). wp۰pures.
      iApply ("HΦ" $! []).
      rewrite !right_id. assert (sz = i) as -> by lia. iSteps.
    - rewrite bool_decide_eq_false_2; first naive_solver lia. wp۰pures.
      iDestruct ("H" with "[%] [//] HΨ") as "H'"; first lia.
      awp۰apply+ (array٠unsafe_get𑁒spec𑁒atomic𑁒cell with "[//]") without "HΦ".
      iApply (aacc𑁒aupd𑁒commit with "H'"); first done. iIntros "%dq %v H↦".
      rewrite Nat2Z.id.
      iAaccIntro with "[$H↦]". 1,2: iSteps. iIntros "$ !> HΨ !> H£ HΦ".
      iMod (lc_fupd_elim_later with "H£ HΨ") as "HΨ".
      wp۰apply+ (wp𑁒wand with "(H [%] [//] HΨ)") as "%acc' HΨ"; first lia.
      wp۰pures.
      rewrite Z.add_1_r -Nat2Z.inj_succ.
      wp۰apply ("IH" with "[%] [%] [%] HΨ [HΦ]"); simpl_length; [naive_solver lia.. |].
      iIntros "!> {% acc} %vs' %acc (<- & HΨ)".
      iApply ("HΦ" $! (v :: vs')).
      rewrite -(assoc (++)). iSteps.
  Qed.
  Lemma array٠foldli𑁒spec𑁒atomic Ψ fn acc t sz :
    {{{
      array۰inv t sz ∗
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
              ▷ Ψ ˖i (vs ++ [v]) None acc
            }}
        end
      )
    }}}
      array٠foldli fn acc t
    {{{
      vs acc
    , RET acc;
      ⌜length vs = sz⌝ ∗
      Ψ sz vs None acc
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & HΨ & #H) HΦ".
    wp۰rec.
    wp۰apply+ (array٠size𑁒spec𑁒inv with "Hinv") as "_".
    rewrite -Nat2Z.inj_0.
    wp۰apply (array٠foldli_aux𑁒spec [] Ψ with "[$HΨ] HΦ"); [lia | done |].
    iSteps.
  Qed.
  Lemma array٠foldli𑁒spec Ψ fn acc t dq vs :
    {{{
      ▷ Ψ 0 [] acc ∗
      array۰model t dq vs ∗
      □ (
        ∀ i v acc,
        ⌜vs !! i = Some v⌝ -∗
        Ψ i (take i vs) acc -∗
        WP fn #i acc v {{ acc,
          ▷ Ψ ˖i (take i vs ++ [v]) acc
        }}
      )
    }}}
      array٠foldli fn acc t
    {{{
      acc
    , RET acc;
      array۰model t dq vs ∗
      Ψ (length vs) vs acc
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hmodel & #Hfn) HΦ".
    iDestruct (array۰model𑁒to𑁒inv with "Hmodel") as "#Hinv".
    pose (Ψ' i vs_left o acc := (
      ⌜vs_left = take i vs⌝ ∗
      array۰model t dq vs ∗
      Ψ i vs_left acc ∗
      ⌜from_option (λ v, v = vs !!! i) True o⌝%I
    )%I).
    wp۰apply (array٠foldli𑁒spec𑁒atomic Ψ' with "[$Hinv $Hmodel $HΨ]"); last first.
    { iIntros "{% acc} %vs_left %acc (%Hvs_left & (-> & Hmodel & HΨ & _))".
      rewrite /Ψ' firstn_all2 //.
      iApply ("HΦ" with "[$Hmodel $HΨ]").
    }
    iStep. iIntros "!> {% acc} %i %vs_left %o %acc %Hi1 %Hi2 (-> & Hmodel & HΨ & %Ho)".
    opose proof* (list_lookup_lookup_total_lt vs i); first lia.
    destruct o as [v |].
    - rewrite Ho.
      wp۰apply (wp𑁒wand with "(Hfn [] HΨ)") as "{% acc} %acc HΨ"; first iSteps.
      iFrame.
      erewrite take_S_r => //.
    - iDestruct (array۰model𑁒lookup𑁒acc i with "Hmodel") as "(H↦ & Hmodel)"; first done.
      iAuIntro. iAaccIntro with "H↦"; iSteps.
  Qed.
  Lemma array٠foldli𑁒spec' Ψ fn acc t dq vs :
    {{{
      ▷ Ψ 0 [] acc ∗
      array۰model t dq vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        ∀ acc,
        Ψ i (take i vs) acc -∗
        WP fn #i acc v {{ acc,
          ▷ Ψ ˖i (take i vs ++ [v]) acc
        }}
      )
    }}}
      array٠foldli fn acc t
    {{{
      acc
    , RET acc;
      array۰model t dq vs ∗
      Ψ (length vs) vs acc
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hmodel & Hfn) HΦ".
    match goal with |- context [big_opL bi_sep ?Ξ' _] => set Ξ := Ξ' end.
    pose (Ψ' i vs_left acc := (
      Ψ i vs_left acc ∗
      [∗ list] j ↦ v ∈ drop i vs, Ξ (i + j) v
    )%I).
    wp۰apply (array٠foldli𑁒spec Ψ' with "[$HΨ $Hmodel $Hfn]"); last iSteps.
    iIntros "!> {% acc} %i %v %acc %Hlookup (HΨ & HΞ)".
    erewrite drop_S => //.
    iDestruct "HΞ" as "(Hfn & HΞ)".
    rewrite Nat.add_0_r. setoid_rewrite Nat.add_succ_r. iSteps.
  Qed.

  Lemma array٠foldl𑁒spec𑁒atomic Ψ fn acc t sz :
    {{{
      array۰inv t sz ∗
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
              ▷ Ψ ˖i (vs ++ [v]) None acc
            }}
        end
      )
    }}}
      array٠foldl fn acc t
    {{{
      vs acc
    , RET acc;
      ⌜length vs = sz⌝ ∗
      Ψ sz vs None acc
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & HΨ & #H) HΦ".
    wp۰rec.
    wp۰apply+ (array٠foldli𑁒spec𑁒atomic Ψ with "[$Hinv $HΨ] HΦ"). iIntros "!> {% acc} %i %vs %o %acc %Hi1 %Hi2 HΨ".
    case_match; try wp۰pures; iApply ("H" with "[%] [%] HΨ"); lia.
  Qed.
  Lemma array٠foldl𑁒spec Ψ fn acc t dq vs :
    {{{
      ▷ Ψ 0 [] acc ∗
      array۰model t dq vs ∗
      □ (
        ∀ i v acc,
        ⌜vs !! i = Some v⌝ -∗
        Ψ i (take i vs) acc -∗
        WP fn acc v {{ acc,
          ▷ Ψ ˖i (take i vs ++ [v]) acc
        }}
      )
    }}}
      array٠foldl fn acc t
    {{{
      acc
    , RET acc;
      array۰model t dq vs ∗
      Ψ (length vs) vs acc
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hmodel & #Hfn) HΦ".
    wp۰rec.
    wp۰apply+ (array٠foldli𑁒spec Ψ with "[$HΨ $Hmodel] HΦ").
    iSteps.
  Qed.
  Lemma array٠foldl𑁒spec' Ψ fn acc t dq vs :
    {{{
      ▷ Ψ 0 [] acc ∗
      array۰model t dq vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        ∀ acc,
        Ψ i (take i vs) acc -∗
        WP fn acc v {{ acc,
          ▷ Ψ ˖i (take i vs ++ [v]) acc
        }}
      )
    }}}
      array٠foldl fn acc t
    {{{
      acc
    , RET acc;
      array۰model t dq vs ∗
      Ψ (length vs) vs acc
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hmodel & Hfn) HΦ".
    wp۰rec.
    wp۰apply+ (array٠foldli𑁒spec' Ψ with "[$HΨ $Hmodel Hfn] HΦ").
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.

  #[local] Lemma array٠foldri_aux𑁒spec sz vs Ψ fn t (i : Z) acc :
    ₊i + length vs = sz →
    {{{
      ▷ Ψ ₊i acc None vs ∗
      □ (
        ∀ i acc (o : option val) vs,
        ⌜(˖i + length vs)%nat = sz⌝ -∗
        Ψ ˖i acc o vs -∗
        match o with
        | None =>
            au_load t i (λ v,
              ▷ Ψ ˖i acc (Some v) vs
            )
        | Some v =>
            WP fn #i v acc {{ acc,
              ▷ Ψ i acc None (v :: vs)
            }}
        end
      )
    }}}
      array٠foldri_aux fn t #i acc
    {{{
      acc vs'
    , RET acc;
      ⌜(length vs' + length vs)%nat = sz⌝ ∗
      Ψ 0 acc None (vs' ++ vs)
    }}}.
  Proof.
    iIntros "%Hi %Φ (HΨ & #H) HΦ".
    remember ₊i as j eqn:Hj.
    iInduction j as [| j] "IH" forall (i vs acc Hi Hj);
      wp۰rec; wp۰pures credit:"H£".
    - rewrite bool_decide_eq_true_2; first lia. wp۰pures.
      iApply ("HΦ" $! _ []).
      iSteps.
    - rewrite bool_decide_eq_false_2; first lia. wp۰pures.
      assert (i = ˖j) as -> by lia. rewrite Z.sub_1_r -Nat2Z.inj_pred /=; first lia.
      iDestruct ("H" with "[%] HΨ") as "H'"; first done.
      awp۰apply+ (array٠unsafe_get𑁒spec𑁒atomic𑁒cell with "[//]") without "HΦ".
      iApply (aacc𑁒aupd𑁒commit with "H'"); first done. iIntros "%dq %v H↦".
      rewrite Nat2Z.id.
      iAaccIntro with "[$H↦]". 1,2: iSteps. iIntros "$ !> HΨ !> _ HΦ".
      iMod (lc_fupd_elim_later with "H£ HΨ") as "HΨ".
      wp۰apply+ (wp𑁒wand with "(H [%] HΨ)") as "%acc' HΨ"; first lia.
      wp۰apply ("IH" with "[] [] HΨ [HΦ]") as "!> {% acc} %acc %vs' (<- & HΨ)"; simpl_length; [iSteps.. |].
      iApply ("HΦ" $! _ (vs' ++ [v])).
      rewrite length_app -(assoc (++)). iSteps.
  Qed.
  Lemma array٠foldri𑁒spec𑁒atomic Ψ fn t sz acc :
    {{{
      array۰inv t sz ∗
      ▷ Ψ sz acc None [] ∗
      □ (
        ∀ i acc (o : option val) vs,
        ⌜(˖i + length vs)%nat = sz⌝ -∗
        Ψ ˖i acc o vs -∗
        match o with
        | None =>
            au_load t i (λ v,
              ▷ Ψ ˖i acc (Some v) vs
            )
        | Some v =>
            WP fn #i v acc {{ acc,
              ▷ Ψ i acc None (v :: vs)
            }}
        end
      )
    }}}
      array٠foldri fn t acc
    {{{
      acc vs
    , RET acc;
      ⌜length vs = sz⌝ ∗
      Ψ 0 acc None vs
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & HΨ & #H) HΦ".
    wp۰rec.
    wp۰apply+ (array٠size𑁒spec𑁒inv with "Hinv") as "_".
    wp۰apply (array٠foldri_aux𑁒spec sz [] Ψ with "[HΨ $H]") as "{% acc} %acc %vs".
    { rewrite right_id. lia. }
    { rewrite Nat2Z.id //. }
    rewrite !right_id. iSteps.
  Qed.
  Lemma array٠foldri𑁒spec Ψ fn t dq vs acc :
    {{{
      array۰model t dq vs ∗
      ▷ Ψ (length vs) acc [] ∗
      □ (
        ∀ i v acc,
        ⌜vs !! i = Some v⌝ -∗
        Ψ ˖i acc (drop ˖i vs) -∗
        WP fn #i v acc {{ acc,
          ▷ Ψ i acc (v :: drop ˖i vs)
        }}
      )
    }}}
      array٠foldri fn t acc
    {{{
      acc
    , RET acc;
      Ψ 0 acc vs ∗
      array۰model t dq vs
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & HΨ & #Hfn) HΦ".
    iDestruct (array۰model𑁒to𑁒inv with "Hmodel") as "#Hinv".
    pose (Ψ' i acc o vs_right := (
      ⌜vs_right = drop i vs⌝ ∗
      array۰model t dq vs ∗
      Ψ i acc vs_right ∗
      ⌜from_option (λ v, v = vs !!! (i - 1)) True o⌝%I
    )%I).
    wp۰apply (array٠foldri𑁒spec𑁒atomic Ψ' with "[$Hinv $Hmodel $HΨ]"); last iSteps.
    iSplitR.
    - rewrite drop_all. iSteps.
    - iIntros "!> {% acc} %i %acc %o %vs_right %Hi (-> & Hmodel & HΨ & %Ho)".
      opose proof* (list_lookup_lookup_total_lt vs i) as Hlookup; first lia.
      destruct o as [v |].
      + rewrite Ho.
        wp۰apply (wp𑁒wand with "(Hfn [] HΨ)") as "{% acc} %acc HΨ".
        { iPureIntro. rewrite Hlookup. repeat f_equal. lia. }
        iFrame. iPureIntro. rewrite -drop_S ?Hlookup; repeat f_equal; lia.
      + iDestruct (array۰model𑁒lookup𑁒acc i with "Hmodel") as "(H↦ & Hmodel)"; first done.
        iAuIntro. iAaccIntro with "H↦"; first iSteps. iIntros "H↦ !>".
        iSteps; iPureIntro; simpl_length; f_equal; lia.
  Qed.
  Lemma array٠foldri𑁒spec' Ψ fn t dq vs acc :
    {{{
      array۰model t dq vs ∗
      ▷ Ψ (length vs) acc [] ∗
      ( [∗ list] i ↦ v ∈ vs,
        ∀ acc,
        Ψ ˖i acc (drop ˖i vs) -∗
        WP fn #i v acc {{ acc,
          ▷ Ψ i acc (v :: drop ˖i vs)
        }}
      )
    }}}
      array٠foldri fn t acc
    {{{
      acc
    , RET acc;
      Ψ 0 acc vs ∗
      array۰model t dq vs
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & HΨ & Hfn) HΦ".
    match goal with |- context [big_opL bi_sep ?Ξ' _] => set Ξ := Ξ' end.
    pose (Ψ' i acc vs_right := (
      Ψ i acc vs_right ∗
      [∗ list] j ↦ v ∈ take i vs, Ξ j v
    )%I).
    wp۰apply (array٠foldri𑁒spec Ψ' with "[$Hmodel HΨ Hfn]"); last iSteps.
    iFrame. rewrite firstn_all2; first lia. iFrame.
    iIntros "!> {% acc} %i %v %acc %Hlookup (HΨ & HΞ)".
    pose proof Hlookup as Hi%lookup_lt_Some.
    erewrite take_S_r => //.
    iDestruct "HΞ" as "(HΞ & Hfn & _)".
    rewrite Nat.add_0_r length_take Nat.min_l; first lia. iSteps.
  Qed.

  Lemma array٠foldr𑁒spec𑁒atomic Ψ fn t sz acc :
    {{{
      array۰inv t sz ∗
      ▷ Ψ sz acc None [] ∗
      □ (
        ∀ i acc (o : option val) vs,
        ⌜(˖i + length vs)%nat = sz⌝ -∗
        Ψ ˖i acc o vs -∗
        match o with
        | None =>
            au_load t i (λ v,
              ▷ Ψ ˖i acc (Some v) vs
            )
        | Some v =>
            WP fn v acc {{ acc,
              ▷ Ψ i acc None (v :: vs)
            }}
        end
      )
    }}}
      array٠foldr fn t acc
    {{{
      acc vs
    , RET acc;
      ⌜length vs = sz⌝ ∗
      Ψ 0 acc None vs
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & HΨ & #H) HΦ".
    wp۰rec.
    wp۰apply+ (array٠foldri𑁒spec𑁒atomic Ψ with "[$Hinv $HΨ] HΦ") as "!> {% acc} %i %acc %o %vs %Hi HΨ".
    case_match; try wp۰pures; iApply ("H" with "[//] HΨ").
  Qed.
  Lemma array٠foldr𑁒spec Ψ fn t dq vs acc :
    {{{
      array۰model t dq vs ∗
      ▷ Ψ (length vs) acc [] ∗
      □ (
        ∀ i v acc,
        ⌜vs !! i = Some v⌝ -∗
        Ψ ˖i acc (drop ˖i vs) -∗
        WP fn v acc {{ acc,
          ▷ Ψ i acc (v :: drop ˖i vs)
        }}
      )
    }}}
      array٠foldr fn t acc
    {{{
      acc
    , RET acc;
      Ψ 0 acc vs ∗
      array۰model t dq vs
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & HΨ & #Hfn) HΦ".
    wp۰rec.
    wp۰apply+ (array٠foldri𑁒spec Ψ with "[$Hmodel $HΨ] HΦ").
    iSteps.
  Qed.
  Lemma array٠foldr𑁒spec' Ψ fn t dq vs acc :
    {{{
      array۰model t dq vs ∗
      ▷ Ψ (length vs) acc [] ∗
      ( [∗ list] i ↦ v ∈ vs,
        ∀ acc,
        Ψ ˖i acc (drop ˖i vs) -∗
        WP fn v acc {{ acc,
          ▷ Ψ i acc (v :: drop ˖i vs)
        }}
      )
    }}}
      array٠foldr fn t acc
    {{{
      acc
    , RET acc;
      Ψ 0 acc vs ∗
      array۰model t dq vs
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & HΨ & Hfn) HΦ".
    wp۰rec.
    wp۰apply+ (array٠foldri𑁒spec' Ψ with "[$Hmodel $HΨ Hfn] HΦ").
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.

  Lemma array٠unsafe_iteri_slice𑁒spec𑁒atomic Ψ fn t (sz : nat) (i n : Z) :
    (0 ≤ i ≤ sz)%Z →
    (0 ≤ n)%Z →
    (i + n ≤ sz)%Z →
    {{{
      array۰inv t sz ∗
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
              ▷ Ψ ˖k (vs ++ [v]) None
            }}
        end
      )
    }}}
      array٠unsafe_iteri_slice fn t #i #n
    {{{
      vs
    , RET ();
      ⌜length vs = ₊n⌝ ∗
      Ψ ₊n vs None
    }}}.
  Proof.
    iIntros "% % % %Φ (#Hinv & HΨ & #H) HΦ".
    wp۰rec.
    pose Ψ' (_ : Z) k := (
      ∃ vs,
      ⌜length vs = k⌝ ∗
      Ψ k vs None
    )%I.
    wp۰apply+ (for𑁒spec𑁒strong Ψ' with "[HΨ]").
    { iSplitL. { iExists []. iSteps. }
      iIntros "!> %k_ %k -> %Hk (%vs & %Hvs & HΨ)".
      iDestruct ("H" with "[%] [//] HΨ") as "H'"; first lia.
      awp۰apply+ (array٠unsafe_get𑁒spec𑁒atomic𑁒cell with "[//]").
      iApply (aacc𑁒aupd𑁒commit with "H'"); first done. iIntros "%dq %v H↦".
      iAaccIntro with "[$H↦]". 1,2: iSteps.
      rewrite Z2Nat.inj_add; [lia.. |]. rewrite Nat2Z.id.
      iIntros "$ !> HΨ !> H£".
      iMod (lc_fupd_elim_later with "H£ HΨ") as "HΨ".
      wp۰apply+ (wp𑁒wand with "(H [%] [//] HΨ)") as "%acc' (-> & HΨ)"; first lia.
      iSteps. iExists (vs ++ [v]). simpl_length. iSteps.
    }
    rewrite right_id. iSteps.
  Qed.
  Lemma array٠unsafe_iteri_slice𑁒spec Ψ fn t dq vs (i n : Z) :
    (0 ≤ i ≤ length vs)%Z →
    (0 ≤ n)%Z →
    (i + n ≤ length vs)%Z →
    {{{
      ▷ Ψ 0 [] ∗
      array۰model t dq vs ∗
      □ (
        ∀ k v,
        ⌜k < ₊n⌝ -∗
        ⌜vs !! (₊i + k)%nat = Some v⌝ -∗
        Ψ k (slice ₊i k vs) -∗
        WP fn #k v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ ˖k (slice ₊i k vs ++ [v])
        }}
      )
    }}}
      array٠unsafe_iteri_slice fn t #i #n
    {{{
      RET ();
      array۰model t dq vs ∗
      Ψ ₊n (slice ₊i ₊n vs)
    }}}.
  Proof.
    iIntros "% % % %Φ (HΨ & Hmodel & #Hfn) HΦ".
    iDestruct (array۰model𑁒to𑁒inv with "Hmodel") as "#Hinv".
    pose (Ψ' k vs_left o := (
      ⌜vs_left = slice ₊i k vs⌝ ∗
      array۰model t dq vs ∗
      Ψ k vs_left ∗
      ⌜from_option (λ v, vs !! (₊i + k)%nat = Some v) True o⌝%I
    )%I).
    wp۰apply+ (array٠unsafe_iteri_slice𑁒spec𑁒atomic Ψ' with "[$Hinv $Hmodel $HΨ]"); [done.. | | iSteps].
    iStep. iIntros "!> %k %vs_left %o %Hk1 %Hk2 (-> & Hmodel & HΨ & %Ho)".
    destruct o as [v |].
    - wp۰apply (wp𑁒wand with "(Hfn [//] [//] HΨ)") as (res) "(-> & HΨ)".
      rewrite slice𑁒snoc //. iSteps.
    - opose proof* (list_lookup_lookup_total_lt vs (₊i + k)); first lia.
      iDestruct (array۰model𑁒lookup𑁒acc with "Hmodel") as "(H↦ & Hmodel)"; first done.
      iAuIntro. iAaccIntro with "H↦"; iSteps.
  Qed.
  Lemma array٠unsafe_iteri_slice𑁒spec' Ψ fn t dq vs (i n : Z) :
    (0 ≤ i ≤ length vs)%Z →
    (0 ≤ n)%Z →
    (i + n ≤ length vs)%Z →
    {{{
      ▷ Ψ 0 [] ∗
      array۰model t dq vs ∗
      ( [∗ list] k ↦ v ∈ slice ₊i ₊n vs,
        Ψ k (slice ₊i k vs) -∗
        WP fn #k v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ ˖k (slice ₊i k vs ++ [v])
        }}
      )
    }}}
      array٠unsafe_iteri_slice fn t #i #n
    {{{
      RET ();
      array۰model t dq vs ∗
      Ψ ₊n (slice ₊i ₊n vs)
    }}}.
  Proof.
    iIntros "% % % %Φ (HΨ & Hmodel & Hfn) HΦ".
    match goal with |- context [big_opL bi_sep ?Ξ' _] => set Ξ := Ξ' end.
    pose (Ψ' k vs_left := (
      Ψ k vs_left ∗
      [∗ list] j ↦ v ∈ slice (₊i + k) (₊n - k) vs, Ξ (k + j) v
    )%I).
    wp۰apply (array٠unsafe_iteri_slice𑁒spec Ψ' with "[$HΨ $Hmodel Hfn]"); [done.. | | iSteps].
    rewrite !right_id. iFrame.
    iIntros "!> %k %v %Hk %Hlookup (HΨ & HΞ)".
    rewrite -(slice𑁒cons' (₊i + k) _ v) //; first lia.
    iDestruct "HΞ" as "(Hfn & HΞ)".
    setoid_rewrite Nat.add_succ_r.
    rewrite Nat.add_0_r -Nat.add_succ_r -Nat.sub_add_distr Nat.add_1_r.
    iSteps.
  Qed.
  Lemma array٠unsafe_iteri_slice𑁒spec𑁒disentangled Ψ fn t dq vs (i n : Z) :
    (0 ≤ i ≤ length vs)%Z →
    (0 ≤ n)%Z →
    (i + n ≤ length vs)%Z →
    {{{
      array۰model t dq vs ∗
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
      array٠unsafe_iteri_slice fn t #i #n
    {{{
      RET ();
      array۰model t dq vs ∗
      ( [∗ list] k ↦ v ∈ slice ₊i ₊n vs,
        Ψ k v
      )
    }}}.
  Proof.
    iIntros "% % % %Φ (Hmodel & #Hfn) HΦ".
    pose (Ψ' k vs := (
      [∗ list] j ↦ v ∈ vs, Ψ j v
    )%I).
    wp۰apply (array٠unsafe_iteri_slice𑁒spec Ψ' with "[$Hmodel]"); [done.. | | iSteps].
    rewrite /Ψ'. iSteps.
    rewrite big_sepL_snoc length𑁒slice'; first lia. iSteps.
  Qed.
  Lemma array٠unsafe_iteri_slice𑁒spec𑁒disentangled' Ψ fn t dq vs (i n : Z) :
    (0 ≤ i ≤ length vs)%Z →
    (0 ≤ n)%Z →
    (i + n ≤ length vs)%Z →
    {{{
      array۰model t dq vs ∗
      ( [∗ list] k ↦ v ∈ slice ₊i ₊n vs,
        WP fn #k v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ k v
        }}
      )
    }}}
      array٠unsafe_iteri_slice fn t #i #n
    {{{
      RET ();
      array۰model t dq vs ∗
      ( [∗ list] k ↦ v ∈ slice ₊i ₊n vs,
        Ψ k v
      )
    }}}.
  Proof.
    iIntros "% % % %Φ (Hmodel & Hfn) HΦ".
    pose (Ψ' k vs := (
      [∗ list] j ↦ v ∈ vs, Ψ j v
    )%I).
    wp۰apply (array٠unsafe_iteri_slice𑁒spec' Ψ' with "[$Hmodel Hfn]"); [done.. | | iSteps].
    rewrite /Ψ'. iSteps.
    iApply (big_sepL_impl with "Hfn").
    iSteps as (k v Hk%slice𑁒lookup𑁒Some𑁒inv) / --silent.
    rewrite big_sepL_snoc length𑁒slice'; first lia. iSteps.
  Qed.

  Lemma array٠iteri_slice𑁒spec𑁒atomic Ψ fn t (sz : nat) (i n : Z) :
    {{{
      array۰inv t sz ∗
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
              ▷ Ψ ˖k (vs ++ [v]) None
            }}
        end
      )
    }}}
      array٠iteri_slice fn t #i #n
    {{{
      vs
    , RET ();
      ⌜0 ≤ i ≤ sz⌝%Z ∗
      ⌜0 ≤ n⌝%Z ∗
      ⌜i + n ≤ sz⌝%Z ∗
      ⌜length vs = ₊n⌝ ∗
      Ψ ₊n vs None
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & HΨ & H) HΦ".
    wp۰rec.
    do 2 (wp۰apply+ assume𑁒spec' as "%").
    wp۰apply+ (array٠size𑁒spec𑁒inv with "Hinv") as "_".
    do 2 (wp۰apply+ assume𑁒spec' as "%").
    wp۰apply+ (array٠unsafe_iteri_slice𑁒spec𑁒atomic Ψ with "[$Hinv $HΨ $H]"); [done.. |].
    iSteps.
  Qed.
  Lemma array٠iteri_slice𑁒spec Ψ fn t dq vs (i n : Z) :
    {{{
      ▷ Ψ 0 [] ∗
      array۰model t dq vs ∗
      □ (
        ∀ k v,
        ⌜k < ₊n⌝ -∗
        ⌜vs !! (₊i + k)%nat = Some v⌝ -∗
        Ψ k (slice ₊i k vs) -∗
        WP fn #k v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ ˖k (slice ₊i k vs ++ [v])
        }}
      )
    }}}
      array٠iteri_slice fn t #i #n
    {{{
      RET ();
      ⌜0 ≤ i ≤ length vs⌝%Z ∗
      ⌜0 ≤ n⌝%Z ∗
      ⌜i + n ≤ length vs⌝%Z ∗
      array۰model t dq vs ∗
      Ψ ₊n (slice ₊i ₊n vs)
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hmodel & #Hfn) HΦ".
    wp۰rec.
    do 2 (wp۰apply+ assume𑁒spec' as "%").
    wp۰apply+ (array٠size𑁒spec with "Hmodel") as "Hmodel".
    do 2 (wp۰apply+ assume𑁒spec' as "%").
    wp۰apply+ (array٠unsafe_iteri_slice𑁒spec Ψ with "[$HΨ $Hmodel $Hfn]"); [done.. |].
    iSteps.
  Qed.
  Lemma array٠iteri_slice𑁒spec' Ψ fn t dq vs (i n : Z) :
    {{{
      ▷ Ψ 0 [] ∗
      array۰model t dq vs ∗
      ( [∗ list] k ↦ v ∈ slice ₊i ₊n vs,
        Ψ k (slice ₊i k vs) -∗
        WP fn #k v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ ˖k (slice ₊i k vs ++ [v])
        }}
      )
    }}}
      array٠iteri_slice fn t #i #n
    {{{
      RET ();
      ⌜0 ≤ i ≤ length vs⌝%Z ∗
      ⌜0 ≤ n⌝%Z ∗
      ⌜i + n ≤ length vs⌝%Z ∗
      array۰model t dq vs ∗
      Ψ ₊n (slice ₊i ₊n vs)
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hmodel & Hfn) HΦ".
    wp۰rec.
    do 2 (wp۰apply+ assume𑁒spec' as "%").
    wp۰apply+ (array٠size𑁒spec with "Hmodel") as "Hmodel".
    do 2 (wp۰apply+ assume𑁒spec' as "%").
    wp۰apply+ (array٠unsafe_iteri_slice𑁒spec' Ψ with "[$HΨ $Hmodel Hfn]"); [done.. |].
    iSteps.
  Qed.
  Lemma array٠iteri_slice𑁒spec𑁒disentangled Ψ fn t dq vs (i n : Z) :
    {{{
      array۰model t dq vs ∗
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
      array٠iteri_slice fn t #i #n
    {{{
      RET ();
      ⌜0 ≤ i ≤ length vs⌝%Z ∗
      ⌜0 ≤ n⌝%Z ∗
      ⌜i + n ≤ length vs⌝%Z ∗
      array۰model t dq vs ∗
      ( [∗ list] k ↦ v ∈ slice ₊i ₊n vs,
        Ψ k v
      )
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & #Hfn) HΦ".
    wp۰rec.
    do 2 (wp۰apply+ assume𑁒spec' as "%").
    wp۰apply+ (array٠size𑁒spec with "Hmodel") as "Hmodel".
    do 2 (wp۰apply+ assume𑁒spec' as "%").
    wp۰apply+ (array٠unsafe_iteri_slice𑁒spec𑁒disentangled Ψ with "[$Hmodel $Hfn]"); [done.. |].
    iSteps.
  Qed.
  Lemma array٠iteri_slice𑁒spec𑁒disentangled' Ψ fn t dq vs (i n : Z) :
    {{{
      array۰model t dq vs ∗
      ( [∗ list] k ↦ v ∈ slice ₊i ₊n vs,
        WP fn #k v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ k v
        }}
      )
    }}}
      array٠iteri_slice fn t #i #n
    {{{
      RET ();
      ⌜0 ≤ i ≤ length vs⌝%Z ∗
      ⌜0 ≤ n⌝%Z ∗
      ⌜i + n ≤ length vs⌝%Z ∗
      array۰model t dq vs ∗
      ( [∗ list] k ↦ v ∈ slice ₊i ₊n vs,
        Ψ k v
      )
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & Hfn) HΦ".
    wp۰rec.
    do 2 (wp۰apply+ assume𑁒spec' as "%").
    wp۰apply+ (array٠size𑁒spec with "Hmodel") as "Hmodel".
    do 2 (wp۰apply+ assume𑁒spec' as "%").
    wp۰apply+ (array٠unsafe_iteri_slice𑁒spec𑁒disentangled' Ψ with "[$Hmodel $Hfn]"); [done.. |].
    iSteps.
  Qed.

  Lemma array٠unsafe_iter_slice𑁒spec𑁒atomic Ψ fn t (sz : nat) (i n : Z) :
    (0 ≤ i ≤ sz)%Z →
    (0 ≤ n)%Z →
    (i + n ≤ sz)%Z →
    {{{
      array۰inv t sz ∗
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
              ▷ Ψ ˖k (vs ++ [v]) None
            }}
        end
      )
    }}}
      array٠unsafe_iter_slice fn t #i #n
    {{{
      vs
    , RET ();
      ⌜length vs = ₊n⌝ ∗
      Ψ ₊n vs None
    }}}.
  Proof.
    iIntros "% % % %Φ (Hinv & HΨ & #H) HΦ".
    wp۰rec.
    wp۰apply+ (array٠unsafe_iteri_slice𑁒spec𑁒atomic Ψ with "[$Hinv $HΨ]"); [done.. | | iSteps].
    iSteps.
    select (option val) (fun o => iSpecialize ("H" $! _ _ o)).
    case_match; iSteps.
  Qed.
  Lemma array٠unsafe_iter_slice𑁒spec Ψ fn t dq vs (i n : Z) :
    (0 ≤ i ≤ length vs)%Z →
    (0 ≤ n)%Z →
    (i + n ≤ length vs)%Z →
    {{{
      ▷ Ψ 0 [] ∗
      array۰model t dq vs ∗
      □ (
        ∀ k v,
        ⌜k < ₊n⌝ -∗
        ⌜vs !! (₊i + k)%nat = Some v⌝ -∗
        Ψ k (slice ₊i k vs) -∗
        WP fn v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ ˖k (slice ₊i k vs ++ [v])
        }}
      )
    }}}
      array٠unsafe_iter_slice fn t #i #n
    {{{
      RET ();
      array۰model t dq vs ∗
      Ψ ₊n (slice ₊i ₊n vs)
    }}}.
  Proof.
    iIntros "% % % %Φ (HΨ & Hmodel & #Hfn) HΦ".
    wp۰rec.
    wp۰apply+ (array٠unsafe_iteri_slice𑁒spec Ψ with "[$HΨ $Hmodel]"); [done.. | | iSteps].
    iSteps.
  Qed.
  Lemma array٠unsafe_iter_slice𑁒spec' Ψ fn t dq vs (i n : Z) :
    (0 ≤ i ≤ length vs)%Z →
    (0 ≤ n)%Z →
    (i + n ≤ length vs)%Z →
    {{{
      ▷ Ψ 0 [] ∗
      array۰model t dq vs ∗
      ( [∗ list] k ↦ v ∈ slice ₊i ₊n vs,
        Ψ k (slice ₊i k vs) -∗
        WP fn v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ ˖k (slice ₊i k vs ++ [v])
        }}
      )
    }}}
      array٠unsafe_iter_slice fn t #i #n
    {{{
      RET ();
      array۰model t dq vs ∗
      Ψ ₊n (slice ₊i ₊n vs)
    }}}.
  Proof.
    iIntros "% % % %Φ (HΨ & Hmodel & Hfn) HΦ".
    wp۰rec.
    wp۰apply+ (array٠unsafe_iteri_slice𑁒spec' Ψ with "[$HΨ $Hmodel Hfn]"); [done.. | | iSteps].
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.
  Lemma array٠unsafe_iter_slice𑁒spec𑁒disentangled Ψ fn t dq vs (i n : Z) :
    (0 ≤ i ≤ length vs)%Z →
    (0 ≤ n)%Z →
    (i + n ≤ length vs)%Z →
    {{{
      array۰model t dq vs ∗
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
      array٠unsafe_iter_slice fn t #i #n
    {{{
      RET ();
      array۰model t dq vs ∗
      ( [∗ list] k ↦ v ∈ slice ₊i ₊n vs,
        Ψ k v
      )
    }}}.
  Proof.
    iIntros "% % % %Φ (Hmodel & #Hfn) HΦ".
    wp۰rec.
    wp۰apply+ (array٠unsafe_iteri_slice𑁒spec𑁒disentangled Ψ with "[$Hmodel]"); [done.. | | iSteps].
    iSteps.
  Qed.
  Lemma array٠unsafe_iter_slice𑁒spec𑁒disentangled' Ψ fn t dq vs (i n : Z) :
    (0 ≤ i ≤ length vs)%Z →
    (0 ≤ n)%Z →
    (i + n ≤ length vs)%Z →
    {{{
      array۰model t dq vs ∗
      ( [∗ list] k ↦ v ∈ slice ₊i ₊n vs,
        WP fn v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ k v
        }}
      )
    }}}
      array٠unsafe_iter_slice fn t #i #n
    {{{
      RET ();
      array۰model t dq vs ∗
      ( [∗ list] k ↦ v ∈ slice ₊i ₊n vs,
        Ψ k v
      )
    }}}.
  Proof.
    iIntros "% % % %Φ (Hmodel & Hfn) HΦ".
    wp۰rec.
    wp۰apply+ (array٠unsafe_iteri_slice𑁒spec𑁒disentangled' Ψ with "[$Hmodel Hfn]"); [done.. | | iSteps].
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.

  Lemma array٠iter_slice𑁒spec𑁒atomic Ψ fn t (sz : nat) (i n : Z) :
    {{{
      array۰inv t sz ∗
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
              ▷ Ψ ˖k (vs ++ [v]) None
            }}
        end
      )
    }}}
      array٠iter_slice fn t #i #n
    {{{
      vs
    , RET ();
      ⌜0 ≤ i ≤ sz⌝%Z ∗
      ⌜0 ≤ n⌝%Z ∗
      ⌜i + n ≤ sz⌝%Z ∗
      ⌜length vs = ₊n⌝ ∗
      Ψ ₊n vs None
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & HΨ & H) HΦ".
    wp۰rec.
    do 2 (wp۰apply+ assume𑁒spec' as "%").
    wp۰apply+ (array٠size𑁒spec𑁒inv with "Hinv") as "_".
    do 2 (wp۰apply+ assume𑁒spec' as "%").
    wp۰apply+ (array٠unsafe_iter_slice𑁒spec𑁒atomic Ψ with "[$Hinv $HΨ $H]"); [done.. |].
    iSteps.
  Qed.
  Lemma array٠iter_slice𑁒spec Ψ fn t dq vs (i n : Z) :
    {{{
      ▷ Ψ 0 [] ∗
      array۰model t dq vs ∗
      □ (
        ∀ k v,
        ⌜k < ₊n⌝ -∗
        ⌜vs !! (₊i + k)%nat = Some v⌝ -∗
        Ψ k (slice ₊i k vs) -∗
        WP fn v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ ˖k (slice ₊i k vs ++ [v])
        }}
      )
    }}}
      array٠iter_slice fn t #i #n
    {{{
      RET ();
      ⌜0 ≤ i ≤ length vs⌝%Z ∗
      ⌜0 ≤ n⌝%Z ∗
      ⌜i + n ≤ length vs⌝%Z ∗
      array۰model t dq vs ∗
      Ψ ₊n (slice ₊i ₊n vs)
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hmodel & #Hfn) HΦ".
    wp۰rec.
    do 2 (wp۰apply+ assume𑁒spec' as "%").
    wp۰apply+ (array٠size𑁒spec with "Hmodel") as "Hmodel".
    do 2 (wp۰apply+ assume𑁒spec' as "%").
    wp۰apply+ (array٠unsafe_iter_slice𑁒spec Ψ with "[$HΨ $Hmodel $Hfn]"); [done.. |].
    iSteps.
  Qed.
  Lemma array٠iter_slice𑁒spec' Ψ fn t dq vs (i n : Z) :
    {{{
      ▷ Ψ 0 [] ∗
      array۰model t dq vs ∗
      ( [∗ list] k ↦ v ∈ slice ₊i ₊n vs,
        Ψ k (slice ₊i k vs) -∗
        WP fn v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ ˖k (slice ₊i k vs ++ [v])
        }}
      )
    }}}
      array٠iter_slice fn t #i #n
    {{{
      RET ();
      ⌜0 ≤ i ≤ length vs⌝%Z ∗
      ⌜0 ≤ n⌝%Z ∗
      ⌜i + n ≤ length vs⌝%Z ∗
      array۰model t dq vs ∗
      Ψ ₊n (slice ₊i ₊n vs)
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hmodel & Hfn) HΦ".
    wp۰rec.
    do 2 (wp۰apply+ assume𑁒spec' as "%").
    wp۰apply+ (array٠size𑁒spec with "Hmodel") as "Hmodel".
    do 2 (wp۰apply+ assume𑁒spec' as "%").
    wp۰apply+ (array٠unsafe_iter_slice𑁒spec' Ψ with "[$HΨ $Hmodel Hfn]"); [done.. |].
    iSteps.
  Qed.
  Lemma array٠iter_slice𑁒spec𑁒disentangled Ψ fn t dq vs (i n : Z) :
    {{{
      array۰model t dq vs ∗
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
      array٠iter_slice fn t #i #n
    {{{
      RET ();
      ⌜0 ≤ i ≤ length vs⌝%Z ∗
      ⌜0 ≤ n⌝%Z ∗
      ⌜i + n ≤ length vs⌝%Z ∗
      array۰model t dq vs ∗
      ( [∗ list] k ↦ v ∈ slice ₊i ₊n vs,
        Ψ k v
      )
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & #Hfn) HΦ".
    wp۰rec.
    do 2 (wp۰apply+ assume𑁒spec' as "%").
    wp۰apply+ (array٠size𑁒spec with "Hmodel") as "Hmodel".
    do 2 (wp۰apply+ assume𑁒spec' as "%").
    wp۰apply+ (array٠unsafe_iter_slice𑁒spec𑁒disentangled Ψ with "[$Hmodel $Hfn]"); [done.. |].
    iSteps.
  Qed.
  Lemma array٠iter_slice𑁒spec𑁒disentangled' Ψ fn t dq vs (i n : Z) :
    {{{
      array۰model t dq vs ∗
      ( [∗ list] k ↦ v ∈ slice ₊i ₊n vs,
        WP fn v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ k v
        }}
      )
    }}}
      array٠iter_slice fn t #i #n
    {{{
      RET ();
      ⌜0 ≤ i ≤ length vs⌝%Z ∗
      ⌜0 ≤ n⌝%Z ∗
      ⌜i + n ≤ length vs⌝%Z ∗
      array۰model t dq vs ∗
      ( [∗ list] k ↦ v ∈ slice ₊i ₊n vs,
        Ψ k v
      )
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & Hfn) HΦ".
    wp۰rec.
    do 2 (wp۰apply+ assume𑁒spec' as "%").
    wp۰apply+ (array٠size𑁒spec with "Hmodel") as "Hmodel".
    do 2 (wp۰apply+ assume𑁒spec' as "%").
    wp۰apply+ (array٠unsafe_iter_slice𑁒spec𑁒disentangled' Ψ with "[$Hmodel $Hfn]"); [done.. |].
    iSteps.
  Qed.

  Lemma array٠iteri𑁒spec𑁒atomic Ψ fn t sz :
    {{{
      array۰inv t sz ∗
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
              ▷ Ψ ˖i (vs ++ [v]) None
            }}
        end
      )
    }}}
      array٠iteri fn t
    {{{
      vs
    , RET ();
      ⌜length vs = sz⌝ ∗
      Ψ sz vs None
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & HΨ & #H) HΦ".
    wp۰rec.
    wp۰apply+ (array٠size𑁒spec𑁒inv with "Hinv") as "_".
    wp۰apply (array٠unsafe_iteri_slice𑁒spec𑁒atomic Ψ with "[$Hinv $HΨ]"); [lia.. | iSteps |].
    rewrite Nat2Z.id. iSteps.
  Qed.
  Lemma array٠iteri𑁒spec Ψ fn t dq vs :
    {{{
      ▷ Ψ 0 [] ∗
      array۰model t dq vs ∗
      □ (
        ∀ i v,
        ⌜vs !! i = Some v⌝ -∗
        Ψ i (take i vs) -∗
        WP fn #i v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ ˖i (take i vs ++ [v])
        }}
      )
    }}}
      array٠iteri fn t
    {{{
      RET ();
      array۰model t dq vs ∗
      Ψ (length vs) vs
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hmodel & #Hfn) HΦ".
    iDestruct (array۰model𑁒to𑁒inv with "Hmodel") as "#Hinv".
    pose (Ψ' i vs_left o := (
      ⌜vs_left = take i vs⌝ ∗
      array۰model t dq vs ∗
      Ψ i vs_left ∗
      ⌜from_option (λ v, v = vs !!! i) True o⌝%I
    )%I).
    wp۰apply+ (array٠iteri𑁒spec𑁒atomic Ψ' with "[$Hinv $Hmodel $HΨ]"); last first.
    { iSteps. rewrite firstn_all //. }
    iStep. iIntros "!> %i %vs_left %o %Hi1 %Hi2 (-> & Hmodel & HΨ & %Ho)".
    opose proof* (list_lookup_lookup_total_lt vs i); first lia.
    destruct o as [v |].
    - rewrite Ho.
      wp۰apply (wp𑁒wand with "(Hfn [] HΨ)") as (res) "(-> & HΨ)"; first iSteps.
      iSteps. erewrite take_S_r => //.
    - iDestruct (array۰model𑁒lookup𑁒acc i with "Hmodel") as "(H↦ & Hmodel)"; first done.
      iAuIntro. iAaccIntro with "H↦"; iSteps.
  Qed.
  Lemma array٠iteri𑁒spec' Ψ fn t dq vs :
    {{{
      ▷ Ψ 0 [] ∗
      array۰model t dq vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i (take i vs) -∗
        WP fn #i v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ ˖i (take i vs ++ [v])
        }}
      )
    }}}
      array٠iteri fn t
    {{{
      RET ();
      array۰model t dq vs ∗
      Ψ (length vs) vs
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hmodel & Hfn) HΦ".
    match goal with |- context [big_opL bi_sep ?Ξ' _] => set Ξ := Ξ' end.
    pose (Ψ' i vs_left := (
      Ψ i vs_left ∗
      [∗ list] j ↦ v ∈ drop i vs, Ξ (i + j) v
    )%I).
    wp۰apply (array٠iteri𑁒spec Ψ' with "[$HΨ $Hmodel $Hfn]"); last iSteps.
    iIntros "!> %i %v %Hlookup (HΨ & HΞ)".
    erewrite drop_S => //.
    iDestruct "HΞ" as "(Hfn & HΞ)".
    rewrite Nat.add_0_r. setoid_rewrite Nat.add_succ_r. iSteps.
  Qed.
  Lemma array٠iteri𑁒spec𑁒disentangled Ψ fn t dq vs :
    {{{
      array۰model t dq vs ∗
      □ (
        ∀ i v,
        ⌜vs !! i = Some v⌝ -∗
        WP fn #i v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ i v
        }}
      )
    }}}
      array٠iteri fn t
    {{{
      RET ();
      array۰model t dq vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & #Hfn) HΦ".
    pose (Ψ' i vs := (
      [∗ list] j ↦ v ∈ vs, Ψ j v
    )%I).
    wp۰apply (array٠iteri𑁒spec Ψ' with "[$Hmodel]"); last iSteps.
    rewrite /Ψ'. iSteps.
    rewrite big_sepL_snoc length_take Nat.min_l; last iSteps.
    eapply Nat.lt_le_incl, lookup_lt_Some. done.
  Qed.
  Lemma array٠iteri𑁒spec𑁒disentangled' Ψ fn t dq vs :
    {{{
      array۰model t dq vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        WP fn #i v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ i v
        }}
      )
    }}}
      array٠iteri fn t
    {{{
      RET ();
      array۰model t dq vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & Hfn) HΦ".
    pose (Ψ' i vs := (
      [∗ list] j ↦ v ∈ vs, Ψ j v
    )%I).
    wp۰apply (array٠iteri𑁒spec' Ψ' with "[$Hmodel Hfn]"); last iSteps.
    rewrite /Ψ'. iSteps.
    iApply (big_sepL_impl with "Hfn"). iSteps.
    rewrite big_sepL_snoc length_take Nat.min_l; last iSteps.
    eapply Nat.lt_le_incl, lookup_lt_Some. done.
  Qed.

  Lemma array٠iter𑁒spec𑁒atomic Ψ fn t sz :
    {{{
      array۰inv t sz ∗
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
              ▷ Ψ ˖i (vs ++ [v]) None
            }}
        end
      )
    }}}
      array٠iter fn t
    {{{
      vs
    , RET ();
      ⌜length vs = sz⌝ ∗
      Ψ sz vs None
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & HΨ & #H) HΦ".
    wp۰rec.
    wp۰apply+ (array٠iteri𑁒spec𑁒atomic Ψ with "[$Hinv $HΨ] HΦ") as "!> %i %vs %o % % HΨ".
    case_match; try wp۰pures; iApply ("H" with "[//] [//] HΨ").
  Qed.
  Lemma array٠iter𑁒spec Ψ fn t dq vs :
    {{{
      ▷ Ψ 0 [] ∗
      array۰model t dq vs ∗
      □ (
        ∀ i v,
        ⌜vs !! i = Some v⌝ -∗
        Ψ i (take i vs) -∗
        WP fn v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ ˖i (take i vs ++ [v])
        }}
      )
    }}}
      array٠iter fn t
    {{{
      RET ();
      array۰model t dq vs ∗
      Ψ (length vs) vs
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hmodel & #Hfn) HΦ".
    wp۰rec.
    wp۰apply+ (array٠iteri𑁒spec Ψ with "[$HΨ $Hmodel] HΦ").
    iSteps.
  Qed.
  Lemma array٠iter𑁒spec' Ψ fn t dq vs :
    {{{
      ▷ Ψ 0 [] ∗
      array۰model t dq vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i (take i vs) -∗
        WP fn v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ ˖i (take i vs ++ [v])
        }}
      )
    }}}
      array٠iter fn t
    {{{
      RET ();
      array۰model t dq vs ∗
      Ψ (length vs) vs
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hmodel & Hfn) HΦ".
    wp۰rec.
    wp۰apply+ (array٠iteri𑁒spec' Ψ with "[$HΨ $Hmodel Hfn] HΦ").
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.
  Lemma array٠iter𑁒spec𑁒disentangled Ψ fn t dq vs :
    {{{
      array۰model t dq vs ∗
      □ (
        ∀ i v,
        ⌜vs !! i = Some v⌝ -∗
        WP fn v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ i v
        }}
      )
    }}}
      array٠iter fn t
    {{{
      RET ();
      array۰model t dq vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & #Hfn) HΦ".
    wp۰rec.
    wp۰apply+ (array٠iteri𑁒spec𑁒disentangled Ψ with "[$Hmodel] HΦ").
    iSteps.
  Qed.
  Lemma array٠iter𑁒spec𑁒disentangled' Ψ fn t dq vs :
    {{{
      array۰model t dq vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        WP fn v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ i v
        }}
      )
    }}}
      array٠iter fn t
    {{{
      RET ();
      array۰model t dq vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & Hfn) HΦ".
    wp۰rec.
    wp۰apply+ (array٠iteri𑁒spec𑁒disentangled' Ψ with "[$Hmodel Hfn] HΦ").
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.

  Lemma array٠unsafe_applyi_slice𑁒spec𑁒atomic Ψ fn t (sz : nat) (i n : Z) :
    (0 ≤ i ≤ sz)%Z →
    (0 ≤ n)%Z →
    (i + n ≤ sz)%Z →
    {{{
      array۰inv t sz ∗
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
              ▷ Ψ ˖k (vs ++ [v]) None (ws ++ [w])
            )
        end
      )
    }}}
      array٠unsafe_applyi_slice fn t #i #n
    {{{
      vs ws
    , RET ();
      ⌜length vs = ₊n⌝ ∗
      ⌜length vs = length ws⌝ ∗
      Ψ ₊n vs None ws
    }}}.
  Proof.
    iIntros "% % % %Φ (#Hinv & HΨ & #H) HΦ".

    wp۰rec credit:"H£".

    pose (Ψ' k vs o := (
      ∃ ws,
      ⌜length vs = length ws⌝ ∗
      Ψ k vs (inl <$> o) ws ∗
      £ 1
    )%I).
    wp۰apply+ (array٠unsafe_iteri_slice𑁒spec𑁒atomic Ψ' with "[$Hinv $HΨ $H£]"); [done.. | | iSteps].
    iStep. iIntros "!> %k %vs %o % % (%ws & %Hws & HΨ & H£)".
    destruct o as [v |].
    - wp۰apply+ (wp𑁒wand with "(H [//] [//] [//] HΨ)") as "%w HΨ".
      iMod (lc_fupd_elim_later with "H£ HΨ") as "HΨ".
      iDestruct ("H" with "[//] [//] [//] HΨ") as "H'".
      awp۰apply+ (array٠unsafe_set𑁒spec𑁒atomic𑁒cell with "[//]").
      iApply (aacc𑁒aupd𑁒commit with "H'"); first done. iIntros "%v' Hslice".
      iAaccIntro with "[$Hslice]". 1,2: iSteps. iIntros "$ !> HΨ !> H£".
      iFrameSteps.
      iPureIntro. simpl_length/=. lia.
    - iApply (atomic_update𑁒wand with "(H [//] [//] [//] HΨ)").
      iSteps.
  Qed.
  Lemma array٠unsafe_applyi_slice𑁒spec Ψ fn t vs (i n : Z) :
    (0 ≤ i ≤ length vs)%Z →
    (0 ≤ n)%Z →
    (i + n ≤ length vs)%Z →
    {{{
      ▷ Ψ 0 [] [] ∗
      array۰model t (DfracOwn 1) vs ∗
      □ (
        ∀ k v ws,
        ⌜k = length ws⌝ -∗
        ⌜k < ₊n⌝ -∗
        ⌜vs !! (₊i + k)%nat = Some v⌝ -∗
        Ψ k (slice ₊i k vs) ws -∗
        WP fn #k v {{ w,
          ▷ Ψ ˖k (slice ₊i k vs ++ [v]) (ws ++ [w])
        }}
      )
    }}}
      array٠unsafe_applyi_slice fn t #i #n
    {{{
      ws
    , RET ();
      ⌜length ws = ₊n⌝ ∗
      array۰model t (DfracOwn 1) (with_slice ₊i ₊n vs ws) ∗
      Ψ ₊n (slice ₊i ₊n vs) ws
    }}}.
  Proof.
    iIntros "% % % %Φ (HΨ & Hmodel & #Hfn) HΦ".
    iDestruct (array۰model𑁒to𑁒inv with "Hmodel") as "#Hinv".

    pose (Ψ' k vs_left o ws := (
      ⌜vs_left = slice ₊i k vs⌝ ∗
      array۰model t (DfracOwn 1) (with_slice ₊i k vs ws) ∗
      match o with
      | None =>
          Ψ k vs_left ws
      | Some (inl v) =>
          ⌜vs !! (₊i + k)%nat = Some v⌝ ∗
          Ψ k vs_left ws
      | Some (inr (v, w)) =>
          ⌜vs !! (₊i + k)%nat = Some v⌝ ∗
          Ψ ˖k (vs_left ++ [v]) (ws ++ [w])
      end
    )%I).
    wp۰apply (array٠unsafe_applyi_slice𑁒spec𑁒atomic Ψ' with "[$Hinv Hmodel $HΨ]"); [done.. | |].
    { rewrite with_slice𑁒slice𑁒nil //. iStep.
      iIntros "!> %k %vs_left %o %ws % % % (-> & Hmodel & HΨ)".
      destruct (lookup_lt_is_Some_2 vs (₊i + k)) as (v & Hlookup); first lia.
      destruct o as [[v_ | (v_ & w)] |].
      - iDestruct "HΨ" as "(% & HΨ)". simplify.
        wp۰apply (wp𑁒wand with "(Hfn [%] [//] [//] HΨ)"); first lia.
        iSteps.
      - iDestruct "HΨ" as "(% & HΨ)". simplify.
        iDestruct (array۰model𑁒update (₊i + k) with "Hmodel") as "(_ & H↦ & Hmodel)".
        { apply with_slice𑁒lookup𑁒right; done || lia. }
        iAuIntro. iAaccIntro with "H↦"; first iSteps. iIntros "H↦ !>". iFrame.
        iSplit. { rewrite slice𑁒snoc //. }
        iDestruct ("Hmodel" with "H↦") as "Hmodel".
        rewrite with_slice𑁒slice𑁒snoc //; lia.
      - iDestruct (array۰model𑁒lookup𑁒acc (₊i + k) with "Hmodel") as "(H↦ & Hmodel)".
        { apply with_slice𑁒lookup𑁒right; done || lia. }
        iAuIntro. iAaccIntro with "H↦"; iSteps.
    }
    iIntros "%vs_left %ws (%Hvs_left_1 & %Hws & (-> & Hmodel & HΨ))".
    iApply ("HΦ" $! ws).
    iSteps.
  Qed.
  Lemma array٠unsafe_applyi_slice𑁒spec' Ψ fn t vs (i n : Z) :
    (0 ≤ i ≤ length vs)%Z →
    (0 ≤ n)%Z →
    (i + n ≤ length vs)%Z →
    {{{
      ▷ Ψ 0 [] [] ∗
      array۰model t (DfracOwn 1) vs ∗
      ( [∗ list] k ↦ v ∈ slice ₊i ₊n vs,
        ∀ ws,
        ⌜k = length ws⌝ -∗
        Ψ k (slice ₊i k vs) ws -∗
        WP fn #k v {{ w,
          ▷ Ψ ˖k (slice ₊i k vs ++ [v]) (ws ++ [w])
        }}
      )
    }}}
      array٠unsafe_applyi_slice fn t #i #n
    {{{
      ws
    , RET ();
      ⌜length ws = ₊n⌝ ∗
      array۰model t (DfracOwn 1) (with_slice ₊i ₊n vs ws) ∗
      Ψ ₊n (slice ₊i ₊n vs) ws
    }}}.
  Proof.
    iIntros "% % % %Φ (HΨ & Hmodel & Hfn) HΦ".

    match goal with |- context [big_opL bi_sep ?Ξ' _] => set Ξ := Ξ' end.
    pose (Ψ' k vs_left ws := (
      Ψ k vs_left ws ∗
      [∗ list] j ↦ v ∈ slice (₊i + k) (₊n - k) vs, Ξ (k + j) v
    )%I).

    wp۰apply (array٠unsafe_applyi_slice𑁒spec Ψ' with "[$HΨ $Hmodel Hfn]"); [done.. | | iSteps].
    rewrite !right_id. iFrame.
    iIntros "!> %k %v %ws % % % (HΨ & HΞ)".
    rewrite -(slice𑁒cons' (₊i + k) _ v) //; first lia.
    iDestruct "HΞ" as "(Hfn & HΞ)".
    setoid_rewrite Nat.add_succ_r.
    rewrite Nat.add_0_r -Nat.add_succ_r -Nat.sub_add_distr Nat.add_1_r.
    iSteps.
  Qed.
  Lemma array٠unsafe_applyi_slice𑁒spec𑁒disentangled Ψ fn t vs (i n : Z) :
    (0 ≤ i ≤ length vs)%Z →
    (0 ≤ n)%Z →
    (i + n ≤ length vs)%Z →
    {{{
      array۰model t (DfracOwn 1) vs ∗
      □ (
        ∀ k v,
        ⌜k < ₊n⌝ -∗
        ⌜vs !! (₊i + k)%nat = Some v⌝ -∗
        WP fn #k v {{ w,
          ▷ Ψ k w
        }}
      )
    }}}
      array٠unsafe_applyi_slice fn t #i #n
    {{{
      ws
    , RET ();
      ⌜length ws = ₊n⌝ ∗
      array۰model t (DfracOwn 1) (with_slice ₊i ₊n vs ws) ∗
      ( [∗ list] i ↦ w ∈ ws,
        Ψ i w
      )
    }}}.
  Proof.
    iIntros "% % % %Φ (Hmodel & #Hfn) HΦ".

    pose (Ψ' k vs_left ws := (
      [∗ list] j ↦ w ∈ ws, Ψ j w
    )%I).
    wp۰apply (array٠unsafe_applyi_slice𑁒spec Ψ' with "[$Hmodel]"); [done.. | | iSteps].
    rewrite /Ψ'. iSteps.
    rewrite big_sepL_snoc. iSteps.
  Qed.
  Lemma array٠unsafe_applyi_slice𑁒spec𑁒disentangled' Ψ fn t vs (i n : Z) :
    (0 ≤ i ≤ length vs)%Z →
    (0 ≤ n)%Z →
    (i + n ≤ length vs)%Z →
    {{{
      array۰model t (DfracOwn 1) vs ∗
      ( [∗ list] k ↦ v ∈ slice ₊i ₊n vs,
        WP fn #k v {{ w,
          ▷ Ψ k w
        }}
      )
    }}}
      array٠unsafe_applyi_slice fn t #i #n
    {{{
      ws
    , RET ();
      array۰model t (DfracOwn 1) (with_slice ₊i ₊n vs ws) ∗
      ( [∗ list] i ↦ w ∈ ws,
        Ψ i w
      )
    }}}.
  Proof.
    iIntros "% % % %Φ (Hmodel & Hfn) HΦ".

    pose (Ψ' k vs_left ws := (
      [∗ list] j ↦ w ∈ ws, Ψ j w
    )%I).
    wp۰apply (array٠unsafe_applyi_slice𑁒spec' Ψ' with "[Hmodel Hfn]"); [done.. | | iSteps].
    rewrite /Ψ'. iSteps.
    iApply (big_sepL_impl with "Hfn"). iSteps.
    rewrite big_sepL_snoc. iSteps.
  Qed.

  Lemma array٠applyi_slice𑁒spec𑁒atomic Ψ fn t (sz : nat) (i n : Z) :
    {{{
      array۰inv t sz ∗
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
              ▷ Ψ ˖k (vs ++ [v]) None (ws ++ [w])
            )
        end
      )
    }}}
      array٠applyi_slice fn t #i #n
    {{{
      vs ws
    , RET ();
      ⌜0 ≤ i ≤ sz⌝%Z ∗
      ⌜0 ≤ n⌝%Z ∗
      ⌜i + n ≤ sz⌝%Z ∗
      ⌜length vs = ₊n⌝ ∗
      ⌜length vs = length ws⌝ ∗
      Ψ ₊n vs None ws
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & HΨ & #H) HΦ".

    wp۰rec.
    do 2 (wp۰apply+ assume𑁒spec' as "%").
    wp۰apply+ (array٠size𑁒spec𑁒inv with "Hinv") as "_".
    do 2 (wp۰apply+ assume𑁒spec' as "%").
    wp۰apply+ (array٠unsafe_applyi_slice𑁒spec𑁒atomic Ψ with "[$Hinv $HΨ $H]"); [done.. |].
    iSteps.
  Qed.
  Lemma array٠applyi_slice𑁒spec Ψ fn t vs (i n : Z) :
    {{{
      ▷ Ψ 0 [] [] ∗
      array۰model t (DfracOwn 1) vs ∗
      □ (
        ∀ k v ws,
        ⌜k = length ws⌝ -∗
        ⌜k < ₊n⌝ -∗
        ⌜vs !! (₊i + k)%nat = Some v⌝ -∗
        Ψ k (slice ₊i k vs) ws -∗
        WP fn #k v {{ w,
          ▷ Ψ ˖k (slice ₊i k vs ++ [v]) (ws ++ [w])
        }}
      )
    }}}
      array٠applyi_slice fn t #i #n
    {{{
      ws
    , RET ();
      ⌜0 ≤ i ≤ length vs⌝%Z ∗
      ⌜0 ≤ n⌝%Z ∗
      ⌜i + n ≤ length vs⌝%Z ∗
      ⌜length ws = ₊n⌝ ∗
      array۰model t (DfracOwn 1) (with_slice ₊i ₊n vs ws) ∗
      Ψ ₊n (slice ₊i ₊n vs) ws
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hmodel & #Hfn) HΦ".

    wp۰rec.
    do 2 (wp۰apply+ assume𑁒spec' as "%").
    wp۰apply+ (array٠size𑁒spec with "Hmodel") as "Hmodel".
    do 2 (wp۰apply+ assume𑁒spec' as "%").
    wp۰apply+ (array٠unsafe_applyi_slice𑁒spec Ψ with "[$HΨ $Hmodel $Hfn]"); [done.. |].
    iSteps.
  Qed.
  Lemma array٠applyi_slice𑁒spec' Ψ fn t vs (i n : Z) :
    {{{
      ▷ Ψ 0 [] [] ∗
      array۰model t (DfracOwn 1) vs ∗
      ( [∗ list] k ↦ v ∈ slice ₊i ₊n vs,
        ∀ ws,
        ⌜k = length ws⌝ -∗
        Ψ k (slice ₊i k vs) ws -∗
        WP fn #k v {{ w,
          ▷ Ψ ˖k (slice ₊i k vs ++ [v]) (ws ++ [w])
        }}
      )
    }}}
      array٠applyi_slice fn t #i #n
    {{{
      ws
    , RET ();
      ⌜0 ≤ i ≤ length vs⌝%Z ∗
      ⌜0 ≤ n⌝%Z ∗
      ⌜i + n ≤ length vs⌝%Z ∗
      ⌜length ws = ₊n⌝ ∗
      array۰model t (DfracOwn 1) (with_slice ₊i ₊n vs ws) ∗
      Ψ ₊n (slice ₊i ₊n vs) ws
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hmodel & Hfn) HΦ".

    wp۰rec.
    do 2 (wp۰apply+ assume𑁒spec' as "%").
    wp۰apply+ (array٠size𑁒spec with "Hmodel") as "Hmodel".
    do 2 (wp۰apply+ assume𑁒spec' as "%").
    wp۰apply+ (array٠unsafe_applyi_slice𑁒spec' Ψ with "[$HΨ $Hmodel Hfn]"); [done.. |].
    iSteps.
  Qed.
  Lemma array٠applyi_slice𑁒spec𑁒disentangled Ψ fn t vs (i n : Z) :
    {{{
      array۰model t (DfracOwn 1) vs ∗
      □ (
        ∀ k v,
        ⌜k < ₊n⌝ -∗
        ⌜vs !! (₊i + k)%nat = Some v⌝ -∗
        WP fn #k v {{ w,
          ▷ Ψ k w
        }}
      )
    }}}
      array٠applyi_slice fn t #i #n
    {{{
      ws
    , RET ();
      ⌜0 ≤ i ≤ length vs⌝%Z ∗
      ⌜0 ≤ n⌝%Z ∗
      ⌜i + n ≤ length vs⌝%Z ∗
      ⌜length ws = ₊n⌝ ∗
      array۰model t (DfracOwn 1) (with_slice ₊i ₊n vs ws) ∗
      ( [∗ list] i ↦ w ∈ ws,
        Ψ i w
      )
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & #Hfn) HΦ".

    wp۰rec.
    do 2 (wp۰apply+ assume𑁒spec' as "%").
    wp۰apply+ (array٠size𑁒spec with "Hmodel") as "Hmodel".
    do 2 (wp۰apply+ assume𑁒spec' as "%").
    wp۰apply+ (array٠unsafe_applyi_slice𑁒spec𑁒disentangled Ψ with "[$Hmodel $Hfn]"); [done.. |].
    iSteps.
  Qed.
  Lemma array٠applyi_slice𑁒spec𑁒disentangled' Ψ fn t vs (i n : Z) :
    {{{
      array۰model t (DfracOwn 1) vs ∗
      ( [∗ list] k ↦ v ∈ slice ₊i ₊n vs,
        WP fn #k v {{ w,
          ▷ Ψ k w
        }}
      )
    }}}
      array٠applyi_slice fn t #i #n
    {{{
      ws
    , RET ();
      ⌜0 ≤ i ≤ length vs⌝%Z ∗
      ⌜0 ≤ n⌝%Z ∗
      ⌜i + n ≤ length vs⌝%Z ∗
      array۰model t (DfracOwn 1) (with_slice ₊i ₊n vs ws) ∗
      ( [∗ list] i ↦ w ∈ ws,
        Ψ i w
      )
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & Hfn) HΦ".

    wp۰rec.
    do 2 (wp۰apply+ assume𑁒spec' as "%").
    wp۰apply+ (array٠size𑁒spec with "Hmodel") as "Hmodel".
    do 2 (wp۰apply+ assume𑁒spec' as "%").
    wp۰apply+ (array٠unsafe_applyi_slice𑁒spec𑁒disentangled' Ψ with "[$Hmodel $Hfn]"); [done.. |].
    iSteps.
  Qed.

  Lemma array٠unsafe_apply_slice𑁒spec𑁒atomic Ψ fn t (sz : nat) (i n : Z) :
    (0 ≤ i ≤ sz)%Z →
    (0 ≤ n)%Z →
    (i + n ≤ sz)%Z →
    {{{
      array۰inv t sz ∗
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
              ▷ Ψ ˖k (vs ++ [v]) None (ws ++ [w])
            )
        end
      )
    }}}
      array٠unsafe_apply_slice fn t #i #n
    {{{
      vs ws
    , RET ();
      ⌜length vs = ₊n⌝ ∗
      ⌜length vs = length ws⌝ ∗
      Ψ ₊n vs None ws
    }}}.
  Proof.
    iIntros "% % % %Φ (#Hinv & HΨ & #H) HΦ".

    wp۰rec.
    wp۰apply+ (array٠unsafe_applyi_slice𑁒spec𑁒atomic Ψ with "[$Hinv $HΨ] HΦ") as "!> %k %vs %o %ws % % % HΨ"; [done.. |].
    repeat case_match; try wp۰pures; iApply ("H" with "[//] [//] [//] HΨ").
  Qed.
  Lemma array٠unsafe_apply_slice𑁒spec Ψ fn t vs (i n : Z) :
    (0 ≤ i ≤ length vs)%Z →
    (0 ≤ n)%Z →
    (i + n ≤ length vs)%Z →
    {{{
      ▷ Ψ 0 [] [] ∗
      array۰model t (DfracOwn 1) vs ∗
      □ (
        ∀ k v ws,
        ⌜k = length ws⌝ -∗
        ⌜k < ₊n⌝ -∗
        ⌜vs !! (₊i + k)%nat = Some v⌝ -∗
        Ψ k (slice ₊i k vs) ws -∗
        WP fn v {{ w,
          ▷ Ψ ˖k (slice ₊i k vs ++ [v]) (ws ++ [w])
        }}
      )
    }}}
      array٠unsafe_apply_slice fn t #i #n
    {{{
      ws
    , RET ();
      ⌜length ws = ₊n⌝ ∗
      array۰model t (DfracOwn 1) (with_slice ₊i ₊n vs ws) ∗
      Ψ ₊n (slice ₊i ₊n vs) ws
    }}}.
  Proof.
    iIntros "% % % %Φ (HΨ & Hmodel & #Hfn) HΦ".

    wp۰rec.
    wp۰apply+ (array٠unsafe_applyi_slice𑁒spec Ψ with "[$HΨ $Hmodel] HΦ"); [done.. |].
    iSteps.
  Qed.
  Lemma array٠unsafe_apply_slice𑁒spec' Ψ fn t vs (i n : Z) :
    (0 ≤ i ≤ length vs)%Z →
    (0 ≤ n)%Z →
    (i + n ≤ length vs)%Z →
    {{{
      ▷ Ψ 0 [] [] ∗
      array۰model t (DfracOwn 1) vs ∗
      ( [∗ list] k ↦ v ∈ slice ₊i ₊n vs,
        ∀ ws,
        ⌜k = length ws⌝ -∗
        Ψ k (slice ₊i k vs) ws -∗
        WP fn v {{ w,
          ▷ Ψ ˖k (slice ₊i k vs ++ [v]) (ws ++ [w])
        }}
      )
    }}}
      array٠unsafe_apply_slice fn t #i #n
    {{{
      ws
    , RET ();
      ⌜length ws = ₊n⌝ ∗
      array۰model t (DfracOwn 1) (with_slice ₊i ₊n vs ws) ∗
      Ψ ₊n (slice ₊i ₊n vs) ws
    }}}.
  Proof.
    iIntros "% % % %Φ (HΨ & Hmodel & Hfn) HΦ".

    wp۰rec.
    wp۰apply+ (array٠unsafe_applyi_slice𑁒spec' Ψ with "[$HΨ $Hmodel Hfn] HΦ"); [done.. |].
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.
  Lemma array٠unsafe_apply_slice𑁒spec𑁒disentangled Ψ fn t vs (i n : Z) :
    (0 ≤ i ≤ length vs)%Z →
    (0 ≤ n)%Z →
    (i + n ≤ length vs)%Z →
    {{{
      array۰model t (DfracOwn 1) vs ∗
      □ (
        ∀ k v,
        ⌜k < ₊n⌝ -∗
        ⌜vs !! (₊i + k)%nat = Some v⌝ -∗
        WP fn v {{ w,
          ▷ Ψ k w
        }}
      )
    }}}
      array٠unsafe_apply_slice fn t #i #n
    {{{
      ws
    , RET ();
      ⌜length ws = ₊n⌝ ∗
      array۰model t (DfracOwn 1) (with_slice ₊i ₊n vs ws) ∗
      ( [∗ list] i ↦ w ∈ ws,
        Ψ i w
      )
    }}}.
  Proof.
    iIntros "% % % %Φ (Hmodel & #Hfn) HΦ".

    wp۰rec.
    wp۰apply+ (array٠unsafe_applyi_slice𑁒spec𑁒disentangled Ψ with "[$Hmodel] HΦ"); [done.. |].
    iSteps.
  Qed.
  Lemma array٠unsafe_apply_slice𑁒spec𑁒disentangled' Ψ fn t vs (i n : Z) :
    (0 ≤ i ≤ length vs)%Z →
    (0 ≤ n)%Z →
    (i + n ≤ length vs)%Z →
    {{{
      array۰model t (DfracOwn 1) vs ∗
      ( [∗ list] k ↦ v ∈ slice ₊i ₊n vs,
        WP fn v {{ w,
          ▷ Ψ k w
        }}
      )
    }}}
      array٠unsafe_apply_slice fn t #i #n
    {{{
      ws
    , RET ();
      array۰model t (DfracOwn 1) (with_slice ₊i ₊n vs ws) ∗
      ( [∗ list] i ↦ w ∈ ws,
        Ψ i w
      )
    }}}.
  Proof.
    iIntros "% % % %Φ (Hmodel & Hfn) HΦ".

    wp۰rec.
    wp۰apply+ (array٠unsafe_applyi_slice𑁒spec𑁒disentangled' Ψ with "[$Hmodel Hfn] HΦ"); [done.. |].
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.

  Lemma array٠apply_slice𑁒spec𑁒atomic Ψ fn t (sz : nat) (i n : Z) :
    {{{
      array۰inv t sz ∗
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
              ▷ Ψ ˖k (vs ++ [v]) None (ws ++ [w])
            )
        end
      )
    }}}
      array٠apply_slice fn t #i #n
    {{{
      vs ws
    , RET ();
      ⌜0 ≤ i ≤ sz⌝%Z ∗
      ⌜0 ≤ n⌝%Z ∗
      ⌜i + n ≤ sz⌝%Z ∗
      ⌜length vs = ₊n⌝ ∗
      ⌜length vs = length ws⌝ ∗
      Ψ ₊n vs None ws
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & HΨ & #H) HΦ".

    wp۰rec.
    do 2 (wp۰apply+ assume𑁒spec' as "%").
    wp۰apply+ (array٠size𑁒spec𑁒inv with "Hinv") as "_".
    do 2 (wp۰apply+ assume𑁒spec' as "%").
    wp۰apply+ (array٠unsafe_apply_slice𑁒spec𑁒atomic Ψ with "[$Hinv $HΨ $H]"); [done.. |].
    iSteps.
  Qed.
  Lemma array٠apply_slice𑁒spec Ψ fn t vs (i n : Z) :
    {{{
      ▷ Ψ 0 [] [] ∗
      array۰model t (DfracOwn 1) vs ∗
      □ (
        ∀ k v ws,
        ⌜k = length ws⌝ -∗
        ⌜k < ₊n⌝ -∗
        ⌜vs !! (₊i + k)%nat = Some v⌝ -∗
        Ψ k (slice ₊i k vs) ws -∗
        WP fn v {{ w,
          ▷ Ψ ˖k (slice ₊i k vs ++ [v]) (ws ++ [w])
        }}
      )
    }}}
      array٠apply_slice fn t #i #n
    {{{
      ws
    , RET ();
      ⌜0 ≤ i ≤ length vs⌝%Z ∗
      ⌜0 ≤ n⌝%Z ∗
      ⌜i + n ≤ length vs⌝%Z ∗
      ⌜length ws = ₊n⌝ ∗
      array۰model t (DfracOwn 1) (with_slice ₊i ₊n vs ws) ∗
      Ψ ₊n (slice ₊i ₊n vs) ws
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hmodel & #Hfn) HΦ".

    wp۰rec.
    do 2 (wp۰apply+ assume𑁒spec' as "%").
    wp۰apply+ (array٠size𑁒spec with "Hmodel") as "Hmodel".
    do 2 (wp۰apply+ assume𑁒spec' as "%").
    wp۰apply+ (array٠unsafe_apply_slice𑁒spec Ψ with "[$HΨ $Hmodel $Hfn]"); [done.. |].
    iSteps.
  Qed.
  Lemma array٠apply_slice𑁒spec' Ψ fn t vs (i n : Z) :
    {{{
      ▷ Ψ 0 [] [] ∗
      array۰model t (DfracOwn 1) vs ∗
      ( [∗ list] k ↦ v ∈ slice ₊i ₊n vs,
        ∀ ws,
        ⌜k = length ws⌝ -∗
        Ψ k (slice ₊i k vs) ws -∗
        WP fn v {{ w,
          ▷ Ψ ˖k (slice ₊i k vs ++ [v]) (ws ++ [w])
        }}
      )
    }}}
      array٠apply_slice fn t #i #n
    {{{
      ws
    , RET ();
      ⌜0 ≤ i ≤ length vs⌝%Z ∗
      ⌜0 ≤ n⌝%Z ∗
      ⌜i + n ≤ length vs⌝%Z ∗
      ⌜length ws = ₊n⌝ ∗
      array۰model t (DfracOwn 1) (with_slice ₊i ₊n vs ws) ∗
      Ψ ₊n (slice ₊i ₊n vs) ws
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hmodel & Hfn) HΦ".

    wp۰rec.
    do 2 (wp۰apply+ assume𑁒spec' as "%").
    wp۰apply+ (array٠size𑁒spec with "Hmodel") as "Hmodel".
    do 2 (wp۰apply+ assume𑁒spec' as "%").
    wp۰apply+ (array٠unsafe_apply_slice𑁒spec' Ψ with "[$HΨ $Hmodel Hfn]"); [done.. |].
    iSteps.
  Qed.
  Lemma array٠apply_slice𑁒spec𑁒disentangled Ψ fn t vs (i n : Z) :
    {{{
      array۰model t (DfracOwn 1) vs ∗
      □ (
        ∀ k v,
        ⌜k < ₊n⌝ -∗
        ⌜vs !! (₊i + k)%nat = Some v⌝ -∗
        WP fn v {{ w,
          ▷ Ψ k w
        }}
      )
    }}}
      array٠apply_slice fn t #i #n
    {{{
      ws
    , RET ();
      ⌜0 ≤ i ≤ length vs⌝%Z ∗
      ⌜0 ≤ n⌝%Z ∗
      ⌜i + n ≤ length vs⌝%Z ∗
      ⌜length ws = ₊n⌝ ∗
      array۰model t (DfracOwn 1) (with_slice ₊i ₊n vs ws) ∗
      ( [∗ list] i ↦ w ∈ ws,
        Ψ i w
      )
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & #Hfn) HΦ".

    wp۰rec.
    do 2 (wp۰apply+ assume𑁒spec' as "%").
    wp۰apply+ (array٠size𑁒spec with "Hmodel") as "Hmodel".
    do 2 (wp۰apply+ assume𑁒spec' as "%").
    wp۰apply+ (array٠unsafe_apply_slice𑁒spec𑁒disentangled Ψ with "[$Hmodel $Hfn]"); [done.. |].
    iSteps.
  Qed.
  Lemma array٠apply_slice𑁒spec𑁒disentangled' Ψ fn t vs (i n : Z) :
    {{{
      array۰model t (DfracOwn 1) vs ∗
      ( [∗ list] k ↦ v ∈ slice ₊i ₊n vs,
        WP fn v {{ w,
          ▷ Ψ k w
        }}
      )
    }}}
      array٠apply_slice fn t #i #n
    {{{
      ws
    , RET ();
      ⌜0 ≤ i ≤ length vs⌝%Z ∗
      ⌜0 ≤ n⌝%Z ∗
      ⌜i + n ≤ length vs⌝%Z ∗
      array۰model t (DfracOwn 1) (with_slice ₊i ₊n vs ws) ∗
      ( [∗ list] i ↦ w ∈ ws,
        Ψ i w
      )
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & Hfn) HΦ".

    wp۰rec.
    do 2 (wp۰apply+ assume𑁒spec' as "%").
    wp۰apply+ (array٠size𑁒spec with "Hmodel") as "Hmodel".
    do 2 (wp۰apply+ assume𑁒spec' as "%").
    wp۰apply+ (array٠unsafe_apply_slice𑁒spec𑁒disentangled' Ψ with "[$Hmodel $Hfn]"); [done.. |].
    iSteps.
  Qed.

  Lemma array٠applyi𑁒spec𑁒atomic Ψ fn t sz :
    {{{
      array۰inv t sz ∗
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
              ▷ Ψ ˖i (vs ++ [v]) None (ws ++ [w])
            )
        end
      )
    }}}
      array٠applyi fn t
    {{{
      vs ws
    , RET ();
      ⌜length vs = sz⌝ ∗
      ⌜length vs = length ws⌝ ∗
      Ψ sz vs None ws
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & HΨ & #H) HΦ".

    wp۰rec.
    wp۰apply+ (array٠size𑁒spec𑁒inv with "Hinv") as "_".
    wp۰apply (array٠unsafe_applyi_slice𑁒spec𑁒atomic Ψ with "[$Hinv $HΨ]"); [lia.. | iSteps |].
    rewrite Nat2Z.id. iSteps.
  Qed.
  Lemma array٠applyi𑁒spec Ψ fn t vs :
    {{{
      ▷ Ψ 0 [] [] ∗
      array۰model t (DfracOwn 1) vs ∗
      □ (
        ∀ i v ws,
        ⌜i = length ws⌝ -∗
        ⌜vs !! i = Some v⌝ -∗
        Ψ i (take i vs) ws -∗
        WP fn #i v {{ w,
          ▷ Ψ ˖i (take i vs ++ [v]) (ws ++ [w])
        }}
      )
    }}}
      array٠applyi fn t
    {{{
      ws
    , RET ();
      ⌜length vs = length ws⌝ ∗
      array۰model t (DfracOwn 1) ws ∗
      Ψ (length vs) vs ws
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hmodel & #H) HΦ".

    wp۰rec.
    wp۰apply+ (array٠size𑁒spec with "Hmodel") as "Hmodel".
    wp۰apply (array٠unsafe_applyi_slice𑁒spec Ψ with "[$HΨ $Hmodel]"); [lia.. | iSteps |].
    iStep 3 as (ws) / --silent. iExists ws.
    rewrite Nat2Z.id with_slice𑁒all // slice𑁒0 firstn_all. iSteps.
  Qed.
  Lemma array٠applyi𑁒spec' Ψ fn t vs :
    {{{
      ▷ Ψ 0 [] [] ∗
      array۰model t (DfracOwn 1) vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        ∀ ws,
        ⌜i = length ws⌝ -∗
        Ψ i (take i vs) ws -∗
        WP fn #i v {{ w,
          ▷ Ψ ˖i (take i vs ++ [v]) (ws ++ [w])
        }}
      )
    }}}
      array٠applyi fn t
    {{{
      ws
    , RET ();
      ⌜length vs = length ws⌝ ∗
      array۰model t (DfracOwn 1) ws ∗
      Ψ (length vs) vs ws
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hmodel & Hfn) HΦ".
    match goal with |- context [big_opL bi_sep ?Ξ' _] => set Ξ := Ξ' end.
    pose (Ψ' i vs_left ws := (
      Ψ i vs_left ws ∗
      [∗ list] j ↦ v ∈ drop i vs, Ξ (i + j) v
    )%I).
    wp۰apply (array٠applyi𑁒spec Ψ' with "[HΨ $Hmodel Hfn]"); last iSteps.
    iFrame. iIntros "!> %i %v %ws %Hi %Hlookup (HΨ & HΞ)".
    erewrite drop_S => //.
    iDestruct "HΞ" as "(Hfn & HΞ)".
    rewrite Nat.add_0_r. setoid_rewrite Nat.add_succ_r. iSteps.
  Qed.
  Lemma array٠applyi𑁒spec𑁒disentangled Ψ fn t vs :
    {{{
      array۰model t (DfracOwn 1) vs ∗
      □ (
        ∀ i v,
        ⌜vs !! i = Some v⌝ -∗
        WP fn #i v {{ w,
          ▷ Ψ i w
        }}
      )
    }}}
      array٠applyi fn t
    {{{
      ws
    , RET ();
      ⌜length vs = length ws⌝ ∗
      array۰model t (DfracOwn 1) ws ∗
      ( [∗ list] i ↦ w ∈ ws,
        Ψ i w
      )
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & #Hfn) HΦ".
    pose (Ψ' i vs_left ws := (
      [∗ list] j ↦ w ∈ ws, Ψ j w
    )%I).
    wp۰apply (array٠applyi𑁒spec Ψ' with "[$Hmodel]"); last iSteps.
    rewrite /Ψ'. iSteps.
    rewrite big_sepL_snoc. iSteps.
  Qed.
  Lemma array٠applyi𑁒spec𑁒disentangled' Ψ fn t vs :
    {{{
      array۰model t (DfracOwn 1) vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        WP fn #i v {{ w,
          ▷ Ψ i w
        }}
      )
    }}}
      array٠applyi fn t
    {{{
      ws
    , RET ();
      array۰model t (DfracOwn 1) ws ∗
      ( [∗ list] i ↦ w ∈ ws,
        Ψ i w
      )
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & Hfn) HΦ".
    pose (Ψ' i vs_left ws := (
      [∗ list] j ↦ w ∈ ws, Ψ j w
    )%I).
    wp۰apply (array٠applyi𑁒spec' Ψ' with "[Hmodel Hfn]"); last iSteps.
    rewrite /Ψ'. iSteps.
    iApply (big_sepL_impl with "Hfn"). iSteps.
    rewrite big_sepL_snoc. iSteps.
  Qed.

  Lemma array٠apply𑁒spec𑁒atomic Ψ fn t sz :
    {{{
      array۰inv t sz ∗
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
              ▷ Ψ ˖i (vs ++ [v]) None (ws ++ [w])
            )
        end
      )
    }}}
      array٠apply fn t
    {{{
      vs ws
    , RET ();
      ⌜length vs = sz⌝ ∗
      ⌜length vs = length ws⌝ ∗
      Ψ sz vs None ws
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & HΨ & #H) HΦ".
    wp۰rec.
    wp۰apply+ (array٠applyi𑁒spec𑁒atomic Ψ with "[$Hinv $HΨ H] HΦ") as "!> %i %vs %o %ws %Hi1 %Hi2 %Hws HΨ".
    repeat case_match; try wp۰pures; iApply ("H" with "[//] [//] [//] HΨ").
  Qed.
  Lemma array٠apply𑁒spec Ψ fn t vs :
    {{{
      ▷ Ψ 0 [] [] ∗
      array۰model t (DfracOwn 1) vs ∗
      □ (
        ∀ i v ws,
        ⌜i = length ws⌝ -∗
        ⌜vs !! i = Some v⌝ -∗
        Ψ i (take i vs) ws -∗
        WP fn v {{ w,
          ▷ Ψ ˖i (take i vs ++ [v]) (ws ++ [w])
        }}
      )
    }}}
      array٠apply fn t
    {{{
      ws
    , RET ();
      ⌜length vs = length ws⌝ ∗
      array۰model t (DfracOwn 1) ws ∗
      Ψ (length vs) vs ws
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hmodel & #Hfn) HΦ".
    wp۰rec.
    wp۰apply+ (array٠applyi𑁒spec Ψ with "[$HΨ $Hmodel] HΦ") as "!> %i %v %ws %Hi %Hlookup HΨ".
    iSteps.
  Qed.
  Lemma array٠apply𑁒spec' Ψ fn t vs :
    {{{
      ▷ Ψ 0 [] [] ∗
      array۰model t (DfracOwn 1) vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        ∀ ws,
        ⌜i = length ws⌝ -∗
        Ψ i (take i vs) ws -∗
        WP fn v {{ w,
          ▷ Ψ ˖i (take i vs ++ [v]) (ws ++ [w])
        }}
      )
    }}}
      array٠apply fn t
    {{{
      ws
    , RET ();
      ⌜length vs = length ws⌝ ∗
      array۰model t (DfracOwn 1) ws ∗
      Ψ (length vs) vs ws
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hmodel & Hfn) HΦ".
    wp۰rec.
    wp۰apply+ (array٠applyi𑁒spec' Ψ with "[$HΨ $Hmodel Hfn] HΦ").
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.
  Lemma array٠apply𑁒spec𑁒disentangled Ψ fn t vs :
    {{{
      array۰model t (DfracOwn 1) vs ∗
      □ (
        ∀ i v,
        ⌜vs !! i = Some v⌝ -∗
        WP fn v {{ w,
          ▷ Ψ i w
        }}
      )
    }}}
      array٠apply fn t
    {{{
      ws
    , RET ();
      ⌜length vs = length ws⌝ ∗
      array۰model t (DfracOwn 1) ws ∗
      ( [∗ list] i ↦ w ∈ ws,
        Ψ i w
      )
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & #Hfn) HΦ".
    wp۰rec.
    wp۰apply+ (array٠applyi𑁒spec𑁒disentangled Ψ with "[$Hmodel] HΦ").
    iSteps.
  Qed.
  Lemma array٠apply𑁒spec𑁒disentangled' Ψ fn t vs :
    {{{
      array۰model t (DfracOwn 1) vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        WP fn v {{ w,
          ▷ Ψ i w
        }}
      )
    }}}
      array٠apply fn t
    {{{
      ws
    , RET ();
      array۰model t (DfracOwn 1) ws ∗
      ( [∗ list] i ↦ w ∈ ws,
        Ψ i w
      )
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & Hfn) HΦ".
    wp۰rec.
    wp۰apply+ (array٠applyi𑁒spec𑁒disentangled' Ψ with "[$Hmodel Hfn] HΦ").
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.

  Lemma array٠unsafe_initi𑁒spec Ψ sz fn :
    (0 ≤ sz)%Z →
    {{{
      ▷ (
        ∀ t,
        |={⊤}=> Ψ t 0 []
      ) ∗
      □ (
        ∀ t i vs,
        ⌜i < ₊sz⌝ -∗
        ⌜i = length vs⌝ -∗
        Ψ t i vs -∗
        WP fn #i {{ v,
          ▷ Ψ t ˖i (vs ++ [v])
        }}
      )
    }}}
      array٠unsafe_initi #sz fn
    {{{
      t vs
    , RET t;
      ⌜length vs = ₊sz⌝ ∗
      array۰model t (DfracOwn 1) vs ∗
      Ψ t ₊sz vs
    }}}.
  Proof.
    iIntros "%Hsz %Φ (HΨ & #Hfn) HΦ".

    wp۰rec.
    wp۰apply+ (array٠unsafe_alloc𑁒spec with "[//]") as (t) "Hmodel"; first done.

    iMod ("HΨ" $! t) as "HΨ".

    pose Ψ' i (_ : list val) vs :=
      Ψ t i vs.
    wp۰apply+ (array٠applyi𑁒spec Ψ' with "[$Hmodel $HΨ]").
    { iSteps. iPureIntro.
      erewrite <- (length_replicate ₊sz). eapply lookup_lt_Some. done.
    }
    iIntros "%vs (%Hvs & Hmodel & HΨ)".

    wp۰pures.

    iApply ("HΦ" $! _ vs).
    rewrite length_replicate in Hvs |- *.
    iSteps.
  Qed.
  Lemma array٠unsafe_initi𑁒spec' Ψ sz fn :
    (0 ≤ sz)%Z →
    {{{
      ▷ (
        ∀ t,
        |={⊤}=> Ψ t 0 []
      ) ∗
      ( [∗ list] i ∈ seq 0 ₊sz,
        ∀ t vs,
        ⌜i = length vs⌝ -∗
        Ψ t i vs -∗
        WP fn #i {{ v,
          ▷ Ψ t ˖i (vs ++ [v])
        }}
      )
    }}}
      array٠unsafe_initi #sz fn
    {{{
      t vs
    , RET t;
      ⌜length vs = ₊sz⌝ ∗
      array۰model t (DfracOwn 1) vs ∗
      Ψ t ₊sz vs
    }}}.
  Proof.
    iIntros "%Hsz %Φ (HΨ & Hfn) HΦ".

    match goal with |- context [big_opL bi_sep (λ _, ?Ξ') _] => set Ξ := Ξ' end.

    pose (Ψ' t i vs := (
      Ψ t i vs ∗
      [∗ list] j ∈ seq i (₊sz - i), Ξ j
    )%I).
    wp۰apply (array٠unsafe_initi𑁒spec Ψ' with "[HΨ Hfn]"); [done | | iSteps].
    iSplitL.
    { iSteps. rewrite Nat.sub_0_r //. }
    { iIntros "!> %t %i %vs % % (HΨ & HΞ)".
      destruct (Nat.lt_exists_pred 0 (₊sz - i)) as (k & Hk & _); first lia. rewrite Hk.
      rewrite -cons_seq. iDestruct "HΞ" as "(Hfn & HΞ)".
      wp۰apply (wp𑁒wand with "(Hfn [//] HΨ)"). iSteps.
      rewrite Nat.sub_succ_r Hk //.
    }
  Qed.
  Lemma array٠unsafe_initi𑁒spec𑁒disentangled𑁒strong Χ Ψ sz fn :
    (0 ≤ sz)%Z →
    {{{
      ▷ (
        ∀ t,
        |={⊤}=> Χ t
      ) ∗
      □ (
        ∀ t i,
        Χ t -∗
        ⌜i < ₊sz⌝ -∗
        WP fn #i {{ v,
          Χ t ∗
          ▷ Ψ t i v
        }}
      )
    }}}
      array٠unsafe_initi #sz fn
    {{{
      t vs
    , RET t;
      ⌜length vs = ₊sz⌝ ∗
      array۰model t (DfracOwn 1) vs ∗
      Χ t ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ t i v
      )
    }}}.
  Proof.
    iIntros "%Hsz %Φ (HΧ & #Hfn) HΦ".

    pose (Ψ' t i vs := (
      Χ t ∗
      [∗ list] j ↦ v ∈ vs, Ψ t j v
    )%I).
    wp۰apply (array٠unsafe_initi𑁒spec Ψ' with "[- HΦ]"); [done | | iSteps].
    iSplitL "HΧ"; first iSteps.
    iSteps. rewrite big_sepL_snoc. iSteps.
  Qed.
  Lemma array٠unsafe_initi𑁒spec𑁒disentangled Ψ sz fn :
    (0 ≤ sz)%Z →
    {{{
      □ (
        ∀ i,
        ⌜i < ₊sz⌝ -∗
        WP fn #i {{ v,
          ▷ Ψ i v
        }}
      )
    }}}
      array٠unsafe_initi #sz fn
    {{{
      t vs
    , RET t;
      ⌜length vs = ₊sz⌝ ∗
      array۰model t (DfracOwn 1) vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Hsz %Φ #Hfn HΦ".

    wp۰apply (array٠unsafe_initi𑁒spec𑁒disentangled𑁒strong (λ _, True)%I (λ _, Ψ)); [done | iSteps..].
  Qed.
  Lemma array٠unsafe_initi𑁒spec𑁒disentangled𑁒strong' Χ Ψ sz fn :
    (0 ≤ sz)%Z →
    {{{
      ▷ (
        ∀ t,
        |={⊤}=> Χ t
      ) ∗
      ( [∗ list] i ∈ seq 0 ₊sz,
        ∀ t,
        Χ t -∗
        WP fn #i {{ v,
          Χ t ∗
          ▷ Ψ t i v
        }}
      )
    }}}
      array٠unsafe_initi #sz fn
    {{{
      t vs
    , RET t;
      ⌜length vs = ₊sz⌝ ∗
      array۰model t (DfracOwn 1) vs ∗
      Χ t ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ t i v
      )
    }}}.
  Proof.
    iIntros "%Hsz %Φ (HΧ & Hfn) HΦ".

    pose (Ψ' t i vs := (
      Χ t ∗
      [∗ list] j ↦ v ∈ vs, Ψ t j v
    )%I).
    wp۰apply (array٠unsafe_initi𑁒spec' Ψ' with "[- HΦ]"); [done | | iSteps].
    iSplitL "HΧ"; first iSteps.
    iApply (big_sepL_impl with "Hfn").
    iSteps. rewrite big_sepL_snoc. iSteps.
  Qed.
  Lemma array٠unsafe_initi𑁒spec𑁒disentangled' Ψ sz fn :
    (0 ≤ sz)%Z →
    {{{
      ( [∗ list] i ∈ seq 0 ₊sz,
        WP fn #i {{ v,
          ▷ Ψ i v
        }}
      )
    }}}
      array٠unsafe_initi #sz fn
    {{{
      t vs
    , RET t;
      ⌜length vs = ₊sz⌝ ∗
      array۰model t (DfracOwn 1) vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Hsz %Φ Hfn HΦ".

    wp۰apply (array٠unsafe_initi𑁒spec𑁒disentangled𑁒strong' (λ _, True)%I (λ _, Ψ) with "[- HΦ]"); [done | iSteps..].
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.

  Lemma array٠initi𑁒spec Ψ sz fn :
    {{{
      ▷ (
        ∀ t,
        |={⊤}=> Ψ t 0 []
      ) ∗
      □ (
        ∀ t i vs,
        ⌜i < ₊sz⌝ -∗
        ⌜i = length vs⌝ -∗
        Ψ t i vs -∗
        WP fn #i {{ v,
          ▷ Ψ t ˖i (vs ++ [v])
        }}
      )
    }}}
      array٠initi #sz fn
    {{{
      t vs
    , RET t;
      ⌜0 ≤ sz⌝%Z ∗
      ⌜length vs = ₊sz⌝ ∗
      array۰model t (DfracOwn 1) vs ∗
      Ψ t ₊sz vs
    }}}.
  Proof.
    iIntros "%Φ (HΨ & #Hfn) HΦ".

    wp۰rec.
    wp۰apply+ assume𑁒spec' as "%Hsz".
    wp۰apply+ (array٠unsafe_initi𑁒spec Ψ with "[$HΨ $Hfn]"); first done.
    iSteps.
  Qed.
  Lemma array٠initi𑁒spec' Ψ sz fn :
    {{{
      ▷ (
        ∀ t,
        |={⊤}=> Ψ t 0 []
      ) ∗
      ( [∗ list] i ∈ seq 0 ₊sz,
        ∀ t vs,
        ⌜i = length vs⌝ -∗
        Ψ t i vs -∗
        WP fn #i {{ v,
          ▷ Ψ t ˖i (vs ++ [v])
        }}
      )
    }}}
      array٠initi #sz fn
    {{{
      t vs
    , RET t;
      ⌜0 ≤ sz⌝%Z ∗
      ⌜length vs = ₊sz⌝ ∗
      array۰model t (DfracOwn 1) vs ∗
      Ψ t ₊sz vs
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hfn) HΦ".

    wp۰rec.
    wp۰apply+ assume𑁒spec' as "%Hsz".
    wp۰apply+ (array٠unsafe_initi𑁒spec' Ψ with "[$HΨ $Hfn]"); first done.
    iSteps.
  Qed.
  Lemma array٠initi𑁒spec𑁒disentangled Ψ sz fn :
    {{{
      □ (
        ∀ i,
        ⌜i < ₊sz⌝ -∗
        WP fn #i {{ v,
          ▷ Ψ i v
        }}
      )
    }}}
      array٠initi #sz fn
    {{{
      t vs
    , RET t;
      ⌜0 ≤ sz⌝%Z ∗
      ⌜length vs = ₊sz⌝ ∗
      array۰model t (DfracOwn 1) vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Φ #Hfn HΦ".

    wp۰rec.
    wp۰apply+ assume𑁒spec' as "%Hsz".
    wp۰apply+ (array٠unsafe_initi𑁒spec𑁒disentangled Ψ with "Hfn"); first done.
    iSteps.
  Qed.
  Lemma array٠initi𑁒spec𑁒disentangled' Ψ sz fn :
    {{{
      ( [∗ list] i ∈ seq 0 ₊sz,
        WP fn #i {{ v,
          ▷ Ψ i v
        }}
      )
    }}}
      array٠initi #sz fn
    {{{
      t vs
    , RET t;
      ⌜0 ≤ sz⌝%Z ∗
      ⌜length vs = ₊sz⌝ ∗
      array۰model t (DfracOwn 1) vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Φ Hfn HΦ".

    wp۰rec.
    wp۰apply+ assume𑁒spec' as "%Hsz".
    wp۰apply+ (array٠unsafe_initi𑁒spec𑁒disentangled' Ψ with "Hfn"); first done.
    iSteps.
  Qed.

  Lemma array٠unsafe_init𑁒spec Ψ sz fn :
    (0 ≤ sz)%Z →
    {{{
      ▷ (
        ∀ t,
        |={⊤}=> Ψ t 0 []
      ) ∗
      □ (
        ∀ t i vs,
        ⌜i < ₊sz⌝ -∗
        ⌜i = length vs⌝ -∗
        Ψ t i vs -∗
        WP fn () {{ v,
          ▷ Ψ t ˖i (vs ++ [v])
        }}
      )
    }}}
      array٠unsafe_init #sz fn
    {{{
      t vs
    , RET t;
      ⌜length vs = ₊sz⌝ ∗
      array۰model t (DfracOwn 1) vs ∗
      Ψ t ₊sz vs
    }}}.
  Proof.
    iIntros "%Hsz %Φ (HΨ & #Hfn) HΦ".

    wp۰rec.
    wp۰apply+ (array٠unsafe_initi𑁒spec Ψ with "[$HΨ] HΦ"); first done.
    iSteps.
  Qed.
  Lemma array٠unsafe_init𑁒spec' Ψ sz fn :
    (0 ≤ sz)%Z →
    {{{
      ▷ (
        ∀ t,
        |={⊤}=> Ψ t 0 []
      ) ∗
      ( [∗ list] i ∈ seq 0 ₊sz,
        ∀ t vs,
        ⌜i = length vs⌝ -∗
        Ψ t i vs -∗
        WP fn () {{ v,
          ▷ Ψ t ˖i (vs ++ [v])
        }}
      )
    }}}
      array٠unsafe_init #sz fn
    {{{
      t vs
    , RET t;
      ⌜length vs = ₊sz⌝ ∗
      array۰model t (DfracOwn 1) vs ∗
      Ψ t ₊sz vs
    }}}.
  Proof.
    iIntros "%Hsz %Φ (HΨ & Hfn) HΦ".

    wp۰rec.
    wp۰apply+ (array٠unsafe_initi𑁒spec' Ψ with "[$HΨ Hfn] HΦ"); first done.
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.
  Lemma array٠unsafe_init𑁒spec𑁒disentangled Ψ sz fn :
    (0 ≤ sz)%Z →
    {{{
      □ (
        ∀ i,
        ⌜i < ₊sz⌝ -∗
        WP fn () {{ v,
          ▷ Ψ i v
        }}
      )
    }}}
      array٠unsafe_init #sz fn
    {{{
      t vs
    , RET t;
      ⌜length vs = ₊sz⌝ ∗
      array۰model t (DfracOwn 1) vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Hsz %Φ #Hfn HΦ".

    wp۰rec.
    wp۰apply+ (array٠unsafe_initi𑁒spec𑁒disentangled Ψ with "[] HΦ"); first done.
    iSteps.
  Qed.
  Lemma array٠unsafe_init𑁒spec𑁒disentangled' Ψ sz fn :
    (0 ≤ sz)%Z →
    {{{
      ( [∗ list] i ∈ seq 0 ₊sz,
        WP fn () {{ v,
          ▷ Ψ i v
        }}
      )
    }}}
      array٠unsafe_init #sz fn
    {{{
      t vs
    , RET t;
      ⌜length vs = ₊sz⌝ ∗
      array۰model t (DfracOwn 1) vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Hsz %Φ Hfn HΦ".

    wp۰rec.
    wp۰apply+ (array٠unsafe_initi𑁒spec𑁒disentangled' Ψ with "[Hfn] HΦ"); first done.
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.

  Lemma array٠init𑁒spec Ψ sz fn :
    {{{
      ▷ (
        ∀ t,
        |={⊤}=> Ψ t 0 []
      ) ∗
      □ (
        ∀ t i vs,
        ⌜i < ₊sz⌝ -∗
        ⌜i = length vs⌝ -∗
        Ψ t i vs -∗
        WP fn () {{ v,
          ▷ Ψ t ˖i (vs ++ [v])
        }}
      )
    }}}
      array٠init #sz fn
    {{{
      t vs
    , RET t;
      ⌜0 ≤ sz⌝%Z ∗
      ⌜length vs = ₊sz⌝ ∗
      array۰model t (DfracOwn 1) vs ∗
      Ψ t ₊sz vs
    }}}.
  Proof.
    iIntros "%Φ (HΨ & #Hfn) HΦ".

    wp۰rec.
    wp۰apply+ assume𑁒spec' as "%Hsz".
    wp۰apply+ (array٠unsafe_init𑁒spec Ψ with "[$HΨ $Hfn]"); first done.
    iSteps.
  Qed.
  Lemma array٠init𑁒spec' Ψ sz fn :
    {{{
      ▷ (
        ∀ t,
        |={⊤}=> Ψ t 0 []
      ) ∗
      ( [∗ list] i ∈ seq 0 ₊sz,
        ∀ t vs,
        ⌜i = length vs⌝ -∗
        Ψ t i vs -∗
        WP fn () {{ v,
          ▷ Ψ t ˖i (vs ++ [v])
        }}
      )
    }}}
      array٠init #sz fn
    {{{
      t vs
    , RET t;
      ⌜0 ≤ sz⌝%Z ∗
      ⌜length vs = ₊sz⌝ ∗
      array۰model t (DfracOwn 1) vs ∗
      Ψ t ₊sz vs
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hfn) HΦ".

    wp۰rec.
    wp۰apply+ assume𑁒spec' as "%Hsz".
    wp۰apply+ (array٠unsafe_init𑁒spec' Ψ with "[$HΨ $Hfn]"); first done.
    iSteps.
  Qed.
  Lemma array٠init𑁒spec𑁒disentangled Ψ sz fn :
    {{{
      □ (
        ∀ i,
        ⌜i < ₊sz⌝ -∗
        WP fn () {{ v,
          ▷ Ψ i v
        }}
      )
    }}}
      array٠init #sz fn
    {{{
      t vs
    , RET t;
      ⌜0 ≤ sz⌝%Z ∗
      ⌜length vs = ₊sz⌝ ∗
      array۰model t (DfracOwn 1) vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Φ #Hfn HΦ".

    wp۰rec.
    wp۰apply+ assume𑁒spec' as "%Hsz".
    wp۰apply+ (array٠unsafe_init𑁒spec𑁒disentangled Ψ with "Hfn"); first done.
    iSteps.
  Qed.
  Lemma array٠init𑁒spec𑁒disentangled' Ψ sz fn :
    {{{
      ( [∗ list] i ∈ seq 0 ₊sz,
        WP fn () {{ v,
          ▷ Ψ i v
        }}
      )
    }}}
      array٠init #sz fn
    {{{
      t vs
    , RET t;
      ⌜0 ≤ sz⌝%Z ∗
      ⌜length vs = ₊sz⌝ ∗
      array۰model t (DfracOwn 1) vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Φ Hfn HΦ".

    wp۰rec.
    wp۰apply+ assume𑁒spec' as "%Hsz".
    wp۰apply+ (array٠unsafe_init𑁒spec𑁒disentangled' Ψ with "Hfn"); first done.
    iSteps.
  Qed.

  Lemma array٠mapi𑁒spec𑁒atomic Ψ fn t sz :
    {{{
      array۰inv t sz ∗
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
              ▷ Ψ ˖i (vs ++ [v]) None (ws ++ [w])
            }}
        end
      )
    }}}
      array٠mapi fn t
    {{{
      t' vs ws
    , RET t';
      ⌜length vs = sz⌝ ∗
      ⌜length vs = length ws⌝ ∗
      array۰model t' (DfracOwn 1) ws ∗
      Ψ sz vs None ws
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & HΨ & #H) HΦ".

    wp۰rec.
    wp۰apply+ (array٠size𑁒spec𑁒inv with "Hinv") as "_".

    pose Ψ' t' i ws := (
      ∃ vs,
      ⌜length vs = length ws⌝ ∗
      Ψ i vs None ws
    )%I.
    wp۰apply (array٠unsafe_initi𑁒spec Ψ' with "[HΨ]") as "%t' %ws (%Hws & Hmodel & (%vs & %Hvs & HΨ))"; first lia.
    { iSplit.
      - iSteps. iExists []. iSteps.
      - iIntros "!> %t' %i %ws %Hi1 %Hi2 (%vs & %Hvs & HΨ)".
        iDestruct ("H" with "[%] [%] [//] HΨ") as "H'"; [lia.. |].
        awp۰apply+ (array٠unsafe_get𑁒spec𑁒atomic𑁒cell with "[//]").
        iApply (aacc𑁒aupd𑁒commit with "H'"); first done. iIntros "%dq %v Hslice".
        rewrite Nat2Z.id.
        iAaccIntro with "[$Hslice]". 1,2: iSteps. iIntros "$ !> HΨ !> H£".
        iMod (lc_fupd_elim_later with "H£ HΨ") as "HΨ".
        wp۰apply (wp𑁒wand with "(H [%] [%] [//] HΨ)") as (w) "HΨ"; [lia.. |].
        iExists (vs ++ [v]). simpl_length. iSteps.
    }
    rewrite Nat2Z.id.

    iApply ("HΦ" with "[$Hmodel $HΨ]").
    iSteps.
  Qed.
  Lemma array٠mapi𑁒spec Ψ fn t dq vs :
    {{{
      ▷ Ψ 0 [] [] ∗
      array۰model t dq vs ∗
      □ (
        ∀ i v ws,
        ⌜vs !! i = Some v⌝ -∗
        ⌜i = length ws⌝ -∗
        Ψ i (take i vs) ws -∗
        WP fn #i v {{ w,
          ▷ Ψ ˖i (take i vs ++ [v]) (ws ++ [w])
        }}
      )
    }}}
      array٠mapi fn t
    {{{
      t' ws
    , RET t';
      ⌜length ws = length vs⌝ ∗
      array۰model t dq vs ∗
      array۰model t' (DfracOwn 1) ws ∗
      Ψ (length vs) vs ws
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hmodel & #Hfn) HΦ".
    iDestruct (array۰model𑁒to𑁒inv with "Hmodel") as "#Hinv".
    pose (Ψ' i vs_left o ws := (
      ⌜vs_left = take i vs⌝ ∗
      array۰model t dq vs ∗
      Ψ i vs_left ws ∗
      ⌜from_option (λ v, v = vs !!! i) True o⌝%I
    )%I).
    wp۰apply (array٠mapi𑁒spec𑁒atomic Ψ' with "[$Hinv $HΨ $Hmodel]") as "%t' %vs_left %ws (%Hvs_left & %Hws & Hmodel' & (-> & Hmodel & HΨ & _))".
    { iStep.
      iIntros "!> %i %vs_left %o %ws %Hi1 %Hi2 %Hws (-> & Hmodel & HΨ & %Ho)".
      opose proof* (list_lookup_lookup_total_lt vs i); first lia.
      destruct o as [v |].
      - rewrite Ho.
        wp۰apply (wp𑁒wand with "(Hfn [//] [] HΨ)") as "%w HΨ"; first iSteps. iFrame.
        erewrite take_S_r => //.
      - iDestruct (array۰model𑁒lookup𑁒acc i with "Hmodel") as "(H↦ & Hmodel)"; first done.
        iAuIntro. iAaccIntro with "H↦"; iSteps.
    }
    rewrite /Ψ' firstn_all2 in Hws |- *; first lia.
    apply symmetry in Hws.
    iSteps.
  Qed.
  Lemma array٠mapi𑁒spec' Ψ fn t dq vs :
    {{{
      ▷ Ψ 0 [] [] ∗
      array۰model t dq vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        ∀ ws,
        ⌜i = length ws⌝ -∗
        Ψ i (take i vs) ws -∗
        WP fn #i v {{ w,
          ▷ Ψ ˖i (take i vs ++ [v]) (ws ++ [w])
        }}
      )
    }}}
      array٠mapi fn t
    {{{
      t' ws
    , RET t';
      ⌜length ws = length vs⌝ ∗
      array۰model t dq vs ∗
      array۰model t' (DfracOwn 1) ws ∗
      Ψ (length vs) vs ws
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hmodel & Hfn) HΦ".
    match goal with |- context [big_opL bi_sep ?Ξ' _] => set Ξ := Ξ' end.
    pose (Ψ' i vs_left ws := (
      Ψ i vs_left ws ∗
      [∗ list] j ↦ v ∈ drop i vs, Ξ (i + j) v
    )%I).
    wp۰apply (array٠mapi𑁒spec Ψ' with "[$HΨ $Hmodel $Hfn]"); last iSteps.
    iIntros "!> %i %v %ws %Hlookup %Hi (HΨ & HΞ)".
    erewrite drop_S => //.
    iDestruct "HΞ" as "(Hfn & HΞ)".
    rewrite Nat.add_0_r. setoid_rewrite Nat.add_succ_r. iSteps.
  Qed.
  Lemma array٠mapi𑁒spec𑁒disentangled Ψ fn t dq vs :
    {{{
      array۰model t dq vs ∗
      □ (
        ∀ i v,
        ⌜vs !! i = Some v⌝ -∗
        WP fn #i v {{ w,
          ▷ Ψ i v w
        }}
      )
    }}}
      array٠mapi fn t
    {{{
      t' ws
    , RET t';
      ⌜length ws = length vs⌝ ∗
      array۰model t dq vs ∗
      array۰model t' (DfracOwn 1) ws ∗
      ( [∗ list] i ↦ v; w ∈ vs; ws,
        Ψ i v w
      )
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & #Hfn) HΦ".
    pose Ψ' i vs_left ws := (
      [∗ list] j ↦ v; w ∈ vs_left; ws, Ψ j v w
    )%I.
    wp۰apply (array٠mapi𑁒spec Ψ' with "[$Hmodel]"); last iSteps.
    rewrite /Ψ'. iSteps.
    rewrite big_sepL2_snoc length_take Nat.min_l; last iSteps.
    eapply Nat.lt_le_incl, lookup_lt_Some. done.
  Qed.
  Lemma array٠mapi𑁒spec𑁒disentangled' Ψ fn t dq vs :
    {{{
      array۰model t dq vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        WP fn #i v {{ w,
          ▷ Ψ i v w
        }}
      )
    }}}
      array٠mapi fn t
    {{{
      t' ws
    , RET t';
      ⌜length ws = length vs⌝ ∗
      array۰model t dq vs ∗
      array۰model t' (DfracOwn 1) ws ∗
      ( [∗ list] i ↦ v; w ∈ vs; ws,
        Ψ i v w
      )
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & Hfn) HΦ".
    pose Ψ' i vs_left ws := (
      [∗ list] j ↦ v; w ∈ vs_left; ws, Ψ j v w
    )%I.
    wp۰apply (array٠mapi𑁒spec' Ψ' with "[$Hmodel Hfn]"); last iSteps.
    rewrite /Ψ'. iSteps.
    iApply (big_sepL_impl with "Hfn"). iSteps.
    rewrite big_sepL2_snoc length_take Nat.min_l; last iSteps.
    eapply Nat.lt_le_incl, lookup_lt_Some. done.
  Qed.

  Lemma array٠map𑁒spec𑁒atomic Ψ fn t sz :
    {{{
      array۰inv t sz ∗
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
              ▷ Ψ ˖i (vs ++ [v]) None (ws ++ [w])
            }}
        end
      )
    }}}
      array٠map fn t
    {{{
      t' vs ws
    , RET t';
      ⌜length vs = sz⌝ ∗
      ⌜length vs = length ws⌝ ∗
      array۰model t' (DfracOwn 1) ws ∗
      Ψ sz vs None ws
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & HΨ & #H) HΦ".
    wp۰rec.
    wp۰apply+ (array٠mapi𑁒spec𑁒atomic Ψ with "[$Hinv $HΨ H] HΦ") as "!> %i %vs %o %ws %Hi1 %Hi2 %Hws HΨ".
    case_match; try wp۰pures; iApply ("H" with "[%] [%] [//] HΨ"); lia.
  Qed.
  Lemma array٠map𑁒spec Ψ fn t dq vs :
    {{{
      ▷ Ψ 0 [] [] ∗
      array۰model t dq vs ∗
      □ (
        ∀ i v ws,
        ⌜vs !! i = Some v⌝ -∗
        ⌜i = length ws⌝ -∗
        Ψ i (take i vs) ws -∗
        WP fn v {{ w,
          ▷ Ψ ˖i (take i vs ++ [v]) (ws ++ [w])
        }}
      )
    }}}
      array٠map fn t
    {{{
      t' ws
    , RET t';
      ⌜length ws = length vs⌝ ∗
      array۰model t dq vs ∗
      array۰model t' (DfracOwn 1) ws ∗
      Ψ (length vs) vs ws
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hmodel & #Hfn) HΦ".
    wp۰rec.
    wp۰apply+ (array٠mapi𑁒spec Ψ with "[$HΨ $Hmodel] HΦ").
    iSteps.
  Qed.
  Lemma array٠map𑁒spec' Ψ fn t dq vs :
    {{{
      ▷ Ψ 0 [] [] ∗
      array۰model t dq vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        ∀ ws,
        ⌜i = length ws⌝ -∗
        Ψ i (take i vs) ws -∗
        WP fn v {{ w,
          ▷ Ψ ˖i (take i vs ++ [v]) (ws ++ [w])
        }}
      )
    }}}
      array٠map fn t
    {{{
      t' ws
    , RET t';
      ⌜length ws = length vs⌝ ∗
      array۰model t dq vs ∗
      array۰model t' (DfracOwn 1) ws ∗
      Ψ (length vs) vs ws
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hmodel & Hfn) HΦ".
    wp۰rec.
    wp۰apply+ (array٠mapi𑁒spec' Ψ with "[$HΨ $Hmodel Hfn] HΦ").
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.
  Lemma array٠map𑁒spec𑁒disentangled Ψ fn t dq vs :
    {{{
      array۰model t dq vs ∗
      □ (
        ∀ i v,
        ⌜vs !! i = Some v⌝ -∗
        WP fn v {{ w,
          ▷ Ψ i v w
        }}
      )
    }}}
      array٠map fn t
    {{{
      t' ws
    , RET t';
      ⌜length ws = length vs⌝ ∗
      array۰model t dq vs ∗
      array۰model t' (DfracOwn 1) ws ∗
      ( [∗ list] i ↦ v; w ∈ vs; ws,
        Ψ i v w
      )
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & #Hfn) HΦ".
    wp۰rec.
    wp۰apply+ (array٠mapi𑁒spec𑁒disentangled Ψ with "[$Hmodel] HΦ").
    iSteps.
  Qed.
  Lemma array٠map𑁒spec𑁒disentangled' Ψ fn t dq vs :
    {{{
      array۰model t dq vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        WP fn v {{ w,
          ▷ Ψ i v w
        }}
      )
    }}}
      array٠map fn t
    {{{
      t' ws
    , RET t';
      ⌜length ws = length vs⌝ ∗
      array۰model t dq vs ∗
      array۰model t' (DfracOwn 1) ws ∗
      ( [∗ list] i ↦ v; w ∈ vs; ws,
        Ψ i v w
      )
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & Hfn) HΦ".
    wp۰rec.
    wp۰apply+ (array٠mapi𑁒spec𑁒disentangled' Ψ with "[$Hmodel Hfn] HΦ").
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.

  Lemma array٠unsafe_copy_slice𑁒spec𑁒atomic Ψ t1 (i1 : Z) t2 (i2 n : Z) :
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
              ▷ Ψ ˖k (vs ++ [v]) None
            )
        end
      )
    }}}
      array٠unsafe_copy_slice t1 #i1 t2 #i2 #n
    {{{
      vs
    , RET ();
      ⌜length vs = ₊n⌝ ∗
      Ψ ₊n vs None
    }}}.
  Proof.
    iIntros "%Hi1 %Hi2 %Hn %Φ (HΨ & #H) HΦ".
    wp۰rec.
    pose Ψ' (_ : Z) k := (
      ∃ vs,
      ⌜length vs = k⌝ ∗
      Ψ k vs None
    )%I.
    wp۰apply+ (for𑁒spec𑁒strong Ψ' with "[HΨ]").
    { iSplitL. { iExists []. iSteps. }
      iIntros "!> % %k -> %Hk (%vs & %Hvs & HΨ)".
      iDestruct ("H" with "[%] [//] HΨ") as "H'"; first lia.
      awp۰apply+ (array٠unsafe_get𑁒spec𑁒atomic𑁒cell with "[//]").
      iApply (aacc𑁒aupd𑁒commit with "H'"); first done. iIntros "%dq %v Hslice".
      iAaccIntro with "[$Hslice]". 1,2: iSteps.
      rewrite Z.add_0_l Z2Nat.inj_add; [lia.. |].
      rewrite Nat2Z.id.
      iIntros "$ !> HΨ !> _".
      iDestruct ("H" with "[%] [//] HΨ") as "H'"; first lia.
      awp۰apply+ (array٠unsafe_set𑁒spec𑁒atomic𑁒cell with "[//]").
      iApply (aacc𑁒aupd𑁒commit with "H'"); first done. iIntros "%w Hslice".
      iAaccIntro with "[$Hslice]". 1,2: iSteps. iIntros "$ !> HΨ !> _".
      iFrameSteps.
      iPureIntro. simpl_length/=. lia.
    }
    rewrite Z.sub_0_r. iSteps.
  Qed.
  Lemma array٠unsafe_copy_slice𑁒spec𑁒slice𑁒fit t1 (i1 : Z) i1_ dq1 vs1 t2 (i2 : Z) i2_ vs2 (n : Z) :
    i1 = ⁺i1_ →
    i2 = ⁺i2_ →
    n = length vs1 →
    length vs1 = length vs2 →
    {{{
      array۰slice t1 i1_ dq1 vs1 ∗
      array۰slice t2 i2_ (DfracOwn 1) vs2
    }}}
      array٠unsafe_copy_slice t1 #i1 t2 #i2 #n
    {{{
      RET ();
      array۰slice t1 i1_ dq1 vs1 ∗
      array۰slice t2 i2_ (DfracOwn 1) vs1
    }}}.
  Proof.
    iIntros (-> -> -> ?) "%Φ (Hslice1 & Hslice2) HΦ".
    pose (Ψ k vs1_done o := (
      ⌜vs1_done = take k vs1⌝ ∗
      array۰slice t1 i1_ dq1 vs1 ∗
      array۰slice t2 i2_ (DfracOwn 1) (vs1_done ++ drop k vs2) ∗
      ⌜from_option (λ v1, vs1 !! k = Some v1) True o⌝
    )%I).
    wp۰apply (array٠unsafe_copy_slice𑁒spec𑁒atomic Ψ with "[$Hslice1 $Hslice2]") as "%vs1_done (_ & (-> & Hslice1 & Hslice2 & _))"; [lia.. | |].
    { iStep.
      iIntros "!> %k %vs1_done %o %Hk _ (-> & Hslice1 & Hslice2 & %Hlookup)".
      rewrite !Nat2Z.id.
      opose proof* (list_lookup_lookup_total_lt vs2 k); first lia.
      destruct o as [v1 |].
      - opose proof* (list_lookup_lookup_total_lt vs2 k); first lia.
        iDestruct (array۰slice𑁒update with "Hslice2") as "(H↦2 & Hslice2)".
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
        iDestruct (array۰slice𑁒lookup𑁒acc k with "Hslice1") as "(H↦1 & Hslice1)"; first done.
        iAuIntro. iAaccIntro with "H↦1"; iSteps.
    }
    iApply ("HΦ" with "[$Hslice1 Hslice2]").
    rewrite firstn_all2; first lia. rewrite skipn_all2; first lia. rewrite right_id //.
  Qed.
  Lemma array٠unsafe_copy_slice𑁒spec𑁒slice𑁒fit𑁒src t1 (i1 : Z) i1_ dq1 vs1 t2 i2 (j2 : Z) vs2 (n : Z) :
    i1 = ⁺i1_ →
    (i2 ≤ j2)%Z →
    n = length vs1 →
    (j2 + n ≤ i2 + length vs2)%Z →
    {{{
      array۰slice t1 i1_ dq1 vs1 ∗
      array۰slice t2 i2 (DfracOwn 1) vs2
    }}}
      array٠unsafe_copy_slice t1 #i1 t2 #j2 #n
    {{{
      RET ();
      array۰slice t1 i1_ dq1 vs1 ∗
      array۰slice t2 i2 (DfracOwn 1) (with_slice (₊j2 - i2) ₊n vs2 vs1)
    }}}.
  Proof.
    iIntros (-> ? ? ?) "%Φ (Hslice1 & Hslice2) HΦ".
    Z_to_nat j2. rewrite Nat2Z.id.
    rewrite (Nat.le_add_sub i2 j2); first lia. set k2 := j2 - i2.
    rewrite -{1}(take_drop k2 vs2) -(take_drop ₊n (drop k2 vs2)) drop_drop.
    iDestruct (array۰slice𑁒app𑁒3₂ with "Hslice2") as "(Hslice21 & Hslice22 & Hslice23)"; first done.
    simpl_length. rewrite !Nat.min_l; [lia.. |].
    wp۰apply (array٠unsafe_copy_slice𑁒spec𑁒slice𑁒fit with "[$Hslice1 $Hslice22]") as "(Hslice1 & Hslice22)"; [simpl_length; lia.. |].
    iApply "HΦ".
    iDestruct (array۰slice𑁒app𑁒3₁ with "Hslice21 Hslice22 Hslice23") as "Hslice2"; [simpl_length; lia.. |].
    rewrite -Nat.le_add_sub; first lia.
    iSteps.
  Qed.
  Lemma array٠unsafe_copy_slice𑁒spec𑁒slice𑁒fit𑁒dst t1 i1 (j1 : Z) dq1 vs1 t2 (i2 : Z) i2_ vs2 (n : Z) :
    (i1 ≤ j1)%Z →
    i2 = ⁺i2_ →
    n = length vs2 →
    (j1 + n ≤ i1 + length vs1)%Z →
    {{{
      array۰slice t1 i1 dq1 vs1 ∗
      array۰slice t2 i2_ (DfracOwn 1) vs2
    }}}
      array٠unsafe_copy_slice t1 #j1 t2 #i2 #n
    {{{
      RET ();
      array۰slice t1 i1 dq1 vs1 ∗
      array۰slice t2 i2_ (DfracOwn 1) (slice (₊j1 - i1) ₊n vs1)
    }}}.
  Proof.
    iIntros (? -> ? ?) "%Φ (Hslice1 & Hslice2) HΦ".
    Z_to_nat j1. rewrite Nat2Z.id.
    rewrite (Nat.le_add_sub i1 j1); first lia. set k1 := j1 - i1.
    rewrite -{1 2}(take_drop k1 vs1) -(take_drop ₊n (drop k1 vs1)) drop_drop.
    iDestruct (array۰slice𑁒app𑁒3₂ with "Hslice1") as "(Hslice11 & Hslice12 & Hslice13)"; first done.
    simpl_length. rewrite !Nat.min_l; [lia.. |].
    wp۰apply (array٠unsafe_copy_slice𑁒spec𑁒slice𑁒fit with "[$Hslice12 $Hslice2]") as "(Hslice12 & Hslice2)"; [simpl_length; lia.. |].
    iApply "HΦ".
    iDestruct (array۰slice𑁒app𑁒3₁ with "Hslice11 Hslice12 Hslice13") as "$"; [simpl_length; lia.. |].
    rewrite -Nat.le_add_sub //; first lia.
  Qed.
  Lemma array٠unsafe_copy_slice𑁒spec𑁒slice t1 i1 (j1 : Z) dq1 vs1 t2 i2 (j2 : Z) vs2 (n : Z) :
    (i1 ≤ j1)%Z →
    (i2 ≤ j2)%Z →
    (0 ≤ n)%Z →
    (j1 + n ≤ i1 + length vs1)%Z →
    (j2 + n ≤ i2 + length vs2)%Z →
    {{{
      array۰slice t1 i1 dq1 vs1 ∗
      array۰slice t2 i2 (DfracOwn 1) vs2
    }}}
      array٠unsafe_copy_slice t1 #j1 t2 #j2 #n
    {{{
      RET ();
      array۰slice t1 i1 dq1 vs1 ∗
      array۰slice t2 i2 (DfracOwn 1) (with_slice (₊j2 - i2) ₊n vs2 (take ₊n (drop (₊j1 - i1) vs1)))
    }}}.
  Proof.
    iIntros "% % % % % %Φ (Hslice1 & Hslice2) HΦ".
    Z_to_nat j2. rewrite Nat2Z.id.
    rewrite (Nat.le_add_sub i2 j2); first lia. set k2 := j2 - i2.
    rewrite -{1}(take_drop k2 vs2) -(take_drop ₊n (drop k2 vs2)) drop_drop.
    iDestruct (array۰slice𑁒app𑁒3₂ with "Hslice2") as "(Hslice21 & Hslice22 & Hslice23)"; first done.
    simpl_length. rewrite !Nat.min_l; [lia.. |].
    wp۰apply (array٠unsafe_copy_slice𑁒spec𑁒slice𑁒fit𑁒dst with "[$Hslice1 $Hslice22]") as "(Hslice1 & Hslice22)"; [simpl_length; lia.. |].
    iApply "HΦ".
    iDestruct (array۰slice𑁒app𑁒3₁ with "Hslice21 Hslice22 Hslice23") as "Hslice2"; [simpl_length; lia.. |].
    rewrite -Nat.le_add_sub; first lia.
    iSteps.
  Qed.
  Lemma array٠unsafe_copy_slice𑁒spec t1 (i1 : Z) dq1 vs1 t2 (i2 : Z) vs2 (n : Z) :
    (0 ≤ i1)%Z →
    (0 ≤ i2)%Z →
    (0 ≤ n)%Z →
    (i1 + n ≤ length vs1)%Z →
    (i2 + n ≤ length vs2)%Z →
    {{{
      array۰model t1 dq1 vs1 ∗
      array۰model t2 (DfracOwn 1) vs2
    }}}
      array٠unsafe_copy_slice t1 #i1 t2 #i2 #n
    {{{
      RET ();
      array۰model t1 dq1 vs1 ∗
      array۰model t2 (DfracOwn 1) (with_slice ₊i2 ₊n vs2 (take ₊n (drop ₊i1 vs1)))
    }}}.
  Proof.
    iIntros "% % % % % %Φ (Hmodel1 & Hmodel2) HΦ".
    iDestruct (array۰model𑁒to𑁒slice' with "Hmodel1") as "(Hslice1 & #?)".
    iDestruct (array۰model𑁒to𑁒slice' with "Hmodel2") as "(Hslice2 & #?)".
    wp۰apply (array٠unsafe_copy_slice𑁒spec𑁒slice with "[$Hslice1 $Hslice2]") as "(Hslice1 & Hslice2)"; [lia.. |].
    rewrite !Nat.sub_0_r. iSteps. iPureIntro.
    simpl_length. lia.
  Qed.

  Lemma array٠copy_slice𑁒spec𑁒slice𑁒fit t1 sz1 (i1 : Z) i1_ dq1 vs1 t2 sz2 (i2 : Z) i2_ vs2 (n : Z) :
    i1_ = ₊i1 →
    i2_ = ₊i2 →
    {{{
      array۰inv t1 sz1 ∗
      array۰inv t2 sz2 ∗
      ( ⌜0 ≤ i1⌝%Z -∗
        ⌜0 ≤ i2⌝%Z -∗
        ⌜0 ≤ n⌝%Z -∗
        ⌜i1 + n ≤ sz1⌝%Z -∗
        ⌜i2 + n ≤ sz2⌝%Z -∗
          ⌜₊n = length vs1⌝ ∗
          ⌜length vs1 = length vs2⌝ ∗
          array۰slice t1 i1_ dq1 vs1 ∗
          array۰slice t2 i2_ (DfracOwn 1) vs2
      )
    }}}
      array٠copy_slice t1 #i1 t2 #i2 #n
    {{{
      RET ();
      ⌜0 ≤ i1⌝%Z ∗
      ⌜0 ≤ i2⌝%Z ∗
      ⌜0 ≤ n⌝%Z ∗
      ⌜i1 + n ≤ sz1⌝%Z ∗
      ⌜i2 + n ≤ sz2⌝%Z ∗
      array۰slice t1 i1_ dq1 vs1 ∗
      array۰slice t2 i2_ (DfracOwn 1) vs1
    }}}.
  Proof.
    iIntros (-> ->) "%Φ (#Hinv1 & #Hinv2 & H) HΦ".
    wp۰rec.
    wp۰apply+ (array٠size𑁒spec𑁒inv with "Hinv1") as "_".
    wp۰apply+ (array٠size𑁒spec𑁒inv with "Hinv2") as "_".
    repeat (wp۰apply+ assume𑁒spec' as "%").
    iDestruct ("H" with "[//] [//] [//] [//] [//]") as "(% & % & Hslice1 & Hslice2)".
    wp۰apply+ (array٠unsafe_copy_slice𑁒spec𑁒slice𑁒fit with "[$Hslice1 $Hslice2]"); [lia.. |].
    iSteps.
  Qed.
  Lemma array٠copy_slice𑁒spec𑁒slice t1 sz1 i1 (j1 : Z) dq1 vs1 t2 sz2 i2 (j2 : Z) vs2 (n : Z) :
    {{{
      array۰inv t1 sz1 ∗
      array۰inv t2 sz2 ∗
      ( ⌜0 ≤ j1⌝%Z -∗
        ⌜0 ≤ j2⌝%Z -∗
        ⌜0 ≤ n⌝%Z -∗
        ⌜j1 + n ≤ sz1⌝%Z -∗
        ⌜j2 + n ≤ sz2⌝%Z -∗
          ⌜i1 ≤ ₊j1⌝ ∗
          ⌜i2 ≤ ₊j2⌝ ∗
          ⌜₊j1 + n ≤ i1 + length vs1⌝%Z ∗
          ⌜₊j2 + n ≤ i2 + length vs2⌝%Z ∗
          array۰slice t1 i1 dq1 vs1 ∗
          array۰slice t2 i2 (DfracOwn 1) vs2
      )
    }}}
      array٠copy_slice t1 #j1 t2 #j2 #n
    {{{
      RET ();
      ⌜0 ≤ j1⌝%Z ∗
      ⌜0 ≤ j2⌝%Z ∗
      ⌜0 ≤ n⌝%Z ∗
      ⌜j1 + n ≤ sz1⌝%Z ∗
      ⌜j2 + n ≤ sz2⌝%Z ∗
      array۰slice t1 i1 dq1 vs1 ∗
      array۰slice t2 i2 (DfracOwn 1) (with_slice (₊j2 - i2) ₊n vs2 (take ₊n (drop (₊j1 - i1) vs1)))
    }}}.
  Proof.
    iIntros "%Φ (#Hinv1 & #Hinv2 & H) HΦ".
    wp۰rec.
    wp۰apply+ (array٠size𑁒spec𑁒inv with "Hinv1") as "_".
    wp۰apply+ (array٠size𑁒spec𑁒inv with "Hinv2") as "_".
    repeat (wp۰apply+ assume𑁒spec' as "%").
    iDestruct ("H" with "[//] [//] [//] [//] [//]") as "(% & % & % & % & Hslice1 & Hslice2)".
    wp۰apply+ (array٠unsafe_copy_slice𑁒spec𑁒slice with "[$Hslice1 $Hslice2]"); [lia.. |].
    iSteps.
  Qed.
  Lemma array٠copy_slice𑁒spec t1 (i1 : Z) dq1 vs1 t2 (i2 : Z) vs2 (n : Z) :
    {{{
      array۰model t1 dq1 vs1 ∗
      array۰model t2 (DfracOwn 1) vs2
    }}}
      array٠copy_slice t1 #i1 t2 #i2 #n
    {{{
      RET ();
      ⌜0 ≤ i1⌝%Z ∗
      ⌜0 ≤ i2⌝%Z ∗
      ⌜0 ≤ n⌝%Z ∗
      ⌜i1 + n ≤ length vs1⌝%Z ∗
      ⌜i2 + n ≤ length vs2⌝%Z ∗
      array۰model t1 dq1 vs1 ∗
      array۰model t2 (DfracOwn 1) (with_slice ₊i2 ₊n vs2 (take ₊n (drop ₊i1 vs1)))
    }}}.
  Proof.
    iIntros "%Φ (Hmodel1 & Hmodel2) HΦ".
    wp۰rec.
    wp۰apply+ (array٠size𑁒spec with "Hmodel1") as "Hmodel1".
    wp۰apply+ (array٠size𑁒spec with "Hmodel2") as "Hmodel2".
    repeat (wp۰apply+ assume𑁒spec' as "%").
    wp۰apply+ (array٠unsafe_copy_slice𑁒spec with "[$Hmodel1 $Hmodel2]"); [lia.. |].
    iSteps.
  Qed.

  Lemma array٠unsafe_copy𑁒spec𑁒atomic Ψ t1 sz1 t2 sz2 (i2 : Z) :
    (0 ≤ i2)%Z →
    {{{
      array۰inv t1 sz1 ∗
      array۰inv t2 sz2 ∗
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
              ▷ Ψ ˖k (vs ++ [v]) None
            )
        end
      )
    }}}
      array٠unsafe_copy t1 t2 #i2
    {{{
      vs
    , RET ();
      ⌜length vs = sz1⌝ ∗
      Ψ sz1 vs None
    }}}.
  Proof.
    iIntros "% %Φ (#Hinv1 & #Hinv2 & HΨ & #H) HΦ".
    wp۰rec.
    wp۰apply+ (array٠size𑁒spec𑁒inv with "Hinv1") as "_".
    wp۰apply (array٠unsafe_copy_slice𑁒spec𑁒atomic Ψ with "[$HΨ]"); [lia.. | iSteps |].
    rewrite Nat2Z.id. iSteps.
  Qed.
  Lemma array٠unsafe_copy𑁒spec𑁒slice𑁒fit t1 dq1 vs1 t2 (i2 : Z) i2_ vs2 :
    i2 = ⁺i2_ →
    length vs1 = length vs2 →
    {{{
      array۰model t1 dq1 vs1 ∗
      array۰slice t2 i2_ (DfracOwn 1) vs2
    }}}
      array٠unsafe_copy t1 t2 #i2
    {{{
      RET ();
      array۰model t1 dq1 vs1 ∗
      array۰slice t2 i2_ (DfracOwn 1) vs1
    }}}.
  Proof.
    iIntros (-> ?) "%Φ (Hmodel1 & Hslice2) HΦ".
    wp۰rec.
    wp۰apply+ (array٠size𑁒spec with "Hmodel1") as "Hmodel1".
    iDestruct (array۰model𑁒to𑁒slice' with "Hmodel1") as "(Hslice1 & #?)".
    wp۰apply (array٠unsafe_copy_slice𑁒spec𑁒slice𑁒fit with "[$Hslice1 $Hslice2]"); [done.. |].
    iSteps.
  Qed.
  Lemma array٠unsafe_copy𑁒spec𑁒slice t1 dq1 vs1 t2 i2 (j2 : Z) vs2 :
    (i2 ≤ j2)%Z →
    (j2 + length vs1 ≤ i2 + length vs2)%Z →
    {{{
      array۰model t1 dq1 vs1 ∗
      array۰slice t2 i2 (DfracOwn 1) vs2
    }}}
      array٠unsafe_copy t1 t2 #j2
    {{{
      RET ();
      array۰model t1 dq1 vs1 ∗
      array۰slice t2 i2 (DfracOwn 1) (with_slice (₊j2 - i2) (length vs1) vs2 vs1)
    }}}.
  Proof.
    iIntros "% % %Φ (Hmodel1 & Hslice2) HΦ".
    wp۰rec.
    wp۰apply+ (array٠size𑁒spec with "Hmodel1") as "Hmodel1".
    iDestruct (array۰model𑁒to𑁒slice' with "Hmodel1") as "(Hslice1 & #?)".
    wp۰apply (array٠unsafe_copy_slice𑁒spec𑁒slice with "[$Hslice1 $Hslice2]"); [lia.. |].
    rewrite Nat2Z.id firstn_all /=. iSteps.
  Qed.
  Lemma array٠unsafe_copy𑁒spec t1 dq1 vs1 t2 (i2 : Z) vs2 :
    (0 ≤ i2)%Z →
    (i2 + length vs1 ≤ length vs2)%Z →
    {{{
      array۰model t1 dq1 vs1 ∗
      array۰model t2 (DfracOwn 1) vs2
    }}}
      array٠unsafe_copy t1 t2 #i2
    {{{
      RET ();
      array۰model t1 dq1 vs1 ∗
      array۰model t2 (DfracOwn 1) (with_slice ₊i2 (length vs1) vs2 vs1)
    }}}.
  Proof.
    iIntros "% % %Φ (Hmodel1 & Hmodel2) HΦ".
    wp۰rec.
    wp۰apply+ (array٠size𑁒spec with "Hmodel1") as "Hmodel1".
    wp۰apply (array٠unsafe_copy_slice𑁒spec with "[$Hmodel1 $Hmodel2]"); [lia.. |].
    rewrite Nat2Z.id firstn_all /=. iSteps.
  Qed.

  Lemma array٠copy𑁒spec𑁒slice𑁒fit t1 dq1 vs1 t2 sz2 (i2 : Z) i2_ vs2 :
    i2_ = ₊i2 →
    {{{
      array۰model t1 dq1 vs1 ∗
      array۰inv t2 sz2 ∗
      ( ⌜0 ≤ i2⌝%Z -∗
        ⌜i2 + length vs1 ≤ sz2⌝%Z -∗
          ⌜length vs1 = length vs2⌝ ∗
          array۰slice t2 i2_ (DfracOwn 1) vs2
      )
    }}}
      array٠copy t1 t2 #i2
    {{{
      RET ();
      ⌜0 ≤ i2⌝%Z ∗
      ⌜i2 + length vs1 ≤ sz2⌝%Z ∗
      array۰model t1 dq1 vs1 ∗
      array۰slice t2 i2_ (DfracOwn 1) vs1
    }}}.
  Proof.
    iIntros (->) "%Φ (Hmodel1 & #Hinv2 & H) HΦ".
    wp۰rec.
    wp۰apply+ assume𑁒spec' as "%".
    wp۰apply+ (array٠size𑁒spec𑁒inv with "Hinv2") as "_".
    wp۰apply+ (array٠size𑁒spec with "Hmodel1") as "Hmodel1".
    wp۰apply+ assume𑁒spec' as "%".
    iDestruct ("H" with "[//] [//]") as "(% & Hslice2)".
    wp۰apply+ (array٠unsafe_copy𑁒spec𑁒slice𑁒fit with "[$Hmodel1 $Hslice2]"); [lia.. |].
    iSteps.
  Qed.
  Lemma array٠copy𑁒spec𑁒slice t1 dq1 vs1 t2 sz2 i2 (j2 : Z) vs2 :
    {{{
      array۰model t1 dq1 vs1 ∗
      array۰inv t2 sz2 ∗
      ( ⌜0 ≤ j2⌝%Z -∗
        ⌜j2 + length vs1 ≤ sz2⌝%Z -∗
          ⌜i2 ≤ j2⌝%Z ∗
          ⌜j2 + length vs1 ≤ i2 + length vs2⌝%Z ∗
          array۰slice t2 i2 (DfracOwn 1) vs2
      )
    }}}
      array٠copy t1 t2 #j2
    {{{
      RET ();
      ⌜0 ≤ i2⌝ ∗
      ⌜i2 + length vs1 ≤ sz2⌝ ∗
      array۰model t1 dq1 vs1 ∗
      array۰slice t2 i2 (DfracOwn 1) (with_slice (₊j2 - i2) (length vs1) vs2 vs1)
    }}}.
  Proof.
    iIntros "%Φ (Hmodel1 & #Hinv2 & H) HΦ".
    wp۰rec.
    wp۰apply+ assume𑁒spec' as "%".
    wp۰apply+ (array٠size𑁒spec𑁒inv with "Hinv2") as "_".
    wp۰apply+ (array٠size𑁒spec with "Hmodel1") as "Hmodel1".
    wp۰apply+ assume𑁒spec' as "%".
    iDestruct ("H" with "[//] [//]") as "(% & % & Hslice2)".
    wp۰apply+ (array٠unsafe_copy𑁒spec𑁒slice with "[$Hmodel1 $Hslice2]"); [lia.. |].
    iSteps.
  Qed.
  Lemma array٠copy𑁒spec t1 dq1 vs1 t2 (i2 : Z) vs2 :
    {{{
      array۰model t1 dq1 vs1 ∗
      array۰model t2 (DfracOwn 1) vs2
    }}}
      array٠copy t1 t2 #i2
    {{{
      RET ();
      ⌜0 ≤ i2⌝%Z ∗
      ⌜i2 + length vs1 ≤ length vs2⌝%Z ∗
      array۰model t1 dq1 vs1 ∗
      array۰model t2 (DfracOwn 1) (with_slice ₊i2 (length vs1) vs2 vs1)
    }}}.
  Proof.
    iIntros "%Φ (Hmodel1 & Hmodel2) HΦ".
    wp۰rec.
    wp۰apply+ assume𑁒spec' as "%".
    wp۰apply+ (array٠size𑁒spec with "Hmodel2") as "Hmodel2".
    wp۰apply+ (array٠size𑁒spec with "Hmodel1") as "Hmodel1".
    wp۰apply+ assume𑁒spec' as "%".
    wp۰apply+ (array٠unsafe_copy𑁒spec with "[$Hmodel1 $Hmodel2]"); [lia.. |].
    iSteps.
  Qed.

  Lemma array٠unsafe_grow𑁒spec t dq vs sz' v' :
    (length vs ≤ sz')%Z →
    {{{
      array۰model t dq vs
    }}}
      array٠unsafe_grow t #sz' v'
    {{{
      t'
    , RET t';
      array۰model t dq vs ∗
      array۰model t' (DfracOwn 1) (vs ++ replicate (₊sz' - length vs) v')
    }}}.
  Proof.
    iIntros "%Hsz' %Φ Hmodel HΦ".
    wp۰rec.
    wp۰apply+ (array٠size𑁒spec with "Hmodel") as "Hmodel".
    wp۰apply+ (array٠unsafe_alloc𑁒spec with "[//]") as "%t' Hmodel'"; first lia.
    iDestruct (array۰model𑁒to𑁒slice' with "Hmodel'") as "(Hslice' & #?)".
    assert (₊sz' = length vs + ₊(sz' - length vs)) as -> by lia.
    rewrite replicate_add.
    iDestruct (array۰slice𑁒app with "Hslice'") as "(Hslice1' & Hslice2')".
    wp۰apply+ (array٠unsafe_copy𑁒spec𑁒slice with "[$Hmodel $Hslice1']") as "(Hmodel & Hslice1')"; first done.
    { simpl_length. }
    wp۰apply+ (array٠unsafe_fill_slice𑁒spec𑁒slice𑁒fit with "Hslice2'") as "Hslice2'".
    { simpl_length. }
    { simpl_length. }
    iDestruct (array۰slice𑁒app₁' with "Hslice1' Hslice2'") as "Hslice'".
    { simpl_length. lia. }
    iSteps.
    - iPureIntro. simpl_length. lia.
    - rewrite with_slice𑁒all; first simpl_length.
      rewrite Nat.add_sub' //.
  Qed.

  Lemma array٠grow𑁒spec t dq vs sz' v' :
    {{{
      array۰model t dq vs
    }}}
      array٠grow t #sz' v'
    {{{
      t'
    , RET t';
      ⌜length vs ≤ sz'⌝%Z ∗
      array۰model t dq vs ∗
      array۰model t' (DfracOwn 1) (vs ++ replicate (₊sz' - length vs) v')
    }}}.
  Proof.
    iIntros "%Φ Hmodel HΦ".
    wp۰rec.
    wp۰apply+ (array٠size𑁒spec with "Hmodel") as "Hmodel".
    wp۰apply+ assume𑁒spec' as "%".
    wp۰apply+ (array٠unsafe_grow𑁒spec with "Hmodel"); first done.
    iSteps.
  Qed.

  Lemma array٠unsafe_sub𑁒spec𑁒slice𑁒fit t dq vs (i : Z) i_ (n : Z) :
    i = ⁺i_ →
    n = length vs →
    {{{
      array۰slice t i_ dq vs
    }}}
      array٠unsafe_sub t #i #n
    {{{
      t'
    , RET t';
      array۰slice t i_ dq vs ∗
      array۰model t' (DfracOwn 1) (take ₊n vs)
    }}}.
  Proof.
    iIntros (-> ->) "%Φ Hslice HΦ".
    wp۰rec.
    wp۰apply+ (array٠unsafe_alloc𑁒spec with "[//]") as (t') "Hmodel'"; first lia.
    iDestruct (array۰model𑁒to𑁒slice' with "Hmodel'") as "(Hslice' & #?)".
    wp۰apply+ (array٠unsafe_copy_slice𑁒spec𑁒slice𑁒fit with "[$Hslice $Hslice']"); [done.. | |].
    { simpl_length. lia. }
    iSteps.
    - iPureIntro. simpl_length. lia.
    - rewrite firstn_all2 //. lia.
  Qed.
  Lemma array٠unsafe_sub𑁒spec𑁒slice t dq vs i (j n : Z) :
    (i ≤ j)%Z →
    (0 ≤ n)%Z →
    (j + n ≤ i + length vs)%Z →
    {{{
      array۰slice t i dq vs
    }}}
      array٠unsafe_sub t #j #n
    {{{
      t'
    , RET t';
      array۰slice t i dq vs ∗
      array۰model t' (DfracOwn 1) (take ₊n (drop (₊j - ₊i) vs))
    }}}.
  Proof.
    iIntros "% % % %Φ Hslice HΦ".
    Z_to_nat j. Z_to_nat n. rewrite !Nat2Z.id.
    rewrite (Nat.le_add_sub i j); first lia. set k := j - i.
    rewrite -{1 2}(take_drop k vs) -(take_drop n (drop k vs)).
    rewrite !drop_drop.
    iDestruct (array۰slice𑁒app𑁒3₂ with "Hslice") as "(Hslice1 & Hslice2 & Hslice3)"; first done.
    simpl_length. rewrite !Nat.min_l; [lia.. |].
    wp۰apply (array٠unsafe_sub𑁒spec𑁒slice𑁒fit with "Hslice2") as "%t' (Hslice2 & Hmodel')"; [simpl_length; lia.. |].
    iApply "HΦ".
    iDestruct (array۰slice𑁒app𑁒3₁ with "Hslice1 Hslice2 Hslice3") as "$"; [simpl_length; lia.. |].
    rewrite Nat2Z.id take_take Nat.min_id -Nat.le_add_sub //. lia.
  Qed.
  Lemma array٠unsafe_sub𑁒spec t dq vs (i n : Z) :
    (0 ≤ i)%Z →
    (0 ≤ n)%Z →
    (i + n ≤ length vs)%Z →
    {{{
      array۰model t dq vs
    }}}
      array٠unsafe_sub t #i #n
    {{{
      t'
    , RET t';
      array۰model t dq vs ∗
      array۰model t' (DfracOwn 1) (take ₊n (drop ₊i vs))
    }}}.
  Proof.
    iIntros "% % % %Φ Hmodel HΦ".
    iDestruct (array۰model𑁒to𑁒slice' with "Hmodel") as "(Hslice & #?)".
    wp۰apply (array٠unsafe_sub𑁒spec𑁒slice with "Hslice"); [done.. |].
    rewrite Nat.sub_0_r. iSteps.
  Qed.

  Lemma array٠sub𑁒spec𑁒slice𑁒fit t sz dq vs (i : Z) i_ (n : Z) :
    i_ = ₊i →
    {{{
      array۰inv t sz ∗
      ( ⌜0 ≤ i⌝%Z -∗
        ⌜0 ≤ n⌝%Z -∗
        ⌜i + n ≤ sz⌝%Z -∗
          ⌜₊n = length vs⌝ ∗
          array۰slice t i_ dq vs
      )
    }}}
      array٠sub t #i #n
    {{{
      t'
    , RET t';
      ⌜0 ≤ i⌝%Z ∗
      ⌜0 ≤ n⌝%Z ∗
      ⌜i + n ≤ sz⌝%Z ∗
      array۰slice t i_ dq vs ∗
      array۰model t' (DfracOwn 1) (take ₊n vs)
    }}}.
  Proof.
    iIntros (->) "%Φ (#Hinv & H) HΦ".
    wp۰rec.
    do 2 (wp۰apply+ assume𑁒spec' as "%").
    wp۰apply+ (array٠size𑁒spec𑁒inv with "Hinv") as "_".
    wp۰apply+ assume𑁒spec' as "%".
    iDestruct ("H" with "[//] [//] [//]") as "(% & Hslice)".
    wp۰apply+ (array٠unsafe_sub𑁒spec𑁒slice𑁒fit with "Hslice"); [lia.. |].
    iSteps.
  Qed.
  Lemma array٠sub𑁒spec𑁒slice t sz dq vs i (j n : Z) :
    {{{
      array۰inv t sz ∗
      ( ⌜0 ≤ j⌝%Z -∗
        ⌜0 ≤ n⌝%Z -∗
        ⌜j + n ≤ sz⌝%Z -∗
          ⌜i ≤ ₊j⌝ ∗
          ⌜₊j + ₊n ≤ i + length vs⌝ ∗
          array۰slice t i dq vs
      )
    }}}
      array٠sub t #j #n
    {{{
      t'
    , RET t';
      ⌜0 ≤ j⌝%Z ∗
      ⌜0 ≤ n⌝%Z ∗
      ⌜j + n ≤ sz⌝%Z ∗
      array۰slice t i dq vs ∗
      array۰model t' (DfracOwn 1) (take ₊n (drop (₊j - ₊i) vs))
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & H) HΦ".
    wp۰rec.
    do 2 (wp۰apply+ assume𑁒spec' as "%").
    wp۰apply+ (array٠size𑁒spec𑁒inv with "Hinv") as "_".
    wp۰apply+ assume𑁒spec' as "%".
    iDestruct ("H" with "[//] [//] [//]") as "(% & % & Hslice)".
    wp۰apply+ (array٠unsafe_sub𑁒spec𑁒slice with "Hslice"); [lia.. |].
    iSteps.
  Qed.
  Lemma array٠sub𑁒spec t dq vs (i n : Z) :
    {{{
      array۰model t dq vs
    }}}
      array٠sub t #i #n
    {{{
      t'
    , RET t';
      ⌜0 ≤ i⌝%Z ∗
      ⌜0 ≤ n⌝%Z ∗
      ⌜i + n ≤ length vs⌝%Z ∗
      array۰model t dq vs ∗
      array۰model t' (DfracOwn 1) (take ₊n (drop ₊i vs))
    }}}.
  Proof.
    iIntros "%Φ Hmodel HΦ".
    wp۰rec.
    do 2 (wp۰apply+ assume𑁒spec' as "%").
    wp۰apply+ (array٠size𑁒spec with "Hmodel") as "Hmodel".
    wp۰apply+ assume𑁒spec' as "%".
    wp۰apply+ (array٠unsafe_sub𑁒spec with "Hmodel"); [done.. |].
    iSteps.
  Qed.

  Lemma array٠unsafe_shrink𑁒spec t dq vs (n : Z) :
    (0 ≤ n ≤ length vs)%Z →
    {{{
      array۰model t dq vs
    }}}
      array٠unsafe_shrink t #n
    {{{
      t'
    , RET t';
      array۰model t dq vs ∗
      array۰model t' (DfracOwn 1) (take ₊n vs)
    }}}.
  Proof.
    iIntros "%Hn %Φ Hmodel HΦ".
    wp۰rec.
    wp۰apply+ (array٠unsafe_sub𑁒spec with "Hmodel"); [lia.. |].
    iSteps.
  Qed.

  Lemma array٠shrink𑁒spec t dq vs (n : Z) :
    {{{
      array۰model t dq vs
    }}}
      array٠shrink t #n
    {{{
      t'
    , RET t';
      ⌜0 ≤ n ≤ length vs⌝%Z ∗
      array۰model t dq vs ∗
      array۰model t' (DfracOwn 1) (take ₊n vs)
    }}}.
  Proof.
    iIntros "%Φ Hmodel HΦ".
    wp۰rec.
    wp۰apply+ assume𑁒spec' as "%".
    wp۰apply+ (array٠size𑁒spec with "Hmodel") as "Hmodel".
    wp۰apply+ assume𑁒spec' as "%".
    wp۰apply+ (array٠unsafe_shrink𑁒spec with "Hmodel"); first done.
    iSteps.
  Qed.

  Lemma array٠clone𑁒spec t dq vs :
    {{{
      array۰model t dq vs
    }}}
      array٠clone t
    {{{
      t'
    , RET t';
      array۰model t dq vs ∗
      array۰model t' (DfracOwn 1) vs
    }}}.
  Proof.
    iIntros "%Φ Hmodel HΦ".
    wp۰rec.
    wp۰apply (array٠size𑁒spec with "Hmodel") as "Hmodel".
    wp۰apply (array٠unsafe_shrink𑁒spec with "Hmodel") as "%t' (Hmodel & Hmodel')"; first lia.
    rewrite firstn_all2; first lia. iSteps.
  Qed.

  Lemma array٠unsafe_cget𑁒spec𑁒atomic t (j : Z) :
    <<<
      True
    | ∀∀ sz i dq vs v,
      ⌜(i ≤ j)%Z⌝ ∗
      ⌜vs !! (₊j - i) = Some v⌝ ∗
      array۰cslice t sz i dq vs
    >>>
      array٠unsafe_cget t #j
    <<<
      array۰cslice t sz i dq vs
    | RET v;
      £ 1
    >>>.
  Proof.
    iIntros "%Φ _ HΦ".

    wp۰rec.

    awp۰apply+ (array٠size𑁒spec𑁒atomic𑁒cslice with "[//]").
    iApply (aacc𑁒aupd𑁒abort with "HΦ"); first done. iIntros "%sz %i %dq %vs %v (% & % & Hcslice)".
    iAaccIntro with "Hcslice"; first iSteps. iIntros "$ !>". iStep. iIntros "HΦ !> (H£ & #Hinv) {%}".

    wp۰pures. wp۰rec. wp۰pures.

    iMod "HΦ" as "(%sz_ & %i & %dq & %vs & %v & (% & % & Hcslice) & _ & HΦ)".
    iDestruct (array𑁒inv𑁒cslice𑁒agree with "Hinv Hcslice") as %<-.
    rewrite /array۰cslice.
    iDestruct "Hcslice" as "(%l & -> & #Hheader & Hcslice)".
    iDestruct (chunk۰cslice𑁒lookup𑁒acc' j with "Hcslice") as "(H↦ & Hcslice)"; [done.. |].
    rewrite Z𑁒rem𑁒mod; [lia.. |].
    wp۰load.
    iApply ("HΦ" with "[H↦ Hcslice] H£").
    iSteps.
  Qed.
  Lemma array٠unsafe_cget𑁒spec𑁒atomic𑁒weak t (i : Z) :
    (0 ≤ i)%Z →
    <<<
      True
    | ∀∀ sz j dq vs,
      array۰cslice t sz j dq vs ∗
      ⌜0 < sz⌝ ∗
      ⌜length vs = sz⌝
    >>>
      array٠unsafe_cget t #i
    <<<
      array۰cslice t sz j dq vs
    | v,
      RET v;
      £ 1
    >>>.
  Proof.
    iIntros "%Hi %Φ _ HΦ".

    awp۰apply (array٠unsafe_cget𑁒spec𑁒atomic with "[//]").
    iApply (aacc𑁒aupd𑁒commit with "HΦ"); first done. iIntros "%sz %j %dq %vs (Hcslice & %Hsz & %Hvs)".
    iDestruct (array۰cslice𑁒rebase ₊i with "Hcslice") as "(%ws & %n & %Hws & Hcslice & Hcslice_rebase)"; [done.. |].
    destruct (lookup_lt_is_Some_2 ws 0) as (v & Hlookup).
    { rewrite Hws. simpl_length. lia. }
    iAaccIntro with "[$Hcslice]"; iSteps.
    rewrite Nat.sub_diag //.
  Qed.
  Lemma array٠unsafe_cget𑁒spec𑁒atomic𑁒cell t sz (i : Z) :
    <<<
      True
    | ∀∀ i_ dq v,
      ⌜i = ⁺i_⌝ ∗
      array۰cslice t sz i_ dq [v]
    >>>
      array٠unsafe_cget t #i
    <<<
      array۰cslice t sz i_ dq [v]
    | RET v;
      £ 1
    >>>.
  Proof.
    iIntros "%Φ _ HΦ".

    awp۰apply (array٠unsafe_cget𑁒spec𑁒atomic with "[//]").
    iApply (aacc𑁒aupd𑁒commit with "HΦ"); first done. iIntros "%i_ %dq %v (-> & Hcslice)".
    iAaccIntro with "[$Hcslice]"; iSteps.
    rewrite Nat2Z.id Nat.sub_diag //.
  Qed.
  Lemma array٠unsafe_cget𑁒spec k v t sz i dq vs (j : Z) :
    (i ≤ j)%Z →
    vs !! k = Some v →
    k = ₊j - i →
    {{{
      array۰cslice t sz i dq vs
    }}}
      array٠unsafe_cget t #j
    {{{
      RET v;
      array۰cslice t sz i dq vs
    }}}.
  Proof.
    iIntros (Hj Hlookup ->) "%Φ Hcslice HΦ".

    iApply wp𑁒fupd.
    awp۰apply (array٠unsafe_cget𑁒spec𑁒atomic with "[//]") without "HΦ".
    iAaccIntro with "[$Hcslice]". 1,2: iSteps. iIntros "Hcslice !> H£ HΦ".
    iApply (lc_fupd_elim_later with "H£ HΦ Hcslice").
  Qed.
  Lemma array٠unsafe_cget𑁒spec𑁒cell t sz (i : Z) i_ dq v :
    i = ⁺i_ →
    {{{
      array۰cslice t sz i_ dq [v]
    }}}
      array٠unsafe_cget t #i
    {{{
      RET v;
      array۰cslice t sz i_ dq [v]
    }}}.
  Proof.
    iIntros (->) "%Φ Hcslice HΦ".

    iApply wp𑁒fupd.
    awp۰apply (array٠unsafe_cget𑁒spec𑁒atomic𑁒cell with "[//]") without "HΦ".
    iAaccIntro with "[$Hcslice]". 1,2: iSteps. iIntros "Hcslice !> H£ HΦ".
    iApply (lc_fupd_elim_later with "H£ HΦ Hcslice").
  Qed.
  Lemma array٠unsafe_cget𑁒spec𑁒model v t dq vs (j : Z) :
    (0 ≤ j)%Z →
    vs !! (₊j `mod` length vs) = Some v →
    {{{
      array۰model t dq vs
    }}}
      array٠unsafe_cget t #j
    {{{
      RET v;
      array۰model t dq vs
    }}}.
  Proof.
    iIntros "% %Hlookup %Φ Hmodel HΦ".

    iDestruct (array۰model𑁒to𑁒inv with "Hmodel") as "#Hinv".
    iDestruct (array۰model𑁒lookup𑁒acc with "Hmodel") as "(Hslice & Hmodel)"; first done.
    iDestruct (array۰slice𑁒to𑁒cslice𑁒cell with "Hinv Hslice") as "Hcslice".
    wp۰apply (array٠unsafe_cget𑁒spec𑁒cell with "Hcslice") as "Hcslice"; first lia.
    iDestruct (array۰cslice𑁒to𑁒slice𑁒cell' with "Hcslice") as "Hslice".
    iSteps.
  Qed.

  Lemma array٠cget𑁒spec𑁒atomic t sz (j : Z) :
    <<<
      array۰inv t sz
    | ∀∀ dq vs i v,
      ⌜0 ≤ j⌝%Z -∗
      ⌜0 < sz⌝%Z -∗
        ⌜i ≤ ₊j⌝ ∗
        ⌜vs !! (₊j - i) = Some v⌝ ∗
        array۰cslice t sz i dq vs
    >>>
      array٠cget t #j
    <<<
      array۰cslice t sz i dq vs
    | RET v;
      ⌜0 ≤ j⌝%Z ∗
      ⌜0 < sz⌝%Z ∗
      £ 1
    >>>.
  Proof.
    iIntros "%Φ #Hinv HΦ".

    wp۰rec.
    wp۰apply+ assume𑁒spec' as "%".
    wp۰apply+ (array٠size𑁒spec𑁒inv with "Hinv") as "_".
    wp۰apply+ assume𑁒spec' as "%".

    awp۰apply+ (array٠unsafe_cget𑁒spec𑁒atomic with "[//]").
    iApply (aacc𑁒aupd𑁒commit with "HΦ"); first done. iIntros "%dq %vs %i %v H".
    iDestruct ("H" with "[//] [//]") as "(% & %Hlookup & Hcslice)".
    iAaccIntro with "[$Hcslice]". 1,3: iSteps.
    iIntros "(_ & _ & $)". iSteps.
  Qed.
  Lemma array٠cget𑁒spec𑁒atomic𑁒weak t sz (i : Z) :
    <<<
      array۰inv t sz
    | ∀∀ j dq vs,
      array۰cslice t sz j dq vs ∗
      ⌜length vs = sz⌝
    >>>
      array٠cget t #i
    <<<
      array۰cslice t sz j dq vs
    | v,
      RET v;
      £ 1
    >>>.
  Proof.
    iIntros "%Φ #Hinv HΦ".

    wp۰rec.
    wp۰apply+ assume𑁒spec' as "%".
    wp۰apply+ (array٠size𑁒spec𑁒inv with "Hinv") as "_".
    wp۰apply+ assume𑁒spec' as "%".

    awp۰apply+ (array٠unsafe_cget𑁒spec𑁒atomic𑁒weak with "[//]"); [lia.. |].
    iApply (aacc𑁒aupd𑁒commit with "HΦ"); first done. iIntros "%j %dq %vs (Hcslice & %)".
    iAaccIntro with "[$Hcslice]"; iSteps.
  Qed.
  Lemma array٠cget𑁒spec𑁒atomic𑁒cell t sz (i : Z) i_ :
    i_ = ₊i →
    <<<
      array۰inv t sz
    | ∀∀ dq v,
      ⌜0 ≤ i⌝%Z -∗
      ⌜0 < sz⌝%Z -∗
      array۰cslice t sz i_ dq [v]
    >>>
      array٠cget t #i
    <<<
      array۰cslice t sz i_ dq [v]
    | RET v;
      ⌜0 ≤ i⌝%Z ∗
      ⌜0 < sz⌝%Z ∗
      £ 1
    >>>.
  Proof.
    iIntros (->) "%Φ #Hinv HΦ".

    awp۰apply (array٠cget𑁒spec𑁒atomic with "Hinv").
    iApply (aacc𑁒aupd𑁒commit with "HΦ"); first done. iIntros "%dq %v H".
    iAaccIntro _, [v], ₊i with "[H]".
    { rewrite Nat.sub_diag. iSteps. }
    { iIntros "H !>". iSplitL; iSteps. }
    iSteps.
  Qed.
  Lemma array٠cget𑁒spec k v t sz i dq vs (j : Z) :
    {{{
      array۰inv t sz ∗
      ( ⌜0 < sz⌝ -∗
        ⌜0 ≤ j⌝%Z -∗
          ⌜i ≤ ₊j⌝ ∗
          ⌜vs !! k = Some v⌝ ∗
          ⌜k = ₊j - i⌝ ∗
          array۰cslice t sz i dq vs
      )
    }}}
      array٠cget t #j
    {{{
      RET v;
      ⌜0 < sz⌝ ∗
      ⌜0 ≤ j⌝%Z ∗
      array۰cslice t sz i dq vs
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & H) HΦ".

    wp۰rec.
    wp۰apply+ assume𑁒spec' as "%".
    wp۰apply+ (array٠size𑁒spec𑁒inv with "Hinv") as "_".
    wp۰apply+ assume𑁒spec' as "%".
    iDestruct ("H" with "[%] [//]") as "(% & %Hlookupk & -> & Hcslice)"; first lia.
    wp۰apply+ (array٠unsafe_cget𑁒spec with "Hcslice"); [lia | done.. |].
    iSteps.
  Qed.
  Lemma array٠cget𑁒spec𑁒cell t sz (i : Z) i_ dq v :
    i_ = ₊i →
    {{{
      array۰inv t sz ∗
      ( ⌜0 < sz⌝ -∗
        ⌜0 ≤ i⌝%Z -∗
        array۰cslice t sz i_ dq [v]
      )
    }}}
      array٠cget t #i
    {{{
      RET v;
      ⌜0 < sz⌝ ∗
      ⌜0 ≤ i⌝%Z ∗
      array۰cslice t sz i_ dq [v]
    }}}.
  Proof.
    iIntros (->) "%Φ (#Hinv & H) HΦ".

    wp۰apply (array٠cget𑁒spec 0 _ _ _ ₊i _ [_] with "[$Hinv H]"); iSteps.
  Qed.
  Lemma array٠cget𑁒spec𑁒model v t dq vs (j : Z) :
    vs !! (₊j `mod` length vs) = Some v →
    {{{
      array۰model t dq vs
    }}}
      array٠cget t #j
    {{{
      RET v;
      array۰model t dq vs
    }}}.
  Proof.
    iIntros "%Hlookup %Φ Hmodel HΦ".

    wp۰rec.
    wp۰apply+ assume𑁒spec' as "%".
    wp۰apply+ (array٠size𑁒spec with "Hmodel") as "Hmodel".
    wp۰apply+ assume𑁒spec' as "_".
    wp۰apply+ (array٠unsafe_cget𑁒spec𑁒model with "Hmodel HΦ"); done.
  Qed.

  Lemma array٠unsafe_cset𑁒spec𑁒atomic t (j : Z) v :
    <<<
      True
    | ∀∀ sz i vs,
      ⌜i ≤ j < i + length vs⌝%Z ∗
      array۰cslice t sz i (DfracOwn 1) vs
    >>>
      array٠unsafe_cset t #j v
    <<<
      array۰cslice t sz i (DfracOwn 1) (<[₊j - i := v]> vs)
    | RET ();
      £ 1
    >>>.
  Proof.
    iIntros "%Φ _ HΦ".

    wp۰rec.

    awp۰apply+ (array٠size𑁒spec𑁒atomic𑁒cslice with "[//]").
    iApply (aacc𑁒aupd𑁒abort with "HΦ"); first done. iIntros "%sz %i %vs (% & Hcslice)".
    iAaccIntro with "Hcslice"; first iSteps. iIntros "$ !>". iStep. iIntros "HΦ !> (H£ & #Hinv) {%}".

    wp۰pures. wp۰rec. wp۰pures.

    iMod "HΦ" as "(%sz_ & %i & %vs & (% & Hcslice) & _ & HΦ)".
    iDestruct (array𑁒inv𑁒cslice𑁒agree with "Hinv Hcslice") as %<-.
    rewrite /array۰cslice.
    iDestruct "Hcslice" as "(%l & -> & #Hheader & Hcslice)".
    iDestruct (chunk۰cslice𑁒update' j with "Hcslice") as "(H↦ & Hcslice)"; [lia | | done |].
    { destruct (nth_lookup_or_length vs (₊j - i) inhabitant); [done | lia]. }
    rewrite Z𑁒rem𑁒mod; [lia.. |].
    wp۰store.
    iApply ("HΦ" with "[H↦ Hcslice] H£").
    iSteps.
  Qed.
  Lemma array٠unsafe_cset𑁒spec𑁒atomic𑁒cell t sz (i : Z) v :
    <<<
      True
    | ∀∀ i_ w,
      ⌜i = ⁺i_⌝ ∗
      array۰cslice t sz i_ (DfracOwn 1) [w]
    >>>
      array٠unsafe_cset t #i v
    <<<
      array۰cslice t sz i_ (DfracOwn 1) [v]
    | RET ();
      £ 1
    >>>.
  Proof.
    iIntros "%Φ _ HΦ".

    awp۰apply (array٠unsafe_cset𑁒spec𑁒atomic with "[//]").
    iApply (aacc𑁒aupd𑁒commit with "HΦ"); first done. iIntros "%i_ %w (-> & Hcslice)".
    iAaccIntro with "[$Hcslice]". 1,2: iSteps.
    rewrite Nat2Z.id Nat.sub_diag. iSteps.
  Qed.
  Lemma array٠unsafe_cset𑁒spec t sz i vs (j : Z) v :
    (i ≤ j < i + length vs)%Z →
    {{{
      array۰cslice t sz i (DfracOwn 1) vs
    }}}
      array٠unsafe_cset t #j v
    {{{
      RET ();
      array۰cslice t sz i (DfracOwn 1) (<[₊j - i := v]> vs)
    }}}.
  Proof.
    iIntros "%Hj %Φ Hcslice HΦ".

    iApply wp𑁒fupd.
    awp۰apply (array٠unsafe_cset𑁒spec𑁒atomic with "[//]") without "HΦ".
    iAaccIntro with "[$Hcslice]". 1,2: iSteps. iIntros "Hcslice !> H£ HΦ".
    iApply (lc_fupd_elim_later with "H£ HΦ Hcslice").
  Qed.
  Lemma array٠unsafe_cset𑁒spec𑁒cell t sz (i : Z) i_ w v :
    i = ⁺i_ →
    {{{
      array۰cslice t sz i_ (DfracOwn 1) [w]
    }}}
      array٠unsafe_cset t #i v
    {{{
      RET ();
      array۰cslice t sz i_ (DfracOwn 1) [v]
    }}}.
  Proof.
    iIntros (->) "%Φ Hcslice HΦ".

    iApply wp𑁒fupd.
    awp۰apply (array٠unsafe_cset𑁒spec𑁒atomic𑁒cell with "[//]") without "HΦ".
    iAaccIntro with "[$Hcslice]". 1,2: iSteps. iIntros "Hcslice !> H£ HΦ".
    iApply (lc_fupd_elim_later with "H£ HΦ Hcslice").
  Qed.
  Lemma array٠unsafe_cset𑁒spec𑁒model t vs (j : Z) v :
    0 < length vs →
    (0 ≤ j)%Z →
    {{{
      array۰model t (DfracOwn 1) vs
    }}}
      array٠unsafe_cset t #j v
    {{{
      RET ();
      array۰model t (DfracOwn 1) (<[₊j `mod` length vs := v]> vs)
    }}}.
  Proof.
    iIntros "% % %Φ Hmodel HΦ".

    destruct (lookup_lt_is_Some_2 vs (₊j `mod` length vs)) as (w & Hlookup); first lia.
    iDestruct (array۰model𑁒update with "Hmodel") as "(#Hinv & Hslice & Hmodel)"; first done.
    iDestruct (array۰slice𑁒to𑁒cslice𑁒cell with "Hinv Hslice") as "Hcslice".
    wp۰apply (array٠unsafe_cset𑁒spec𑁒cell with "Hcslice") as "Hcslice"; first lia.
    iDestruct (array۰cslice𑁒to𑁒slice𑁒cell' with "Hcslice") as "Hslice".
    iSteps.
  Qed.

  Lemma array٠cset𑁒spec𑁒atomic t sz (j : Z) v :
    <<<
      array۰inv t sz
    | ∀∀ vs i,
      ⌜0 < sz⌝ -∗
      ⌜0 ≤ j⌝%Z -∗
        ⌜i ≤ ₊j < i + length vs⌝ ∗
        array۰cslice t sz i (DfracOwn 1) vs
    >>>
      array٠cset t #j v
    <<<
      array۰cslice t sz i (DfracOwn 1) (<[₊j - i := v]> vs)
    | RET ();
      ⌜0 < sz⌝ ∗
      ⌜0 ≤ j⌝%Z ∗
      £ 1
    >>>.
  Proof.
    iIntros "%Φ #Hinv HΦ".

    wp۰rec.
    wp۰apply+ assume𑁒spec' as "%".
    wp۰apply+ (array٠size𑁒spec𑁒inv with "Hinv") as "_".
    wp۰apply+ assume𑁒spec' as "%".

    awp۰apply+ (array٠unsafe_cset𑁒spec𑁒atomic with "[//]").
    iApply (aacc𑁒aupd𑁒commit with "HΦ"); first done. iIntros "%vs %i H".
    iDestruct ("H" with "[%] [//]") as "(% & Hcslice)"; first lia.
    iAaccIntro with "[$Hcslice]". 1,3: iSteps.
    iIntros "(_ & $)". iSteps.
  Qed.
  Lemma array٠cset𑁒spec𑁒atomic𑁒cell t sz (i : Z) i_ v :
    i_ = ₊i →
    <<<
      array۰inv t sz
    | ∀∀ w,
      ⌜0 < sz⌝ -∗
      ⌜0 ≤ i⌝%Z -∗
      array۰cslice t sz i_ (DfracOwn 1) [w]
    >>>
      array٠cset t #i v
    <<<
      array۰cslice t sz i_ (DfracOwn 1) [v]
    | RET ();
      ⌜0 < sz⌝ ∗
      ⌜0 ≤ i⌝%Z ∗
      £ 1
    >>>.
  Proof.
    iIntros (->) "%Φ #Hinv HΦ".

    awp۰apply (array٠cset𑁒spec𑁒atomic with "Hinv").
    iApply (aacc𑁒aupd𑁒commit with "HΦ"); first done. iIntros "%w Hcslice".
    iAaccIntro [w], ₊i with "[Hcslice]".
    { iSteps. }
    { iIntros "H !>". iSplitL; iSteps. }
    rewrite Nat.sub_diag. iSteps.
  Qed.
  Lemma array٠cset𑁒spec t sz i vs (j : Z) v :
    {{{
      array۰inv t sz ∗
      ( ⌜0 < sz⌝ -∗
        ⌜0 ≤ j⌝%Z -∗
          ⌜i ≤ ₊j < i + length vs⌝ ∗
          array۰cslice t sz i (DfracOwn 1) vs
      )
    }}}
      array٠cset t #j v
    {{{
      RET ();
      ⌜0 < sz⌝ ∗
      ⌜0 ≤ j⌝%Z ∗
      array۰cslice t sz i (DfracOwn 1) (<[₊j - i := v]> vs)
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & H) HΦ".

    wp۰rec.
    wp۰apply+ assume𑁒spec' as "%".
    wp۰apply+ (array٠size𑁒spec𑁒inv with "Hinv") as "_".
    wp۰apply+ assume𑁒spec' as "%".
    iDestruct ("H" with "[%] [//]") as "(% & Hcslice)"; first lia.
    wp۰apply+ (array٠unsafe_cset𑁒spec with "Hcslice"); first lia.
    iSteps.
  Qed.
  Lemma array٠cset𑁒spec𑁒cell t sz (i : Z) i_ w v :
    i_ = ₊i →
    {{{
      array۰inv t sz ∗
      ( ⌜0 < sz⌝ -∗
        ⌜0 ≤ i⌝%Z -∗
        array۰cslice t sz i_ (DfracOwn 1) [w]
      )
    }}}
      array٠cset t #i v
    {{{
      RET ();
      ⌜0 < sz⌝ ∗
      ⌜0 ≤ i⌝%Z ∗
      array۰cslice t sz i_ (DfracOwn 1) [v]
    }}}.
  Proof.
    iIntros (->) "%Φ (#Hinv & H) HΦ".

    wp۰apply (array٠cset𑁒spec _ _ ₊i [_] with "[$Hinv H]"); first iSteps.
    rewrite Nat.sub_diag //.
  Qed.
  Lemma array٠cset𑁒spec𑁒model t vs (j : Z) v :
    {{{
      array۰model t (DfracOwn 1) vs
    }}}
      array٠cset t #j v
    {{{
      RET ();
      array۰model t (DfracOwn 1) (<[₊j `mod` length vs := v]> vs)
    }}}.
  Proof.
    iIntros "%Φ Hmodel HΦ".

    wp۰rec.
    wp۰apply+ assume𑁒spec' as "%".
    wp۰apply+ (array٠size𑁒spec with "Hmodel") as "Hmodel".
    wp۰apply+ assume𑁒spec' as "%".
    wp۰apply+ (array٠unsafe_cset𑁒spec𑁒model with "Hmodel HΦ"); lia.
  Qed.

  #[local] Lemma array٠unsafe_ccopy_slice₀𑁒spec t1 (i1 : Z) i1_ dq1 vs1 t2 sz2 (i2 : Z) i2_ vs2 (n : Z) :
    0 < sz2 →
    i1 = ⁺i1_ →
    i2 = ⁺i2_ →
    n = length vs1 →
    length vs1 = length vs2 →
    {{{
      array۰slice t1 i1_ dq1 vs1 ∗
      array۰cslice t2 sz2 i2_ (DfracOwn 1) vs2
    }}}
      array٠unsafe_ccopy_slice₀ t1 #i1 t2 #i2 #n
    {{{
      RET ();
      array۰slice t1 i1_ dq1 vs1 ∗
      array۰cslice t2 sz2 i2_ (DfracOwn 1) vs1
    }}}.
  Proof.
    iIntros (Hsz2 -> -> ? ?) "%Φ (Hslice1 & Hcslice2) HΦ".
    iDestruct (array۰cslice𑁒length with "Hcslice2") as %Hvs2; first done.

    wp۰rec.
    wp۰apply+ (array٠size𑁒spec𑁒cslice with "Hcslice2") as "Hcslice2".
    wp۰pures.
    rewrite Z.rem_mod_nonneg; [lia.. |].
    rewrite !array۰cslice𑁒to𑁒slice; [simpl_length; lia.. |].
    iDestruct "Hcslice2" as "(#Hinv2 & Hslice21 & Hslice22)".
    case_bool_decide as Hif; wp۰pures.

    - wp۰apply (array٠unsafe_copy_slice𑁒spec𑁒slice𑁒fit with "[$Hslice1 $Hslice21]") as "(Hslice1 & Hslice21)"; [simpl_length; lia.. |].
      rewrite firstn_all2; first lia.
      rewrite skipn_all2; first lia.
      iSteps.
      iApply (array۰slice𑁒nil with "Hslice22").

    - wp۰apply (array٠unsafe_copy_slice𑁒spec𑁒slice𑁒fit𑁒dst with "[$Hslice1 $Hslice21]") as "(Hslice1 & Hslice21)"; [simpl_length; lia.. |].
      iEval (rewrite Nat2Z.id Nat.sub_diag slice𑁒0 -Nat2Z.inj_mod -Nat2Z.inj_sub; first lia) in "Hslice21".
      iEval (rewrite Nat2Z.id) in "Hslice21".
      wp۰apply+ (array٠unsafe_copy_slice𑁒spec𑁒slice𑁒fit𑁒dst with "[$Hslice1 $Hslice22]") as "(Hslice1 & Hslice22)"; [simpl_length; lia.. |].
      iEval (rewrite -Nat2Z.inj_mod -Nat2Z.inj_sub; first lia) in "Hslice22".
      iEval (rewrite -Nat2Z.inj_add Nat2Z.id Nat.add_sub') in "Hslice22".
      iEval (rewrite /slice firstn_all2; first (simpl_length; lia)) in "Hslice22".
      iSteps.
  Qed.
  Lemma array٠unsafe_ccopy_slice𑁒spec𑁒fit t1 sz1 (i1 : Z) i1_ dq1 vs1 t2 sz2 (i2 : Z) i2_ vs2 (n : Z) :
    0 < sz1 →
    length vs1 ≤ sz1 →
    0 < sz2 →
    i1 = ⁺i1_ →
    i2 = ⁺i2_ →
    n = length vs1 →
    length vs1 = length vs2 →
    {{{
      array۰cslice t1 sz1 i1_ dq1 vs1 ∗
      array۰cslice t2 sz2 i2_ (DfracOwn 1) vs2
    }}}
      array٠unsafe_ccopy_slice t1 #i1 t2 #i2 #n
    {{{
      RET ();
      array۰cslice t1 sz1 i1_ dq1 vs1 ∗
      array۰cslice t2 sz2 i2_ (DfracOwn 1) vs1
    }}}.
  Proof.
    iIntros (Hsz1 Hvs1 Hsz2 -> -> -> ?) "%Φ (Hcslice1 & Hcslice2) HΦ".

    wp۰rec.
    wp۰apply+ (array٠size𑁒spec𑁒cslice with "Hcslice1") as "Hcslice1".
    wp۰pures.
    rewrite Z.rem_mod_nonneg; [lia.. |].
    rewrite (array۰cslice𑁒to𑁒slice t1) //.
    iDestruct "Hcslice1" as "(#Hinv2 & Hslice11 & Hslice12)".
    case_bool_decide as Hif; wp۰pures.

    - wp۰apply (array٠unsafe_ccopy_slice₀𑁒spec with "[$Hslice11 $Hcslice2]") as "(Hslice11 & Hcslice2)"; [simpl_length; lia.. |].
      rewrite firstn_all2; first lia.
      iSteps.

    - rewrite -(take_drop (sz1 - i1_ `mod` sz1) vs2).
      iDestruct (array۰cslice𑁒app₂ with "Hcslice2") as "(Hcslice21 & Hcslice22)"; first done.
      wp۰apply (array٠unsafe_ccopy_slice₀𑁒spec with "[$Hslice11 $Hcslice21]") as "(Hslice11 & Hcslice21)"; [simpl_length; lia.. |].
      wp۰apply+ (array٠unsafe_ccopy_slice₀𑁒spec with "[$Hslice12 $Hcslice22]") as "(Hslice12 & Hcslice22)"; [simpl_length; lia.. |].
      iDestruct (array۰cslice𑁒app₁ with "Hcslice21 Hcslice22") as "Hcslice2".
      { simpl_length. lia. }
      iEval (rewrite take_drop) in "Hcslice2".
      iSteps.
  Qed.
  Lemma array٠unsafe_ccopy_slice𑁒spec𑁒fit𑁒src t1 sz1 (i1 : Z) i1_ dq1 vs1 t2 sz2 i2 (j2 : Z) vs2 (n : Z) :
    0 < sz1 →
    length vs1 ≤ sz1 →
    0 < sz2 →
    i1 = ⁺i1_ →
    (i2 ≤ j2)%Z →
    n = length vs1 →
    (j2 + n ≤ i2 + length vs2)%Z →
    {{{
      array۰cslice t1 sz1 i1_ dq1 vs1 ∗
      array۰cslice t2 sz2 i2 (DfracOwn 1) vs2
    }}}
      array٠unsafe_ccopy_slice t1 #i1 t2 #j2 #n
    {{{
      RET ();
      array۰cslice t1 sz1 i1_ dq1 vs1 ∗
      array۰cslice t2 sz2 i2 (DfracOwn 1) (with_slice (₊j2 - i2) ₊n vs2 vs1)
    }}}.
  Proof.
    iIntros (Hsz1 Hvs1 Hsz2 -> ? ? ?) "%Φ (Hcslice1 & Hcslice2) HΦ".
    Z_to_nat j2. rewrite Nat2Z.id.
    rewrite (Nat.le_add_sub i2 j2); first lia. set k2 := j2 - i2.
    rewrite -{1}(take_drop k2 vs2) -(take_drop ₊n (drop k2 vs2)) drop_drop.
    iDestruct (array۰cslice𑁒app𑁒3₂ with "Hcslice2") as "(Hcslice21 & Hcslice22 & Hcslice23)"; first done.
    simpl_length. rewrite !Nat.min_l; [lia.. |].
    wp۰apply (array٠unsafe_ccopy_slice𑁒spec𑁒fit with "[$Hcslice1 $Hcslice22]") as "(Hcslice1 & Hcslice22)"; [simpl_length; lia.. |].
    iApply "HΦ".
    iDestruct (array۰cslice𑁒app𑁒3₁ with "Hcslice21 Hcslice22 Hcslice23") as "Hcslice2"; [simpl_length; lia.. |].
    rewrite -Nat.le_add_sub; first lia.
    iSteps.
  Qed.
  Lemma array٠unsafe_ccopy_slice𑁒spec𑁒fit𑁒dst t1 sz1 i1 (j1 : Z) dq1 vs1 t2 sz2 (i2 : Z) i2_ vs2 (n : Z) :
    0 < sz1 →
    length vs1 ≤ sz1 →
    0 < sz2 →
    (i1 ≤ j1)%Z →
    i2 = ⁺i2_ →
    n = length vs2 →
    (j1 + n ≤ i1 + length vs1)%Z →
    {{{
      array۰cslice t1 sz1 i1 dq1 vs1 ∗
      array۰cslice t2 sz2 i2_ (DfracOwn 1) vs2
    }}}
      array٠unsafe_ccopy_slice t1 #j1 t2 #i2 #n
    {{{
      RET ();
      array۰cslice t1 sz1 i1 dq1 vs1 ∗
      array۰cslice t2 sz2 i2_ (DfracOwn 1) (slice (₊j1 - i1) ₊n vs1)
    }}}.
  Proof.
    iIntros (Hsz1 Hvs1 Hsz2 ? -> ? ?) "%Φ (Hcslice1 & Hcslice2) HΦ".
    Z_to_nat j1. rewrite Nat2Z.id.
    rewrite (Nat.le_add_sub i1 j1); first lia. set k1 := j1 - i1.
    rewrite -{1 2}(take_drop k1 vs1) -(take_drop ₊n (drop k1 vs1)) drop_drop.
    iDestruct (array۰cslice𑁒app𑁒3₂ with "Hcslice1") as "(Hcslice11 & Hcslice12 & Hcslice13)"; first done.
    simpl_length. rewrite !Nat.min_l; [lia.. |].
    wp۰apply (array٠unsafe_ccopy_slice𑁒spec𑁒fit with "[$Hcslice12 $Hcslice2]") as "(Hcslice12 & Hcslice2)"; [simpl_length; lia.. |].
    iApply "HΦ".
    iDestruct (array۰cslice𑁒app𑁒3₁ with "Hcslice11 Hcslice12 Hcslice13") as "$"; [simpl_length; lia.. |].
    rewrite -Nat.le_add_sub //; first lia.
  Qed.
  Lemma array٠unsafe_ccopy_slice𑁒spec t1 sz1 i1 (j1 : Z) dq1 vs1 t2 sz2 i2 (j2 : Z) vs2 (n : Z) :
    0 < sz1 →
    length vs1 ≤ sz1 →
    0 < sz2 →
    (i1 ≤ j1)%Z →
    (i2 ≤ j2)%Z →
    (0 ≤ n)%Z →
    (j1 + n ≤ i1 + length vs1)%Z →
    (j2 + n ≤ i2 + length vs2)%Z →
    {{{
      array۰cslice t1 sz1 i1 dq1 vs1 ∗
      array۰cslice t2 sz2 i2 (DfracOwn 1) vs2
    }}}
      array٠unsafe_ccopy_slice t1 #j1 t2 #j2 #n
    {{{
      RET ();
      array۰cslice t1 sz1 i1 dq1 vs1 ∗
      array۰cslice t2 sz2 i2 (DfracOwn 1) (with_slice (₊j2 - i2) ₊n vs2 (take ₊n (drop (₊j1 - i1) vs1)))
    }}}.
  Proof.
    iIntros "%Hsz1 %Hvs1 %Hsz2 % % %Hn % % %Φ (Hcslice1 & Hcslice2) HΦ".
    Z_to_nat j2. rewrite Nat2Z.id.
    rewrite (Nat.le_add_sub i2 j2); first lia. set k2 := j2 - i2.
    rewrite -{1}(take_drop k2 vs2) -(take_drop ₊n (drop k2 vs2)) drop_drop.
    iDestruct (array۰cslice𑁒app𑁒3₂ with "Hcslice2") as "(Hcslice21 & Hcslice22 & Hcslice23)"; first done.
    simpl_length. rewrite !Nat.min_l; [lia.. |].
    wp۰apply (array٠unsafe_ccopy_slice𑁒spec𑁒fit𑁒dst with "[$Hcslice1 $Hcslice22]") as "(Hcslice1 & Hcslice22)"; [simpl_length; lia.. |].
    iApply "HΦ".
    iDestruct (array۰cslice𑁒app𑁒3₁ with "Hcslice21 Hcslice22 Hcslice23") as "Hcslice2"; [simpl_length; lia.. |].
    rewrite -Nat.le_add_sub; first lia.
    iSteps.
  Qed.

  Lemma array٠ccopy_slice𑁒spec𑁒fit t1 sz1 (i1 : Z) i1_ dq1 vs1 t2 sz2 (i2 : Z) i2_ vs2 (n : Z) :
    i1_ = ₊i1 →
    i2_ = ₊i2 →
    {{{
      array۰inv t1 sz1 ∗
      array۰inv t2 sz2 ∗
      ( ⌜0 < sz1⌝ -∗
        ⌜0 < sz2⌝ -∗
        ⌜0 ≤ i1⌝%Z -∗
        ⌜0 ≤ i2⌝%Z -∗
        ⌜0 ≤ n⌝%Z -∗
        ⌜n ≤ sz1⌝%Z -∗
        ⌜n ≤ sz2⌝%Z -∗
          ⌜₊n = length vs1⌝ ∗
          ⌜length vs1 = length vs2⌝ ∗
          array۰cslice t1 sz1 i1_ dq1 vs1 ∗
          array۰cslice t2 sz2 i2_ (DfracOwn 1) vs2
      )
    }}}
      array٠ccopy_slice t1 #i1 t2 #i2 #n
    {{{
      RET ();
      ⌜0 < sz1⌝ ∗
      ⌜0 < sz2⌝ ∗
      ⌜0 ≤ i1⌝%Z ∗
      ⌜0 ≤ i2⌝%Z ∗
      ⌜0 ≤ n⌝%Z ∗
      ⌜n ≤ sz1⌝%Z ∗
      ⌜n ≤ sz2⌝%Z ∗
      array۰cslice t1 sz1 i1_ dq1 vs1 ∗
      array۰cslice t2 sz2 i2_ (DfracOwn 1) vs1
    }}}.
  Proof.
    iIntros (-> ->) "%Φ (#Hinv1 & #Hinv2 & H) HΦ".
    wp۰rec.
    do 3 wp۰apply+ assume𑁒spec' as "%".
    wp۰apply+ (array٠size𑁒spec𑁒inv with "Hinv1") as "_".
    wp۰apply+ (array٠size𑁒spec𑁒inv with "Hinv2") as "_".
    do 4 (wp۰apply+ assume𑁒spec' as "%").
    iDestruct ("H" with "[%] [%] [//] [//] [//] [//] [//]") as "(% & % & Hcslice1 & Hcslice2)"; [lia.. |].
    wp۰apply+ (array٠unsafe_ccopy_slice𑁒spec𑁒fit with "[$Hcslice1 $Hcslice2]"); [lia.. |].
    iSteps.
  Qed.
  Lemma array٠ccopy_slice𑁒spec t1 sz1 i1 (j1 : Z) dq1 vs1 t2 sz2 i2 (j2 : Z) vs2 (n : Z) :
    {{{
      array۰inv t1 sz1 ∗
      array۰inv t2 sz2 ∗
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
          array۰cslice t1 sz1 i1 dq1 vs1 ∗
          array۰cslice t2 sz2 i2 (DfracOwn 1) vs2
      )
    }}}
      array٠ccopy_slice t1 #j1 t2 #j2 #n
    {{{
      RET ();
      ⌜0 < sz1⌝ ∗
      ⌜0 < sz2⌝ ∗
      ⌜0 ≤ j1⌝%Z ∗
      ⌜0 ≤ j2⌝%Z ∗
      ⌜0 ≤ n⌝%Z ∗
      ⌜n ≤ sz1⌝%Z ∗
      ⌜n ≤ sz2⌝%Z ∗
      array۰cslice t1 sz1 i1 dq1 vs1 ∗
      array۰cslice t2 sz2 i2 (DfracOwn 1) (with_slice (₊j2 - i2) ₊n vs2 (take ₊n (drop (₊j1 - i1) vs1)))
    }}}.
  Proof.
    iIntros "%Φ (#Hinv1 & #Hinv2 & H) HΦ".
    wp۰rec.
    do 3 wp۰apply+ assume𑁒spec' as "%".
    wp۰apply+ (array٠size𑁒spec𑁒inv with "Hinv1") as "_".
    wp۰apply+ (array٠size𑁒spec𑁒inv with "Hinv2") as "_".
    do 4 (wp۰apply+ assume𑁒spec' as "%").
    iDestruct ("H" with "[%] [%] [//] [//] [//] [//] [//]") as "(% & % & % & % & % & Hslice1 & Hslice2)"; [lia.. |].
    wp۰apply+ (array٠unsafe_ccopy_slice𑁒spec with "[$Hslice1 $Hslice2]"); [lia.. |].
    iSteps.
  Qed.

  Lemma array٠unsafe_ccopy𑁒spec𑁒fit t1 sz1 (i1 : Z) i1_ dq1 vs1 t2 sz2 (i2 : Z) i2_ vs2 :
    0 < sz1 →
    0 < sz2 →
    i1 = ⁺i1_ →
    i2 = ⁺i2_ →
    length vs1 = sz1 →
    length vs1 = length vs2 →
    {{{
      array۰cslice t1 sz1 i1_ dq1 vs1 ∗
      array۰cslice t2 sz2 i2_ (DfracOwn 1) vs2
    }}}
      array٠unsafe_ccopy t1 #i1 t2 #i2
    {{{
      RET ();
      array۰cslice t1 sz1 i1_ dq1 vs1 ∗
      array۰cslice t2 sz2 i2_ (DfracOwn 1) vs1
    }}}.
  Proof.
    iIntros (Hsz1 Hsz2 -> -> ? ?) "%Φ (Hcslice1 & Hcslice2) HΦ".
    wp۰rec.
    wp۰apply+ (array٠size𑁒spec𑁒cslice with "Hcslice1") as "Hcslice1".
    wp۰apply (array٠unsafe_ccopy_slice𑁒spec𑁒fit with "[$Hcslice1 $Hcslice2]"); [lia.. |].
    iSteps.
  Qed.
  Lemma array٠unsafe_ccopy𑁒spec t1 sz1 (i1 : Z) i1_ dq1 vs1 t2 sz2 i2 (j2 : Z) vs2 :
    0 < sz1 →
    0 < sz2 →
    i1 = ⁺i1_ →
    length vs1 = sz1 →
    (i2 ≤ j2)%Z →
    (j2 + length vs1 ≤ i2 + length vs2)%Z →
    {{{
      array۰cslice t1 sz1 i1_ dq1 vs1 ∗
      array۰cslice t2 sz2 i2 (DfracOwn 1) vs2
    }}}
      array٠unsafe_ccopy t1 #i1 t2 #j2
    {{{
      RET ();
      array۰cslice t1 sz1 i1_ dq1 vs1 ∗
      array۰cslice t2 sz2 i2 (DfracOwn 1) (with_slice (₊j2 - i2) (length vs1) vs2 vs1)
    }}}.
  Proof.
    iIntros (Hsz1 Hsz2 -> Hvs1 ? ?) "%Φ (Hcslice1 & Hcslice2) HΦ".
    wp۰rec.
    wp۰apply+ (array٠size𑁒spec𑁒cslice with "Hcslice1") as "Hcslice1".
    wp۰apply (array٠unsafe_ccopy_slice𑁒spec with "[$Hcslice1 $Hcslice2]"); [lia.. |].
    rewrite !Nat2Z.id Nat.sub_diag -Hvs1 firstn_all //.
  Qed.

  Lemma array٠ccopy𑁒spec𑁒fit t1 sz1 (i1 : Z) i1_ dq1 vs1 t2 sz2 (i2 : Z) i2_ vs2 :
    i1_ = ₊i1 →
    i2_ = ₊i2 →
    length vs1 = sz1 →
    length vs1 = length vs2 →
    {{{
      array۰inv t1 sz1 ∗
      array۰inv t2 sz2 ∗
      ( ⌜0 < sz1⌝ -∗
        ⌜0 < sz2⌝ -∗
        ⌜0 ≤ i1⌝%Z -∗
        ⌜0 ≤ i2⌝%Z -∗
          array۰cslice t1 sz1 i1_ dq1 vs1 ∗
          array۰cslice t2 sz2 i2_ (DfracOwn 1) vs2
      )
    }}}
      array٠ccopy t1 #i1 t2 #i2
    {{{
      RET ();
      ⌜0 < sz1⌝ ∗
      ⌜0 < sz2⌝ ∗
      ⌜0 ≤ i1⌝%Z ∗
      ⌜0 ≤ i2⌝%Z ∗
      array۰cslice t1 sz1 i1_ dq1 vs1 ∗
      array۰cslice t2 sz2 i2_ (DfracOwn 1) vs1
    }}}.
  Proof.
    iIntros (-> ->) "% % %Φ (#Hinv1 & #Hinv2 & H) HΦ".
    wp۰rec.
    do 2 (wp۰apply+ assume𑁒spec' as "%").
    wp۰apply+ (array٠size𑁒spec𑁒inv with "Hinv1") as "_".
    wp۰apply+ (array٠size𑁒spec𑁒inv with "Hinv2") as "_".
    do 2 (wp۰apply+ assume𑁒spec' as "%").
    iDestruct ("H" with "[%] [%] [//] [//]") as "(Hcslice1 & Hcslice2)"; [lia.. |].
    wp۰apply+ (array٠unsafe_ccopy𑁒spec𑁒fit with "[$Hcslice1 $Hcslice2]"); [lia.. |].
    iSteps.
  Qed.
  Lemma array٠ccopy𑁒spec t1 sz1 (i1 : Z) dq1 vs1 t2 sz2 i2 (j2 : Z) vs2 :
    length vs1 = sz1 →
    {{{
      array۰inv t1 sz1 ∗
      array۰inv t2 sz2 ∗
      ( ⌜0 < sz1⌝ -∗
        ⌜0 < sz2⌝ -∗
        ⌜0 ≤ i1⌝%Z -∗
        ⌜0 ≤ j2⌝%Z -∗
          ⌜i2 ≤ ₊j2⌝%Z ∗
          ⌜₊j2 + length vs1 ≤ i2 + length vs2⌝%Z ∗
          array۰cslice t1 sz1 ₊i1 dq1 vs1 ∗
          array۰cslice t2 sz2 i2 (DfracOwn 1) vs2
      )
    }}}
      array٠ccopy t1 #i1 t2 #j2
    {{{
      RET ();
      ⌜0 < sz1⌝ ∗
      ⌜0 < sz2⌝ ∗
      ⌜0 ≤ i1⌝%Z ∗
      ⌜0 ≤ j2⌝%Z ∗
      array۰cslice t1 sz1 ₊i1 dq1 vs1 ∗
      array۰cslice t2 sz2 i2 (DfracOwn 1) (with_slice (₊j2 - i2) (length vs1) vs2 vs1)
    }}}.
  Proof.
    iIntros "% %Φ (#Hinv1 & #Hinv2 & H) HΦ".
    wp۰rec.
    do 2 (wp۰apply+ assume𑁒spec' as "%").
    wp۰apply+ (array٠size𑁒spec𑁒inv with "Hinv1") as "_".
    wp۰apply+ (array٠size𑁒spec𑁒inv with "Hinv2") as "_".
    do 2 (wp۰apply+ assume𑁒spec' as "%").
    iDestruct ("H" with "[%] [%] [//] [//]") as "(% & % & Hcslice1 & Hcslice2)"; [lia.. |].
    wp۰apply+ (array٠unsafe_ccopy𑁒spec with "[$Hcslice1 $Hcslice2]"); [lia.. |].
    iSteps.
  Qed.

  Lemma array٠unsafe_cgrow_slice𑁒spec t sz (i : Z) i_ dq vs (n : Z) sz' v :
    0 < sz →
    length vs ≤ sz →
    i = ⁺i_ →
    n = ⁺(length vs) →
    (0 < sz')%Z →
    (n ≤ sz')%Z →
    {{{
      array۰cslice t sz i_ dq vs
    }}}
      array٠unsafe_cgrow_slice t #i #n #sz' v
    {{{
      t'
    , RET t';
      array۰cslice t sz i_ dq vs ∗
      array۰cslice t' ₊sz' i_ (DfracOwn 1) (vs ++ replicate (₊sz' - ₊n) v)
    }}}.
  Proof.
    iIntros (Hsz Hvs -> -> Hsz' ?) "%Φ Hcslice HΦ".

    wp۰rec.
    wp۰apply+ (array٠unsafe_make𑁒spec with "[//]") as (t') "Hmodel'"; first lia.
    iDestruct (array۰model𑁒to𑁒cslice with "Hmodel'") as "Hcslice'". simpl_length.
    iDestruct (array۰cslice𑁒rotation𑁒right𑁒0 i_ with "Hcslice'") as "Hcslice'"; [lia | simpl_length |].
    rewrite rotation𑁒replicate.
    wp۰apply+ (array٠unsafe_ccopy_slice𑁒spec with "[$Hcslice $Hcslice']") as "(Hcslice & Hcslice')"; [simpl_length; lia.. |].
    rewrite !Nat2Z.id Nat.sub_diag firstn_all with_slice𑁒0 drop_replicate.
    iSteps.
  Qed.

  Lemma array٠unsafe_cgrow𑁒spec t (sz : nat) (i : Z) i_ dq vs sz' v :
    0 < sz →
    i = ⁺i_ →
    length vs = sz →
    (0 < sz')%Z →
    (sz ≤ sz')%Z →
    {{{
      array۰cslice t sz i_ dq vs
    }}}
      array٠unsafe_cgrow t #i #sz' v
    {{{
      t'
    , RET t';
      array۰cslice t sz i_ dq vs ∗
      array۰cslice t' ₊sz' i_ (DfracOwn 1) (vs ++ replicate (₊sz' - sz) v)
    }}}.
  Proof.
    iIntros (Hsz -> Hvs Hsz' ?) "%Φ Hcslice HΦ".

    wp۰rec.
    wp۰apply+ (array٠size𑁒spec𑁒cslice with "Hcslice") as "Hcslice".
    wp۰apply (array٠unsafe_cgrow_slice𑁒spec with "Hcslice") as (t') "(Hcslice & Hcslice')"; [lia.. |].
    rewrite Nat2Z.id. iSteps.
  Qed.

  Lemma array٠unsafe_cshrink_slice𑁒spec𑁒fit t sz (i : Z) i_ dq vs sz' :
    0 < sz →
    length vs ≤ sz →
    i = ⁺i_ →
    (0 < sz' ≤ length vs)%Z →
    {{{
      array۰cslice t sz i_ dq vs
    }}}
      array٠unsafe_cshrink_slice t #i #sz'
    {{{
      t'
    , RET t';
      array۰cslice t sz i_ dq vs ∗
      array۰cslice t' ₊sz' i_ (DfracOwn 1) (take ₊sz' vs)
    }}}.
  Proof.
    iIntros (Hsz Hvs -> ?) "%Φ Hcslice HΦ".

    wp۰rec.
    wp۰apply+ (array٠unsafe_alloc𑁒spec with "[//]") as (t') "Hmodel'"; first lia.
    iDestruct (array۰model𑁒to𑁒cslice with "Hmodel'") as "Hcslice'". simpl_length.
    iDestruct (array۰cslice𑁒rotation𑁒right𑁒0 i_ with "Hcslice'") as "Hcslice'"; [lia | simpl_length |].
    rewrite rotation𑁒replicate.
    wp۰apply+ (array٠unsafe_ccopy_slice𑁒spec with "[$Hcslice $Hcslice']") as "(Hcslice & Hcslice')"; [simpl_length; lia.. |].
    rewrite Nat2Z.id Nat.sub_diag with_slice𑁒0 drop_replicate Nat.sub_diag right_id.
    iSteps.
  Qed.
  Lemma array٠unsafe_cshrink_slice𑁒spec t sz i dq vs (j : Z) sz' :
    0 < sz →
    length vs ≤ sz →
    (i ≤ j)%Z →
    (0 < sz')%Z →
    (j + sz' ≤ i + length vs)%Z →
    {{{
      array۰cslice t sz i dq vs
    }}}
      array٠unsafe_cshrink_slice t #j #sz'
    {{{
      t'
    , RET t';
      array۰cslice t sz i dq vs ∗
      array۰cslice t' ₊sz' ₊j (DfracOwn 1) (slice (₊j - i) ₊sz' vs)
    }}}.
  Proof.
    iIntros "%Hsz %Hvs % %Hsz' % %Φ Hcslice HΦ".

    rewrite (Nat.le_add_sub i ₊j); first lia. set k := ₊j - i.
    rewrite -{1 2}(take_drop k vs) -(take_drop ₊sz' (drop k vs)).
    rewrite !drop_drop.
    iDestruct (array۰cslice𑁒app𑁒3₂ with "Hcslice") as "(Hcslice1 & Hcslice2 & Hcslice3)"; first done.
    simpl_length. rewrite !Nat.min_l; [lia.. |].
    wp۰apply (array٠unsafe_cshrink_slice𑁒spec𑁒fit with "Hcslice2") as (t') "(Hcslice2 & Hcslice')"; [simpl_length; lia.. |].
    iApply "HΦ".
    iDestruct (array۰cslice𑁒app𑁒3₁ with "Hcslice1 Hcslice2 Hcslice3") as "$"; [simpl_length; lia.. |].
    rewrite take_idemp -!Nat.le_add_sub //; first lia.
  Qed.

  Definition itype۰array τ `{!iType _ τ} (sz : nat) t : iProp Σ :=
    ∃ l,
    ⌜t = #l⌝ ∗
    l ↦ₕ Header 0 sz ∗
    itype۰chunk τ sz l.
  #[global] Instance itype۰array𑁒itype τ `{!iType _ τ} sz :
    iType _ (itype۰array τ sz).
  Proof.
    split. apply _.
  Qed.

  Lemma itype۰array𑁒intro τ `{!iType _ τ} t vs :
    array۰model t (DfracOwn 1) vs -∗
    ([∗ list] v ∈ vs, τ v) ={⊤}=∗
    itype۰array τ (length vs) t.
  Proof.
    rewrite /array۰model.
    iSteps.
  Qed.
  Lemma itype۰array𑁒intro𑁒slice τ `{!iType _ τ} t sz vs :
    length vs = sz →
    array۰inv t sz -∗
    array۰slice t 0 (DfracOwn 1) vs -∗
    ([∗ list] v ∈ vs, τ v) ={⊤}=∗
    itype۰array τ sz t.
  Proof.
    iIntros "%Hvs #Hinv Hslice".
    iDestruct (array۰slice𑁒to𑁒model with "Hinv Hslice") as "Hmodel"; first done.
    rewrite -Hvs.
    iApply (itype۰array𑁒intro with "Hmodel").
  Qed.
  Lemma itype۰array𑁒intro𑁒cslice τ `{!iType _ τ} t sz i vs :
    0 < sz →
    length vs = sz →
    array۰cslice t sz i (DfracOwn 1) vs -∗
    ([∗ list] v ∈ vs, τ v) ={⊤}=∗
    itype۰array τ sz t.
  Proof.
    iIntros "% %Hvs Hcslice #Hvs".
    iDestruct (array۰cslice𑁒to𑁒model with "Hcslice") as "Hmodel"; [done.. |].
    iMod (itype۰array𑁒intro τ with "Hmodel []") as "Htype".
    { rewrite big_sepL_app comm -big_sepL_app take_drop //. }
    rewrite length𑁒rotation Hvs //.
  Qed.
  Lemma itype۰array𑁒to𑁒inv τ `{!iType _ τ} sz t :
    itype۰array τ sz t ⊢
    array۰inv t sz.
  Proof.
    rewrite /array۰inv. iSteps.
  Qed.

  Lemma array٠create𑁒type τ `{!iType _ τ} :
    {{{
      True
    }}}
      array٠create ()
    {{{
      t
    , RET t;
      itype۰array τ 0 t
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    iApply wp𑁒fupd.
    wp۰apply (array٠create𑁒spec with "[//]") as (t) "Hmodel".
    rewrite /array۰model.
    iDestruct "Hmodel" as "(%l & -> & #Hheader & Hmodel)".
    iApply "HΦ". iStep 2. iApply itype۰chunk𑁒0.
  Qed.

  Lemma array٠size𑁒type τ `{!iType _ τ} t sz :
    {{{
      itype۰array τ sz t
    }}}
      array٠size t
    {{{
      RET #sz;
      True
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma array٠unsafe_get𑁒type τ `{!iType _ τ} t (sz : nat) (i : Z) :
    (0 ≤ i < sz)%Z →
    {{{
      itype۰array τ sz t
    }}}
      array٠unsafe_get t #i
    {{{
      v
    , RET v;
      τ v
    }}}.
  Proof.
    iIntros "%Hi %Φ (%l & -> & #Hheader & #Htype) HΦ".
    wp۰rec. wp۰pures.
    Z_to_nat i.
    iInv "Htype" as "(%vs & >%Hvs & Hmodel & #Hvs)".
    destruct (lookup_lt_is_Some_2 vs i) as (w & Hlookup); first lia.
    iDestruct (chunk۰model𑁒lookup𑁒acc i with "Hmodel") as "(H↦ & Hmodel)"; [lia | done | lia |].
    wp۰load.
    iDestruct (big_sepL_lookup with "Hvs") as "Hv"; first done.
    iSteps.
  Qed.

  Lemma array٠get𑁒type τ `{!iType _ τ} t sz (i : Z) :
    {{{
      itype۰array τ sz t
    }}}
      array٠get t #i
    {{{
      v
    , RET v;
      ⌜0 ≤ i < sz⌝%Z ∗
      τ v
    }}}.
  Proof.
    iIntros "%Φ #Ht HΦ".
    wp۰rec.
    wp۰apply+ assume𑁒spec' as "%Hi".
    wp۰apply+ (array٠size𑁒type with "Ht") as "_".
    wp۰apply+ assume𑁒spec' as "%Hi'".
    wp۰apply+ (array٠unsafe_get𑁒type with "Ht"); first lia.
    iSteps.
  Qed.

  Lemma array٠unsafe_set𑁒type τ `{!iType _ τ} t (sz : nat) (i : Z) v :
    (0 ≤ i < sz)%Z →
    {{{
      itype۰array τ sz t ∗
      τ v
    }}}
      array٠unsafe_set t #i v
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Hi %Φ ((%l & -> & #Hheader & Htype) & #Hv) HΦ".
    wp۰rec. wp۰pures.
    Z_to_nat i.
    iInv "Htype" as "(%vs & >%Hvs & Hmodel & Hvs)".
    destruct (lookup_lt_is_Some_2 vs i) as (w & Hlookup); first lia.
    iDestruct (chunk۰model𑁒update i with "Hmodel") as "(H↦ & Hmodel)"; [lia | done | lia |].
    wp۰store.
    iDestruct (big_sepL_insert_acc with "Hvs") as "(_ & Hvs)"; first done.
    iSplitR "HΦ"; last iSteps.
    iExists (<[i := v]> vs). simpl_length. iSteps.
  Qed.

  Lemma array٠set𑁒type τ `{!iType _ τ} t sz (i : Z) v :
    {{{
      itype۰array τ sz t ∗
      τ v
    }}}
      array٠set t #i v
    {{{
      RET ();
      ⌜0 ≤ i < sz⌝%Z
    }}}.
  Proof.
    iIntros "%Φ (#Htype & #Hv) HΦ".
    wp۰rec.
    wp۰apply+ assume𑁒spec' as "%Hi".
    wp۰apply+ (array٠size𑁒type with "Htype") as "_".
    wp۰apply+ assume𑁒spec' as "%Hi'".
    wp۰apply+ (array٠unsafe_set𑁒type with "[$Htype $Hv]"); first lia.
    iSteps.
  Qed.

  Lemma array٠unsafe_xchg𑁒type τ `{!iType _ τ} t (sz : nat) (i : Z) v :
    (0 ≤ i < sz)%Z →
    {{{
      itype۰array τ sz t ∗
      τ v
    }}}
      array٠unsafe_xchg t #i v
    {{{
      w
    , RET w;
      τ w
    }}}.
  Proof.
    iIntros "%Hi %Φ ((%l & -> & #Hheader & Htype) & #Hv) HΦ".
    wp۰rec. wp۰pures.
    Z_to_nat i.
    iInv "Htype" as "(%vs & >%Hvs & Hmodel & Hvs)".
    destruct (lookup_lt_is_Some_2 vs i) as (w & Hlookup); first lia.
    iDestruct (chunk۰model𑁒update i with "Hmodel") as "(H↦ & Hmodel)"; [lia | done | lia |].
    wp۰xchg.
    iDestruct (big_sepL_insert_acc with "Hvs") as "(#Hw & Hvs)"; first done.
    iSplitR "HΦ"; last iSteps.
    iExists (<[i := v]> vs). simpl_length. iSteps.
  Qed.

  Lemma array٠unsafe_cas𑁒type τ `{!iType _ τ} t (sz : nat) (i : Z) v1 v2 :
    (0 ≤ i < sz)%Z →
    {{{
      itype۰array τ sz t ∗
      τ v1 ∗
      τ v2
    }}}
      array٠unsafe_cas t #i v1 v2
    {{{
      b
    , RET #b;
      True
    }}}.
  Proof.
    iIntros "%Hi %Φ ((%l & -> & #Hheader & Htype) & #Hv1 & #Hv2) HΦ".
    wp۰rec. wp۰pures.
    Z_to_nat i.
    iInv "Htype" as "(%vs & >%Hvs & Hmodel & Hvs)".
    destruct (lookup_lt_is_Some_2 vs i) as (v & Hlookup); first lia.
    iDestruct (chunk۰model𑁒update i with "Hmodel") as "(H↦ & Hmodel)"; [lia | done | lia |].
    wp۰apply (wp𑁒cas𑁒nobranch' with "H↦") as (b) "_ H↦ !>".
    iDestruct (big_sepL_insert_acc with "Hvs") as "(#Hv & Hvs)"; first done.
    iSplitR "HΦ"; last iSteps.
    iExists (<[i := if b then v2 else v]> vs). simpl_length. destruct b; iSteps.
  Qed.

  Lemma array٠unsafe_fill_slice𑁒type τ `{!iType _ τ} t (sz : nat) (i n : Z) v :
    (0 ≤ i)%Z →
    (0 ≤ n)%Z →
    (i + n ≤ sz)%Z →
    {{{
      itype۰array τ sz t ∗
      τ v
    }}}
      array٠unsafe_fill_slice t #i #n v
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "% % % %Φ (#Htype & #Hv) HΦ".
    wp۰rec.
    wp۰apply+ for𑁒type; last iSteps. iIntros "!> % (%k & -> & %Hk)".
    wp۰apply+ (array٠unsafe_set𑁒type with "[$Htype $Hv]"); first lia.
    iSteps.
  Qed.

  Lemma array٠fill_slice𑁒type τ `{!iType _ τ} t sz (i n : Z) v :
    {{{
      itype۰array τ sz t ∗
      τ v
    }}}
      array٠fill_slice t #i #n v
    {{{
      RET ();
      ⌜0 ≤ i⌝%Z ∗
      ⌜0 ≤ n⌝%Z ∗
      ⌜i + n ≤ sz⌝%Z
    }}}.
  Proof.
    iIntros "%Φ (#Htype & #Hv) HΦ".
    wp۰rec.
    wp۰apply+ (array٠size𑁒type with "Htype") as "_".
    repeat (wp۰apply+ assume𑁒spec' as "%").
    wp۰pures.
    wp۰apply+ (array٠unsafe_fill_slice𑁒type with "[$Htype $Hv]"); [done.. |].
    iSteps.
  Qed.

  Lemma array٠fill𑁒type τ `{!iType _ τ} t sz v :
    {{{
      itype۰array τ sz t ∗
      τ v
    }}}
      array٠fill t v
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ (#Htype & #Hv) HΦ".
    wp۰rec.
    wp۰apply+ (array٠size𑁒type with "Htype") as "_".
    wp۰apply (array٠unsafe_fill_slice𑁒type with "[$Htype $Hv] HΦ"); lia.
  Qed.

  Lemma array٠unsafe_make𑁒type τ `{!iType _ τ} sz v :
    (0 ≤ sz)%Z →
    {{{
      τ v
    }}}
      array٠unsafe_make #sz v
    {{{
      t
    , RET t;
      itype۰array τ ₊sz t
    }}}.
  Proof.
    iIntros "% %Φ #Hv HΦ".
    wp۰rec.
    wp۰apply+ (array٠unsafe_alloc𑁒spec with "[//]") as (t) "Hmodel"; first done.
    wp۰apply+ (array٠fill𑁒spec with "[Hmodel]") as "Hmodel"; first iSteps.
    iStep 5.
    iMod (itype۰array𑁒intro with "Hmodel []") as "#Htype"; simpl_length.
    iApply big_sepL_intro. iIntros "%k %_v" ((-> & Hk)%lookup_replicate) "//".
  Qed.

  Lemma array٠make𑁒type τ `{!iType _ τ} sz v :
    {{{
      τ v
    }}}
      array٠make #sz v
    {{{
      t
    , RET t;
      ⌜0 ≤ sz⌝%Z ∗
      itype۰array τ ₊sz t
    }}}.
  Proof.
    iIntros "%Φ #Hv HΦ".
    wp۰rec.
    wp۰apply+ assume𑁒spec' as "%".
    wp۰apply+ (array٠unsafe_make𑁒type with "[//]"); first done.
    iSteps.
  Qed.

  Lemma array٠foldli𑁒type τ `{!iType _ τ} υ `{!iType _ υ} fn acc t sz :
    {{{
      itype۰array τ sz t ∗
      υ acc ∗
      (itype۰nat_upto sz --> υ --> τ --> υ)%T fn
    }}}
      array٠foldli fn acc t
    {{{
      acc'
    , RET acc';
      υ acc'
    }}}.
  Proof.
    iIntros "%Φ (Htype & Hacc & #Hfn) HΦ".
    iDestruct (itype۰array𑁒to𑁒inv with "Htype") as "#Hinv".
    iDestruct "Htype" as "(%l & -> & #Hheader & #Htype)".
    pose (Ψ i vs o acc := (
      from_option τ True o ∗
      υ acc
    )%I).
    wp۰apply (array٠foldli𑁒spec𑁒atomic Ψ with "[$Hinv $Hacc]"); last iSteps.
    iIntros "!> {% acc} %i %vs_left %o %acc %Hi1 %Hi2 (Ho & Hacc)".
    destruct o as [v |].
    - wp۰apply (wp𑁒wand with "(Hfn [])") as "{Hfn} {% fn} %fn Hfn"; first iSteps.
      wp۰apply (wp𑁒wand with "(Hfn Hacc)") as "{% fn} %fn Hfn".
      wp۰apply (wp𑁒wand with "(Hfn Ho)").
      iSteps.
    - iAuIntro.
      iInv "Htype" as "(%vs & >%Hvs & >Hmodel & #Hvs)".
      opose proof* (list_lookup_lookup_total_lt vs i); first lia.
      iDestruct (chunk۰model𑁒lookup𑁒acc i with "Hmodel") as "(H↦ & Hmodel)"; [lia | done | lia |].
      iDestruct (big_sepL_lookup with "Hvs") as "Hv"; first done.
      rewrite /array۰slice chunk۰model𑁒singleton.
      iAaccIntro with "[$H↦]"; iSteps.
  Qed.

  Lemma array٠foldl𑁒type τ `{!iType _ τ} υ `{!iType _ υ} fn acc t sz :
    {{{
      itype۰array τ sz t ∗
      υ acc ∗
      (υ --> τ --> υ)%T fn
    }}}
      array٠foldl fn acc t
    {{{
      acc'
    , RET acc';
      υ acc'
    }}}.
  Proof.
    iIntros "%Φ (#Htype & #Hacc & #Hfn) HΦ".
    wp۰rec.
    wp۰apply+ (array٠foldli𑁒type τ υ with "[$Htype $Hacc] HΦ").
    iSteps.
  Qed.

  Lemma array٠foldri𑁒type τ `{!iType _ τ} υ `{!iType _ υ} fn acc t sz :
    {{{
      itype۰array τ sz t ∗
      (itype۰nat_upto sz --> τ --> υ --> υ)%T fn ∗
      υ acc
    }}}
      array٠foldri fn t acc
    {{{
      acc'
    , RET acc';
      υ acc'
    }}}.
  Proof.
    iIntros "%Φ (#Htype & #Hfn & Hacc) HΦ".
    iDestruct (itype۰array𑁒to𑁒inv with "Htype") as "#Hinv".
    iDestruct "Htype" as "(%l & -> & #Hheader & #Htype)".
    pose (Ψ i acc o vs := (
      from_option τ True o ∗
      υ acc
    )%I).
    wp۰apply (array٠foldri𑁒spec𑁒atomic Ψ with "[$Hinv $Hacc]"); last iSteps.
    iIntros "!> {% acc} %i %acc %o %vs_right %Hi (Ho & Hacc)".
    destruct o as [v |].
    - wp۰apply (wp𑁒wand with "(Hfn [])") as "{Hfn} {% fn} %fn Hfn"; first iSteps.
      wp۰apply (wp𑁒wand with "(Hfn Ho)") as "{% fn} %fn Hfn".
      wp۰apply (wp𑁒wand with "(Hfn Hacc)").
      iSteps.
    - iAuIntro.
      iInv "Htype" as "(%vs & >%Hvs & >Hmodel & #Hvs)".
      opose proof* (list_lookup_lookup_total_lt vs i); first lia.
      iDestruct (chunk۰model𑁒lookup𑁒acc i with "Hmodel") as "(H↦ & Hmodel)"; [lia | done | lia |].
      iDestruct (big_sepL_lookup with "Hvs") as "Hv"; first done.
      rewrite /array۰slice chunk۰model𑁒singleton.
      iAaccIntro with "[$H↦]"; iSteps.
  Qed.

  Lemma array٠foldr𑁒type τ `{!iType _ τ} υ `{!iType _ υ} fn t sz acc :
    {{{
      itype۰array τ sz t ∗
      (τ --> υ --> υ)%T fn ∗
      υ acc
    }}}
      array٠foldr fn t acc
    {{{
      acc'
    , RET acc';
      υ acc'
    }}}.
  Proof.
    iIntros "%Φ (#Htype & #Hfn & #Hacc) HΦ".
    wp۰rec.
    wp۰apply+ (array٠foldri𑁒type τ υ with "[$Htype $Hacc] HΦ").
    iSteps.
  Qed.

  Lemma array٠unsafe_iteri_slice𑁒type τ `{!iType _ τ} fn t (sz : nat) (i n : Z) :
    (0 ≤ i ≤ sz)%Z →
    (0 ≤ n)%Z →
    (i + n ≤ sz)%Z →
    {{{
      itype۰array τ sz t ∗
      (itype۰nat_upto ₊n --> τ --> itype۰unit)%T fn
    }}}
      array٠unsafe_iteri_slice fn t #i #n
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "% % % %Φ (#Htype & #Hfn) HΦ".
    wp۰rec.
    wp۰apply+ (for𑁒type with "[] HΦ"). iIntros "!> % (%k & -> & %Hk)".
    wp۰apply+ (array٠unsafe_get𑁒type with "Htype"); first lia.
    iSteps.
  Qed.

  Lemma array٠iteri_slice𑁒type τ `{!iType _ τ} fn t (sz : nat) (i n : Z) :
    {{{
      itype۰array τ sz t ∗
      (itype۰nat_upto ₊n --> τ --> itype۰unit)%T fn
    }}}
      array٠iteri_slice fn t #i #n
    {{{
      RET ();
      ⌜0 ≤ i ≤ sz⌝%Z ∗
      ⌜0 ≤ n⌝%Z ∗
      ⌜i + n ≤ sz⌝%Z
    }}}.
  Proof.
    iIntros "%Φ (#Htype & #Hfn) HΦ".
    wp۰rec.
    do 2 (wp۰apply+ assume𑁒spec' as "%").
    wp۰apply+ (array٠size𑁒type with "Htype") as "_".
    do 2 (wp۰apply+ assume𑁒spec' as "%").
    wp۰apply+ (array٠unsafe_iteri_slice𑁒type with "[$Htype $Hfn]"); [done.. |].
    iSteps.
  Qed.

  Lemma array٠unsafe_iter_slice𑁒type τ `{!iType _ τ} fn t (sz : nat) (i n : Z) :
    (0 ≤ i ≤ sz)%Z →
    (0 ≤ n)%Z →
    (i + n ≤ sz)%Z →
    {{{
      itype۰array τ sz t ∗
      (τ --> itype۰unit)%T fn
    }}}
      array٠unsafe_iter_slice fn t #i #n
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "% % % %Φ (#Htype & #Hfn) HΦ".
    wp۰rec.
    wp۰apply+ (array٠unsafe_iteri_slice𑁒type with "[$Htype] HΦ"); [done.. |].
    iSteps.
  Qed.

  Lemma array٠iter_slice𑁒type τ `{!iType _ τ} fn t (sz : nat) (i n : Z) :
    {{{
      itype۰array τ sz t ∗
      (τ --> itype۰unit)%T fn
    }}}
      array٠iter_slice fn t #i #n
    {{{
      RET ();
      ⌜0 ≤ i ≤ sz⌝%Z ∗
      ⌜0 ≤ n⌝%Z ∗
      ⌜i + n ≤ sz⌝%Z
    }}}.
  Proof.
    iIntros "%Φ (#Htype & #Hfn) HΦ".
    wp۰rec.
    do 2 (wp۰apply+ assume𑁒spec' as "%").
    wp۰apply+ (array٠size𑁒type with "Htype") as "_".
    do 2 (wp۰apply+ assume𑁒spec' as "%").
    wp۰apply+ (array٠unsafe_iter_slice𑁒type with "[$Htype $Hfn]"); [done.. |].
    iSteps.
  Qed.

  Lemma array٠iteri𑁒type τ `{!iType _ τ} fn t sz :
    {{{
      itype۰array τ sz t ∗
      (itype۰nat_upto sz --> τ --> itype۰unit)%T fn
    }}}
      array٠iteri fn t
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ (#Htype & #Hfn) HΦ".
    wp۰rec.
    wp۰apply+ (array٠size𑁒type with "Htype") as "_".
    wp۰apply+ (array٠unsafe_iteri_slice𑁒type with "[$Htype Hfn] HΦ"); [lia.. | iSteps].
  Qed.

  Lemma array٠iter𑁒type τ `{!iType _ τ} fn t sz :
    {{{
      itype۰array τ sz t ∗
      (τ --> itype۰unit)%T fn
    }}}
      array٠iter fn t
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ (#Htype & #Hfn) HΦ".
    wp۰rec.
    wp۰apply+ (array٠iteri𑁒type τ with "[$Htype] HΦ").
    iSteps.
  Qed.

  Lemma array٠unsafe_applyi_slice𑁒type τ `{!iType _ τ} fn t (sz : nat) (i n : Z) :
    (0 ≤ i ≤ sz)%Z →
    (0 ≤ n)%Z →
    (i + n ≤ sz)%Z →
    {{{
      itype۰array τ sz t ∗
      (itype۰nat_upto ₊n --> τ --> τ)%T fn
    }}}
      array٠unsafe_applyi_slice fn t #i #n
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "% % % %Φ (#Htype & #Hfn) HΦ".

    wp۰rec.
    wp۰apply+ (array٠unsafe_iteri_slice𑁒type τ with "[$Htype] HΦ"); [done.. |].
    iIntros "!> % (%k & -> & %Hk)". wp۰pures. iIntros "!> !> %v Hv".
    wp۰apply+ (wp𑁒wand with "(Hfn [])") as "{Hfn} {% fn} %fn Hfn"; first iSteps.
    wp۰apply (wp𑁒wand with "(Hfn Hv)") as "%w Hw".
    wp۰apply+ (array٠unsafe_set𑁒type with "[$Htype $Hw]"); first lia.
    iSteps.
  Qed.

  Lemma array٠applyi_slice𑁒type τ `{!iType _ τ} fn t (sz : nat) (i n : Z) :
    {{{
      itype۰array τ sz t ∗
      (itype۰nat_upto ₊n --> τ --> τ)%T fn
    }}}
      array٠applyi_slice fn t #i #n
    {{{
      RET ();
      ⌜0 ≤ i ≤ sz⌝%Z ∗
      ⌜0 ≤ n⌝%Z ∗
      ⌜i + n ≤ sz⌝%Z
    }}}.
  Proof.
    iIntros "%Φ (#Htype & #Hfn) HΦ".

    wp۰rec.
    do 2 (wp۰apply+ assume𑁒spec' as "%").
    wp۰apply+ (array٠size𑁒type with "Htype") as "_".
    do 2 (wp۰apply+ assume𑁒spec' as "%").
    wp۰apply+ (array٠unsafe_applyi_slice𑁒type with "[$Htype $Hfn]"); [done.. |].
    iSteps.
  Qed.

  Lemma array٠unsafe_apply_slice𑁒type τ `{!iType _ τ} fn t (sz : nat) (i n : Z) :
    (0 ≤ i ≤ sz)%Z →
    (0 ≤ n)%Z →
    (i + n ≤ sz)%Z →
    {{{
      itype۰array τ sz t ∗
      (τ --> τ)%T fn
    }}}
      array٠unsafe_apply_slice fn t #i #n
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "% % % %Φ (#Htype & #Hfn) HΦ".

    wp۰rec.
    wp۰apply+ (array٠unsafe_applyi_slice𑁒type τ with "[$Htype] HΦ"); [done.. |].
    iSteps.
  Qed.

  Lemma array٠apply_slice𑁒type τ `{!iType _ τ} fn t (sz : nat) (i n : Z) :
    {{{
      itype۰array τ sz t ∗
      (τ --> τ)%T fn
    }}}
      array٠apply_slice fn t #i #n
    {{{
      RET ();
      ⌜0 ≤ i ≤ sz⌝%Z ∗
      ⌜0 ≤ n⌝%Z ∗
      ⌜i + n ≤ sz⌝%Z
    }}}.
  Proof.
    iIntros "%Φ (#Htype & #Hfn) HΦ".

    wp۰rec.
    do 2 (wp۰apply+ assume𑁒spec' as "%").
    wp۰apply+ (array٠size𑁒type with "Htype") as "_".
    do 2 (wp۰apply+ assume𑁒spec' as "%").
    wp۰apply+ (array٠unsafe_apply_slice𑁒type with "[$Htype $Hfn]"); [done.. |].
    iSteps.
  Qed.

  Lemma array٠applyi𑁒type τ `{!iType _ τ} fn t sz :
    {{{
      itype۰array τ sz t ∗
      (itype۰nat_upto sz --> τ --> τ)%T fn
    }}}
      array٠applyi fn t
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ (#Htype & #Hfn) HΦ".

    wp۰rec.
    wp۰apply+ (array٠size𑁒type with "Htype") as "_".
    wp۰apply (array٠unsafe_applyi_slice𑁒type τ with "[$Htype] HΦ"); [lia.. | iSteps].
  Qed.

  Lemma array٠apply𑁒type τ `{!iType _ τ} fn t sz :
    {{{
      itype۰array τ sz t ∗
      (τ --> τ)%T fn
    }}}
      array٠apply fn t
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ (#Htype & #Hfn) HΦ".
    wp۰rec.
    wp۰apply+ (array٠applyi𑁒type τ with "[$Htype] HΦ").
    iSteps.
  Qed.

  Lemma array٠unsafe_initi𑁒type τ `{!iType _ τ} sz sz_ fn :
    sz = ⁺sz_ →
    {{{
      (itype۰nat_upto sz_ --> τ)%T fn
    }}}
      array٠unsafe_initi #sz fn
    {{{
      t
    , RET t;
      itype۰array τ sz_ t
    }}}.
  Proof.
    iIntros (->) "%Φ #Hfn HΦ".
    wp۰rec.
    wp۰apply+ (array٠unsafe_alloc𑁒spec with "[//]") as (t) "Hmodel"; first lia.
    wp۰apply+ (array٠applyi𑁒spec𑁒disentangled (λ _, τ) with "[$Hmodel]") as (vs) "(%Hvs & Hmodel & Hvs)".
    { iIntros "!> %i %v %Hlookup".
      wp۰apply+ (wp𑁒wand with "(Hfn [])"); last iSteps.
      apply lookup_lt_Some in Hlookup. simpl_length in Hlookup. iSteps.
    }
    rewrite /array۰model.
    iDestruct "Hmodel" as "(%l & -> & #Hheader & Hmodel)".
    rewrite length_replicate Nat2Z.id in Hvs. rewrite -Hvs. iSteps.
  Qed.

  Lemma array٠initi𑁒type τ `{!iType _ τ} sz fn :
    {{{
      (itype۰nat_upto ₊sz --> τ)%T fn
    }}}
      array٠initi #sz fn
    {{{
      t
    , RET t;
      ⌜0 ≤ sz⌝%Z ∗
      itype۰array τ ₊sz t
    }}}.
  Proof.
    iIntros "%Φ #Hfn HΦ".
    wp۰rec.
    wp۰apply+ assume𑁒spec' as "%".
    wp۰apply+ (array٠unsafe_initi𑁒type with "Hfn"); first lia.
    iSteps.
  Qed.

  Lemma array٠unsafe_init𑁒type τ `{!iType _ τ} sz fn :
    (0 ≤ sz)%Z →
    {{{
      (itype۰unit --> τ)%T fn
    }}}
      array٠unsafe_init #sz fn
    {{{
      t
    , RET t;
      itype۰array τ ₊sz t
    }}}.
  Proof.
    iIntros "% %Φ #Hfn HΦ".
    wp۰rec.
    wp۰apply+ (array٠unsafe_initi𑁒type with "[] HΦ"); first lia.
    iSteps.
  Qed.

  Lemma array٠init𑁒type τ `{!iType _ τ} sz fn :
    {{{
      (itype۰unit --> τ)%T fn
    }}}
      array٠init #sz fn
    {{{
      t
    , RET t;
      ⌜0 ≤ sz⌝%Z ∗
      itype۰array τ ₊sz t
    }}}.
  Proof.
    iIntros "%Φ #Hfn HΦ".
    wp۰rec.
    wp۰apply+ assume𑁒spec' as "%".
    wp۰apply+ (array٠unsafe_init𑁒type with "Hfn"); first done.
    iSteps.
  Qed.

  Lemma array٠mapi𑁒type τ `{!iType _ τ} υ `{!iType _ υ} fn t sz sz_ :
    sz_ = ⁺sz →
    {{{
      itype۰array τ sz t ∗
      (itype۰nat_upto sz --> τ --> υ)%T fn
    }}}
      array٠mapi fn t
    {{{
      t'
    , RET t';
      itype۰array υ sz t'
    }}}.
  Proof.
    iIntros (->) "%Φ (#Htype & #Hfn) HΦ".
    wp۰rec.
    wp۰apply+ (array٠size𑁒type with "Htype") as "_".
    wp۰apply (array٠unsafe_initi𑁒type υ); first done.
    { iIntros "!> % (%i & -> & %Hi)".
      wp۰apply+ (array٠unsafe_get𑁒type with "Htype"); first lia.
      iSteps.
    }
    iSteps.
  Qed.

  Lemma array٠map𑁒type τ `{!iType _ τ} υ `{!iType _ υ} fn t sz sz_ :
    sz_ = ⁺sz →
    {{{
      itype۰array τ sz t ∗
      (τ --> υ)%T fn
    }}}
      array٠map fn t
    {{{
      t'
    , RET t';
      itype۰array υ sz t'
    }}}.
  Proof.
    iIntros (->) "%Φ (#Htype & #Hfn) HΦ".
    wp۰rec.
    wp۰apply+ (array٠mapi𑁒type τ υ with "[] HΦ"); first done.
    iFrame "#∗". iSteps.
  Qed.

  Lemma array٠unsafe_copy_slice𑁒type τ `{!iType _ τ} t1 (sz1 : nat) (i1 : Z) t2 (sz2 : nat) (i2 n : Z) :
    (0 ≤ i1)%Z →
    (0 ≤ i2)%Z →
    (0 ≤ n)%Z →
    (i1 + n ≤ sz1)%Z →
    (i2 + n ≤ sz2)%Z →
    {{{
      itype۰array τ sz1 t1 ∗
      itype۰array τ sz2 t2
    }}}
      array٠unsafe_copy_slice t1 #i1 t2 #i2 #n
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "% % % % % %Φ (#Htype1 & #Htype2) HΦ".
    wp۰rec.
    wp۰apply+ (for𑁒type with "[] HΦ"). iIntros "!> % (%k & -> & %Hk)".
    wp۰apply+ (array٠unsafe_get𑁒type with "Htype1") as (v) "#Hv"; first lia.
    wp۰apply+ (array٠unsafe_set𑁒type with "[$Htype2 $Hv]"); first lia.
    iSteps.
  Qed.
  Lemma array٠unsafe_copy_slice۰type' τ `{!iType _ τ} t1 (sz : nat) (i1 : Z) t2 (i2 : Z) i2_ vs (n : Z) :
    (0 ≤ i1)%Z →
    i2 = ⁺i2_ →
    n = length vs →
    (i1 + n ≤ sz)%Z →
    {{{
      itype۰array τ sz t1 ∗
      array۰slice t2 i2_ (DfracOwn 1) vs
    }}}
      array٠unsafe_copy_slice t1 #i1 t2 #i2 #n
    {{{
      ws
    , RET ();
      ⌜length ws = length vs⌝ ∗
      array۰slice t2 i2_ (DfracOwn 1) ws ∗
      [∗ list] w ∈ ws, τ w
    }}}.
  Proof.
    iIntros (? -> -> ?) "%Φ (#Htype1 & Hslice2) HΦ".
    wp۰rec.
    pose (Ψ (_ : Z) k := (
      ∃ ws,
      ⌜length ws = k⌝ ∗
      array۰slice t2 i2_ (DfracOwn 1) (ws ++ drop k vs) ∗
      [∗ list] w ∈ ws, τ w
    )%I).
    wp۰apply+ (for𑁒spec𑁒strong Ψ with "[Hslice2]").
    { iSplitL.
      - iExists []. iSteps.
      - iIntros "!> % %k -> %Hk (%ws & %Hws & Hslice2 & Hws)".
        wp۰apply+ (array٠unsafe_get𑁒type with "Htype1") as (v) "Hv"; first lia.
        wp۰apply+ (array٠unsafe_set𑁒spec𑁒slice with "Hslice2") as "Hslice2".
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

  Lemma array٠copy_slice𑁒type τ `{!iType _ τ} t1 sz1 (i1 : Z) t2 sz2 (i2 n : Z) :
    {{{
      itype۰array τ sz1 t1 ∗
      itype۰array τ sz2 t2
    }}}
      array٠copy_slice t1 #i1 t2 #i2 #n
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
    wp۰rec.
    wp۰apply+ (array٠size𑁒type with "Htype1") as "_".
    wp۰apply+ (array٠size𑁒type with "Htype2") as "_".
    repeat (wp۰apply+ assume𑁒spec' as "%").
    wp۰apply+ array٠unsafe_copy_slice𑁒type; [done.. | iFrame "#" |].
    iSteps.
  Qed.

  Lemma array٠unsafe_copy𑁒type τ `{!iType _ τ} t1 (sz1 : nat) t2 (sz2 : nat) (i2 : Z) :
    (0 ≤ i2)%Z →
    (i2 + sz1 ≤ sz2)%Z →
    {{{
      itype۰array τ sz1 t1 ∗
      itype۰array τ sz2 t2
    }}}
      array٠unsafe_copy t1 t2 #i2
    {{{
      RET ();
      ⌜i2 + sz1 ≤ sz2⌝%Z
    }}}.
  Proof.
    iIntros "% % %Φ (#Htype1 & #Htype2) HΦ".
    wp۰rec.
    wp۰apply+ (array٠size𑁒type with "Htype1") as "_".
    wp۰apply (array٠unsafe_copy_slice𑁒type τ t1 with "[$]"); [lia.. |].
    iSteps.
  Qed.
  Lemma array٠unsafe_copy۰type' τ `{!iType _ τ} t1 sz t2 (i2 : Z) i2_ vs :
    i2 = ⁺i2_ →
    sz = length vs →
    {{{
      itype۰array τ sz t1 ∗
      array۰slice t2 i2_ (DfracOwn 1) vs
    }}}
      array٠unsafe_copy t1 t2 #i2
    {{{
      ws
    , RET ();
      ⌜length ws = length vs⌝ ∗
      array۰slice t2 i2_ (DfracOwn 1) ws ∗
      [∗ list] w ∈ ws, τ w
    }}}.
  Proof.
    iIntros (-> ->) "%Φ (#Htype1 & Hmodel2) HΦ".
    wp۰rec.
    wp۰apply+ (array٠size𑁒type with "Htype1") as "_".
    wp۰apply (array٠unsafe_copy_slice۰type' with "[$Htype1 $Hmodel2] HΦ"); done.
  Qed.

  Lemma array٠copy𑁒type τ `{!iType _ τ} t1 sz1 t2 sz2 (i2 : Z) :
    {{{
      itype۰array τ sz1 t1 ∗
      itype۰array τ sz2 t2
    }}}
      array٠copy t1 t2 #i2
    {{{
      RET ();
      ⌜0 ≤ i2⌝%Z ∗
      ⌜i2 + sz1 ≤ sz2⌝%Z
    }}}.
  Proof.
    iIntros "%Φ (#Htype1 & #Htype2) HΦ".
    wp۰rec.
    wp۰apply+ assume𑁒spec' as "%".
    wp۰apply+ (array٠size𑁒type with "Htype2") as "_".
    wp۰apply+ (array٠size𑁒type with "Htype1") as "_".
    wp۰apply+ assume𑁒spec' as "%".
    wp۰apply+ array٠unsafe_copy𑁒type. 3: iFrame "#". all: try done.
    iSteps.
  Qed.

  Lemma array٠unsafe_grow𑁒type τ `{!iType _ τ} t (sz : nat) sz' v' :
    (sz ≤ sz')%Z →
    {{{
      itype۰array τ sz t ∗
      τ v'
    }}}
      array٠unsafe_grow t #sz' v'
    {{{
      t'
    , RET t';
      itype۰array τ ₊sz' t'
    }}}.
  Proof.
    iIntros "% %Φ (#Htype & #Hv') HΦ".
    wp۰rec.
    wp۰apply+ (array٠size𑁒type with "Htype") as "_".
    wp۰apply+ (array٠unsafe_alloc𑁒spec with "[//]") as (t') "Hmodel'"; first lia.
    iDestruct (array۰model𑁒to𑁒slice with "Hmodel'") as "(Hinv' & Hslice')".
    replace ₊sz' with (sz + (₊sz' - sz)) at 2 by lia.
    rewrite replicate_add.
    iDestruct (array۰slice𑁒app with "Hslice'") as "(Hslice1' & Hslice2')".
    wp۰apply+ (array٠unsafe_copy۰type' with "[$Htype $Hslice1']") as (vs) "(%Hvs & Hslice1' & #Hvs)"; first done.
    { simpl_length. }
    wp۰apply+ (array٠unsafe_fill_slice𑁒spec𑁒slice𑁒fit with "Hslice2'") as "Hslice2'".
    { simpl_length. }
    { simpl_length. lia. }
    iDestruct (array۰slice𑁒app₁' with "Hslice1' Hslice2'") as "Hslice'"; first done.
    iStep 5. simpl_length.
    iApply (itype۰array𑁒intro𑁒slice with "Hinv' Hslice'").
    { rewrite length_app Hvs !length_replicate. lia. }
    iApply big_sepL_app. iSteps.
    iApply big_sepL_intro. iIntros "!>" (i _v' (-> & _)%lookup_replicate).
    iSteps.
  Qed.

  Lemma array٠grow𑁒type τ `{!iType _ τ} t sz sz' v' :
    {{{
      itype۰array τ sz t ∗
      τ v'
    }}}
      array٠grow t #sz' v'
    {{{
      t'
    , RET t';
      ⌜sz ≤ sz'⌝ ∗
      itype۰array τ ₊sz' t'
    }}}.
  Proof.
    iIntros "%Φ (#Htype & #Hv') HΦ".
    wp۰rec.
    wp۰apply+ (array٠size𑁒type with "Htype") as "_".
    wp۰apply+ assume𑁒spec' as "%".
    wp۰apply+ (array٠unsafe_grow𑁒type with "[$Htype $Hv']"); first done.
    iSteps.
  Qed.

  Lemma array٠unsafe_sub𑁒type τ `{!iType _ τ} t (sz : nat) (i n : Z) :
    (0 ≤ i)%Z →
    (0 ≤ n)%Z →
    (i + n ≤ sz)%Z →
    {{{
      itype۰array τ sz t
    }}}
      array٠unsafe_sub t #i #n
    {{{
      t'
    , RET t';
      itype۰array τ ₊n t'
    }}}.
  Proof.
    iIntros "% % % %Φ #Htype HΦ".
    wp۰rec.
    wp۰apply+ (array٠unsafe_alloc𑁒spec with "[//]") as (t') "Hmodel'"; first done.
    iDestruct (array۰model𑁒to𑁒slice with "Hmodel'") as "(#Hinv' & Hslice')".
    wp۰apply+ (array٠unsafe_copy_slice۰type' with "[$Htype $Hslice']") as (vs) "(%Hvs & Hslice' & Hvs)"; try done.
    { simpl_length. lia. }
    iStep 5. simpl_length.
    iApply (itype۰array𑁒intro𑁒slice with "Hinv' Hslice' Hvs").
    { rewrite Hvs length_replicate //. }
  Qed.

  Lemma array٠sub𑁒type τ `{!iType _ τ} t sz (i n : Z) :
    {{{
      itype۰array τ sz t
    }}}
      array٠sub t #i #n
    {{{
      t'
    , RET t';
      ⌜0 ≤ i⌝%Z ∗
      ⌜0 ≤ n⌝%Z ∗
      ⌜i + n ≤ sz⌝%Z ∗
      itype۰array τ ₊n t'
    }}}.
  Proof.
    iIntros "%Φ #Htype HΦ".
    wp۰rec.
    do 2 (wp۰apply+ assume𑁒spec' as "%").
    wp۰apply+ (array٠size𑁒type with "Htype") as "_".
    wp۰apply+ assume𑁒spec' as "%".
    wp۰apply+ (array٠unsafe_sub𑁒type with "Htype"); [done.. |].
    iSteps.
  Qed.

  Lemma array٠unsafe_shrink𑁒type τ `{!iType _ τ} t (sz : nat) (n : Z) :
    (0 ≤ n ≤ sz)%Z →
    {{{
      itype۰array τ sz t
    }}}
      array٠unsafe_shrink t #n
    {{{
      t'
    , RET t';
      itype۰array τ ₊n t'
    }}}.
  Proof.
    iIntros "% %Φ Htype HΦ".
    wp۰rec.
    wp۰apply+ (array٠unsafe_sub𑁒type with "Htype"); [lia.. |].
    iSteps.
  Qed.

  Lemma array٠shrink𑁒type τ `{!iType _ τ} t sz (n : Z) :
    {{{
      itype۰array τ sz t
    }}}
      array٠shrink t #n
    {{{
      t'
    , RET t';
      ⌜0 ≤ n ≤ sz⌝%Z ∗
      itype۰array τ ₊n t'
    }}}.
  Proof.
    iIntros "%Φ #Htype HΦ".
    wp۰rec.
    wp۰apply+ assume𑁒spec' as "%".
    wp۰apply+ (array٠size𑁒type with "Htype") as "_".
    wp۰apply+ assume𑁒spec' as "%".
    wp۰apply+ (array٠unsafe_shrink𑁒type with "Htype"); first done.
    iSteps.
  Qed.

  Lemma array٠clone𑁒type τ `{!iType _ τ} t sz :
    {{{
      itype۰array τ sz t
    }}}
      array٠clone t
    {{{
      t'
    , RET t';
      itype۰array τ sz t'
    }}}.
  Proof.
    iIntros "%Φ #Htype HΦ".
    wp۰rec.
    wp۰apply (array٠size𑁒type with "Htype") as "_".
    wp۰apply (array٠unsafe_shrink𑁒type with "Htype"); first lia.
    rewrite Nat2Z.id. iSteps.
  Qed.

  Lemma array٠unsafe_cget𑁒type τ `{!iType _ τ} t sz (i : Z) :
    0 < sz →
    (0 ≤ i)%Z →
    {{{
      itype۰array τ sz t
    }}}
      array٠unsafe_cget t #i
    {{{
      v
    , RET v;
      τ v
    }}}.
  Proof.
    iIntros "%Hsz %Hi %Φ #Htype HΦ".
    wp۰rec.
    wp۰apply+ (array٠size𑁒type with "Htype") as "_".
    wp۰apply+ (array٠unsafe_get𑁒type with "Htype HΦ").
    { rewrite Z𑁒rem𑁒mod; lia. }
  Qed.

  Lemma array٠cget𑁒type τ `{!iType _ τ} t sz (i : Z) :
    {{{
      itype۰array τ sz t
    }}}
      array٠cget t #i
    {{{
      v
    , RET v;
      ⌜0 < sz⌝ ∗
      ⌜0 ≤ i⌝%Z ∗
      τ v
    }}}.
  Proof.
    iIntros "%Φ #Htype HΦ".
    wp۰rec.
    wp۰apply+ assume𑁒spec' as "%".
    wp۰apply+ (array٠size𑁒type with "Htype") as "_".
    wp۰apply+ assume𑁒spec' as "%".
    wp۰apply+ (array٠unsafe_cget𑁒type with "Htype"); [lia.. |].
    iSteps.
  Qed.

  Lemma array٠unsafe_cset𑁒type τ `{!iType _ τ} t sz (i : Z) v :
    0 < sz →
    (0 ≤ i)%Z →
    {{{
      itype۰array τ sz t ∗
      τ v
    }}}
      array٠unsafe_cset t #i v
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Hsz %Hi %Φ (#Htype & #Hv) HΦ".
    wp۰rec.
    wp۰apply+ (array٠size𑁒type with "Htype") as "_".
    wp۰apply+ (array٠unsafe_set𑁒type with "[$Htype $Hv] HΦ").
    { rewrite Z𑁒rem𑁒mod; lia. }
  Qed.

  Lemma array٠cset𑁒type τ `{!iType _ τ} t sz (i : Z) v :
    {{{
      itype۰array τ sz t ∗
      τ v
    }}}
      array٠cset t #i v
    {{{
      RET ();
      ⌜0 < sz⌝ ∗
      ⌜0 ≤ i⌝%Z
    }}}.
  Proof.
    iIntros "%Φ (#Htype & #Hv) HΦ".
    wp۰rec.
    wp۰apply+ assume𑁒spec' as "%".
    wp۰apply+ (array٠size𑁒type with "Htype") as "_".
    wp۰apply+ assume𑁒spec' as "%".
    wp۰apply+ (array٠unsafe_cset𑁒type with "[$Htype $Hv]"); [lia.. |].
    iSteps.
  Qed.

  #[local] Lemma array٠unsafe_ccopy_slice₀𑁒type τ `{!iType _ τ} t1 sz1 (i1 : Z) t2 sz2 (i2 n : Z) :
    0 < sz1 →
    0 < sz2 →
    (0 ≤ i1)%Z →
    (0 ≤ i2)%Z →
    (0 ≤ n)%Z →
    (i1 + n ≤ sz1)%Z →
    (n ≤ sz2)%Z →
    {{{
      itype۰array τ sz1 t1 ∗
      itype۰array τ sz2 t2
    }}}
      array٠unsafe_ccopy_slice₀ t1 #i1 t2 #i2 #n
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "% % % % % % % %Φ (#Htype1 & #Htype2) HΦ".

    wp۰rec.
    wp۰apply+ (array٠size𑁒type with "Htype2") as "_".
    wp۰pures.
    rewrite Z.rem_mod_nonneg; [lia.. |].
    case_bool_decide; wp۰pures.

    - wp۰apply (array٠unsafe_copy_slice𑁒type τ t1 with "[$]") as "_"; [lia.. |].
      iSteps.

    - wp۰apply (array٠unsafe_copy_slice𑁒type τ t1 with "[$]") as "_"; [lia.. |].
      wp۰apply+ (array٠unsafe_copy_slice𑁒type τ t1 with "[$]") as "_"; [lia.. |].
      iSteps.
  Qed.
  Lemma array٠unsafe_ccopy_slice𑁒type τ `{!iType _ τ} t1 sz1 (i1 : Z) t2 sz2 (i2 n : Z) :
    0 < sz1 →
    0 < sz2 →
    (0 ≤ i1)%Z →
    (0 ≤ i2)%Z →
    (0 ≤ n)%Z →
    (n ≤ sz1)%Z →
    (n ≤ sz2)%Z →
    {{{
      itype۰array τ sz1 t1 ∗
      itype۰array τ sz2 t2
    }}}
      array٠unsafe_ccopy_slice t1 #i1 t2 #i2 #n
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "% % % % % % % %Φ (#Htype1 & #Htype2) HΦ".

    wp۰rec.
    wp۰apply+ (array٠size𑁒type with "Htype1") as "_".
    wp۰pures.
    rewrite Z.rem_mod_nonneg; [lia.. |].
    case_bool_decide; wp۰pures.

    - wp۰apply (array٠unsafe_ccopy_slice₀𑁒type τ t1 with "[$]") as "_"; [lia.. |].
      iSteps.

    - wp۰apply (array٠unsafe_ccopy_slice₀𑁒type τ t1 with "[$]") as "_"; [lia.. |].
      wp۰apply+ (array٠unsafe_ccopy_slice₀𑁒type τ t1 with "[$]") as "_"; [lia.. |].
      iSteps.
  Qed.
  #[local] Lemma array٠unsafe_ccopy_slice₀۰type' τ `{!iType _ τ} t1 sz1 (i1 : Z) t2 sz2 (i2 : Z) i2_ vs (n : Z) :
    0 < sz1 →
    0 < sz2 →
    length vs ≤ sz2 →
    (0 ≤ i1)%Z →
    (i1 + length vs ≤ sz1)%Z →
    i2 = ⁺i2_ →
    n = length vs →
    {{{
      itype۰array τ sz1 t1 ∗
      array۰cslice t2 sz2 i2_ (DfracOwn 1) vs
    }}}
      array٠unsafe_ccopy_slice₀ t1 #i1 t2 #i2 #n
    {{{
      ws
    , RET ();
      ⌜length ws = length vs⌝ ∗
      array۰cslice t2 sz2 i2_ (DfracOwn 1) ws ∗
      [∗ list] w ∈ ws, τ w
    }}}.
  Proof.
    iIntros (Hsz1 Hsz2 ? ? ? -> ->) "%Φ (#Htype1 & Hcslice2) HΦ".

    wp۰rec.
    wp۰apply+ (array٠size𑁒spec𑁒cslice with "Hcslice2") as "Hcslice2".
    wp۰pures.
    rewrite Z.rem_mod_nonneg; [lia.. |].
    rewrite array۰cslice𑁒to𑁒slice //.
    iDestruct "Hcslice2" as "(#Hinv2 & Hslice21 & Hslice22)".
    case_bool_decide as Hif; wp۰pures.

    - wp۰apply (array٠unsafe_copy_slice۰type' with "[$Htype1 $Hslice21]") as (ws) "(%Hws & Hslice21 & #Hws)"; [simpl_length; lia.. |].
      simpl_length in Hws.
      iApply ("HΦ" with "[- $Hws]").
      iSteps.
      iEval (rewrite array۰cslice𑁒to𑁒slice; [lia.. |]).
      iEval (rewrite firstn_all2; first lia).
      iEval (rewrite !skipn_all2; [lia.. |]).
      iSteps.
      iApply (array۰slice𑁒nil with "Hslice22").

    - wp۰apply (array٠unsafe_copy_slice۰type' with "[$Htype1 $Hslice21]") as (ws1) "(%Hws1 & Hslice21 & #Hws1)"; [simpl_length; lia.. |].
      wp۰apply+ (array٠unsafe_copy_slice۰type' with "[$Htype1 $Hslice22]") as (ws2) "(%Hws2 & Hslice22 & #Hws2)"; [simpl_length; lia.. |].
      iDestruct (big_sepL𑁒app₂ with "Hws1 Hws2") as "Hws".
      iApply ("HΦ" with "[- $Hws]").
      simpl_length in *. iSteps.
      iEval (rewrite array۰cslice𑁒to𑁒slice; [simpl_length; lia.. |]).
      iEval (rewrite take_app_length'; first lia).
      iEval (rewrite drop_app_length'; first lia).
      iSteps.
  Qed.
  Lemma array٠unsafe_ccopy_slice۰type' τ `{!iType _ τ} t1 sz1 (i1 : Z) t2 sz2 (i2 : Z) i2_ vs (n : Z) :
    0 < sz1 →
    length vs ≤ sz1 →
    0 < sz2 →
    length vs ≤ sz2 →
    (0 ≤ i1)%Z →
    i2 = ⁺i2_ →
    n = length vs →
    {{{
      itype۰array τ sz1 t1 ∗
      array۰cslice t2 sz2 i2_ (DfracOwn 1) vs
    }}}
      array٠unsafe_ccopy_slice t1 #i1 t2 #i2 #n
    {{{
      ws
    , RET ();
      ⌜length ws = length vs⌝ ∗
      array۰cslice t2 sz2 i2_ (DfracOwn 1) ws ∗
      [∗ list] w ∈ ws, τ w
    }}}.
  Proof.
    iIntros (Hsz1 ? Hsz2 ? Hi1 -> ?) "%Φ (#Htype1 & Hcslice2) HΦ".

    wp۰rec.
    wp۰apply+ (array٠size𑁒type with "Htype1") as "_".
    wp۰pures.
    rewrite Z.rem_mod_nonneg; [lia.. |].
    case_bool_decide as Hif; wp۰pures.

    - wp۰apply (array٠unsafe_ccopy_slice₀۰type' with "[$Htype1 $Hcslice2]") as (ws) "(%Hws & Hcslice2 & Hws)"; [simpl_length; lia.. |].
      iSteps.

    - rewrite -(take_drop (sz1 - ₊i1 `mod` sz1) vs).
      iDestruct (array۰cslice𑁒app₂ with "Hcslice2") as "(Hcslice21 & Hcslice22)"; first done.
      assert (i1 `mod` sz1 = ⁺(₊i1 `mod` sz1))%Z.
      { rewrite Nat2Z.inj_mod Z2Nat.id //. }
      wp۰apply (array٠unsafe_ccopy_slice₀۰type' with "[$Htype1 $Hcslice21]") as (ws1) "(%Hws1 & Hcslice21 & Hws1)"; [simpl_length; lia.. |].
      wp۰apply+ (array٠unsafe_ccopy_slice₀۰type' with "[$Htype1 $Hcslice22]") as (ws2) "(%Hws2 & Hcslice22 & Hws2)"; [simpl_length; lia.. |].
      iDestruct (big_sepL𑁒app₂ with "Hws1 Hws2") as "Hws".
      iApply ("HΦ" with "[- $Hws]").
      simpl_length in *. iSteps.
      iApply (array۰cslice𑁒app₁ with "Hcslice21 Hcslice22"); first lia.
  Qed.

  Lemma array٠ccopy_slice𑁒type τ `{!iType _ τ} t1 sz1 (i1 : Z) t2 sz2 (i2 : Z) (n : Z) :
    0 < sz1 →
    0 < sz2 →
    {{{
      itype۰array τ sz1 t1 ∗
      itype۰array τ sz2 t2
    }}}
      array٠ccopy_slice t1 #i1 t2 #i2 #n
    {{{
      RET ();
      ⌜0 < sz1⌝ ∗
      ⌜0 < sz2⌝ ∗
      ⌜0 ≤ i1⌝%Z ∗
      ⌜0 ≤ i2⌝%Z
    }}}.
  Proof.
    iIntros "% % %Φ (#Htype1 & #Htype2) HΦ".
    wp۰rec.
    do 3 (wp۰apply+ assume𑁒spec' as "%").
    wp۰apply+ (array٠size𑁒type with "Htype1") as "_".
    wp۰apply+ (array٠size𑁒type with "Htype2") as "_".
    do 4 (wp۰apply+ assume𑁒spec' as "%").
    wp۰apply+ (array٠unsafe_ccopy_slice𑁒type τ t1 with "[$]"); [lia.. |].
    iSteps.
  Qed.

  Lemma array٠unsafe_ccopy𑁒type τ `{!iType _ τ} t1 sz1 (i1 : Z) t2 sz2 (i2 : Z) :
    0 < sz1 →
    0 < sz2 →
    sz1 ≤ sz2 →
    (0 ≤ i1)%Z →
    (0 ≤ i2)%Z →
    {{{
      itype۰array τ sz1 t1 ∗
      itype۰array τ sz2 t2
    }}}
      array٠unsafe_ccopy t1 #i1 t2 #i2
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "% % % % % %Φ (#Htype1 & #Htype2) HΦ".
    wp۰rec.
    wp۰apply+ (array٠size𑁒type with "Htype1") as "_".
    wp۰apply (array٠unsafe_ccopy_slice𑁒type τ t1 with "[$]"); [lia.. |].
    iSteps.
  Qed.

  Lemma array٠ccopy𑁒type τ `{!iType _ τ} t1 sz1 (i1 : Z) t2 sz2 (i2 : Z) :
    {{{
      itype۰array τ sz1 t1 ∗
      itype۰array τ sz2 t2
    }}}
      array٠ccopy t1 #i1 t2 #i2
    {{{
      RET ();
      ⌜0 < sz1⌝ ∗
      ⌜0 < sz2⌝ ∗
      ⌜0 ≤ i1⌝%Z ∗
      ⌜0 ≤ i2⌝%Z
    }}}.
  Proof.
    iIntros "%Φ (#Htype1 & #Htype2) HΦ".
    wp۰rec.
    do 2 (wp۰apply+ assume𑁒spec' as "%").
    wp۰apply+ (array٠size𑁒type with "Htype1") as "_".
    wp۰apply+ (array٠size𑁒type with "Htype2") as "_".
    do 2 (wp۰apply+ assume𑁒spec' as "%").
    wp۰apply+ (array٠unsafe_ccopy𑁒type τ t1 with "[$]"); [lia.. |].
    iSteps.
  Qed.

  Lemma array٠unsafe_cgrow_slice𑁒type τ `{!iType _ τ} sz t (i n : Z) sz' v :
    0 < sz →
    (0 ≤ i)%Z →
    (0 ≤ n)%Z →
    (0 < sz')%Z →
    (n ≤ sz)%Z →
    (n ≤ sz')%Z →
    {{{
      itype۰array τ sz t ∗
      τ v
    }}}
      array٠unsafe_cgrow_slice t #i #n #sz' v
    {{{
      t'
    , RET t';
      itype۰array τ ₊sz' t'
    }}}.
  Proof.
    iIntros "% % % % % % %Φ (#Htype & #Hv) HΦ".

    wp۰rec.
    wp۰apply+ (array٠unsafe_make𑁒type with "Hv") as (t') "#Htype'"; first lia.
    wp۰apply+ (array٠unsafe_ccopy_slice𑁒type τ t with "[$]") as "_"; [lia.. |].
    wp۰pures.
    iApply ("HΦ" with "Htype'").
  Qed.

  Lemma array٠unsafe_cgrow𑁒type τ `{!iType _ τ} sz t (i n : Z) sz' v :
    0 < sz →
    (0 ≤ i)%Z →
    (0 < sz')%Z →
    (sz ≤ sz')%Z →
    {{{
      itype۰array τ sz t ∗
      τ v
    }}}
      array٠unsafe_cgrow t #i #sz' v
    {{{
      t'
    , RET t';
      itype۰array τ ₊sz' t'
    }}}.
  Proof.
    iIntros "% % % % %Φ (#Htype & #Hv) HΦ".

    wp۰rec.
    wp۰apply+ (array٠size𑁒type with "Htype") as "_".
    wp۰apply (array٠unsafe_cgrow_slice𑁒type with "[$Htype $Hv]"); [lia.. |].
    iSteps.
  Qed.

  Lemma array٠unsafe_cshrink_slice𑁒type τ `{!iType _ τ} sz t (i : Z) sz' :
    0 < sz →
    (0 ≤ i)%Z →
    (0 < sz')%Z →
    (sz' ≤ sz)%Z →
    {{{
      itype۰array τ sz t
    }}}
      array٠unsafe_cshrink_slice t #i #sz'
    {{{
      t'
    , RET t';
      itype۰array τ ₊sz' t'
    }}}.
  Proof.
    iIntros "% % % % %Φ #Htype HΦ".

    wp۰rec.
    wp۰apply+ (array٠unsafe_alloc𑁒spec with "[//]") as (t') "Hmodel'"; first lia.
    iDestruct (array۰model𑁒to𑁒cslice with "Hmodel'") as "Hcslice'".
    iDestruct (array۰cslice𑁒rotation𑁒right𑁒0 ₊i with "Hcslice'") as "Hcslice'"; simpl_length; [lia.. |].
    rewrite rotation𑁒replicate.
    wp۰apply+ (array٠unsafe_ccopy_slice۰type' with "[$Htype $Hcslice']") as (vs') "(%Hvs' & Hcslice' & Hvs')"; simpl_length; [lia.. |].
    simpl_length in Hvs'.
    iStep 5.
    iApply (itype۰array𑁒intro𑁒cslice with "Hcslice' Hvs'"); lia.
  Qed.
End zoo۰G.

Require zoo_std.array__opaque.
#[global] Opaque array٠unsafe_xchg.
#[global] Opaque array٠unsafe_cas.
#[global] Opaque array٠unsafe_faa.

#[global] Opaque array۰inv.
#[global] Opaque array۰slice.
#[global] Opaque array۰model.
#[global] Opaque array۰cslice.
#[global] Opaque itype۰array.
