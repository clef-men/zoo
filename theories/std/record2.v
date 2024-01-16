From zebra Require Import
  prelude.
From zebra.language Require Import
  notations
  diaframe.
From zebra.std Require Export
  base.
From zebra Require Import
  options.

Implicit Types l : loc.

Definition record2_make : val :=
  λ: "v₀" "v₁",
    let: "l" := Alloc #2 "v₀" in
    "l".[#1] <- "v₁" ;;
    "l".

Section zebra_G.
  Context `{zebra_G : !ZebraG Σ}.

  Definition record2_model l dq₀ v₀ dq₁ v₁ : iProp Σ :=
    l.[0] ↦{dq₀} v₀ ∗
    l.[1] ↦{dq₁} v₁.
  Definition record2_model' l dq v₀ v₁ :=
    record2_model l dq v₀ dq v₁.

  Lemma record2_model_eq l dq₀ v₀ dq₁ v₁ :
    record2_model l dq₀ v₀ dq₁ v₁ ⊣⊢
      l.[0] ↦{dq₀} v₀ ∗
      l.[1] ↦{dq₁} v₁.
  Proof.
    iSteps.
  Qed.
  Lemma record2_model_eq_1 l dq₀ v₀ dq₁ v₁ :
    record2_model l dq₀ v₀ dq₁ v₁ ⊢
      l.[0] ↦{dq₀} v₀ ∗
      l.[1] ↦{dq₁} v₁.
  Proof.
    iSteps.
  Qed.
  Lemma record2_model_eq_2 l dq₀ v₀ dq₁ v₁ :
    l.[0] ↦{dq₀} v₀ -∗
    l.[1] ↦{dq₁} v₁ -∗
    record2_model l dq₀ v₀ dq₁ v₁.
  Proof.
    iSteps.
  Qed.

  #[global] Instance record2_model_timeless l dq₀ v₀ dq₁ v₁ :
    Timeless (record2_model l dq₀ v₀ dq₁ v₁).
  Proof.
    apply _.
  Qed.
  #[global] Instance record2_model_persistent l v₀ v₁ :
    Persistent (record2_model' l DfracDiscarded v₀ v₁).
  Proof.
    apply _.
  Qed.

  #[global] Instance record2_model_fractional₀ l v₀ v₁ :
    Fractional (λ q₀, record2_model l (DfracOwn q₀) v₀ DfracDiscarded v₁).
  Proof.
    apply _.
  Qed.
  #[global] Instance record2_model_as_fractional₀ l q₀ v₀ v₁ :
    AsFractional (record2_model l (DfracOwn q₀) v₀ DfracDiscarded v₁) (λ q₀, record2_model l (DfracOwn q₀) v₀ DfracDiscarded v₁) q₀.
  Proof.
    split; done || apply _.
  Qed.
  #[global] Instance record2_model_fractional₁ l v₀ v₁ :
    Fractional (λ q₁, record2_model l DfracDiscarded v₀ (DfracOwn q₁) v₁).
  Proof.
    apply _.
  Qed.
  #[global] Instance record2_model_as_fractional₁ l v₀ q₁ v₁ :
    AsFractional (record2_model l DfracDiscarded v₀ (DfracOwn q₁) v₁) (λ q₁, record2_model l DfracDiscarded v₀ (DfracOwn q₁) v₁) q₁.
  Proof.
    split; done || apply _.
  Qed.
  #[global] Instance record2_model_fractional l v₀ v₁ :
    Fractional (λ q, record2_model' l (DfracOwn q) v₀ v₁).
  Proof.
    apply _.
  Qed.
  #[global] Instance record2_model_as_fractional l q v₀ v₁ :
    AsFractional (record2_model' l (DfracOwn q) v₀ v₁) (λ q, record2_model' l (DfracOwn q) v₀ v₁) q.
  Proof.
    split; done || apply _.
  Qed.

  Lemma record2_model_valid l dq₀ v₀ dq₁ v₁ :
    record2_model l dq₀ v₀ dq₁ v₁ ⊢
    ⌜✓ dq₀ ∧ ✓ dq₁⌝.
  Proof.
    iIntros "(Hv₀ & Hv₁)".
    iDestruct (mapsto_valid with "Hv₀") as %Hdq₀.
    iDestruct (mapsto_valid with "Hv₁") as %Hdq₁.
    iSteps.
  Qed.
  Lemma record2_model_combine l dq₀1 v₀1 dq₁1 v₁1 dq₀2 v₀2 dq₁2 v₁2 :
    record2_model l dq₀1 v₀1 dq₁1 v₁1 -∗
    record2_model l dq₀2 v₀2 dq₁2 v₁2 -∗
      record2_model l (dq₀1 ⋅ dq₀2) v₀1 (dq₁1 ⋅ dq₁2) v₁1 ∗
      ⌜v₀1 = v₀2 ∧ v₁1 = v₁2⌝.
  Proof.
    iIntros "(Hv₀1 & Hv₁1) (Hv₀2 & Hv₁2)".
    iDestruct (mapsto_combine with "Hv₀1 Hv₀2") as "(Hv₀ & <-)".
    iDestruct (mapsto_combine with "Hv₁1 Hv₁2") as "(Hv₁ & <-)".
    iSteps.
  Qed.
  Lemma record2_model_valid_2 l dq₀1 v₀1 dq₁1 v₁1 dq₀2 v₀2 dq₁2 v₁2 :
    record2_model l dq₀1 v₀1 dq₁1 v₁1 -∗
    record2_model l dq₀2 v₀2 dq₁2 v₁2 -∗
    ⌜✓ (dq₀1 ⋅ dq₀2) ∧ ✓ (dq₁1 ⋅ dq₁2) ∧ v₀1 = v₀2 ∧ v₁1 = v₁2⌝.
  Proof.
    iIntros "Hl1 Hl2".
    iDestruct (record2_model_combine with "Hl1 Hl2") as "(Hl & %)".
    iDestruct (record2_model_valid with "Hl") as %?.
    naive_solver.
  Qed.
  Lemma record2_model_agree l dq₀1 v₀1 dq₁1 v₁1 dq₀2 v₀2 dq₁2 v₁2 :
    record2_model l dq₀1 v₀1 dq₁1 v₁1 -∗
    record2_model l dq₀2 v₀2 dq₁2 v₁2 -∗
    ⌜v₀1 = v₀2 ∧ v₁1 = v₁2⌝.
  Proof.
    iSteps.
  Qed.
  Lemma record2_model_dfrac_ne l1 dq₀1 v₀1 dq₁1 v₁1 l2 dq₀2 v₀2 dq₁2 v₁2 :
    ¬ ✓ (dq₀1 ⋅ dq₀2) ∨ ¬ ✓ (dq₁1 ⋅ dq₁2) →
    record2_model l1 dq₀1 v₀1 dq₁1 v₁1 -∗
    record2_model l2 dq₀2 v₀2 dq₁2 v₁2 -∗
    ⌜l1 ≠ l2⌝.
  Proof.
    iIntros "% Hl1 Hl2 ->".
    iDestruct (record2_model_valid_2 with "Hl1 Hl2") as %?.
    naive_solver.
  Qed.
  Lemma record2_model_ne l1 dq₀1 v₀1 dq₁1 v₁1 l2 dq₀2 v₀2 dq₁2 v₁2 :
    dq₀1 = DfracOwn 1 ∨ dq₁1 = DfracOwn 1 →
    record2_model l1 dq₀1 v₀1 dq₁1 v₁1 -∗
    record2_model l2 dq₀2 v₀2 dq₁2 v₁2 -∗
    ⌜l1 ≠ l2⌝.
  Proof.
    intros []; iSteps.
  Qed.
  Lemma record2_model_exclusive l dq₀1 v₀1 dq₁1 v₁1 dq₀2 v₀2 dq₁2 v₁2 :
    dq₀1 = DfracOwn 1 ∨ dq₁1 = DfracOwn 1 →
    record2_model l dq₀1 v₀1 dq₁1 v₁1 -∗
    record2_model l dq₀2 v₀2 dq₁2 v₁2 -∗
    False.
  Proof.
    intros []; iSteps.
  Qed.
  Lemma record2_model_persist₀ l dq₀ v₀ dq₁ v₁ :
    record2_model l dq₀ v₀ dq₁ v₁ ⊢ |==>
    record2_model l DfracDiscarded v₀ dq₁ v₁.
  Proof.
    iSteps.
  Qed.
  Lemma record2_model_persist₁ l dq₀ v₀ dq₁ v₁ :
    record2_model l dq₀ v₀ dq₁ v₁ ⊢ |==>
    record2_model l dq₀ v₀ DfracDiscarded  v₁.
  Proof.
    iSteps.
  Qed.
  Lemma record2_model_persist l dq₀ v₀ dq₁ v₁ :
    record2_model l dq₀ v₀ dq₁ v₁ ⊢ |==>
    record2_model' l DfracDiscarded v₀ v₁.
  Proof.
    iSteps.
  Qed.

  Lemma record2_make_spec v₀ v₁ :
    {{{ True }}}
      record2_make v₀ v₁
    {{{ l,
      RET #l;
      record2_model' l (DfracOwn 1) v₀ v₁ ∗
      meta_token l ⊤
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_rec.
    wp_smart_apply (wp_alloc with "[//]") as "%l (Hmeta & Hl)"; first done.
    iSteps.
  Qed.

  Lemma record2_get_spec₀ l dq₀ v₀ dq₁ v₁ :
    {{{
      record2_model l dq₀ v₀ dq₁ v₁
    }}}
      !#l.[0]
    {{{
      RET v₀;
      record2_model l dq₀ v₀ dq₁ v₁
    }}}.
  Proof.
    iSteps.
  Qed.
  Lemma record2_get_spec₁ l dq₀ v₀ dq₁ v₁ :
    {{{
      record2_model l dq₀ v₀ dq₁ v₁
    }}}
      !#l.[1]
    {{{
      RET v₁;
      record2_model l dq₀ v₀ dq₁ v₁
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma record2_set_spec₀ l v₀ dq₁ v₁ v :
    {{{
      record2_model l (DfracOwn 1) v₀ dq₁ v₁
    }}}
      #l.[0] <- v
    {{{
      RET #();
      record2_model l (DfracOwn 1) v dq₁ v₁
    }}}.
  Proof.
    iSteps.
  Qed.
  Lemma record2_set_spec₁ l dq₀ v₀ v₁ v :
    {{{
      record2_model l dq₀ v₀ (DfracOwn 1) v₁
    }}}
      #l.[1] <- v
    {{{
      RET #();
      record2_model l dq₀ v₀ (DfracOwn 1) v
    }}}.
  Proof.
    iSteps.
  Qed.
End zebra_G.

#[global] Opaque record2_make.

#[global] Opaque record2_model.
