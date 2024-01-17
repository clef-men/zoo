From zebre Require Import
  prelude.
From zebre.language Require Import
  notations
  diaframe.
From zebre.std Require Export
  base.
From zebre Require Import
  options.

Implicit Types l : loc.

Definition record3_make : val :=
  λ: "v₀" "v₁" "v₂",
    let: "l" := Alloc #3 "v₀" in
    "l".[#1] <- "v₁" ;;
    "l".[#2] <- "v₂" ;;
    "l".

Section zebre_G.
  Context `{zebre_G : !ZebreG Σ}.

  Definition record3_model l dq₀ v₀ dq₁ v₁ dq₂ v₂ : iProp Σ :=
    l.[0] ↦{dq₀} v₀ ∗
    l.[1] ↦{dq₁} v₁ ∗
    l.[2] ↦{dq₂} v₂.
  Definition record3_model' l dq v₀ v₁ v₂ : iProp Σ :=
    record3_model l dq v₀ dq v₁ dq v₂.

  Lemma record3_model_eq l dq₀ v₀ dq₁ v₁ dq₂ v₂ :
    record3_model l dq₀ v₀ dq₁ v₁ dq₂ v₂ ⊣⊢
      l.[0] ↦{dq₀} v₀ ∗
      l.[1] ↦{dq₁} v₁ ∗
      l.[2] ↦{dq₂} v₂.
  Proof.
    iSteps.
  Qed.
  Lemma record3_model_eq_1 l dq₀ v₀ dq₁ v₁ dq₂ v₂ :
    record3_model l dq₀ v₀ dq₁ v₁ dq₂ v₂ ⊢
      l.[0] ↦{dq₀} v₀ ∗
      l.[1] ↦{dq₁} v₁ ∗
      l.[2] ↦{dq₂} v₂.
  Proof.
    iSteps.
  Qed.
  Lemma record3_model_eq_2 l dq₀ v₀ dq₁ v₁ dq₂ v₂ :
    l.[0] ↦{dq₀} v₀ -∗
    l.[1] ↦{dq₁} v₁ -∗
    l.[2] ↦{dq₂} v₂ -∗
    record3_model l dq₀ v₀ dq₁ v₁ dq₂ v₂.
  Proof.
    iSteps.
  Qed.

  #[global] Instance record3_model_timeless l dq₀ v₀ dq₁ v₁ dq₂ v₂ :
    Timeless (record3_model l dq₀ v₀ dq₁ v₁ dq₂ v₂).
  Proof.
    apply _.
  Qed.
  #[global] Instance record3_model_persistent l v₀ v₁ v₂ :
    Persistent (record3_model' l DfracDiscarded v₀ v₁ v₂).
  Proof.
    apply _.
  Qed.

  #[global] Instance record3_model_fractional₀ l v₀ v₁ v₂ :
    Fractional (λ q₀, record3_model l (DfracOwn q₀) v₀ DfracDiscarded v₁ DfracDiscarded v₂).
  Proof.
    apply _.
  Qed.
  #[global] Instance record3_model_as_fractional₀ l q₀ v₀ v₁ v₂ :
    AsFractional (record3_model l (DfracOwn q₀) v₀ DfracDiscarded v₁ DfracDiscarded v₂) (λ q₀, record3_model l (DfracOwn q₀) v₀ DfracDiscarded v₁ DfracDiscarded v₂) q₀.
  Proof.
    split; done || apply _.
  Qed.
  #[global] Instance record3_model_fractional₁ l v₀ v₁ v₂ :
    Fractional (λ q₁, record3_model l DfracDiscarded v₀ (DfracOwn q₁) v₁ DfracDiscarded v₂).
  Proof.
    apply _.
  Qed.
  #[global] Instance record3_model_as_fractional₁ l v₀ q₁ v₁ v₂ :
    AsFractional (record3_model l DfracDiscarded v₀ (DfracOwn q₁) v₁ DfracDiscarded v₂) (λ q₁, record3_model l DfracDiscarded v₀ (DfracOwn q₁) v₁ DfracDiscarded v₂) q₁.
  Proof.
    split; done || apply _.
  Qed.
  #[global] Instance record3_model_fractional₂ l v₀ v₁ v₂ :
    Fractional (λ q₂, record3_model l DfracDiscarded v₀ DfracDiscarded v₁ (DfracOwn q₂) v₂).
  Proof.
    apply _.
  Qed.
  #[global] Instance record3_model_as_fractional₂ l v₀ v₁ q₂ v₂ :
    AsFractional (record3_model l DfracDiscarded v₀ DfracDiscarded v₁ (DfracOwn q₂) v₂) (λ q₂, record3_model l DfracDiscarded v₀ DfracDiscarded v₁ (DfracOwn q₂) v₂) q₂.
  Proof.
    split; done || apply _.
  Qed.
  #[global] Instance record3_model_fractional l v₀ v₁ v₂ :
    Fractional (λ q, record3_model' l (DfracOwn q) v₀ v₁ v₂).
  Proof.
    apply _.
  Qed.
  #[global] Instance record3_model_as_fractional l q v₀ v₁ v₂ :
    AsFractional (record3_model' l (DfracOwn q) v₀ v₁ v₂) (λ q, record3_model' l (DfracOwn q) v₀ v₁ v₂) q.
  Proof.
    split; done || apply _.
  Qed.

  Lemma record3_model_valid l dq₀ v₀ dq₁ v₁ dq₂ v₂ :
    record3_model l dq₀ v₀ dq₁ v₁ dq₂ v₂ ⊢
    ⌜✓ dq₀ ∧ ✓ dq₁ ∧ ✓ dq₂⌝.
  Proof.
    iIntros "(Hv₀ & Hv₁ & Hv₂)".
    iDestruct (mapsto_valid with "Hv₀") as %Hdq₀.
    iDestruct (mapsto_valid with "Hv₁") as %Hdq₁.
    iDestruct (mapsto_valid with "Hv₂") as %Hdq₂.
    iSteps.
  Qed.
  Lemma record3_model_combine l dq₀1 v₀1 dq₁1 v₁1 dq₂1 v₂1 dq₀2 v₀2 dq₁2 v₁2 dq₂2 v₂2 :
    record3_model l dq₀1 v₀1 dq₁1 v₁1 dq₂1 v₂1 -∗
    record3_model l dq₀2 v₀2 dq₁2 v₁2 dq₂2 v₂2 -∗
      record3_model l (dq₀1 ⋅ dq₀2) v₀1 (dq₁1 ⋅ dq₁2) v₁1 (dq₂1 ⋅ dq₂2) v₂1 ∗
      ⌜v₀1 = v₀2 ∧ v₁1 = v₁2 ∧ v₂1 = v₂2⌝.
  Proof.
    iIntros "(Hv₀1 & Hv₁1 & Hv₂1) (Hv₀2 & Hv₁2 & Hv₂2)".
    iDestruct (mapsto_combine with "Hv₀1 Hv₀2") as "(Hv₀ & <-)".
    iDestruct (mapsto_combine with "Hv₁1 Hv₁2") as "(Hv₁ & <-)".
    iDestruct (mapsto_combine with "Hv₂1 Hv₂2") as "(Hv₂ & <-)".
    iSteps.
  Qed.
  Lemma record3_model_valid_2 l dq₀1 v₀1 dq₁1 v₁1 dq₂1 v₂1 dq₀2 v₀2 dq₁2 v₁2 dq₂2 v₂2 :
    record3_model l dq₀1 v₀1 dq₁1 v₁1 dq₂1 v₂1 -∗
    record3_model l dq₀2 v₀2 dq₁2 v₁2 dq₂2 v₂2 -∗
    ⌜✓ (dq₀1 ⋅ dq₀2) ∧ ✓ (dq₁1 ⋅ dq₁2) ∧ ✓ (dq₂1 ⋅ dq₂2) ∧ v₀1 = v₀2 ∧ v₁1 = v₁2 ∧ v₂1 = v₂2⌝.
  Proof.
    iIntros "Hl1 Hl2".
    iDestruct (record3_model_combine with "Hl1 Hl2") as "(Hl & %)".
    iDestruct (record3_model_valid with "Hl") as %?.
    naive_solver.
  Qed.
  Lemma record3_model_agree l dq₀1 v₀1 dq₁1 v₁1 dq₂1 v₂1 dq₀2 v₀2 dq₁2 v₁2 dq₂2 v₂2 :
    record3_model l dq₀1 v₀1 dq₁1 v₁1 dq₂1 v₂1 -∗
    record3_model l dq₀2 v₀2 dq₁2 v₁2 dq₂2 v₂2 -∗
    ⌜v₀1 = v₀2 ∧ v₁1 = v₁2 ∧ v₂1 = v₂2⌝.
  Proof.
    iSteps.
  Qed.
  Lemma record3_model_dfrac_ne l1 dq₀1 v₀1 dq₁1 v₁1 dq₂1 v₂1 l2 dq₀2 v₀2 dq₁2 v₁2 dq₂2 v₂2 :
    ¬ ✓ (dq₀1 ⋅ dq₀2) ∨ ¬ ✓ (dq₁1 ⋅ dq₁2) ∨ ¬ ✓ (dq₂1 ⋅ dq₂2) →
    record3_model l1 dq₀1 v₀1 dq₁1 v₁1 dq₂1 v₂1 -∗
    record3_model l2 dq₀2 v₀2 dq₁2 v₁2 dq₂2 v₂2 -∗
    ⌜l1 ≠ l2⌝.
  Proof.
    iIntros "% Hl1 Hl2" (->).
    iDestruct (record3_model_valid_2 with "Hl1 Hl2") as %?.
    naive_solver.
  Qed.
  Lemma record3_model_ne l1 dq₀1 v₀1 dq₁1 v₁1 dq₂1 v₂1 l2 dq₀2 v₀2 dq₁2 v₁2 dq₂2 v₂2 :
    dq₀1 = DfracOwn 1 ∨ dq₁1 = DfracOwn 1 ∨ dq₂1 = DfracOwn 1 →
    record3_model l1 dq₀1 v₀1 dq₁1 v₁1 dq₂1 v₂1 -∗
    record3_model l2 dq₀2 v₀2 dq₁2 v₁2 dq₂2 v₂2 -∗
    ⌜l1 ≠ l2⌝.
  Proof.
    intros [| []]; iSteps.
  Qed.
  Lemma record3_model_exclusive l dq₀1 v₀1 dq₁1 v₁1 dq₂1 v₂1 dq₀2 v₀2 dq₁2 v₁2 dq₂2 v₂2 :
    dq₀1 = DfracOwn 1 ∨ dq₁1 = DfracOwn 1 ∨ dq₂1 = DfracOwn 1 →
    record3_model l dq₀1 v₀1 dq₁1 v₁1 dq₂1 v₂1 -∗
    record3_model l dq₀2 v₀2 dq₁2 v₁2 dq₂2 v₂2 -∗
    False.
  Proof.
    intros [| []]; iSteps.
  Qed.
  Lemma record3_model_persist₀ l dq₀ v₀ dq₁ v₁ dq₂ v₂ :
    record3_model l dq₀ v₀ dq₁ v₁ dq₂ v₂ ⊢ |==>
    record3_model l DfracDiscarded v₀ dq₁ v₁ dq₂ v₂.
  Proof.
    iSteps.
  Qed.
  Lemma record3_model_persist₁ l dq₀ v₀ dq₁ v₁ dq₂ v₂ :
    record3_model l dq₀ v₀ dq₁ v₁ dq₂ v₂ ⊢ |==>
    record3_model l dq₀ v₀ DfracDiscarded v₁ dq₂ v₂.
  Proof.
    iSteps.
  Qed.
  Lemma record3_model_persist₂ l dq₀ v₀ dq₁ v₁ dq₂ v₂ :
    record3_model l dq₀ v₀ dq₁ v₁ dq₂ v₂ ⊢ |==>
    record3_model l dq₀ v₀ dq₁ v₁ DfracDiscarded v₂.
  Proof.
    iSteps.
  Qed.
  Lemma record3_model_persist l dq₀ v₀ dq₁ v₁ dq₂ v₂ :
    record3_model l dq₀ v₀ dq₁ v₁ dq₂ v₂ ⊢ |==>
    record3_model l DfracDiscarded v₀ DfracDiscarded v₁ DfracDiscarded v₂.
  Proof.
    iSteps.
  Qed.

  Lemma record3_make_spec v₀ v₁ v₂ :
    {{{ True }}}
      record3_make v₀ v₁ v₂
    {{{ l,
      RET #l;
      record3_model' l (DfracOwn 1) v₀ v₁ v₂ ∗
      meta_token l ⊤
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_rec.
    wp_smart_apply (wp_alloc with "[//]") as "%l (Hmeta & Hl)"; first done.
    iSteps.
  Qed.

  Lemma record3_get_spec₀ l dq₀ v₀ dq₁ v₁ dq₂ v₂ :
    {{{
      record3_model l dq₀ v₀ dq₁ v₁ dq₂ v₂
    }}}
      !#l.[0]
    {{{
      RET v₀;
      record3_model l dq₀ v₀ dq₁ v₁ dq₂ v₂
    }}}.
  Proof.
    iSteps.
  Qed.
  Lemma record3_get_spec₁ l dq₀ v₀ dq₁ v₁ dq₂ v₂ :
    {{{
      record3_model l dq₀ v₀ dq₁ v₁ dq₂ v₂
    }}}
      !#l.[1]
    {{{
      RET v₁;
      record3_model l dq₀ v₀ dq₁ v₁ dq₂ v₂
    }}}.
  Proof.
    iSteps.
  Qed.
  Lemma record3_get_spec₂ l dq₀ v₀ dq₁ v₁ dq₂ v₂ :
    {{{
      record3_model l dq₀ v₀ dq₁ v₁ dq₂ v₂
    }}}
      !#l.[2]
    {{{
      RET v₂;
      record3_model l dq₀ v₀ dq₁ v₁ dq₂ v₂
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma record3_set_spec₀ l v₀ dq₁ v₁ dq₂ v₂ v :
    {{{
      record3_model l (DfracOwn 1) v₀ dq₁ v₁ dq₂ v₂
    }}}
      #l.[0] <- v
    {{{
      RET #();
      record3_model l (DfracOwn 1) v dq₁ v₁ dq₂ v₂
    }}}.
  Proof.
    iSteps.
  Qed.
  Lemma record3_set_spec₁ l dq₀ v₀ v₁ dq₂ v₂ v :
    {{{
      record3_model l dq₀ v₀ (DfracOwn 1) v₁ dq₂ v₂
    }}}
      #l.[1] <- v
    {{{
      RET #();
      record3_model l dq₀ v₀ (DfracOwn 1) v dq₂ v₂
    }}}.
  Proof.
    iSteps.
  Qed.
  Lemma record3_set_spec₂ l dq₀ v₀ dq₁ v₁ v₂ v :
    {{{
      record3_model l dq₀ v₀ dq₁ v₁ (DfracOwn 1) v₂
    }}}
      #l.[2] <- v
    {{{
      RET #();
      record3_model l dq₀ v₀ dq₁ v₁ (DfracOwn 1) v
    }}}.
  Proof.
    iSteps.
  Qed.
End zebre_G.

#[global] Opaque record3_make.

#[global] Opaque record3_model.
