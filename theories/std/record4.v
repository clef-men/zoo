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

Definition record4_make : val :=
  λ: "v₀" "v₁" "v₂" "v₃",
    let: "l" := Alloc #4 "v₀" in
    "l".[#1] <- "v₁" ;;
    "l".[#2] <- "v₂" ;;
    "l".[#3] <- "v₃" ;;
    "l".

Section zebra_G.
  Context `{zebra_G : !ZebraG Σ}.

  Definition record4_model l dq₀ v₀ dq₁ v₁ dq₂ v₂ dq₃ v₃ : iProp Σ :=
    l.[0] ↦{dq₀} v₀ ∗
    l.[1] ↦{dq₁} v₁ ∗
    l.[2] ↦{dq₂} v₂ ∗
    l.[3] ↦{dq₃} v₃.
  Definition record4_model' l dq v₀ v₁ v₂ v₃ :=
    record4_model l dq v₀ dq v₁ dq v₂ dq v₃.

  Lemma record4_model_eq l dq₀ v₀ dq₁ v₁ dq₂ v₂ dq₃ v₃ :
    record4_model l dq₀ v₀ dq₁ v₁ dq₂ v₂ dq₃ v₃ ⊣⊢
      l.[0] ↦{dq₀} v₀ ∗
      l.[1] ↦{dq₁} v₁ ∗
      l.[2] ↦{dq₂} v₂ ∗
      l.[3] ↦{dq₃} v₃.
  Proof.
    iSteps.
  Qed.
  Lemma record4_model_eq_1 l dq₀ v₀ dq₁ v₁ dq₂ v₂ dq₃ v₃ :
    record4_model l dq₀ v₀ dq₁ v₁ dq₂ v₂ dq₃ v₃ ⊢
      l.[0] ↦{dq₀} v₀ ∗
      l.[1] ↦{dq₁} v₁ ∗
      l.[2] ↦{dq₂} v₂ ∗
      l.[3] ↦{dq₃} v₃.
  Proof.
    iSteps.
  Qed.
  Lemma record4_model_eq_2 l dq₀ v₀ dq₁ v₁ dq₂ v₂ dq₃ v₃ :
    l.[0] ↦{dq₀} v₀ -∗
    l.[1] ↦{dq₁} v₁ -∗
    l.[2] ↦{dq₂} v₂ -∗
    l.[3] ↦{dq₃} v₃ -∗
    record4_model l dq₀ v₀ dq₁ v₁ dq₂ v₂ dq₃ v₃.
  Proof.
    iSteps.
  Qed.

  #[global] Instance record4_model_timeless l dq₀ v₀ dq₁ v₁ dq₂ v₂ dq₃ v₃ :
    Timeless (record4_model l dq₀ v₀ dq₁ v₁ dq₂ v₂ dq₃ v₃).
  Proof.
    apply _.
  Qed.
  #[global] Instance record4_model_persistent l v₀ v₁ v₂ v₃ :
    Persistent (record4_model' l DfracDiscarded v₀ v₁ v₂ v₃).
  Proof.
    apply _.
  Qed.

  #[global] Instance record4_model_fractional₀ l v₀ v₁ v₂ v₃ :
    Fractional (λ q₀, record4_model l (DfracOwn q₀) v₀ DfracDiscarded v₁ DfracDiscarded v₂ DfracDiscarded v₃).
  Proof.
    apply _.
  Qed.
  #[global] Instance record4_model_as_fractional₀ l q₀ v₀ v₁ v₂ v₃ :
    AsFractional (record4_model l (DfracOwn q₀) v₀ DfracDiscarded v₁ DfracDiscarded v₂ DfracDiscarded v₃) (λ q₀, record4_model l (DfracOwn q₀) v₀ DfracDiscarded v₁ DfracDiscarded v₂ DfracDiscarded v₃) q₀.
  Proof.
    split; done || apply _.
  Qed.
  #[global] Instance record4_model_fractional₁ l v₀ v₁ v₂ v₃ :
    Fractional (λ q₁, record4_model l DfracDiscarded v₀ (DfracOwn q₁) v₁ DfracDiscarded v₂ DfracDiscarded v₃).
  Proof.
    apply _.
  Qed.
  #[global] Instance record4_model_as_fractional₁ l v₀ q₁ v₁ v₂ v₃ :
    AsFractional (record4_model l DfracDiscarded v₀ (DfracOwn q₁) v₁ DfracDiscarded v₂ DfracDiscarded v₃) (λ q₁, record4_model l DfracDiscarded v₀ (DfracOwn q₁) v₁ DfracDiscarded v₂ DfracDiscarded v₃) q₁.
  Proof.
    split; done || apply _.
  Qed.
  #[global] Instance record4_model_fractional₂ l v₀ v₁ v₂ v₃ :
    Fractional (λ q₂, record4_model l DfracDiscarded v₀ DfracDiscarded v₁ (DfracOwn q₂) v₂ DfracDiscarded v₃).
  Proof.
    apply _.
  Qed.
  #[global] Instance record4_model_as_fractional₂ l v₀ v₁ q₂ v₂ v₃ :
    AsFractional (record4_model l DfracDiscarded v₀ DfracDiscarded v₁ (DfracOwn q₂) v₂ DfracDiscarded v₃) (λ q₂, record4_model l DfracDiscarded v₀ DfracDiscarded v₁ (DfracOwn q₂) v₂ DfracDiscarded v₃) q₂.
  Proof.
    split; done || apply _.
  Qed.
  #[global] Instance record4_model_fractional₃ l v₀ v₁ v₂ v₃ :
    Fractional (λ q₃, record4_model l DfracDiscarded v₀ DfracDiscarded v₁ DfracDiscarded v₂ (DfracOwn q₃) v₃).
  Proof.
    apply _.
  Qed.
  #[global] Instance record4_model_as_fractional₃ l v₀ v₁ v₂ q₃ v₃ :
    AsFractional (record4_model l DfracDiscarded v₀ DfracDiscarded v₁ DfracDiscarded v₂ (DfracOwn q₃) v₃) (λ q₃, record4_model l DfracDiscarded v₀ DfracDiscarded v₁ DfracDiscarded v₂ (DfracOwn q₃) v₃) q₃.
  Proof.
    split; done || apply _.
  Qed.
  #[global] Instance record4_model_fractional l v₀ v₁ v₂ v₃ :
    Fractional (λ q, record4_model' l (DfracOwn q) v₀ v₁ v₂ v₃).
  Proof.
    apply _.
  Qed.
  #[global] Instance record4_model_as_fractional l q v₀ v₁ v₂ v₃ :
    AsFractional (record4_model' l (DfracOwn q) v₀ v₁ v₂ v₃) (λ q, record4_model' l (DfracOwn q) v₀ v₁ v₂ v₃) q.
  Proof.
    split; done || apply _.
  Qed.

  Lemma record4_model_valid l dq₀ v₀ dq₁ v₁ dq₂ v₂ dq₃ v₃ :
    record4_model l dq₀ v₀ dq₁ v₁ dq₂ v₂ dq₃ v₃ ⊢
    ⌜✓ dq₀ ∧ ✓ dq₁ ∧ ✓ dq₂ ∧ ✓ dq₃⌝.
  Proof.
    iIntros "(Hv₀ & Hv₁ & Hv₂ & Hv₃)".
    iDestruct (mapsto_valid with "Hv₀") as %Hdq₀.
    iDestruct (mapsto_valid with "Hv₁") as %Hdq₁.
    iDestruct (mapsto_valid with "Hv₂") as %Hdq₂.
    iDestruct (mapsto_valid with "Hv₃") as %Hdq₃.
    iSteps.
  Qed.
  Lemma record4_model_combine l dq₀1 v₀1 dq₁1 v₁1 dq₂1 v₂1 dq₃1 v₃1 dq₀2 v₀2 dq₁2 v₁2 dq₂2 v₂2 dq₃2 v₃2 :
    record4_model l dq₀1 v₀1 dq₁1 v₁1 dq₂1 v₂1 dq₃1 v₃1 -∗
    record4_model l dq₀2 v₀2 dq₁2 v₁2 dq₂2 v₂2 dq₃2 v₃2 -∗
      record4_model l (dq₀1 ⋅ dq₀2) v₀1 (dq₁1 ⋅ dq₁2) v₁1 (dq₂1 ⋅ dq₂2) v₂1 (dq₃1 ⋅ dq₃2) v₃1 ∗
      ⌜v₀1 = v₀2 ∧ v₁1 = v₁2 ∧ v₂1 = v₂2 ∧ v₃1 = v₃2⌝.
  Proof.
    iIntros "(Hv₀1 & Hv₁1 & Hv₂1 & Hv₃1) (Hv₀2 & Hv₁2 & Hv₂2 & Hv₃2)".
    iDestruct (mapsto_combine with "Hv₀1 Hv₀2") as "(Hv₀ & <-)".
    iDestruct (mapsto_combine with "Hv₁1 Hv₁2") as "(Hv₁ & <-)".
    iDestruct (mapsto_combine with "Hv₂1 Hv₂2") as "(Hv₂ & <-)".
    iDestruct (mapsto_combine with "Hv₃1 Hv₃2") as "(Hv₃ & <-)".
    iSteps.
  Qed.
  Lemma record4_model_valid_2 l dq₀1 v₀1 dq₁1 v₁1 dq₂1 v₂1 dq₃1 v₃1 dq₀2 v₀2 dq₁2 v₁2 dq₂2 v₂2 dq₃2 v₃2 :
    record4_model l dq₀1 v₀1 dq₁1 v₁1 dq₂1 v₂1 dq₃1 v₃1 -∗
    record4_model l dq₀2 v₀2 dq₁2 v₁2 dq₂2 v₂2 dq₃2 v₃2 -∗
    ⌜✓ (dq₀1 ⋅ dq₀2) ∧ ✓ (dq₁1 ⋅ dq₁2) ∧ ✓ (dq₂1 ⋅ dq₂2) ∧ ✓ (dq₃1 ⋅ dq₃2) ∧ v₀1 = v₀2 ∧ v₁1 = v₁2 ∧ v₂1 = v₂2 ∧ v₃1 = v₃2⌝.
  Proof.
    iIntros "Hl1 Hl2".
    iDestruct (record4_model_combine with "Hl1 Hl2") as "(Hl & %)".
    iDestruct (record4_model_valid with "Hl") as %?.
    naive_solver.
  Qed.
  Lemma record4_model_agree l dq₀1 v₀1 dq₁1 v₁1 dq₂1 v₂1 dq₃1 v₃1 dq₀2 v₀2 dq₁2 v₁2 dq₂2 v₂2 dq₃2 v₃2 :
    record4_model l dq₀1 v₀1 dq₁1 v₁1 dq₂1 v₂1 dq₃1 v₃1 -∗
    record4_model l dq₀2 v₀2 dq₁2 v₁2 dq₂2 v₂2 dq₃2 v₃2 -∗
    ⌜v₀1 = v₀2 ∧ v₁1 = v₁2 ∧ v₂1 = v₂2 ∧ v₃1 = v₃2⌝.
  Proof.
    iSteps.
  Qed.
  Lemma record4_model_dfrac_ne l1 dq₀1 v₀1 dq₁1 v₁1 dq₂1 v₂1 dq₃1 v₃1 l2 dq₀2 v₀2 dq₁2 v₁2 dq₂2 v₂2 dq₃2 v₃2 :
    ¬ ✓ (dq₀1 ⋅ dq₀2) ∨ ¬ ✓ (dq₁1 ⋅ dq₁2) ∨ ¬ ✓ (dq₂1 ⋅ dq₂2) ∨ ¬ ✓ (dq₃1 ⋅ dq₃2) →
    record4_model l1 dq₀1 v₀1 dq₁1 v₁1 dq₂1 v₂1 dq₃1 v₃1 -∗
    record4_model l2 dq₀2 v₀2 dq₁2 v₁2 dq₂2 v₂2 dq₃2 v₃2 -∗
    ⌜l1 ≠ l2⌝.
  Proof.
    iIntros "% Hl1 Hl2" (->).
    iDestruct (record4_model_valid_2 with "Hl1 Hl2") as %?.
    naive_solver.
  Qed.
  Lemma record4_model_ne l1 dq₀1 v₀1 dq₁1 v₁1 dq₂1 v₂1 dq₃1 v₃1 l2 dq₀2 v₀2 dq₁2 v₁2 dq₂2 v₂2 dq₃2 v₃2 :
    dq₀1 = DfracOwn 1 ∨ dq₁1 = DfracOwn 1 ∨ dq₂1 = DfracOwn 1 ∨ dq₃1 = DfracOwn 1 →
    record4_model l1 dq₀1 v₀1 dq₁1 v₁1 dq₂1 v₂1 dq₃1 v₃1 -∗
    record4_model l2 dq₀2 v₀2 dq₁2 v₁2 dq₂2 v₂2 dq₃2 v₃2 -∗
    ⌜l1 ≠ l2⌝.
  Proof.
    intros [| [| []]]; iSteps.
  Qed.
  Lemma record4_model_exclusive l dq₀1 v₀1 dq₁1 v₁1 dq₂1 v₂1 dq₃1 v₃1 dq₀2 v₀2 dq₁2 v₁2 dq₂2 v₂2 dq₃2 v₃2 :
    dq₀1 = DfracOwn 1 ∨ dq₁1 = DfracOwn 1 ∨ dq₂1 = DfracOwn 1 ∨ dq₃1 = DfracOwn 1 →
    record4_model l dq₀1 v₀1 dq₁1 v₁1 dq₂1 v₂1 dq₃1 v₃1 -∗
    record4_model l dq₀2 v₀2 dq₁2 v₁2 dq₂2 v₂2 dq₃2 v₃2 -∗
    False.
  Proof.
    intros [| [| []]]; iSteps.
  Qed.
  Lemma record4_model_persist₀ l dq₀ v₀ dq₁ v₁ dq₂ v₂ dq₃ v₃ :
    record4_model l dq₀ v₀ dq₁ v₁ dq₂ v₂ dq₃ v₃ ⊢ |==>
    record4_model l DfracDiscarded v₀ dq₁ v₁ dq₂ v₂ dq₃ v₃.
  Proof.
    iSteps.
  Qed.
  Lemma record4_model_persist₁ l dq₀ v₀ dq₁ v₁ dq₂ v₂ dq₃ v₃ :
    record4_model l dq₀ v₀ dq₁ v₁ dq₂ v₂ dq₃ v₃ ⊢ |==>
    record4_model l dq₀ v₀ DfracDiscarded v₁ dq₂ v₂ dq₃ v₃.
  Proof.
    iSteps.
  Qed.
  Lemma record4_model_persist₂ l dq₀ v₀ dq₁ v₁ dq₂ v₂ dq₃ v₃ :
    record4_model l dq₀ v₀ dq₁ v₁ dq₂ v₂ dq₃ v₃ ⊢ |==>
    record4_model l dq₀ v₀ dq₁ v₁ DfracDiscarded v₂ dq₃ v₃.
  Proof.
    iSteps.
  Qed.
  Lemma record4_model_persist₃ l dq₀ v₀ dq₁ v₁ dq₂ v₂ dq₃ v₃ :
    record4_model l dq₀ v₀ dq₁ v₁ dq₂ v₂ dq₃ v₃ ⊢ |==>
    record4_model l dq₀ v₀ dq₁ v₁ dq₂ v₂ DfracDiscarded v₃.
  Proof.
    iSteps.
  Qed.
  Lemma record4_model_persist l dq₀ v₀ dq₁ v₁ dq₂ v₂ dq₃ v₃ :
    record4_model l dq₀ v₀ dq₁ v₁ dq₂ v₂ dq₃ v₃ ⊢ |==>
    record4_model l DfracDiscarded v₀ DfracDiscarded v₁ DfracDiscarded v₂ DfracDiscarded v₃.
  Proof.
    iSteps.
  Qed.

  Lemma record4_make_spec v₀ v₁ v₂ v₃ :
    {{{ True }}}
      record4_make v₀ v₁ v₂ v₃
    {{{ l,
      RET #l;
      record4_model' l (DfracOwn 1) v₀ v₁ v₂ v₃ ∗
      meta_token l ⊤
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_rec. wp_pures.
    wp_apply (wp_alloc with "[//]") as "%l (Hmeta & Hl)"; first done.
    iSteps.
  Qed.

  Lemma record4_get_spec₀ l dq₀ v₀ dq₁ v₁ dq₂ v₂ dq₃ v₃ :
    {{{
      record4_model l dq₀ v₀ dq₁ v₁ dq₂ v₂ dq₃ v₃
    }}}
      !#l.[0]
    {{{
      RET v₀;
      record4_model l dq₀ v₀ dq₁ v₁ dq₂ v₂ dq₃ v₃
    }}}.
  Proof.
    iSteps.
  Qed.
  Lemma record4_get_spec₁ l dq₀ v₀ dq₁ v₁ dq₂ v₂ dq₃ v₃ :
    {{{
      record4_model l dq₀ v₀ dq₁ v₁ dq₂ v₂ dq₃ v₃
    }}}
      !#l.[1]
    {{{
      RET v₁;
      record4_model l dq₀ v₀ dq₁ v₁ dq₂ v₂ dq₃ v₃
    }}}.
  Proof.
    iSteps.
  Qed.
  Lemma record4_get_spec₂ l dq₀ v₀ dq₁ v₁ dq₂ v₂ dq₃ v₃ :
    {{{
      record4_model l dq₀ v₀ dq₁ v₁ dq₂ v₂ dq₃ v₃
    }}}
      !#l.[2]
    {{{
      RET v₂;
      record4_model l dq₀ v₀ dq₁ v₁ dq₂ v₂ dq₃ v₃
    }}}.
  Proof.
    iSteps.
  Qed.
  Lemma record4_get_spec₃ l dq₀ v₀ dq₁ v₁ dq₂ v₂ dq₃ v₃ :
    {{{
      record4_model l dq₀ v₀ dq₁ v₁ dq₂ v₂ dq₃ v₃
    }}}
      !#l.[3]
    {{{
      RET v₃;
      record4_model l dq₀ v₀ dq₁ v₁ dq₂ v₂ dq₃ v₃
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma record4_set_spec₀ l v₀ dq₁ v₁ dq₂ v₂ dq₃ v₃ v :
    {{{
      record4_model l (DfracOwn 1) v₀ dq₁ v₁ dq₂ v₂ dq₃ v₃
    }}}
      #l.[0] <- v
    {{{
      RET #();
      record4_model l (DfracOwn 1) v dq₁ v₁ dq₂ v₂ dq₃ v₃
    }}}.
  Proof.
    iSteps.
  Qed.
  Lemma record4_set_spec₁ l dq₀ v₀ v₁ dq₂ v₂ dq₃ v₃ v :
    {{{
      record4_model l dq₀ v₀ (DfracOwn 1) v₁ dq₂ v₂ dq₃ v₃
    }}}
      #l.[1] <- v
    {{{
      RET #();
      record4_model l dq₀ v₀ (DfracOwn 1) v dq₂ v₂ dq₃ v₃
    }}}.
  Proof.
    iSteps.
  Qed.
  Lemma record4_set_spec₂ l dq₀ v₀ dq₁ v₁ v₂ dq₃ v₃ v :
    {{{
      record4_model l dq₀ v₀ dq₁ v₁ (DfracOwn 1) v₂ dq₃ v₃
    }}}
      #l.[2] <- v
    {{{
      RET #();
      record4_model l dq₀ v₀ dq₁ v₁ (DfracOwn 1) v dq₃ v₃
    }}}.
  Proof.
    iSteps.
  Qed.
  Lemma record4_set_spec₃ l dq₀ v₀ dq₁ v₁ dq₂ v₂ v₃ v :
    {{{
      record4_model l dq₀ v₀ dq₁ v₁ dq₂ v₂ (DfracOwn 1) v₃
    }}}
      #l.[3] <- v
    {{{
      RET #();
      record4_model l dq₀ v₀ dq₁ v₁ dq₂ v₂ (DfracOwn 1) v
    }}}.
  Proof.
    iSteps.
  Qed.
End zebra_G.

#[global] Opaque record4_make.

#[global] Opaque record4_model.
