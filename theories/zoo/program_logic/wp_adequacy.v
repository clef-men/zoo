From zoo Require Import
  prelude.
From zoo.iris Require Import
  diaframe.
From zoo.program_logic Require Export
  bwp_adequacy
  wp.
From zoo Require Import
  options.

Implicit Types e : expr.
Implicit Types v : val.
Implicit Types σ : state.

Lemma wp_adequacy' `{inv_Gpre : !invGpreS Σ} e σ :
  ( ∀ `{inv_G : !invGS Σ} κs,
    ⊢ |={⊤}=>
      ∃ (zoo_G : ZooG Σ) Φ,
      ⌜zoo_G.(zoo_G_inv_G) = inv_G⌝ ∗
      state_interp 0 1 σ κs ∗
      WP e ∶ 0 {{ Φ }}
  ) →
  safe ([e], σ).
Proof.
  intros H.
  apply: bwp_adequacy' => inv_G κs.
  iMod H as "(%zoo_G & %Φ & <- & Hinterp & Hwp)".
  iExists zoo_G, Φ. iFrameSteps.
  iApply (wp_bwp with "Hwp").
Qed.
Lemma wp_adequacy `{zoo_Gpre : !ZooGpre Σ} {e σ} param :
  state_wf σ param →
  ( ∀ `{zoo_G : !ZooG Σ},
    ⊢ ∃ Φ,
      ([∗ map] l ↦ v ∈ state_heap_initial σ, l ↦ v) -∗
      0 ↦ₗ param.(zoo_parameter_local) -∗
      WP e ∶ 0 {{ Φ }}
  ) →
  safe ([e], σ).
Proof.
  intros Hwf Hwp.
  apply: wp_adequacy' => // Hinv_G κs.
  iMod (zoo_init σ param κs) as "(%zoo_G & <- & Hinterp & Hheap & Hlocals)"; first done.
  iDestruct (Hwp zoo_G) as "(%Φ & Hwp)".
  iExists zoo_G, Φ. iFrameSteps.
Qed.
