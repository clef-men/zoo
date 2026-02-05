From zoo Require Import
  prelude.
From zoo.iris Require Import
  diaframe.
From zoo.iris.program_logic Require Import
  bwp_adequacy.
From zoo.iris.program_logic Require Export
  wp.
From zoo Require Import
  options.

Lemma wp_adequacy Λ `{inv_Gpre : !invGpreS Σ} e σ :
  ( ∀ `{inv_G : !invGS Σ} κs,
    ⊢ |={⊤}=>
      ∃ state_interp fork_post Φ,
      let iris_G : IrisG Λ Σ := Build_IrisG state_interp fork_post in
      state_interp 1 σ κs ∗
      WP e ∶ 0 {{ Φ }}
  ) →
  safe ([e], σ).
Proof.
  intros H.
  apply: bwp_adequacy => inv_G κs.
  iMod H as "(%state_interp & %fork_post & %Φ & Hinterp & Hwp)".
  iExists state_interp, fork_post, Φ. iFrame.
  iApply (wp_bwp with "Hwp").
Qed.
