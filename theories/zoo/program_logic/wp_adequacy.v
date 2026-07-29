Require Import zoo.prelude.
Require Import zoo.iris.diaframe.
Require Export zoo.program_logic.bwp_adequacy.
Require Export zoo.program_logic.wp.
Require Import zoo.options.

Implicit Type e : expr.
Implicit Type v : val.
Implicit Type σ : state.

Lemma wpｰadequacy' `{inv_Gpre : !invGpreS Σ} e σ :
  ( ∀ `{inv۰G : !invGS Σ} κs,
    ⊢ |={⊤}=>
      ∃ (zoo۰G : ZooG Σ) Φ,
      ⌜zoo۰G.(zoo۰G۰inv۰G) = inv۰G⌝ ∗
      state_interp 0 1 σ κs ∗
      WP e ∶ 0 {{ Φ }}
  ) →
  safe ([e], σ).
Proof.
  intros H.
  apply: bwpｰadequacy' => inv۰G κs.
  iMod H as "(%zoo۰G & %Φ & <- & Hinterp & Hwp)".
  iExists zoo۰G, Φ. iFrameSteps.
  iApply (wpｰbwp with "Hwp").
Qed.
Lemma wpｰadequacy `{zoo۰Gpre : !ZooGpre Σ} {e σ} v :
  state۰wf σ v →
  ( ∀ `{zoo۰G : !ZooG Σ},
    ⊢ ∃ Φ,
      ([∗ map] l ↦ v ∈ state۰heap۰initial σ, l ↦ v) -∗
      0 ↦ₗ v -∗
      WP e ∶ 0 {{ Φ }}
  ) →
  safe ([e], σ).
Proof.
  intros Hwf Hwp.
  apply: wpｰadequacy' => // Hinv_G κs.
  iMod (state_interpｰinit σ v κs) as "(%zoo۰G & <- & Hinterp & Hheap & Hlocals)"; first done.
  iDestruct (Hwp zoo۰G) as "(%Φ & Hwp)".
  iExists zoo۰G, Φ. iFrameSteps.
Qed.
