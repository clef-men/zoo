Require Import zoo.prelude.
Require Import zoo.iris.diaframe.
Require Export zoo.program_logic.bwp_adequacy.
Require Export zoo.program_logic.wp.
Require Import zoo.options.

Implicit Types e : expr.
Implicit Types v : val.
Implicit Types σ : state.

Lemma wp𑁒adequacy' `{inv_Gpre : !invGpreS Σ} e σ :
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
  apply: bwp𑁒adequacy' => inv۰G κs.
  iMod H as "(%zoo۰G & %Φ & <- & Hinterp & Hwp)".
  iExists zoo۰G, Φ. iFrameSteps.
  iApply (wp𑁒bwp with "Hwp").
Qed.
Lemma wp𑁒adequacy `{zoo۰Gpre : !ZooGpre Σ} {e σ} v :
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
  apply: wp𑁒adequacy' => // Hinv_G κs.
  iMod (state_interp𑁒init σ v κs) as "(%zoo۰G & <- & Hinterp & Hheap & Hlocals)"; first done.
  iDestruct (Hwp zoo۰G) as "(%Φ & Hwp)".
  iExists zoo۰G, Φ. iFrameSteps.
Qed.
