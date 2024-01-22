From iris.program_logic Require Export
  adequacy.

From zebre Require Import
  prelude.
From zebre.iris Require Import
  diaframe.
From zebre.language Require Export
  language.
From zebre.language Require Import
  rules.
From zebre Require Import
  options.

Implicit Types e : expr.
Implicit Types v : val.
Implicit Types σ : state.

Definition zebre_adequacy Σ `{zebre_Gpre : !ZebreGpre Σ} e σ ϕ :
  ( ∀ `{zebre_G : !ZebreG Σ},
    ⊢ WP e @ ⊤ {{ v, ⌜ϕ v⌝ }}
  ) →
  adequate NotStuck e σ (λ v σ, ϕ v).
Proof.
  intros Hwp.
  apply adequate_alt. intros t2 σ2 (n & (κ & ?))%erased_steps_nsteps.
  eapply (wp_strong_adequacy Σ _); last done.
  iIntros "%Hinv_G".
  iMod zebre_init as "(%zebre_G & Hsi)".
  iDestruct (Hwp (Build_ZebreG Σ)) as "Hwp".
  iModIntro.
  iExists zebre_state_interp, [(λ v, ⌜ϕ v⌝%I)], (λ _, True%I), _ => /=.
  iFrame. iStep. iIntros (es' t2' -> Hes' Hnot_stuck) " _ Hϕ _".
  iApply fupd_mask_intro_discard; first done. iSplit; last done.
  iDestruct (big_sepL2_cons_inv_r with "Hϕ") as (e' ? ->) "(Hϕ & _)".
  iIntros (v2 t2'' [= -> <-]). rewrite to_of_val //.
Qed.
