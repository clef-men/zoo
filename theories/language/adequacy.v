From iris.program_logic Require Export
  adequacy.

From zebra Require Import
  prelude.
From zebra.iris Require Import
  diaframe.
From zebra Require Export
  language.
From zebra.language Require Import
  rules.
From zebra Require Import
  options.

Implicit Types e : expr.
Implicit Types v : val.
Implicit Types σ : state.

Definition zebra_adequacy Σ `{zebra_Gpre : !ZebraGpre Σ} e σ ϕ :
  ( ∀ `{zebra_G : !ZebraG Σ},
    ⊢ WP e @ ⊤ {{ v, ⌜ϕ v⌝ }}
  ) →
  adequate NotStuck e σ (λ v σ, ϕ v).
Proof.
  intros Hwp.
  apply adequate_alt. intros t2 σ2 (n & (κ & ?))%erased_steps_nsteps.
  eapply (wp_strong_adequacy Σ _); last done.
  iIntros "%Hinv_G".
  iMod zebra_init as "(%zebra_G & Hsi)".
  iDestruct (Hwp (Build_ZebraG Σ)) as "Hwp".
  iModIntro.
  iExists zebra_state_interp, [(λ v, ⌜ϕ v⌝%I)], (λ _, True%I), _ => /=.
  iFrame. iStep. iIntros (es' t2' -> Hes' Hnot_stuck) " _ Hϕ _".
  iApply fupd_mask_intro_discard; first done. iSplit; last done.
  iDestruct (big_sepL2_cons_inv_r with "Hϕ") as (e' ? ->) "(Hϕ & _)".
  iIntros (v2 t2'' [= -> <-]). rewrite to_of_val //.
Qed.
