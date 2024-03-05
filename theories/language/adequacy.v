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
  apply: wp_adequacy => Hinv_G κs.
  iMod zebre_init as "(%zebre_G & Hσ)".
  iExists zebre_state_interp, (λ _, True%I). iFrame.
  iApply (Hwp (Build_ZebreG Σ)).
Qed.
