From zebre Require Import
  prelude.
From zebre.iris.program_logic Require Export
  adequacy.
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

Definition zebre_adequacy Σ `{zebre_Gpre : !ZebreGpre Σ} e σ :
  ( ∀ `{zebre_G : !ZebreG Σ},
    ⊢ WP e @ ⊤ {{ v, True }}
  ) →
  adequate e σ.
Proof.
  intros Hwp.
  apply: wp_adequacy => Hinv_G κs.
  iMod zebre_init as "(%zebre_G & Hσ)".
  iExists zebre_state_interp, (λ _, True%I), _. iFrame.
  iApply (Hwp (Build_ZebreG Σ)).
Qed.
