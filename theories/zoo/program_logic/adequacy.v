From zoo Require Import
  prelude.
From zoo.iris.program_logic Require Export
  adequacy.
From zoo.iris Require Import
  diaframe.
From zoo.language Require Export
  language.
From zoo.program_logic Require Import
  wp.
From zoo Require Import
  options.

Implicit Types e : expr.
Implicit Types v : val.
Implicit Types σ : state.

Definition zoo_adequacy Σ `{zoo_Gpre : !ZooGpre Σ} e σ :
  ( ∀ `{zoo_G : !ZooG Σ},
    ⊢ WP e {{ v, True }}
  ) →
  adequate e σ.
Proof.
  intros Hwp.
  apply: wp_adequacy => Hinv_G κs.
  iMod zoo_init' as "(%zoo_G & Hσ)".
  iExists zoo_state_interp. repeat iExists _. iFrame.
  iApply (Hwp (Build_ZooG _)).
Qed.
