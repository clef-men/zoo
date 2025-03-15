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

Definition zoo_adequacy `{zoo_Gpre : !ZooGpre Σ} e σ v :
  σ.(state_locals) = [v] →
  ( ∀ `{zoo_G : !ZooG Σ},
    0 ↦ₗ v -∗
    WP e ∶ 0 {{ v, True }}
  ) →
  safe ([e], σ).
Proof.
  intros Hlocals Hwp.
  apply: wp_adequacy => // Hinv_G κs.
  iMod (zoo_init' σ v κs) as "(%zoo_G & Hσ & Htid)"; first done.
  iExists zoo_state_interp. repeat iExists _. iFrame.
  iApply (Hwp (Build_ZooG _ _) with "Htid").
Qed.
