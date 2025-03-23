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

Definition zoo_adequacy `{zoo_Gpre : !ZooGpre Σ} e σ v cnt :
  σ.(state_locals) = [v] →
  σ.(state_heap) !! zoo_counter = Some (ValNat cnt) →
  ( ∀ `{zoo_G : !ZooG Σ},
    ( [∗ map] l ↦ v ∈ delete zoo_counter σ.(state_heap),
      l ↦ v
    ) -∗
    0 ↦ₗ v -∗
    WP e ∶ 0 {{ v, True }}
  ) →
  safe ([e], σ).
Proof.
  intros Hlocals Hcounter Hwp.
  apply: wp_adequacy => // Hinv_G κs.
  iMod (zoo_init' σ v cnt κs) as "(%zoo_G & <- & Hσ & Hheap & Hlocals)"; [done.. |].
  iExists zoo_state_interp, (λ _, True)%I, (λ _, True)%I. iFrame.
  iApply (Hwp with "Hheap Hlocals").
Qed.
