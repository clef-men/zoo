From zoo Require Import
  prelude.
From zoo.iris.program_logic Require Export
  wp_adequacy.
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

Definition zoo_adequacy `{zoo_Gpre : !ZooGpre Σ} {e σ} param :
  state_wf σ param →
  ( ∀ `{zoo_G : !ZooG Σ},
    ( [∗ map] l ↦ v ∈ state_heap_initial σ,
      l ↦ v
    ) -∗
    0 ↦ₗ param.(zoo_parameter_local) -∗
    WP e ∶ 0 {{ _, True }}
  ) →
  safe ([e], σ).
Proof.
  intros Hwf Hwp.
  apply: wp_adequacy => // Hinv_G κs.
  iMod (zoo_init σ param κs) as "(%zoo_G & <- & Hinterp & Hheap & Hlocals)"; first done.
  iExists zoo_state_interp, (λ _, True)%I, (λ _, True)%I. iFrame.
  iApply (Hwp with "Hheap Hlocals").
Qed.
