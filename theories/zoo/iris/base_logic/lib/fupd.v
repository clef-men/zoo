From iris.base_logic Require Export
  lib.fancy_updates.

From zoo Require Import
  prelude.
From zoo.iris.base_logic Require Export
  lib.base.
From zoo.iris Require Import
  diaframe.
From zoo Require Import
  options.

Lemma lc_fupd_elim_laterN `{inv_G : invGS Σ} n P E :
  £ n -∗
  ▷^n P ={E}=∗
  P.
Proof.
  iIntros "H£s HP".
  iInduction n as [| n IH].
  - iSteps.
  - iDestruct "H£s" as "(H£ & H£s)".
    iMod (lc_fupd_elim_later with "H£ HP") as "HP".
    iSteps.
Qed.
