Require Export iris.base_logic.lib.fancy_updates.

Require Import zoo.prelude.
Require Export zoo.iris.base_logic.lib.base.
Require Import zoo.iris.diaframe.
Require Import zoo.options.

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
