From diaframe Require Export
  proofmode_base.

From zoo Require Import
  prelude.
From zoo.iris Require Export
  proofmode.
From zoo Require Import
  options.

Tactic Notation "iFrameSteps" integer(n) :=
  do n iFrame; iSteps.
Tactic Notation "iFrameSteps" :=
  iFrameSteps 1.
