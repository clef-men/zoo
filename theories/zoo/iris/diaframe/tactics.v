Require Import diaframe.proofmode_base.

Require Import zoo.prelude.
Require Export zoo.iris.diaframe.base.
Require Import zoo.options.

#[local] Ltac iStep_ n_step :=
  let step := ltac2:(n_step |-
    let opts := parse_iStep_options [] in
    let n_step := Option.get (Ltac1.to_int n_step) in
    iStep_num opts n_step
  ) in
  step n_step.

Tactic Notation "iFrameStep" integer(n_step) :=
  iFrame; iStep_ n_step.
Tactic Notation "iFrameStep" :=
  iFrame; iStep_ integer:(1).

#[local] Ltac iFrameSteps_ n_frame :=
  do n_frame iFrame; iSteps.
Tactic Notation "iFrameSteps" integer(n_frame) :=
  iFrameSteps_ n_frame.
Tactic Notation "iFrameSteps" :=
  iFrameSteps_ integer:(1).

#[local] Ltac iStepFrameSteps_ n_step n_frame :=
  iStep_ n_step; iFrameSteps_ n_frame.
Tactic Notation "iStepFrameSteps" integer(n_step) integer(n_frame) :=
  iStepFrameSteps_ n_step n_frame.
Tactic Notation "iStepFrameSteps" integer(n_step) :=
  iStepFrameSteps_ n_step integer:(1).
Tactic Notation "iStepFrameSteps" :=
  iStepFrameSteps_ integer:(1) integer:(1).
