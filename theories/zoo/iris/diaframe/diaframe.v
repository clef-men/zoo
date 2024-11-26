From diaframe Require Export
  proofmode_base.

From zoo Require Import
  prelude.
From zoo.iris Require Export
  proofmode.
From zoo Require Import
  options.

(* FIXME: some goals are solved by [done] but not by [iSmash] *)
Tactic Notation "iSmash+" :=
  done || iSmash.
