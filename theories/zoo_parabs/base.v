From iris.base_logic Require Export
  lib.invariants.

From zoo Require Import
  prelude.
From zoo.program_logic Require Export
  wp.
From zoo Require Import
  options.

Inductive status :=
  | Blocked
  | Nonblocked.

Inductive emptiness :=
  | Empty
  | Nonempty.
