From iris.base_logic Require Export
  lib.invariants.

From zoo Require Import
  prelude.
From zoo.program_logic Require Export
  wp.
From zoo Require Import
  options.

Variant status :=
  | Blocked
  | Nonblocked.

Variant emptiness :=
  | Empty
  | Nonempty.
