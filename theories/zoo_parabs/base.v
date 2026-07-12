Require Export iris.base_logic.lib.invariants.

Require Import zoo.prelude.
Require Export zoo.program_logic.wp.
Require Import zoo.options.

Variant status :=
  | Blocked
  | Nonblocked.

Variant emptiness :=
  | Empty
  | Nonempty.
