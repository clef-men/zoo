Require Import zoo.prelude.
Require Import zoo.base.
Require Export zoo_std.sys__code.
Require Import zoo_std.sys__types.
Require Import zoo.options.

Axiom sys٠max_array_lengthｰspec :
  ∃ n : nat,
  sys٠max_array_length = #n.

Require zoo_std.sys__opaque.
