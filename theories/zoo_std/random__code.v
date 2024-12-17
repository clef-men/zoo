From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  random__types.
From zoo Require Import
  options.

Parameter random_init : val.

Parameter random_bits : val.

Parameter random_int : val.

Definition random_int_in_range : val :=
  fun: "lb" "ub" =>
    "lb" + random_int ("ub" - "lb").
