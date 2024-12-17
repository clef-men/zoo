From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  random_state__types.
From zoo Require Import
  options.

Parameter random_state_create : val.

Parameter random_state_bits : val.

Parameter random_state_int : val.

Definition random_state_int_in_range : val :=
  fun: "t" "lb" "ub" =>
    "lb" + random_state_int "t" ("ub" - "lb").
