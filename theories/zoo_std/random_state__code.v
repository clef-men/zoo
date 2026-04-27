From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  random_state__types.
From zoo Require Import
  options.

Parameter random_state٠create : val.

Parameter random_state٠bits : val.

Parameter random_state٠int : val.

Definition random_state٠int_in_range : val :=
  fun: "t" "lb" "ub" =>
    "lb" + random_state٠int "t" ("ub" - "lb").
