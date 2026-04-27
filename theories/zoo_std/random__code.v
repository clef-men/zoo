From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  random__types.
From zoo Require Import
  options.

Parameter random٠init : val.

Parameter random٠bits : val.

Parameter random٠int : val.

Definition random٠int_in_range : val :=
  fun: "lb" "ub" =>
    "lb" + random٠int ("ub" - "lb").
