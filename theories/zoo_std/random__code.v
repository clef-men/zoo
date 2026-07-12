Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.random__types.
Require Import zoo.options.

Parameter random٠init : val.

Parameter random٠bits : val.

Parameter random٠int : val.

Definition random٠int_in_range : val :=
  fun: "lb" "ub" =>
    "lb" + random٠int ("ub" - "lb").
