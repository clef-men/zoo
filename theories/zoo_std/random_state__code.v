Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo.options.

Parameter random_state٠create : val.

Parameter random_state٠bits : val.

Parameter random_state٠int : val.

Definition random_state٠int_in_range : val :=
  𝗳𝘂𝗻 "t" "lb" "ub" ->
    "lb" + random_state٠int "t" ("ub" - "lb").
