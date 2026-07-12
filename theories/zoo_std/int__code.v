Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.int__types.
Require Import zoo.options.

Definition int٠min : val :=
  fun: "n1" "n2" =>
    if: "n1" < "n2" then (
      "n1"
    ) else (
      "n2"
    ).

Definition int٠max : val :=
  fun: "n1" "n2" =>
    if: "n1" < "n2" then (
      "n2"
    ) else (
      "n1"
    ).

Definition int٠positive_part : val :=
  fun: "t" =>
    int٠max 0 "t".
