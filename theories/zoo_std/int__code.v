From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  int__types.
From zoo Require Import
  options.

Definition int_min : val :=
  fun: "n1" "n2" =>
    if: "n1" < "n2" then (
      "n1"
    ) else (
      "n2"
    ).

Definition int_max : val :=
  fun: "n1" "n2" =>
    if: "n1" < "n2" then (
      "n2"
    ) else (
      "n1"
    ).

Definition int_positive_part : val :=
  fun: "t" =>
    int_max 0 "t".
