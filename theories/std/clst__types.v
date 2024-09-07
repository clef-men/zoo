From zoo Require Import
  prelude.
From zoo.language Require Import
  notations.
From zoo Require Import
  options.

Notation "'ClstClosed'" := (
  in_type "t" 0
)(in custom zoo_tag
).
Notation "'ClstOpen'" := (
  in_type "t" 1
)(in custom zoo_tag
).
Notation "'ClstCons'" := (
  in_type "t" 2
)(in custom zoo_tag
).
