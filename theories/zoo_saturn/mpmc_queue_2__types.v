From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  domain.
From zoo Require Import
  options.

Notation "'Front'" := (
  in_type "front" 0
)(in custom zoo_tag
).
Notation "'Cons'" := (
  in_type "front" 1
)(in custom zoo_tag
).

Notation "'Back'" := (
  in_type "back" 0
)(in custom zoo_tag
).
Notation "'Snoc'" := (
  in_type "back" 1
)(in custom zoo_tag
).
Notation "'Used'" := (
  in_type "back" 2
)(in custom zoo_tag
).

Notation "'index'" := (
  in_type "back__Back" 0
)(in custom zoo_field
).
Notation "'move'" := (
  in_type "back__Back" 1
)(in custom zoo_field
).

Notation "'front'" := (
  in_type "t" 0
)(in custom zoo_field
).
Notation "'back'" := (
  in_type "t" 1
)(in custom zoo_field
).
