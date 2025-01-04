From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo Require Import
  options.

Notation "'Null'" := (
  in_type "node" 0
)(in custom zoo_tag
).
Notation "'Node'" := (
  in_type "node" 1
)(in custom zoo_tag
).

Notation "'next'" := (
  in_type "node__Node" 0
)(in custom zoo_field
).
Notation "'data'" := (
  in_type "node__Node" 1
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
