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

Notation "'head'" := (
  in_type "node__Node" 0
)(in custom zoo_field
).
Notation "'tail'" := (
  in_type "node__Node" 1
)(in custom zoo_field
).

Notation "'front'" := (
  in_type "t" 0
)(in custom zoo_field
).
Notation "'sentinel'" := (
  in_type "t" 1
)(in custom zoo_field
).
