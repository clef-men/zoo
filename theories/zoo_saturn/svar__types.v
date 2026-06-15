From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo Require Import
  identifier.
From zoo Require Import
  options.

Notation "'snapshot_value'" := (
  in_type "zoo_saturn.svar.snapshot" 0
)(in custom zoo_proj
).
Notation "'snapshot_gen'" := (
  in_type "zoo_saturn.svar.snapshot" 1
)(in custom zoo_proj
).

Notation "'Forward'" := (
  in_type "zoo_saturn.svar.prophecy" 0
)(in custom zoo_tag
).
Notation "'Set'" := (
  in_type "zoo_saturn.svar.prophecy" 1
)(in custom zoo_tag
).

Notation "'value'" := (
  in_type "zoo_saturn.svar.t" 0
)(in custom zoo_field
).
Notation "'gen'" := (
  in_type "zoo_saturn.svar.t" 1
)(in custom zoo_field
).
Notation "'snapshot'" := (
  in_type "zoo_saturn.svar.t" 2
)(in custom zoo_field
).
Notation "'proph'" := (
  in_type "zoo_saturn.svar.t" 3
)(in custom zoo_field
).
