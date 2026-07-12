Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo.options.

Notation "'Nothing'" := (
  in_type "zoo_std.optional.t" 0
)(in custom zoo_tag
).
Notation "'Anything'" := (
  in_type "zoo_std.optional.t" 1
)(in custom zoo_tag
).
Notation "'Something'" := (
  in_type "zoo_std.optional.t" 2
)(in custom zoo_tag
).
