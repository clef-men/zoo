Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo.options.

Notation "'None'" := (
  in_type "zoo_std.goption.t" 0
)(in custom zoo_tag
).
Notation "'Some'" := (
  in_type "zoo_std.goption.t" 1
)(in custom zoo_tag
).
