Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo.options.

Notation "'Unset'" := (
  in_type "zoo_std.ivar_3.state" 0
)(in custom zoo_tag
).
Notation "'Set'" := (
  in_type "zoo_std.ivar_3.state" 1
)(in custom zoo_tag
).
