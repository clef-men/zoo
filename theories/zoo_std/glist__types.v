Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo.options.

Notation "'Gnil'" := (
  in_type "zoo_std.glist.t" 0
)(in custom zoo_tag
).
Notation "'Gcons'" := (
  in_type "zoo_std.glist.t" 1
)(in custom zoo_tag
).
