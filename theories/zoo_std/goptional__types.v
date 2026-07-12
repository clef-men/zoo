Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo.options.

Notation "'Gnothing'" := (
  in_type "zoo_std.goptional.t" 0
)(in custom zoo_tag
).
Notation "'Ganything'" := (
  in_type "zoo_std.goptional.t" 1
)(in custom zoo_tag
).
Notation "'Gsomething'" := (
  in_type "zoo_std.goptional.t" 2
)(in custom zoo_tag
).
