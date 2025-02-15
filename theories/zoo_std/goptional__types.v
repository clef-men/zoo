From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo Require Import
  options.

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
