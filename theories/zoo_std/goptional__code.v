Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo.options.

Notation "'goptional٠Nothing'" := (
  in_type "zoo_std.goptional.t" 0
)(in custom zoo_tag
).
Notation "'goptional٠Anything'" := (
  in_type "zoo_std.goptional.t" 1
)(in custom zoo_tag
).
Notation "'goptional٠Something'" := (
  in_type "zoo_std.goptional.t" 2
)(in custom zoo_tag
).
