Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.mutex.
Require Import zoo.options.

Notation "'Unset'" := (
  in_type "zoo_std.lazy.state" 0
)(in custom zoo_tag
).
Notation "'Setting'" := (
  in_type "zoo_std.lazy.state" 1
)(in custom zoo_tag
).
Notation "'Set'" := (
  in_type "zoo_std.lazy.state" 2
)(in custom zoo_tag
).
