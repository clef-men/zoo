From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  mutex.
From zoo Require Import
  options.

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
