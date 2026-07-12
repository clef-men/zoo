Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import unix.unix.
Require Import zoo_std.spsc_waiter.
Require Import zoo.options.

Notation "'Open'" := (
  in_type "zoo_eio.rcfd.state" 0
)(in custom zoo_tag
).
Notation "'Closing'" := (
  in_type "zoo_eio.rcfd.state" 1
)(in custom zoo_tag
).

Notation "'ops'" := (
  in_type "zoo_eio.rcfd.t" 0
)(in custom zoo_field
).
Notation "'state'" := (
  in_type "zoo_eio.rcfd.t" 1
)(in custom zoo_field
).
