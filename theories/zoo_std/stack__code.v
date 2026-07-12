Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.dynarray_1.
Require Import zoo_std.stack__types.
Require Import zoo.options.

Definition stack٠create : val :=
  dynarray_1٠create.

Definition stack٠is_empty : val :=
  dynarray_1٠is_empty.

Definition stack٠push : val :=
  dynarray_1٠push.

Definition stack٠pop : val :=
  dynarray_1٠pop.
