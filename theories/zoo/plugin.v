Require Import zoo.prelude.
Require Import zoo.iris.base_logic.lib.base.
Require Import zoo.program_logic.ghost_state.
Require Import zoo.options.

Ltac solve_iris_typeclass :=
  first
  [ apply _
  | lazymatch goal with
    | |- _ ?P =>
        let pred := get_head P in
        rewrite /pred
    end;
    apply _
  ].

Declare ML Module "rocq-zoo.plugin".
