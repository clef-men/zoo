Require Export Ltac2.Constructor.
Require Export Ltac2.Init.

Require Import zoo.prelude.
Require Import zoo.ltac2.Constr.
Require Import zoo.ltac2.Ind.
Require Import zoo.options.

Ltac2 number_index t inst :=
  Ind.number_index (inductive t) inst.

Ltac2 arity_full t inst :=
  let t := Constr.Unsafe.make_constructor t inst in
  Constr.product_arity (Constr.type t).
Ltac2 arity t inst :=
  Int.sub (arity_full t inst) (number_index t inst).
