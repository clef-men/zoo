From Ltac2 Require Export
  Constructor
  Init.

From zoo Require Import
  prelude.
From zoo.ltac2 Require Import
  Constr
  Ind.
From zoo Require Import
  options.

Ltac2 number_index t inst :=
  Ind.number_index (inductive t) inst.

Ltac2 arity_full t inst :=
  let t := Constr.Unsafe.make_constructor t inst in
  Constr.product_arity (Constr.type t).
Ltac2 arity t inst :=
  Int.sub (arity_full t inst) (number_index t inst).
