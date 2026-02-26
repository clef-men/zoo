From Ltac2 Require Export
  Ind
  Init.

From zoo Require Import
  prelude.
From zoo.ltac2 Require Import
  Constr.
From zoo Require Import
  options.

Ltac2 nconstructors' t :=
  nconstructors (data t).

Ltac2 number_index t inst :=
  let t := Constr.Unsafe.make_ind t inst in
  Constr.product_arity (Constr.type t).
