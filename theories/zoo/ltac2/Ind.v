Require Export Ltac2.Ind.
Require Export Ltac2.Init.

Require Import zoo.prelude.
Require Import zoo.ltac2.Constr.
Require Import zoo.options.

Ltac2 nconstructors' t :=
  nconstructors (data t).

Ltac2 number_index t inst :=
  let t := Constr.Unsafe.make_ind t inst in
  Constr.product_arity (Constr.type t).
