From Ltac2 Require Export
  Init
  List.

From zoo Require Import
  prelude.
From zoo Require Import
  options.

Ltac2 fold_righti fn xs acc :=
  let rec go i xs acc :=
    match xs with
    | [] =>
        acc
    | x :: xs =>
        fn i x (go (Int.add i 1) xs acc)
    end
  in
  go 0 xs acc.
