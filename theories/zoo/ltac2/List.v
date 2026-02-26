From Ltac2 Require Export
  Init
  List.

From zoo Require Import
  prelude.
From zoo Require Import
  options.

#[local] Ltac2 rec init_foldl' fn acc i n :=
  if Int.equal n 0 then
    acc
  else
    let acc := fn acc i in
    init_foldl' fn acc (Int.add i 1) (Int.sub n 1).
Ltac2 init_foldl fn acc :=
  init_foldl' fn acc 0.

Ltac2 foldr :=
  fold_right.
Ltac2 foldri fn xs acc :=
  let rec go i xs acc :=
    match xs with
    | [] =>
        acc
    | x :: xs =>
        fn i x (go (Int.add i 1) xs acc)
    end
  in
  go 0 xs acc.

Ltac2 foldl :=
  fold_left.
Ltac2 foldli:=
  fold_lefti.
