From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_parabs Require Import
  future
  pool.
From examples Require Import
  fibonacci__types.
From zoo Require Import
  options.

Definition fibonacci_fibonacci_0 : val :=
  rec: "fibonacci" "n" "ctx" =>
    if: "n" ≤ 1 then (
      "n"
    ) else (
      let: "fut1" :=
        future_async "ctx" (fun: "ctx" => "fibonacci" ("n" - 1) "ctx")
      in
      let: "fut2" :=
        future_async "ctx" (fun: "ctx" => "fibonacci" ("n" - 2) "ctx")
      in
      future_wait "ctx" "fut1" + future_wait "ctx" "fut2"
    ).

Definition fibonacci_fibonacci : val :=
  fun: "n" "pool" =>
    pool_run "pool" (fun: "ctx" => fibonacci_fibonacci_0 "n" "ctx").
