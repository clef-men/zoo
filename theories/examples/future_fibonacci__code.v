From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_parabs Require Import
  future
  pool.
From examples Require Import
  future_fibonacci__types.
From zoo Require Import
  options.

Definition future_fibonacci_main_0 : val :=
  rec: "main" "ctx" "n" =>
    if: "n" ≤ 1 then (
      "n"
    ) else (
      let: "fut1" :=
        future_async "ctx" (fun: "ctx" => "main" "ctx" ("n" - 1))
      in
      let: "fut2" :=
        future_async "ctx" (fun: "ctx" => "main" "ctx" ("n" - 2))
      in
      future_wait "ctx" "fut1" + future_wait "ctx" "fut2"
    ).

Definition future_fibonacci_main : val :=
  fun: "num_dom" "n" =>
    let: "pool" := pool_create "num_dom" in
    let: "res" :=
      pool_run "pool" (fun: "ctx" => future_fibonacci_main_0 "ctx" "n")
    in
    pool_kill "pool" ;;
    "res".
