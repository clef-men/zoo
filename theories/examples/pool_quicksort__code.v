From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_parabs Require Import
  pool.
From zoo_std Require Import
  array.
From examples Require Import
  pool_quicksort__types.
From zoo Require Import
  options.

Definition pool_quicksort_partition : val :=
  fun: "arr" "i" "sz" =>
    let: "pivot" := array_unsafe_get "arr" "i" in
    let: "i1" := ref ("i" + 1) in
    for: "i2" := "i" + 1 to "i" + "sz" begin
      if: array_unsafe_get "arr" "i2" < "pivot" then (
        array_unsafe_swap "arr" !"i1" "i2" ;;
        "i1" <- !"i1" + 1
      )
    end ;;
    array_unsafe_swap "arr" "i" (!"i1" - 1) ;;
    !"i1" - 1.

Definition pool_quicksort_main₀ : val :=
  rec: "main" "ctx" "arr" "i" "sz" =>
    if: 1 < "sz" then (
      let: "pivot" := pool_quicksort_partition "arr" "i" "sz" in
      pool_async "ctx" (fun: "ctx" => "main" "ctx" "arr" "i" ("pivot" - "i")) ;;
      pool_async
        "ctx"
        (fun: "ctx" =>
           "main" "ctx" "arr" ("pivot" + 1) ("sz" - ("pivot" - "i") - 1))
    ).

Definition pool_quicksort_main₁ : val :=
  fun: "ctx" "arr" =>
    pool_quicksort_main₀ "ctx" "arr" 0 (array_size "arr").

Definition pool_quicksort_main : val :=
  fun: "num_worker" "arr" =>
    pool_run "num_worker" (fun: "ctx" => pool_quicksort_main₁ "ctx" "arr").
