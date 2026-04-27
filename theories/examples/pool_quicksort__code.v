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

Definition pool_quicksort٠partition : val :=
  fun: "arr" "i" "sz" =>
    let: "pivot" := array٠unsafe_get "arr" "i" in
    let: "i1" := ref ("i" + 1) in
    for: "i2" := "i" + 1 to "i" + "sz" begin
      if: array٠unsafe_get "arr" "i2" < "pivot" then (
        array٠unsafe_swap "arr" !"i1" "i2" ;;
        "i1" <- !"i1" + 1
      )
    end ;;
    array٠unsafe_swap "arr" "i" (!"i1" - 1) ;;
    !"i1" - 1.

Definition pool_quicksort٠main₀ : val :=
  rec: "main" "ctx" "arr" "i" "sz" =>
    if: 1 < "sz" then (
      let: "pivot" := pool_quicksort٠partition "arr" "i" "sz" in
      pool٠async
        "ctx"
        (fun: "ctx" => "main" "ctx" "arr" "i" ("pivot" - "i")) ;;
      pool٠async
        "ctx"
        (fun: "ctx" =>
           "main" "ctx" "arr" ("pivot" + 1) ("sz" - ("pivot" - "i") - 1))
    ).

Definition pool_quicksort٠main₁ : val :=
  fun: "ctx" "arr" =>
    pool_quicksort٠main₀ "ctx" "arr" 0 (array٠size "arr").

Definition pool_quicksort٠main : val :=
  fun: "num_worker" "arr" =>
    pool٠run
      "num_worker"
      (fun: "ctx" => pool_quicksort٠main₁ "ctx" "arr").
