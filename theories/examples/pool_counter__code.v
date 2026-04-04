From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_parabs Require Import
  pool.
From examples Require Import
  pool_counter__types.
From zoo Require Import
  options.

Definition pool_counter_main : val :=
  fun: "num_domain" "n" =>
    let: "cnt" := ref 0 in
    pool_run
      "num_domain"
      (fun: "ctx" =>
         for: <> := 0 to "n" begin
           pool_async "ctx" (fun: "_ctx" => FAA "cnt".[contents] 1 ;;
                                            ())
         end) ;;
    !"cnt".
