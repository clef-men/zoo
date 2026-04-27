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

Definition pool_counter٠main : val :=
  fun: "num_worker" "n" =>
    let: "cnt" := ref 0 in
    pool٠run
      "num_worker"
      (fun: "ctx" =>
         for: <> := 0 to "n" begin
           pool٠async "ctx" (fun: "_ctx" => FAA "cnt".[contents] 1 ;;
                                             ())
         end) ;;
    !"cnt".
