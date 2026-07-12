Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_parabs.pool.
Require Import examples.pool_counter__types.
Require Import zoo.options.

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
