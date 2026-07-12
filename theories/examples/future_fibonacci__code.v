Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_parabs.future.
Require Import zoo_parabs.pool.
Require Import examples.future_fibonacci__types.
Require Import zoo.options.

Definition future_fibonacci٠main₀ : val :=
  rec: "main" "ctx" "n" =>
    if: "n" ≤ 1 then (
      "n"
    ) else (
      let: "fut1" :=
        future٠async "ctx" (fun: "ctx" => "main" "ctx" ("n" - 1))
      in
      let: "fut2" :=
        future٠async "ctx" (fun: "ctx" => "main" "ctx" ("n" - 2))
      in
      future٠wait "ctx" "fut1" + future٠wait "ctx" "fut2"
    ).

Definition future_fibonacci٠main : val :=
  fun: "num_worker" "n" =>
    pool٠run
      "num_worker"
      (fun: "ctx" => future_fibonacci٠main₀ "ctx" "n").
