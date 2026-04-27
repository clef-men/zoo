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
