From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  mvar
  int.
From zoo_parabs Require Import
  future
  pool.
From zoo_parabs Require Import
  algo__types.
From zoo Require Import
  options.

Definition algo_adjust_chunk : val :=
  fun: "ctx" "beg" "end_" "chunk" =>
    match: "chunk" with
    | Some "chunk" =>
        "chunk"
    | None =>
        let: "num_dom" := pool_size "ctx" + #1 in
        let: "num_task" := "end_" - "beg" in
        if: "num_dom" == #1 then (
          "num_task"
        ) else (
          int_max #1 ("num_task" `quot` (#8 * "num_dom"))
        )
    end.

Definition algo_for__0 : val :=
  rec: "for_" "ctx" "beg" "end_" "chunk" "task" =>
    let: "num_task" := "end_" - "beg" in
    if: "num_task" ≤ "chunk" then (
      "task" "ctx" "beg" "num_task"
    ) else (
      let: "mid" := "beg" + "num_task" `quot` #2 in
      let: "left" :=
        future_async "ctx"
          (fun: "ctx" => "for_" "ctx" "beg" "mid" "chunk" "task")
      in
      "for_" "ctx" "mid" "end_" "chunk" "task" ;;
      future_wait "ctx" "left"
    ).

Definition algo_for_ : val :=
  fun: "ctx" "beg" "end_" "chunk" "task" =>
    let: "chunk" := algo_adjust_chunk "ctx" "beg" "end_" "chunk" in
    algo_for__0 "ctx" "beg" "end_" "chunk" "task".

Definition algo_for_each : val :=
  fun: "ctx" "beg" "end_" "chunk" "task" =>
    algo_for_ "ctx" "beg" "end_" "chunk"
      (fun: "ctx" "beg" "sz" =>
         for: "i" := "beg" to "beg" + "sz" begin
           "task" "ctx" "i"
         end).

Definition algo_fold_seq : val :=
  rec: "fold_seq" "ctx" "beg" "end_" "body" "op" "acc" =>
    if: "beg" == "end_" then (
      "acc"
    ) else (
      let: "v" := "body" "ctx" "beg" in
      let: "acc" := "op" "acc" "v" in
      let: "beg" := "beg" + #1 in
      "fold_seq" "ctx" "beg" "end_" "body" "op" "acc"
    ).

Definition algo_fold_0 : val :=
  rec: "fold" "ctx" "beg" "end_" "chunk" "body" "op" "zero" =>
    let: "num_task" := "end_" - "beg" in
    if: "num_task" ≤ "chunk" then (
      algo_fold_seq "ctx" "beg" ("beg" + "num_task") "body" "op" "zero"
    ) else (
      let: "mid" := "beg" + "num_task" `quot` #2 in
      let: "left" :=
        future_async "ctx"
          (fun: "ctx" => "fold" "ctx" "beg" "mid" "chunk" "body" "op" "zero")
      in
      let: "right" := "fold" "ctx" "mid" "end_" "chunk" "body" "op" "zero" in
      let: "left" := future_wait "ctx" "left" in
      "op" "left" "right"
    ).

Definition algo_fold : val :=
  fun: "ctx" "beg" "end_" "chunk" "body" "op" "zero" =>
    let: "chunk" := algo_adjust_chunk "ctx" "beg" "end_" "chunk" in
    algo_fold_0 "ctx" "beg" "end_" "chunk" "body" "op" "zero".

Definition algo_find_seq : val :=
  rec: "find_seq" "ctx" "beg" "end_" "pred" "found" =>
    if: "beg" != "end_" and mvar_is_unset "found" then (
      if: "pred" "ctx" "beg" then (
        mvar_set "found" "beg"
      ) else (
        let: "beg" := "beg" + #1 in
        "find_seq" "ctx" "beg" "end_" "pred" "found"
      )
    ).

Definition algo_find_0 : val :=
  rec: "find" "ctx" "beg" "end_" "chunk" "pred" "found" =>
    let: "num_task" := "end_" - "beg" in
    if: "num_task" ≤ "chunk" then (
      algo_find_seq "ctx" "beg" ("beg" + "num_task") "pred" "found"
    ) else if: mvar_is_unset "found" then (
      let: "mid" := "beg" + "num_task" `quot` #2 in
      let: "left" :=
        future_async "ctx"
          (fun: "ctx" => "find" "ctx" "beg" "mid" "chunk" "pred" "found")
      in
      "find" "ctx" "mid" "end_" "chunk" "pred" "found" ;;
      future_wait "ctx" "left"
    ).

Definition algo_find : val :=
  fun: "ctx" "beg" "end_" "chunk" "pred" =>
    let: "chunk" := algo_adjust_chunk "ctx" "beg" "end_" "chunk" in
    let: "found" := mvar_create () in
    algo_find_0 "ctx" "beg" "end_" "chunk" "pred" "found" ;;
    mvar_try_get "found".
