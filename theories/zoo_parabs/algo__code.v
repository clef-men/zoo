From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_parabs Require Import
  future
  pool.
From zoo_std Require Import
  mvar
  int.
From zoo_parabs Require Import
  algo__types.
From zoo Require Import
  options.

Definition algo٠adjust_chunk : val :=
  fun: "ctx" "beg" "end_" "chunk" =>
    match: "chunk" with
    | Some "chunk" =>
        "chunk"
    | None =>
        let: "num_dom" := pool٠size "ctx" + 1 in
        let: "num_task" := "end_" - "beg" in
        if: "num_dom" == 1 then (
          "num_task"
        ) else (
          int٠max 1 ("num_task" `quot` (8 * "num_dom"))
        )
    end.

Definition algo٠for_₀ : val :=
  rec: "for_" "ctx" "beg" "end_" "chunk" "task" =>
    let: "num_task" := "end_" - "beg" in
    if: "num_task" ≤ "chunk" then (
      "task" "ctx" "beg" "num_task"
    ) else (
      let: "mid" := "beg" + "num_task" `quot` 2 in
      let: "left" :=
        future٠async "ctx"
          (fun: "ctx" => "for_" "ctx" "beg" "mid" "chunk" "task")
      in
      "for_" "ctx" "mid" "end_" "chunk" "task" ;;
      future٠wait "ctx" "left"
    ).

Definition algo٠for_ : val :=
  fun: "ctx" "beg" "end_" "chunk" "task" =>
    let: "chunk" := algo٠adjust_chunk "ctx" "beg" "end_" "chunk" in
    algo٠for_₀ "ctx" "beg" "end_" "chunk" "task".

Definition algo٠for_each : val :=
  fun: "ctx" "beg" "end_" "chunk" "task" =>
    algo٠for_ "ctx" "beg" "end_" "chunk"
      (fun: "ctx" "beg" "sz" =>
         for: "i" := "beg" to "beg" + "sz" begin
           "task" "ctx" "i"
         end).

Definition algo٠fold_seq : val :=
  rec: "fold_seq" "ctx" "beg" "end_" "body" "op" "acc" =>
    if: "beg" == "end_" then (
      "acc"
    ) else (
      let: "v" := "body" "ctx" "beg" in
      let: "acc" := "op" "acc" "v" in
      let: "beg" := "beg" + 1 in
      "fold_seq" "ctx" "beg" "end_" "body" "op" "acc"
    ).

Definition algo٠fold₀ : val :=
  rec: "fold" "ctx" "beg" "end_" "chunk" "body" "op" "zero" =>
    let: "num_task" := "end_" - "beg" in
    if: "num_task" ≤ "chunk" then (
      algo٠fold_seq "ctx" "beg" ("beg" + "num_task") "body" "op" "zero"
    ) else (
      let: "mid" := "beg" + "num_task" `quot` 2 in
      let: "left" :=
        future٠async "ctx"
          (fun: "ctx" => "fold" "ctx" "beg" "mid" "chunk" "body" "op" "zero")
      in
      let: "right" := "fold" "ctx" "mid" "end_" "chunk" "body" "op" "zero" in
      let: "left" := future٠wait "ctx" "left" in
      "op" "left" "right"
    ).

Definition algo٠fold : val :=
  fun: "ctx" "beg" "end_" "chunk" "body" "op" "zero" =>
    let: "chunk" := algo٠adjust_chunk "ctx" "beg" "end_" "chunk" in
    algo٠fold₀ "ctx" "beg" "end_" "chunk" "body" "op" "zero".

Definition algo٠find_seq : val :=
  rec: "find_seq" "ctx" "beg" "end_" "pred" "found" =>
    if: "beg" != "end_" and mvar٠is_unset "found" then (
      if: "pred" "ctx" "beg" then (
        mvar٠set "found" "beg"
      ) else (
        let: "beg" := "beg" + 1 in
        "find_seq" "ctx" "beg" "end_" "pred" "found"
      )
    ).

Definition algo٠find₀ : val :=
  rec: "find" "ctx" "beg" "end_" "chunk" "pred" "found" =>
    let: "num_task" := "end_" - "beg" in
    if: "num_task" ≤ "chunk" then (
      algo٠find_seq "ctx" "beg" ("beg" + "num_task") "pred" "found"
    ) else if: mvar٠is_unset "found" then (
      let: "mid" := "beg" + "num_task" `quot` 2 in
      let: "left" :=
        future٠async "ctx"
          (fun: "ctx" => "find" "ctx" "beg" "mid" "chunk" "pred" "found")
      in
      "find" "ctx" "mid" "end_" "chunk" "pred" "found" ;;
      future٠wait "ctx" "left"
    ).

Definition algo٠find : val :=
  fun: "ctx" "beg" "end_" "chunk" "pred" =>
    let: "chunk" := algo٠adjust_chunk "ctx" "beg" "end_" "chunk" in
    let: "found" := mvar٠create () in
    algo٠find₀ "ctx" "beg" "end_" "chunk" "pred" "found" ;;
    mvar٠try_get "found".
