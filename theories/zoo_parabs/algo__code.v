Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_parabs.future.
Require Import zoo_parabs.pool.
Require Import zoo_std.int.
Require Import zoo_std.mvar.
Require Import zoo.options.

Definition algo٠adjust_chunk : val :=
  𝗳𝘂𝗻 "ctx" "beg" "end_" "chunk" ->
    𝗺𝗮𝘁𝗰𝗵 "chunk" 𝘄𝗶𝘁𝗵
    | Some "chunk" ->
        "chunk"
    | None ->
        𝗹𝗲𝘁 "num_dom" = pool٠size "ctx" + 1 𝗶𝗻
        𝗹𝗲𝘁 "num_task" = "end_" - "beg" 𝗶𝗻
        𝗶𝗳 "num_dom" == 1 𝘁𝗵𝗲𝗻 (
          "num_task"
        ) 𝗲𝗹𝘀𝗲 (
          int٠max 1 ("num_task" 𝗾𝘂𝗼𝘁 (8 * "num_dom"))
        )
    𝗲𝗻𝗱.

Definition algo٠for_₁ : val :=
  𝗿𝗲𝗰 "for_" "ctx" "beg" "end_" "chunk" "task" ->
    𝗹𝗲𝘁 "num_task" = "end_" - "beg" 𝗶𝗻
    𝗶𝗳 "num_task" ≤ "chunk" 𝘁𝗵𝗲𝗻 (
      "task" "ctx" "beg" "num_task"
    ) 𝗲𝗹𝘀𝗲 (
      𝗹𝗲𝘁 "mid" = "beg" + "num_task" 𝗾𝘂𝗼𝘁 2 𝗶𝗻
      𝗹𝗲𝘁 "left" =
        future٠async "ctx"
          (𝗳𝘂𝗻 "ctx" -> "for_" "ctx" "beg" "mid" "chunk" "task")
      𝗶𝗻
      "for_" "ctx" "mid" "end_" "chunk" "task" ⍮
      future٠wait "ctx" "left"
    ).

Definition algo٠for_ : val :=
  𝗳𝘂𝗻 "ctx" "beg" "end_" "chunk" "task" ->
    𝗹𝗲𝘁 "chunk" =
      algo٠adjust_chunk "ctx" "beg" "end_" "chunk"
    𝗶𝗻
    algo٠for_₁ "ctx" "beg" "end_" "chunk" "task".

Definition algo٠for_each : val :=
  𝗳𝘂𝗻 "ctx" "beg" "end_" "chunk" "task" ->
    algo٠for_ "ctx" "beg" "end_" "chunk"
      (𝗳𝘂𝗻 "ctx" "beg" "sz" ->
         𝗳𝗼𝗿 "i" = "beg" 𝘁𝗼 "beg" + "sz" 𝗱𝗼
           "task" "ctx" "i"
         𝗱𝗼𝗻𝗲).

Definition algo٠fold_seq : val :=
  𝗿𝗲𝗰 "fold_seq" "ctx" "beg" "end_" "body" "op" "acc" ->
    𝗶𝗳 "beg" == "end_" 𝘁𝗵𝗲𝗻 (
      "acc"
    ) 𝗲𝗹𝘀𝗲 (
      𝗹𝗲𝘁 "v" = "body" "ctx" "beg" 𝗶𝗻
      𝗹𝗲𝘁 "acc" = "op" "acc" "v" 𝗶𝗻
      𝗹𝗲𝘁 "beg" = "beg" + 1 𝗶𝗻
      "fold_seq" "ctx" "beg" "end_" "body" "op" "acc"
    ).

Definition algo٠fold₁ : val :=
  𝗿𝗲𝗰 "fold" "ctx" "beg" "end_" "chunk" "body" "op" "zero" ->
    𝗹𝗲𝘁 "num_task" = "end_" - "beg" 𝗶𝗻
    𝗶𝗳 "num_task" ≤ "chunk" 𝘁𝗵𝗲𝗻 (
      algo٠fold_seq "ctx" "beg" ("beg" + "num_task") "body" "op" "zero"
    ) 𝗲𝗹𝘀𝗲 (
      𝗹𝗲𝘁 "mid" = "beg" + "num_task" 𝗾𝘂𝗼𝘁 2 𝗶𝗻
      𝗹𝗲𝘁 "left" =
        future٠async "ctx"
          (𝗳𝘂𝗻 "ctx" ->
             "fold" "ctx" "beg" "mid" "chunk" "body" "op" "zero")
      𝗶𝗻
      𝗹𝗲𝘁 "right" =
        "fold" "ctx" "mid" "end_" "chunk" "body" "op" "zero"
      𝗶𝗻
      𝗹𝗲𝘁 "left" = future٠wait "ctx" "left" 𝗶𝗻
      "op" "left" "right"
    ).

Definition algo٠fold : val :=
  𝗳𝘂𝗻 "ctx" "beg" "end_" "chunk" "body" "op" "zero" ->
    𝗹𝗲𝘁 "chunk" =
      algo٠adjust_chunk "ctx" "beg" "end_" "chunk"
    𝗶𝗻
    algo٠fold₁ "ctx" "beg" "end_" "chunk" "body" "op" "zero".

Definition algo٠find_seq : val :=
  𝗿𝗲𝗰 "find_seq" "ctx" "beg" "end_" "pred" "found" ->
    𝗶𝗳
      "beg" != "end_" 𝗮𝗻𝗱 mvar٠is_unset "found"
    𝘁𝗵𝗲𝗻 (
      𝗶𝗳 "pred" "ctx" "beg" 𝘁𝗵𝗲𝗻 (
        mvar٠set "found" "beg"
      ) 𝗲𝗹𝘀𝗲 (
        𝗹𝗲𝘁 "beg" = "beg" + 1 𝗶𝗻
        "find_seq" "ctx" "beg" "end_" "pred" "found"
      )
    ).

Definition algo٠find₁ : val :=
  𝗿𝗲𝗰 "find" "ctx" "beg" "end_" "chunk" "pred" "found" ->
    𝗹𝗲𝘁 "num_task" = "end_" - "beg" 𝗶𝗻
    𝗶𝗳 "num_task" ≤ "chunk" 𝘁𝗵𝗲𝗻 (
      algo٠find_seq "ctx" "beg" ("beg" + "num_task") "pred" "found"
    ) 𝗲𝗹𝘀𝗲 𝗶𝗳 mvar٠is_unset "found" 𝘁𝗵𝗲𝗻 (
      𝗹𝗲𝘁 "mid" = "beg" + "num_task" 𝗾𝘂𝗼𝘁 2 𝗶𝗻
      𝗹𝗲𝘁 "left" =
        future٠async "ctx"
          (𝗳𝘂𝗻 "ctx" ->
             "find" "ctx" "beg" "mid" "chunk" "pred" "found")
      𝗶𝗻
      "find" "ctx" "mid" "end_" "chunk" "pred" "found" ⍮
      future٠wait "ctx" "left"
    ).

Definition algo٠find : val :=
  𝗳𝘂𝗻 "ctx" "beg" "end_" "chunk" "pred" ->
    𝗹𝗲𝘁 "chunk" =
      algo٠adjust_chunk "ctx" "beg" "end_" "chunk"
    𝗶𝗻
    𝗹𝗲𝘁 "found" = mvar٠create () 𝗶𝗻
    algo٠find₁ "ctx" "beg" "end_" "chunk" "pred" "found" ⍮
    mvar٠try_get "found".
