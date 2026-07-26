Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_parabs.future.
Require Import zoo_parabs.pool.
Require Import examples.future_fibonacci__types.
Require Import zoo.options.

Definition future_fibonacci٠main₀ : val :=
  𝗿𝗲𝗰 "main" "ctx" "n" ->
    𝗶𝗳 "n" ≤ 1 𝘁𝗵𝗲𝗻 (
      "n"
    ) 𝗲𝗹𝘀𝗲 (
      𝗹𝗲𝘁 "fut1" =
        future٠async "ctx" (𝗳𝘂𝗻 "ctx" -> "main" "ctx" ("n" - 1))
      𝗶𝗻
      𝗹𝗲𝘁 "fut2" =
        future٠async "ctx" (𝗳𝘂𝗻 "ctx" -> "main" "ctx" ("n" - 2))
      𝗶𝗻
      future٠wait "ctx" "fut1" + future٠wait "ctx" "fut2"
    ).

Definition future_fibonacci٠main : val :=
  𝗳𝘂𝗻 "num_worker" "n" ->
    pool٠run
      "num_worker"
      (𝗳𝘂𝗻 "ctx" -> future_fibonacci٠main₀ "ctx" "n").
