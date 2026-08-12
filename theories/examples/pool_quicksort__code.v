Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_parabs.pool.
Require Import zoo_std.array.
Require Import zoo_std.for_.
Require Import zoo.options.

Definition pool_quicksort٠partition : val :=
  𝗳𝘂𝗻 "arr" "i" "sz" ->
    𝗹𝗲𝘁 "pivot" = array٠unsafe_get "arr" "i" 𝗶𝗻
    𝗹𝗲𝘁 "i1" = 𝗿𝗲𝗳 ("i" + 1) 𝗶𝗻
    𝗳𝗼𝗿 "i2" = "i" + 1 𝘁𝗼 "i" + "sz" 𝗱𝗼
      𝗶𝗳 array٠unsafe_get "arr" "i2" < "pivot" 𝘁𝗵𝗲𝗻 (
        array٠unsafe_swap "arr" !"i1" "i2" ⍮
        "i1" <- !"i1" + 1
      )
    𝗱𝗼𝗻𝗲 ⍮
    array٠unsafe_swap "arr" "i" (!"i1" - 1) ⍮
    !"i1" - 1.

Definition pool_quicksort٠main₂ : val :=
  𝗿𝗲𝗰 "main" "ctx" "arr" "i" "sz" ->
    𝗶𝗳 1 < "sz" 𝘁𝗵𝗲𝗻 (
      𝗹𝗲𝘁 "pivot" =
        pool_quicksort٠partition "arr" "i" "sz"
      𝗶𝗻
      pool٠async
        "ctx"
        (𝗳𝘂𝗻 "ctx" -> "main" "ctx" "arr" "i" ("pivot" - "i")) ⍮
      pool٠async
        "ctx"
        (𝗳𝘂𝗻 "ctx" ->
           "main" "ctx" "arr" ("pivot" + 1) ("sz" - ("pivot" - "i") - 1))
    ).

Definition pool_quicksort٠main₁ : val :=
  𝗳𝘂𝗻 "ctx" "arr" ->
    pool_quicksort٠main₂ "ctx" "arr" 0 (array٠size "arr").

Definition pool_quicksort٠main : val :=
  𝗳𝘂𝗻 "num_worker" "arr" ->
    pool٠run
      "num_worker"
      (𝗳𝘂𝗻 "ctx" -> pool_quicksort٠main₁ "ctx" "arr").
