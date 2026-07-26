Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_parabs.pool.
Require Import examples.pool_counter__types.
Require Import zoo.options.

Definition pool_counter٠main : val :=
  𝗳𝘂𝗻 "num_worker" "n" ->
    𝗹𝗲𝘁 "cnt" = 𝗿𝗲𝗳 0 𝗶𝗻
    pool٠run
      "num_worker"
      (𝗳𝘂𝗻 "ctx" ->
         𝗳𝗼𝗿 ⎽ = 0 𝘁𝗼 "n" 𝗱𝗼
           pool٠async
             "ctx"
             (𝗳𝘂𝗻 "_ctx" -> 𝗳𝗮𝗮 "cnt".[contents] 1 ⍮
                                     ())
         𝗱𝗼𝗻𝗲) ⍮
    !"cnt".
