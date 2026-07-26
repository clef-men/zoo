Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.array.
Require Import zoo_std.random_state.
Require Import zoo_std.random_round__types.
Require Import zoo.options.

Definition random_round٠create : val :=
  𝗳𝘂𝗻 "sz" ->
    { random_state٠create (),
      array٠unsafe_initi "sz" (𝗳𝘂𝗻 "i" -> "i"),
      "sz"
    }.

Definition random_round٠reset : val :=
  𝗳𝘂𝗻 "t" ->
    "t" <-{index} array٠size "t".{array}.

Definition random_round٠next : val :=
  𝗳𝘂𝗻 "t" ->
    𝗹𝗲𝘁 "arr" = "t".{array} 𝗶𝗻
    𝗹𝗲𝘁 "i" = "t".{index} 𝗶𝗻
    𝗹𝗲𝘁 "j" = random_state٠int "t".{random} "i" 𝗶𝗻
    𝗹𝗲𝘁 "res" = array٠unsafe_get "arr" "j" 𝗶𝗻
    𝗹𝗲𝘁 "i" = "i" - 1 𝗶𝗻
    array٠unsafe_set "arr" "j" (array٠unsafe_get "arr" "i") ⍮
    array٠unsafe_set "arr" "i" "res" ⍮
    "t" <-{index} "i" ⍮
    "res".
