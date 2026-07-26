Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_saturn.ws_deque_2.
Require Import zoo_std.array.
Require Import zoo_std.random_round.
Require Import zoo_parabs.ws_deques_public__types.
Require Import zoo.options.

Definition ws_deques_public٠create : val :=
  𝗳𝘂𝗻 "sz" ->
    array٠unsafe_init "sz" ws_deque_2٠create.

Definition ws_deques_public٠size : val :=
  array٠size.

Definition ws_deques_public٠block : val :=
  𝗳𝘂𝗻 "_t" "_i" ->
    ().

Definition ws_deques_public٠unblock : val :=
  𝗳𝘂𝗻 "_t" "_i" ->
    ().

Definition ws_deques_public٠push : val :=
  𝗳𝘂𝗻 "t" "i" "v" ->
    𝗹𝗲𝘁 "queue" = array٠unsafe_get "t" "i" 𝗶𝗻
    ws_deque_2٠push "queue" "v".

Definition ws_deques_public٠pop : val :=
  𝗳𝘂𝗻 "t" "i" ->
    𝗹𝗲𝘁 "queue" = array٠unsafe_get "t" "i" 𝗶𝗻
    ws_deque_2٠pop "queue".

Definition ws_deques_public٠steal_to : val :=
  𝗳𝘂𝗻 "t" "_i" "j" ->
    𝗹𝗲𝘁 "queue" = array٠unsafe_get "t" "j" 𝗶𝗻
    ws_deque_2٠steal "queue".

Definition ws_deques_public٠steal_as₀ : val :=
  𝗿𝗲𝗰 "steal_as" "t" "sz" "i" "round" "n" ->
    𝗶𝗳 "n" ≤ 0 𝘁𝗵𝗲𝗻 (
      §None
    ) 𝗲𝗹𝘀𝗲 (
      𝗹𝗲𝘁 "j" =
        ("i" + 1 + random_round٠next "round") 𝗿𝗲𝗺 "sz"
      𝗶𝗻
      𝗺𝗮𝘁𝗰𝗵
        ws_deques_public٠steal_to "t" "i" "j"
      𝘄𝗶𝘁𝗵
      | None ->
          "steal_as" "t" "sz" "i" "round" ("n" - 1)
      | ⎽ 𝗮𝘀 "res" ->
          "res"
      𝗲𝗻𝗱
    ).

Definition ws_deques_public٠steal_as : val :=
  𝗳𝘂𝗻 "t" "i" "round" ->
    𝗹𝗲𝘁 "sz" = ws_deques_public٠size "t" 𝗶𝗻
    ws_deques_public٠steal_as₀ "t" "sz" "i" "round" ("sz" - 1).
