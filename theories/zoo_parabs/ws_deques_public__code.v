From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  array
  random_round.
From zoo_saturn Require Import
  inf_ws_deque_2.
From zoo_parabs Require Import
  ws_deques_public__types.
From zoo Require Import
  options.

Definition ws_deques_public_create : val :=
  fun: "sz" =>
    array_unsafe_init "sz" inf_ws_deque_2_create.

Definition ws_deques_public_size : val :=
  array_size.

Definition ws_deques_public_block : val :=
  fun: "_t" "_i" =>
    ().

Definition ws_deques_public_unblock : val :=
  fun: "_t" "_i" =>
    ().

Definition ws_deques_public_push : val :=
  fun: "t" "i" "v" =>
    let: "deque" := array_unsafe_get "t" "i" in
    inf_ws_deque_2_push "deque" "v".

Definition ws_deques_public_pop : val :=
  fun: "t" "i" =>
    let: "deque" := array_unsafe_get "t" "i" in
    inf_ws_deque_2_pop "deque".

Definition ws_deques_public_steal_to : val :=
  fun: "t" "_i" "j" =>
    let: "deque" := array_unsafe_get "t" "j" in
    inf_ws_deque_2_steal "deque".

Definition ws_deques_public_steal_as_0 : val :=
  rec: "steal_as" "t" "sz" "i" "round" "n" =>
    if: "n" ≤ #0 then (
      §None
    ) else (
      let: "j" := ("i" + #1 + random_round_next "round") `rem` "sz" in
      match: ws_deques_public_steal_to "t" "i" "j" with
      | None =>
          "steal_as" "t" "sz" "i" "round" ("n" - #1)
      |_ as "res" =>
          "res"
      end
    ).

Definition ws_deques_public_steal_as : val :=
  fun: "t" "i" "round" =>
    let: "sz" := ws_deques_public_size "t" in
    ws_deques_public_steal_as_0 "t" "sz" "i" "round" ("sz" - #1).
