Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_saturn.ws_bdeque_2.
Require Import zoo_std.array.
Require Import zoo_std.random_round.
Require Import zoo_parabs.ws_bdeques_public__types.
Require Import zoo.options.

Definition ws_bdeques_public٠capacity : val :=
  256.

Definition ws_bdeques_public٠create : val :=
  fun: "sz" =>
    array٠unsafe_init
      "sz"
      (fun: <> => ws_bdeque_2٠create ws_bdeques_public٠capacity).

Definition ws_bdeques_public٠size : val :=
  array٠size.

Definition ws_bdeques_public٠block : val :=
  fun: "_t" "_i" =>
    ().

Definition ws_bdeques_public٠unblock : val :=
  fun: "_t" "_i" =>
    ().

Definition ws_bdeques_public٠push : val :=
  fun: "t" "i" "v" =>
    let: "queue" := array٠unsafe_get "t" "i" in
    ws_bdeque_2٠push "queue" "v".

Definition ws_bdeques_public٠pop : val :=
  fun: "t" "i" =>
    let: "queue" := array٠unsafe_get "t" "i" in
    ws_bdeque_2٠pop "queue".

Definition ws_bdeques_public٠steal_to : val :=
  fun: "t" "_i" "j" =>
    let: "queue" := array٠unsafe_get "t" "j" in
    ws_bdeque_2٠steal "queue".

Definition ws_bdeques_public٠steal_as₀ : val :=
  rec: "steal_as" "t" "sz" "i" "round" "n" =>
    if: "n" ≤ 0 then (
      §None
    ) else (
      let: "j" := ("i" + 1 + random_round٠next "round") `rem` "sz" in
      match: ws_bdeques_public٠steal_to "t" "i" "j" with
      | None =>
          "steal_as" "t" "sz" "i" "round" ("n" - 1)
      |_ as "res" =>
          "res"
      end
    ).

Definition ws_bdeques_public٠steal_as : val :=
  fun: "t" "i" "round" =>
    let: "sz" := ws_bdeques_public٠size "t" in
    ws_bdeques_public٠steal_as₀ "t" "sz" "i" "round" ("sz" - 1).
