From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  goption
  array
  domain.
From zoo_saturn Require Import
  bag_1__types.
From zoo Require Import
  options.

Definition bag_1٠create : val :=
  fun: "sz" =>
    { array٠unsafe_init "sz" (fun: <> => ref §Gnone), 0, 0 }.

Definition bag_1٠push₀ : val :=
  rec: "push" "slot" "o" =>
    if: ~ CAS "slot".[contents] §Gnone "o" then (
      domain٠yield () ;;
      "push" "slot" "o"
    ).

Definition bag_1٠push : val :=
  fun: "t" "v" =>
    let: "data" := "t".{data} in
    let: "i" := FAA "t".[back] 1 `rem` array٠size "data" in
    bag_1٠push₀ (array٠unsafe_get "data" "i") ‘Gsome[ "v" ].

Definition bag_1٠pop₀ : val :=
  rec: "pop" "slot" =>
    match: !"slot" with
    | Gnone =>
        "pop" "slot"
    | Gsome "v" as "o" =>
        if: CAS "slot".[contents] "o" §Gnone then (
          "v"
        ) else (
          domain٠yield () ;;
          "pop" "slot"
        )
    end.

Definition bag_1٠pop : val :=
  fun: "t" =>
    let: "data" := "t".{data} in
    let: "i" := FAA "t".[front] 1 `rem` array٠size "data" in
    bag_1٠pop₀ (array٠unsafe_get "data" "i").
