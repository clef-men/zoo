Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.array.
Require Import zoo_std.domain.
Require Import zoo_std.goption.
Require Import zoo_saturn.bag_1__types.
Require Import zoo.options.

Definition bag_1٠create : val :=
  𝗳𝘂𝗻 "sz" ->
    { array٠unsafe_init "sz" (𝗳𝘂𝗻 ⎽ -> 𝗿𝗲𝗳 §Gnone),
      0,
      0
    }.

Definition bag_1٠push₀ : val :=
  𝗿𝗲𝗰 "push" "slot" "o" ->
    𝗶𝗳 ~ 𝗰𝗮𝘀 "slot".[contents] §Gnone "o" 𝘁𝗵𝗲𝗻 (
      domain٠yield () ⍮
      "push" "slot" "o"
    ).

Definition bag_1٠push : val :=
  𝗳𝘂𝗻 "t" "v" ->
    𝗹𝗲𝘁 "data" = "t".{data} 𝗶𝗻
    𝗹𝗲𝘁 "i" =
      𝗳𝗮𝗮 "t".[back] 1 𝗿𝗲𝗺 array٠size "data"
    𝗶𝗻
    bag_1٠push₀ (array٠unsafe_get "data" "i") ‘Gsome[ "v" ].

Definition bag_1٠pop₀ : val :=
  𝗿𝗲𝗰 "pop" "slot" ->
    𝗺𝗮𝘁𝗰𝗵 !"slot" 𝘄𝗶𝘁𝗵
    | Gnone ->
        "pop" "slot"
    | Gsome "v" 𝗮𝘀 "o" ->
        𝗶𝗳
          𝗰𝗮𝘀 "slot".[contents] "o" §Gnone
        𝘁𝗵𝗲𝗻 (
          "v"
        ) 𝗲𝗹𝘀𝗲 (
          domain٠yield () ⍮
          "pop" "slot"
        )
    𝗲𝗻𝗱.

Definition bag_1٠pop : val :=
  𝗳𝘂𝗻 "t" ->
    𝗹𝗲𝘁 "data" = "t".{data} 𝗶𝗻
    𝗹𝗲𝘁 "i" =
      𝗳𝗮𝗮 "t".[front] 1 𝗿𝗲𝗺 array٠size "data"
    𝗶𝗻
    bag_1٠pop₀ (array٠unsafe_get "data" "i").
