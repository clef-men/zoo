Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.array.
Require Import zoo_std.domain.
Require Import zoo_std.goption.
Require Import zoo.options.

Notation "'bag_1٠data'" := (
  in_type "zoo_saturn.bag_1.t" 0
)(in custom zoo_field
).
Notation "'bag_1٠front'" := (
  in_type "zoo_saturn.bag_1.t" 1
)(in custom zoo_field
).
Notation "'bag_1٠back'" := (
  in_type "zoo_saturn.bag_1.t" 2
)(in custom zoo_field
).

Definition bag_1٠create : val :=
  𝗳𝘂𝗻 "sz" ->
    { array٠unsafe_init
        "sz"
        (𝗳𝘂𝗻 ⎽ -> 𝗿𝗲𝗳 §goption٠None),
      0,
      0
    }.

Definition bag_1٠push₁ : val :=
  𝗿𝗲𝗰 "push" "slot" "o" ->
    𝗶𝗳
      ~ 𝗰𝗮𝘀 "slot".[contents] §goption٠None "o"
    𝘁𝗵𝗲𝗻 (
      domain٠yield () ⍮
      "push" "slot" "o"
    ).

Definition bag_1٠push : val :=
  𝗳𝘂𝗻 "t" "v" ->
    𝗹𝗲𝘁 "data" = "t".{bag_1٠data} 𝗶𝗻
    𝗹𝗲𝘁 "i" =
      𝗳𝗮𝗮 "t".[bag_1٠back] 1 𝗿𝗲𝗺 array٠size "data"
    𝗶𝗻
    bag_1٠push₁ (array٠unsafe_get "data" "i") ‘goption٠Some[ "v" ].

Definition bag_1٠pop₁ : val :=
  𝗿𝗲𝗰 "pop" "slot" ->
    𝗺𝗮𝘁𝗰𝗵 !"slot" 𝘄𝗶𝘁𝗵
    | goption٠None ->
        "pop" "slot"
    | goption٠Some "v" 𝗮𝘀 "o" ->
        𝗶𝗳
          𝗰𝗮𝘀 "slot".[contents] "o" §goption٠None
        𝘁𝗵𝗲𝗻 (
          "v"
        ) 𝗲𝗹𝘀𝗲 (
          domain٠yield () ⍮
          "pop" "slot"
        )
    𝗲𝗻𝗱.

Definition bag_1٠pop : val :=
  𝗳𝘂𝗻 "t" ->
    𝗹𝗲𝘁 "data" = "t".{bag_1٠data} 𝗶𝗻
    𝗹𝗲𝘁 "i" =
      𝗳𝗮𝗮 "t".[bag_1٠front] 1 𝗿𝗲𝗺 array٠size "data"
    𝗶𝗻
    bag_1٠pop₁ (array٠unsafe_get "data" "i").
