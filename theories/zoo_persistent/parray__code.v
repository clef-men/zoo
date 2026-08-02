Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.array.
Require Import zoo_persistent.parray__types.
Require Import zoo.options.

Definition parray٠make : val :=
  𝗳𝘂𝗻 "equal" "sz" "v" ->
    𝗹𝗲𝘁 "data" = array٠unsafe_make "sz" "v" 𝗶𝗻
    𝗿𝗲𝗳 ‘Root( "equal", "data" ).

Definition parray٠reroot₁ : val :=
  𝗿𝗲𝗰 "reroot" "t" ->
    𝗺𝗮𝘁𝗰𝗵 !"t" 𝘄𝗶𝘁𝗵
    | Root ⎽ ⎽ 𝗮𝘀 "root_r" ->
        ("root_r".<equal>, "root_r".<data>)
    | Diff "i" "v" "t'" ->
        𝗹𝗲𝘁 "equal", "data" = "reroot" "t'" 𝗶𝗻
        "t'" <- ‘Diff( "i", array٠unsafe_get "data" "i", "t" ) ⍮
        array٠unsafe_set "data" "i" "v" ⍮
        ("equal", "data")
    𝗲𝗻𝗱.

Definition parray٠reroot : val :=
  𝗳𝘂𝗻 "t" ->
    𝗺𝗮𝘁𝗰𝗵 !"t" 𝘄𝗶𝘁𝗵
    | Root ⎽ ⎽ 𝗮𝘀 "root_r" ->
        ("root_r".<equal>, "root_r".<data>)
    | Diff ⎽ ⎽ ⎽ ->
        𝗹𝗲𝘁 "equal", "data" = parray٠reroot₁ "t" 𝗶𝗻
        "t" <- ‘Root( "equal", "data" ) ⍮
        ("equal", "data")
    𝗲𝗻𝗱.

Definition parray٠get : val :=
  𝗳𝘂𝗻 "t" "i" ->
    𝗹𝗲𝘁 ⎽, "data" = parray٠reroot "t" 𝗶𝗻
    array٠unsafe_get "data" "i".

Definition parray٠set : val :=
  𝗳𝘂𝗻 "t" "i" "v" ->
    𝗹𝗲𝘁 "equal", "data" = parray٠reroot "t" 𝗶𝗻
    𝗹𝗲𝘁 "v'" = array٠unsafe_get "data" "i" 𝗶𝗻
    𝗶𝗳 "equal" "v" "v'" 𝘁𝗵𝗲𝗻 (
      "t"
    ) 𝗲𝗹𝘀𝗲 (
      array٠unsafe_set "data" "i" "v" ⍮
      𝗹𝗲𝘁 "t'" = 𝗿𝗲𝗳 !"t" 𝗶𝗻
      "t" <- ‘Diff( "i", "v'", "t'" ) ⍮
      "t'"
    ).
