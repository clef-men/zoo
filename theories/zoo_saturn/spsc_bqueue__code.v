Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.array.
Require Import zoo_saturn.spsc_bqueue__types.
Require Import zoo.options.

Definition spsc_bqueue٠create : val :=
  𝗳𝘂𝗻 "cap" ->
    { array٠unsafe_make "cap" §None, 0, 0, 0, 0 }.

Definition spsc_bqueue٠capacity : val :=
  𝗳𝘂𝗻 "t" ->
    array٠size "t".{data}.

Definition spsc_bqueue٠size : val :=
  𝗳𝘂𝗻 "t" ->
    𝗹𝗲𝘁 "back" = "t".{back} 𝗶𝗻
    𝗹𝗲𝘁 "front" = "t".{front} 𝗶𝗻
    "back" - "front".

Definition spsc_bqueue٠is_empty : val :=
  𝗳𝘂𝗻 "t" ->
    spsc_bqueue٠size "t" == 0.

Definition spsc_bqueue٠push₀ : val :=
  𝗳𝘂𝗻 "t" "data" "back" ->
    𝗹𝗲𝘁 "cap" = array٠size "data" 𝗶𝗻
    𝗶𝗳 "back" < "t".{front_cache} + "cap" 𝘁𝗵𝗲𝗻 (
      true
    ) 𝗲𝗹𝘀𝗲 (
      𝗹𝗲𝘁 "front" = "t".{front} 𝗶𝗻
      "t" <-{front_cache} "front" ⍮
      "back" < "front" + "cap"
    ).

Definition spsc_bqueue٠push : val :=
  𝗳𝘂𝗻 "t" "v" ->
    𝗹𝗲𝘁 "data" = "t".{data} 𝗶𝗻
    𝗹𝗲𝘁 "back" = "t".{back} 𝗶𝗻
    𝗶𝗳 spsc_bqueue٠push₀ "t" "data" "back" 𝘁𝗵𝗲𝗻 (
      array٠unsafe_cset "data" "back" ‘Some( "v" ) ⍮
      "t" <-{back} "back" + 1 ⍮
      false
    ) 𝗲𝗹𝘀𝗲 (
      true
    ).

Definition spsc_bqueue٠pop₀ : val :=
  𝗳𝘂𝗻 "t" "front" ->
    𝗶𝗳 "front" < "t".{back_cache} 𝘁𝗵𝗲𝗻 (
      true
    ) 𝗲𝗹𝘀𝗲 (
      𝗹𝗲𝘁 "back" = "t".{back} 𝗶𝗻
      "t" <-{back_cache} "back" ⍮
      "front" < "back"
    ).

Definition spsc_bqueue٠pop : val :=
  𝗳𝘂𝗻 "t" ->
    𝗹𝗲𝘁 "front" = "t".{front} 𝗶𝗻
    𝗶𝗳 spsc_bqueue٠pop₀ "t" "front" 𝘁𝗵𝗲𝗻 (
      𝗹𝗲𝘁 "data" = "t".{data} 𝗶𝗻
      𝗹𝗲𝘁 "res" = array٠unsafe_cget "data" "front" 𝗶𝗻
      array٠unsafe_cset "data" "front" §None ⍮
      "t" <-{front} "front" + 1 ⍮
      "res"
    ) 𝗲𝗹𝘀𝗲 (
      §None
    ).
