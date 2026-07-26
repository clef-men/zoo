Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.array.
Require Import zoo_std.bqueue__types.
Require Import zoo.options.

Definition bqueue٠create : val :=
  𝗳𝘂𝗻 "cap" ->
    { "cap", array٠unsafe_make "cap" (), 0, 0 }.

Definition bqueue٠size : val :=
  𝗳𝘂𝗻 "t" ->
    "t".{back} - "t".{front}.

Definition bqueue٠is_empty : val :=
  𝗳𝘂𝗻 "t" ->
    bqueue٠size "t" == 0.

Definition bqueue٠unsafe_get : val :=
  𝗳𝘂𝗻 "t" "i" ->
    array٠unsafe_cget "t".{data} ("t".{front} + "i").

Definition bqueue٠unsafe_set : val :=
  𝗳𝘂𝗻 "t" "i" "v" ->
    array٠unsafe_cset "t".{data} ("t".{front} + "i") "v".

Definition bqueue٠push : val :=
  𝗳𝘂𝗻 "t" "v" ->
    𝗹𝗲𝘁 "front" = "t".{front} 𝗶𝗻
    𝗹𝗲𝘁 "back" = "t".{back} 𝗶𝗻
    𝗶𝗳 "front" + "t".{capacity} == "back" 𝘁𝗵𝗲𝗻 (
      false
    ) 𝗲𝗹𝘀𝗲 (
      array٠unsafe_cset "t".{data} "back" "v" ⍮
      "t" <-{back} "back" + 1 ⍮
      true
    ).

Definition bqueue٠pop_front : val :=
  𝗳𝘂𝗻 "t" ->
    𝗹𝗲𝘁 "front" = "t".{front} 𝗶𝗻
    𝗹𝗲𝘁 "back" = "t".{back} 𝗶𝗻
    𝗶𝗳 "front" == "back" 𝘁𝗵𝗲𝗻 (
      §None
    ) 𝗲𝗹𝘀𝗲 (
      𝗹𝗲𝘁 "data" = "t".{data} 𝗶𝗻
      𝗹𝗲𝘁 "v" = array٠unsafe_cget "data" "front" 𝗶𝗻
      array٠unsafe_cset "data" "front" () ⍮
      "t" <-{front} "front" + 1 ⍮
      ‘Some( "v" )
    ).

Definition bqueue٠pop_back : val :=
  𝗳𝘂𝗻 "t" ->
    𝗹𝗲𝘁 "front" = "t".{front} 𝗶𝗻
    𝗹𝗲𝘁 "back" = "t".{back} 𝗶𝗻
    𝗶𝗳 "front" == "back" 𝘁𝗵𝗲𝗻 (
      §None
    ) 𝗲𝗹𝘀𝗲 (
      𝗹𝗲𝘁 "data" = "t".{data} 𝗶𝗻
      𝗹𝗲𝘁 "back" = "back" - 1 𝗶𝗻
      𝗹𝗲𝘁 "v" = array٠unsafe_cget "data" "back" 𝗶𝗻
      array٠unsafe_cset "data" "back" () ⍮
      "t" <-{back} "back" ⍮
      ‘Some( "v" )
    ).
