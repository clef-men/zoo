Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.array.
Require Import zoo.options.

Notation "'bqueue٠capacity'" := (
  in_type "zoo_std.bqueue.t" 0
)(in custom zoo_field
).
Notation "'bqueue٠data'" := (
  in_type "zoo_std.bqueue.t" 1
)(in custom zoo_field
).
Notation "'bqueue٠front'" := (
  in_type "zoo_std.bqueue.t" 2
)(in custom zoo_field
).
Notation "'bqueue٠back'" := (
  in_type "zoo_std.bqueue.t" 3
)(in custom zoo_field
).

Definition bqueue٠create : val :=
  𝗳𝘂𝗻 "cap" ->
    { "cap", array٠unsafe_make "cap" (), 0, 0 }.

Definition bqueue٠size : val :=
  𝗳𝘂𝗻 "t" ->
    "t".{bqueue٠back} - "t".{bqueue٠front}.

Definition bqueue٠is_empty : val :=
  𝗳𝘂𝗻 "t" ->
    bqueue٠size "t" == 0.

Definition bqueue٠unsafe_get : val :=
  𝗳𝘂𝗻 "t" "i" ->
    array٠unsafe_cget "t".{bqueue٠data} ("t".{bqueue٠front} + "i").

Definition bqueue٠unsafe_set : val :=
  𝗳𝘂𝗻 "t" "i" "v" ->
    array٠unsafe_cset "t".{bqueue٠data} ("t".{bqueue٠front} + "i") "v".

Definition bqueue٠push : val :=
  𝗳𝘂𝗻 "t" "v" ->
    𝗹𝗲𝘁 "front" = "t".{bqueue٠front} 𝗶𝗻
    𝗹𝗲𝘁 "back" = "t".{bqueue٠back} 𝗶𝗻
    𝗶𝗳 "front" + "t".{bqueue٠capacity} == "back" 𝘁𝗵𝗲𝗻 (
      false
    ) 𝗲𝗹𝘀𝗲 (
      array٠unsafe_cset "t".{bqueue٠data} "back" "v" ⍮
      "t" <-{bqueue٠back} "back" + 1 ⍮
      true
    ).

Definition bqueue٠pop_front : val :=
  𝗳𝘂𝗻 "t" ->
    𝗹𝗲𝘁 "front" = "t".{bqueue٠front} 𝗶𝗻
    𝗹𝗲𝘁 "back" = "t".{bqueue٠back} 𝗶𝗻
    𝗶𝗳 "front" == "back" 𝘁𝗵𝗲𝗻 (
      §None
    ) 𝗲𝗹𝘀𝗲 (
      𝗹𝗲𝘁 "data" = "t".{bqueue٠data} 𝗶𝗻
      𝗹𝗲𝘁 "v" = array٠unsafe_cget "data" "front" 𝗶𝗻
      array٠unsafe_cset "data" "front" () ⍮
      "t" <-{bqueue٠front} "front" + 1 ⍮
      ‘Some( "v" )
    ).

Definition bqueue٠pop_back : val :=
  𝗳𝘂𝗻 "t" ->
    𝗹𝗲𝘁 "front" = "t".{bqueue٠front} 𝗶𝗻
    𝗹𝗲𝘁 "back" = "t".{bqueue٠back} 𝗶𝗻
    𝗶𝗳 "front" == "back" 𝘁𝗵𝗲𝗻 (
      §None
    ) 𝗲𝗹𝘀𝗲 (
      𝗹𝗲𝘁 "data" = "t".{bqueue٠data} 𝗶𝗻
      𝗹𝗲𝘁 "back" = "back" - 1 𝗶𝗻
      𝗹𝗲𝘁 "v" = array٠unsafe_cget "data" "back" 𝗶𝗻
      array٠unsafe_cset "data" "back" () ⍮
      "t" <-{bqueue٠back} "back" ⍮
      ‘Some( "v" )
    ).
