Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.array.
Require Import zoo.options.

Notation "'spsc_bqueue٠data'" := (
  in_type "zoo_saturn.spsc_bqueue.t" 0
)(in custom zoo_field
).
Notation "'spsc_bqueue٠front'" := (
  in_type "zoo_saturn.spsc_bqueue.t" 1
)(in custom zoo_field
).
Notation "'spsc_bqueue٠front_cache'" := (
  in_type "zoo_saturn.spsc_bqueue.t" 2
)(in custom zoo_field
).
Notation "'spsc_bqueue٠back'" := (
  in_type "zoo_saturn.spsc_bqueue.t" 3
)(in custom zoo_field
).
Notation "'spsc_bqueue٠back_cache'" := (
  in_type "zoo_saturn.spsc_bqueue.t" 4
)(in custom zoo_field
).

Definition spsc_bqueue٠create : val :=
  𝗳𝘂𝗻 "cap" ->
    { array٠unsafe_make "cap" §None, 0, 0, 0, 0 }.

Definition spsc_bqueue٠capacity : val :=
  𝗳𝘂𝗻 "t" ->
    array٠size "t".{spsc_bqueue٠data}.

Definition spsc_bqueue٠size : val :=
  𝗳𝘂𝗻 "t" ->
    𝗹𝗲𝘁 "back" = "t".{spsc_bqueue٠back} 𝗶𝗻
    𝗹𝗲𝘁 "front" = "t".{spsc_bqueue٠front} 𝗶𝗻
    "back" - "front".

Definition spsc_bqueue٠is_empty : val :=
  𝗳𝘂𝗻 "t" ->
    spsc_bqueue٠size "t" == 0.

Definition spsc_bqueue٠push₁ : val :=
  𝗳𝘂𝗻 "t" "data" "back" ->
    𝗹𝗲𝘁 "cap" = array٠size "data" 𝗶𝗻
    𝗶𝗳
      "back" < "t".{spsc_bqueue٠front_cache} + "cap"
    𝘁𝗵𝗲𝗻 (
      true
    ) 𝗲𝗹𝘀𝗲 (
      𝗹𝗲𝘁 "front" = "t".{spsc_bqueue٠front} 𝗶𝗻
      "t" <-{spsc_bqueue٠front_cache} "front" ⍮
      "back" < "front" + "cap"
    ).

Definition spsc_bqueue٠push : val :=
  𝗳𝘂𝗻 "t" "v" ->
    𝗹𝗲𝘁 "data" = "t".{spsc_bqueue٠data} 𝗶𝗻
    𝗹𝗲𝘁 "back" = "t".{spsc_bqueue٠back} 𝗶𝗻
    𝗶𝗳 spsc_bqueue٠push₁ "t" "data" "back" 𝘁𝗵𝗲𝗻 (
      array٠unsafe_cset "data" "back" ‘Some( "v" ) ⍮
      "t" <-{spsc_bqueue٠back} "back" + 1 ⍮
      false
    ) 𝗲𝗹𝘀𝗲 (
      true
    ).

Definition spsc_bqueue٠pop₁ : val :=
  𝗳𝘂𝗻 "t" "front" ->
    𝗶𝗳 "front" < "t".{spsc_bqueue٠back_cache} 𝘁𝗵𝗲𝗻 (
      true
    ) 𝗲𝗹𝘀𝗲 (
      𝗹𝗲𝘁 "back" = "t".{spsc_bqueue٠back} 𝗶𝗻
      "t" <-{spsc_bqueue٠back_cache} "back" ⍮
      "front" < "back"
    ).

Definition spsc_bqueue٠pop : val :=
  𝗳𝘂𝗻 "t" ->
    𝗹𝗲𝘁 "front" = "t".{spsc_bqueue٠front} 𝗶𝗻
    𝗶𝗳 spsc_bqueue٠pop₁ "t" "front" 𝘁𝗵𝗲𝗻 (
      𝗹𝗲𝘁 "data" = "t".{spsc_bqueue٠data} 𝗶𝗻
      𝗹𝗲𝘁 "res" = array٠unsafe_cget "data" "front" 𝗶𝗻
      array٠unsafe_cset "data" "front" §None ⍮
      "t" <-{spsc_bqueue٠front} "front" + 1 ⍮
      "res"
    ) 𝗲𝗹𝘀𝗲 (
      §None
    ).
