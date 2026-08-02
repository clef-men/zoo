Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.array.
Require Import zoo_std.int.
Require Import zoo.options.

Notation "'queue_3٠data'" := (
  in_type "zoo_std.queue_3.t" 0
)(in custom zoo_field
).
Notation "'queue_3٠front'" := (
  in_type "zoo_std.queue_3.t" 1
)(in custom zoo_field
).
Notation "'queue_3٠back'" := (
  in_type "zoo_std.queue_3.t" 2
)(in custom zoo_field
).

Definition queue_3٠min_capacity : val :=
  16.

Definition queue_3٠create : val :=
  𝗳𝘂𝗻 ⎽ ->
    { array٠unsafe_make queue_3٠min_capacity (), 0, 0 }.

Definition queue_3٠size : val :=
  𝗳𝘂𝗻 "t" ->
    "t".{queue_3٠back} - "t".{queue_3٠front}.

Definition queue_3٠is_empty : val :=
  𝗳𝘂𝗻 "t" ->
    queue_3٠size "t" == 0.

Definition queue_3٠unsafe_get : val :=
  𝗳𝘂𝗻 "t" "i" ->
    array٠unsafe_cget "t".{queue_3٠data} ("t".{queue_3٠front} + "i").

Definition queue_3٠unsafe_set : val :=
  𝗳𝘂𝗻 "t" "i" "v" ->
    array٠unsafe_cset "t".{queue_3٠data} ("t".{queue_3٠front} + "i") "v".

Definition queue_3٠next_capacity : val :=
  𝗳𝘂𝗻 "n" ->
    int٠max
      8
      𝗶𝗳 "n" ≤ 512 𝘁𝗵𝗲𝗻 (
        2 * "n"
      ) 𝗲𝗹𝘀𝗲 (
        "n" + "n" 𝗾𝘂𝗼𝘁 2
      ).

Definition queue_3٠grow : val :=
  𝗳𝘂𝗻 "t" ->
    𝗹𝗲𝘁 "front" = "t".{queue_3٠front} 𝗶𝗻
    𝗹𝗲𝘁 "back" = "t".{queue_3٠back} 𝗶𝗻
    𝗹𝗲𝘁 "data" = "t".{queue_3٠data} 𝗶𝗻
    𝗹𝗲𝘁 "cap" = array٠size "data" 𝗶𝗻
    𝗶𝗳 "front" + "cap" == "back" 𝘁𝗵𝗲𝗻 (
      𝗹𝗲𝘁 "new_cap" =
        int٠max ("cap" + 1) (queue_3٠next_capacity "cap")
      𝗶𝗻
      𝗹𝗲𝘁 "new_data" =
        array٠unsafe_cgrow "data" "front" "new_cap" ()
      𝗶𝗻
      "t" <-{queue_3٠data} "new_data"
    ).

Definition queue_3٠push : val :=
  𝗳𝘂𝗻 "t" "v" ->
    queue_3٠grow "t" ⍮
    𝗹𝗲𝘁 "back" = "t".{queue_3٠back} 𝗶𝗻
    array٠unsafe_cset "t".{queue_3٠data} "back" "v" ⍮
    "t" <-{queue_3٠back} "back" + 1.

Definition queue_3٠shrink : val :=
  𝗳𝘂𝗻 "t" ->
    𝗹𝗲𝘁 "front" = "t".{queue_3٠front} 𝗶𝗻
    𝗹𝗲𝘁 "back" = "t".{queue_3٠back} 𝗶𝗻
    𝗹𝗲𝘁 "sz" = "back" - "front" 𝗶𝗻
    𝗹𝗲𝘁 "data" = "t".{queue_3٠data} 𝗶𝗻
    𝗹𝗲𝘁 "cap" = array٠size "data" 𝗶𝗻
    𝗶𝗳 queue_3٠min_capacity + 3 * "sz" ≤ "cap" 𝘁𝗵𝗲𝗻 (
      𝗹𝗲𝘁 "new_cap" = "cap" 𝗹𝘀𝗿 1 + 1 𝗶𝗻
      𝗹𝗲𝘁 "new_data" =
        array٠unsafe_cshrink_slice "data" "front" "new_cap"
      𝗶𝗻
      "t" <-{queue_3٠data} "new_data"
    ).

Definition queue_3٠pop_front : val :=
  𝗳𝘂𝗻 "t" ->
    𝗹𝗲𝘁 "front" = "t".{queue_3٠front} 𝗶𝗻
    𝗹𝗲𝘁 "back" = "t".{queue_3٠back} 𝗶𝗻
    𝗶𝗳 "front" == "back" 𝘁𝗵𝗲𝗻 (
      §None
    ) 𝗲𝗹𝘀𝗲 (
      𝗹𝗲𝘁 "data" = "t".{queue_3٠data} 𝗶𝗻
      𝗹𝗲𝘁 "v" = array٠unsafe_cget "data" "front" 𝗶𝗻
      array٠unsafe_cset "data" "front" () ⍮
      "t" <-{queue_3٠front} "front" + 1 ⍮
      queue_3٠shrink "t" ⍮
      ‘Some( "v" )
    ).

Definition queue_3٠pop_back : val :=
  𝗳𝘂𝗻 "t" ->
    𝗹𝗲𝘁 "front" = "t".{queue_3٠front} 𝗶𝗻
    𝗹𝗲𝘁 "back" = "t".{queue_3٠back} 𝗶𝗻
    𝗶𝗳 "front" == "back" 𝘁𝗵𝗲𝗻 (
      §None
    ) 𝗲𝗹𝘀𝗲 (
      𝗹𝗲𝘁 "data" = "t".{queue_3٠data} 𝗶𝗻
      𝗹𝗲𝘁 "back" = "back" - 1 𝗶𝗻
      𝗹𝗲𝘁 "v" = array٠unsafe_cget "data" "back" 𝗶𝗻
      array٠unsafe_cset "data" "back" () ⍮
      "t" <-{queue_3٠back} "back" ⍮
      queue_3٠shrink "t" ⍮
      ‘Some( "v" )
    ).
