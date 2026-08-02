Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.domain.
Require Import zoo.options.

Notation "'spmc_queue٠Null'" := (
  in_type "zoo_saturn.spmc_queue.node" 0
)(in custom zoo_tag
).
Notation "'spmc_queue٠Node'" := (
  in_type "zoo_saturn.spmc_queue.node" 1
)(in custom zoo_tag
).

Notation "'spmc_queue٠next'" := (
  in_type "zoo_saturn.spmc_queue.node.Node" 0
)(in custom zoo_field
).
Notation "'spmc_queue٠data'" := (
  in_type "zoo_saturn.spmc_queue.node.Node" 1
)(in custom zoo_field
).

Notation "'spmc_queue٠front'" := (
  in_type "zoo_saturn.spmc_queue.t" 0
)(in custom zoo_field
).
Notation "'spmc_queue٠back'" := (
  in_type "zoo_saturn.spmc_queue.t" 1
)(in custom zoo_field
).

Definition spmc_queue٠create : val :=
  𝗳𝘂𝗻 ⎽ ->
    𝗹𝗲𝘁 "front" =
      ‘spmc_queue٠Node{ §spmc_queue٠Null, () }
    𝗶𝗻
    { "front", "front" }.

Definition spmc_queue٠is_empty : val :=
  𝗳𝘂𝗻 "t" ->
    𝗺𝗮𝘁𝗰𝗵 "t".{spmc_queue٠front} 𝘄𝗶𝘁𝗵
    | spmc_queue٠Node ⎽ ⎽ 𝗮𝘀 "front_r" ->
        "front_r".{spmc_queue٠next} == §spmc_queue٠Null
    𝗲𝗻𝗱.

Definition spmc_queue٠push : val :=
  𝗳𝘂𝗻 "t" "v" ->
    𝗺𝗮𝘁𝗰𝗵
      ‘spmc_queue٠Node{ §spmc_queue٠Null, "v" }
    𝘄𝗶𝘁𝗵
    | spmc_queue٠Node ⎽ ⎽ 𝗮𝘀 "new_back" ->
        𝗺𝗮𝘁𝗰𝗵 "t".{spmc_queue٠back} 𝘄𝗶𝘁𝗵
        | spmc_queue٠Node ⎽ ⎽ 𝗮𝘀 "back_r" ->
            "back_r" <-{spmc_queue٠next} "new_back" ⍮
            "t" <-{spmc_queue٠back} "new_back"
        𝗲𝗻𝗱
    𝗲𝗻𝗱.

Definition spmc_queue٠pop : val :=
  𝗿𝗲𝗰 "pop" "t" ->
    𝗺𝗮𝘁𝗰𝗵 "t".{spmc_queue٠front} 𝘄𝗶𝘁𝗵
    | spmc_queue٠Node ⎽ ⎽ 𝗮𝘀 "front" ->
        𝗹𝗲𝘁 "front_r" = "front" 𝗶𝗻
        𝗺𝗮𝘁𝗰𝗵 "front_r".{spmc_queue٠next} 𝘄𝗶𝘁𝗵
        | spmc_queue٠Null ->
            §None
        | spmc_queue٠Node ⎽ ⎽ 𝗮𝘀 "new_front" ->
            𝗹𝗲𝘁 "new_front_r" = "new_front" 𝗶𝗻
            𝗶𝗳
              𝗰𝗮𝘀 "t".[spmc_queue٠front] "front" "new_front"
            𝘁𝗵𝗲𝗻 (
              𝗹𝗲𝘁 "v" = "new_front_r".{spmc_queue٠data} 𝗶𝗻
              "new_front_r" <-{spmc_queue٠data} () ⍮
              ‘Some( "v" )
            ) 𝗲𝗹𝘀𝗲 (
              domain٠yield () ⍮
              "pop" "t"
            )
        𝗲𝗻𝗱
    𝗲𝗻𝗱.
