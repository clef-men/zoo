Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.domain.
Require Import zoo_saturn.spmc_queue__types.
Require Import zoo.options.

Definition spmc_queue٠create : val :=
  𝗳𝘂𝗻 ⎽ ->
    𝗹𝗲𝘁 "front" = ‘Node{ §Null, () } 𝗶𝗻
    { "front", "front" }.

Definition spmc_queue٠is_empty : val :=
  𝗳𝘂𝗻 "t" ->
    𝗺𝗮𝘁𝗰𝗵 "t".{front} 𝘄𝗶𝘁𝗵
    | Node ⎽ ⎽ 𝗮𝘀 "front_r" ->
        "front_r".{next} == §Null
    𝗲𝗻𝗱.

Definition spmc_queue٠push : val :=
  𝗳𝘂𝗻 "t" "v" ->
    𝗺𝗮𝘁𝗰𝗵 ‘Node{ §Null, "v" } 𝘄𝗶𝘁𝗵
    | Node ⎽ ⎽ 𝗮𝘀 "new_back" ->
        𝗺𝗮𝘁𝗰𝗵 "t".{back} 𝘄𝗶𝘁𝗵
        | Node ⎽ ⎽ 𝗮𝘀 "back_r" ->
            "back_r" <-{next} "new_back" ⍮
            "t" <-{back} "new_back"
        𝗲𝗻𝗱
    𝗲𝗻𝗱.

Definition spmc_queue٠pop : val :=
  𝗿𝗲𝗰 "pop" "t" ->
    𝗺𝗮𝘁𝗰𝗵 "t".{front} 𝘄𝗶𝘁𝗵
    | Node ⎽ ⎽ 𝗮𝘀 "front" ->
        𝗹𝗲𝘁 "front_r" = "front" 𝗶𝗻
        𝗺𝗮𝘁𝗰𝗵 "front_r".{next} 𝘄𝗶𝘁𝗵
        | Null ->
            §None
        | Node ⎽ ⎽ 𝗮𝘀 "new_front" ->
            𝗹𝗲𝘁 "new_front_r" = "new_front" 𝗶𝗻
            𝗶𝗳
              𝗰𝗮𝘀 "t".[front] "front" "new_front"
            𝘁𝗵𝗲𝗻 (
              𝗹𝗲𝘁 "v" = "new_front_r".{data} 𝗶𝗻
              "new_front_r" <-{data} () ⍮
              ‘Some( "v" )
            ) 𝗲𝗹𝘀𝗲 (
              domain٠yield () ⍮
              "pop" "t"
            )
        𝗲𝗻𝗱
    𝗲𝗻𝗱.
