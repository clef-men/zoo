Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.queue_2__types.
Require Import zoo.options.

Definition queue_2٠create : val :=
  𝗳𝘂𝗻 ⎽ ->
    𝗹𝗲𝘁 "front" = ‘Node{ §Null, () } 𝗶𝗻
    { "front", "front" }.

Definition queue_2٠is_empty : val :=
  𝗳𝘂𝗻 "t" ->
    "t".{front} == "t".{back}.

Definition queue_2٠push : val :=
  𝗳𝘂𝗻 "t" "v" ->
    𝗺𝗮𝘁𝗰𝗵 ‘Node{ §Null, () } 𝘄𝗶𝘁𝗵
    | Node ⎽ ⎽ 𝗮𝘀 "new_back" ->
        𝗺𝗮𝘁𝗰𝗵 "t".{back} 𝘄𝗶𝘁𝗵
        | Node ⎽ ⎽ 𝗮𝘀 "back_r" ->
            "back_r" <-{next} "new_back" ⍮
            "back_r" <-{data} "v" ⍮
            "t" <-{back} "new_back"
        𝗲𝗻𝗱
    𝗲𝗻𝗱.

Definition queue_2٠pop : val :=
  𝗳𝘂𝗻 "t" ->
    𝗺𝗮𝘁𝗰𝗵 "t".{front} 𝘄𝗶𝘁𝗵
    | Node ⎽ ⎽ 𝗮𝘀 "front_r" ->
        𝗺𝗮𝘁𝗰𝗵 "front_r".{next} 𝘄𝗶𝘁𝗵
        | Null ->
            §None
        | Node ⎽ ⎽ 𝗮𝘀 "next" ->
            "t" <-{front} "next" ⍮
            ‘Some( "front_r".{data} )
        𝗲𝗻𝗱
    𝗲𝗻𝗱.
