Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo.options.

Notation "'queue_2٠Null'" := (
  in_type "zoo_std.queue_2.node" 0
)(in custom zoo_tag
).
Notation "'queue_2٠Node'" := (
  in_type "zoo_std.queue_2.node" 1
)(in custom zoo_tag
).

Notation "'queue_2٠next'" := (
  in_type "zoo_std.queue_2.node.Node" 0
)(in custom zoo_field
).
Notation "'queue_2٠data'" := (
  in_type "zoo_std.queue_2.node.Node" 1
)(in custom zoo_field
).

Notation "'queue_2٠front'" := (
  in_type "zoo_std.queue_2.t" 0
)(in custom zoo_field
).
Notation "'queue_2٠back'" := (
  in_type "zoo_std.queue_2.t" 1
)(in custom zoo_field
).

Definition queue_2٠create : val :=
  𝗳𝘂𝗻 ⎽ ->
    𝗹𝗲𝘁 "front" = ‘queue_2٠Node{ §queue_2٠Null, () } 𝗶𝗻
    { "front", "front" }.

Definition queue_2٠is_empty : val :=
  𝗳𝘂𝗻 "t" ->
    "t".{queue_2٠front} == "t".{queue_2٠back}.

Definition queue_2٠push : val :=
  𝗳𝘂𝗻 "t" "v" ->
    𝗺𝗮𝘁𝗰𝗵
      ‘queue_2٠Node{ §queue_2٠Null, () }
    𝘄𝗶𝘁𝗵
    | queue_2٠Node ⎽ ⎽ 𝗮𝘀 "new_back" ->
        𝗺𝗮𝘁𝗰𝗵 "t".{queue_2٠back} 𝘄𝗶𝘁𝗵
        | queue_2٠Node ⎽ ⎽ 𝗮𝘀 "back_r" ->
            "back_r" <-{queue_2٠next} "new_back" ⍮
            "back_r" <-{queue_2٠data} "v" ⍮
            "t" <-{queue_2٠back} "new_back"
        𝗲𝗻𝗱
    𝗲𝗻𝗱.

Definition queue_2٠pop : val :=
  𝗳𝘂𝗻 "t" ->
    𝗺𝗮𝘁𝗰𝗵 "t".{queue_2٠front} 𝘄𝗶𝘁𝗵
    | queue_2٠Node ⎽ ⎽ 𝗮𝘀 "front_r" ->
        𝗺𝗮𝘁𝗰𝗵 "front_r".{queue_2٠next} 𝘄𝗶𝘁𝗵
        | queue_2٠Null ->
            §None
        | queue_2٠Node ⎽ ⎽ 𝗮𝘀 "next" ->
            "t" <-{queue_2٠front} "next" ⍮
            ‘Some( "front_r".{queue_2٠data} )
        𝗲𝗻𝗱
    𝗲𝗻𝗱.
