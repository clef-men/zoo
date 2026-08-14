Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import unix.unix.
Require Import zoo_std.waiter_spsc.
Require Import zoo.options.

Notation "'rcfd٠Open'" := (
  in_type "zoo_eio.rcfd.state" 0
)(in custom zoo_tag
).
Notation "'rcfd٠Closing'" := (
  in_type "zoo_eio.rcfd.state" 1
)(in custom zoo_tag
).

Notation "'rcfd٠ops'" := (
  in_type "zoo_eio.rcfd.t" 0
)(in custom zoo_field
).
Notation "'rcfd٠state'" := (
  in_type "zoo_eio.rcfd.t" 1
)(in custom zoo_field
).

Definition rcfd٠make : val :=
  𝗳𝘂𝗻 "fd" ->
    { 0, ‘rcfd٠Open@[ "fd" ] }.

Definition rcfd٠closed : val :=
  ‘rcfd٠Closing[ 𝗳𝘂𝗻 ⎽ -> () ].

Definition rcfd٠finish : val :=
  𝗳𝘂𝗻 "t" "close" "state" ->
    𝗶𝗳
      "t".{rcfd٠ops} == 0
      𝗮𝗻𝗱
      𝗰𝗮𝘀 "t".[rcfd٠state] "state" rcfd٠closed
    𝘁𝗵𝗲𝗻 (
      "close" ()
    ).

Definition rcfd٠put : val :=
  𝗳𝘂𝗻 "t" ->
    𝗹𝗲𝘁 "old" = 𝗳𝗮𝗮 "t".[rcfd٠ops] (-1) 𝗶𝗻
    𝗶𝗳 "old" == 1 𝘁𝗵𝗲𝗻 (
      𝗺𝗮𝘁𝗰𝗵 "t".{rcfd٠state} 𝘄𝗶𝘁𝗵
      | rcfd٠Open ⎽ ->
          ()
      | rcfd٠Closing "close" 𝗮𝘀 "state" ->
          rcfd٠finish "t" "close" "state"
      𝗲𝗻𝗱
    ).

Definition rcfd٠get : val :=
  𝗳𝘂𝗻 "t" ->
    𝗳𝗮𝗮 "t".[rcfd٠ops] 1 ⍮
    𝗺𝗮𝘁𝗰𝗵 "t".{rcfd٠state} 𝘄𝗶𝘁𝗵
    | rcfd٠Open "fd" ->
        ‘Some( "fd" )
    | rcfd٠Closing ⎽ ->
        rcfd٠put "t" ⍮
        §None
    𝗲𝗻𝗱.

Definition rcfd٠use : val :=
  𝗳𝘂𝗻 "t" "closed" "open_" ->
    𝗺𝗮𝘁𝗰𝗵 rcfd٠get "t" 𝘄𝗶𝘁𝗵
    | None ->
        "closed" ()
    | Some "fd" ->
        𝗹𝗲𝘁 "res" = "open_" "fd" 𝗶𝗻
        rcfd٠put "t" ⍮
        "res"
    𝗲𝗻𝗱.

Definition rcfd٠close : val :=
  𝗳𝘂𝗻 "t" ->
    𝗺𝗮𝘁𝗰𝗵 "t".{rcfd٠state} 𝘄𝗶𝘁𝗵
    | rcfd٠Closing ⎽ ->
        false
    | rcfd٠Open "fd" 𝗮𝘀 "state" ->
        𝗹𝗲𝘁 "close" ⎽ = unix٠close "fd" 𝗶𝗻
        𝗹𝗲𝘁 "new_state" = ‘rcfd٠Closing[ "close" ] 𝗶𝗻
        𝗶𝗳
          𝗰𝗮𝘀 "t".[rcfd٠state] "state" "new_state"
        𝘁𝗵𝗲𝗻 (
          rcfd٠finish "t" "close" "new_state" ⍮
          true
        ) 𝗲𝗹𝘀𝗲 (
          false
        )
    𝗲𝗻𝗱.

Definition rcfd٠remove : val :=
  𝗳𝘂𝗻 "t" ->
    𝗺𝗮𝘁𝗰𝗵 "t".{rcfd٠state} 𝘄𝗶𝘁𝗵
    | rcfd٠Closing ⎽ ->
        §None
    | rcfd٠Open "fd" 𝗮𝘀 "state" ->
        𝗹𝗲𝘁 "waiter" = waiter_spsc٠create () 𝗶𝗻
        𝗹𝗲𝘁 "new_state" =
          ‘rcfd٠Closing[ 𝗳𝘂𝗻 ⎽ -> waiter_spsc٠notify "waiter"
          ]
        𝗶𝗻
        𝗶𝗳
          𝗰𝗮𝘀 "t".[rcfd٠state] "state" "new_state"
        𝘁𝗵𝗲𝗻 (
          waiter_spsc٠wait "waiter" ⍮
          ‘Some( "fd" )
        ) 𝗲𝗹𝘀𝗲 (
          §None
        )
    𝗲𝗻𝗱.

Definition rcfd٠is_open : val :=
  𝗳𝘂𝗻 "t" ->
    𝗺𝗮𝘁𝗰𝗵 "t".{rcfd٠state} 𝘄𝗶𝘁𝗵
    | rcfd٠Open ⎽ ->
        true
    | rcfd٠Closing ⎽ ->
        false
    𝗲𝗻𝗱.

Definition rcfd٠peek : val :=
  𝗳𝘂𝗻 "t" ->
    𝗺𝗮𝘁𝗰𝗵 "t".{rcfd٠state} 𝘄𝗶𝘁𝗵
    | rcfd٠Open "fd" ->
        ‘Some( "fd" )
    | rcfd٠Closing ⎽ ->
        §None
    𝗲𝗻𝗱.
