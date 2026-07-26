Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import unix.unix.
Require Import zoo_std.spsc_waiter.
Require Import zoo_eio.rcfd__types.
Require Import zoo.options.

Definition rcfd٠make : val :=
  𝗳𝘂𝗻 "fd" ->
    { 0, ‘Open@[ "fd" ] }.

Definition rcfd٠closed : val :=
  ‘Closing[ 𝗳𝘂𝗻 ⎽ -> () ].

Definition rcfd٠finish : val :=
  𝗳𝘂𝗻 "t" "close" "state" ->
    𝗶𝗳
      "t".{ops} == 0
      𝗮𝗻𝗱
      𝗰𝗮𝘀 "t".[state] "state" rcfd٠closed
    𝘁𝗵𝗲𝗻 (
      "close" ()
    ).

Definition rcfd٠put : val :=
  𝗳𝘂𝗻 "t" ->
    𝗹𝗲𝘁 "old" = 𝗳𝗮𝗮 "t".[ops] (-1) 𝗶𝗻
    𝗶𝗳 "old" == 1 𝘁𝗵𝗲𝗻 (
      𝗺𝗮𝘁𝗰𝗵 "t".{state} 𝘄𝗶𝘁𝗵
      | Open ⎽ ->
          ()
      | Closing "close" 𝗮𝘀 "state" ->
          rcfd٠finish "t" "close" "state"
      𝗲𝗻𝗱
    ).

Definition rcfd٠get : val :=
  𝗳𝘂𝗻 "t" ->
    𝗳𝗮𝗮 "t".[ops] 1 ⍮
    𝗺𝗮𝘁𝗰𝗵 "t".{state} 𝘄𝗶𝘁𝗵
    | Open "fd" ->
        ‘Some( "fd" )
    | Closing ⎽ ->
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
    𝗺𝗮𝘁𝗰𝗵 "t".{state} 𝘄𝗶𝘁𝗵
    | Closing ⎽ ->
        false
    | Open "fd" 𝗮𝘀 "state" ->
        𝗹𝗲𝘁 "close" ⎽ = unix٠close "fd" 𝗶𝗻
        𝗹𝗲𝘁 "new_state" = ‘Closing[ "close" ] 𝗶𝗻
        𝗶𝗳
          𝗰𝗮𝘀 "t".[state] "state" "new_state"
        𝘁𝗵𝗲𝗻 (
          rcfd٠finish "t" "close" "new_state" ⍮
          true
        ) 𝗲𝗹𝘀𝗲 (
          false
        )
    𝗲𝗻𝗱.

Definition rcfd٠remove : val :=
  𝗳𝘂𝗻 "t" ->
    𝗺𝗮𝘁𝗰𝗵 "t".{state} 𝘄𝗶𝘁𝗵
    | Closing ⎽ ->
        §None
    | Open "fd" 𝗮𝘀 "state" ->
        𝗹𝗲𝘁 "waiter" = spsc_waiter٠create () 𝗶𝗻
        𝗹𝗲𝘁 "new_state" =
          ‘Closing[ 𝗳𝘂𝗻 ⎽ -> spsc_waiter٠notify "waiter" ]
        𝗶𝗻
        𝗶𝗳
          𝗰𝗮𝘀 "t".[state] "state" "new_state"
        𝘁𝗵𝗲𝗻 (
          spsc_waiter٠wait "waiter" ⍮
          ‘Some( "fd" )
        ) 𝗲𝗹𝘀𝗲 (
          §None
        )
    𝗲𝗻𝗱.

Definition rcfd٠is_open : val :=
  𝗳𝘂𝗻 "t" ->
    𝗺𝗮𝘁𝗰𝗵 "t".{state} 𝘄𝗶𝘁𝗵
    | Open ⎽ ->
        true
    | Closing ⎽ ->
        false
    𝗲𝗻𝗱.

Definition rcfd٠peek : val :=
  𝗳𝘂𝗻 "t" ->
    𝗺𝗮𝘁𝗰𝗵 "t".{state} 𝘄𝗶𝘁𝗵
    | Open "fd" ->
        ‘Some( "fd" )
    | Closing ⎽ ->
        §None
    𝗲𝗻𝗱.
