Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.clist.
Require Import zoo_std.domain.
Require Import zoo_saturn.mpsc_queue_3__types.
Require Import zoo.options.

Definition mpsc_queue_3٠create : val :=
  𝗳𝘂𝗻 ⎽ ->
    { §ClistOpen, §ClistOpen }.

Definition mpsc_queue_3٠is_empty : val :=
  𝗳𝘂𝗻 "t" ->
    𝗺𝗮𝘁𝗰𝗵 "t".{front} 𝘄𝗶𝘁𝗵
    | ClistClosed ->
        true
    | ClistCons ⎽ ⎽ ->
        false
    | ClistOpen ->
        𝗺𝗮𝘁𝗰𝗵 "t".{back} 𝘄𝗶𝘁𝗵
        | ClistCons ⎽ ⎽ ->
            false
        | ⎽ ->
            true
        𝗲𝗻𝗱
    𝗲𝗻𝗱.

Definition mpsc_queue_3٠push_front : val :=
  𝗳𝘂𝗻 "t" "v" ->
    𝗺𝗮𝘁𝗰𝗵 "t".{front} 𝘄𝗶𝘁𝗵
    | ClistClosed ->
        true
    | ⎽ 𝗮𝘀 "front" ->
        "t" <-{front} ‘ClistCons[ "v", "front" ] ⍮
        false
    𝗲𝗻𝗱.

Definition mpsc_queue_3٠push_back : val :=
  𝗿𝗲𝗰 "push_back" "t" "v" ->
    𝗺𝗮𝘁𝗰𝗵 "t".{back} 𝘄𝗶𝘁𝗵
    | ClistClosed ->
        true
    | ⎽ 𝗮𝘀 "back" ->
        𝗶𝗳
          𝗰𝗮𝘀 "t".[back] "back" ‘ClistCons[ "v", "back" ]
        𝘁𝗵𝗲𝗻 (
          false
        ) 𝗲𝗹𝘀𝗲 (
          domain٠yield () ⍮
          "push_back" "t" "v"
        )
    𝗲𝗻𝗱.

Definition mpsc_queue_3٠pop : val :=
  𝗳𝘂𝗻 "t" ->
    𝗺𝗮𝘁𝗰𝗵 "t".{front} 𝘄𝗶𝘁𝗵
    | ClistClosed ->
        §None
    | ClistCons "v" "front" ->
        "t" <-{front} "front" ⍮
        ‘Some( "v" )
    | ClistOpen ->
        𝗺𝗮𝘁𝗰𝗵
          𝘅𝗰𝗵𝗴 "t".[back] §ClistOpen
        𝘄𝗶𝘁𝗵
        | ClistOpen ->
            §None
        | ⎽ 𝗮𝘀 "back" ->
            𝗺𝗮𝘁𝗰𝗵
              clist٠rev_app "back" §ClistOpen
            𝘄𝗶𝘁𝗵
            | ClistCons "v" "front" ->
                "t" <-{front} "front" ⍮
                ‘Some( "v" )
            | ⎽ ->
                𝗳𝗮𝗶𝗹
            𝗲𝗻𝗱
        𝗲𝗻𝗱
    𝗲𝗻𝗱.

Definition mpsc_queue_3٠close : val :=
  𝗳𝘂𝗻 "t" ->
    𝗺𝗮𝘁𝗰𝗵
      𝘅𝗰𝗵𝗴 "t".[back] §ClistClosed
    𝘄𝗶𝘁𝗵
    | ClistClosed ->
        true
    | ⎽ 𝗮𝘀 "back" ->
        "t" <-{front}
          clist٠app "t".{front} (clist٠rev_app "back" §ClistClosed) ⍮
        false
    𝗲𝗻𝗱.
