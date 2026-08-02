Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.clist.
Require Import zoo_std.domain.
Require Import zoo.options.

Notation "'mpsc_queue_3٠front'" := (
  in_type "zoo_saturn.mpsc_queue_3.t" 0
)(in custom zoo_field
).
Notation "'mpsc_queue_3٠back'" := (
  in_type "zoo_saturn.mpsc_queue_3.t" 1
)(in custom zoo_field
).

Definition mpsc_queue_3٠create : val :=
  𝗳𝘂𝗻 ⎽ ->
    { §clist٠Open, §clist٠Open }.

Definition mpsc_queue_3٠is_empty : val :=
  𝗳𝘂𝗻 "t" ->
    𝗺𝗮𝘁𝗰𝗵 "t".{mpsc_queue_3٠front} 𝘄𝗶𝘁𝗵
    | clist٠Closed ->
        true
    | clist٠Cons ⎽ ⎽ ->
        false
    | clist٠Open ->
        𝗺𝗮𝘁𝗰𝗵 "t".{mpsc_queue_3٠back} 𝘄𝗶𝘁𝗵
        | clist٠Cons ⎽ ⎽ ->
            false
        | ⎽ ->
            true
        𝗲𝗻𝗱
    𝗲𝗻𝗱.

Definition mpsc_queue_3٠push_front : val :=
  𝗳𝘂𝗻 "t" "v" ->
    𝗺𝗮𝘁𝗰𝗵 "t".{mpsc_queue_3٠front} 𝘄𝗶𝘁𝗵
    | clist٠Closed ->
        true
    | ⎽ 𝗮𝘀 "front" ->
        "t" <-{mpsc_queue_3٠front} ‘clist٠Cons[ "v", "front" ] ⍮
        false
    𝗲𝗻𝗱.

Definition mpsc_queue_3٠push_back : val :=
  𝗿𝗲𝗰 "push_back" "t" "v" ->
    𝗺𝗮𝘁𝗰𝗵 "t".{mpsc_queue_3٠back} 𝘄𝗶𝘁𝗵
    | clist٠Closed ->
        true
    | ⎽ 𝗮𝘀 "back" ->
        𝗶𝗳
          𝗰𝗮𝘀
            "t".[mpsc_queue_3٠back]
            "back"
            ‘clist٠Cons[ "v", "back" ]
        𝘁𝗵𝗲𝗻 (
          false
        ) 𝗲𝗹𝘀𝗲 (
          domain٠yield () ⍮
          "push_back" "t" "v"
        )
    𝗲𝗻𝗱.

Definition mpsc_queue_3٠pop : val :=
  𝗳𝘂𝗻 "t" ->
    𝗺𝗮𝘁𝗰𝗵 "t".{mpsc_queue_3٠front} 𝘄𝗶𝘁𝗵
    | clist٠Closed ->
        §None
    | clist٠Cons "v" "front" ->
        "t" <-{mpsc_queue_3٠front} "front" ⍮
        ‘Some( "v" )
    | clist٠Open ->
        𝗺𝗮𝘁𝗰𝗵
          𝘅𝗰𝗵𝗴 "t".[mpsc_queue_3٠back] §clist٠Open
        𝘄𝗶𝘁𝗵
        | clist٠Open ->
            §None
        | ⎽ 𝗮𝘀 "back" ->
            𝗺𝗮𝘁𝗰𝗵
              clist٠rev_app "back" §clist٠Open
            𝘄𝗶𝘁𝗵
            | clist٠Cons "v" "front" ->
                "t" <-{mpsc_queue_3٠front} "front" ⍮
                ‘Some( "v" )
            | ⎽ ->
                𝗳𝗮𝗶𝗹
            𝗲𝗻𝗱
        𝗲𝗻𝗱
    𝗲𝗻𝗱.

Definition mpsc_queue_3٠close : val :=
  𝗳𝘂𝗻 "t" ->
    𝗺𝗮𝘁𝗰𝗵
      𝘅𝗰𝗵𝗴 "t".[mpsc_queue_3٠back] §clist٠Closed
    𝘄𝗶𝘁𝗵
    | clist٠Closed ->
        true
    | ⎽ 𝗮𝘀 "back" ->
        "t" <-{mpsc_queue_3٠front}
          clist٠app
            "t".{mpsc_queue_3٠front}
            (clist٠rev_app "back" §clist٠Closed) ⍮
        false
    𝗲𝗻𝗱.
