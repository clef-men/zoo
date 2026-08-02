Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.domain.
Require Import zoo_std.glist.
Require Import zoo.options.

Notation "'mpsc_queue_2٠front'" := (
  in_type "zoo_saturn.mpsc_queue_2.t" 0
)(in custom zoo_field
).
Notation "'mpsc_queue_2٠back'" := (
  in_type "zoo_saturn.mpsc_queue_2.t" 1
)(in custom zoo_field
).

Definition mpsc_queue_2٠create : val :=
  𝗳𝘂𝗻 ⎽ ->
    { §glist٠Nil, §glist٠Nil }.

Definition mpsc_queue_2٠is_empty : val :=
  𝗳𝘂𝗻 "t" ->
    𝗺𝗮𝘁𝗰𝗵 "t".{mpsc_queue_2٠front} 𝘄𝗶𝘁𝗵
    | glist٠Cons ⎽ ⎽ ->
        false
    | glist٠Nil ->
        "t".{mpsc_queue_2٠back} == §glist٠Nil
    𝗲𝗻𝗱.

Definition mpsc_queue_2٠push_front : val :=
  𝗳𝘂𝗻 "t" "v" ->
    "t" <-{mpsc_queue_2٠front}
      ‘glist٠Cons[ "v", "t".{mpsc_queue_2٠front} ].

Definition mpsc_queue_2٠push_back : val :=
  𝗿𝗲𝗰 "push_back" "t" "v" ->
    𝗹𝗲𝘁 "back" = "t".{mpsc_queue_2٠back} 𝗶𝗻
    𝗶𝗳
      ~
      𝗰𝗮𝘀
        "t".[mpsc_queue_2٠back]
        "back"
        ‘glist٠Cons[ "v", "back" ]
    𝘁𝗵𝗲𝗻 (
      domain٠yield () ⍮
      "push_back" "t" "v"
    ).

Definition mpsc_queue_2٠pop : val :=
  𝗳𝘂𝗻 "t" ->
    𝗺𝗮𝘁𝗰𝗵 "t".{mpsc_queue_2٠front} 𝘄𝗶𝘁𝗵
    | glist٠Nil ->
        𝗺𝗮𝘁𝗰𝗵
          glist٠rev (𝘅𝗰𝗵𝗴 "t".[mpsc_queue_2٠back] §glist٠Nil)
        𝘄𝗶𝘁𝗵
        | glist٠Nil ->
            §None
        | glist٠Cons "v" "front" ->
            "t" <-{mpsc_queue_2٠front} "front" ⍮
            ‘Some( "v" )
        𝗲𝗻𝗱
    | glist٠Cons "v" "front" ->
        "t" <-{mpsc_queue_2٠front} "front" ⍮
        ‘Some( "v" )
    𝗲𝗻𝗱.
