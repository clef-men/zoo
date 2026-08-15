Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import backoff.backoff.
Require Import zoo_std.glist.
Require Import zoo.options.

Notation "'queue_mpsc_2٠front'" := (
  in_type "zoo_saturn.queue_mpsc_2.t" 0
)(in custom zoo_field
).
Notation "'queue_mpsc_2٠back'" := (
  in_type "zoo_saturn.queue_mpsc_2.t" 1
)(in custom zoo_field
).

Definition queue_mpsc_2٠create : val :=
  𝗳𝘂𝗻 ⎽ ->
    { §glist٠Nil, §glist٠Nil }.

Definition queue_mpsc_2٠is_empty : val :=
  𝗳𝘂𝗻 "t" ->
    𝗺𝗮𝘁𝗰𝗵 "t".{queue_mpsc_2٠front} 𝘄𝗶𝘁𝗵
    | glist٠Cons ⎽ ⎽ ->
        false
    | glist٠Nil ->
        "t".{queue_mpsc_2٠back} == §glist٠Nil
    𝗲𝗻𝗱.

Definition queue_mpsc_2٠push_front : val :=
  𝗳𝘂𝗻 "t" "v" ->
    "t" <-{queue_mpsc_2٠front}
      ‘glist٠Cons[ "v", "t".{queue_mpsc_2٠front} ].

Definition queue_mpsc_2٠push_back₁ : val :=
  𝗿𝗲𝗰 "push_back" "t" "v" "backoff" ->
    𝗹𝗲𝘁 "back" = "t".{queue_mpsc_2٠back} 𝗶𝗻
    𝗶𝗳
      ~
      𝗰𝗮𝘀
        "t".[queue_mpsc_2٠back]
        "back"
        ‘glist٠Cons[ "v", "back" ]
    𝘁𝗵𝗲𝗻 (
      "push_back" "t" "v" (backoff٠once "backoff")
    ).

Definition queue_mpsc_2٠push_back : val :=
  𝗳𝘂𝗻 "t" "v" ->
    queue_mpsc_2٠push_back₁ "t" "v" backoff٠default.

Definition queue_mpsc_2٠pop : val :=
  𝗳𝘂𝗻 "t" ->
    𝗺𝗮𝘁𝗰𝗵 "t".{queue_mpsc_2٠front} 𝘄𝗶𝘁𝗵
    | glist٠Nil ->
        𝗺𝗮𝘁𝗰𝗵
          glist٠rev (𝘅𝗰𝗵𝗴 "t".[queue_mpsc_2٠back] §glist٠Nil)
        𝘄𝗶𝘁𝗵
        | glist٠Nil ->
            §None
        | glist٠Cons "v" "front" ->
            "t" <-{queue_mpsc_2٠front} "front" ⍮
            ‘Some( "v" )
        𝗲𝗻𝗱
    | glist٠Cons "v" "front" ->
        "t" <-{queue_mpsc_2٠front} "front" ⍮
        ‘Some( "v" )
    𝗲𝗻𝗱.
