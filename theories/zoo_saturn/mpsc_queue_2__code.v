Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.glist.
Require Import zoo_std.domain.
Require Import zoo_saturn.mpsc_queue_2__types.
Require Import zoo.options.

Definition mpsc_queue_2٠create : val :=
  𝗳𝘂𝗻 ⎽ ->
    { §Gnil, §Gnil }.

Definition mpsc_queue_2٠is_empty : val :=
  𝗳𝘂𝗻 "t" ->
    𝗺𝗮𝘁𝗰𝗵 "t".{front} 𝘄𝗶𝘁𝗵
    | Gcons ⎽ ⎽ ->
        false
    | Gnil ->
        "t".{back} == §Gnil
    𝗲𝗻𝗱.

Definition mpsc_queue_2٠push_front : val :=
  𝗳𝘂𝗻 "t" "v" ->
    "t" <-{front} ‘Gcons[ "v", "t".{front} ].

Definition mpsc_queue_2٠push_back : val :=
  𝗿𝗲𝗰 "push_back" "t" "v" ->
    𝗹𝗲𝘁 "back" = "t".{back} 𝗶𝗻
    𝗶𝗳
      ~ 𝗰𝗮𝘀 "t".[back] "back" ‘Gcons[ "v", "back" ]
    𝘁𝗵𝗲𝗻 (
      domain٠yield () ⍮
      "push_back" "t" "v"
    ).

Definition mpsc_queue_2٠pop : val :=
  𝗳𝘂𝗻 "t" ->
    𝗺𝗮𝘁𝗰𝗵 "t".{front} 𝘄𝗶𝘁𝗵
    | Gnil ->
        𝗺𝗮𝘁𝗰𝗵
          glist٠rev (𝘅𝗰𝗵𝗴 "t".[back] §Gnil)
        𝘄𝗶𝘁𝗵
        | Gnil ->
            §None
        | Gcons "v" "front" ->
            "t" <-{front} "front" ⍮
            ‘Some( "v" )
        𝗲𝗻𝗱
    | Gcons "v" "front" ->
        "t" <-{front} "front" ⍮
        ‘Some( "v" )
    𝗲𝗻𝗱.
