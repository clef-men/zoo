Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.domain.
Require Import zoo.options.

Notation "'mpsc_queue_1٠Null'" := (
  in_type "zoo_saturn.mpsc_queue_1.node" 0
)(in custom zoo_tag
).
Notation "'mpsc_queue_1٠Node'" := (
  in_type "zoo_saturn.mpsc_queue_1.node" 1
)(in custom zoo_tag
).

Notation "'mpsc_queue_1٠next'" := (
  in_type "zoo_saturn.mpsc_queue_1.node.Node" 0
)(in custom zoo_field
).
Notation "'mpsc_queue_1٠data'" := (
  in_type "zoo_saturn.mpsc_queue_1.node.Node" 1
)(in custom zoo_field
).

Notation "'mpsc_queue_1٠front'" := (
  in_type "zoo_saturn.mpsc_queue_1.t" 0
)(in custom zoo_field
).
Notation "'mpsc_queue_1٠back'" := (
  in_type "zoo_saturn.mpsc_queue_1.t" 1
)(in custom zoo_field
).

Definition mpsc_queue_1٠create : val :=
  𝗳𝘂𝗻 ⎽ ->
    𝗹𝗲𝘁 "front" =
      ‘mpsc_queue_1٠Node{ §mpsc_queue_1٠Null, () }
    𝗶𝗻
    { "front", "front" }.

Definition mpsc_queue_1٠is_empty : val :=
  𝗳𝘂𝗻 "t" ->
    𝗺𝗮𝘁𝗰𝗵 "t".{mpsc_queue_1٠front} 𝘄𝗶𝘁𝗵
    | mpsc_queue_1٠Node ⎽ ⎽ 𝗮𝘀 "front_r" ->
        "front_r".{mpsc_queue_1٠next} == §mpsc_queue_1٠Null
    𝗲𝗻𝗱.

Definition mpsc_queue_1٠push₁ : val :=
  𝗿𝗲𝗰 "push" "node" "new_back" ->
    𝗺𝗮𝘁𝗰𝗵 "node" 𝘄𝗶𝘁𝗵
    | mpsc_queue_1٠Node ⎽ ⎽ 𝗮𝘀 "node_r" ->
        𝗺𝗮𝘁𝗰𝗵 "node_r".{mpsc_queue_1٠next} 𝘄𝗶𝘁𝗵
        | mpsc_queue_1٠Node ⎽ ⎽ 𝗮𝘀 "next" ->
            "push" "next" "new_back"
        | mpsc_queue_1٠Null ->
            𝗶𝗳
              ~
              𝗰𝗮𝘀
                "node_r".[mpsc_queue_1٠next]
                §mpsc_queue_1٠Null
                "new_back"
            𝘁𝗵𝗲𝗻 (
              domain٠yield () ⍮
              "push" "node" "new_back"
            )
        𝗲𝗻𝗱
    𝗲𝗻𝗱.

Definition mpsc_queue_1٠fix_back : val :=
  𝗿𝗲𝗰 "fix_back" "t" "back" "new_back" ->
    𝗺𝗮𝘁𝗰𝗵 "new_back" 𝘄𝗶𝘁𝗵
    | mpsc_queue_1٠Node ⎽ ⎽ 𝗮𝘀 "new_back_r" ->
        𝗶𝗳
          "new_back_r".{mpsc_queue_1٠next} == §mpsc_queue_1٠Null
          𝗮𝗻𝗱
          ~ 𝗰𝗮𝘀 "t".[mpsc_queue_1٠back] "back" "new_back"
        𝘁𝗵𝗲𝗻 (
          domain٠yield () ⍮
          "fix_back" "t" "t".{mpsc_queue_1٠back} "new_back"
        )
    𝗲𝗻𝗱.

Definition mpsc_queue_1٠push : val :=
  𝗳𝘂𝗻 "t" "v" ->
    𝗺𝗮𝘁𝗰𝗵
      ‘mpsc_queue_1٠Node{ §mpsc_queue_1٠Null, "v" }
    𝘄𝗶𝘁𝗵
    | mpsc_queue_1٠Node ⎽ ⎽ 𝗮𝘀 "new_back" ->
        𝗹𝗲𝘁 "back" = "t".{mpsc_queue_1٠back} 𝗶𝗻
        mpsc_queue_1٠push₁ "back" "new_back" ⍮
        mpsc_queue_1٠fix_back "t" "back" "new_back"
    𝗲𝗻𝗱.

Definition mpsc_queue_1٠pop : val :=
  𝗳𝘂𝗻 "t" ->
    𝗺𝗮𝘁𝗰𝗵 "t".{mpsc_queue_1٠front} 𝘄𝗶𝘁𝗵
    | mpsc_queue_1٠Node ⎽ ⎽ 𝗮𝘀 "front_r" ->
        𝗺𝗮𝘁𝗰𝗵 "front_r".{mpsc_queue_1٠next} 𝘄𝗶𝘁𝗵
        | mpsc_queue_1٠Null ->
            §None
        | mpsc_queue_1٠Node ⎽ ⎽ 𝗮𝘀 "new_front" ->
            𝗹𝗲𝘁 "new_front_r" = "new_front" 𝗶𝗻
            "t" <-{mpsc_queue_1٠front} "new_front" ⍮
            𝗹𝗲𝘁 "v" = "new_front_r".{mpsc_queue_1٠data} 𝗶𝗻
            "new_front_r" <-{mpsc_queue_1٠data} () ⍮
            ‘Some( "v" )
        𝗲𝗻𝗱
    𝗲𝗻𝗱.
