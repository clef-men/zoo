Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.domain.
Require Import zoo_saturn.mpsc_queue_1__types.
Require Import zoo.options.

Definition mpsc_queue_1٠create : val :=
  𝗳𝘂𝗻 ⎽ ->
    𝗹𝗲𝘁 "front" = ‘Node{ §Null, () } 𝗶𝗻
    { "front", "front" }.

Definition mpsc_queue_1٠is_empty : val :=
  𝗳𝘂𝗻 "t" ->
    𝗺𝗮𝘁𝗰𝗵 "t".{front} 𝘄𝗶𝘁𝗵
    | Node ⎽ ⎽ 𝗮𝘀 "front_r" ->
        "front_r".{next} == §Null
    𝗲𝗻𝗱.

Definition mpsc_queue_1٠push₁ : val :=
  𝗿𝗲𝗰 "push" "node" "new_back" ->
    𝗺𝗮𝘁𝗰𝗵 "node" 𝘄𝗶𝘁𝗵
    | Node ⎽ ⎽ 𝗮𝘀 "node_r" ->
        𝗺𝗮𝘁𝗰𝗵 "node_r".{next} 𝘄𝗶𝘁𝗵
        | Node ⎽ ⎽ 𝗮𝘀 "next" ->
            "push" "next" "new_back"
        | Null ->
            𝗶𝗳
              ~ 𝗰𝗮𝘀 "node_r".[next] §Null "new_back"
            𝘁𝗵𝗲𝗻 (
              domain٠yield () ⍮
              "push" "node" "new_back"
            )
        𝗲𝗻𝗱
    𝗲𝗻𝗱.

Definition mpsc_queue_1٠fix_back : val :=
  𝗿𝗲𝗰 "fix_back" "t" "back" "new_back" ->
    𝗺𝗮𝘁𝗰𝗵 "new_back" 𝘄𝗶𝘁𝗵
    | Node ⎽ ⎽ 𝗮𝘀 "new_back_r" ->
        𝗶𝗳
          "new_back_r".{next} == §Null
          𝗮𝗻𝗱
          ~ 𝗰𝗮𝘀 "t".[back] "back" "new_back"
        𝘁𝗵𝗲𝗻 (
          domain٠yield () ⍮
          "fix_back" "t" "t".{back} "new_back"
        )
    𝗲𝗻𝗱.

Definition mpsc_queue_1٠push : val :=
  𝗳𝘂𝗻 "t" "v" ->
    𝗺𝗮𝘁𝗰𝗵 ‘Node{ §Null, "v" } 𝘄𝗶𝘁𝗵
    | Node ⎽ ⎽ 𝗮𝘀 "new_back" ->
        𝗹𝗲𝘁 "back" = "t".{back} 𝗶𝗻
        mpsc_queue_1٠push₁ "back" "new_back" ⍮
        mpsc_queue_1٠fix_back "t" "back" "new_back"
    𝗲𝗻𝗱.

Definition mpsc_queue_1٠pop : val :=
  𝗳𝘂𝗻 "t" ->
    𝗺𝗮𝘁𝗰𝗵 "t".{front} 𝘄𝗶𝘁𝗵
    | Node ⎽ ⎽ 𝗮𝘀 "front_r" ->
        𝗺𝗮𝘁𝗰𝗵 "front_r".{next} 𝘄𝗶𝘁𝗵
        | Null ->
            §None
        | Node ⎽ ⎽ 𝗮𝘀 "new_front" ->
            𝗹𝗲𝘁 "new_front_r" = "new_front" 𝗶𝗻
            "t" <-{front} "new_front" ⍮
            𝗹𝗲𝘁 "v" = "new_front_r".{data} 𝗶𝗻
            "new_front_r" <-{data} () ⍮
            ‘Some( "v" )
        𝗲𝗻𝗱
    𝗲𝗻𝗱.
