Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import backoff.backoff.
Require Import zoo.options.

Notation "'queue_mpmc_1٠Null'" := (
  in_type "zoo_saturn.queue_mpmc_1.node" 0
)(in custom zoo_tag
).
Notation "'queue_mpmc_1٠Node'" := (
  in_type "zoo_saturn.queue_mpmc_1.node" 1
)(in custom zoo_tag
).

Notation "'queue_mpmc_1٠next'" := (
  in_type "zoo_saturn.queue_mpmc_1.node.Node" 0
)(in custom zoo_field
).
Notation "'queue_mpmc_1٠data'" := (
  in_type "zoo_saturn.queue_mpmc_1.node.Node" 1
)(in custom zoo_field
).

Notation "'queue_mpmc_1٠front'" := (
  in_type "zoo_saturn.queue_mpmc_1.t" 0
)(in custom zoo_field
).
Notation "'queue_mpmc_1٠back'" := (
  in_type "zoo_saturn.queue_mpmc_1.t" 1
)(in custom zoo_field
).

Definition queue_mpmc_1٠create : val :=
  𝗳𝘂𝗻 ⎽ ->
    𝗹𝗲𝘁 "front" =
      ‘queue_mpmc_1٠Node{ §queue_mpmc_1٠Null, () }
    𝗶𝗻
    { "front", "front" }.

Definition queue_mpmc_1٠is_empty : val :=
  𝗳𝘂𝗻 "t" ->
    𝗺𝗮𝘁𝗰𝗵 "t".{queue_mpmc_1٠front} 𝘄𝗶𝘁𝗵
    | queue_mpmc_1٠Node ⎽ ⎽ 𝗮𝘀 "front_r" ->
        "front_r".{queue_mpmc_1٠next} == §queue_mpmc_1٠Null
    𝗲𝗻𝗱.

Definition queue_mpmc_1٠push₂ : val :=
  𝗿𝗲𝗰 "push" "node" "new_back" "backoff" ->
    𝗺𝗮𝘁𝗰𝗵 "node" 𝘄𝗶𝘁𝗵
    | queue_mpmc_1٠Node ⎽ ⎽ 𝗮𝘀 "node_r" ->
        𝗺𝗮𝘁𝗰𝗵 "node_r".{queue_mpmc_1٠next} 𝘄𝗶𝘁𝗵
        | queue_mpmc_1٠Node ⎽ ⎽ 𝗮𝘀 "next" ->
            "push" "next" "new_back" "backoff"
        | queue_mpmc_1٠Null ->
            𝗶𝗳
              ~
              𝗰𝗮𝘀
                "node_r".[queue_mpmc_1٠next]
                §queue_mpmc_1٠Null
                "new_back"
            𝘁𝗵𝗲𝗻 (
              "push" "node" "new_back" (backoff٠once "backoff")
            )
        𝗲𝗻𝗱
    𝗲𝗻𝗱.

Definition queue_mpmc_1٠push₁ : val :=
  𝗳𝘂𝗻 "node" "new_back" ->
    queue_mpmc_1٠push₂ "node" "new_back" backoff٠default.

Definition queue_mpmc_1٠fix_back₁ : val :=
  𝗿𝗲𝗰 "fix_back" "t" "back" "new_back" "backoff" ->
    𝗺𝗮𝘁𝗰𝗵 "new_back" 𝘄𝗶𝘁𝗵
    | queue_mpmc_1٠Node ⎽ ⎽ 𝗮𝘀 "new_back_r" ->
        𝗶𝗳
          "new_back_r".{queue_mpmc_1٠next} == §queue_mpmc_1٠Null
          𝗮𝗻𝗱
          ~ 𝗰𝗮𝘀 "t".[queue_mpmc_1٠back] "back" "new_back"
        𝘁𝗵𝗲𝗻 (
          "fix_back"
            "t"
            "t".{queue_mpmc_1٠back}
            "new_back"
            (backoff٠once "backoff")
        )
    𝗲𝗻𝗱.

Definition queue_mpmc_1٠fix_back : val :=
  𝗳𝘂𝗻 "t" "back" "new_back" ->
    queue_mpmc_1٠fix_back₁ "t" "back" "new_back" backoff٠default.

Definition queue_mpmc_1٠push : val :=
  𝗳𝘂𝗻 "t" "v" ->
    𝗺𝗮𝘁𝗰𝗵
      ‘queue_mpmc_1٠Node{ §queue_mpmc_1٠Null, "v" }
    𝘄𝗶𝘁𝗵
    | queue_mpmc_1٠Node ⎽ ⎽ 𝗮𝘀 "new_back" ->
        𝗹𝗲𝘁 "back" = "t".{queue_mpmc_1٠back} 𝗶𝗻
        queue_mpmc_1٠push₁ "back" "new_back" ⍮
        queue_mpmc_1٠fix_back "t" "back" "new_back"
    𝗲𝗻𝗱.

Definition queue_mpmc_1٠pop₁ : val :=
  𝗿𝗲𝗰 "pop" "t" "backoff" ->
    𝗺𝗮𝘁𝗰𝗵 "t".{queue_mpmc_1٠front} 𝘄𝗶𝘁𝗵
    | queue_mpmc_1٠Node ⎽ ⎽ 𝗮𝘀 "front" ->
        𝗹𝗲𝘁 "front_r" = "front" 𝗶𝗻
        𝗺𝗮𝘁𝗰𝗵 "front_r".{queue_mpmc_1٠next} 𝘄𝗶𝘁𝗵
        | queue_mpmc_1٠Null ->
            §None
        | queue_mpmc_1٠Node ⎽ ⎽ 𝗮𝘀 "new_front" ->
            𝗹𝗲𝘁 "new_front_r" = "new_front" 𝗶𝗻
            𝗶𝗳
              𝗰𝗮𝘀 "t".[queue_mpmc_1٠front] "front" "new_front"
            𝘁𝗵𝗲𝗻 (
              𝗹𝗲𝘁 "v" = "new_front_r".{queue_mpmc_1٠data} 𝗶𝗻
              "new_front_r" <-{queue_mpmc_1٠data} () ⍮
              ‘Some( "v" )
            ) 𝗲𝗹𝘀𝗲 (
              "pop" "t" (backoff٠once "backoff")
            )
        𝗲𝗻𝗱
    𝗲𝗻𝗱.

Definition queue_mpmc_1٠pop : val :=
  𝗳𝘂𝗻 "t" ->
    queue_mpmc_1٠pop₁ "t" backoff٠default.
