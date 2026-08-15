Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import backoff.backoff.
Require Import zoo.options.

Notation "'bqueue_mpmc٠Null'" := (
  in_type "zoo_saturn.bqueue_mpmc.node" 0
)(in custom zoo_tag
).
Notation "'bqueue_mpmc٠Node'" := (
  in_type "zoo_saturn.bqueue_mpmc.node" 1
)(in custom zoo_tag
).

Notation "'bqueue_mpmc٠next'" := (
  in_type "zoo_saturn.bqueue_mpmc.node.Node" 0
)(in custom zoo_field
).
Notation "'bqueue_mpmc٠data'" := (
  in_type "zoo_saturn.bqueue_mpmc.node.Node" 1
)(in custom zoo_field
).
Notation "'bqueue_mpmc٠index'" := (
  in_type "zoo_saturn.bqueue_mpmc.node.Node" 2
)(in custom zoo_field
).
Notation "'bqueue_mpmc٠estimated_capacity'" := (
  in_type "zoo_saturn.bqueue_mpmc.node.Node" 3
)(in custom zoo_field
).

Notation "'bqueue_mpmc٠capacity'" := (
  in_type "zoo_saturn.bqueue_mpmc.t" 0
)(in custom zoo_field
).
Notation "'bqueue_mpmc٠front'" := (
  in_type "zoo_saturn.bqueue_mpmc.t" 1
)(in custom zoo_field
).
Notation "'bqueue_mpmc٠back'" := (
  in_type "zoo_saturn.bqueue_mpmc.t" 2
)(in custom zoo_field
).

Definition bqueue_mpmc٠create : val :=
  𝗳𝘂𝗻 "cap" ->
    𝗹𝗲𝘁 "front" =
      ‘bqueue_mpmc٠Node{ §bqueue_mpmc٠Null, (), 0, "cap" }
    𝗶𝗻
    { "cap", "front", "front" }.

Definition bqueue_mpmc٠capacity : val :=
  𝗳𝘂𝗻 "t" ->
    "t".{bqueue_mpmc٠capacity}.

Definition bqueue_mpmc٠size : val :=
  𝗿𝗲𝗰 "size" "t" ->
    𝗺𝗮𝘁𝗰𝗵 "t".{bqueue_mpmc٠front} 𝘄𝗶𝘁𝗵
    | bqueue_mpmc٠Node ⎽ ⎽ ⎽ ⎽ 𝗮𝘀 "front" ->
        𝗹𝗲𝘁 "front_r" = "front" 𝗶𝗻
        𝗹𝗲𝘁 "proph" = 𝗽𝗿𝗼𝗽𝗵 𝗶𝗻
        𝗺𝗮𝘁𝗰𝗵 "t".{bqueue_mpmc٠back} 𝘄𝗶𝘁𝗵
        | bqueue_mpmc٠Node ⎽ ⎽ ⎽ ⎽ 𝗮𝘀 "back" ->
            𝗹𝗲𝘁 "back_r" = "back" 𝗶𝗻
            𝗺𝗮𝘁𝗰𝗵
              "back_r".{bqueue_mpmc٠next}
            𝘄𝗶𝘁𝗵
            | bqueue_mpmc٠Node ⎽ ⎽ ⎽ ⎽ 𝗮𝘀 "node" ->
                𝗰𝗮𝘀 "t".[bqueue_mpmc٠back] "back" "node" ⍮
                "size" "t"
            | bqueue_mpmc٠Null ->
                𝗶𝗳
                  𝗿𝗲𝘀𝗼𝗹𝘃𝗲
                    "t".{bqueue_mpmc٠front}
                    "proph"
                    ()
                  ==
                  "front"
                𝘁𝗵𝗲𝗻 (
                  "back_r".{bqueue_mpmc٠index}
                  -
                  "front_r".{bqueue_mpmc٠index}
                ) 𝗲𝗹𝘀𝗲 (
                  "size" "t"
                )
            𝗲𝗻𝗱
        𝗲𝗻𝗱
    𝗲𝗻𝗱.

Definition bqueue_mpmc٠is_empty : val :=
  𝗳𝘂𝗻 "t" ->
    𝗺𝗮𝘁𝗰𝗵 "t".{bqueue_mpmc٠front} 𝘄𝗶𝘁𝗵
    | bqueue_mpmc٠Node ⎽ ⎽ ⎽ ⎽ 𝗮𝘀 "front_r" ->
        "front_r".{bqueue_mpmc٠next} == §bqueue_mpmc٠Null
    𝗲𝗻𝗱.

Definition bqueue_mpmc٠fix_back₁ : val :=
  𝗿𝗲𝗰 "fix_back" "t" "back" "new_back" "backoff" ->
    𝗺𝗮𝘁𝗰𝗵 "new_back" 𝘄𝗶𝘁𝗵
    | bqueue_mpmc٠Node ⎽ ⎽ ⎽ ⎽ 𝗮𝘀 "new_back_r" ->
        𝗶𝗳
          "new_back_r".{bqueue_mpmc٠next} == §bqueue_mpmc٠Null
          𝗮𝗻𝗱
          ~ 𝗰𝗮𝘀 "t".[bqueue_mpmc٠back] "back" "new_back"
        𝘁𝗵𝗲𝗻 (
          "fix_back"
            "t"
            "t".{bqueue_mpmc٠back}
            "new_back"
            (backoff٠once "backoff")
        )
    𝗲𝗻𝗱.

Definition bqueue_mpmc٠fix_back : val :=
  𝗳𝘂𝗻 "t" "back" "new_back" ->
    bqueue_mpmc٠fix_back₁ "t" "back" "new_back" backoff٠default.

#[local] Definition __zoo_recs_0 :=
  ( 𝗿𝗲𝗰𝘀 "push_1" "t" "back" "cap" "new_back" ->
      𝗺𝗮𝘁𝗰𝗵 "back" 𝘄𝗶𝘁𝗵
      | bqueue_mpmc٠Node ⎽ ⎽ ⎽ ⎽ 𝗮𝘀 "back_r" ->
          𝗺𝗮𝘁𝗰𝗵 "new_back" 𝘄𝗶𝘁𝗵
          | bqueue_mpmc٠Node ⎽ ⎽ ⎽ ⎽ 𝗮𝘀 "new_back" ->
              𝗹𝗲𝘁 "new_back_r" = "new_back" 𝗶𝗻
              𝗶𝗳 "cap" == 0 𝘁𝗵𝗲𝗻 (
                𝗺𝗮𝘁𝗰𝗵
                  "t".{bqueue_mpmc٠front}
                𝘄𝗶𝘁𝗵
                | bqueue_mpmc٠Node ⎽ ⎽ ⎽ ⎽ 𝗮𝘀 "front_r" ->
                    𝗹𝗲𝘁 "cap" =
                      "t".{bqueue_mpmc٠capacity}
                      -
                      ("back_r".{bqueue_mpmc٠index}
                       -
                       "front_r".{bqueue_mpmc٠index})
                    𝗶𝗻
                    𝗶𝗳 "cap" == 0 𝘁𝗵𝗲𝗻 (
                      false
                    ) 𝗲𝗹𝘀𝗲 (
                      "back_r" <-{bqueue_mpmc٠estimated_capacity} "cap" ⍮
                      "push_1" "t" "back" "cap" "new_back"
                    )
                𝗲𝗻𝗱
              ) 𝗲𝗹𝘀𝗲 (
                "new_back_r" <-{bqueue_mpmc٠index}
                  "back_r".{bqueue_mpmc٠index} + 1 ⍮
                "new_back_r" <-{bqueue_mpmc٠estimated_capacity} "cap" - 1 ⍮
                𝗶𝗳
                  𝗰𝗮𝘀
                    "back_r".[bqueue_mpmc٠next]
                    §bqueue_mpmc٠Null
                    "new_back"
                𝘁𝗵𝗲𝗻 (
                  bqueue_mpmc٠fix_back "t" "back" "new_back" ⍮
                  true
                ) 𝗲𝗹𝘀𝗲 (
                  𝗺𝗮𝘁𝗰𝗵
                    "back_r".{bqueue_mpmc٠next}
                  𝘄𝗶𝘁𝗵
                  | bqueue_mpmc٠Null ->
                      𝗳𝗮𝗶𝗹
                  | bqueue_mpmc٠Node ⎽ ⎽ ⎽ ⎽ 𝗮𝘀 "back" ->
                      "push_2" "t" "back" "new_back"
                  𝗲𝗻𝗱
                )
              )
          𝗲𝗻𝗱
      𝗲𝗻𝗱
    𝘄𝗶𝘁𝗵 "push_2" "t" "back" "new_back" ->
      𝗺𝗮𝘁𝗰𝗵 "back" 𝘄𝗶𝘁𝗵
      | bqueue_mpmc٠Node ⎽ ⎽ ⎽ ⎽ 𝗮𝘀 "back" ->
          𝗹𝗲𝘁 "back_r" = "back" 𝗶𝗻
          "push_1"
            "t"
            "back"
            "back_r".{bqueue_mpmc٠estimated_capacity}
            "new_back"
      𝗲𝗻𝗱
  )%zoo_recs.
Definition bqueue_mpmc٠push_1 :=
  ValRecs 0 __zoo_recs_0.
Definition bqueue_mpmc٠push_2 :=
  ValRecs 1 __zoo_recs_0.
#[global] Instance :
  AsValRecs' bqueue_mpmc٠push_1 0 __zoo_recs_0 [
    bqueue_mpmc٠push_1 ;
    bqueue_mpmc٠push_2
  ].
Proof.
  done.
Qed.
#[global] Instance :
  AsValRecs' bqueue_mpmc٠push_2 1 __zoo_recs_0 [
    bqueue_mpmc٠push_1 ;
    bqueue_mpmc٠push_2
  ].
Proof.
  done.
Qed.

Definition bqueue_mpmc٠push : val :=
  𝗳𝘂𝗻 "t" "v" ->
    𝗹𝗲𝘁 "new_back" =
      ‘bqueue_mpmc٠Node{ §bqueue_mpmc٠Null, "v", 0, 0 }
    𝗶𝗻
    bqueue_mpmc٠push_2 "t" "t".{bqueue_mpmc٠back} "new_back".

Definition bqueue_mpmc٠pop₁ : val :=
  𝗿𝗲𝗰 "pop" "t" "backoff" ->
    𝗺𝗮𝘁𝗰𝗵 "t".{bqueue_mpmc٠front} 𝘄𝗶𝘁𝗵
    | bqueue_mpmc٠Node ⎽ ⎽ ⎽ ⎽ 𝗮𝘀 "front" ->
        𝗹𝗲𝘁 "front_r" = "front" 𝗶𝗻
        𝗺𝗮𝘁𝗰𝗵 "front_r".{bqueue_mpmc٠next} 𝘄𝗶𝘁𝗵
        | bqueue_mpmc٠Null ->
            §None
        | bqueue_mpmc٠Node ⎽ ⎽ ⎽ ⎽ 𝗮𝘀 "new_front" ->
            𝗹𝗲𝘁 "new_front_r" = "new_front" 𝗶𝗻
            𝗶𝗳
              𝗰𝗮𝘀 "t".[bqueue_mpmc٠front] "front" "new_front"
            𝘁𝗵𝗲𝗻 (
              𝗹𝗲𝘁 "v" = "new_front_r".{bqueue_mpmc٠data} 𝗶𝗻
              "new_front_r" <-{bqueue_mpmc٠data} () ⍮
              ‘Some( "v" )
            ) 𝗲𝗹𝘀𝗲 (
              "pop" "t" (backoff٠once "backoff")
            )
        𝗲𝗻𝗱
    𝗲𝗻𝗱.

Definition bqueue_mpmc٠pop : val :=
  𝗳𝘂𝗻 "t" ->
    bqueue_mpmc٠pop₁ "t" backoff٠default.
