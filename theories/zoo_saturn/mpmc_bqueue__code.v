Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.domain.
Require Import zoo.options.

Notation "'mpmc_bqueue٠Null'" := (
  in_type "zoo_saturn.mpmc_bqueue.node" 0
)(in custom zoo_tag
).
Notation "'mpmc_bqueue٠Node'" := (
  in_type "zoo_saturn.mpmc_bqueue.node" 1
)(in custom zoo_tag
).

Notation "'mpmc_bqueue٠next'" := (
  in_type "zoo_saturn.mpmc_bqueue.node.Node" 0
)(in custom zoo_field
).
Notation "'mpmc_bqueue٠data'" := (
  in_type "zoo_saturn.mpmc_bqueue.node.Node" 1
)(in custom zoo_field
).
Notation "'mpmc_bqueue٠index'" := (
  in_type "zoo_saturn.mpmc_bqueue.node.Node" 2
)(in custom zoo_field
).
Notation "'mpmc_bqueue٠estimated_capacity'" := (
  in_type "zoo_saturn.mpmc_bqueue.node.Node" 3
)(in custom zoo_field
).

Notation "'mpmc_bqueue٠capacity'" := (
  in_type "zoo_saturn.mpmc_bqueue.t" 0
)(in custom zoo_field
).
Notation "'mpmc_bqueue٠front'" := (
  in_type "zoo_saturn.mpmc_bqueue.t" 1
)(in custom zoo_field
).
Notation "'mpmc_bqueue٠back'" := (
  in_type "zoo_saturn.mpmc_bqueue.t" 2
)(in custom zoo_field
).

Definition mpmc_bqueue٠create : val :=
  𝗳𝘂𝗻 "cap" ->
    𝗹𝗲𝘁 "front" =
      ‘mpmc_bqueue٠Node{ §mpmc_bqueue٠Null, (), 0, "cap" }
    𝗶𝗻
    { "cap", "front", "front" }.

Definition mpmc_bqueue٠capacity : val :=
  𝗳𝘂𝗻 "t" ->
    "t".{mpmc_bqueue٠capacity}.

Definition mpmc_bqueue٠size : val :=
  𝗿𝗲𝗰 "size" "t" ->
    𝗺𝗮𝘁𝗰𝗵 "t".{mpmc_bqueue٠front} 𝘄𝗶𝘁𝗵
    | mpmc_bqueue٠Node ⎽ ⎽ ⎽ ⎽ 𝗮𝘀 "front" ->
        𝗹𝗲𝘁 "front_r" = "front" 𝗶𝗻
        𝗹𝗲𝘁 "proph" = 𝗽𝗿𝗼𝗽𝗵 𝗶𝗻
        𝗺𝗮𝘁𝗰𝗵 "t".{mpmc_bqueue٠back} 𝘄𝗶𝘁𝗵
        | mpmc_bqueue٠Node ⎽ ⎽ ⎽ ⎽ 𝗮𝘀 "back" ->
            𝗹𝗲𝘁 "back_r" = "back" 𝗶𝗻
            𝗺𝗮𝘁𝗰𝗵
              "back_r".{mpmc_bqueue٠next}
            𝘄𝗶𝘁𝗵
            | mpmc_bqueue٠Node ⎽ ⎽ ⎽ ⎽ 𝗮𝘀 "node" ->
                𝗰𝗮𝘀 "t".[mpmc_bqueue٠back] "back" "node" ⍮
                "size" "t"
            | mpmc_bqueue٠Null ->
                𝗶𝗳
                  𝗿𝗲𝘀𝗼𝗹𝘃𝗲
                    "t".{mpmc_bqueue٠front}
                    "proph"
                    ()
                  ==
                  "front"
                𝘁𝗵𝗲𝗻 (
                  "back_r".{mpmc_bqueue٠index}
                  -
                  "front_r".{mpmc_bqueue٠index}
                ) 𝗲𝗹𝘀𝗲 (
                  "size" "t"
                )
            𝗲𝗻𝗱
        𝗲𝗻𝗱
    𝗲𝗻𝗱.

Definition mpmc_bqueue٠is_empty : val :=
  𝗳𝘂𝗻 "t" ->
    𝗺𝗮𝘁𝗰𝗵 "t".{mpmc_bqueue٠front} 𝘄𝗶𝘁𝗵
    | mpmc_bqueue٠Node ⎽ ⎽ ⎽ ⎽ 𝗮𝘀 "front_r" ->
        "front_r".{mpmc_bqueue٠next} == §mpmc_bqueue٠Null
    𝗲𝗻𝗱.

Definition mpmc_bqueue٠fix_back : val :=
  𝗿𝗲𝗰 "fix_back" "t" "back" "new_back" ->
    𝗺𝗮𝘁𝗰𝗵 "new_back" 𝘄𝗶𝘁𝗵
    | mpmc_bqueue٠Node ⎽ ⎽ ⎽ ⎽ 𝗮𝘀 "new_back_r" ->
        𝗶𝗳
          "new_back_r".{mpmc_bqueue٠next} == §mpmc_bqueue٠Null
          𝗮𝗻𝗱
          ~ 𝗰𝗮𝘀 "t".[mpmc_bqueue٠back] "back" "new_back"
        𝘁𝗵𝗲𝗻 (
          domain٠yield () ⍮
          "fix_back" "t" "t".{mpmc_bqueue٠back} "new_back"
        )
    𝗲𝗻𝗱.

#[local] Definition __zoo_recs_0 :=
  ( 𝗿𝗲𝗰𝘀 "push_1" "t" "back" "cap" "new_back" ->
      𝗺𝗮𝘁𝗰𝗵 "back" 𝘄𝗶𝘁𝗵
      | mpmc_bqueue٠Node ⎽ ⎽ ⎽ ⎽ 𝗮𝘀 "back_r" ->
          𝗺𝗮𝘁𝗰𝗵 "new_back" 𝘄𝗶𝘁𝗵
          | mpmc_bqueue٠Node ⎽ ⎽ ⎽ ⎽ 𝗮𝘀 "new_back" ->
              𝗹𝗲𝘁 "new_back_r" = "new_back" 𝗶𝗻
              𝗶𝗳 "cap" == 0 𝘁𝗵𝗲𝗻 (
                𝗺𝗮𝘁𝗰𝗵
                  "t".{mpmc_bqueue٠front}
                𝘄𝗶𝘁𝗵
                | mpmc_bqueue٠Node ⎽ ⎽ ⎽ ⎽ 𝗮𝘀 "front_r" ->
                    𝗹𝗲𝘁 "cap" =
                      "t".{mpmc_bqueue٠capacity}
                      -
                      ("back_r".{mpmc_bqueue٠index}
                       -
                       "front_r".{mpmc_bqueue٠index})
                    𝗶𝗻
                    𝗶𝗳 "cap" == 0 𝘁𝗵𝗲𝗻 (
                      false
                    ) 𝗲𝗹𝘀𝗲 (
                      "back_r" <-{mpmc_bqueue٠estimated_capacity} "cap" ⍮
                      "push_1" "t" "back" "cap" "new_back"
                    )
                𝗲𝗻𝗱
              ) 𝗲𝗹𝘀𝗲 (
                "new_back_r" <-{mpmc_bqueue٠index}
                  "back_r".{mpmc_bqueue٠index} + 1 ⍮
                "new_back_r" <-{mpmc_bqueue٠estimated_capacity} "cap" - 1 ⍮
                𝗶𝗳
                  𝗰𝗮𝘀
                    "back_r".[mpmc_bqueue٠next]
                    §mpmc_bqueue٠Null
                    "new_back"
                𝘁𝗵𝗲𝗻 (
                  mpmc_bqueue٠fix_back "t" "back" "new_back" ⍮
                  true
                ) 𝗲𝗹𝘀𝗲 (
                  𝗺𝗮𝘁𝗰𝗵
                    "back_r".{mpmc_bqueue٠next}
                  𝘄𝗶𝘁𝗵
                  | mpmc_bqueue٠Null ->
                      𝗳𝗮𝗶𝗹
                  | mpmc_bqueue٠Node ⎽ ⎽ ⎽ ⎽ 𝗮𝘀 "back" ->
                      "push_2" "t" "back" "new_back"
                  𝗲𝗻𝗱
                )
              )
          𝗲𝗻𝗱
      𝗲𝗻𝗱
    𝘄𝗶𝘁𝗵 "push_2" "t" "back" "new_back" ->
      𝗺𝗮𝘁𝗰𝗵 "back" 𝘄𝗶𝘁𝗵
      | mpmc_bqueue٠Node ⎽ ⎽ ⎽ ⎽ 𝗮𝘀 "back" ->
          𝗹𝗲𝘁 "back_r" = "back" 𝗶𝗻
          "push_1"
            "t"
            "back"
            "back_r".{mpmc_bqueue٠estimated_capacity}
            "new_back"
      𝗲𝗻𝗱
  )%zoo_recs.
Definition mpmc_bqueue٠push_1 :=
  ValRecs 0 __zoo_recs_0.
Definition mpmc_bqueue٠push_2 :=
  ValRecs 1 __zoo_recs_0.
#[global] Instance :
  AsValRecs' mpmc_bqueue٠push_1 0 __zoo_recs_0 [
    mpmc_bqueue٠push_1 ;
    mpmc_bqueue٠push_2
  ].
Proof.
  done.
Qed.
#[global] Instance :
  AsValRecs' mpmc_bqueue٠push_2 1 __zoo_recs_0 [
    mpmc_bqueue٠push_1 ;
    mpmc_bqueue٠push_2
  ].
Proof.
  done.
Qed.

Definition mpmc_bqueue٠push : val :=
  𝗳𝘂𝗻 "t" "v" ->
    𝗹𝗲𝘁 "new_back" =
      ‘mpmc_bqueue٠Node{ §mpmc_bqueue٠Null, "v", 0, 0 }
    𝗶𝗻
    mpmc_bqueue٠push_2 "t" "t".{mpmc_bqueue٠back} "new_back".

Definition mpmc_bqueue٠pop : val :=
  𝗿𝗲𝗰 "pop" "t" ->
    𝗺𝗮𝘁𝗰𝗵 "t".{mpmc_bqueue٠front} 𝘄𝗶𝘁𝗵
    | mpmc_bqueue٠Node ⎽ ⎽ ⎽ ⎽ 𝗮𝘀 "front" ->
        𝗹𝗲𝘁 "front_r" = "front" 𝗶𝗻
        𝗺𝗮𝘁𝗰𝗵 "front_r".{mpmc_bqueue٠next} 𝘄𝗶𝘁𝗵
        | mpmc_bqueue٠Null ->
            §None
        | mpmc_bqueue٠Node ⎽ ⎽ ⎽ ⎽ 𝗮𝘀 "new_front" ->
            𝗹𝗲𝘁 "new_front_r" = "new_front" 𝗶𝗻
            𝗶𝗳
              𝗰𝗮𝘀 "t".[mpmc_bqueue٠front] "front" "new_front"
            𝘁𝗵𝗲𝗻 (
              𝗹𝗲𝘁 "v" = "new_front_r".{mpmc_bqueue٠data} 𝗶𝗻
              "new_front_r" <-{mpmc_bqueue٠data} () ⍮
              ‘Some( "v" )
            ) 𝗲𝗹𝘀𝗲 (
              domain٠yield () ⍮
              "pop" "t"
            )
        𝗲𝗻𝗱
    𝗲𝗻𝗱.
