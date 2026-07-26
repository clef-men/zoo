Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.domain.
Require Import zoo_saturn.mpmc_bqueue__types.
Require Import zoo.options.

Definition mpmc_bqueue٠create : val :=
  𝗳𝘂𝗻 "cap" ->
    𝗹𝗲𝘁 "front" = ‘Node{ §Null, (), 0, "cap" } 𝗶𝗻
    { "cap", "front", "front" }.

Definition mpmc_bqueue٠capacity : val :=
  𝗳𝘂𝗻 "t" ->
    "t".{capacity}.

Definition mpmc_bqueue٠size : val :=
  𝗿𝗲𝗰 "size" "t" ->
    𝗺𝗮𝘁𝗰𝗵 "t".{front} 𝘄𝗶𝘁𝗵
    | Node ⎽ ⎽ ⎽ ⎽ 𝗮𝘀 "front" ->
        𝗹𝗲𝘁 "front_r" = "front" 𝗶𝗻
        𝗹𝗲𝘁 "proph" = 𝗽𝗿𝗼𝗽𝗵 𝗶𝗻
        𝗺𝗮𝘁𝗰𝗵 "t".{back} 𝘄𝗶𝘁𝗵
        | Node ⎽ ⎽ ⎽ ⎽ 𝗮𝘀 "back" ->
            𝗹𝗲𝘁 "back_r" = "back" 𝗶𝗻
            𝗺𝗮𝘁𝗰𝗵 "back_r".{next} 𝘄𝗶𝘁𝗵
            | Node ⎽ ⎽ ⎽ ⎽ 𝗮𝘀 "node" ->
                𝗰𝗮𝘀 "t".[back] "back" "node" ⍮
                "size" "t"
            | Null ->
                𝗶𝗳
                  𝗿𝗲𝘀𝗼𝗹𝘃𝗲 "t".{front} "proph" ()
                  ==
                  "front"
                𝘁𝗵𝗲𝗻 (
                  "back_r".{index} - "front_r".{index}
                ) 𝗲𝗹𝘀𝗲 (
                  "size" "t"
                )
            𝗲𝗻𝗱
        𝗲𝗻𝗱
    𝗲𝗻𝗱.

Definition mpmc_bqueue٠is_empty : val :=
  𝗳𝘂𝗻 "t" ->
    𝗺𝗮𝘁𝗰𝗵 "t".{front} 𝘄𝗶𝘁𝗵
    | Node ⎽ ⎽ ⎽ ⎽ 𝗮𝘀 "front_r" ->
        "front_r".{next} == §Null
    𝗲𝗻𝗱.

Definition mpmc_bqueue٠fix_back : val :=
  𝗿𝗲𝗰 "fix_back" "t" "back" "new_back" ->
    𝗺𝗮𝘁𝗰𝗵 "new_back" 𝘄𝗶𝘁𝗵
    | Node ⎽ ⎽ ⎽ ⎽ 𝗮𝘀 "new_back_r" ->
        𝗶𝗳
          "new_back_r".{next} == §Null
          𝗮𝗻𝗱
          ~ 𝗰𝗮𝘀 "t".[back] "back" "new_back"
        𝘁𝗵𝗲𝗻 (
          domain٠yield () ⍮
          "fix_back" "t" "t".{back} "new_back"
        )
    𝗲𝗻𝗱.

#[local] Definition __zoo_recs_0 :=
  ( 𝗿𝗲𝗰𝘀 "push_1" "t" "back" "cap" "new_back" ->
      𝗺𝗮𝘁𝗰𝗵 "back" 𝘄𝗶𝘁𝗵
      | Node ⎽ ⎽ ⎽ ⎽ 𝗮𝘀 "back_r" ->
          𝗺𝗮𝘁𝗰𝗵 "new_back" 𝘄𝗶𝘁𝗵
          | Node ⎽ ⎽ ⎽ ⎽ 𝗮𝘀 "new_back" ->
              𝗹𝗲𝘁 "new_back_r" = "new_back" 𝗶𝗻
              𝗶𝗳 "cap" == 0 𝘁𝗵𝗲𝗻 (
                𝗺𝗮𝘁𝗰𝗵 "t".{front} 𝘄𝗶𝘁𝗵
                | Node ⎽ ⎽ ⎽ ⎽ 𝗮𝘀 "front_r" ->
                    𝗹𝗲𝘁 "cap" =
                      "t".{capacity} - ("back_r".{index} - "front_r".{index})
                    𝗶𝗻
                    𝗶𝗳 "cap" == 0 𝘁𝗵𝗲𝗻 (
                      false
                    ) 𝗲𝗹𝘀𝗲 (
                      "back_r" <-{estimated_capacity} "cap" ⍮
                      "push_1" "t" "back" "cap" "new_back"
                    )
                𝗲𝗻𝗱
              ) 𝗲𝗹𝘀𝗲 (
                "new_back_r" <-{index} "back_r".{index} + 1 ⍮
                "new_back_r" <-{estimated_capacity} "cap" - 1 ⍮
                𝗶𝗳
                  𝗰𝗮𝘀 "back_r".[next] §Null "new_back"
                𝘁𝗵𝗲𝗻 (
                  mpmc_bqueue٠fix_back "t" "back" "new_back" ⍮
                  true
                ) 𝗲𝗹𝘀𝗲 (
                  𝗺𝗮𝘁𝗰𝗵 "back_r".{next} 𝘄𝗶𝘁𝗵
                  | Null ->
                      𝗳𝗮𝗶𝗹
                  | Node ⎽ ⎽ ⎽ ⎽ 𝗮𝘀 "back" ->
                      "push_2" "t" "back" "new_back"
                  𝗲𝗻𝗱
                )
              )
          𝗲𝗻𝗱
      𝗲𝗻𝗱
    𝘄𝗶𝘁𝗵 "push_2" "t" "back" "new_back" ->
      𝗺𝗮𝘁𝗰𝗵 "back" 𝘄𝗶𝘁𝗵
      | Node ⎽ ⎽ ⎽ ⎽ 𝗮𝘀 "back" ->
          𝗹𝗲𝘁 "back_r" = "back" 𝗶𝗻
          "push_1" "t" "back" "back_r".{estimated_capacity} "new_back"
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
    𝗹𝗲𝘁 "new_back" = ‘Node{ §Null, "v", 0, 0 } 𝗶𝗻
    mpmc_bqueue٠push_2 "t" "t".{back} "new_back".

Definition mpmc_bqueue٠pop : val :=
  𝗿𝗲𝗰 "pop" "t" ->
    𝗺𝗮𝘁𝗰𝗵 "t".{front} 𝘄𝗶𝘁𝗵
    | Node ⎽ ⎽ ⎽ ⎽ 𝗮𝘀 "front" ->
        𝗹𝗲𝘁 "front_r" = "front" 𝗶𝗻
        𝗺𝗮𝘁𝗰𝗵 "front_r".{next} 𝘄𝗶𝘁𝗵
        | Null ->
            §None
        | Node ⎽ ⎽ ⎽ ⎽ 𝗮𝘀 "new_front" ->
            𝗹𝗲𝘁 "new_front_r" = "new_front" 𝗶𝗻
            𝗶𝗳
              𝗰𝗮𝘀 "t".[front] "front" "new_front"
            𝘁𝗵𝗲𝗻 (
              𝗹𝗲𝘁 "v" = "new_front_r".{data} 𝗶𝗻
              "new_front_r" <-{data} () ⍮
              ‘Some( "v" )
            ) 𝗲𝗹𝘀𝗲 (
              domain٠yield () ⍮
              "pop" "t"
            )
        𝗲𝗻𝗱
    𝗲𝗻𝗱.
