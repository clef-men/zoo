Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.domain.
Require Import zoo_saturn.mpmc_queue_2__types.
Require Import zoo.options.

Definition mpmc_queue_2٠suffix_index : val :=
  𝗳𝘂𝗻 "suff" ->
    𝗺𝗮𝘁𝗰𝗵 "suff" 𝘄𝗶𝘁𝗵
    | Front "i" ->
        "i"
    | Cons "i" ⎽ ⎽ ->
        "i"
    𝗲𝗻𝗱.

Definition mpmc_queue_2٠prefix_index : val :=
  𝗳𝘂𝗻 "pref" ->
    𝗺𝗮𝘁𝗰𝗵 "pref" 𝘄𝗶𝘁𝗵
    | Back ⎽ ⎽ 𝗮𝘀 "back_r" ->
        "back_r".{index}
    | Snoc "i" ⎽ ⎽ ->
        "i"
    𝗲𝗻𝗱.

Definition mpmc_queue_2٠rev₀ : val :=
  𝗿𝗲𝗰 "rev" "suff" "pref" ->
    𝗺𝗮𝘁𝗰𝗵 "suff" 𝘄𝗶𝘁𝗵
    | Cons ⎽ ⎽ ⎽ 𝗮𝘀 "suff" ->
        𝗺𝗮𝘁𝗰𝗵 "pref" 𝘄𝗶𝘁𝗵
        | Back ⎽ ⎽ ->
            "suff"
        | Snoc "i" "v" "pref" ->
            "rev" ‘Cons[ "i", "v", "suff" ] "pref"
        𝗲𝗻𝗱
    𝗲𝗻𝗱.

Definition mpmc_queue_2٠rev : val :=
  𝗳𝘂𝗻 "back" ->
    𝗺𝗮𝘁𝗰𝗵 "back" 𝘄𝗶𝘁𝗵
    | Snoc "i" "v" "pref" ->
        mpmc_queue_2٠rev₀ ‘Cons[ "i", "v", ‘Front[ "i" + 1 ] ] "pref"
    𝗲𝗻𝗱.

Definition mpmc_queue_2٠create : val :=
  𝗳𝘂𝗻 ⎽ ->
    { ‘Front[ 1 ], ‘Back{ 0, §Used } }.

Definition mpmc_queue_2٠size : val :=
  𝗿𝗲𝗰 "size" "t" ->
    𝗹𝗲𝘁 "front" = "t".{front} 𝗶𝗻
    𝗹𝗲𝘁 "proph" = 𝗽𝗿𝗼𝗽𝗵 𝗶𝗻
    𝗹𝗲𝘁 "back" = "t".{back} 𝗶𝗻
    𝗶𝗳
      𝗹𝗲𝘁 "@tmp" = "t".{front} == "front" 𝗶𝗻
      𝗿𝗲𝘀𝗼𝗹𝘃𝗲 𝘀𝗸𝗶𝗽 "proph" "@tmp" ⍮
      "@tmp"
    𝘁𝗵𝗲𝗻 (
      mpmc_queue_2٠prefix_index "back" - mpmc_queue_2٠suffix_index "front"
      +
      1
    ) 𝗲𝗹𝘀𝗲 (
      "size" "t"
    ).

Definition mpmc_queue_2٠is_empty : val :=
  𝗳𝘂𝗻 "t" ->
    mpmc_queue_2٠size "t" == 0.

Definition mpmc_queue_2٠finish : val :=
  𝗳𝘂𝗻 "back" ->
    𝗺𝗮𝘁𝗰𝗵 "back" 𝘄𝗶𝘁𝗵
    | Back ⎽ ⎽ 𝗮𝘀 "back_r" ->
        "back_r" <-{move} §Used
    𝗲𝗻𝗱.

Definition mpmc_queue_2٠help : val :=
  𝗳𝘂𝗻 "t" "back" "i_move" "move" ->
    𝗺𝗮𝘁𝗰𝗵 "t".{front} 𝘄𝗶𝘁𝗵
    | Front "i_front" 𝗮𝘀 "front" ->
        𝗶𝗳
          "i_move" < "i_front"
          𝗼𝗿
          𝗰𝗮𝘀 "t".[front] "front" (mpmc_queue_2٠rev "move")
        𝘁𝗵𝗲𝗻 (
          mpmc_queue_2٠finish "back"
        )
    | ⎽ ->
        mpmc_queue_2٠finish "back"
    𝗲𝗻𝗱.

#[local] Definition __zoo_recs_0 :=
  ( 𝗿𝗲𝗰𝘀 "push_aux" "t" "v" "i" "back" ->
      𝗹𝗲𝘁 "new_back" = ‘Snoc[ "i" + 1, "v", "back" ] 𝗶𝗻
      𝗶𝗳 ~ 𝗰𝗮𝘀 "t".[back] "back" "new_back" 𝘁𝗵𝗲𝗻 (
        domain٠yield () ⍮
        "push" "t" "v"
      )
    𝘄𝗶𝘁𝗵 "push" "t" "v" ->
      𝗺𝗮𝘁𝗰𝗵 "t".{back} 𝘄𝗶𝘁𝗵
      | Snoc "i" ⎽ ⎽ 𝗮𝘀 "back" ->
          "push_aux" "t" "v" "i" "back"
      | Back ⎽ ⎽ 𝗮𝘀 "back" ->
          𝗹𝗲𝘁 "back_r" = "back" 𝗶𝗻
          𝗺𝗮𝘁𝗰𝗵 "back_r".{move} 𝘄𝗶𝘁𝗵
          | Used ->
              "push_aux" "t" "v" "back_r".{index} "back"
          | Snoc "i_move" ⎽ ⎽ 𝗮𝘀 "move" ->
              mpmc_queue_2٠help "t" "back" "i_move" "move" ⍮
              "push" "t" "v"
          𝗲𝗻𝗱
      𝗲𝗻𝗱
  )%zoo_recs.
Definition mpmc_queue_2٠push_aux :=
  ValRecs 0 __zoo_recs_0.
Definition mpmc_queue_2٠push :=
  ValRecs 1 __zoo_recs_0.
#[global] Instance :
  AsValRecs' mpmc_queue_2٠push_aux 0 __zoo_recs_0 [
    mpmc_queue_2٠push_aux ;
    mpmc_queue_2٠push
  ].
Proof.
  done.
Qed.
#[global] Instance :
  AsValRecs' mpmc_queue_2٠push 1 __zoo_recs_0 [
    mpmc_queue_2٠push_aux ;
    mpmc_queue_2٠push
  ].
Proof.
  done.
Qed.

#[local] Definition __zoo_recs_1 :=
  ( 𝗿𝗲𝗰𝘀 "pop_1" "t" "front" ->
      𝗺𝗮𝘁𝗰𝗵 "front" 𝘄𝗶𝘁𝗵
      | Cons ⎽ "v" "new_front" ->
          𝗶𝗳
            𝗰𝗮𝘀 "t".[front] "front" "new_front"
          𝘁𝗵𝗲𝗻 (
            ‘Some( "v" )
          ) 𝗲𝗹𝘀𝗲 (
            domain٠yield () ⍮
            "pop" "t"
          )
      | Front "i_front" 𝗮𝘀 "front" ->
          𝗺𝗮𝘁𝗰𝗵 "t".{back} 𝘄𝗶𝘁𝗵
          | Snoc "i_move" "v" "move_pref" 𝗮𝘀 "move" ->
              𝗶𝗳 "i_front" == "i_move" 𝘁𝗵𝗲𝗻 (
                𝗶𝗳
                  𝗰𝗮𝘀 "t".[back] "move" "move_pref"
                𝘁𝗵𝗲𝗻 (
                  ‘Some( "v" )
                ) 𝗲𝗹𝘀𝗲 (
                  "pop" "t"
                )
              ) 𝗲𝗹𝘀𝗲 (
                𝗺𝗮𝘁𝗰𝗵
                  ‘Back{ "i_move", "move" }
                𝘄𝗶𝘁𝗵
                | Back ⎽ ⎽ 𝗮𝘀 "back" ->
                    𝗹𝗲𝘁 "front'" = "t".{front} 𝗶𝗻
                    𝗶𝗳 "front'" != "front" 𝘁𝗵𝗲𝗻 (
                      "pop_1" "t" "front'"
                    ) 𝗲𝗹𝘀𝗲 𝗶𝗳
                       𝗰𝗮𝘀 "t".[back] "move" "back"
                     𝘁𝗵𝗲𝗻 (
                      "pop_2" "t" "front" "back" "move"
                    ) 𝗲𝗹𝘀𝗲 (
                      "pop" "t"
                    )
                𝗲𝗻𝗱
              )
          | Back ⎽ ⎽ ->
              "pop_3" "t" "front"
          𝗲𝗻𝗱
      𝗲𝗻𝗱
    𝘄𝗶𝘁𝗵 "pop_2" "t" "front" "back" "move" ->
      𝗺𝗮𝘁𝗰𝗵 mpmc_queue_2٠rev "move" 𝘄𝗶𝘁𝗵
      | Cons ⎽ "v" "new_front" ->
          𝗶𝗳
            𝗰𝗮𝘀 "t".[front] "front" "new_front"
          𝘁𝗵𝗲𝗻 (
            mpmc_queue_2٠finish "back" ⍮
            ‘Some( "v" )
          ) 𝗲𝗹𝘀𝗲 (
            domain٠yield () ⍮
            "pop" "t"
          )
      𝗲𝗻𝗱
    𝘄𝗶𝘁𝗵 "pop_3" "t" "front" ->
      𝗹𝗲𝘁 "front'" = "t".{front} 𝗶𝗻
      𝗶𝗳 "front'" == "front" 𝘁𝗵𝗲𝗻 (
        §None
      ) 𝗲𝗹𝘀𝗲 (
        "pop_1" "t" "front'"
      )
    𝘄𝗶𝘁𝗵 "pop" "t" ->
      "pop_1" "t" "t".{front}
  )%zoo_recs.
Definition mpmc_queue_2٠pop_1 :=
  ValRecs 0 __zoo_recs_1.
Definition mpmc_queue_2٠pop_2 :=
  ValRecs 1 __zoo_recs_1.
Definition mpmc_queue_2٠pop_3 :=
  ValRecs 2 __zoo_recs_1.
Definition mpmc_queue_2٠pop :=
  ValRecs 3 __zoo_recs_1.
#[global] Instance :
  AsValRecs' mpmc_queue_2٠pop_1 0 __zoo_recs_1 [
    mpmc_queue_2٠pop_1 ;
    mpmc_queue_2٠pop_2 ;
    mpmc_queue_2٠pop_3 ;
    mpmc_queue_2٠pop
  ].
Proof.
  done.
Qed.
#[global] Instance :
  AsValRecs' mpmc_queue_2٠pop_2 1 __zoo_recs_1 [
    mpmc_queue_2٠pop_1 ;
    mpmc_queue_2٠pop_2 ;
    mpmc_queue_2٠pop_3 ;
    mpmc_queue_2٠pop
  ].
Proof.
  done.
Qed.
#[global] Instance :
  AsValRecs' mpmc_queue_2٠pop_3 2 __zoo_recs_1 [
    mpmc_queue_2٠pop_1 ;
    mpmc_queue_2٠pop_2 ;
    mpmc_queue_2٠pop_3 ;
    mpmc_queue_2٠pop
  ].
Proof.
  done.
Qed.
#[global] Instance :
  AsValRecs' mpmc_queue_2٠pop 3 __zoo_recs_1 [
    mpmc_queue_2٠pop_1 ;
    mpmc_queue_2٠pop_2 ;
    mpmc_queue_2٠pop_3 ;
    mpmc_queue_2٠pop
  ].
Proof.
  done.
Qed.
