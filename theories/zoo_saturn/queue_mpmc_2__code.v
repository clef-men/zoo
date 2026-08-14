Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.domain.
Require Import zoo.options.

Notation "'queue_mpmc_2٠Front'" := (
  in_type "zoo_saturn.queue_mpmc_2.suffix" 0
)(in custom zoo_tag
).
Notation "'queue_mpmc_2٠Cons'" := (
  in_type "zoo_saturn.queue_mpmc_2.suffix" 1
)(in custom zoo_tag
).

Notation "'queue_mpmc_2٠Back'" := (
  in_type "zoo_saturn.queue_mpmc_2.prefix" 0
)(in custom zoo_tag
).
Notation "'queue_mpmc_2٠Snoc'" := (
  in_type "zoo_saturn.queue_mpmc_2.prefix" 1
)(in custom zoo_tag
).
Notation "'queue_mpmc_2٠Used'" := (
  in_type "zoo_saturn.queue_mpmc_2.prefix" 2
)(in custom zoo_tag
).

Notation "'queue_mpmc_2٠index'" := (
  in_type "zoo_saturn.queue_mpmc_2.prefix.Back" 0
)(in custom zoo_field
).
Notation "'queue_mpmc_2٠move'" := (
  in_type "zoo_saturn.queue_mpmc_2.prefix.Back" 1
)(in custom zoo_field
).

Notation "'queue_mpmc_2٠front'" := (
  in_type "zoo_saturn.queue_mpmc_2.t" 0
)(in custom zoo_field
).
Notation "'queue_mpmc_2٠back'" := (
  in_type "zoo_saturn.queue_mpmc_2.t" 1
)(in custom zoo_field
).

Definition queue_mpmc_2٠suffix_index : val :=
  𝗳𝘂𝗻 "suff" ->
    𝗺𝗮𝘁𝗰𝗵 "suff" 𝘄𝗶𝘁𝗵
    | queue_mpmc_2٠Front "i" ->
        "i"
    | queue_mpmc_2٠Cons "i" ⎽ ⎽ ->
        "i"
    𝗲𝗻𝗱.

Definition queue_mpmc_2٠prefix_index : val :=
  𝗳𝘂𝗻 "pref" ->
    𝗺𝗮𝘁𝗰𝗵 "pref" 𝘄𝗶𝘁𝗵
    | queue_mpmc_2٠Back ⎽ ⎽ 𝗮𝘀 "back_r" ->
        "back_r".{queue_mpmc_2٠index}
    | queue_mpmc_2٠Snoc "i" ⎽ ⎽ ->
        "i"
    𝗲𝗻𝗱.

Definition queue_mpmc_2٠rev₁ : val :=
  𝗿𝗲𝗰 "rev" "suff" "pref" ->
    𝗺𝗮𝘁𝗰𝗵 "suff" 𝘄𝗶𝘁𝗵
    | queue_mpmc_2٠Cons ⎽ ⎽ ⎽ 𝗮𝘀 "suff" ->
        𝗺𝗮𝘁𝗰𝗵 "pref" 𝘄𝗶𝘁𝗵
        | queue_mpmc_2٠Back ⎽ ⎽ ->
            "suff"
        | queue_mpmc_2٠Snoc "i" "v" "pref" ->
            "rev" ‘queue_mpmc_2٠Cons[ "i", "v", "suff" ] "pref"
        𝗲𝗻𝗱
    𝗲𝗻𝗱.

Definition queue_mpmc_2٠rev : val :=
  𝗳𝘂𝗻 "back" ->
    𝗺𝗮𝘁𝗰𝗵 "back" 𝘄𝗶𝘁𝗵
    | queue_mpmc_2٠Snoc "i" "v" "pref" ->
        queue_mpmc_2٠rev₁
          ‘queue_mpmc_2٠Cons[ "i",
            "v",
            ‘queue_mpmc_2٠Front[ "i" + 1 ]
          ]
          "pref"
    𝗲𝗻𝗱.

Definition queue_mpmc_2٠create : val :=
  𝗳𝘂𝗻 ⎽ ->
    { ‘queue_mpmc_2٠Front[ 1 ],
      ‘queue_mpmc_2٠Back{ 0, §queue_mpmc_2٠Used }
    }.

Definition queue_mpmc_2٠size : val :=
  𝗿𝗲𝗰 "size" "t" ->
    𝗹𝗲𝘁 "front" = "t".{queue_mpmc_2٠front} 𝗶𝗻
    𝗹𝗲𝘁 "proph" = 𝗽𝗿𝗼𝗽𝗵 𝗶𝗻
    𝗹𝗲𝘁 "back" = "t".{queue_mpmc_2٠back} 𝗶𝗻
    𝗶𝗳
      𝗹𝗲𝘁 "@tmp" = "t".{queue_mpmc_2٠front} == "front" 𝗶𝗻
      𝗿𝗲𝘀𝗼𝗹𝘃𝗲 𝘀𝗸𝗶𝗽 "proph" "@tmp" ⍮
      "@tmp"
    𝘁𝗵𝗲𝗻 (
      queue_mpmc_2٠prefix_index "back" - queue_mpmc_2٠suffix_index "front"
      +
      1
    ) 𝗲𝗹𝘀𝗲 (
      "size" "t"
    ).

Definition queue_mpmc_2٠is_empty : val :=
  𝗳𝘂𝗻 "t" ->
    queue_mpmc_2٠size "t" == 0.

Definition queue_mpmc_2٠finish : val :=
  𝗳𝘂𝗻 "back" ->
    𝗺𝗮𝘁𝗰𝗵 "back" 𝘄𝗶𝘁𝗵
    | queue_mpmc_2٠Back ⎽ ⎽ 𝗮𝘀 "back_r" ->
        "back_r" <-{queue_mpmc_2٠move} §queue_mpmc_2٠Used
    𝗲𝗻𝗱.

Definition queue_mpmc_2٠help : val :=
  𝗳𝘂𝗻 "t" "back" "i_move" "move" ->
    𝗺𝗮𝘁𝗰𝗵 "t".{queue_mpmc_2٠front} 𝘄𝗶𝘁𝗵
    | queue_mpmc_2٠Front "i_front" 𝗮𝘀 "front" ->
        𝗶𝗳
          "i_move" < "i_front"
          𝗼𝗿
          𝗰𝗮𝘀
            "t".[queue_mpmc_2٠front]
            "front"
            (queue_mpmc_2٠rev "move")
        𝘁𝗵𝗲𝗻 (
          queue_mpmc_2٠finish "back"
        )
    | ⎽ ->
        queue_mpmc_2٠finish "back"
    𝗲𝗻𝗱.

#[local] Definition __zoo_recs_0 :=
  ( 𝗿𝗲𝗰𝘀 "push_aux" "t" "v" "i" "back" ->
      𝗹𝗲𝘁 "new_back" =
        ‘queue_mpmc_2٠Snoc[ "i" + 1, "v", "back" ]
      𝗶𝗻
      𝗶𝗳
        ~ 𝗰𝗮𝘀 "t".[queue_mpmc_2٠back] "back" "new_back"
      𝘁𝗵𝗲𝗻 (
        domain٠yield () ⍮
        "push" "t" "v"
      )
    𝘄𝗶𝘁𝗵 "push" "t" "v" ->
      𝗺𝗮𝘁𝗰𝗵 "t".{queue_mpmc_2٠back} 𝘄𝗶𝘁𝗵
      | queue_mpmc_2٠Snoc "i" ⎽ ⎽ 𝗮𝘀 "back" ->
          "push_aux" "t" "v" "i" "back"
      | queue_mpmc_2٠Back ⎽ ⎽ 𝗮𝘀 "back" ->
          𝗹𝗲𝘁 "back_r" = "back" 𝗶𝗻
          𝗺𝗮𝘁𝗰𝗵 "back_r".{queue_mpmc_2٠move} 𝘄𝗶𝘁𝗵
          | queue_mpmc_2٠Used ->
              "push_aux" "t" "v" "back_r".{queue_mpmc_2٠index} "back"
          | queue_mpmc_2٠Snoc "i_move" ⎽ ⎽ 𝗮𝘀 "move" ->
              queue_mpmc_2٠help "t" "back" "i_move" "move" ⍮
              "push" "t" "v"
          𝗲𝗻𝗱
      𝗲𝗻𝗱
  )%zoo_recs.
Definition queue_mpmc_2٠push_aux :=
  ValRecs 0 __zoo_recs_0.
Definition queue_mpmc_2٠push :=
  ValRecs 1 __zoo_recs_0.
#[global] Instance :
  AsValRecs' queue_mpmc_2٠push_aux 0 __zoo_recs_0 [
    queue_mpmc_2٠push_aux ;
    queue_mpmc_2٠push
  ].
Proof.
  done.
Qed.
#[global] Instance :
  AsValRecs' queue_mpmc_2٠push 1 __zoo_recs_0 [
    queue_mpmc_2٠push_aux ;
    queue_mpmc_2٠push
  ].
Proof.
  done.
Qed.

#[local] Definition __zoo_recs_1 :=
  ( 𝗿𝗲𝗰𝘀 "pop_1" "t" "front" ->
      𝗺𝗮𝘁𝗰𝗵 "front" 𝘄𝗶𝘁𝗵
      | queue_mpmc_2٠Cons ⎽ "v" "new_front" ->
          𝗶𝗳
            𝗰𝗮𝘀 "t".[queue_mpmc_2٠front] "front" "new_front"
          𝘁𝗵𝗲𝗻 (
            ‘Some( "v" )
          ) 𝗲𝗹𝘀𝗲 (
            domain٠yield () ⍮
            "pop" "t"
          )
      | queue_mpmc_2٠Front "i_front" 𝗮𝘀 "front" ->
          𝗺𝗮𝘁𝗰𝗵 "t".{queue_mpmc_2٠back} 𝘄𝗶𝘁𝗵
          | queue_mpmc_2٠Snoc "i_move" "v" "move_pref" 𝗮𝘀 "move" ->
              𝗶𝗳 "i_front" == "i_move" 𝘁𝗵𝗲𝗻 (
                𝗶𝗳
                  𝗰𝗮𝘀 "t".[queue_mpmc_2٠back] "move" "move_pref"
                𝘁𝗵𝗲𝗻 (
                  ‘Some( "v" )
                ) 𝗲𝗹𝘀𝗲 (
                  "pop" "t"
                )
              ) 𝗲𝗹𝘀𝗲 (
                𝗺𝗮𝘁𝗰𝗵
                  ‘queue_mpmc_2٠Back{ "i_move", "move" }
                𝘄𝗶𝘁𝗵
                | queue_mpmc_2٠Back ⎽ ⎽ 𝗮𝘀 "back" ->
                    𝗹𝗲𝘁 "front'" =
                      "t".{queue_mpmc_2٠front}
                    𝗶𝗻
                    𝗶𝗳 "front'" != "front" 𝘁𝗵𝗲𝗻 (
                      "pop_1" "t" "front'"
                    ) 𝗲𝗹𝘀𝗲 𝗶𝗳
                       𝗰𝗮𝘀 "t".[queue_mpmc_2٠back] "move" "back"
                     𝘁𝗵𝗲𝗻 (
                      "pop_2" "t" "front" "back" "move"
                    ) 𝗲𝗹𝘀𝗲 (
                      "pop" "t"
                    )
                𝗲𝗻𝗱
              )
          | queue_mpmc_2٠Back ⎽ ⎽ ->
              "pop_3" "t" "front"
          𝗲𝗻𝗱
      𝗲𝗻𝗱
    𝘄𝗶𝘁𝗵 "pop_2" "t" "front" "back" "move" ->
      𝗺𝗮𝘁𝗰𝗵 queue_mpmc_2٠rev "move" 𝘄𝗶𝘁𝗵
      | queue_mpmc_2٠Cons ⎽ "v" "new_front" ->
          𝗶𝗳
            𝗰𝗮𝘀 "t".[queue_mpmc_2٠front] "front" "new_front"
          𝘁𝗵𝗲𝗻 (
            queue_mpmc_2٠finish "back" ⍮
            ‘Some( "v" )
          ) 𝗲𝗹𝘀𝗲 (
            domain٠yield () ⍮
            "pop" "t"
          )
      𝗲𝗻𝗱
    𝘄𝗶𝘁𝗵 "pop_3" "t" "front" ->
      𝗹𝗲𝘁 "front'" = "t".{queue_mpmc_2٠front} 𝗶𝗻
      𝗶𝗳 "front'" == "front" 𝘁𝗵𝗲𝗻 (
        §None
      ) 𝗲𝗹𝘀𝗲 (
        "pop_1" "t" "front'"
      )
    𝘄𝗶𝘁𝗵 "pop" "t" ->
      "pop_1" "t" "t".{queue_mpmc_2٠front}
  )%zoo_recs.
Definition queue_mpmc_2٠pop_1 :=
  ValRecs 0 __zoo_recs_1.
Definition queue_mpmc_2٠pop_2 :=
  ValRecs 1 __zoo_recs_1.
Definition queue_mpmc_2٠pop_3 :=
  ValRecs 2 __zoo_recs_1.
Definition queue_mpmc_2٠pop :=
  ValRecs 3 __zoo_recs_1.
#[global] Instance :
  AsValRecs' queue_mpmc_2٠pop_1 0 __zoo_recs_1 [
    queue_mpmc_2٠pop_1 ;
    queue_mpmc_2٠pop_2 ;
    queue_mpmc_2٠pop_3 ;
    queue_mpmc_2٠pop
  ].
Proof.
  done.
Qed.
#[global] Instance :
  AsValRecs' queue_mpmc_2٠pop_2 1 __zoo_recs_1 [
    queue_mpmc_2٠pop_1 ;
    queue_mpmc_2٠pop_2 ;
    queue_mpmc_2٠pop_3 ;
    queue_mpmc_2٠pop
  ].
Proof.
  done.
Qed.
#[global] Instance :
  AsValRecs' queue_mpmc_2٠pop_3 2 __zoo_recs_1 [
    queue_mpmc_2٠pop_1 ;
    queue_mpmc_2٠pop_2 ;
    queue_mpmc_2٠pop_3 ;
    queue_mpmc_2٠pop
  ].
Proof.
  done.
Qed.
#[global] Instance :
  AsValRecs' queue_mpmc_2٠pop 3 __zoo_recs_1 [
    queue_mpmc_2٠pop_1 ;
    queue_mpmc_2٠pop_2 ;
    queue_mpmc_2٠pop_3 ;
    queue_mpmc_2٠pop
  ].
Proof.
  done.
Qed.
