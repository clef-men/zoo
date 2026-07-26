Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.domain.
Require Import zoo_saturn.mpmc_bstack__types.
Require Import zoo.options.

Definition mpmc_bstack٠create : val :=
  𝗳𝘂𝗻 "cap" ->
    { "cap", §Nil }.

Definition mpmc_bstack٠size : val :=
  𝗳𝘂𝗻 "t" ->
    𝗺𝗮𝘁𝗰𝗵 "t".{front} 𝘄𝗶𝘁𝗵
    | Nil ->
        0
    | Cons "sz" ⎽ ⎽ ->
        "sz"
    𝗲𝗻𝗱.

Definition mpmc_bstack٠is_empty : val :=
  𝗳𝘂𝗻 "t" ->
    "t".{front} == §Nil.

#[local] Definition __zoo_recs_0 :=
  ( 𝗿𝗲𝗰𝘀 "push_aux" "t" "sz" "v" "front" ->
      𝗹𝗲𝘁 "new_front" = ‘Cons[ "sz" + 1, "v", "front" ] 𝗶𝗻
      𝗶𝗳
        𝗰𝗮𝘀 "t".[front] "front" "new_front"
      𝘁𝗵𝗲𝗻 (
        true
      ) 𝗲𝗹𝘀𝗲 (
        domain٠yield () ⍮
        "push" "t" "v"
      )
    𝘄𝗶𝘁𝗵 "push" "t" "v" ->
      𝗺𝗮𝘁𝗰𝗵 "t".{front} 𝘄𝗶𝘁𝗵
      | Nil ->
          "push_aux" "t" 0 "v" §Nil
      | Cons "sz" ⎽ ⎽ 𝗮𝘀 "front" ->
          𝗶𝗳 "t".{capacity} ≤ "sz" 𝘁𝗵𝗲𝗻 (
            false
          ) 𝗲𝗹𝘀𝗲 (
            "push_aux" "t" "sz" "v" "front"
          )
      𝗲𝗻𝗱
  )%zoo_recs.
Definition mpmc_bstack٠push_aux :=
  ValRecs 0 __zoo_recs_0.
Definition mpmc_bstack٠push :=
  ValRecs 1 __zoo_recs_0.
#[global] Instance :
  AsValRecs' mpmc_bstack٠push_aux 0 __zoo_recs_0 [
    mpmc_bstack٠push_aux ;
    mpmc_bstack٠push
  ].
Proof.
  done.
Qed.
#[global] Instance :
  AsValRecs' mpmc_bstack٠push 1 __zoo_recs_0 [
    mpmc_bstack٠push_aux ;
    mpmc_bstack٠push
  ].
Proof.
  done.
Qed.

Definition mpmc_bstack٠pop : val :=
  𝗿𝗲𝗰 "pop" "t" ->
    𝗺𝗮𝘁𝗰𝗵 "t".{front} 𝘄𝗶𝘁𝗵
    | Nil ->
        §None
    | Cons ⎽ "v" "new_front" 𝗮𝘀 "front" ->
        𝗶𝗳
          𝗰𝗮𝘀 "t".[front] "front" "new_front"
        𝘁𝗵𝗲𝗻 (
          ‘Some( "v" )
        ) 𝗲𝗹𝘀𝗲 (
          domain٠yield () ⍮
          "pop" "t"
        )
    𝗲𝗻𝗱.
