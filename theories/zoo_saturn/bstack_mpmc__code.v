Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.domain.
Require Import zoo.options.

Notation "'bstack_mpmc٠Nil'" := (
  in_type "zoo_saturn.bstack_mpmc.list" 0
)(in custom zoo_tag
).
Notation "'bstack_mpmc٠Cons'" := (
  in_type "zoo_saturn.bstack_mpmc.list" 1
)(in custom zoo_tag
).

Notation "'bstack_mpmc٠capacity'" := (
  in_type "zoo_saturn.bstack_mpmc.t" 0
)(in custom zoo_field
).
Notation "'bstack_mpmc٠front'" := (
  in_type "zoo_saturn.bstack_mpmc.t" 1
)(in custom zoo_field
).

Definition bstack_mpmc٠create : val :=
  𝗳𝘂𝗻 "cap" ->
    { "cap", §bstack_mpmc٠Nil }.

Definition bstack_mpmc٠size : val :=
  𝗳𝘂𝗻 "t" ->
    𝗺𝗮𝘁𝗰𝗵 "t".{bstack_mpmc٠front} 𝘄𝗶𝘁𝗵
    | bstack_mpmc٠Nil ->
        0
    | bstack_mpmc٠Cons "sz" ⎽ ⎽ ->
        "sz"
    𝗲𝗻𝗱.

Definition bstack_mpmc٠is_empty : val :=
  𝗳𝘂𝗻 "t" ->
    "t".{bstack_mpmc٠front} == §bstack_mpmc٠Nil.

#[local] Definition __zoo_recs_0 :=
  ( 𝗿𝗲𝗰𝘀 "push_aux" "t" "sz" "v" "front" ->
      𝗹𝗲𝘁 "new_front" =
        ‘bstack_mpmc٠Cons[ "sz" + 1, "v", "front" ]
      𝗶𝗻
      𝗶𝗳
        𝗰𝗮𝘀 "t".[bstack_mpmc٠front] "front" "new_front"
      𝘁𝗵𝗲𝗻 (
        true
      ) 𝗲𝗹𝘀𝗲 (
        domain٠yield () ⍮
        "push" "t" "v"
      )
    𝘄𝗶𝘁𝗵 "push" "t" "v" ->
      𝗺𝗮𝘁𝗰𝗵 "t".{bstack_mpmc٠front} 𝘄𝗶𝘁𝗵
      | bstack_mpmc٠Nil ->
          "push_aux" "t" 0 "v" §bstack_mpmc٠Nil
      | bstack_mpmc٠Cons "sz" ⎽ ⎽ 𝗮𝘀 "front" ->
          𝗶𝗳 "t".{bstack_mpmc٠capacity} ≤ "sz" 𝘁𝗵𝗲𝗻 (
            false
          ) 𝗲𝗹𝘀𝗲 (
            "push_aux" "t" "sz" "v" "front"
          )
      𝗲𝗻𝗱
  )%zoo_recs.
Definition bstack_mpmc٠push_aux :=
  ValRecs 0 __zoo_recs_0.
Definition bstack_mpmc٠push :=
  ValRecs 1 __zoo_recs_0.
#[global] Instance :
  AsValRecs' bstack_mpmc٠push_aux 0 __zoo_recs_0 [
    bstack_mpmc٠push_aux ;
    bstack_mpmc٠push
  ].
Proof.
  done.
Qed.
#[global] Instance :
  AsValRecs' bstack_mpmc٠push 1 __zoo_recs_0 [
    bstack_mpmc٠push_aux ;
    bstack_mpmc٠push
  ].
Proof.
  done.
Qed.

Definition bstack_mpmc٠pop : val :=
  𝗿𝗲𝗰 "pop" "t" ->
    𝗺𝗮𝘁𝗰𝗵 "t".{bstack_mpmc٠front} 𝘄𝗶𝘁𝗵
    | bstack_mpmc٠Nil ->
        §None
    | bstack_mpmc٠Cons ⎽ "v" "new_front" 𝗮𝘀 "front" ->
        𝗶𝗳
          𝗰𝗮𝘀 "t".[bstack_mpmc٠front] "front" "new_front"
        𝘁𝗵𝗲𝗻 (
          ‘Some( "v" )
        ) 𝗲𝗹𝘀𝗲 (
          domain٠yield () ⍮
          "pop" "t"
        )
    𝗲𝗻𝗱.
