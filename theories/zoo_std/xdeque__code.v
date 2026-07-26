Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.xdeque__types.
Require Import zoo.options.

Definition xdeque٠create : val :=
  𝗳𝘂𝗻 ⎽ ->
    𝗹𝗲𝘁 "t" = { (), (), () } 𝗶𝗻
    "t" <-{xdeque_prev} "t" ⍮
    "t" <-{xdeque_next} "t" ⍮
    "t".

Definition xdeque٠is_empty : val :=
  𝗳𝘂𝗻 "t" ->
    "t".{xdeque_next} == "t".

Definition xdeque٠link : val :=
  𝗳𝘂𝗻 "node1" "node2" ->
    "node1" <-{xdeque_next} "node2" ⍮
    "node2" <-{xdeque_prev} "node1".

Definition xdeque٠insert : val :=
  𝗳𝘂𝗻 "prev" "node" "next" ->
    xdeque٠link "prev" "node" ⍮
    xdeque٠link "node" "next".

Definition xdeque٠push_front : val :=
  𝗳𝘂𝗻 "t" "front" ->
    xdeque٠insert "t" "front" "t".{xdeque_next}.

Definition xdeque٠push_back : val :=
  𝗳𝘂𝗻 "t" "back" ->
    xdeque٠insert "t".{xdeque_prev} "back" "t".

Definition xdeque٠pop_front : val :=
  𝗳𝘂𝗻 "t" ->
    𝗶𝗳 xdeque٠is_empty "t" 𝘁𝗵𝗲𝗻 (
      §None
    ) 𝗲𝗹𝘀𝗲 (
      𝗹𝗲𝘁 "old_front" = "t".{xdeque_next} 𝗶𝗻
      𝗹𝗲𝘁 "front" = "old_front".{xdeque_next} 𝗶𝗻
      xdeque٠link "t" "front" ⍮
      ‘Some( "old_front" )
    ).

Definition xdeque٠pop_back : val :=
  𝗳𝘂𝗻 "t" ->
    𝗶𝗳 xdeque٠is_empty "t" 𝘁𝗵𝗲𝗻 (
      §None
    ) 𝗲𝗹𝘀𝗲 (
      𝗹𝗲𝘁 "old_back" = "t".{xdeque_prev} 𝗶𝗻
      𝗹𝗲𝘁 "back" = "old_back".{xdeque_prev} 𝗶𝗻
      xdeque٠link "back" "t" ⍮
      ‘Some( "old_back" )
    ).

Definition xdeque٠remove : val :=
  𝗳𝘂𝗻 "node" ->
    𝗹𝗲𝘁 "prev" = "node".{xdeque_prev} 𝗶𝗻
    𝗹𝗲𝘁 "next" = "node".{xdeque_next} 𝗶𝗻
    xdeque٠link "prev" "next".

Definition xdeque٠iter_aux : val :=
  𝗿𝗲𝗰 "iter_aux" "fn" "t" "node" ->
    𝗶𝗳 "node" == "t" 𝘁𝗵𝗲𝗻 (
      ()
    ) 𝗲𝗹𝘀𝗲 (
      "fn" "node" ⍮
      "iter_aux" "fn" "t" "node".{xdeque_next}
    ).

Definition xdeque٠iter : val :=
  𝗳𝘂𝗻 "fn" "t" ->
    xdeque٠iter_aux "fn" "t" "t".{xdeque_next}.
