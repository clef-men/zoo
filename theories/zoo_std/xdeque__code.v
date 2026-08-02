Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo.options.

Notation "'xdeque٠prev'" := (
  in_type "zoo_std.xdeque.node" 0
)(in custom zoo_field
).
Notation "'xdeque٠next'" := (
  in_type "zoo_std.xdeque.node" 1
)(in custom zoo_field
).
Notation "'xdeque٠data'" := (
  in_type "zoo_std.xdeque.node" 2
)(in custom zoo_field
).

Definition xdeque٠create : val :=
  𝗳𝘂𝗻 ⎽ ->
    𝗹𝗲𝘁 "t" = { (), (), () } 𝗶𝗻
    "t" <-{xdeque٠prev} "t" ⍮
    "t" <-{xdeque٠next} "t" ⍮
    "t".

Definition xdeque٠is_empty : val :=
  𝗳𝘂𝗻 "t" ->
    "t".{xdeque٠next} == "t".

Definition xdeque٠link : val :=
  𝗳𝘂𝗻 "node1" "node2" ->
    "node1" <-{xdeque٠next} "node2" ⍮
    "node2" <-{xdeque٠prev} "node1".

Definition xdeque٠insert : val :=
  𝗳𝘂𝗻 "prev" "node" "next" ->
    xdeque٠link "prev" "node" ⍮
    xdeque٠link "node" "next".

Definition xdeque٠push_front : val :=
  𝗳𝘂𝗻 "t" "front" ->
    xdeque٠insert "t" "front" "t".{xdeque٠next}.

Definition xdeque٠push_back : val :=
  𝗳𝘂𝗻 "t" "back" ->
    xdeque٠insert "t".{xdeque٠prev} "back" "t".

Definition xdeque٠pop_front : val :=
  𝗳𝘂𝗻 "t" ->
    𝗶𝗳 xdeque٠is_empty "t" 𝘁𝗵𝗲𝗻 (
      §None
    ) 𝗲𝗹𝘀𝗲 (
      𝗹𝗲𝘁 "old_front" = "t".{xdeque٠next} 𝗶𝗻
      𝗹𝗲𝘁 "front" = "old_front".{xdeque٠next} 𝗶𝗻
      xdeque٠link "t" "front" ⍮
      ‘Some( "old_front" )
    ).

Definition xdeque٠pop_back : val :=
  𝗳𝘂𝗻 "t" ->
    𝗶𝗳 xdeque٠is_empty "t" 𝘁𝗵𝗲𝗻 (
      §None
    ) 𝗲𝗹𝘀𝗲 (
      𝗹𝗲𝘁 "old_back" = "t".{xdeque٠prev} 𝗶𝗻
      𝗹𝗲𝘁 "back" = "old_back".{xdeque٠prev} 𝗶𝗻
      xdeque٠link "back" "t" ⍮
      ‘Some( "old_back" )
    ).

Definition xdeque٠remove : val :=
  𝗳𝘂𝗻 "node" ->
    𝗹𝗲𝘁 "prev" = "node".{xdeque٠prev} 𝗶𝗻
    𝗹𝗲𝘁 "next" = "node".{xdeque٠next} 𝗶𝗻
    xdeque٠link "prev" "next".

Definition xdeque٠iter_aux : val :=
  𝗿𝗲𝗰 "iter_aux" "fn" "t" "node" ->
    𝗶𝗳 "node" == "t" 𝘁𝗵𝗲𝗻 (
      ()
    ) 𝗲𝗹𝘀𝗲 (
      "fn" "node" ⍮
      "iter_aux" "fn" "t" "node".{xdeque٠next}
    ).

Definition xdeque٠iter : val :=
  𝗳𝘂𝗻 "fn" "t" ->
    xdeque٠iter_aux "fn" "t" "t".{xdeque٠next}.
