Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.chain.
Require Import zoo_std.queue_1__types.
Require Import zoo.options.

Definition queue_1٠create : val :=
  𝗳𝘂𝗻 ⎽ ->
    𝗹𝗲𝘁 "front" = { (), () } 𝗶𝗻
    { "front", "front" }.

Definition queue_1٠is_empty : val :=
  𝗳𝘂𝗻 "t" ->
    "t".{front} == "t".{back}.

Definition queue_1٠push : val :=
  𝗳𝘂𝗻 "t" "v" ->
    𝗹𝗲𝘁 "back" = "t".{back} 𝗶𝗻
    𝗹𝗲𝘁 "new_back" = { (), () } 𝗶𝗻
    "back" <-{chain_next} "new_back" ⍮
    "back" <-{chain_data} "v" ⍮
    "t" <-{back} "new_back".

Definition queue_1٠pop : val :=
  𝗳𝘂𝗻 "t" ->
    𝗶𝗳 queue_1٠is_empty "t" 𝘁𝗵𝗲𝗻 (
      §None
    ) 𝗲𝗹𝘀𝗲 (
      𝗹𝗲𝘁 "front" = "t".{front} 𝗶𝗻
      "t" <-{front} "front".{chain_next} ⍮
      𝗹𝗲𝘁 "v" = "front".{chain_data} 𝗶𝗻
      ‘Some( "v" )
    ).
