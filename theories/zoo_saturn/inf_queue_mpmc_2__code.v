Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import backoff.backoff.
Require Import zoo.program_logic.identifier.
Require Import zoo_std.inf_array.
Require Import zoo_std.int.
Require Import zoo_std.optional.
Require Import zoo.options.

Notation "'inf_queue_mpmc_2٠data'" := (
  in_type "zoo_saturn.inf_queue_mpmc_2.t" 0
)(in custom zoo_field
).
Notation "'inf_queue_mpmc_2٠front'" := (
  in_type "zoo_saturn.inf_queue_mpmc_2.t" 1
)(in custom zoo_field
).
Notation "'inf_queue_mpmc_2٠back'" := (
  in_type "zoo_saturn.inf_queue_mpmc_2.t" 2
)(in custom zoo_field
).
Notation "'inf_queue_mpmc_2٠proph'" := (
  in_type "zoo_saturn.inf_queue_mpmc_2.t" 3
)(in custom zoo_field
).

Definition inf_queue_mpmc_2٠create : val :=
  𝗳𝘂𝗻 ⎽ ->
    { inf_array٠create §optional٠Nothing, 0, 0, 𝗽𝗿𝗼𝗽𝗵 }.

Definition inf_queue_mpmc_2٠size : val :=
  𝗿𝗲𝗰 "size" "t" ->
    𝗹𝗲𝘁 "front" = "t".{inf_queue_mpmc_2٠front} 𝗶𝗻
    𝗹𝗲𝘁 "proph" = 𝗽𝗿𝗼𝗽𝗵 𝗶𝗻
    𝗹𝗲𝘁 "back" = "t".{inf_queue_mpmc_2٠back} 𝗶𝗻
    𝗶𝗳
      (𝗹𝗲𝘁 "@tmp" = "t".{inf_queue_mpmc_2٠front} 𝗶𝗻
       𝗿𝗲𝘀𝗼𝗹𝘃𝗲 𝘀𝗸𝗶𝗽 "proph" "@tmp" ⍮
       "@tmp")
      ==
      "front"
    𝘁𝗵𝗲𝗻 (
      int٠positive_part ("back" - "front")
    ) 𝗲𝗹𝘀𝗲 (
      "size" "t"
    ).

Definition inf_queue_mpmc_2٠is_empty : val :=
  𝗳𝘂𝗻 "t" ->
    inf_queue_mpmc_2٠size "t" == 0.

Definition inf_queue_mpmc_2٠push : val :=
  𝗿𝗲𝗰 "push" "t" "v" ->
    𝗹𝗲𝘁 "id" = 𝗶𝗱 𝗶𝗻
    𝗹𝗲𝘁 "i" = 𝗳𝗮𝗮 "t".[inf_queue_mpmc_2٠back] 1 𝗶𝗻
    𝗶𝗳
      ~
      inf_array٠cas_resolve
        "t".{inf_queue_mpmc_2٠data}
        "i"
        §optional٠Nothing
        ‘optional٠Something( "v" )
        "t".{inf_queue_mpmc_2٠proph}
        ("i", "id")
    𝘁𝗵𝗲𝗻 (
      "push" "t" "v"
    ).

Definition inf_queue_mpmc_2٠pop₁ : val :=
  𝗿𝗲𝗰 "pop" "t" "backoff" ->
    𝗹𝗲𝘁 "id" = 𝗶𝗱 𝗶𝗻
    𝗹𝗲𝘁 "i" = 𝗳𝗮𝗮 "t".[inf_queue_mpmc_2٠front] 1 𝗶𝗻
    𝗺𝗮𝘁𝗰𝗵
      inf_array٠xchg_resolve
        "t".{inf_queue_mpmc_2٠data}
        "i"
        §optional٠Anything
        "t".{inf_queue_mpmc_2٠proph}
        ("i", "id")
    𝘄𝗶𝘁𝗵
    | optional٠Nothing ->
        "pop" "t" (backoff٠once "backoff")
    | optional٠Anything ->
        𝗳𝗮𝗶𝗹
    | optional٠Something "v" ->
        "v"
    𝗲𝗻𝗱.

Definition inf_queue_mpmc_2٠pop : val :=
  𝗳𝘂𝗻 "t" ->
    inf_queue_mpmc_2٠pop₁ "t" backoff٠default.
