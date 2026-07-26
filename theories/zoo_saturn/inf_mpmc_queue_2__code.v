Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.inf_array.
Require Import zoo_std.int.
Require Import zoo_std.optional.
Require Import zoo_std.domain.
Require Import zoo.program_logic.identifier.
Require Import zoo_saturn.inf_mpmc_queue_2__types.
Require Import zoo.options.

Definition inf_mpmc_queue_2٠create : val :=
  𝗳𝘂𝗻 ⎽ ->
    { inf_array٠create §Nothing, 0, 0, 𝗽𝗿𝗼𝗽𝗵 }.

Definition inf_mpmc_queue_2٠size : val :=
  𝗿𝗲𝗰 "size" "t" ->
    𝗹𝗲𝘁 "front" = "t".{front} 𝗶𝗻
    𝗹𝗲𝘁 "proph" = 𝗽𝗿𝗼𝗽𝗵 𝗶𝗻
    𝗹𝗲𝘁 "back" = "t".{back} 𝗶𝗻
    𝗶𝗳
      (𝗹𝗲𝘁 "@tmp" = "t".{front} 𝗶𝗻
       𝗿𝗲𝘀𝗼𝗹𝘃𝗲 𝘀𝗸𝗶𝗽 "proph" "@tmp" ⍮
       "@tmp")
      ==
      "front"
    𝘁𝗵𝗲𝗻 (
      int٠positive_part ("back" - "front")
    ) 𝗲𝗹𝘀𝗲 (
      "size" "t"
    ).

Definition inf_mpmc_queue_2٠is_empty : val :=
  𝗳𝘂𝗻 "t" ->
    inf_mpmc_queue_2٠size "t" == 0.

Definition inf_mpmc_queue_2٠push : val :=
  𝗿𝗲𝗰 "push" "t" "v" ->
    𝗹𝗲𝘁 "id" = 𝗶𝗱 𝗶𝗻
    𝗹𝗲𝘁 "i" = 𝗳𝗮𝗮 "t".[back] 1 𝗶𝗻
    𝗶𝗳
      ~
      inf_array٠cas_resolve
        "t".{data}
        "i"
        §Nothing
        ‘Something( "v" )
        "t".{proph}
        ("i", "id")
    𝘁𝗵𝗲𝗻 (
      "push" "t" "v"
    ).

Definition inf_mpmc_queue_2٠pop : val :=
  𝗿𝗲𝗰 "pop" "t" ->
    𝗹𝗲𝘁 "id" = 𝗶𝗱 𝗶𝗻
    𝗹𝗲𝘁 "i" = 𝗳𝗮𝗮 "t".[front] 1 𝗶𝗻
    𝗺𝗮𝘁𝗰𝗵
      inf_array٠xchg_resolve
        "t".{data}
        "i"
        §Anything
        "t".{proph}
        ("i", "id")
    𝘄𝗶𝘁𝗵
    | Nothing ->
        domain٠yield () ⍮
        "pop" "t"
    | Anything ->
        𝗳𝗮𝗶𝗹
    | Something "v" ->
        "v"
    𝗲𝗻𝗱.
