Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.domain.
Require Import zoo_std.inf_array.
Require Import zoo_std.int.
Require Import zoo_std.optional.
Require Import zoo_saturn.inf_mpmc_queue_1__types.
Require Import zoo.options.

Definition inf_mpmc_queue_1٠create : val :=
  𝗳𝘂𝗻 ⎽ ->
    { inf_array٠create §Nothing, 0, 0 }.

Definition inf_mpmc_queue_1٠size : val :=
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

Definition inf_mpmc_queue_1٠is_empty : val :=
  𝗳𝘂𝗻 "t" ->
    inf_mpmc_queue_1٠size "t" == 0.

Definition inf_mpmc_queue_1٠is_empty_weak : val :=
  𝗳𝘂𝗻 "t" ->
    𝗹𝗲𝘁 "front" = "t".{front} 𝗶𝗻
    𝗹𝗲𝘁 "back" = "t".{back} 𝗶𝗻
    "back" ≤ "front".

Definition inf_mpmc_queue_1٠push : val :=
  𝗳𝘂𝗻 "t" "v" ->
    𝗹𝗲𝘁 "i" = 𝗳𝗮𝗮 "t".[back] 1 𝗶𝗻
    inf_array٠set "t".{data} "i" ‘Something( "v" ).

Definition inf_mpmc_queue_1٠pop₁ : val :=
  𝗿𝗲𝗰 "pop" "t" "i" ->
    𝗺𝗮𝘁𝗰𝗵 inf_array٠get "t".{data} "i" 𝘄𝗶𝘁𝗵
    | Nothing ->
        domain٠yield () ⍮
        "pop" "t" "i"
    | Anything ->
        𝗳𝗮𝗶𝗹
    | Something "v" ->
        inf_array٠set "t".{data} "i" §Anything ⍮
        "v"
    𝗲𝗻𝗱.

Definition inf_mpmc_queue_1٠pop : val :=
  𝗳𝘂𝗻 "t" ->
    𝗹𝗲𝘁 "i" = 𝗳𝗮𝗮 "t".[front] 1 𝗶𝗻
    inf_mpmc_queue_1٠pop₁ "t" "i".

Definition inf_mpmc_queue_1٠try_pop : val :=
  𝗳𝘂𝗻 "t" ->
    𝗶𝗳 inf_mpmc_queue_1٠is_empty_weak "t" 𝘁𝗵𝗲𝗻 (
      §None
    ) 𝗲𝗹𝘀𝗲 (
      ‘Some( inf_mpmc_queue_1٠pop "t" )
    ).
