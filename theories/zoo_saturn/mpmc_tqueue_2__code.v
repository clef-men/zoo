Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.atomic_array.
Require Import zoo_std.optional.
Require Import zoo_saturn.mpmc_tqueue_2__types.
Require Import zoo.options.

Definition mpmc_tqueue_2٠create : val :=
  𝗳𝘂𝗻 "cap" ->
    𝗹𝗲𝘁 "data" = atomic_array٠make "cap" §Nothing 𝗶𝗻
    { "cap", "data", 0, 0 }.

Definition mpmc_tqueue_2٠make : val :=
  𝗳𝘂𝗻 "cap" "v" ->
    𝗹𝗲𝘁 "data" = atomic_array٠make "cap" §Nothing 𝗶𝗻
    atomic_array٠unsafe_set "data" 0 ‘Something( "v" ) ⍮
    { "cap", "data", 0, 1 }.

Definition mpmc_tqueue_2٠is_empty : val :=
  𝗳𝘂𝗻 "t" ->
    𝗹𝗲𝘁 "front" = "t".{front} 𝗶𝗻
    𝗹𝗲𝘁 "back" = "t".{back} 𝗶𝗻
    "back" ≤ "front".

Definition mpmc_tqueue_2٠push₁ : val :=
  𝗿𝗲𝗰 "push" "t" "v" ->
    𝗹𝗲𝘁 "i" = 𝗳𝗮𝗮 "t".[back] 1 𝗶𝗻
    𝗶𝗳 "t".{capacity} ≤ "i" 𝘁𝗵𝗲𝗻 (
      false
    ) 𝗲𝗹𝘀𝗲 𝗶𝗳
       atomic_array٠unsafe_cas "t".{data} "i" §Nothing ‘Something( "v" )
     𝘁𝗵𝗲𝗻 (
      true
    ) 𝗲𝗹𝘀𝗲 (
      "push" "t" "v"
    ).

Definition mpmc_tqueue_2٠push : val :=
  𝗳𝘂𝗻 "t" "v" ->
    𝗶𝗳 "t".{capacity} ≤ "t".{back} 𝘁𝗵𝗲𝗻 (
      false
    ) 𝗲𝗹𝘀𝗲 (
      mpmc_tqueue_2٠push₁ "t" "v"
    ).

Definition mpmc_tqueue_2٠pop : val :=
  𝗳𝘂𝗻 "t" ->
    𝗶𝗳 "t".{capacity} ≤ "t".{front} 𝘁𝗵𝗲𝗻 (
      §Anything
    ) 𝗲𝗹𝘀𝗲 (
      𝗹𝗲𝘁 "i" = 𝗳𝗮𝗮 "t".[front] 1 𝗶𝗻
      𝗶𝗳 "t".{capacity} ≤ "i" 𝘁𝗵𝗲𝗻 (
        §Anything
      ) 𝗲𝗹𝘀𝗲 (
        atomic_array٠unsafe_xchg "t".{data} "i" §Anything
      )
    ).
