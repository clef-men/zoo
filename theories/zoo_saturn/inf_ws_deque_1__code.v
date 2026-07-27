Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo.program_logic.identifier.
Require Import zoo_std.domain.
Require Import zoo_std.inf_array.
Require Import zoo_saturn.inf_ws_deque_1__types.
Require Import zoo.options.

Definition inf_ws_deque_1٠create : val :=
  𝗳𝘂𝗻 ⎽ ->
    { 1, 1, inf_array٠create (), 𝗽𝗿𝗼𝗽𝗵 }.

Definition inf_ws_deque_1٠size : val :=
  𝗳𝘂𝗻 "t" ->
    "t".{back} - "t".{front}.

Definition inf_ws_deque_1٠is_empty : val :=
  𝗳𝘂𝗻 "t" ->
    inf_ws_deque_1٠size "t" == 0.

Definition inf_ws_deque_1٠push : val :=
  𝗳𝘂𝗻 "t" "v" ->
    𝗹𝗲𝘁 "back" = "t".{back} 𝗶𝗻
    inf_array٠set "t".{data} "back" "v" ⍮
    "t" <-{back} "back" + 1.

Definition inf_ws_deque_1٠steal : val :=
  𝗿𝗲𝗰 "steal" "t" ->
    𝗹𝗲𝘁 "id" = 𝗶𝗱 𝗶𝗻
    𝗹𝗲𝘁 "front" = "t".{front} 𝗶𝗻
    𝗹𝗲𝘁 "back" = "t".{back} 𝗶𝗻
    𝗶𝗳 "back" ≤ "front" 𝘁𝗵𝗲𝗻 (
      §None
    ) 𝗲𝗹𝘀𝗲 𝗶𝗳
       𝗿𝗲𝘀𝗼𝗹𝘃𝗲
         (𝗰𝗮𝘀 "t".[front] "front" ("front" + 1))
         "t".{proph}
         ("front", "id")
     𝘁𝗵𝗲𝗻 (
      ‘Some( inf_array٠get "t".{data} "front" )
    ) 𝗲𝗹𝘀𝗲 (
      domain٠yield () ⍮
      "steal" "t"
    ).

Definition inf_ws_deque_1٠pop₀ : val :=
  𝗳𝘂𝗻 "t" "id" "back" ->
    𝗹𝗲𝘁 "front" = "t".{front} 𝗶𝗻
    𝗶𝗳 "back" < "front" 𝘁𝗵𝗲𝗻 (
      "t" <-{back} "front" ⍮
      §None
    ) 𝗲𝗹𝘀𝗲 𝗶𝗳 "front" < "back" 𝘁𝗵𝗲𝗻 (
      ‘Some( inf_array٠get "t".{data} "back" )
    ) 𝗲𝗹𝘀𝗲 (
      𝗹𝗲𝘁 "won" =
        𝗿𝗲𝘀𝗼𝗹𝘃𝗲
          (𝗰𝗮𝘀 "t".[front] "front" ("front" + 1))
          "t".{proph}
          ("front", "id")
      𝗶𝗻
      "t" <-{back} "front" + 1 ⍮
      𝗶𝗳 "won" 𝘁𝗵𝗲𝗻 (
        ‘Some( inf_array٠get "t".{data} "front" )
      ) 𝗲𝗹𝘀𝗲 (
        §None
      )
    ).

Definition inf_ws_deque_1٠pop : val :=
  𝗳𝘂𝗻 "t" ->
    𝗹𝗲𝘁 "id" = 𝗶𝗱 𝗶𝗻
    𝗹𝗲𝘁 "back" = "t".{back} - 1 𝗶𝗻
    "t" <-{back} "back" ⍮
    inf_ws_deque_1٠pop₀ "t" "id" "back".
