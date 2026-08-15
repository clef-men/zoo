Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import backoff.backoff.
Require Import zoo.program_logic.identifier.
Require Import zoo_std.inf_array.
Require Import zoo.options.

Notation "'inf_ws_deque_1٠front'" := (
  in_type "zoo_saturn.inf_ws_deque_1.t" 0
)(in custom zoo_field
).
Notation "'inf_ws_deque_1٠back'" := (
  in_type "zoo_saturn.inf_ws_deque_1.t" 1
)(in custom zoo_field
).
Notation "'inf_ws_deque_1٠data'" := (
  in_type "zoo_saturn.inf_ws_deque_1.t" 2
)(in custom zoo_field
).
Notation "'inf_ws_deque_1٠proph'" := (
  in_type "zoo_saturn.inf_ws_deque_1.t" 3
)(in custom zoo_field
).

Definition inf_ws_deque_1٠create : val :=
  𝗳𝘂𝗻 ⎽ ->
    { 1, 1, inf_array٠create (), 𝗽𝗿𝗼𝗽𝗵 }.

Definition inf_ws_deque_1٠size : val :=
  𝗳𝘂𝗻 "t" ->
    "t".{inf_ws_deque_1٠back} - "t".{inf_ws_deque_1٠front}.

Definition inf_ws_deque_1٠is_empty : val :=
  𝗳𝘂𝗻 "t" ->
    inf_ws_deque_1٠size "t" == 0.

Definition inf_ws_deque_1٠push : val :=
  𝗳𝘂𝗻 "t" "v" ->
    𝗹𝗲𝘁 "back" = "t".{inf_ws_deque_1٠back} 𝗶𝗻
    inf_array٠set "t".{inf_ws_deque_1٠data} "back" "v" ⍮
    "t" <-{inf_ws_deque_1٠back} "back" + 1.

Definition inf_ws_deque_1٠steal₁ : val :=
  𝗿𝗲𝗰 "steal" "t" "backoff" ->
    𝗹𝗲𝘁 "id" = 𝗶𝗱 𝗶𝗻
    𝗹𝗲𝘁 "front" = "t".{inf_ws_deque_1٠front} 𝗶𝗻
    𝗹𝗲𝘁 "back" = "t".{inf_ws_deque_1٠back} 𝗶𝗻
    𝗶𝗳 "back" ≤ "front" 𝘁𝗵𝗲𝗻 (
      §None
    ) 𝗲𝗹𝘀𝗲 𝗶𝗳
       𝗿𝗲𝘀𝗼𝗹𝘃𝗲
         (𝗰𝗮𝘀 "t".[inf_ws_deque_1٠front] "front" ("front" + 1))
         "t".{inf_ws_deque_1٠proph}
         ("front", "id")
     𝘁𝗵𝗲𝗻 (
      ‘Some( inf_array٠get "t".{inf_ws_deque_1٠data} "front" )
    ) 𝗲𝗹𝘀𝗲 (
      "steal" "t" (backoff٠once "backoff")
    ).

Definition inf_ws_deque_1٠steal : val :=
  𝗳𝘂𝗻 "t" ->
    inf_ws_deque_1٠steal₁ "t" backoff٠default.

Definition inf_ws_deque_1٠pop₁ : val :=
  𝗳𝘂𝗻 "t" "id" "back" ->
    𝗹𝗲𝘁 "front" = "t".{inf_ws_deque_1٠front} 𝗶𝗻
    𝗶𝗳 "back" < "front" 𝘁𝗵𝗲𝗻 (
      "t" <-{inf_ws_deque_1٠back} "front" ⍮
      §None
    ) 𝗲𝗹𝘀𝗲 𝗶𝗳 "front" < "back" 𝘁𝗵𝗲𝗻 (
      ‘Some( inf_array٠get "t".{inf_ws_deque_1٠data} "back" )
    ) 𝗲𝗹𝘀𝗲 (
      𝗹𝗲𝘁 "won" =
        𝗿𝗲𝘀𝗼𝗹𝘃𝗲
          (𝗰𝗮𝘀 "t".[inf_ws_deque_1٠front] "front" ("front" + 1))
          "t".{inf_ws_deque_1٠proph}
          ("front", "id")
      𝗶𝗻
      "t" <-{inf_ws_deque_1٠back} "front" + 1 ⍮
      𝗶𝗳 "won" 𝘁𝗵𝗲𝗻 (
        ‘Some( inf_array٠get "t".{inf_ws_deque_1٠data} "front" )
      ) 𝗲𝗹𝘀𝗲 (
        §None
      )
    ).

Definition inf_ws_deque_1٠pop : val :=
  𝗳𝘂𝗻 "t" ->
    𝗹𝗲𝘁 "id" = 𝗶𝗱 𝗶𝗻
    𝗹𝗲𝘁 "back" = "t".{inf_ws_deque_1٠back} - 1 𝗶𝗻
    "t" <-{inf_ws_deque_1٠back} "back" ⍮
    inf_ws_deque_1٠pop₁ "t" "id" "back".
