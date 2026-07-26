Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_saturn.inf_ws_deque_1.
Require Import zoo_saturn.inf_ws_deque_2__types.
Require Import zoo.options.

Definition inf_ws_deque_2٠create : val :=
  inf_ws_deque_1٠create.

Definition inf_ws_deque_2٠size : val :=
  inf_ws_deque_1٠size.

Definition inf_ws_deque_2٠is_empty : val :=
  inf_ws_deque_1٠is_empty.

Definition inf_ws_deque_2٠push : val :=
  𝗳𝘂𝗻 "t" "v" ->
    inf_ws_deque_1٠push "t" (𝗿𝗲𝗳 "v").

Definition inf_ws_deque_2٠steal : val :=
  𝗳𝘂𝗻 "t" ->
    𝗺𝗮𝘁𝗰𝗵 inf_ws_deque_1٠steal "t" 𝘄𝗶𝘁𝗵
    | None ->
        §None
    | Some "slot" ->
        𝗹𝗲𝘁 "v" = !"slot" 𝗶𝗻
        "slot" <- () ⍮
        ‘Some( "v" )
    𝗲𝗻𝗱.

Definition inf_ws_deque_2٠pop : val :=
  𝗳𝘂𝗻 "t" ->
    𝗺𝗮𝘁𝗰𝗵 inf_ws_deque_1٠pop "t" 𝘄𝗶𝘁𝗵
    | None ->
        §None
    | Some "slot" ->
        𝗹𝗲𝘁 "v" = !"slot" 𝗶𝗻
        "slot" <- () ⍮
        ‘Some( "v" )
    𝗲𝗻𝗱.
