Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_saturn.ws_bdeque_1.
Require Import zoo_saturn.ws_bdeque_2__types.
Require Import zoo.options.

Definition ws_bdeque_2٠create : val :=
  ws_bdeque_1٠create.

Definition ws_bdeque_2٠capacity : val :=
  ws_bdeque_1٠capacity.

Definition ws_bdeque_2٠size : val :=
  ws_bdeque_1٠size.

Definition ws_bdeque_2٠is_empty : val :=
  ws_bdeque_1٠is_empty.

Definition ws_bdeque_2٠push : val :=
  𝗳𝘂𝗻 "t" "v" ->
    ws_bdeque_1٠push "t" (𝗿𝗲𝗳 "v").

Definition ws_bdeque_2٠steal : val :=
  𝗳𝘂𝗻 "t" ->
    𝗺𝗮𝘁𝗰𝗵 ws_bdeque_1٠steal "t" 𝘄𝗶𝘁𝗵
    | None ->
        §None
    | Some "slot" ->
        𝗹𝗲𝘁 "v" = !"slot" 𝗶𝗻
        "slot" <- () ⍮
        ‘Some( "v" )
    𝗲𝗻𝗱.

Definition ws_bdeque_2٠pop : val :=
  𝗳𝘂𝗻 "t" ->
    𝗺𝗮𝘁𝗰𝗵 ws_bdeque_1٠pop "t" 𝘄𝗶𝘁𝗵
    | None ->
        §None
    | Some "slot" ->
        𝗹𝗲𝘁 "v" = !"slot" 𝗶𝗻
        "slot" <- () ⍮
        ‘Some( "v" )
    𝗲𝗻𝗱.
