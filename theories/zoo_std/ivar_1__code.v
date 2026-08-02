Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo.options.

Definition ivar_1٠create : val :=
  𝗳𝘂𝗻 ⎽ ->
    𝗿𝗲𝗳 §None.

Definition ivar_1٠make : val :=
  𝗳𝘂𝗻 "v" ->
    𝗿𝗲𝗳 ‘Some( "v" ).

Definition ivar_1٠try_get : val :=
  𝗳𝘂𝗻 "t" ->
    !"t".

Definition ivar_1٠is_unset : val :=
  𝗳𝘂𝗻 "t" ->
    ivar_1٠try_get "t" == §None.

Definition ivar_1٠is_set : val :=
  𝗳𝘂𝗻 "t" ->
    ~ ivar_1٠is_unset "t".

Definition ivar_1٠get : val :=
  𝗳𝘂𝗻 "t" ->
    𝗺𝗮𝘁𝗰𝗵 ivar_1٠try_get "t" 𝘄𝗶𝘁𝗵
    | None ->
        𝗳𝗮𝗶𝗹
    | Some "v" ->
        "v"
    𝗲𝗻𝗱.

Definition ivar_1٠set : val :=
  𝗳𝘂𝗻 "t" "v" ->
    "t" <- ‘Some( "v" ).
