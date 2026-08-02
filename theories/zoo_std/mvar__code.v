Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo.options.

Definition mvar٠create : val :=
  𝗳𝘂𝗻 ⎽ ->
    𝗿𝗲𝗳 §None.

Definition mvar٠make : val :=
  𝗳𝘂𝗻 "v" ->
    𝗿𝗲𝗳 ‘Some( "v" ).

Definition mvar٠try_get : val :=
  𝗳𝘂𝗻 "t" ->
    !"t".

Definition mvar٠is_unset : val :=
  𝗳𝘂𝗻 "t" ->
    mvar٠try_get "t" == §None.

Definition mvar٠is_set : val :=
  𝗳𝘂𝗻 "t" ->
    ~ mvar٠is_unset "t".

Definition mvar٠get : val :=
  𝗳𝘂𝗻 "t" ->
    𝗺𝗮𝘁𝗰𝗵 mvar٠try_get "t" 𝘄𝗶𝘁𝗵
    | None ->
        𝗳𝗮𝗶𝗹
    | Some "v" ->
        "v"
    𝗲𝗻𝗱.

Definition mvar٠set : val :=
  𝗳𝘂𝗻 "t" "v" ->
    "t" <- ‘Some( "v" ).
