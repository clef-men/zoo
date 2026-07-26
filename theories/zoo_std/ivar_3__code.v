Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.ivar_3__types.
Require Import zoo.options.

Definition ivar_3٠create : val :=
  𝗳𝘂𝗻 ⎽ ->
    𝗿𝗲𝗳 ‘Unset[ [] ].

Definition ivar_3٠make : val :=
  𝗳𝘂𝗻 "v" ->
    𝗿𝗲𝗳 ‘Set( "v" ).

Definition ivar_3٠is_unset : val :=
  𝗳𝘂𝗻 "t" ->
    𝗺𝗮𝘁𝗰𝗵 !"t" 𝘄𝗶𝘁𝗵
    | Unset ⎽ ->
        true
    | Set ⎽ ->
        false
    𝗲𝗻𝗱.

Definition ivar_3٠is_set : val :=
  𝗳𝘂𝗻 "t" ->
    ~ ivar_3٠is_unset "t".

Definition ivar_3٠try_get : val :=
  𝗳𝘂𝗻 "t" ->
    𝗺𝗮𝘁𝗰𝗵 !"t" 𝘄𝗶𝘁𝗵
    | Unset ⎽ ->
        §None
    | Set "v" ->
        ‘Some( "v" )
    𝗲𝗻𝗱.

Definition ivar_3٠get : val :=
  𝗳𝘂𝗻 "t" ->
    𝗺𝗮𝘁𝗰𝗵 !"t" 𝘄𝗶𝘁𝗵
    | Unset ⎽ ->
        𝗳𝗮𝗶𝗹
    | Set "v" ->
        "v"
    𝗲𝗻𝗱.

Definition ivar_3٠wait : val :=
  𝗿𝗲𝗰 "wait" "t" "waiter" ->
    𝗺𝗮𝘁𝗰𝗵 !"t" 𝘄𝗶𝘁𝗵
    | Unset "waiters" 𝗮𝘀 "state" ->
        𝗶𝗳
          𝗰𝗮𝘀
            "t".[contents]
            "state"
            ‘Unset[ "waiter" :: "waiters" ]
        𝘁𝗵𝗲𝗻 (
          §None
        ) 𝗲𝗹𝘀𝗲 (
          "wait" "t" "waiter"
        )
    | Set "v" ->
        ‘Some( "v" )
    𝗲𝗻𝗱.

Definition ivar_3٠set : val :=
  𝗳𝘂𝗻 "t" "v" ->
    𝗺𝗮𝘁𝗰𝗵
      𝘅𝗰𝗵𝗴 "t".[contents] ‘Set( "v" )
    𝘄𝗶𝘁𝗵
    | Set ⎽ ->
        𝗳𝗮𝗶𝗹
    | Unset "waiters" ->
        "waiters"
    𝗲𝗻𝗱.
