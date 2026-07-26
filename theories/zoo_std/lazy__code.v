Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.mutex.
Require Import zoo_std.lazy__types.
Require Import zoo.options.

Definition lazy٠make : val :=
  𝗳𝘂𝗻 "fn" ->
    𝗿𝗲𝗳 ‘Unset( "fn" ).

Definition lazy٠return : val :=
  𝗳𝘂𝗻 "res" ->
    𝗿𝗲𝗳 ‘Set( "res" ).

Definition lazy٠is_set : val :=
  𝗳𝘂𝗻 "t" ->
    𝗺𝗮𝘁𝗰𝗵 !"t" 𝘄𝗶𝘁𝗵
    | Set ⎽ ->
        true
    | ⎽ ->
        false
    𝗲𝗻𝗱.

Definition lazy٠is_unset : val :=
  𝗳𝘂𝗻 "t" ->
    ~ lazy٠is_set "t".

Definition lazy٠get : val :=
  𝗿𝗲𝗰 "get" "t" ->
    𝗺𝗮𝘁𝗰𝗵 !"t" 𝘄𝗶𝘁𝗵
    | Set "res" ->
        "res"
    | Setting "mtx" ->
        mutex٠synchronize "mtx" ⍮
        "get" "t"
    | Unset "fn" 𝗮𝘀 "state" ->
        𝗹𝗲𝘁 "mtx" = mutex٠create_lock () 𝗶𝗻
        𝗶𝗳
          𝗰𝗮𝘀 "t".[contents] "state" ‘Setting( "mtx" )
        𝘁𝗵𝗲𝗻 (
          𝗹𝗲𝘁 "res" = "fn" () 𝗶𝗻
          "t" <- ‘Set( "res" ) ⍮
          mutex٠unlock "mtx" ⍮
          "res"
        ) 𝗲𝗹𝘀𝗲 (
          mutex٠unlock "mtx" ⍮
          "get" "t"
        )
    𝗲𝗻𝗱.
