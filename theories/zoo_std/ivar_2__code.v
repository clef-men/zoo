Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.condition.
Require Import zoo_std.mutex.
Require Import zoo_std.ivar_2__types.
Require Import zoo.options.

Definition ivar_2٠create : val :=
  𝗳𝘂𝗻 ⎽ ->
    { mutex٠create (), condition٠create (), §None }.

Definition ivar_2٠make : val :=
  𝗳𝘂𝗻 "v" ->
    { mutex٠create (), condition٠create (), ‘Some( "v" ) }.

Definition ivar_2٠try_get : val :=
  𝗳𝘂𝗻 "t" ->
    "t".{result}.

Definition ivar_2٠is_unset : val :=
  𝗳𝘂𝗻 "t" ->
    ivar_2٠try_get "t" == §None.

Definition ivar_2٠is_set : val :=
  𝗳𝘂𝗻 "t" ->
    ~ ivar_2٠is_unset "t".

Definition ivar_2٠get : val :=
  𝗳𝘂𝗻 "t" ->
    𝗺𝗮𝘁𝗰𝗵 ivar_2٠try_get "t" 𝘄𝗶𝘁𝗵
    | Some "v" ->
        mutex٠synchronize "t".{mutex} ⍮
        "v"
    | None ->
        𝗹𝗲𝘁 "mtx" = "t".{mutex} 𝗶𝗻
        𝗹𝗲𝘁 "cond" = "t".{condition} 𝗶𝗻
        mutex٠protect
          "mtx"
          (𝗳𝘂𝗻 ⎽ ->
             condition٠wait_while
               "cond"
               "mtx"
               (𝗳𝘂𝗻 ⎽ -> "t".{result} == §None)) ⍮
        𝗺𝗮𝘁𝗰𝗵 "t".{result} 𝘄𝗶𝘁𝗵
        | Some "v" ->
            "v"
        | None ->
            𝗳𝗮𝗶𝗹
        𝗲𝗻𝗱
    𝗲𝗻𝗱.

Definition ivar_2٠set : val :=
  𝗳𝘂𝗻 "t" "v" ->
    mutex٠protect
      "t".{mutex}
      (𝗳𝘂𝗻 ⎽ -> "t" <-{result} ‘Some( "v" )) ⍮
    condition٠notify_all "t".{condition}.
