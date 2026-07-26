Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.condition.
Require Import zoo_std.mutex.
Require Import zoo_std.mpsc_waiter__types.
Require Import zoo.options.

Definition mpsc_waiter٠create : val :=
  𝗳𝘂𝗻 ⎽ ->
    { mutex٠create (), condition٠create (), false }.

Definition mpsc_waiter٠notify : val :=
  𝗳𝘂𝗻 "t" ->
    𝗶𝗳 "t".{flag} 𝘁𝗵𝗲𝗻 (
      true
    ) 𝗲𝗹𝘀𝗲 (
      𝗹𝗲𝘁 "res" =
        mutex٠protect "t".{mutex}
          (𝗳𝘂𝗻 ⎽ ->
             𝗶𝗳 "t".{flag} 𝘁𝗵𝗲𝗻 (
               true
             ) 𝗲𝗹𝘀𝗲 (
               "t" <-{flag} true ⍮
               false
             ))
      𝗶𝗻
      condition٠notify "t".{condition} ⍮
      "res"
    ).

Definition mpsc_waiter٠try_wait : val :=
  𝗳𝘂𝗻 "t" ->
    "t".{flag}.

Definition mpsc_waiter٠wait : val :=
  𝗳𝘂𝗻 "t" ->
    𝗶𝗳 ~ mpsc_waiter٠try_wait "t" 𝘁𝗵𝗲𝗻 (
      𝗹𝗲𝘁 "mtx" = "t".{mutex} 𝗶𝗻
      𝗹𝗲𝘁 "cond" = "t".{condition} 𝗶𝗻
      mutex٠protect "mtx"
        (𝗳𝘂𝗻 ⎽ ->
           condition٠wait_until
             "cond"
             "mtx"
             (𝗳𝘂𝗻 ⎽ -> "t".{flag}))
    ).
