Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.condition.
Require Import zoo_std.mutex.
Require Import zoo.options.

Notation "'mpsc_waiter٠mutex'" := (
  in_type "zoo_std.mpsc_waiter.t" 0
)(in custom zoo_field
).
Notation "'mpsc_waiter٠condition'" := (
  in_type "zoo_std.mpsc_waiter.t" 1
)(in custom zoo_field
).
Notation "'mpsc_waiter٠flag'" := (
  in_type "zoo_std.mpsc_waiter.t" 2
)(in custom zoo_field
).

Definition mpsc_waiter٠create : val :=
  𝗳𝘂𝗻 ⎽ ->
    { mutex٠create (), condition٠create (), false }.

Definition mpsc_waiter٠notify : val :=
  𝗳𝘂𝗻 "t" ->
    𝗶𝗳 "t".{mpsc_waiter٠flag} 𝘁𝗵𝗲𝗻 (
      true
    ) 𝗲𝗹𝘀𝗲 (
      𝗹𝗲𝘁 "res" =
        mutex٠protect "t".{mpsc_waiter٠mutex}
          (𝗳𝘂𝗻 ⎽ ->
             𝗶𝗳 "t".{mpsc_waiter٠flag} 𝘁𝗵𝗲𝗻 (
               true
             ) 𝗲𝗹𝘀𝗲 (
               "t" <-{mpsc_waiter٠flag} true ⍮
               false
             ))
      𝗶𝗻
      condition٠notify "t".{mpsc_waiter٠condition} ⍮
      "res"
    ).

Definition mpsc_waiter٠try_wait : val :=
  𝗳𝘂𝗻 "t" ->
    "t".{mpsc_waiter٠flag}.

Definition mpsc_waiter٠wait : val :=
  𝗳𝘂𝗻 "t" ->
    𝗶𝗳 ~ mpsc_waiter٠try_wait "t" 𝘁𝗵𝗲𝗻 (
      𝗹𝗲𝘁 "mtx" = "t".{mpsc_waiter٠mutex} 𝗶𝗻
      𝗹𝗲𝘁 "cond" = "t".{mpsc_waiter٠condition} 𝗶𝗻
      mutex٠protect "mtx"
        (𝗳𝘂𝗻 ⎽ ->
           condition٠wait_until
             "cond"
             "mtx"
             (𝗳𝘂𝗻 ⎽ -> "t".{mpsc_waiter٠flag}))
    ).
