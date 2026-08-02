Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.condition.
Require Import zoo_std.mutex.
Require Import zoo.options.

Notation "'spsc_waiter٠mutex'" := (
  in_type "zoo_std.spsc_waiter.t" 0
)(in custom zoo_field
).
Notation "'spsc_waiter٠condition'" := (
  in_type "zoo_std.spsc_waiter.t" 1
)(in custom zoo_field
).
Notation "'spsc_waiter٠flag'" := (
  in_type "zoo_std.spsc_waiter.t" 2
)(in custom zoo_field
).

Definition spsc_waiter٠create : val :=
  𝗳𝘂𝗻 ⎽ ->
    { mutex٠create (), condition٠create (), false }.

Definition spsc_waiter٠notify : val :=
  𝗳𝘂𝗻 "t" ->
    mutex٠protect
      "t".{spsc_waiter٠mutex}
      (𝗳𝘂𝗻 ⎽ -> "t" <-{spsc_waiter٠flag} true) ⍮
    condition٠notify "t".{spsc_waiter٠condition}.

Definition spsc_waiter٠try_wait : val :=
  𝗳𝘂𝗻 "t" ->
    "t".{spsc_waiter٠flag}.

Definition spsc_waiter٠wait : val :=
  𝗳𝘂𝗻 "t" ->
    𝗶𝗳 ~ spsc_waiter٠try_wait "t" 𝘁𝗵𝗲𝗻 (
      𝗹𝗲𝘁 "mtx" = "t".{spsc_waiter٠mutex} 𝗶𝗻
      𝗹𝗲𝘁 "cond" = "t".{spsc_waiter٠condition} 𝗶𝗻
      mutex٠protect "mtx"
        (𝗳𝘂𝗻 ⎽ ->
           condition٠wait_until
             "cond"
             "mtx"
             (𝗳𝘂𝗻 ⎽ -> "t".{spsc_waiter٠flag}))
    ).
