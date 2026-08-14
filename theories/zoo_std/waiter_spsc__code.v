Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.condition.
Require Import zoo_std.mutex.
Require Import zoo.options.

Notation "'waiter_spsc٠mutex'" := (
  in_type "zoo_std.waiter_spsc.t" 0
)(in custom zoo_field
).
Notation "'waiter_spsc٠condition'" := (
  in_type "zoo_std.waiter_spsc.t" 1
)(in custom zoo_field
).
Notation "'waiter_spsc٠flag'" := (
  in_type "zoo_std.waiter_spsc.t" 2
)(in custom zoo_field
).

Definition waiter_spsc٠create : val :=
  𝗳𝘂𝗻 ⎽ ->
    { mutex٠create (), condition٠create (), false }.

Definition waiter_spsc٠notify : val :=
  𝗳𝘂𝗻 "t" ->
    mutex٠protect
      "t".{waiter_spsc٠mutex}
      (𝗳𝘂𝗻 ⎽ -> "t" <-{waiter_spsc٠flag} true) ⍮
    condition٠notify "t".{waiter_spsc٠condition}.

Definition waiter_spsc٠try_wait : val :=
  𝗳𝘂𝗻 "t" ->
    "t".{waiter_spsc٠flag}.

Definition waiter_spsc٠wait : val :=
  𝗳𝘂𝗻 "t" ->
    𝗶𝗳 ~ waiter_spsc٠try_wait "t" 𝘁𝗵𝗲𝗻 (
      𝗹𝗲𝘁 "mtx" = "t".{waiter_spsc٠mutex} 𝗶𝗻
      𝗹𝗲𝘁 "cond" = "t".{waiter_spsc٠condition} 𝗶𝗻
      mutex٠protect "mtx"
        (𝗳𝘂𝗻 ⎽ ->
           condition٠wait_until
             "cond"
             "mtx"
             (𝗳𝘂𝗻 ⎽ -> "t".{waiter_spsc٠flag}))
    ).
