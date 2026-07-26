Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.condition.
Require Import zoo_std.mutex.
Require Import zoo_std.spsc_waiter__types.
Require Import zoo.options.

Definition spsc_waiter٠create : val :=
  𝗳𝘂𝗻 ⎽ ->
    { mutex٠create (), condition٠create (), false }.

Definition spsc_waiter٠notify : val :=
  𝗳𝘂𝗻 "t" ->
    mutex٠protect "t".{mutex} (𝗳𝘂𝗻 ⎽ -> "t" <-{flag} true) ⍮
    condition٠notify "t".{condition}.

Definition spsc_waiter٠try_wait : val :=
  𝗳𝘂𝗻 "t" ->
    "t".{flag}.

Definition spsc_waiter٠wait : val :=
  𝗳𝘂𝗻 "t" ->
    𝗶𝗳 ~ spsc_waiter٠try_wait "t" 𝘁𝗵𝗲𝗻 (
      𝗹𝗲𝘁 "mtx" = "t".{mutex} 𝗶𝗻
      𝗹𝗲𝘁 "cond" = "t".{condition} 𝗶𝗻
      mutex٠protect "mtx"
        (𝗳𝘂𝗻 ⎽ ->
           condition٠wait_until
             "cond"
             "mtx"
             (𝗳𝘂𝗻 ⎽ -> "t".{flag}))
    ).
