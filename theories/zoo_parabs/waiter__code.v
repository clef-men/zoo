Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.condition.
Require Import zoo_std.mutex.
Require Import zoo_parabs.waiter__types.
Require Import zoo.options.

Definition waiter٠create : val :=
  𝗳𝘂𝗻 ⎽ ->
    { mutex٠create (), condition٠create (), false }.

Definition waiter٠notify : val :=
  𝗳𝘂𝗻 "t" ->
    mutex٠lock "t".{mutex} ⍮
    𝗶𝗳 "t".{flag} 𝘁𝗵𝗲𝗻 (
      mutex٠unlock "t".{mutex} ⍮
      false
    ) 𝗲𝗹𝘀𝗲 (
      "t" <-{flag} true ⍮
      mutex٠unlock "t".{mutex} ⍮
      condition٠notify "t".{condition} ⍮
      true
    ).

Definition waiter٠prepare_wait : val :=
  𝗳𝘂𝗻 "t" ->
    mutex٠protect "t".{mutex} (𝗳𝘂𝗻 ⎽ -> "t" <-{flag} false).

Definition waiter٠cancel_wait : val :=
  𝗳𝘂𝗻 "t" ->
    mutex٠protect "t".{mutex}
      (𝗳𝘂𝗻 ⎽ ->
         𝗶𝗳 "t".{flag} 𝘁𝗵𝗲𝗻 (
           false
         ) 𝗲𝗹𝘀𝗲 (
           "t" <-{flag} true ⍮
           true
         )).

Definition waiter٠commit_wait : val :=
  𝗳𝘂𝗻 "t" ->
    mutex٠protect "t".{mutex}
      (𝗳𝘂𝗻 ⎽ ->
         condition٠wait_until
           "t".{condition}
           "t".{mutex}
           (𝗳𝘂𝗻 ⎽ -> "t".{flag})).
