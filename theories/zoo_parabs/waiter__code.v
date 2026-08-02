Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.condition.
Require Import zoo_std.mutex.
Require Import zoo.options.

Notation "'waiter٠mutex'" := (
  in_type "zoo_parabs.waiter.t" 0
)(in custom zoo_field
).
Notation "'waiter٠condition'" := (
  in_type "zoo_parabs.waiter.t" 1
)(in custom zoo_field
).
Notation "'waiter٠flag'" := (
  in_type "zoo_parabs.waiter.t" 2
)(in custom zoo_field
).

Definition waiter٠create : val :=
  𝗳𝘂𝗻 ⎽ ->
    { mutex٠create (), condition٠create (), false }.

Definition waiter٠notify : val :=
  𝗳𝘂𝗻 "t" ->
    mutex٠lock "t".{waiter٠mutex} ⍮
    𝗶𝗳 "t".{waiter٠flag} 𝘁𝗵𝗲𝗻 (
      mutex٠unlock "t".{waiter٠mutex} ⍮
      false
    ) 𝗲𝗹𝘀𝗲 (
      "t" <-{waiter٠flag} true ⍮
      mutex٠unlock "t".{waiter٠mutex} ⍮
      condition٠notify "t".{waiter٠condition} ⍮
      true
    ).

Definition waiter٠prepare_wait : val :=
  𝗳𝘂𝗻 "t" ->
    mutex٠protect "t".{waiter٠mutex}
      (𝗳𝘂𝗻 ⎽ -> "t" <-{waiter٠flag} false).

Definition waiter٠cancel_wait : val :=
  𝗳𝘂𝗻 "t" ->
    mutex٠protect "t".{waiter٠mutex}
      (𝗳𝘂𝗻 ⎽ ->
         𝗶𝗳 "t".{waiter٠flag} 𝘁𝗵𝗲𝗻 (
           false
         ) 𝗲𝗹𝘀𝗲 (
           "t" <-{waiter٠flag} true ⍮
           true
         )).

Definition waiter٠commit_wait : val :=
  𝗳𝘂𝗻 "t" ->
    mutex٠protect "t".{waiter٠mutex}
      (𝗳𝘂𝗻 ⎽ ->
         condition٠wait_until
           "t".{waiter٠condition}
           "t".{waiter٠mutex}
           (𝗳𝘂𝗻 ⎽ -> "t".{waiter٠flag})).
