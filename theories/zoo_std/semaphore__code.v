Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.condition.
Require Import zoo_std.mutex.
Require Import zoo_std.semaphore__types.
Require Import zoo.options.

Definition semaphore٠create : val :=
  𝗳𝘂𝗻 "cap" ->
    { mutex٠create (), condition٠create (), "cap" - 1 }.

Definition semaphore٠try_lock : val :=
  𝗳𝘂𝗻 "t" ->
    mutex٠protect "t".{mutex}
      (𝗳𝘂𝗻 ⎽ ->
         𝗹𝗲𝘁 "cnt" = "t".{count} 𝗶𝗻
         𝗶𝗳 0 < "cnt" 𝘁𝗵𝗲𝗻 (
           "t" <-{count} "cnt" - 1 ⍮
           true
         ) 𝗲𝗹𝘀𝗲 (
           false
         )).

Definition semaphore٠lock : val :=
  𝗳𝘂𝗻 "t" ->
    mutex٠protect "t".{mutex}
      (𝗳𝘂𝗻 ⎽ ->
         condition٠wait_until
           "t".{condition}
           "t".{mutex}
           (𝗳𝘂𝗻 ⎽ -> 0 < "t".{count}) ⍮
         "t" <-{count} "t".{count} - 1).

Definition semaphore٠unlock : val :=
  𝗳𝘂𝗻 "t" ->
    mutex٠protect
      "t".{mutex}
      (𝗳𝘂𝗻 ⎽ -> "t" <-{count} "t".{count} + 1) ⍮
    condition٠notify "t".{condition}.
