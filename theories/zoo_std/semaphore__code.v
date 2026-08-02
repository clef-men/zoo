Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.condition.
Require Import zoo_std.mutex.
Require Import zoo.options.

Notation "'semaphore٠mutex'" := (
  in_type "zoo_std.semaphore.t" 0
)(in custom zoo_field
).
Notation "'semaphore٠condition'" := (
  in_type "zoo_std.semaphore.t" 1
)(in custom zoo_field
).
Notation "'semaphore٠count'" := (
  in_type "zoo_std.semaphore.t" 2
)(in custom zoo_field
).

Definition semaphore٠create : val :=
  𝗳𝘂𝗻 "cap" ->
    { mutex٠create (), condition٠create (), "cap" - 1 }.

Definition semaphore٠try_lock : val :=
  𝗳𝘂𝗻 "t" ->
    mutex٠protect "t".{semaphore٠mutex}
      (𝗳𝘂𝗻 ⎽ ->
         𝗹𝗲𝘁 "cnt" = "t".{semaphore٠count} 𝗶𝗻
         𝗶𝗳 0 < "cnt" 𝘁𝗵𝗲𝗻 (
           "t" <-{semaphore٠count} "cnt" - 1 ⍮
           true
         ) 𝗲𝗹𝘀𝗲 (
           false
         )).

Definition semaphore٠lock : val :=
  𝗳𝘂𝗻 "t" ->
    mutex٠protect "t".{semaphore٠mutex}
      (𝗳𝘂𝗻 ⎽ ->
         condition٠wait_until
           "t".{semaphore٠condition}
           "t".{semaphore٠mutex}
           (𝗳𝘂𝗻 ⎽ -> 0 < "t".{semaphore٠count}) ⍮
         "t" <-{semaphore٠count} "t".{semaphore٠count} - 1).

Definition semaphore٠unlock : val :=
  𝗳𝘂𝗻 "t" ->
    mutex٠protect
      "t".{semaphore٠mutex}
      (𝗳𝘂𝗻 ⎽ ->
         "t" <-{semaphore٠count} "t".{semaphore٠count} + 1) ⍮
    condition٠notify "t".{semaphore٠condition}.
