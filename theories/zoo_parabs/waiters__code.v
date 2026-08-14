Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_parabs.waiter.
Require Import zoo_saturn.queue_mpmc_1.
Require Import zoo_std.array.
Require Import zoo.options.

Notation "'waiters٠waiters'" := (
  in_type "zoo_parabs.waiters.t" 0
)(in custom zoo_proj
).
Notation "'waiters٠queue'" := (
  in_type "zoo_parabs.waiters.t" 1
)(in custom zoo_proj
).

Definition waiters٠create : val :=
  𝗳𝘂𝗻 "sz" ->
    (array٠unsafe_init "sz" waiter٠create, queue_mpmc_1٠create ()).

Definition waiters٠notify : val :=
  𝗳𝘂𝗻 "t" "i" ->
    𝗹𝗲𝘁 "waiter" =
      array٠unsafe_get "t".<waiters٠waiters> "i"
    𝗶𝗻
    waiter٠notify "waiter" ⍮
    ().

Definition waiters٠notify_one : val :=
  𝗿𝗲𝗰 "notify_one" "t" ->
    𝗺𝗮𝘁𝗰𝗵
      queue_mpmc_1٠pop "t".<waiters٠queue>
    𝘄𝗶𝘁𝗵
    | None ->
        ()
    | Some "waiter" ->
        𝗶𝗳 ~ waiter٠notify "waiter" 𝘁𝗵𝗲𝗻 (
          "notify_one" "t"
        )
    𝗲𝗻𝗱.

Definition waiters٠notify_all : val :=
  𝗿𝗲𝗰 "notify_all" "t" ->
    𝗺𝗮𝘁𝗰𝗵
      queue_mpmc_1٠pop "t".<waiters٠queue>
    𝘄𝗶𝘁𝗵
    | None ->
        ()
    | Some "waiter" ->
        waiter٠notify "waiter" ⍮
        "notify_all" "t"
    𝗲𝗻𝗱.

Definition waiters٠prepare_wait : val :=
  𝗳𝘂𝗻 "t" "i" ->
    𝗹𝗲𝘁 "waiter" =
      array٠unsafe_get "t".<waiters٠waiters> "i"
    𝗶𝗻
    waiter٠prepare_wait "waiter" ⍮
    queue_mpmc_1٠push "t".<waiters٠queue> "waiter".

Definition waiters٠cancel_wait : val :=
  𝗳𝘂𝗻 "t" "i" ->
    𝗹𝗲𝘁 "waiter" =
      array٠unsafe_get "t".<waiters٠waiters> "i"
    𝗶𝗻
    waiter٠cancel_wait "waiter".

Definition waiters٠commit_wait : val :=
  𝗳𝘂𝗻 "t" "i" ->
    𝗹𝗲𝘁 "waiter" =
      array٠unsafe_get "t".<waiters٠waiters> "i"
    𝗶𝗻
    waiter٠commit_wait "waiter".
