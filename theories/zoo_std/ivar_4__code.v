Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.ivar_3.
Require Import zoo_std.list.
Require Import zoo.options.

Definition ivar_4٠create : val :=
  ivar_3٠create.

Definition ivar_4٠make : val :=
  ivar_3٠make.

Definition ivar_4٠is_unset : val :=
  ivar_3٠is_unset.

Definition ivar_4٠is_set : val :=
  ivar_3٠is_set.

Definition ivar_4٠try_get : val :=
  ivar_3٠try_get.

Definition ivar_4٠get : val :=
  ivar_3٠get.

Definition ivar_4٠wait : val :=
  ivar_3٠wait.

Definition ivar_4٠set : val :=
  ivar_3٠set.

Definition ivar_4٠notify : val :=
  𝗳𝘂𝗻 "t" "ctx" "v" ->
    𝗹𝗲𝘁 "waiters" = ivar_4٠set "t" "v" 𝗶𝗻
    list٠iter (𝗳𝘂𝗻 "waiter" -> "waiter" "ctx" "v") "waiters".
