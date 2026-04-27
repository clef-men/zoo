From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  lst
  ivar_3.
From zoo_std Require Import
  ivar_4__types.
From zoo Require Import
  options.

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
  fun: "t" "ctx" "v" =>
    let: "waiters" := ivar_4٠set "t" "v" in
    lst٠iter (fun: "waiter" => "waiter" "ctx" "v") "waiters".
