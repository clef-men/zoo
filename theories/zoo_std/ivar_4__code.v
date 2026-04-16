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

Definition ivar_4_create : val :=
  ivar_3_create.

Definition ivar_4_make : val :=
  ivar_3_make.

Definition ivar_4_is_unset : val :=
  ivar_3_is_unset.

Definition ivar_4_is_set : val :=
  ivar_3_is_set.

Definition ivar_4_try_get : val :=
  ivar_3_try_get.

Definition ivar_4_get : val :=
  ivar_3_get.

Definition ivar_4_wait : val :=
  ivar_3_wait.

Definition ivar_4_set : val :=
  ivar_3_set.

Definition ivar_4_notify : val :=
  fun: "t" "ctx" "v" =>
    let: "waiters" := ivar_4_set "t" "v" in
    lst_iter (fun: "waiter" => "waiter" "ctx" "v") "waiters".
