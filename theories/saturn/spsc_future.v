From zebre Require Import
  prelude.
From zebre.language Require Import
  notations.
From zebre.std Require Import
  opt
  condition.
From zebre.saturn Require Export
  base.
From zebre Require Import
  options.

#[local] Notation "'result'" := (
  in_type "t" 0
)(in custom zebre_field
).
#[local] Notation "'mutex'" := (
  in_type "t" 1
)(in custom zebre_field
).
#[local] Notation "'condition'" := (
  in_type "t" 2
)(in custom zebre_field
).

Definition spsc_future_create : val :=
  λ: <>,
    { §None;
      mutex_create ();
      condition_create ()
    }.

Definition spsc_future_set : val :=
  λ: "t" "v",
    "t" <-{result} ‘Some{ "v" } ;;
    condition_signal "t".{condition}.

Definition spsc_future_try_get : val :=
  λ: "t",
    "t".{result}.
Definition spsc_future_get : val :=
  λ: "t",
    match: spsc_future_try_get "t" with
    | Some "v" =>
        "v"
    | None =>
        let: "mtx" := "t".{mutex} in
        let: "cond" := "t".{condition} in
        mutex_protect "mtx" (λ: <>,
          condition_wait_while "cond" "mtx" (λ: <>, "t".{result} = §None)
        )
    end.

#[global] Opaque spsc_future_create.
#[global] Opaque spsc_future_set.
#[global] Opaque spsc_future_try_get.
#[global] Opaque spsc_future_get.
