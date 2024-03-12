From zebre Require Import
  prelude.
From zebre.language Require Import
  notations.
From zebre.std Require Import
  condition.
From zebre.saturn Require Export
  base.
From zebre Require Import
  options.

#[local] Notation "'flag'" := (
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

Definition mpsc_latch1_create : val :=
  λ: <>,
    let: "t" := { #false; (); () } in
    "t" <-{mutex} mutex_create () ;;
    "t" <-{condition} condition_create () ;;
    "t".

Definition mpsc_latch1_signal : val :=
  λ: "t",
    if: "t".{flag} then (
      #true
    ) else (
      let: "res" :=
        mutex_protect "t".{mutex} (λ: <>,
          if: "t".{flag} then (
            #true
          ) else (
            "t" <-{flag} #true ;;
            #false
          )
        )
      in
      condition_broadcast "t".{condition} ;;
      "res"
    ).

Definition mpsc_latch1_wait : val :=
  λ: "t",
    let: "mtx" := "t".{mutex} in
    let: "cond" := "t".{condition} in
    mutex_protect "mtx" (λ: <>,
      condition_wait_until "cond" "mtx" (λ: <>, "t".{flag})
    ).

#[global] Opaque mpsc_latch1_create.
#[global] Opaque mpsc_latch1_wait.
#[global] Opaque mpsc_latch1_signal.
