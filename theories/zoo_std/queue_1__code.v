From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  chain.
From zoo_std Require Import
  queue_1__types.
From zoo Require Import
  options.

Definition queue_1_create : val :=
  fun: <> =>
    let: "sent" := { (), () } in
    { "sent", "sent" }.

Definition queue_1_is_empty : val :=
  fun: "t" =>
    "t".{front} == "t".{sentinel}.

Definition queue_1_push : val :=
  fun: "t" "v" =>
    let: "sent" := { (), () } in
    "t".{sentinel} <-{chain_head} "v" ;;
    "t".{sentinel} <-{chain_tail} "sent" ;;
    "t" <-{sentinel} "sent".

Definition queue_1_pop : val :=
  fun: "t" =>
    if: queue_1_is_empty "t" then (
      §None
    ) else (
      let: "v" := "t".{front}.{chain_head} in
      "t" <-{front} "t".{front}.{chain_tail} ;;
      ‘Some( "v" )
    ).
