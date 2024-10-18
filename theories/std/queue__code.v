From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo Require Import
  chain.
From zoo.std Require Import
  queue__types.
From zoo Require Import
  options.

Definition queue_create : val :=
  fun: <> =>
    let: "sent" := { (), () } in
    { "sent", "sent" }.

Definition queue_is_empty : val :=
  fun: "t" =>
    "t".{front} == "t".{sentinel}.

Definition queue_push : val :=
  fun: "t" "v" =>
    let: "sent" := { (), () } in
    "t".{sentinel} <-{chain_head} "v" ;;
    "t".{sentinel} <-{chain_tail} "sent" ;;
    "t" <-{sentinel} "sent".

Definition queue_pop : val :=
  fun: "t" =>
    if: queue_is_empty "t" then (
      §None
    ) else (
      let: "v" := "t".{front}.{chain_head} in
      "t" <-{front} "t".{front}.{chain_tail} ;;
      ‘Some( "v" )
    ).
