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
    let: "front" := { (), () } in
    { "front", "front" }.

Definition queue_1_is_empty : val :=
  fun: "t" =>
    "t".{front} == "t".{back}.

Definition queue_1_push : val :=
  fun: "t" "v" =>
    let: "back" := "t".{back} in
    let: "new_back" := { (), () } in
    "back" <-{chain_next} "new_back" ;;
    "back" <-{chain_data} "v" ;;
    "t" <-{back} "new_back".

Definition queue_1_pop : val :=
  fun: "t" =>
    if: queue_1_is_empty "t" then (
      §None
    ) else (
      let: "front" := "t".{front} in
      "t" <-{front} "front".{chain_next} ;;
      let: "v" := "front".{chain_data} in
      ‘Some( "v" )
    ).
