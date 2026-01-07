From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  array.
From zoo_std Require Import
  bqueue__types.
From zoo Require Import
  options.

Definition bqueue_create : val :=
  fun: "cap" =>
    { "cap", array_unsafe_make "cap" (), 0, 0 }.

Definition bqueue_size : val :=
  fun: "t" =>
    "t".{back} - "t".{front}.

Definition bqueue_is_empty : val :=
  fun: "t" =>
    bqueue_size "t" == 0.

Definition bqueue_unsafe_get : val :=
  fun: "t" "i" =>
    array_unsafe_cget "t".{data} ("t".{front} + "i").

Definition bqueue_unsafe_set : val :=
  fun: "t" "i" "v" =>
    array_unsafe_cset "t".{data} ("t".{front} + "i") "v".

Definition bqueue_push : val :=
  fun: "t" "v" =>
    let: "front" := "t".{front} in
    let: "back" := "t".{back} in
    if: "front" + "t".{capacity} == "back" then (
      false
    ) else (
      array_unsafe_cset "t".{data} "back" "v" ;;
      "t" <-{back} "back" + 1 ;;
      true
    ).

Definition bqueue_pop_front : val :=
  fun: "t" =>
    let: "front" := "t".{front} in
    let: "back" := "t".{back} in
    if: "front" == "back" then (
      §None
    ) else (
      let: "data" := "t".{data} in
      let: "v" := array_unsafe_cget "data" "front" in
      array_unsafe_cset "data" "front" () ;;
      "t" <-{front} "front" + 1 ;;
      ‘Some( "v" )
    ).

Definition bqueue_pop_back : val :=
  fun: "t" =>
    let: "front" := "t".{front} in
    let: "back" := "t".{back} in
    if: "front" == "back" then (
      §None
    ) else (
      let: "data" := "t".{data} in
      let: "back" := "back" - 1 in
      let: "v" := array_unsafe_cget "data" "back" in
      array_unsafe_cset "data" "back" () ;;
      "t" <-{back} "back" ;;
      ‘Some( "v" )
    ).
