From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  array.
From zoo_saturn Require Import
  spsc_bqueue__types.
From zoo Require Import
  options.

Definition spsc_bqueue_create : val :=
  fun: "cap" =>
    { array_unsafe_make "cap" §None, #0, #0, #0, #0 }.

Definition spsc_bqueue_size : val :=
  fun: "t" =>
    let: "back" := "t".{back} in
    let: "front" := "t".{front} in
    "back" - "front".

Definition spsc_bqueue_is_empty : val :=
  fun: "t" =>
    spsc_bqueue_size "t" == #0.

Definition spsc_bqueue_push_0 : val :=
  fun: "t" "data" "back" =>
    let: "cap" := array_size "data" in
    if: "back" < "t".{front_cache} + "cap" then (
      #true
    ) else (
      let: "front" := "t".{front} in
      "t" <-{front_cache} "front" ;;
      "back" < "front" + "cap"
    ).

Definition spsc_bqueue_push : val :=
  fun: "t" "v" =>
    let: "data" := "t".{data} in
    let: "back" := "t".{back} in
    if: spsc_bqueue_push_0 "t" "data" "back" then (
      array_unsafe_cset "data" "back" ‘Some( "v" ) ;;
      "t" <-{back} "back" + #1 ;;
      #false
    ) else (
      #true
    ).

Definition spsc_bqueue_pop_0 : val :=
  fun: "t" "front" =>
    if: "front" < "t".{back_cache} then (
      #true
    ) else (
      let: "back" := "t".{back} in
      "t" <-{back_cache} "back" ;;
      "front" < "back"
    ).

Definition spsc_bqueue_pop : val :=
  fun: "t" =>
    let: "front" := "t".{front} in
    if: spsc_bqueue_pop_0 "t" "front" then (
      let: "data" := "t".{data} in
      let: "res" := array_unsafe_cget "data" "front" in
      array_unsafe_cset "data" "front" §None ;;
      "t" <-{front} "front" + #1 ;;
      "res"
    ) else (
      §None
    ).
