From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo Require Import
  identifier.
From zoo_std Require Import
  array
  domain.
From zoo_saturn Require Import
  ws_bqueue_1__types.
From zoo Require Import
  options.

Definition ws_bqueue_1_create : val :=
  fun: "cap" =>
    { "cap", #1, #1, array_unsafe_make "cap" (), Proph }.

Definition ws_bqueue_1_capacity : val :=
  fun: "t" =>
    "t".{capacity}.

Definition ws_bqueue_1_size : val :=
  fun: "t" =>
    "t".{back} - "t".{front}.

Definition ws_bqueue_1_is_empty : val :=
  fun: "t" =>
    ws_bqueue_1_size "t" == #0.

Definition ws_bqueue_1_push : val :=
  fun: "t" "v" =>
    let: "front" := "t".{front} in
    let: "back" := "t".{back} in
    let: "data" := "t".{data} in
    let: "cap" := array_size "data" in
    if: "back" < "front" + "cap" then (
      array_unsafe_cset "data" "back" "v" ;;
      "t" <-{back} "back" + #1 ;;
      #true
    ) else (
      #false
    ).

Definition ws_bqueue_1_steal : val :=
  rec: "steal" "t" =>
    let: "id" := Id in
    let: "front" := "t".{front} in
    let: "back" := "t".{back} in
    if: "back" ≤ "front" then (
      §None
    ) else (
      let: "data" := "t".{data} in
      let: "v" := array_unsafe_cget "data" "front" in
      if:
        Resolve
          (CAS "t".[front] "front" ("front" + #1))
          "t".{proph}
          ("front", "id")
      then (
        ‘Some( "v" )
      ) else (
        domain_yield () ;;
        "steal" "t"
      )
    ).

Definition ws_bqueue_1_pop_0 : val :=
  fun: "t" "id" "back" =>
    let: "front" := "t".{front} in
    if: "back" < "front" then (
      "t" <-{back} "front" ;;
      §None
    ) else if: "front" < "back" then (
      ‘Some( array_unsafe_cget "t".{data} "back" )
    ) else (
      let: "won" :=
        Resolve
          (CAS "t".[front] "front" ("front" + #1))
          "t".{proph}
          ("front", "id")
      in
      "t" <-{back} "front" + #1 ;;
      if: "won" then (
        ‘Some( array_unsafe_cget "t".{data} "front" )
      ) else (
        §None
      )
    ).

Definition ws_bqueue_1_pop : val :=
  fun: "t" =>
    let: "id" := Id in
    let: "back" := "t".{back} - #1 in
    "t" <-{back} "back" ;;
    ws_bqueue_1_pop_0 "t" "id" "back".
