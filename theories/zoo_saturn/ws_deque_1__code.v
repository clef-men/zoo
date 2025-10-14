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
  ws_deque_1__types.
From zoo Require Import
  options.

Definition ws_deque_1_min_capacity : val :=
  #16.

Definition ws_deque_1_create : val :=
  fun: <> =>
    { #1, #1, array_unsafe_make ws_deque_1_min_capacity (), Proph }.

Definition ws_deque_1_size : val :=
  fun: "t" =>
    "t".{back} - "t".{front}.

Definition ws_deque_1_is_empty : val :=
  fun: "t" =>
    ws_deque_1_size "t" == #0.

Definition ws_deque_1_push : val :=
  fun: "t" "v" =>
    let: "back" := "t".{back} in
    let: "data" := "t".{data} in
    let: "cap" := array_size "data" in
    let: "front" := "t".{front} in
    if: "back" < "front" + "cap" then (
      array_unsafe_cset "data" "back" "v"
    ) else (
      let: "new_cap" := "cap" `lsl` #1 in
      let: "new_data" := array_unsafe_cgrow "data" "front" "new_cap" () in
      array_unsafe_cset "new_data" "back" "v" ;;
      "t" <-{data} "new_data"
    ) ;;
    "t" <-{back} "back" + #1.

Definition ws_deque_1_steal : val :=
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

Definition ws_deque_1_pop_0 : val :=
  fun: "t" "id" "back" =>
    let: "front" := "t".{front} in
    if: "back" < "front" then (
      "t" <-{back} "front" ;;
      §None
    ) else if: "front" < "back" then (
      let: "data" := "t".{data} in
      let: "cap" := array_size "data" in
      if: ws_deque_1_min_capacity + #3 * ("back" - "front") ≤ "cap" then (
        let: "new_cap" := "cap" `lsr` #1 in
        let: "new_data" :=
          array_unsafe_cshrink_slice "data" "front" "new_cap"
        in
        "t" <-{data} "new_data"
      ) else (
        ()
      ) ;;
      ‘Some( array_unsafe_cget "data" "back" )
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

Definition ws_deque_1_pop : val :=
  fun: "t" =>
    let: "id" := Id in
    let: "back" := "t".{back} - #1 in
    "t" <-{back} "back" ;;
    ws_deque_1_pop_0 "t" "id" "back".
