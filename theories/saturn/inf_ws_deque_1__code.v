From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo Require Import
  identifier.
From zoo_std Require Import
  inf_array.
From saturn Require Import
  inf_ws_deque_1__types.
From zoo Require Import
  options.

Definition inf_ws_deque_1_create : val :=
  fun: <> =>
    { #0, #0, inf_array_create (), Proph }.

Definition inf_ws_deque_1_push : val :=
  fun: "t" "v" =>
    let: "back" := "t".{back} in
    inf_array_set "t".{data} "back" "v" ;;
    "t" <-{back} "back" + #1.

Definition inf_ws_deque_1_steal : val :=
  rec: "steal" "t" =>
    let: "id" := Id in
    let: "front" := "t".{front} in
    let: "back" := "t".{back} in
    if: "back" ≤ "front" then (
      §None
    ) else if:
       Resolve
         (CAS "t".[front] "front" ("front" + #1))
         "t".{proph}
         ("front", "id")
     then (
      ‘Some( inf_array_get "t".{data} "front" )
    ) else (
      Yield ;;
      "steal" "t"
    ).

Definition inf_ws_deque_1_pop : val :=
  fun: "t" =>
    let: "id" := Id in
    let: "back" := "t".{back} - #1 in
    "t" <-{back} "back" ;;
    let: "front" := "t".{front} in
    if: "back" < "front" then (
      "t" <-{back} "front" ;;
      §None
    ) else if: "front" < "back" then (
      ‘Some( inf_array_get "t".{data} "back" )
    ) else if:
       Resolve
         (CAS "t".[front] "front" ("front" + #1))
         "t".{proph}
         ("front", "id")
     then (
      "t" <-{back} "front" + #1 ;;
      ‘Some( inf_array_get "t".{data} "back" )
    ) else (
      "t" <-{back} "front" + #1 ;;
      §None
    ).
