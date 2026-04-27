From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  array
  int.
From zoo_std Require Import
  queue_3__types.
From zoo Require Import
  options.

Definition queue_3٠min_capacity : val :=
  16.

Definition queue_3٠create : val :=
  fun: <> =>
    { array٠unsafe_make queue_3٠min_capacity (), 0, 0 }.

Definition queue_3٠size : val :=
  fun: "t" =>
    "t".{back} - "t".{front}.

Definition queue_3٠is_empty : val :=
  fun: "t" =>
    queue_3٠size "t" == 0.

Definition queue_3٠unsafe_get : val :=
  fun: "t" "i" =>
    array٠unsafe_cget "t".{data} ("t".{front} + "i").

Definition queue_3٠unsafe_set : val :=
  fun: "t" "i" "v" =>
    array٠unsafe_cset "t".{data} ("t".{front} + "i") "v".

Definition queue_3٠next_capacity : val :=
  fun: "n" =>
    int٠max 8 if: "n" ≤ 512 then (
                 2 * "n"
               ) else (
                 "n" + "n" `quot` 2
               ).

Definition queue_3٠grow : val :=
  fun: "t" =>
    let: "front" := "t".{front} in
    let: "back" := "t".{back} in
    let: "data" := "t".{data} in
    let: "cap" := array٠size "data" in
    if: "front" + "cap" == "back" then (
      let: "new_cap" :=
        int٠max ("cap" + 1) (queue_3٠next_capacity "cap")
      in
      let: "new_data" := array٠unsafe_cgrow "data" "front" "new_cap" () in
      "t" <-{data} "new_data"
    ).

Definition queue_3٠push : val :=
  fun: "t" "v" =>
    queue_3٠grow "t" ;;
    let: "back" := "t".{back} in
    array٠unsafe_cset "t".{data} "back" "v" ;;
    "t" <-{back} "back" + 1.

Definition queue_3٠shrink : val :=
  fun: "t" =>
    let: "front" := "t".{front} in
    let: "back" := "t".{back} in
    let: "sz" := "back" - "front" in
    let: "data" := "t".{data} in
    let: "cap" := array٠size "data" in
    if: queue_3٠min_capacity + 3 * "sz" ≤ "cap" then (
      let: "new_cap" := "cap" `lsr` 1 + 1 in
      let: "new_data" :=
        array٠unsafe_cshrink_slice "data" "front" "new_cap"
      in
      "t" <-{data} "new_data"
    ).

Definition queue_3٠pop_front : val :=
  fun: "t" =>
    let: "front" := "t".{front} in
    let: "back" := "t".{back} in
    if: "front" == "back" then (
      §None
    ) else (
      let: "data" := "t".{data} in
      let: "v" := array٠unsafe_cget "data" "front" in
      array٠unsafe_cset "data" "front" () ;;
      "t" <-{front} "front" + 1 ;;
      queue_3٠shrink "t" ;;
      ‘Some( "v" )
    ).

Definition queue_3٠pop_back : val :=
  fun: "t" =>
    let: "front" := "t".{front} in
    let: "back" := "t".{back} in
    if: "front" == "back" then (
      §None
    ) else (
      let: "data" := "t".{data} in
      let: "back" := "back" - 1 in
      let: "v" := array٠unsafe_cget "data" "back" in
      array٠unsafe_cset "data" "back" () ;;
      "t" <-{back} "back" ;;
      queue_3٠shrink "t" ;;
      ‘Some( "v" )
    ).
