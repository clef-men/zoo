From zoo Require Import
  prelude.
From zoo.language Require Import
  notations.
From zoo.std Require Import
  array
  math.
From zoo.std Require Import
  dynarray_1__types.
From zoo Require Import
  options.

Definition dynarray_1_create : val :=
  fun: <> =>
    { #0, array_create () }.

Definition dynarray_1_make : val :=
  fun: "sz" "v" =>
    { "sz", array_unsafe_make "sz" "v" }.

Definition dynarray_1_initi : val :=
  fun: "sz" "fn" =>
    { "sz", array_unsafe_initi "sz" "fn" }.

Definition dynarray_1_size : val :=
  fun: "t" =>
    "t".{size}.

Definition dynarray_1_capacity : val :=
  fun: "t" =>
    array_size "t".{data}.

Definition dynarray_1_is_empty : val :=
  fun: "t" =>
    dynarray_1_size "t" = #0.

Definition dynarray_1_get : val :=
  fun: "t" "i" =>
    array_unsafe_get "t".{data} "i".

Definition dynarray_1_set : val :=
  fun: "t" "i" "v" =>
    array_unsafe_set "t".{data} "i" "v".

Definition dynarray_1_next_capacity : val :=
  fun: "n" =>
    maximum
      #8
      if: "n" ≤ #512 then (
        #2 * "n"
      ) else (
        "n" + "n" `quot` #2
      ).

Definition dynarray_1_reserve : val :=
  fun: "t" "n" =>
    let: "data" := "t".{data} in
    let: "cap" := array_size "data" in
    if: "cap" < "n" then (
      let: "new_cap" := maximum "n" (dynarray_1_next_capacity "cap") in
      let: "new_data" := array_unsafe_alloc "new_cap" in
      array_unsafe_copy_slice "data" #0 "new_data" #0 "t".{size} ;;
      "t" <-{data} "new_data"
    ).

Definition dynarray_1_reserve_extra : val :=
  fun: "t" "n" =>
    if: #0 ≤ "n" then (
      dynarray_1_reserve "t" ("t".{size} + "n")
    ).

Definition dynarray_1_push : val :=
  fun: "t" "v" =>
    dynarray_1_reserve_extra "t" #1 ;;
    let: "sz" := "t".{size} in
    "t" <-{size} "sz" + #1 ;;
    array_unsafe_set "t".{data} "sz" "v".

Definition dynarray_1_pop : val :=
  fun: "t" =>
    let: "sz" := "t".{size} - #1 in
    "t" <-{size} "sz" ;;
    let: "data" := "t".{data} in
    let: "v" := array_unsafe_get "data" "sz" in
    array_unsafe_set "data" "sz" () ;;
    "v".

Definition dynarray_1_fit_capacity : val :=
  fun: "t" =>
    let: "sz" := "t".{size} in
    let: "data" := "t".{data} in
    if: "sz" ≠ array_size "data" then (
      "t" <-{data} array_unsafe_shrink "data" "sz"
    ).

Definition dynarray_1_reset : val :=
  fun: "t" =>
    "t" <-{size} #0 ;;
    "t" <-{data} array_create ().
