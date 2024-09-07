From zoo Require Import
  prelude.
From zoo.language Require Import
  notations.
From zoo.std Require Import
  assume
  array
  math
  diverge.
From zoo.std Require Import
  dynarray_2__types.
From zoo Require Import
  options.

Definition dynarray_2_create : val :=
  fun: <> =>
    { #0, array_create () }.

Definition dynarray_2_make : val :=
  fun: "sz" "v" =>
    { "sz", array_init "sz" (fun: <> => ‘Some( ref "v" )) }.

Definition dynarray_2_initi : val :=
  fun: "sz" "fn" =>
    { "sz", array_initi "sz" (fun: "i" => ‘Some( ref ("fn" "i") )) }.

Definition dynarray_2_size : val :=
  fun: "t" =>
    "t".{size}.

Definition dynarray_2_data : val :=
  fun: "t" =>
    "t".{data}.

Definition dynarray_2_capacity : val :=
  fun: "t" =>
    array_size (dynarray_2_data "t").

Definition dynarray_2_set_size : val :=
  fun: "t" "sz" =>
    "t" <-{size} "sz".

Definition dynarray_2_set_data : val :=
  fun: "t" "data" =>
    "t" <-{data} "data".

Definition dynarray_2_is_empty : val :=
  fun: "t" =>
    dynarray_2_size "t" = #0.

Definition dynarray_2_get : val :=
  fun: "t" "i" =>
    match: array_get (dynarray_2_data "t") "i" with
    | None =>
        diverge ()
    | Some "ref" =>
        !"ref"
    end.

Definition dynarray_2_set : val :=
  fun: "t" "i" "v" =>
    match: array_get (dynarray_2_data "t") "i" with
    | None =>
        diverge ()
    | Some "ref" =>
        "ref" <- "v"
    end.

Definition dynarray_2_next_capacity : val :=
  fun: "n" =>
    maximum
      #8
      if: "n" ≤ #512 then (
        #2 * "n"
      ) else (
        "n" + "n" `quot` #2
      ).

Definition dynarray_2_reserve : val :=
  fun: "t" "n" =>
    assume (#0 ≤ "n") ;;
    let: "data" := dynarray_2_data "t" in
    let: "cap" := array_size "data" in
    if: "cap" < "n" then (
      let: "new_cap" := maximum "n" (dynarray_2_next_capacity "cap") in
      let: "new_data" := array_unsafe_make "new_cap" §None in
      array_copy_slice "data" #0 "new_data" #0 (dynarray_2_size "t") ;;
      dynarray_2_set_data "t" "new_data"
    ).

Definition dynarray_2_reserve_extra : val :=
  fun: "t" "n" =>
    assume (#0 ≤ "n") ;;
    dynarray_2_reserve "t" (dynarray_2_size "t" + "n").

Definition dynarray_2_try_push : val :=
  fun: "t" "slot" =>
    let: "sz" := dynarray_2_size "t" in
    let: "data" := dynarray_2_data "t" in
    if: array_size "data" ≤ "sz" then (
      #false
    ) else (
      dynarray_2_set_size "t" (#1 + "sz") ;;
      array_unsafe_set "data" "sz" "slot" ;;
      #true
    ).

Definition dynarray_2_push_aux : val :=
  rec: "push_aux" "t" "slot" =>
    dynarray_2_reserve_extra "t" #1 ;;
    ifnot: dynarray_2_try_push "t" "slot" then (
      "push_aux" "t" "slot"
    ).

Definition dynarray_2_push : val :=
  fun: "t" "v" =>
    let: "slot" := ‘Some( ref "v" ) in
    ifnot: dynarray_2_try_push "t" "slot" then (
      dynarray_2_push_aux "t" "slot"
    ).

Definition dynarray_2_pop : val :=
  fun: "t" =>
    let: "sz" := dynarray_2_size "t" in
    let: "data" := dynarray_2_data "t" in
    assume ("sz" ≤ array_size "data") ;;
    assume (#0 < "sz") ;;
    let: "sz" := "sz" - #1 in
    match: array_unsafe_get "data" "sz" with
    | None =>
        diverge ()
    | Some "ref" =>
        array_unsafe_set "data" "sz" §None ;;
        dynarray_2_set_size "t" "sz" ;;
        !"ref"
    end.

Definition dynarray_2_fit_capacity : val :=
  fun: "t" =>
    let: "sz" := dynarray_2_size "t" in
    let: "data" := dynarray_2_data "t" in
    if: array_size "data" ≠ "sz" then (
      dynarray_2_set_data "t" (array_shrink "data" "sz")
    ).

Definition dynarray_2_reset : val :=
  fun: "t" =>
    dynarray_2_set_size "t" #0 ;;
    dynarray_2_set_data "t" (array_create ()).
