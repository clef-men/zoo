From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  diverge
  array
  assume
  int.
From zoo_std Require Import
  dynarray_2__types.
From zoo Require Import
  options.

Definition dynarray_2_element : val :=
  fun: "v" =>
    ‘Element{ "v" }.

Definition dynarray_2_create : val :=
  fun: <> =>
    { #0, array_create () }.

Definition dynarray_2_make : val :=
  fun: "sz" "v" =>
    { "sz", array_init "sz" (fun: <> => dynarray_2_element "v") }.

Definition dynarray_2_initi : val :=
  fun: "sz" "fn" =>
    { "sz", array_initi "sz" (fun: "i" => dynarray_2_element ("fn" "i")) }.

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
    dynarray_2_size "t" == #0.

Definition dynarray_2_get : val :=
  fun: "t" "i" =>
    match: array_get (dynarray_2_data "t") "i" with
    | Empty =>
        diverge ()
    | Element <> as "slot_r" =>
        "slot_r".{value}
    end.

Definition dynarray_2_set : val :=
  fun: "t" "i" "v" =>
    match: array_get (dynarray_2_data "t") "i" with
    | Empty =>
        diverge ()
    | Element <> as "slot_r" =>
        "slot_r" <-{value} "v"
    end.

Definition dynarray_2_next_capacity : val :=
  fun: "n" =>
    int_max
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
      let: "cap" := int_max "n" (dynarray_2_next_capacity "cap") in
      let: "data" := array_unsafe_grow "data" "cap" §Empty in
      dynarray_2_set_data "t" "data"
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
      dynarray_2_set_size "t" ("sz" + #1) ;;
      array_unsafe_set "data" "sz" "slot" ;;
      #true
    ).

Definition dynarray_2_push_aux : val :=
  rec: "push_aux" "t" "slot" =>
    dynarray_2_reserve_extra "t" #1 ;;
    if: ~ dynarray_2_try_push "t" "slot" then (
      "push_aux" "t" "slot"
    ).

Definition dynarray_2_push : val :=
  fun: "t" "v" =>
    let: "slot" := dynarray_2_element "v" in
    if: ~ dynarray_2_try_push "t" "slot" then (
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
    | Empty =>
        diverge ()
    | Element <> as "slot_r" =>
        array_unsafe_set "data" "sz" §Empty ;;
        dynarray_2_set_size "t" "sz" ;;
        "slot_r".{value}
    end.

Definition dynarray_2_fit_capacity : val :=
  fun: "t" =>
    let: "sz" := dynarray_2_size "t" in
    let: "data" := dynarray_2_data "t" in
    if: array_size "data" != "sz" then (
      dynarray_2_set_data "t" (array_shrink "data" "sz")
    ).

Definition dynarray_2_reset : val :=
  fun: "t" =>
    dynarray_2_set_size "t" #0 ;;
    dynarray_2_set_data "t" (array_create ()).

Definition dynarray_2_iteri : val :=
  fun: "fn" "t" =>
    let: "sz" := dynarray_2_size "t" in
    let: "data" := dynarray_2_data "t" in
    assume ("sz" ≤ array_size "data") ;;
    array_unsafe_iteri_slice
      (fun: "i" "slot" =>
         match: "slot" with
         | Empty =>
             diverge ()
         | Element <> as "slot_r" =>
             "fn" "i" "slot_r".{value}
         end)
      "data"
      #0
      "sz".

Definition dynarray_2_iter : val :=
  fun: "fn" =>
    dynarray_2_iteri (fun: "_i" => "fn").
