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

Definition dynarray_2٠element : val :=
  fun: "v" =>
    ‘Element{ "v" }.

Definition dynarray_2٠create : val :=
  fun: <> =>
    { 0, array٠create () }.

Definition dynarray_2٠make : val :=
  fun: "sz" "v" =>
    { "sz", array٠init "sz" (fun: <> => dynarray_2٠element "v") }.

Definition dynarray_2٠initi : val :=
  fun: "sz" "fn" =>
    { "sz", array٠initi "sz" (fun: "i" => dynarray_2٠element ("fn" "i")) }.

Definition dynarray_2٠size : val :=
  fun: "t" =>
    "t".{size}.

Definition dynarray_2٠data : val :=
  fun: "t" =>
    "t".{data}.

Definition dynarray_2٠capacity : val :=
  fun: "t" =>
    array٠size (dynarray_2٠data "t").

Definition dynarray_2٠set_size : val :=
  fun: "t" "sz" =>
    "t" <-{size} "sz".

Definition dynarray_2٠set_data : val :=
  fun: "t" "data" =>
    "t" <-{data} "data".

Definition dynarray_2٠is_empty : val :=
  fun: "t" =>
    dynarray_2٠size "t" == 0.

Definition dynarray_2٠get : val :=
  fun: "t" "i" =>
    match: array٠get (dynarray_2٠data "t") "i" with
    | Empty =>
        diverge ()
    | Element <> as "slot_r" =>
        "slot_r".{value}
    end.

Definition dynarray_2٠set : val :=
  fun: "t" "i" "v" =>
    match: array٠get (dynarray_2٠data "t") "i" with
    | Empty =>
        diverge ()
    | Element <> as "slot_r" =>
        "slot_r" <-{value} "v"
    end.

Definition dynarray_2٠next_capacity : val :=
  fun: "n" =>
    int٠max 8 if: "n" ≤ 512 then (
                 2 * "n"
               ) else (
                 "n" + "n" `quot` 2
               ).

Definition dynarray_2٠reserve : val :=
  fun: "t" "n" =>
    assume (0 ≤ "n") ;;
    let: "data" := dynarray_2٠data "t" in
    let: "cap" := array٠size "data" in
    if: "cap" < "n" then (
      let: "cap" := int٠max "n" (dynarray_2٠next_capacity "cap") in
      let: "data" := array٠unsafe_grow "data" "cap" §Empty in
      dynarray_2٠set_data "t" "data"
    ).

Definition dynarray_2٠reserve_extra : val :=
  fun: "t" "n" =>
    assume (0 ≤ "n") ;;
    dynarray_2٠reserve "t" (dynarray_2٠size "t" + "n").

Definition dynarray_2٠try_grow : val :=
  fun: "t" "sz" "v" =>
    let: "old_sz" := dynarray_2٠size "t" in
    if: "sz" ≤ "old_sz" then (
      true
    ) else (
      let: "data" := dynarray_2٠data "t" in
      if: array٠size "data" < "sz" then (
        false
      ) else (
        dynarray_2٠set_size "t" "sz" ;;
        array٠unsafe_apply_slice
          (fun: <> => dynarray_2٠element "v")
          "data"
          "old_sz"
          ("sz" - "old_sz") ;;
        true
      )
    ).

Definition dynarray_2٠grow₀ : val :=
  rec: "grow" "t" "sz" "v" =>
    dynarray_2٠reserve "t" "sz" ;;
    if: ~ dynarray_2٠try_grow "t" "sz" "v" then (
      "grow" "t" "sz" "v"
    ).

Definition dynarray_2٠grow : val :=
  fun: "t" "sz" "v" =>
    if: ~ dynarray_2٠try_grow "t" "sz" "v" then (
      dynarray_2٠grow₀ "t" "sz" "v"
    ).

Definition dynarray_2٠try_push : val :=
  fun: "t" "slot" =>
    let: "sz" := dynarray_2٠size "t" in
    let: "data" := dynarray_2٠data "t" in
    if: array٠size "data" ≤ "sz" then (
      false
    ) else (
      dynarray_2٠set_size "t" ("sz" + 1) ;;
      array٠unsafe_set "data" "sz" "slot" ;;
      true
    ).

Definition dynarray_2٠push₀ : val :=
  rec: "push" "t" "slot" =>
    dynarray_2٠reserve_extra "t" 1 ;;
    if: ~ dynarray_2٠try_push "t" "slot" then (
      "push" "t" "slot"
    ).

Definition dynarray_2٠push : val :=
  fun: "t" "v" =>
    let: "slot" := dynarray_2٠element "v" in
    if: ~ dynarray_2٠try_push "t" "slot" then (
      dynarray_2٠push₀ "t" "slot"
    ).

Definition dynarray_2٠pop : val :=
  fun: "t" =>
    let: "sz" := dynarray_2٠size "t" in
    let: "data" := dynarray_2٠data "t" in
    assume ("sz" ≤ array٠size "data") ;;
    assume (0 < "sz") ;;
    let: "sz" := "sz" - 1 in
    match: array٠unsafe_get "data" "sz" with
    | Empty =>
        diverge ()
    | Element <> as "slot_r" =>
        array٠unsafe_set "data" "sz" §Empty ;;
        dynarray_2٠set_size "t" "sz" ;;
        "slot_r".{value}
    end.

Definition dynarray_2٠fit_capacity : val :=
  fun: "t" =>
    let: "sz" := dynarray_2٠size "t" in
    let: "data" := dynarray_2٠data "t" in
    if: array٠size "data" != "sz" then (
      dynarray_2٠set_data "t" (array٠shrink "data" "sz")
    ).

Definition dynarray_2٠reset : val :=
  fun: "t" =>
    dynarray_2٠set_size "t" 0 ;;
    dynarray_2٠set_data "t" (array٠create ()).

Definition dynarray_2٠iteri : val :=
  fun: "fn" "t" =>
    let: "sz" := dynarray_2٠size "t" in
    let: "data" := dynarray_2٠data "t" in
    assume ("sz" ≤ array٠size "data") ;;
    array٠unsafe_iteri_slice
      (fun: "i" "slot" =>
         match: "slot" with
         | Empty =>
             diverge ()
         | Element <> as "slot_r" =>
             "fn" "i" "slot_r".{value}
         end)
      "data"
      0
      "sz".

Definition dynarray_2٠iter : val :=
  fun: "fn" =>
    dynarray_2٠iteri (fun: "_i" => "fn").
