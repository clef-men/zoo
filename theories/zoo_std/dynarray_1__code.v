Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.array.
Require Import zoo_std.int.
Require Import zoo_std.dynarray_1__types.
Require Import zoo.options.

Definition dynarray_1٠create : val :=
  fun: <> =>
    { 0, array٠create () }.

Definition dynarray_1٠make : val :=
  fun: "sz" "v" =>
    { "sz", array٠unsafe_make "sz" "v" }.

Definition dynarray_1٠initi : val :=
  fun: "sz" "fn" =>
    { "sz", array٠unsafe_initi "sz" "fn" }.

Definition dynarray_1٠size : val :=
  fun: "t" =>
    "t".{size}.

Definition dynarray_1٠capacity : val :=
  fun: "t" =>
    array٠size "t".{data}.

Definition dynarray_1٠is_empty : val :=
  fun: "t" =>
    dynarray_1٠size "t" == 0.

Definition dynarray_1٠get : val :=
  fun: "t" "i" =>
    array٠unsafe_get "t".{data} "i".

Definition dynarray_1٠set : val :=
  fun: "t" "i" "v" =>
    array٠unsafe_set "t".{data} "i" "v".

Definition dynarray_1٠next_capacity : val :=
  fun: "n" =>
    int٠max 8 if: "n" ≤ 512 then (
                 2 * "n"
               ) else (
                 "n" + "n" `quot` 2
               ).

Definition dynarray_1٠reserve : val :=
  fun: "t" "n" =>
    let: "data" := "t".{data} in
    let: "cap" := array٠size "data" in
    if: "cap" < "n" then (
      let: "new_cap" := int٠max "n" (dynarray_1٠next_capacity "cap") in
      let: "new_data" := array٠unsafe_alloc "new_cap" in
      array٠unsafe_copy_slice "data" 0 "new_data" 0 "t".{size} ;;
      "t" <-{data} "new_data"
    ).

Definition dynarray_1٠reserve_extra : val :=
  fun: "t" "n" =>
    dynarray_1٠reserve "t" ("t".{size} + "n").

Definition dynarray_1٠grow : val :=
  fun: "t" "sz" "v" =>
    let: "old_sz" := "t".{size} in
    if: "old_sz" < "sz" then (
      dynarray_1٠reserve "t" "sz" ;;
      array٠unsafe_fill_slice "t".{data} "old_sz" ("sz" - "old_sz") "v" ;;
      "t" <-{size} "sz"
    ).

Definition dynarray_1٠push : val :=
  fun: "t" "v" =>
    dynarray_1٠reserve_extra "t" 1 ;;
    let: "sz" := "t".{size} in
    "t" <-{size} "sz" + 1 ;;
    array٠unsafe_set "t".{data} "sz" "v".

Definition dynarray_1٠pop : val :=
  fun: "t" =>
    let: "sz" := "t".{size} - 1 in
    "t" <-{size} "sz" ;;
    let: "data" := "t".{data} in
    let: "v" := array٠unsafe_get "data" "sz" in
    array٠unsafe_set "data" "sz" () ;;
    "v".

Definition dynarray_1٠fit_capacity : val :=
  fun: "t" =>
    let: "sz" := "t".{size} in
    let: "data" := "t".{data} in
    if: "sz" != array٠size "data" then (
      "t" <-{data} array٠unsafe_shrink "data" "sz"
    ).

Definition dynarray_1٠reset : val :=
  fun: "t" =>
    "t" <-{size} 0 ;;
    "t" <-{data} array٠create ().

Definition dynarray_1٠iteri : val :=
  fun: "fn" "t" =>
    array٠unsafe_iteri_slice "fn" "t".{data} 0 "t".{size}.

Definition dynarray_1٠iter : val :=
  fun: "fn" =>
    dynarray_1٠iteri (fun: "_i" => "fn").
