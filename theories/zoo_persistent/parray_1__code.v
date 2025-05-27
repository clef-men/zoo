From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  array.
From zoo_persistent Require Import
  parray_1__types.
From zoo Require Import
  options.

Definition parray_1_make : val :=
  fun: "sz" "v" =>
    ref ‘Root( array_unsafe_make "sz" "v" ).

Definition parray_1_reroot_0 : val :=
  rec: "reroot" "t" =>
    match: !"t" with
    | Root "data" =>
        "data"
    | Diff "i" "v" "t'" =>
        let: "data" := "reroot" "t'" in
        "t'" <- ‘Diff( "i", array_unsafe_get "data" "i", "t" ) ;;
        array_unsafe_set "data" "i" "v" ;;
        "data"
    end.

Definition parray_1_reroot : val :=
  fun: "t" =>
    match: !"t" with
    | Root "data" =>
        "data"
    | Diff <> <> <> =>
        let: "data" := parray_1_reroot_0 "t" in
        "t" <- ‘Root( "data" ) ;;
        "data"
    end.

Definition parray_1_get : val :=
  fun: "t" "i" =>
    let: "data" := parray_1_reroot "t" in
    array_unsafe_get "data" "i".

Definition parray_1_set : val :=
  fun: "t" "equal" "i" "v" =>
    let: "data" := parray_1_reroot "t" in
    let: "v'" := array_unsafe_get "data" "i" in
    if: "equal" "v" "v'" then (
      "t"
    ) else (
      array_unsafe_set "data" "i" "v" ;;
      let: "t'" := ref !"t" in
      "t" <- ‘Diff( "i", "v'", "t'" ) ;;
      "t'"
    ).
