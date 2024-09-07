From zoo Require Import
  prelude.
From zoo.language Require Import
  notations.
From zoo.std Require Import
  array.
From zoo.persistent Require Import
  parray__types.
From zoo Require Import
  options.

Definition parray_make : val :=
  fun: "sz" "v" =>
    ref ‘Root( array_unsafe_make "sz" "v" ).

Definition parray_reroot : val :=
  rec: "reroot" "t" =>
    match: !"t" with
    | Root "arr" =>
        "arr"
    | Diff "i" "v" "t'" =>
        let: "arr" := "reroot" "t'" in
        "t'" <- ‘Diff( "i", array_unsafe_get "arr" "i", "t" ) ;;
        array_unsafe_set "arr" "i" "v" ;;
        "t" <- ‘Root( "arr" ) ;;
        "arr"
    end.

Definition parray_get : val :=
  fun: "t" "i" =>
    array_unsafe_get (parray_reroot "t") "i".

Definition parray_set : val :=
  fun: "t" "eq" "i" "v" =>
    let: "arr" := parray_reroot "t" in
    let: "v'" := array_unsafe_get "arr" "i" in
    if: "eq" "v" "v'" then (
      "t"
    ) else (
      array_unsafe_set "arr" "i" "v" ;;
      let: "t'" := ref !"t" in
      "t" <- ‘Diff( "i", "v'", "t'" ) ;;
      "t'"
    ).
