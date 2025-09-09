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
  fun: "equal" "sz" "v" =>
    let: "data" := array_unsafe_make "sz" "v" in
    ref ‘Root( "equal", "data" ).

Definition parray_1_reroot_0 : val :=
  rec: "reroot" "t" =>
    match: !"t" with
    | Root <> <> as "root_r" =>
        ("root_r".<equal>, "root_r".<data>)
    | Diff "i" "v" "t'" =>
        let: "equal", "data" := "reroot" "t'" in
        "t'" <- ‘Diff( "i", array_unsafe_get "data" "i", "t" ) ;;
        array_unsafe_set "data" "i" "v" ;;
        ("equal", "data")
    end.

Definition parray_1_reroot : val :=
  fun: "t" =>
    match: !"t" with
    | Root <> <> as "root_r" =>
        ("root_r".<equal>, "root_r".<data>)
    | Diff <> <> <> =>
        let: "equal", "data" := parray_1_reroot_0 "t" in
        "t" <- ‘Root( "equal", "data" ) ;;
        ("equal", "data")
    end.

Definition parray_1_get : val :=
  fun: "t" "i" =>
    let: <>, "data" := parray_1_reroot "t" in
    array_unsafe_get "data" "i".

Definition parray_1_set : val :=
  fun: "t" "i" "v" =>
    let: "equal", "data" := parray_1_reroot "t" in
    let: "v'" := array_unsafe_get "data" "i" in
    if: "equal" "v" "v'" then (
      "t"
    ) else (
      array_unsafe_set "data" "i" "v" ;;
      let: "t'" := ref !"t" in
      "t" <- ‘Diff( "i", "v'", "t'" ) ;;
      "t'"
    ).
