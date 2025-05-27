From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  array.
From zoo_persistent Require Import
  parray_2__types.
From zoo Require Import
  options.

Definition parray_2_make : val :=
  fun: "equal" "sz" "v" =>
    let: "data" := array_unsafe_make "sz" "v" in
    let: "root" := ref §Root in
    { "equal", "data", "root" }.

Definition parray_2_get : val :=
  fun: "t" "i" =>
    array_unsafe_get "t".{data} "i".

Definition parray_2_set : val :=
  fun: "t" "i" "v" =>
    let: "v'" := array_unsafe_get "t".{data} "i" in
    if: ~ "t".{equal} "v" "v'" then (
      let: "root" := ref §Root in
      "t".{root} <- ‘Diff( "i", "v'", "root" ) ;;
      "t" <-{root} "root" ;;
      array_unsafe_set "t".{data} "i" "v"
    ).

Definition parray_2_capture : val :=
  fun: "t" =>
    "t".{root}.

Definition parray_2_restore_0 : val :=
  rec: "restore" "data" "node" =>
    match: !"node" with
    | Root =>
        ()
    | Diff "i" "v" "node'" =>
        "restore" "data" "node'" ;;
        "node'" <- ‘Diff( "i", array_unsafe_get "data" "i", "node" ) ;;
        array_unsafe_set "data" "i" "v"
    end.

Definition parray_2_restore : val :=
  fun: "t" "s" =>
    match: !"s" with
    | Root =>
        ()
    | Diff <> <> <> =>
        parray_2_restore_0 "t".{data} "s" ;;
        "s" <- §Root ;;
        "t" <-{root} "s"
    end.
