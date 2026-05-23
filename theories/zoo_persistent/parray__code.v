From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  array.
From zoo_persistent Require Import
  parray__types.
From zoo Require Import
  options.

Definition parray٠make : val :=
  fun: "equal" "sz" "v" =>
    let: "data" := array٠unsafe_make "sz" "v" in
    ref ‘Root( "equal", "data" ).

Definition parray٠reroot₀ : val :=
  rec: "reroot" "t" =>
    match: !"t" with
    | Root <> <> as "root_r" =>
        ("root_r".<equal>, "root_r".<data>)
    | Diff "i" "v" "t'" =>
        let: "equal", "data" := "reroot" "t'" in
        "t'" <- ‘Diff( "i", array٠unsafe_get "data" "i", "t" ) ;;
        array٠unsafe_set "data" "i" "v" ;;
        ("equal", "data")
    end.

Definition parray٠reroot : val :=
  fun: "t" =>
    match: !"t" with
    | Root <> <> as "root_r" =>
        ("root_r".<equal>, "root_r".<data>)
    | Diff <> <> <> =>
        let: "equal", "data" := parray٠reroot₀ "t" in
        "t" <- ‘Root( "equal", "data" ) ;;
        ("equal", "data")
    end.

Definition parray٠get : val :=
  fun: "t" "i" =>
    let: <>, "data" := parray٠reroot "t" in
    array٠unsafe_get "data" "i".

Definition parray٠set : val :=
  fun: "t" "i" "v" =>
    let: "equal", "data" := parray٠reroot "t" in
    let: "v'" := array٠unsafe_get "data" "i" in
    if: "equal" "v" "v'" then (
      "t"
    ) else (
      array٠unsafe_set "data" "i" "v" ;;
      let: "t'" := ref !"t" in
      "t" <- ‘Diff( "i", "v'", "t'" ) ;;
      "t'"
    ).
