From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_persistent Require Import
  sstore_2.
From zoo_persistent Require Import
  suf__types.
From zoo Require Import
  options.

Definition suf٠create : val :=
  sstore_2٠create.

Definition suf٠make : val :=
  fun: "t" =>
    sstore_2٠ref "t" ‘Root( 0 ).

Definition suf٠repr : val :=
  rec: "repr" "t" "elt" =>
    match: sstore_2٠get "t" "elt" with
    | Root <> =>
        "elt"
    | Link "parent" =>
        let: "repr" := "repr" "t" "parent" in
        sstore_2٠set "t" "elt" ‘Link( "repr" ) ;;
        "repr"
    end.

Definition suf٠equiv : val :=
  fun: "t" "elt1" "elt2" =>
    suf٠repr "t" "elt1" == suf٠repr "t" "elt2".

Definition suf٠rank : val :=
  fun: "t" "elt" =>
    match: sstore_2٠get "t" "elt" with
    | Root "rank" =>
        "rank"
    | Link <> =>
        Fail
    end.

Definition suf٠union : val :=
  fun: "t" "elt1" "elt2" =>
    let: "repr1" := suf٠repr "t" "elt1" in
    let: "rank1" := suf٠rank "t" "repr1" in
    let: "repr2" := suf٠repr "t" "elt2" in
    let: "rank2" := suf٠rank "t" "repr2" in
    if: "repr1" != "repr2" then (
      if: "rank1" < "rank2" then (
        sstore_2٠set "t" "repr1" ‘Link( "repr2" )
      ) else (
        sstore_2٠set "t" "repr2" ‘Link( "repr1" ) ;;
        if: "rank1" == "rank2" then (
          sstore_2٠set "t" "repr1" ‘Root( "rank1" + 1 )
        )
      )
    ).

Definition suf٠capture : val :=
  sstore_2٠capture.

Definition suf٠restore : val :=
  sstore_2٠restore.
