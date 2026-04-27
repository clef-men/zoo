From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_persistent Require Import
  pstore_2.
From zoo_persistent Require Import
  puf__types.
From zoo Require Import
  options.

Definition puf٠create : val :=
  pstore_2٠create.

Definition puf٠make : val :=
  fun: "t" =>
    pstore_2٠ref "t" ‘Root( 0 ).

Definition puf٠repr : val :=
  rec: "repr" "t" "elt" =>
    match: pstore_2٠get "t" "elt" with
    | Root <> =>
        "elt"
    | Link "parent" =>
        let: "repr" := "repr" "t" "parent" in
        pstore_2٠set "t" "elt" ‘Link( "repr" ) ;;
        "repr"
    end.

Definition puf٠equiv : val :=
  fun: "t" "elt1" "elt2" =>
    puf٠repr "t" "elt1" == puf٠repr "t" "elt2".

Definition puf٠rank : val :=
  fun: "t" "elt" =>
    match: pstore_2٠get "t" "elt" with
    | Root "rank" =>
        "rank"
    | Link <> =>
        Fail
    end.

Definition puf٠union : val :=
  fun: "t" "elt1" "elt2" =>
    let: "repr1" := puf٠repr "t" "elt1" in
    let: "rank1" := puf٠rank "t" "repr1" in
    let: "repr2" := puf٠repr "t" "elt2" in
    let: "rank2" := puf٠rank "t" "repr2" in
    if: "repr1" != "repr2" then (
      if: "rank1" < "rank2" then (
        pstore_2٠set "t" "repr1" ‘Link( "repr2" )
      ) else (
        pstore_2٠set "t" "repr2" ‘Link( "repr1" ) ;;
        if: "rank1" == "rank2" then (
          pstore_2٠set "t" "repr1" ‘Root( "rank1" + 1 )
        )
      )
    ).

Definition puf٠capture : val :=
  pstore_2٠capture.

Definition puf٠restore : val :=
  pstore_2٠restore.
