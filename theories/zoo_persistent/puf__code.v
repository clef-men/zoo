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

Definition puf_create : val :=
  pstore_2_create.

Definition puf_make : val :=
  fun: "t" =>
    pstore_2_ref "t" ‘Root( #0 ).

Definition puf_repr : val :=
  rec: "repr" "t" "elt" =>
    match: pstore_2_get "t" "elt" with
    | Root <> =>
        "elt"
    | Link "parent" =>
        let: "repr" := "repr" "t" "parent" in
        pstore_2_set "t" "elt" ‘Link( "repr" ) ;;
        "repr"
    end.

Definition puf_equiv : val :=
  fun: "t" "elt1" "elt2" =>
    puf_repr "t" "elt1" == puf_repr "t" "elt2".

Definition puf_rank : val :=
  fun: "t" "elt" =>
    match: pstore_2_get "t" "elt" with
    | Root "rank" =>
        "rank"
    | Link <> =>
        Fail
    end.

Definition puf_union : val :=
  fun: "t" "elt1" "elt2" =>
    let: "repr1" := puf_repr "t" "elt1" in
    let: "rank1" := puf_rank "t" "repr1" in
    let: "repr2" := puf_repr "t" "elt2" in
    let: "rank2" := puf_rank "t" "repr2" in
    if: "repr1" != "repr2" then (
      if: "rank1" < "rank2" then (
        pstore_2_set "t" "repr1" ‘Link( "repr2" )
      ) else (
        pstore_2_set "t" "repr2" ‘Link( "repr1" ) ;;
        if: "rank1" == "rank2" then (
          pstore_2_set "t" "repr1" ‘Root( "rank1" + #1 )
        )
      )
    ).

Definition puf_capture : val :=
  pstore_2_capture.

Definition puf_restore : val :=
  pstore_2_restore.
