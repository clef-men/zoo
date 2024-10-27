From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  lst__types.
From zoo Require Import
  options.

Definition lst_singleton : val :=
  fun: "v" =>
    "v" :: [].

Definition lst_head : val :=
  fun: "param" =>
    match: "param" with
    | [] =>
        Fail
    | "v" :: <> =>
        "v"
    end.

Definition lst_tail : val :=
  fun: "param" =>
    match: "param" with
    | [] =>
        Fail
    | <> :: "t" =>
        "t"
    end.

Definition lst_is_empty : val :=
  fun: "param" =>
    match: "param" with
    | [] =>
        #true
    | <> :: <> =>
        #false
    end.

Definition lst_get : val :=
  rec: "get" "t" "i" =>
    if: "i" ≤ #0 then (
      lst_head "t"
    ) else (
      "get" (lst_tail "t") ("i" - #1)
    ).

Definition lst_initi_aux : val :=
  rec: "initi_aux" "sz" "fn" "i" =>
    if: "sz" ≤ "i" then (
      []
    ) else (
      let: "v" := "fn" "i" in
      "v" :: "initi_aux" "sz" "fn" ("i" + #1)
    ).

Definition lst_initi : val :=
  fun: "sz" "fn" =>
    lst_initi_aux "sz" "fn" #0.

Definition lst_init : val :=
  fun: "sz" "fn" =>
    lst_initi "sz" (fun: <> => "fn" ()).

Definition lst_foldli_aux : val :=
  rec: "foldli_aux" "t" "acc" "fn" "i" =>
    match: "t" with
    | [] =>
        "acc"
    | "v" :: "t" =>
        "foldli_aux" "t" ("fn" "acc" "i" "v") "fn" ("i" + #1)
    end.

Definition lst_foldli : val :=
  fun: "t" "acc" "fn" =>
    lst_foldli_aux "t" "acc" "fn" #0.

Definition lst_foldl : val :=
  fun: "t" "acc" "fn" =>
    lst_foldli "t" "acc" (fun: "acc" <> => "fn" "acc").

Definition lst_foldri_aux : val :=
  rec: "foldri_aux" "t" "fn" "acc" "i" =>
    match: "t" with
    | [] =>
        "acc"
    | "v" :: "t" =>
        "fn" "i" "v" ("foldri_aux" "t" "fn" "acc" ("i" + #1))
    end.

Definition lst_foldri : val :=
  fun: "t" "fn" "acc" =>
    lst_foldri_aux "t" "fn" "acc" #0.

Definition lst_foldr : val :=
  fun: "t" "fn" "acc" =>
    lst_foldri "t" (fun: <> => "fn") "acc".

Definition lst_size : val :=
  fun: "t" =>
    lst_foldl "t" #0 (fun: "acc" <> => "acc" + #1).

Definition lst_rev_app : val :=
  fun: "t1" "t2" =>
    lst_foldl "t1" "t2" (fun: "acc" "v" => "v" :: "acc").

Definition lst_rev : val :=
  fun: "t" =>
    lst_rev_app "t" [].

Definition lst_app : val :=
  fun: "t1" "t2" =>
    lst_foldr "t1" (fun: "v" "acc" => "v" :: "acc") "t2".

Definition lst_snoc : val :=
  fun: "t" "v" =>
    lst_app "t" (lst_singleton "v").

Definition lst_iteri : val :=
  fun: "t" "fn" =>
    lst_foldli "t" () (fun: <> => "fn").

Definition lst_iter : val :=
  fun: "t" "fn" =>
    lst_iteri "t" (fun: <> => "fn").

Definition lst_mapi_aux : val :=
  rec: "mapi_aux" "t" "fn" "i" =>
    match: "t" with
    | [] =>
        []
    | "v" :: "t" =>
        let: "v" := "fn" "i" "v" in
        let: "t" := "mapi_aux" "t" "fn" ("i" + #1) in
        "v" :: "t"
    end.

Definition lst_mapi : val :=
  fun: "t" "fn" =>
    lst_mapi_aux "t" "fn" #0.

Definition lst_map : val :=
  fun: "t" "fn" =>
    lst_mapi "t" (fun: <> => "fn").
