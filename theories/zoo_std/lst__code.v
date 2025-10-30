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

Definition lst_initi_0 : val :=
  rec: "initi" "sz" "fn" "i" =>
    if: "sz" ≤ "i" then (
      []
    ) else (
      let: "v" := "fn" "i" in
      "v" :: "initi" "sz" "fn" ("i" + #1)
    ).

Definition lst_initi : val :=
  fun: "sz" "fn" =>
    lst_initi_0 "sz" "fn" #0.

Definition lst_init : val :=
  fun: "sz" "fn" =>
    lst_initi "sz" (fun: "_i" => "fn" ()).

Definition lst_foldli_0 : val :=
  rec: "foldli" "fn" "i" "acc" "t" =>
    match: "t" with
    | [] =>
        "acc"
    | "v" :: "t" =>
        "foldli" "fn" ("i" + #1) ("fn" "i" "acc" "v") "t"
    end.

Definition lst_foldli : val :=
  fun: "fn" =>
    lst_foldli_0 "fn" #0.

Definition lst_foldl : val :=
  fun: "fn" =>
    lst_foldli (fun: "_i" => "fn").

Definition lst_foldri_0 : val :=
  rec: "foldri" "fn" "i" "t" "acc" =>
    match: "t" with
    | [] =>
        "acc"
    | "v" :: "t" =>
        "fn" "i" "v" ("foldri" "fn" ("i" + #1) "t" "acc")
    end.

Definition lst_foldri : val :=
  fun: "fn" =>
    lst_foldri_0 "fn" #0.

Definition lst_foldr : val :=
  fun: "fn" =>
    lst_foldri (fun: "_i" => "fn").

Definition lst_size : val :=
  fun: "t" =>
    lst_foldl (fun: "acc" <> => "acc" + #1) #0 "t".

Definition lst_rev_app : val :=
  fun: "t1" "t2" =>
    lst_foldl (fun: "acc" "v" => "v" :: "acc") "t2" "t1".

Definition lst_rev : val :=
  fun: "t" =>
    lst_rev_app "t" [].

Definition lst_app : val :=
  fun: "t1" "t2" =>
    lst_foldr (fun: "v" "acc" => "v" :: "acc") "t1" "t2".

Definition lst_snoc : val :=
  fun: "t" "v" =>
    lst_app "t" (lst_singleton "v").

Definition lst_iteri : val :=
  fun: "fn" =>
    lst_foldli (fun: "i" <> => "fn" "i") ().

Definition lst_iter : val :=
  fun: "fn" =>
    lst_iteri (fun: "_i" => "fn").

Definition lst_mapi_0 : val :=
  rec: "mapi" "fn" "i" "t" =>
    match: "t" with
    | [] =>
        []
    | "v" :: "t" =>
        let: "v" := "fn" "i" "v" in
        "v" :: "mapi" "fn" ("i" + #1) "t"
    end.

Definition lst_mapi : val :=
  fun: "fn" =>
    lst_mapi_0 "fn" #0.

Definition lst_map : val :=
  fun: "fn" =>
    lst_mapi (fun: "_i" => "fn").

Definition lst_forall : val :=
  rec: "forall" "pred" "param" =>
    match: "param" with
    | [] =>
        #true
    | "v" :: "t" =>
        "pred" "v" and "forall" "pred" "t"
    end.

Definition lst_exists : val :=
  rec: "exists" "pred" "param" =>
    match: "param" with
    | [] =>
        #false
    | "v" :: "t" =>
        "pred" "v" or "exists" "pred" "t"
    end.
