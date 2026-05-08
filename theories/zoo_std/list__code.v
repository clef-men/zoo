From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  list__types.
From zoo Require Import
  options.

Definition list٠singleton : val :=
  fun: "v" =>
    "v" :: [].

Definition list٠head : val :=
  fun: "param" =>
    match: "param" with
    | [] =>
        Fail
    | "v" :: <> =>
        "v"
    end.

Definition list٠tail : val :=
  fun: "param" =>
    match: "param" with
    | [] =>
        Fail
    | <> :: "t" =>
        "t"
    end.

Definition list٠is_empty : val :=
  fun: "param" =>
    match: "param" with
    | [] =>
        true
    | <> :: <> =>
        false
    end.

Definition list٠get : val :=
  rec: "get" "t" "i" =>
    if: "i" ≤ 0 then (
      list٠head "t"
    ) else (
      "get" (list٠tail "t") ("i" - 1)
    ).

Definition list٠initi₀ : val :=
  rec: "initi" "sz" "fn" "i" =>
    if: "sz" ≤ "i" then (
      []
    ) else (
      let: "v" := "fn" "i" in
      "v" :: "initi" "sz" "fn" ("i" + 1)
    ).

Definition list٠initi : val :=
  fun: "sz" "fn" =>
    list٠initi₀ "sz" "fn" 0.

Definition list٠init : val :=
  fun: "sz" "fn" =>
    list٠initi "sz" (fun: "_i" => "fn" ()).

Definition list٠foldli₀ : val :=
  rec: "foldli" "fn" "i" "acc" "t" =>
    match: "t" with
    | [] =>
        "acc"
    | "v" :: "t" =>
        "foldli" "fn" ("i" + 1) ("fn" "i" "acc" "v") "t"
    end.

Definition list٠foldli : val :=
  fun: "fn" =>
    list٠foldli₀ "fn" 0.

Definition list٠foldl : val :=
  fun: "fn" =>
    list٠foldli (fun: "_i" => "fn").

Definition list٠foldri₀ : val :=
  rec: "foldri" "fn" "i" "t" "acc" =>
    match: "t" with
    | [] =>
        "acc"
    | "v" :: "t" =>
        "fn" "i" "v" ("foldri" "fn" ("i" + 1) "t" "acc")
    end.

Definition list٠foldri : val :=
  fun: "fn" =>
    list٠foldri₀ "fn" 0.

Definition list٠foldr : val :=
  fun: "fn" =>
    list٠foldri (fun: "_i" => "fn").

Definition list٠size : val :=
  fun: "t" =>
    list٠foldl (fun: "acc" <> => "acc" + 1) 0 "t".

Definition list٠rev_app : val :=
  fun: "t1" "t2" =>
    list٠foldl (fun: "acc" "v" => "v" :: "acc") "t2" "t1".

Definition list٠rev : val :=
  fun: "t" =>
    list٠rev_app "t" [].

Definition list٠app : val :=
  fun: "t1" "t2" =>
    list٠foldr (fun: "v" "acc" => "v" :: "acc") "t1" "t2".

Definition list٠snoc : val :=
  fun: "t" "v" =>
    list٠app "t" (list٠singleton "v").

Definition list٠iteri : val :=
  fun: "fn" =>
    list٠foldli (fun: "i" <> => "fn" "i") ().

Definition list٠iter : val :=
  fun: "fn" =>
    list٠iteri (fun: "_i" => "fn").

Definition list٠mapi₀ : val :=
  rec: "mapi" "fn" "i" "t" =>
    match: "t" with
    | [] =>
        []
    | "v" :: "t" =>
        let: "v" := "fn" "i" "v" in
        "v" :: "mapi" "fn" ("i" + 1) "t"
    end.

Definition list٠mapi : val :=
  fun: "fn" =>
    list٠mapi₀ "fn" 0.

Definition list٠map : val :=
  fun: "fn" =>
    list٠mapi (fun: "_i" => "fn").

Definition list٠forall : val :=
  rec: "forall" "pred" "param" =>
    match: "param" with
    | [] =>
        true
    | "v" :: "t" =>
        "pred" "v" and "forall" "pred" "t"
    end.

Definition list٠exists : val :=
  rec: "exists" "pred" "param" =>
    match: "param" with
    | [] =>
        false
    | "v" :: "t" =>
        "pred" "v" or "exists" "pred" "t"
    end.
