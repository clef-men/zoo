From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  lst__types.
From zoo Require Import
  options.

Definition lst٠singleton : val :=
  fun: "v" =>
    "v" :: [].

Definition lst٠head : val :=
  fun: "param" =>
    match: "param" with
    | [] =>
        Fail
    | "v" :: <> =>
        "v"
    end.

Definition lst٠tail : val :=
  fun: "param" =>
    match: "param" with
    | [] =>
        Fail
    | <> :: "t" =>
        "t"
    end.

Definition lst٠is_empty : val :=
  fun: "param" =>
    match: "param" with
    | [] =>
        true
    | <> :: <> =>
        false
    end.

Definition lst٠get : val :=
  rec: "get" "t" "i" =>
    if: "i" ≤ 0 then (
      lst٠head "t"
    ) else (
      "get" (lst٠tail "t") ("i" - 1)
    ).

Definition lst٠initi₀ : val :=
  rec: "initi" "sz" "fn" "i" =>
    if: "sz" ≤ "i" then (
      []
    ) else (
      let: "v" := "fn" "i" in
      "v" :: "initi" "sz" "fn" ("i" + 1)
    ).

Definition lst٠initi : val :=
  fun: "sz" "fn" =>
    lst٠initi₀ "sz" "fn" 0.

Definition lst٠init : val :=
  fun: "sz" "fn" =>
    lst٠initi "sz" (fun: "_i" => "fn" ()).

Definition lst٠foldli₀ : val :=
  rec: "foldli" "fn" "i" "acc" "t" =>
    match: "t" with
    | [] =>
        "acc"
    | "v" :: "t" =>
        "foldli" "fn" ("i" + 1) ("fn" "i" "acc" "v") "t"
    end.

Definition lst٠foldli : val :=
  fun: "fn" =>
    lst٠foldli₀ "fn" 0.

Definition lst٠foldl : val :=
  fun: "fn" =>
    lst٠foldli (fun: "_i" => "fn").

Definition lst٠foldri₀ : val :=
  rec: "foldri" "fn" "i" "t" "acc" =>
    match: "t" with
    | [] =>
        "acc"
    | "v" :: "t" =>
        "fn" "i" "v" ("foldri" "fn" ("i" + 1) "t" "acc")
    end.

Definition lst٠foldri : val :=
  fun: "fn" =>
    lst٠foldri₀ "fn" 0.

Definition lst٠foldr : val :=
  fun: "fn" =>
    lst٠foldri (fun: "_i" => "fn").

Definition lst٠size : val :=
  fun: "t" =>
    lst٠foldl (fun: "acc" <> => "acc" + 1) 0 "t".

Definition lst٠rev_app : val :=
  fun: "t1" "t2" =>
    lst٠foldl (fun: "acc" "v" => "v" :: "acc") "t2" "t1".

Definition lst٠rev : val :=
  fun: "t" =>
    lst٠rev_app "t" [].

Definition lst٠app : val :=
  fun: "t1" "t2" =>
    lst٠foldr (fun: "v" "acc" => "v" :: "acc") "t1" "t2".

Definition lst٠snoc : val :=
  fun: "t" "v" =>
    lst٠app "t" (lst٠singleton "v").

Definition lst٠iteri : val :=
  fun: "fn" =>
    lst٠foldli (fun: "i" <> => "fn" "i") ().

Definition lst٠iter : val :=
  fun: "fn" =>
    lst٠iteri (fun: "_i" => "fn").

Definition lst٠mapi₀ : val :=
  rec: "mapi" "fn" "i" "t" =>
    match: "t" with
    | [] =>
        []
    | "v" :: "t" =>
        let: "v" := "fn" "i" "v" in
        "v" :: "mapi" "fn" ("i" + 1) "t"
    end.

Definition lst٠mapi : val :=
  fun: "fn" =>
    lst٠mapi₀ "fn" 0.

Definition lst٠map : val :=
  fun: "fn" =>
    lst٠mapi (fun: "_i" => "fn").

Definition lst٠forall : val :=
  rec: "forall" "pred" "param" =>
    match: "param" with
    | [] =>
        true
    | "v" :: "t" =>
        "pred" "v" and "forall" "pred" "t"
    end.

Definition lst٠exists : val :=
  rec: "exists" "pred" "param" =>
    match: "param" with
    | [] =>
        false
    | "v" :: "t" =>
        "pred" "v" or "exists" "pred" "t"
    end.
