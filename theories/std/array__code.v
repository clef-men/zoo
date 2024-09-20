From zoo Require Import
  prelude.
From zoo.language Require Import
  notations.
From zoo Require Import
  assume.
From zoo.std Require Import
  array__types.
From zoo Require Import
  options.

Definition array_unsafe_alloc : val :=
  fun: "sz" =>
    Alloc #0 "sz".

Definition array_alloc : val :=
  fun: "sz" =>
    assume (#0 ≤ "sz") ;;
    array_unsafe_alloc "sz".

Definition array_create : val :=
  fun: <> =>
    array_unsafe_alloc #0.

Definition array_size : val :=
  fun: "t" =>
    GetSize "t".

Definition array_unsafe_get : val :=
  fun: "t" "i" =>
    Load "t" "i".

Definition array_get : val :=
  fun: "t" "i" =>
    assume (#0 ≤ "i") ;;
    assume ("i" < array_size "t") ;;
    array_unsafe_get "t" "i".

Definition array_unsafe_set : val :=
  fun: "t" "i" "v" =>
    Store "t" "i" "v".

Definition array_set : val :=
  fun: "t" "i" "v" =>
    assume (#0 ≤ "i") ;;
    assume ("i" < array_size "t") ;;
    array_unsafe_set "t" "i" "v".

Definition array_unsafe_fill_slice : val :=
  fun: "t" "i" "n" "v" =>
    for: "j" := #0 to "n" begin
      array_unsafe_set "t" ("i" + "j") "v"
    end.

Definition array_fill_slice : val :=
  fun: "t" "i" "n" "v" =>
    let: "sz" := array_size "t" in
    assume (#0 ≤ "i") ;;
    assume (#0 ≤ "n") ;;
    assume ("i" + "n" ≤ "sz") ;;
    array_unsafe_fill_slice "t" "i" "n" "v".

Definition array_fill : val :=
  fun: "t" "v" =>
    array_unsafe_fill_slice "t" #0 (array_size "t") "v".

Definition array_unsafe_make : val :=
  fun: "sz" "v" =>
    let: "t" := array_unsafe_alloc "sz" in
    array_fill "t" "v" ;;
    "t".

Definition array_make : val :=
  fun: "sz" "v" =>
    assume (#0 ≤ "sz") ;;
    array_unsafe_make "sz" "v".

Definition array_foldli_aux : val :=
  rec: "foldli_aux" "t" "sz" "acc" "fn" "i" =>
    if: "sz" ≤ "i" then (
      "acc"
    ) else (
      let: "v" := array_unsafe_get "t" "i" in
      "foldli_aux" "t" "sz" ("fn" "acc" "i" "v") "fn" ("i" + #1)
    ).

Definition array_foldli : val :=
  fun: "t" "acc" "fn" =>
    array_foldli_aux "t" (array_size "t") "acc" "fn" #0.

Definition array_foldl : val :=
  fun: "t" "acc" "fn" =>
    array_foldli "t" "acc" (fun: "acc" <> "v" => "fn" "acc" "v").

Definition array_foldri_aux : val :=
  rec: "foldri_aux" "t" "fn" "acc" "i" =>
    if: "i" ≤ #0 then (
      "acc"
    ) else (
      let: "i" := "i" - #1 in
      let: "v" := array_unsafe_get "t" "i" in
      "foldri_aux" "t" "fn" ("fn" "i" "v" "acc") "i"
    ).

Definition array_foldri : val :=
  fun: "t" "fn" "acc" =>
    array_foldri_aux "t" "fn" "acc" (array_size "t").

Definition array_foldr : val :=
  fun: "t" "fn" "acc" =>
    array_foldri "t" (fun: <> => "fn") "acc".

Definition array_iteri : val :=
  fun: "t" "fn" =>
    for: "i" := #0 to array_size "t" begin
      "fn" "i" (array_unsafe_get "t" "i")
    end.

Definition array_iter : val :=
  fun: "t" "fn" =>
    array_iteri "t" (fun: <> => "fn").

Definition array_applyi : val :=
  fun: "t" "fn" =>
    array_iteri "t" (fun: "i" "v" => array_unsafe_set "t" "i" ("fn" "i" "v")).

Definition array_apply : val :=
  fun: "t" "fn" =>
    array_applyi "t" (fun: <> => "fn").

Definition array_unsafe_initi : val :=
  fun: "sz" "fn" =>
    let: "t" := array_unsafe_alloc "sz" in
    array_applyi "t" (fun: "i" <> => "fn" "i") ;;
    "t".

Definition array_initi : val :=
  fun: "sz" "fn" =>
    assume (#0 ≤ "sz") ;;
    array_unsafe_initi "sz" "fn".

Definition array_unsafe_init : val :=
  fun: "sz" "fn" =>
    array_unsafe_initi "sz" (fun: <> => "fn" ()).

Definition array_init : val :=
  fun: "sz" "fn" =>
    assume (#0 ≤ "sz") ;;
    array_unsafe_init "sz" "fn".

Definition array_mapi : val :=
  fun: "t" "fn" =>
    array_unsafe_initi
      (array_size "t")
      (fun: "i" => "fn" "i" (array_unsafe_get "t" "i")).

Definition array_map : val :=
  fun: "t" "fn" =>
    array_mapi "t" (fun: <> => "fn").

Definition array_unsafe_copy_slice : val :=
  fun: "t1" "i1" "t2" "i2" "n" =>
    for: "k" := #0 to "n" begin
      let: "v" := array_unsafe_get "t1" ("i1" + "k") in
      array_unsafe_set "t2" ("i2" + "k") "v"
    end.

Definition array_copy_slice : val :=
  fun: "t1" "i1" "t2" "i2" "n" =>
    let: "sz1" := array_size "t1" in
    let: "sz2" := array_size "t2" in
    assume (#0 ≤ "i1") ;;
    assume (#0 ≤ "i2") ;;
    assume (#0 ≤ "n") ;;
    assume ("i1" + "n" ≤ "sz1") ;;
    assume ("i2" + "n" ≤ "sz2") ;;
    array_unsafe_copy_slice "t1" "i1" "t2" "i2" "n".

Definition array_unsafe_copy : val :=
  fun: "t1" "t2" "i2" =>
    array_unsafe_copy_slice "t1" #0 "t2" "i2" (array_size "t1").

Definition array_copy : val :=
  fun: "t1" "t2" "i2" =>
    assume (#0 ≤ "i2") ;;
    assume ("i2" + array_size "t1" ≤ array_size "t2") ;;
    array_unsafe_copy "t1" "t2" "i2".

Definition array_unsafe_grow : val :=
  fun: "t" "sz'" "v'" =>
    let: "sz" := array_size "t" in
    let: "t'" := array_unsafe_alloc "sz'" in
    array_unsafe_copy "t" "t'" #0 ;;
    array_unsafe_fill_slice "t'" "sz" ("sz'" - "sz") "v'" ;;
    "t'".

Definition array_grow : val :=
  fun: "t" "sz'" "v'" =>
    assume (array_size "t" ≤ "sz'") ;;
    array_unsafe_grow "t" "sz'" "v'".

Definition array_unsafe_sub : val :=
  fun: "t" "i" "n" =>
    let: "t'" := array_unsafe_alloc "n" in
    array_unsafe_copy_slice "t" "i" "t'" #0 "n" ;;
    "t'".

Definition array_sub : val :=
  fun: "t" "i" "n" =>
    assume (#0 ≤ "i") ;;
    assume (#0 ≤ "n") ;;
    assume ("i" + "n" ≤ array_size "t") ;;
    array_unsafe_sub "t" "i" "n".

Definition array_unsafe_shrink : val :=
  fun: "t" "sz'" =>
    array_unsafe_sub "t" #0 "sz'".

Definition array_shrink : val :=
  fun: "t" "sz'" =>
    assume (#0 ≤ "sz'") ;;
    assume ("sz'" ≤ array_size "t") ;;
    array_unsafe_shrink "t" "sz'".

Definition array_clone : val :=
  fun: "t" =>
    array_unsafe_shrink "t" (array_size "t").

Definition array_unsafe_cget : val :=
  fun: "t" "i" =>
    array_unsafe_get "t" ("i" `rem` array_size "t").

Definition array_cget : val :=
  fun: "t" "i" =>
    assume (#0 ≤ "i") ;;
    assume (#0 < array_size "t") ;;
    array_unsafe_cget "t" "i".

Definition array_unsafe_cset : val :=
  fun: "t" "i" "v" =>
    array_unsafe_set "t" ("i" `rem` array_size "t") "v".

Definition array_cset : val :=
  fun: "t" "i" "v" =>
    assume (#0 ≤ "i") ;;
    assume (#0 < array_size "t") ;;
    array_unsafe_cset "t" "i" "v".

Definition array_unsafe_ccopy_slice : val :=
  fun: "t1" "i1" "t2" "i2" "n" =>
    for: "j" := #0 to "n" begin
      let: "v" := array_unsafe_cget "t1" ("i1" + "j") in
      array_unsafe_cset "t2" ("i2" + "j") "v"
    end.

Definition array_ccopy_slice : val :=
  fun: "t1" "i1" "t2" "i2" "n" =>
    assume (#0 ≤ "i1") ;;
    assume (#0 ≤ "i2") ;;
    assume (#0 ≤ "n") ;;
    let: "sz1" := array_size "t1" in
    let: "sz2" := array_size "t2" in
    assume (#0 < "sz1") ;;
    assume (#0 < "sz2") ;;
    assume ("n" ≤ "sz1") ;;
    assume ("n" ≤ "sz2") ;;
    array_unsafe_ccopy_slice "t1" "i1" "t2" "i2" "n".

Definition array_unsafe_ccopy : val :=
  fun: "t1" "i1" "t2" "i2" =>
    array_unsafe_ccopy_slice "t1" "i1" "t2" "i2" (array_size "t1").

Definition array_ccopy : val :=
  fun: "t1" "i1" "t2" "i2" =>
    assume (#0 ≤ "i1") ;;
    assume (#0 ≤ "i2") ;;
    let: "sz1" := array_size "t1" in
    let: "sz2" := array_size "t2" in
    assume (#0 < "sz1") ;;
    assume ("sz1" ≤ "sz2") ;;
    array_unsafe_ccopy "t1" "i1" "t2" "i2".
