From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  assume.
From zoo_std Require Import
  array__types.
From zoo Require Import
  options.

Definition array_unsafe_alloc : val :=
  fun: "sz" =>
    Alloc 0 "sz".

Definition array_alloc : val :=
  fun: "sz" =>
    assume (0 ≤ "sz") ;;
    array_unsafe_alloc "sz".

Definition array_create : val :=
  fun: <> =>
    array_unsafe_alloc 0.

Definition array_size : val :=
  fun: "t" =>
    GetSize "t".

Definition array_unsafe_get : val :=
  fun: "t" "i" =>
    Load "t" "i".

Definition array_get : val :=
  fun: "t" "i" =>
    assume (0 ≤ "i") ;;
    assume ("i" < array_size "t") ;;
    array_unsafe_get "t" "i".

Definition array_unsafe_set : val :=
  fun: "t" "i" "v" =>
    Store "t" "i" "v".

Definition array_set : val :=
  fun: "t" "i" "v" =>
    assume (0 ≤ "i") ;;
    assume ("i" < array_size "t") ;;
    array_unsafe_set "t" "i" "v".

Definition array_unsafe_fill_slice : val :=
  fun: "t" "i" "n" "v" =>
    for: "j" := 0 to "n" begin
      array_unsafe_set "t" ("i" + "j") "v"
    end.

Definition array_fill_slice : val :=
  fun: "t" "i" "n" "v" =>
    let: "sz" := array_size "t" in
    assume (0 ≤ "i") ;;
    assume (0 ≤ "n") ;;
    assume ("i" + "n" ≤ "sz") ;;
    array_unsafe_fill_slice "t" "i" "n" "v".

Definition array_fill : val :=
  fun: "t" "v" =>
    array_unsafe_fill_slice "t" 0 (array_size "t") "v".

Definition array_unsafe_make : val :=
  fun: "sz" "v" =>
    let: "t" := array_unsafe_alloc "sz" in
    array_fill "t" "v" ;;
    "t".

Definition array_make : val :=
  fun: "sz" "v" =>
    assume (0 ≤ "sz") ;;
    array_unsafe_make "sz" "v".

Definition array_foldli_aux : val :=
  rec: "foldli_aux" "fn" "t" "sz" "i" "acc" =>
    if: "sz" ≤ "i" then (
      "acc"
    ) else (
      let: "v" := array_unsafe_get "t" "i" in
      "foldli_aux" "fn" "t" "sz" ("i" + 1) ("fn" "i" "acc" "v")
    ).

Definition array_foldli : val :=
  fun: "fn" "acc" "t" =>
    array_foldli_aux "fn" "t" (array_size "t") 0 "acc".

Definition array_foldl : val :=
  fun: "fn" =>
    array_foldli (fun: "_i" => "fn").

Definition array_foldri_aux : val :=
  rec: "foldri_aux" "fn" "t" "i" "acc" =>
    if: "i" ≤ 0 then (
      "acc"
    ) else (
      let: "i" := "i" - 1 in
      let: "v" := array_unsafe_get "t" "i" in
      "foldri_aux" "fn" "t" "i" ("fn" "i" "v" "acc")
    ).

Definition array_foldri : val :=
  fun: "fn" "t" "acc" =>
    array_foldri_aux "fn" "t" (array_size "t") "acc".

Definition array_foldr : val :=
  fun: "fn" =>
    array_foldri (fun: "_i" => "fn").

Definition array_sum : val :=
  fun: "t" =>
    array_foldl (fun: "1" "2" => "1" + "2") 0 "t".

Definition array_unsafe_iteri_slice : val :=
  fun: "fn" "t" "i" "n" =>
    for: "k" := 0 to "n" begin
      "fn" "k" (array_unsafe_get "t" ("i" + "k"))
    end.

Definition array_iteri_slice : val :=
  fun: "fn" "t" "i" "n" =>
    assume (0 ≤ "i") ;;
    assume (0 ≤ "n") ;;
    let: "sz" := array_size "t" in
    assume ("i" ≤ "sz") ;;
    assume ("i" + "n" ≤ "sz") ;;
    array_unsafe_iteri_slice "fn" "t" "i" "n".

Definition array_unsafe_iter_slice : val :=
  fun: "fn" =>
    array_unsafe_iteri_slice (fun: "_i" => "fn").

Definition array_iter_slice : val :=
  fun: "fn" "t" "i" "n" =>
    assume (0 ≤ "i") ;;
    assume (0 ≤ "n") ;;
    let: "sz" := array_size "t" in
    assume ("i" ≤ "sz") ;;
    assume ("i" + "n" ≤ "sz") ;;
    array_unsafe_iter_slice "fn" "t" "i" "n".

Definition array_iteri : val :=
  fun: "fn" "t" =>
    array_unsafe_iteri_slice "fn" "t" 0 (array_size "t").

Definition array_iter : val :=
  fun: "fn" =>
    array_iteri (fun: "_i" => "fn").

Definition array_unsafe_applyi_slice : val :=
  fun: "fn" "t" "i" "n" =>
    array_unsafe_iteri_slice
      (fun: "k" "v" => array_unsafe_set "t" ("i" + "k") ("fn" "k" "v"))
      "t"
      "i"
      "n".

Definition array_applyi_slice : val :=
  fun: "fn" "t" "i" "n" =>
    assume (0 ≤ "i") ;;
    assume (0 ≤ "n") ;;
    let: "sz" := array_size "t" in
    assume ("i" ≤ "sz") ;;
    assume ("i" + "n" ≤ "sz") ;;
    array_unsafe_applyi_slice "fn" "t" "i" "n".

Definition array_unsafe_apply_slice : val :=
  fun: "fn" =>
    array_unsafe_applyi_slice (fun: "_i" => "fn").

Definition array_apply_slice : val :=
  fun: "fn" "t" "i" "n" =>
    assume (0 ≤ "i") ;;
    assume (0 ≤ "n") ;;
    let: "sz" := array_size "t" in
    assume ("i" ≤ "sz") ;;
    assume ("i" + "n" ≤ "sz") ;;
    array_unsafe_apply_slice "fn" "t" "i" "n".

Definition array_applyi : val :=
  fun: "fn" "t" =>
    array_unsafe_applyi_slice "fn" "t" 0 (array_size "t").

Definition array_apply : val :=
  fun: "fn" =>
    array_applyi (fun: "_i" => "fn").

Definition array_unsafe_initi : val :=
  fun: "sz" "fn" =>
    let: "t" := array_unsafe_alloc "sz" in
    array_applyi (fun: "i" <> => "fn" "i") "t" ;;
    "t".

Definition array_initi : val :=
  fun: "sz" "fn" =>
    assume (0 ≤ "sz") ;;
    array_unsafe_initi "sz" "fn".

Definition array_unsafe_init : val :=
  fun: "sz" "fn" =>
    array_unsafe_initi "sz" (fun: "_i" => "fn" ()).

Definition array_init : val :=
  fun: "sz" "fn" =>
    assume (0 ≤ "sz") ;;
    array_unsafe_init "sz" "fn".

Definition array_mapi : val :=
  fun: "fn" "t" =>
    array_unsafe_initi
      (array_size "t")
      (fun: "i" => "fn" "i" (array_unsafe_get "t" "i")).

Definition array_map : val :=
  fun: "fn" =>
    array_mapi (fun: "_i" => "fn").

Definition array_unsafe_copy_slice : val :=
  fun: "t1" "i1" "t2" "i2" "n" =>
    for: "k" := 0 to "n" begin
      let: "v" := array_unsafe_get "t1" ("i1" + "k") in
      array_unsafe_set "t2" ("i2" + "k") "v"
    end.

Definition array_copy_slice : val :=
  fun: "t1" "i1" "t2" "i2" "n" =>
    let: "sz1" := array_size "t1" in
    let: "sz2" := array_size "t2" in
    assume (0 ≤ "i1") ;;
    assume (0 ≤ "i2") ;;
    assume (0 ≤ "n") ;;
    assume ("i1" + "n" ≤ "sz1") ;;
    assume ("i2" + "n" ≤ "sz2") ;;
    array_unsafe_copy_slice "t1" "i1" "t2" "i2" "n".

Definition array_unsafe_copy : val :=
  fun: "t1" "t2" "i2" =>
    array_unsafe_copy_slice "t1" 0 "t2" "i2" (array_size "t1").

Definition array_copy : val :=
  fun: "t1" "t2" "i2" =>
    assume (0 ≤ "i2") ;;
    assume ("i2" + array_size "t1" ≤ array_size "t2") ;;
    array_unsafe_copy "t1" "t2" "i2".

Definition array_unsafe_grow : val :=
  fun: "t" "sz'" "v'" =>
    let: "sz" := array_size "t" in
    let: "t'" := array_unsafe_alloc "sz'" in
    array_unsafe_copy "t" "t'" 0 ;;
    array_unsafe_fill_slice "t'" "sz" ("sz'" - "sz") "v'" ;;
    "t'".

Definition array_grow : val :=
  fun: "t" "sz'" "v'" =>
    assume (array_size "t" ≤ "sz'") ;;
    array_unsafe_grow "t" "sz'" "v'".

Definition array_unsafe_sub : val :=
  fun: "t" "i" "n" =>
    let: "t'" := array_unsafe_alloc "n" in
    array_unsafe_copy_slice "t" "i" "t'" 0 "n" ;;
    "t'".

Definition array_sub : val :=
  fun: "t" "i" "n" =>
    assume (0 ≤ "i") ;;
    assume (0 ≤ "n") ;;
    assume ("i" + "n" ≤ array_size "t") ;;
    array_unsafe_sub "t" "i" "n".

Definition array_unsafe_shrink : val :=
  fun: "t" "sz'" =>
    array_unsafe_sub "t" 0 "sz'".

Definition array_shrink : val :=
  fun: "t" "sz'" =>
    assume (0 ≤ "sz'") ;;
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
    assume (0 ≤ "i") ;;
    assume (0 < array_size "t") ;;
    array_unsafe_cget "t" "i".

Definition array_unsafe_cset : val :=
  fun: "t" "i" "v" =>
    array_unsafe_set "t" ("i" `rem` array_size "t") "v".

Definition array_cset : val :=
  fun: "t" "i" "v" =>
    assume (0 ≤ "i") ;;
    assume (0 < array_size "t") ;;
    array_unsafe_cset "t" "i" "v".

Definition array_unsafe_ccopy_slice_0 : val :=
  fun: "t1" "i1" "t2" "i2" "n" =>
    let: "sz2" := array_size "t2" in
    let: "i2" := "i2" `rem` "sz2" in
    if: "i2" + "n" ≤ "sz2" then (
      array_unsafe_copy_slice "t1" "i1" "t2" "i2" "n"
    ) else (
      let: "n1" := "sz2" - "i2" in
      let: "n2" := "n" - "n1" in
      array_unsafe_copy_slice "t1" "i1" "t2" "i2" "n1" ;;
      array_unsafe_copy_slice "t1" ("i1" + "n1") "t2" 0 "n2"
    ).

Definition array_unsafe_ccopy_slice : val :=
  fun: "t1" "i1" "t2" "i2" "n" =>
    let: "sz1" := array_size "t1" in
    let: "i1" := "i1" `rem` "sz1" in
    if: "i1" + "n" ≤ "sz1" then (
      array_unsafe_ccopy_slice_0 "t1" "i1" "t2" "i2" "n"
    ) else (
      let: "n1" := "sz1" - "i1" in
      let: "n2" := "n" - "n1" in
      array_unsafe_ccopy_slice_0 "t1" "i1" "t2" "i2" "n1" ;;
      array_unsafe_ccopy_slice_0 "t1" 0 "t2" ("i2" + "n1") "n2"
    ).

Definition array_ccopy_slice : val :=
  fun: "t1" "i1" "t2" "i2" "n" =>
    assume (0 ≤ "i1") ;;
    assume (0 ≤ "i2") ;;
    assume (0 ≤ "n") ;;
    let: "sz1" := array_size "t1" in
    let: "sz2" := array_size "t2" in
    assume (0 < "sz1") ;;
    assume (0 < "sz2") ;;
    assume ("n" ≤ "sz1") ;;
    assume ("n" ≤ "sz2") ;;
    array_unsafe_ccopy_slice "t1" "i1" "t2" "i2" "n".

Definition array_unsafe_ccopy : val :=
  fun: "t1" "i1" "t2" "i2" =>
    array_unsafe_ccopy_slice "t1" "i1" "t2" "i2" (array_size "t1").

Definition array_ccopy : val :=
  fun: "t1" "i1" "t2" "i2" =>
    assume (0 ≤ "i1") ;;
    assume (0 ≤ "i2") ;;
    let: "sz1" := array_size "t1" in
    let: "sz2" := array_size "t2" in
    assume (0 < "sz1") ;;
    assume ("sz1" ≤ "sz2") ;;
    array_unsafe_ccopy "t1" "i1" "t2" "i2".

Definition array_unsafe_cgrow_slice : val :=
  fun: "t" "i" "n" "sz'" "v" =>
    let: "t'" := array_unsafe_make "sz'" "v" in
    array_unsafe_ccopy_slice "t" "i" "t'" "i" "n" ;;
    "t'".

Definition array_unsafe_cgrow : val :=
  fun: "t" "i" "sz'" "v" =>
    array_unsafe_cgrow_slice "t" "i" (array_size "t") "sz'" "v".

Definition array_unsafe_cshrink_slice : val :=
  fun: "t" "i" "sz'" =>
    let: "t'" := array_unsafe_alloc "sz'" in
    array_unsafe_ccopy_slice "t" "i" "t'" "i" "sz'" ;;
    "t'".
