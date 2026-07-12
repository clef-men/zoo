Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.assume.
Require Import zoo_std.array__types.
Require Import zoo.options.

Definition array٠unsafe_alloc : val :=
  fun: "sz" =>
    Alloc 0 "sz".

Definition array٠alloc : val :=
  fun: "sz" =>
    assume (0 ≤ "sz") ;;
    array٠unsafe_alloc "sz".

Definition array٠create : val :=
  fun: <> =>
    array٠unsafe_alloc 0.

Definition array٠size : val :=
  fun: "t" =>
    GetSize "t".

Definition array٠unsafe_get : val :=
  fun: "t" "i" =>
    Load "t" "i".

Definition array٠get : val :=
  fun: "t" "i" =>
    assume (0 ≤ "i") ;;
    assume ("i" < array٠size "t") ;;
    array٠unsafe_get "t" "i".

Definition array٠unsafe_set : val :=
  fun: "t" "i" "v" =>
    Store "t" "i" "v".

Definition array٠set : val :=
  fun: "t" "i" "v" =>
    assume (0 ≤ "i") ;;
    assume ("i" < array٠size "t") ;;
    array٠unsafe_set "t" "i" "v".

Definition array٠unsafe_swap : val :=
  fun: "t" "i1" "i2" =>
    let: "v1" := array٠unsafe_get "t" "i1" in
    let: "v2" := array٠unsafe_get "t" "i2" in
    array٠unsafe_set "t" "i1" "v2" ;;
    array٠unsafe_set "t" "i2" "v1".

Definition array٠unsafe_fill_slice : val :=
  fun: "t" "i" "n" "v" =>
    for: "j" := 0 to "n" begin
      array٠unsafe_set "t" ("i" + "j") "v"
    end.

Definition array٠fill_slice : val :=
  fun: "t" "i" "n" "v" =>
    let: "sz" := array٠size "t" in
    assume (0 ≤ "i") ;;
    assume (0 ≤ "n") ;;
    assume ("i" + "n" ≤ "sz") ;;
    array٠unsafe_fill_slice "t" "i" "n" "v".

Definition array٠fill : val :=
  fun: "t" "v" =>
    array٠unsafe_fill_slice "t" 0 (array٠size "t") "v".

Definition array٠unsafe_make : val :=
  fun: "sz" "v" =>
    let: "t" := array٠unsafe_alloc "sz" in
    array٠fill "t" "v" ;;
    "t".

Definition array٠make : val :=
  fun: "sz" "v" =>
    assume (0 ≤ "sz") ;;
    array٠unsafe_make "sz" "v".

Definition array٠foldli_aux : val :=
  rec: "foldli_aux" "fn" "t" "sz" "i" "acc" =>
    if: "sz" ≤ "i" then (
      "acc"
    ) else (
      let: "v" := array٠unsafe_get "t" "i" in
      "foldli_aux" "fn" "t" "sz" ("i" + 1) ("fn" "i" "acc" "v")
    ).

Definition array٠foldli : val :=
  fun: "fn" "acc" "t" =>
    array٠foldli_aux "fn" "t" (array٠size "t") 0 "acc".

Definition array٠foldl : val :=
  fun: "fn" =>
    array٠foldli (fun: "_i" => "fn").

Definition array٠foldri_aux : val :=
  rec: "foldri_aux" "fn" "t" "i" "acc" =>
    if: "i" ≤ 0 then (
      "acc"
    ) else (
      let: "i" := "i" - 1 in
      let: "v" := array٠unsafe_get "t" "i" in
      "foldri_aux" "fn" "t" "i" ("fn" "i" "v" "acc")
    ).

Definition array٠foldri : val :=
  fun: "fn" "t" "acc" =>
    array٠foldri_aux "fn" "t" (array٠size "t") "acc".

Definition array٠foldr : val :=
  fun: "fn" =>
    array٠foldri (fun: "_i" => "fn").

Definition array٠sum : val :=
  fun: "t" =>
    array٠foldl (fun: "1" "2" => "1" + "2") 0 "t".

Definition array٠unsafe_iteri_slice : val :=
  fun: "fn" "t" "i" "n" =>
    for: "k" := 0 to "n" begin
      "fn" "k" (array٠unsafe_get "t" ("i" + "k"))
    end.

Definition array٠iteri_slice : val :=
  fun: "fn" "t" "i" "n" =>
    assume (0 ≤ "i") ;;
    assume (0 ≤ "n") ;;
    let: "sz" := array٠size "t" in
    assume ("i" ≤ "sz") ;;
    assume ("i" + "n" ≤ "sz") ;;
    array٠unsafe_iteri_slice "fn" "t" "i" "n".

Definition array٠unsafe_iter_slice : val :=
  fun: "fn" =>
    array٠unsafe_iteri_slice (fun: "_i" => "fn").

Definition array٠iter_slice : val :=
  fun: "fn" "t" "i" "n" =>
    assume (0 ≤ "i") ;;
    assume (0 ≤ "n") ;;
    let: "sz" := array٠size "t" in
    assume ("i" ≤ "sz") ;;
    assume ("i" + "n" ≤ "sz") ;;
    array٠unsafe_iter_slice "fn" "t" "i" "n".

Definition array٠iteri : val :=
  fun: "fn" "t" =>
    array٠unsafe_iteri_slice "fn" "t" 0 (array٠size "t").

Definition array٠iter : val :=
  fun: "fn" =>
    array٠iteri (fun: "_i" => "fn").

Definition array٠unsafe_applyi_slice : val :=
  fun: "fn" "t" "i" "n" =>
    array٠unsafe_iteri_slice
      (fun: "k" "v" => array٠unsafe_set "t" ("i" + "k") ("fn" "k" "v"))
      "t"
      "i"
      "n".

Definition array٠applyi_slice : val :=
  fun: "fn" "t" "i" "n" =>
    assume (0 ≤ "i") ;;
    assume (0 ≤ "n") ;;
    let: "sz" := array٠size "t" in
    assume ("i" ≤ "sz") ;;
    assume ("i" + "n" ≤ "sz") ;;
    array٠unsafe_applyi_slice "fn" "t" "i" "n".

Definition array٠unsafe_apply_slice : val :=
  fun: "fn" =>
    array٠unsafe_applyi_slice (fun: "_i" => "fn").

Definition array٠apply_slice : val :=
  fun: "fn" "t" "i" "n" =>
    assume (0 ≤ "i") ;;
    assume (0 ≤ "n") ;;
    let: "sz" := array٠size "t" in
    assume ("i" ≤ "sz") ;;
    assume ("i" + "n" ≤ "sz") ;;
    array٠unsafe_apply_slice "fn" "t" "i" "n".

Definition array٠applyi : val :=
  fun: "fn" "t" =>
    array٠unsafe_applyi_slice "fn" "t" 0 (array٠size "t").

Definition array٠apply : val :=
  fun: "fn" =>
    array٠applyi (fun: "_i" => "fn").

Definition array٠unsafe_initi : val :=
  fun: "sz" "fn" =>
    let: "t" := array٠unsafe_alloc "sz" in
    array٠applyi (fun: "i" <> => "fn" "i") "t" ;;
    "t".

Definition array٠initi : val :=
  fun: "sz" "fn" =>
    assume (0 ≤ "sz") ;;
    array٠unsafe_initi "sz" "fn".

Definition array٠unsafe_init : val :=
  fun: "sz" "fn" =>
    array٠unsafe_initi "sz" (fun: "_i" => "fn" ()).

Definition array٠init : val :=
  fun: "sz" "fn" =>
    assume (0 ≤ "sz") ;;
    array٠unsafe_init "sz" "fn".

Definition array٠mapi : val :=
  fun: "fn" "t" =>
    array٠unsafe_initi
      (array٠size "t")
      (fun: "i" => "fn" "i" (array٠unsafe_get "t" "i")).

Definition array٠map : val :=
  fun: "fn" =>
    array٠mapi (fun: "_i" => "fn").

Definition array٠unsafe_copy_slice : val :=
  fun: "t1" "i1" "t2" "i2" "n" =>
    for: "k" := 0 to "n" begin
      let: "v" := array٠unsafe_get "t1" ("i1" + "k") in
      array٠unsafe_set "t2" ("i2" + "k") "v"
    end.

Definition array٠copy_slice : val :=
  fun: "t1" "i1" "t2" "i2" "n" =>
    let: "sz1" := array٠size "t1" in
    let: "sz2" := array٠size "t2" in
    assume (0 ≤ "i1") ;;
    assume (0 ≤ "i2") ;;
    assume (0 ≤ "n") ;;
    assume ("i1" + "n" ≤ "sz1") ;;
    assume ("i2" + "n" ≤ "sz2") ;;
    array٠unsafe_copy_slice "t1" "i1" "t2" "i2" "n".

Definition array٠unsafe_copy : val :=
  fun: "t1" "t2" "i2" =>
    array٠unsafe_copy_slice "t1" 0 "t2" "i2" (array٠size "t1").

Definition array٠copy : val :=
  fun: "t1" "t2" "i2" =>
    assume (0 ≤ "i2") ;;
    assume ("i2" + array٠size "t1" ≤ array٠size "t2") ;;
    array٠unsafe_copy "t1" "t2" "i2".

Definition array٠unsafe_grow : val :=
  fun: "t" "sz'" "v'" =>
    let: "sz" := array٠size "t" in
    let: "t'" := array٠unsafe_alloc "sz'" in
    array٠unsafe_copy "t" "t'" 0 ;;
    array٠unsafe_fill_slice "t'" "sz" ("sz'" - "sz") "v'" ;;
    "t'".

Definition array٠grow : val :=
  fun: "t" "sz'" "v'" =>
    assume (array٠size "t" ≤ "sz'") ;;
    array٠unsafe_grow "t" "sz'" "v'".

Definition array٠unsafe_sub : val :=
  fun: "t" "i" "n" =>
    let: "t'" := array٠unsafe_alloc "n" in
    array٠unsafe_copy_slice "t" "i" "t'" 0 "n" ;;
    "t'".

Definition array٠sub : val :=
  fun: "t" "i" "n" =>
    assume (0 ≤ "i") ;;
    assume (0 ≤ "n") ;;
    assume ("i" + "n" ≤ array٠size "t") ;;
    array٠unsafe_sub "t" "i" "n".

Definition array٠unsafe_shrink : val :=
  fun: "t" "sz'" =>
    array٠unsafe_sub "t" 0 "sz'".

Definition array٠shrink : val :=
  fun: "t" "sz'" =>
    assume (0 ≤ "sz'") ;;
    assume ("sz'" ≤ array٠size "t") ;;
    array٠unsafe_shrink "t" "sz'".

Definition array٠clone : val :=
  fun: "t" =>
    array٠unsafe_shrink "t" (array٠size "t").

Definition array٠unsafe_cget : val :=
  fun: "t" "i" =>
    array٠unsafe_get "t" ("i" `rem` array٠size "t").

Definition array٠cget : val :=
  fun: "t" "i" =>
    assume (0 ≤ "i") ;;
    assume (0 < array٠size "t") ;;
    array٠unsafe_cget "t" "i".

Definition array٠unsafe_cset : val :=
  fun: "t" "i" "v" =>
    array٠unsafe_set "t" ("i" `rem` array٠size "t") "v".

Definition array٠cset : val :=
  fun: "t" "i" "v" =>
    assume (0 ≤ "i") ;;
    assume (0 < array٠size "t") ;;
    array٠unsafe_cset "t" "i" "v".

Definition array٠unsafe_ccopy_slice₀ : val :=
  fun: "t1" "i1" "t2" "i2" "n" =>
    let: "sz2" := array٠size "t2" in
    let: "i2" := "i2" `rem` "sz2" in
    if: "i2" + "n" ≤ "sz2" then (
      array٠unsafe_copy_slice "t1" "i1" "t2" "i2" "n"
    ) else (
      let: "n1" := "sz2" - "i2" in
      let: "n2" := "n" - "n1" in
      array٠unsafe_copy_slice "t1" "i1" "t2" "i2" "n1" ;;
      array٠unsafe_copy_slice "t1" ("i1" + "n1") "t2" 0 "n2"
    ).

Definition array٠unsafe_ccopy_slice : val :=
  fun: "t1" "i1" "t2" "i2" "n" =>
    let: "sz1" := array٠size "t1" in
    let: "i1" := "i1" `rem` "sz1" in
    if: "i1" + "n" ≤ "sz1" then (
      array٠unsafe_ccopy_slice₀ "t1" "i1" "t2" "i2" "n"
    ) else (
      let: "n1" := "sz1" - "i1" in
      let: "n2" := "n" - "n1" in
      array٠unsafe_ccopy_slice₀ "t1" "i1" "t2" "i2" "n1" ;;
      array٠unsafe_ccopy_slice₀ "t1" 0 "t2" ("i2" + "n1") "n2"
    ).

Definition array٠ccopy_slice : val :=
  fun: "t1" "i1" "t2" "i2" "n" =>
    assume (0 ≤ "i1") ;;
    assume (0 ≤ "i2") ;;
    assume (0 ≤ "n") ;;
    let: "sz1" := array٠size "t1" in
    let: "sz2" := array٠size "t2" in
    assume (0 < "sz1") ;;
    assume (0 < "sz2") ;;
    assume ("n" ≤ "sz1") ;;
    assume ("n" ≤ "sz2") ;;
    array٠unsafe_ccopy_slice "t1" "i1" "t2" "i2" "n".

Definition array٠unsafe_ccopy : val :=
  fun: "t1" "i1" "t2" "i2" =>
    array٠unsafe_ccopy_slice "t1" "i1" "t2" "i2" (array٠size "t1").

Definition array٠ccopy : val :=
  fun: "t1" "i1" "t2" "i2" =>
    assume (0 ≤ "i1") ;;
    assume (0 ≤ "i2") ;;
    let: "sz1" := array٠size "t1" in
    let: "sz2" := array٠size "t2" in
    assume (0 < "sz1") ;;
    assume ("sz1" ≤ "sz2") ;;
    array٠unsafe_ccopy "t1" "i1" "t2" "i2".

Definition array٠unsafe_cgrow_slice : val :=
  fun: "t" "i" "n" "sz'" "v" =>
    let: "t'" := array٠unsafe_make "sz'" "v" in
    array٠unsafe_ccopy_slice "t" "i" "t'" "i" "n" ;;
    "t'".

Definition array٠unsafe_cgrow : val :=
  fun: "t" "i" "sz'" "v" =>
    array٠unsafe_cgrow_slice "t" "i" (array٠size "t") "sz'" "v".

Definition array٠unsafe_cshrink_slice : val :=
  fun: "t" "i" "sz'" =>
    let: "t'" := array٠unsafe_alloc "sz'" in
    array٠unsafe_ccopy_slice "t" "i" "t'" "i" "sz'" ;;
    "t'".
