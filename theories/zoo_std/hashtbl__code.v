From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  random
  array.
From zoo_std Require Import
  hashtbl__types.
From zoo Require Import
  options.

Parameter hashtbl_min_buckets : val.

Parameter hashtbl_max_buckets : val.

Definition hashtbl_bucket_assoc : val :=
  rec: "bucket_assoc" "equal" "key" "bucket" =>
    match: "bucket" with
    | Nil =>
        §Nil
    | Cons "key'" <> "bucket'" as "bucket" =>
        if: "equal" "key" "key'" then (
          "bucket"
        ) else (
          "bucket_assoc" "equal" "key" "bucket'"
        )
    end.

Parameter hashtbl_bucket_dissoc : val.

Definition hashtbl_bucket_filter : val :=
  rec: "bucket_filter" "pred" "param" =>
    match: "param" with
    | Nil =>
        §Nil
    | Cons "key" "v" "bucket" =>
        if: "pred" "key" then (
          ‘Cons( "key", "v", "bucket_filter" "pred" "bucket" )
        ) else (
          "bucket_filter" "pred" "bucket"
        )
    end.

Definition hashtbl_bucket_merge : val :=
  rec: "bucket_merge" "bucket" "param" =>
    match: "param" with
    | Nil =>
        "bucket"
    | Cons "key" "v" "bucket" =>
        ‘Cons( "key", "v", "bucket_merge" "bucket" "bucket" )
    end.

Definition hashtbl_create : val :=
  fun: "hash" "equal" =>
    let: "buckets" := array_make hashtbl_min_buckets §Nil in
    let: "mask" := hashtbl_min_buckets - #1 in
    { "hash", "equal", "buckets", "mask", #0 }.

Definition hashtbl_index : val :=
  fun: "t" "key" =>
    "t".{hash} "key" `land` "t".{mask}.

Definition hashtbl_find_node : val :=
  fun: "t" "key" =>
    let: "i" := hashtbl_index "t" "key" in
    let: "bucket" := array_unsafe_get "t".{buckets} "i" in
    hashtbl_bucket_assoc "t".{equal} "key" "bucket".

Definition hashtbl_find : val :=
  fun: "t" "key" =>
    match: hashtbl_find_node "t" "key" with
    | Nil =>
        §None
    | Cons <> "v" <> =>
        ‘Some( "v" )
    end.

Definition hashtbl_mem : val :=
  fun: "t" "key" =>
    hashtbl_find_node "t" "key" != §Nil.

Definition hashtbl_resize_0 : val :=
  fun: "t" "cap" "new_cap" =>
    let: "new_buckets" := array_make "new_cap" §Nil in
    if: "cap" < "new_cap" then (
      for: "i" := #0 to "cap" begin
        let: "bucket" := array_unsafe_get "t".{buckets} "i" in
        let: "new_bucket_1" :=
          hashtbl_bucket_filter
            (fun: "key" => "t".{hash} "key" `land` "cap" == #0)
            "bucket"
        in
        let: "new_bucket_2" :=
          hashtbl_bucket_filter
            (fun: "key" => "t".{hash} "key" `land` "cap" == "cap")
            "bucket"
        in
        array_unsafe_set "new_buckets" "i" "new_bucket_1" ;;
        array_unsafe_set "new_buckets" ("i" + "cap") "new_bucket_2"
      end
    ) else (
      for: "i" := #0 to "new_cap" begin
        let: "bucket_1" := array_unsafe_get "t".{buckets} "i" in
        let: "bucket_2" :=
          array_unsafe_get "t".{buckets} ("i" + "new_cap")
        in
        let: "new_bucket" := hashtbl_bucket_merge "bucket_1" "bucket_2" in
        array_unsafe_set "new_buckets" "i" "new_bucket"
      end
    ) ;;
    "t" <-{buckets} "new_buckets" ;;
    "t" <-{mask} "new_cap" - #1.

Definition hashtbl_resize : val :=
  fun: "t" "delta" =>
    let: "sz" := "t".{size} in
    "t" <-{size} "sz" + "delta" ;;
    if: random_bits () `land` "t".{mask} == #0 then (
      let: "cap" := array_size "t".{buckets} in
      if: "cap" < "sz" and "cap" < hashtbl_max_buckets then (
        hashtbl_resize_0 "t" "cap" ("cap" `lsl` #1)
      ) else if: hashtbl_min_buckets < "cap" and #3 * "sz" < "cap" then (
        hashtbl_resize_0 "t" "cap" ("cap" `lsr` #1)
      )
    ).

Definition hashtbl_add : val :=
  fun: "t" "key" "v" =>
    let: "i" := hashtbl_index "t" "key" in
    let: "bucket" := array_unsafe_get "t".{buckets} "i" in
    if: hashtbl_bucket_assoc "t".{equal} "key" "bucket" != §Nil then (
      #false
    ) else (
      array_unsafe_set "t".{buckets} "i" ‘Cons( "key", "v", "bucket" ) ;;
      hashtbl_resize "t" #1 ;;
      #true
    ).

Definition hashtbl_remove : val :=
  fun: "t" "key" =>
    let: "i" := hashtbl_index "t" "key" in
    let: "bucket" := array_unsafe_get "t".{buckets} "i" in
    match: hashtbl_bucket_dissoc "t".{equal} "key" "bucket" with
    | None =>
        #false
    | Some "new_bucket" =>
        array_unsafe_set "t".{buckets} "i" "new_bucket" ;;
        hashtbl_resize "t" #(-1) ;;
        #true
    end.
