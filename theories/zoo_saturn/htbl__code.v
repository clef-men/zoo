From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  atomic_array
  random
  domain.
From zoo_saturn Require Import
  htbl__types.
From zoo Require Import
  options.

Parameter htbl_min_buckets : val.

Parameter htbl_max_buckets : val.

Definition htbl_bucket_assoc : val :=
  rec: "bucket_assoc" "equal" "key" "bucket" =>
    match: "bucket" with
    | Init =>
        Fail
    | Nil =>
        §Nil
    | Cons "key'" <> "bucket'" as "bucket" =>
        if: "equal" "key" "key'" then (
          "bucket"
        ) else (
          "bucket_assoc" "equal" "key" "bucket'"
        )
    | Resize "bucket" =>
        "bucket_assoc" "equal" "key" "bucket"
    end.

Parameter htbl_bucket_dissoc : val.

Definition htbl_bucket_filter : val :=
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
    |_ =>
        Fail
    end.

Definition htbl_bucket_merge : val :=
  rec: "bucket_merge" "bucket" "param" =>
    match: "param" with
    | Nil =>
        "bucket"
    | Cons "key" "v" "bucket" =>
        ‘Cons( "key", "v", "bucket_merge" "bucket" "bucket" )
    |_ =>
        Fail
    end.

Definition htbl_create : val :=
  fun: "hash" "equal" =>
    let: "sizes" :=
      atomic_array_make (domain_recommended_domain_count ()) #0
    in
    let: "state" :=
      (atomic_array_make htbl_min_buckets §Nil,
       htbl_min_buckets - #1,
       §Normal
      )
    in
    { "hash", "equal", "sizes", "state" }.

Definition htbl_index : val :=
  fun: "t" "state" "key" =>
    "t".{hash} "key" `land` "state".<mask>.

Definition htbl_find_node : val :=
  fun: "t" "key" =>
    let: "state" := "t".{state} in
    let: "i" := htbl_index "t" "state" "key" in
    let: "bucket" := atomic_array_unsafe_get "state".<buckets> "i" in
    htbl_bucket_assoc "t".{equal} "key" "bucket".

Definition htbl_find : val :=
  fun: "t" "key" =>
    match: htbl_find_node "t" "key" with
    | Nil =>
        §None
    | Cons <> "v" <> =>
        ‘Some( "v" )
    |_ =>
        Fail
    end.

Definition htbl_mem : val :=
  fun: "t" "key" =>
    htbl_find_node "t" "key" != §Nil.

Definition htbl_take : val :=
  rec: "take" "buckets" "i" =>
    match: atomic_array_unsafe_get "buckets" "i" with
    | Init =>
        Fail
    | Resize "bucket" =>
        "bucket"
    |_ as "bucket" =>
        if:
          atomic_array_unsafe_cas
            "buckets"
            "i"
            "bucket"
            ‘Resize( "bucket" )
        then (
          "bucket"
        ) else (
          domain_yield () ;;
          "take" "buckets" "i"
        )
    end.

Definition htbl_split_buckets : val :=
  rec: "split_buckets" "t" "state" "buckets" "mask" "i" "step" =>
    let: "i" := ("i" + "step") `land` "mask" in
    let: "bucket" := htbl_take "state".<buckets> "i" in
    let: "cap" := atomic_array_size "state".<buckets> in
    let: "new_bucket_1" :=
      htbl_bucket_filter
        (fun: "key" => "t".{hash} "key" `land` "cap" == #0)
        "bucket"
    in
    let: "new_bucket_2" :=
      htbl_bucket_filter
        (fun: "key" => "t".{hash} "key" `land` "cap" == "cap")
        "bucket"
    in
    if: "t".{state} != "state" then (
      #false
    ) else (
      if: atomic_array_unsafe_get "buckets" "i" == §Init then (
        atomic_array_unsafe_cas "buckets" "i" §Init "new_bucket_1" ;;
        ()
      ) else (
        ()
      ) ;;
      if: atomic_array_unsafe_get "buckets" ("i" + "cap") == §Init then (
        atomic_array_unsafe_cas "buckets" ("i" + "cap") §Init "new_bucket_2" ;;
        ()
      ) else (
        ()
      ) ;;
      "i" == #0 or "split_buckets" "t" "state" "buckets" "mask" "i" "step"
    ).

Definition htbl_merge_buckets : val :=
  rec: "merge_buckets" "t" "state" "buckets" "mask" "i" "step" =>
    let: "i" := ("i" + "step") `land` "mask" in
    let: "bucket_1" := htbl_take "state".<buckets> "i" in
    let: "bucket_2" :=
      htbl_take "state".<buckets> ("i" + atomic_array_size "buckets")
    in
    let: "new_bucket" := htbl_bucket_merge "bucket_1" "bucket_2" in
    if: "t".{state} != "state" then (
      #false
    ) else (
      if: atomic_array_unsafe_get "buckets" "i" == §Init then (
        atomic_array_unsafe_cas "buckets" "i" §Init "new_bucket" ;;
        ()
      ) else (
        ()
      ) ;;
      "i" == #0 or "merge_buckets" "t" "state" "buckets" "mask" "i" "step"
    ).

#[local] Definition __zoo_recs_0 := (
  recs: "finish_as" "t" "state" =>
    match: "state".<status> with
    | Normal =>
        ()
    | Resizing "buckets" "mask" =>
        if:
          let: "cap" := atomic_array_size "state".<buckets> in
          let: "new_cap" := atomic_array_size "buckets" in
          let: "step" := random_bits () `lor` #1 in
          if: "cap" < "new_cap" then (
            htbl_split_buckets "t" "state" "buckets" "mask" #0 "step"
          ) else (
            htbl_merge_buckets "t" "state" "buckets" "mask" #0 "step"
          )
        then (
          let: "new_state" := ("buckets", "mask", §Normal) in
          if: ~ CAS "t".[state] "state" "new_state" then (
            "finish" "t"
          ) else (
            "finish" "t"
          )
        )
    end
  and: "finish" "t" =>
    "finish_as" "t" "t".{state}
)%zoo_recs.
Definition htbl_finish_as :=
  ValRecs 0 __zoo_recs_0.
Definition htbl_finish :=
  ValRecs 1 __zoo_recs_0.
#[global] Instance :
  AsValRecs' htbl_finish_as 0 __zoo_recs_0 [
    htbl_finish_as ;
    htbl_finish
  ].
Proof.
  done.
Qed.
#[global] Instance :
  AsValRecs' htbl_finish 1 __zoo_recs_0 [
    htbl_finish_as ;
    htbl_finish
  ].
Proof.
  done.
Qed.

Definition htbl_resize_0 : val :=
  fun: "t" "state" "new_cap" =>
    let: "new_buckets" := atomic_array_make "new_cap" §Init in
    let: "new_status" := ‘Resizing( "new_buckets", "new_cap" - #1 ) in
    let: "new_state" := ("state".<buckets>, "state".<mask>, "new_status") in
    if: CAS "t".[state] "state" "new_state" then (
      htbl_finish_as "t" "new_state"
    ).

Definition htbl_resize : val :=
  fun: "t" "state" "delta" =>
    let: "i" := domain_self_index () `rem` atomic_array_size "t".{sizes} in
    atomic_array_unsafe_faa "t".{sizes} "i" "delta" ;;
    if:
      "state".<status> == §Normal
      and
      (random_bits () `land` "state".<mask> == #0 and "t".{state} == "state")
    then (
      let: "sz" := atomic_array_sum "t".{sizes} in
      let: "cap" := atomic_array_size "state".<buckets> in
      if: "cap" < "sz" and "cap" < htbl_max_buckets then (
        htbl_resize_0 "t" "state" ("cap" `lsl` #1)
      ) else if: htbl_min_buckets < "cap" and #3 * "sz" < "cap" then (
        htbl_resize_0 "t" "state" ("cap" `lsr` #1)
      )
    ).

Definition htbl_add : val :=
  rec: "add" "t" "key" "v" =>
    let: "state" := "t".{state} in
    let: "i" := htbl_index "t" "state" "key" in
    match: atomic_array_unsafe_get "state".<buckets> "i" with
    | Init =>
        Fail
    | Resize <> =>
        htbl_finish "t" ;;
        "add" "t" "key" "v"
    |_ as "bucket" =>
        if: htbl_bucket_assoc "t".{equal} "key" "bucket" != §Nil then (
          #false
        ) else if:
           atomic_array_unsafe_cas
             "state".<buckets>
             "i"
             "bucket"
             ‘Cons( "key", "v", "bucket" )
         then (
          htbl_resize "t" "state" #1 ;;
          #true
        ) else (
          domain_yield () ;;
          "add" "t" "key" "v"
        )
    end.

Definition htbl_remove : val :=
  rec: "remove" "t" "key" =>
    let: "state" := "t".{state} in
    let: "i" := htbl_index "t" "state" "key" in
    match: atomic_array_unsafe_get "state".<buckets> "i" with
    | Init =>
        Fail
    | Resize <> =>
        htbl_finish "t" ;;
        "remove" "t" "key"
    |_ as "bucket" =>
        match: htbl_bucket_dissoc "t".{equal} "key" "bucket" with
        | None =>
            #false
        | Some "new_bucket" =>
            if:
              atomic_array_unsafe_cas
                "state".<buckets>
                "i"
                "bucket"
                "new_bucket"
            then (
              htbl_resize "t" "state" #(-1) ;;
              #true
            ) else (
              domain_yield () ;;
              "remove" "t" "key"
            )
        end
    end.
