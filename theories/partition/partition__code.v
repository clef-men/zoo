From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  lst.
From partition Require Import
  partition__types.
From zoo Require Import
  options.

Definition partition_dllist_create : val :=
  fun: "v" "class_" =>
    let: "elt" := { (), (), "v", "class_", #false } in
    "elt" <-{prev} "elt" ;;
    "elt" <-{next} "elt" ;;
    "elt".

Definition partition_dllist_link : val :=
  fun: "elt1" "elt2" =>
    "elt1" <-{next} "elt2" ;;
    "elt2" <-{prev} "elt1".

Definition partition_dllist_insert_right : val :=
  fun: "dst" "elt" =>
    partition_dllist_link "elt" "dst".{next} ;;
    partition_dllist_link "dst" "elt".

Definition partition_dllist_swap : val :=
  fun: "elt1" "elt2" =>
    if: "elt1" != "elt2" then (
      let: "prev1" := "elt1".{prev} in
      let: "next1" := "elt1".{next} in
      let: "prev2" := "elt2".{prev} in
      let: "next2" := "elt2".{next} in
      if: "next1" == "elt2" then (
        if: "next2" != "elt1" then (
          partition_dllist_link "elt1" "next2" ;;
          partition_dllist_link "elt2" "elt1" ;;
          partition_dllist_link "prev1" "elt2"
        )
      ) else if: "prev1" == "elt2" then (
        partition_dllist_link "prev2" "elt1" ;;
        partition_dllist_link "elt1" "elt2" ;;
        partition_dllist_link "elt2" "next1"
      ) else (
        partition_dllist_link "prev2" "elt1" ;;
        partition_dllist_link "elt1" "next2" ;;
        partition_dllist_link "elt2" "next1" ;;
        partition_dllist_link "prev1" "elt2"
      )
    ).

Definition partition_dllist_iter : val :=
  rec: "dllist_iter" "fn" "from" "to_" =>
    "fn" "from" ;;
    if: "from" != "to_" then (
      "dllist_iter" "fn" "from".{next} "to_"
    ).

Definition partition_class_is_singleton : val :=
  fun: "class_" =>
    "class_".{len} == #1.

Definition partition_class_swap : val :=
  fun: "class_" "elt1" "elt2" =>
    if: "elt1" != "elt2" then (
      let: "first" := "class_".{first} in
      let: "last" := "class_".{last} in
      if: "first" == "elt1" then (
        "class_" <-{first} "elt2"
      ) else if: "first" == "elt2" then (
        "class_" <-{first} "elt1"
      ) ;;
      if: "last" == "elt2" then (
        "class_" <-{last} "elt1"
      ) else if: "last" == "elt1" then (
        "class_" <-{last} "elt2"
      ) ;;
      partition_dllist_swap "elt1" "elt2"
    ).

Definition partition_class_iter : val :=
  fun: "fn" "class_" =>
    partition_dllist_iter "fn" "class_".{first} "class_".{last}.

Definition partition_elt_equal : val :=
  fun: "1" "2" =>
    "1" == "2".

Definition partition_elt_equiv : val :=
  fun: "elt1" "elt2" =>
    "elt1".{class_} == "elt2".{class_}.

Definition partition_elt_repr : val :=
  fun: "elt" =>
    "elt".{class_}.{first}.

Definition partition_elt_get : val :=
  fun: "elt" =>
    "elt".{data}.

Definition partition_elt_cardinal : val :=
  fun: "elt" =>
    "elt".{class_}.{len}.

Definition partition_create : val :=
  fun: "v" =>
    let: "elt" := { (), (), "v", (), #false } in
    let: "class_" := { "elt", "elt", #1, "elt", #0 } in
    "elt" <-{prev} "elt" ;;
    "elt" <-{next} "elt" ;;
    "elt" <-{class_} "class_" ;;
    "elt".

Definition partition_add_same_class : val :=
  fun: "elt" "v" =>
    let: "class_" := "elt".{class_} in
    let: "elt" := partition_dllist_create "v" "class_" in
    partition_dllist_insert_right "class_".{last} "elt" ;;
    "class_" <-{last} "elt" ;;
    "class_" <-{len} "class_".{len} + #1 ;;
    "elt".

Definition partition_add_new_class : val :=
  fun: "v" =>
    let: "elt" := { (), (), "v", (), #false } in
    let: "class_" := { "elt", "elt", #1, "elt", #0 } in
    "elt" <-{prev} "elt" ;;
    "elt" <-{next} "elt" ;;
    "elt" <-{class_} "class_" ;;
    "elt".

Definition partition_record_split : val :=
  fun: "split_list" "elt" =>
    let: "class_" := "elt".{class_} in
    if: partition_class_is_singleton "class_" or "elt".{seen} then (
      "split_list"
    ) else (
      "elt" <-{seen} #true ;;
      let: "split_start" := "class_".{split_start} in
      if: "split_start" == "class_".{last} then (
        "class_" <-{split_start} "class_".{first} ;;
        "class_" <-{split_len} #0 ;;
        "split_list"
      ) else (
        let: "never_split" := "split_start" == "class_".{first} in
        partition_class_swap "class_" "split_start" "elt" ;;
        "class_" <-{split_start} "elt".{next} ;;
        "class_" <-{split_len} "class_".{split_len} + #1 ;;
        if: "never_split" then (
          "class_" :: "split_list"
        ) else (
          "split_list"
        )
      )
    ).

Definition partition_split_class : val :=
  fun: "class_" =>
    let: "first" := "class_".{first} in
    let: "split_start" := "class_".{split_start} in
    if: "split_start" == "first" then (
      partition_class_iter (fun: "elt" => "elt" <-{seen} #false) "class_"
    ) else (
      "class_" <-{first} "split_start" ;;
      "class_" <-{split_start} "split_start" ;;
      let: "split_len" := "class_".{split_len} in
      "class_" <-{split_len} #0 ;;
      "class_" <-{len} "class_".{len} - "split_len" ;;
      let: "prev" := "split_start".{prev} in
      let: "class'" := { "first", "prev", "split_len", "first", #0 } in
      partition_dllist_iter
        (fun: "elt" => "elt" <-{class_} "class'" ;;
                       "elt" <-{seen} #false)
        "first"
        "prev"
    ).

Definition partition_refine : val :=
  fun: "elts" =>
    lst_iter partition_split_class
      (lst_foldl partition_record_split [] "elts").
