From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  list.
From zoo_partition Require Import
  partition__types.
From zoo Require Import
  options.

Definition partition٠dllist_create : val :=
  fun: "v" "class_" =>
    let: "elt" := { (), (), "v", "class_", false } in
    "elt" <-{prev} "elt" ;;
    "elt" <-{next} "elt" ;;
    "elt".

Definition partition٠dllist_link : val :=
  fun: "elt1" "elt2" =>
    "elt1" <-{next} "elt2" ;;
    "elt2" <-{prev} "elt1".

Definition partition٠dllist_insert_right : val :=
  fun: "dst" "elt" =>
    partition٠dllist_link "elt" "dst".{next} ;;
    partition٠dllist_link "dst" "elt".

Definition partition٠dllist_swap : val :=
  fun: "elt1" "elt2" =>
    if: "elt1" != "elt2" then (
      let: "prev1" := "elt1".{prev} in
      let: "next1" := "elt1".{next} in
      let: "prev2" := "elt2".{prev} in
      let: "next2" := "elt2".{next} in
      if: "next1" == "elt2" then (
        if: "next2" != "elt1" then (
          partition٠dllist_link "elt1" "next2" ;;
          partition٠dllist_link "elt2" "elt1" ;;
          partition٠dllist_link "prev1" "elt2"
        )
      ) else if: "prev1" == "elt2" then (
        partition٠dllist_link "prev2" "elt1" ;;
        partition٠dllist_link "elt1" "elt2" ;;
        partition٠dllist_link "elt2" "next1"
      ) else (
        partition٠dllist_link "prev2" "elt1" ;;
        partition٠dllist_link "elt1" "next2" ;;
        partition٠dllist_link "elt2" "next1" ;;
        partition٠dllist_link "prev1" "elt2"
      )
    ).

Definition partition٠dllist_iter : val :=
  rec: "dllist_iter" "fn" "from" "to_" =>
    "fn" "from" ;;
    if: "from" != "to_" then (
      "dllist_iter" "fn" "from".{next} "to_"
    ).

Definition partition٠class_is_singleton : val :=
  fun: "class_" =>
    "class_".{len} == 1.

Definition partition٠class_add : val :=
  fun: "class_" "elt" =>
    partition٠dllist_insert_right "class_".{last} "elt" ;;
    "class_" <-{last} "elt" ;;
    "class_" <-{len} "class_".{len} + 1.

Definition partition٠class_swap : val :=
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
      partition٠dllist_swap "elt1" "elt2"
    ).

Definition partition٠class_iter : val :=
  fun: "fn" "class_" =>
    partition٠dllist_iter "fn" "class_".{first} "class_".{last}.

Definition partition٠make : val :=
  fun: "v" =>
    let: "elt" := partition٠dllist_create "v" () in
    let: "class_" := { "elt", "elt", 1, "elt", 0 } in
    "elt" <-{class_} "class_" ;;
    "elt".

Definition partition٠make_same_class : val :=
  fun: "elt" "v" =>
    let: "class_" := "elt".{class_} in
    let: "elt" := partition٠dllist_create "v" "class_" in
    partition٠class_add "class_" "elt" ;;
    "elt".

Definition partition٠get : val :=
  fun: "elt" =>
    "elt".{data}.

Definition partition٠equal : val :=
  fun: "1" "2" =>
    "1" == "2".

Definition partition٠equiv : val :=
  fun: "elt1" "elt2" =>
    "elt1".{class_} == "elt2".{class_}.

Definition partition٠repr : val :=
  fun: "elt" =>
    "elt".{class_}.{first}.

Definition partition٠cardinal : val :=
  fun: "elt" =>
    "elt".{class_}.{len}.

Definition partition٠record₀ : val :=
  fun: "split_list" "elt" =>
    let: "class_" := "elt".{class_} in
    if: partition٠class_is_singleton "class_" or "elt".{seen} then (
      "split_list"
    ) else (
      "elt" <-{seen} true ;;
      let: "split" := "class_".{split} in
      if: "split" == "class_".{last} then (
        "class_" <-{split} "class_".{first} ;;
        "class_" <-{split_len} 0 ;;
        "split_list"
      ) else (
        let: "record_class" := "split" == "class_".{first} in
        partition٠class_swap "class_" "split" "elt" ;;
        "class_" <-{split} "elt".{next} ;;
        "class_" <-{split_len} "class_".{split_len} + 1 ;;
        if: "record_class" then (
          "class_" :: "split_list"
        ) else (
          "split_list"
        )
      )
    ).

Definition partition٠record : val :=
  fun: "elts" =>
    list٠foldl partition٠record₀ [] "elts".

Definition partition٠split₀ : val :=
  fun: "class_" =>
    let: "first" := "class_".{first} in
    let: "split" := "class_".{split} in
    if: "split" == "first" then (
      partition٠class_iter (fun: "elt" => "elt" <-{seen} false) "class_"
    ) else (
      "class_" <-{first} "split" ;;
      "class_" <-{split} "split" ;;
      let: "split_len" := "class_".{split_len} in
      "class_" <-{split_len} 0 ;;
      "class_" <-{len} "class_".{len} - "split_len" ;;
      let: "prev" := "split".{prev} in
      let: "class'" := { "first", "prev", "split_len", "first", 0 } in
      partition٠dllist_iter
        (fun: "elt" => "elt" <-{class_} "class'" ;;
                       "elt" <-{seen} false)
        "first"
        "prev"
    ).

Definition partition٠split : val :=
  fun: "split_list" =>
    list٠iter partition٠split₀ "split_list".

Definition partition٠refine : val :=
  fun: "elts" =>
    partition٠split (partition٠record "elts").
