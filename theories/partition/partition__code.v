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
    let: "cell" := { (), (), "v", "class_", #false } in
    "cell" <-{prev} "cell" ;;
    "cell" <-{next} "cell" ;;
    "cell".

Definition partition_dllist_link : val :=
  fun: "cell1" "cell2" =>
    "cell1" <-{next} "cell2" ;;
    "cell2" <-{prev} "cell1".

Definition partition_dllist_insert_right : val :=
  fun: "dst" "cell" =>
    partition_dllist_link "cell" "dst".{next} ;;
    partition_dllist_link "dst" "cell".

Definition partition_dllist_swap : val :=
  fun: "cell1" "cell2" =>
    if: "cell1" != "cell2" then (
      let: "prev1" := "cell1".{prev} in
      let: "next1" := "cell1".{next} in
      let: "prev2" := "cell2".{prev} in
      let: "next2" := "cell2".{next} in
      if: "next1" == "cell2" then (
        if: "next2" != "cell1" then (
          partition_dllist_link "cell1" "next2" ;;
          partition_dllist_link "cell2" "cell1" ;;
          partition_dllist_link "prev1" "cell2"
        )
      ) else if: "prev1" == "cell2" then (
        partition_dllist_link "prev2" "cell1" ;;
        partition_dllist_link "cell1" "cell2" ;;
        partition_dllist_link "cell2" "next1"
      ) else (
        partition_dllist_link "prev2" "cell1" ;;
        partition_dllist_link "cell1" "next2" ;;
        partition_dllist_link "cell2" "next1" ;;
        partition_dllist_link "prev1" "cell2"
      )
    ).

Definition partition_dllist_iter : val :=
  rec: "dllist_iter" "fn" "from" "to_" =>
    "fn" "from" ;;
    if: "from" != "to_" then (
      "dllist_iter" "fn" "from".{next} "to_"
    ).

Definition partition_class_iter : val :=
  fun: "fn" "class_" =>
    partition_dllist_iter "fn" "class_".{first} "class_".{last}.

Definition partition_class_is_singleton : val :=
  fun: "class_" =>
    "class_".{len} == #1.

Definition partition_class_swap : val :=
  fun: "class_" "cell1" "cell2" =>
    if: "cell1" != "cell2" then (
      let: "first" := "class_".{first} in
      let: "last" := "class_".{last} in
      if: "first" == "cell1" then (
        "class_" <-{first} "cell2"
      ) else if: "first" == "cell2" then (
        "class_" <-{first} "cell1"
      ) ;;
      if: "last" == "cell2" then (
        "class_" <-{last} "cell1"
      ) else if: "last" == "cell1" then (
        "class_" <-{last} "cell2"
      ) ;;
      partition_dllist_swap "cell1" "cell2"
    ).

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
    let: "class_" := { (), "elt", "elt", #1, "elt", #0 } in
    "elt" <-{prev} "elt" ;;
    "elt" <-{next} "elt" ;;
    "elt" <-{class_} "class_" ;;
    "class_" <-{next_split} "class_" ;;
    let: "t" := { "class_" } in
    ("t", "elt").

Definition partition_add_same_class : val :=
  fun: "elt" "v" =>
    let: "class_" := "elt".{class_} in
    let: "cell" := partition_dllist_create "v" "class_" in
    partition_dllist_insert_right "class_".{last} "cell" ;;
    "class_" <-{last} "cell" ;;
    "class_" <-{len} "class_".{len} + #1 ;;
    "cell".

Definition partition_add_new_class : val :=
  fun: "t" "v" =>
    let: "elt" := { (), (), "v", (), #false } in
    let: "class_" := { (), "elt", "elt", #1, "elt", #0 } in
    "elt" <-{prev} "elt" ;;
    "elt" <-{next} "elt" ;;
    "elt" <-{class_} "class_" ;;
    "class_" <-{next_split} "class_" ;;
    "t" <-{classes_head} "class_" ;;
    "elt".

Definition partition_record_split : val :=
  fun: "start_of_split_list" "cell" =>
    let: "class_" := "cell".{class_} in
    if: partition_class_is_singleton "class_" or "cell".{seen} then (
      "start_of_split_list"
    ) else (
      "cell" <-{seen} #true ;;
      let: "cur_split_start" := "class_".{split_start} in
      if: "cur_split_start" == "class_".{last} then (
        "class_" <-{split_start} "class_".{first} ;;
        "class_" <-{split_len} #0 ;;
        "start_of_split_list"
      ) else (
        let: "never_split" := "cur_split_start" == "class_".{first} in
        partition_class_swap "class_" "cur_split_start" "cell" ;;
        "class_" <-{split_start} "cell".{next} ;;
        "class_" <-{split_len} "class_".{split_len} + #1 ;;
        if: "never_split" then (
          match: "start_of_split_list" with
          | None =>
              ()
          | Some "list_head" =>
              "class_" <-{next_split} "list_head"
          end ;;
          ‘Some( "class_" )
        ) else (
          "start_of_split_list"
        )
      )
    ).

Definition partition_split_class : val :=
  fun: "elt_class" "t" =>
    let: "elt" := "elt_class".{split_start} in
    let: "elt_class_first" := "elt_class".{first} in
    if: "elt" == "elt_class_first" then (
      partition_class_iter
        (fun: "cell" => "cell" <-{seen} #false)
        "elt_class"
    ) else (
      let: "old_prev" := "elt".{prev} in
      "elt_class" <-{first} "elt" ;;
      "elt_class" <-{split_start} "elt" ;;
      let: "elt_class_split_len" := "elt_class".{split_len} in
      "elt_class" <-{split_len} #0 ;;
      "elt_class" <-{len} "elt_class".{len} - "elt_class_split_len" ;;
      let: "class_descr" :=
        { (),
          "elt_class_first",
          "old_prev",
          "elt_class_split_len",
          "elt_class_first",
          #0
        }
      in
      "class_descr" <-{next_split} "class_descr" ;;
      "t" <-{classes_head} "class_descr" ;;
      partition_dllist_iter
        (fun: "elt" => "elt" <-{class_} "class_descr" ;;
                       "elt" <-{seen} #false)
        "elt_class_first"
        "old_prev"
    ).

Definition partition_split_classes : val :=
  rec: "split_classes" "class_" "t" =>
    let: "next" := "class_".{next_split} in
    partition_split_class "class_" "t" ;;
    "class_" <-{split_start} "class_".{first} ;;
    "class_" <-{next_split} "class_" ;;
    if: "next" != "class_" then (
      "split_classes" "next" "t"
    ).

Definition partition_refine : val :=
  fun: "t" "elts" =>
    match: lst_foldl partition_record_split §None "elts" with
    | None =>
        ()
    | Some "split_list" =>
        partition_split_classes "split_list" "t"
    end.
