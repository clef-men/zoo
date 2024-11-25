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

Definition partition_block_iter : val :=
  fun: "fn" "block" =>
    partition_dllist_iter "fn" "block".{first} "block".{last}.

Definition partition_block_is_singleton : val :=
  fun: "block" =>
    "block".{len} == #1.

Definition partition_block_swap : val :=
  fun: "block" "cell1" "cell2" =>
    if: "cell1" != "cell2" then (
      let: "first" := "block".{first} in
      let: "last" := "block".{last} in
      if: "first" == "cell1" then (
        "block" <-{first} "cell2"
      ) else if: "first" == "cell2" then (
        "block" <-{first} "cell1"
      ) ;;
      if: "last" == "cell2" then (
        "block" <-{last} "cell1"
      ) else if: "last" == "cell1" then (
        "block" <-{last} "cell2"
      ) ;;
      partition_dllist_swap "cell1" "cell2"
    ).

Definition partition_block_record_split : val :=
  fun: "start_of_split_list" "cell" =>
    let: "block" := "cell".{class_} in
    if: partition_block_is_singleton "block" or "cell".{seen} then (
      "start_of_split_list"
    ) else (
      "cell" <-{seen} #true ;;
      let: "cur_split_start" := "block".{split_start} in
      if: "cur_split_start" == "block".{last} then (
        "block" <-{split_start} "block".{first} ;;
        "block" <-{split_len} #0 ;;
        "start_of_split_list"
      ) else (
        let: "never_split" := "cur_split_start" == "block".{first} in
        partition_block_swap "block" "cur_split_start" "cell" ;;
        "block" <-{split_start} "cell".{next} ;;
        "block" <-{split_len} "block".{split_len} + #1 ;;
        if: "never_split" then (
          match: "start_of_split_list" with
          | None =>
              ()
          | Some "list_head" =>
              "block" <-{next_split} "list_head"
          end ;;
          ‘Some( "block" )
        ) else (
          "start_of_split_list"
        )
      )
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
    let: "block" := { (), (), #true, "elt", "elt", #1, "elt", #0 } in
    "elt" <-{prev} "elt" ;;
    "elt" <-{next} "elt" ;;
    "elt" <-{class_} "block" ;;
    "block" <-{next_split} "block" ;;
    "block" <-{work_list_next} "block" ;;
    let: "t" := { "block", ‘Some( "block" ) } in
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
    let: "block" := { (), (), #true, "elt", "elt", #1, "elt", #0 } in
    "elt" <-{prev} "elt" ;;
    "elt" <-{next} "elt" ;;
    "elt" <-{class_} "block" ;;
    "block" <-{next_split} "block" ;;
    "block" <-{work_list_next}
      match: "t".{work_list_head} with
      | None =>
          "block"
      | Some "wl" =>
          "wl"
      end ;;
    "t" <-{blocks_head} "block" ;;
    "t" <-{work_list_head} ‘Some( "block" ) ;;
    "elt".

Definition partition_split_at : val :=
  fun: "elt_class" "t" =>
    let: "elt" := "elt_class".{split_start} in
    let: "elt_class_first" := "elt_class".{first} in
    if: "elt" == "elt_class_first" then (
      partition_block_iter
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
          (),
          #false,
          "elt_class_first",
          "old_prev",
          "elt_class_split_len",
          "elt_class_first",
          #0
        }
      in
      "class_descr" <-{next_split} "class_descr" ;;
      "class_descr" <-{work_list_next} "class_descr" ;;
      "t" <-{blocks_head} "class_descr" ;;
      if: "elt_class".{in_work_list} then (
        "class_descr" <-{in_work_list} #true ;;
        match: "t".{work_list_head} with
        | None =>
            Fail
        | Some "hd" =>
            "class_descr" <-{work_list_next} "hd"
        end ;;
        "t" <-{work_list_head} ‘Some( "class_descr" )
      ) else (
        let: "selected_class" :=
          if: "elt_class".{len} ≤ "class_descr".{len} then (
            "elt_class"
          ) else (
            "class_descr"
          )
        in
        "selected_class" <-{in_work_list} #true ;;
        match: "t".{work_list_head} with
        | None =>
            ()
        | Some "hd" =>
            "selected_class" <-{work_list_next} "hd"
        end ;;
        "t" <-{work_list_head} ‘Some( "selected_class" )
      ) ;;
      partition_dllist_iter
        (fun: "elt" => "elt" <-{class_} "class_descr" ;;
                       "elt" <-{seen} #false)
        "elt_class_first"
        "old_prev"
    ).

Definition partition_split_class : val :=
  fun: "class_" "t" =>
    partition_split_at "class_" "t" ;;
    "class_" <-{split_start} "class_".{first} ;;
    "class_" <-{next_split} "class_".

Definition partition_split_classes : val :=
  rec: "split_classes" "class_" "t" =>
    let: "next" := "class_".{next_split} in
    partition_split_class "class_" "t" ;;
    if: "next" != "class_" then (
      "split_classes" "next" "t"
    ).

Definition partition_refine : val :=
  fun: "t" "elts" =>
    match: lst_foldl partition_block_record_split §None "elts" with
    | None =>
        ()
    | Some "split_list" =>
        partition_split_classes "split_list" "t"
    end.
