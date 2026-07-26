Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.list.
Require Import zoo_partition.partition__types.
Require Import zoo.options.

Definition partition٠dllist_create : val :=
  𝗳𝘂𝗻 "v" "class_" ->
    𝗹𝗲𝘁 "elt" = { (), (), "v", "class_", false } 𝗶𝗻
    "elt" <-{prev} "elt" ⍮
    "elt" <-{next} "elt" ⍮
    "elt".

Definition partition٠dllist_link : val :=
  𝗳𝘂𝗻 "elt1" "elt2" ->
    "elt1" <-{next} "elt2" ⍮
    "elt2" <-{prev} "elt1".

Definition partition٠dllist_insert_right : val :=
  𝗳𝘂𝗻 "dst" "elt" ->
    partition٠dllist_link "elt" "dst".{next} ⍮
    partition٠dllist_link "dst" "elt".

Definition partition٠dllist_swap : val :=
  𝗳𝘂𝗻 "elt1" "elt2" ->
    𝗶𝗳 "elt1" != "elt2" 𝘁𝗵𝗲𝗻 (
      𝗹𝗲𝘁 "prev1" = "elt1".{prev} 𝗶𝗻
      𝗹𝗲𝘁 "next1" = "elt1".{next} 𝗶𝗻
      𝗹𝗲𝘁 "prev2" = "elt2".{prev} 𝗶𝗻
      𝗹𝗲𝘁 "next2" = "elt2".{next} 𝗶𝗻
      𝗶𝗳 "next1" == "elt2" 𝘁𝗵𝗲𝗻 (
        𝗶𝗳 "next2" != "elt1" 𝘁𝗵𝗲𝗻 (
          partition٠dllist_link "elt1" "next2" ⍮
          partition٠dllist_link "elt2" "elt1" ⍮
          partition٠dllist_link "prev1" "elt2"
        )
      ) 𝗲𝗹𝘀𝗲 𝗶𝗳 "prev1" == "elt2" 𝘁𝗵𝗲𝗻 (
        partition٠dllist_link "prev2" "elt1" ⍮
        partition٠dllist_link "elt1" "elt2" ⍮
        partition٠dllist_link "elt2" "next1"
      ) 𝗲𝗹𝘀𝗲 (
        partition٠dllist_link "prev2" "elt1" ⍮
        partition٠dllist_link "elt1" "next2" ⍮
        partition٠dllist_link "elt2" "next1" ⍮
        partition٠dllist_link "prev1" "elt2"
      )
    ).

Definition partition٠dllist_iter : val :=
  𝗿𝗲𝗰 "dllist_iter" "fn" "from" "to_" ->
    "fn" "from" ⍮
    𝗶𝗳 "from" != "to_" 𝘁𝗵𝗲𝗻 (
      "dllist_iter" "fn" "from".{next} "to_"
    ).

Definition partition٠class_is_singleton : val :=
  𝗳𝘂𝗻 "class_" ->
    "class_".{len} == 1.

Definition partition٠class_add : val :=
  𝗳𝘂𝗻 "class_" "elt" ->
    partition٠dllist_insert_right "class_".{last} "elt" ⍮
    "class_" <-{last} "elt" ⍮
    "class_" <-{len} "class_".{len} + 1.

Definition partition٠class_swap : val :=
  𝗳𝘂𝗻 "class_" "elt1" "elt2" ->
    𝗶𝗳 "elt1" != "elt2" 𝘁𝗵𝗲𝗻 (
      𝗹𝗲𝘁 "first" = "class_".{first} 𝗶𝗻
      𝗹𝗲𝘁 "last" = "class_".{last} 𝗶𝗻
      𝗶𝗳 "first" == "elt1" 𝘁𝗵𝗲𝗻 (
        "class_" <-{first} "elt2"
      ) 𝗲𝗹𝘀𝗲 𝗶𝗳 "first" == "elt2" 𝘁𝗵𝗲𝗻 (
        "class_" <-{first} "elt1"
      ) ⍮
      𝗶𝗳 "last" == "elt2" 𝘁𝗵𝗲𝗻 (
        "class_" <-{last} "elt1"
      ) 𝗲𝗹𝘀𝗲 𝗶𝗳 "last" == "elt1" 𝘁𝗵𝗲𝗻 (
        "class_" <-{last} "elt2"
      ) ⍮
      partition٠dllist_swap "elt1" "elt2"
    ).

Definition partition٠class_iter : val :=
  𝗳𝘂𝗻 "fn" "class_" ->
    partition٠dllist_iter "fn" "class_".{first} "class_".{last}.

Definition partition٠make : val :=
  𝗳𝘂𝗻 "v" ->
    𝗹𝗲𝘁 "elt" = partition٠dllist_create "v" () 𝗶𝗻
    𝗹𝗲𝘁 "class_" = { "elt", "elt", 1, "elt", 0 } 𝗶𝗻
    "elt" <-{class_} "class_" ⍮
    "elt".

Definition partition٠make_same_class : val :=
  𝗳𝘂𝗻 "elt" "v" ->
    𝗹𝗲𝘁 "class_" = "elt".{class_} 𝗶𝗻
    𝗹𝗲𝘁 "elt" = partition٠dllist_create "v" "class_" 𝗶𝗻
    partition٠class_add "class_" "elt" ⍮
    "elt".

Definition partition٠get : val :=
  𝗳𝘂𝗻 "elt" ->
    "elt".{data}.

Definition partition٠equal : val :=
  𝗳𝘂𝗻 "1" "2" ->
    "1" == "2".

Definition partition٠equiv : val :=
  𝗳𝘂𝗻 "elt1" "elt2" ->
    "elt1".{class_} == "elt2".{class_}.

Definition partition٠repr : val :=
  𝗳𝘂𝗻 "elt" ->
    "elt".{class_}.{first}.

Definition partition٠cardinal : val :=
  𝗳𝘂𝗻 "elt" ->
    "elt".{class_}.{len}.

Definition partition٠record₀ : val :=
  𝗳𝘂𝗻 "split_list" "elt" ->
    𝗹𝗲𝘁 "class_" = "elt".{class_} 𝗶𝗻
    𝗶𝗳
      partition٠class_is_singleton "class_" 𝗼𝗿 "elt".{seen}
    𝘁𝗵𝗲𝗻 (
      "split_list"
    ) 𝗲𝗹𝘀𝗲 (
      "elt" <-{seen} true ⍮
      𝗹𝗲𝘁 "split" = "class_".{split} 𝗶𝗻
      𝗶𝗳 "split" == "class_".{last} 𝘁𝗵𝗲𝗻 (
        "class_" <-{split} "class_".{first} ⍮
        "class_" <-{split_len} 0 ⍮
        "split_list"
      ) 𝗲𝗹𝘀𝗲 (
        𝗹𝗲𝘁 "record_class" = "split" == "class_".{first} 𝗶𝗻
        partition٠class_swap "class_" "split" "elt" ⍮
        "class_" <-{split} "elt".{next} ⍮
        "class_" <-{split_len} "class_".{split_len} + 1 ⍮
        𝗶𝗳 "record_class" 𝘁𝗵𝗲𝗻 (
          "class_" :: "split_list"
        ) 𝗲𝗹𝘀𝗲 (
          "split_list"
        )
      )
    ).

Definition partition٠record : val :=
  𝗳𝘂𝗻 "elts" ->
    list٠foldl partition٠record₀ [] "elts".

Definition partition٠split₀ : val :=
  𝗳𝘂𝗻 "class_" ->
    𝗹𝗲𝘁 "first" = "class_".{first} 𝗶𝗻
    𝗹𝗲𝘁 "split" = "class_".{split} 𝗶𝗻
    𝗶𝗳 "split" == "first" 𝘁𝗵𝗲𝗻 (
      partition٠class_iter
        (𝗳𝘂𝗻 "elt" -> "elt" <-{seen} false)
        "class_"
    ) 𝗲𝗹𝘀𝗲 (
      "class_" <-{first} "split" ⍮
      "class_" <-{split} "split" ⍮
      𝗹𝗲𝘁 "split_len" = "class_".{split_len} 𝗶𝗻
      "class_" <-{split_len} 0 ⍮
      "class_" <-{len} "class_".{len} - "split_len" ⍮
      𝗹𝗲𝘁 "prev" = "split".{prev} 𝗶𝗻
      𝗹𝗲𝘁 "class'" =
        { "first", "prev", "split_len", "first", 0 }
      𝗶𝗻
      partition٠dllist_iter
        (𝗳𝘂𝗻 "elt" ->
           "elt" <-{class_} "class'" ⍮
           "elt" <-{seen} false)
        "first"
        "prev"
    ).

Definition partition٠split : val :=
  𝗳𝘂𝗻 "split_list" ->
    list٠iter partition٠split₀ "split_list".

Definition partition٠refine : val :=
  𝗳𝘂𝗻 "elts" ->
    partition٠split (partition٠record "elts").
