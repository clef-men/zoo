From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  mutex
  array
  int.
From zoo_std Require Import
  inf_array__types.
From zoo Require Import
  options.

Definition inf_array_create : val :=
  fun: "default" =>
    let: "data" := array_create () in
    let: "mutex" := mutex_create () in
    { "data", "default", "mutex" }.

Definition inf_array_next_capacity : val :=
  fun: "n" =>
    maximum
      #8
      if: "n" ≤ #512 then (
        #2 * "n"
      ) else (
        "n" + "n" `quot` #2
      ).

Definition inf_array_reserve : val :=
  fun: "t" "n" =>
    let: "data" := "t".{data} in
    let: "cap" := array_size "data" in
    if: "cap" < "n" then (
      let: "cap" := maximum "n" (inf_array_next_capacity "cap") in
      let: "data" := array_unsafe_grow "data" "cap" "t".{default} in
      "t" <-{data} "data"
    ).

Definition inf_array_get : val :=
  fun: "t" "i" =>
    mutex_protect "t".{mutex}
      (fun: <> =>
         let: "data" := "t".{data} in
         if: "i" < array_size "data" then (
           array_unsafe_get "data" "i"
         ) else (
           "t".{default}
         )).

Definition inf_array_set : val :=
  fun: "t" "i" "v" =>
    mutex_protect "t".{mutex}
      (fun: <> =>
         inf_array_reserve "t" ("i" + #1) ;;
         array_unsafe_set "t".{data} "i" "v").

Definition inf_array_xchg : val :=
  fun: "t" "i" "v" =>
    mutex_protect "t".{mutex}
      (fun: <> =>
         inf_array_reserve "t" ("i" + #1) ;;
         let: "v'" := array_unsafe_get "t".{data} "i" in
         array_unsafe_set "t".{data} "i" "v" ;;
         "v'").

Definition inf_array_cas : val :=
  fun: "t" "i" "v1" "v2" =>
    mutex_protect "t".{mutex}
      (fun: <> =>
         inf_array_reserve "t" ("i" + #1) ;;
         if: array_unsafe_get "t".{data} "i" != "v1" then (
           #false
         ) else (
           array_unsafe_set "t".{data} "i" "v2" ;;
           #true
         )).

Definition inf_array_faa : val :=
  fun: "t" "i" "incr" =>
    mutex_protect "t".{mutex}
      (fun: <> =>
         inf_array_reserve "t" ("i" + #1) ;;
         let: "n" := array_unsafe_get "t".{data} "i" in
         array_unsafe_set "t".{data} "i" ("n" + "incr") ;;
         "n").
