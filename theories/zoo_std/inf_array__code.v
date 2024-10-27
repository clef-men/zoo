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

Definition inf_array_get : val :=
  fun: "t" "i" =>
    mutex_protect
      "t".{mutex}
      (fun: <> =>
         let: "data" := "t".{data} in
         if: "i" < array_size "data" then (
           array_unsafe_get "data" "i"
         ) else (
           "t".{default}
         )).

Definition inf_array_set : val :=
  fun: "t" "i" "v" =>
    mutex_protect
      "t".{mutex}
      (fun: <> =>
         let: "data" := "t".{data} in
         let: "sz" := array_size "data" in
         if: "i" < "sz" then (
           array_unsafe_set "data" "i" "v"
         ) else (
           let: "data" :=
             array_unsafe_grow
               "data"
               (maximum ("i" + #1) (#2 * "sz"))
               "t".{default}
           in
           array_unsafe_set "data" "i" "v" ;;
           "t" <-{data} "data"
         )).
