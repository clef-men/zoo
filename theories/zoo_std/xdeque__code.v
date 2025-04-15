From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  xdeque__types.
From zoo Require Import
  options.

Definition xdeque_create : val :=
  fun: <> =>
    let: "t" := Alloc #0 #2 in
    "t" <-{xdeque_prev} "t" ;;
    "t" <-{xdeque_next} "t" ;;
    "t".

Definition xdeque_is_empty : val :=
  fun: "t" =>
    "t".{xdeque_next} == "t".

Definition xdeque_link : val :=
  fun: "node1" "node2" =>
    "node1" <-{xdeque_next} "node2" ;;
    "node2" <-{xdeque_prev} "node1".

Definition xdeque_insert : val :=
  fun: "prev" "node" "next" =>
    xdeque_link "prev" "node" ;;
    xdeque_link "node" "next".

Definition xdeque_push_front : val :=
  fun: "t" "front" =>
    xdeque_insert "t" "front" "t".{xdeque_next}.

Definition xdeque_push_back : val :=
  fun: "t" "back" =>
    xdeque_insert "t".{xdeque_prev} "back" "t".

Definition xdeque_pop_front : val :=
  fun: "t" =>
    if: xdeque_is_empty "t" then (
      §None
    ) else (
      let: "old_front" := "t".{xdeque_next} in
      let: "front" := "old_front".{xdeque_next} in
      xdeque_link "t" "front" ;;
      ‘Some( "old_front" )
    ).

Definition xdeque_pop_back : val :=
  fun: "t" =>
    if: xdeque_is_empty "t" then (
      §None
    ) else (
      let: "old_back" := "t".{xdeque_prev} in
      let: "back" := "old_back".{xdeque_prev} in
      xdeque_link "back" "t" ;;
      ‘Some( "old_back" )
    ).

Definition xdeque_remove : val :=
  fun: "node" =>
    let: "prev" := "node".{xdeque_prev} in
    let: "next" := "node".{xdeque_next} in
    xdeque_link "prev" "next".

Definition xdeque_iter_aux : val :=
  rec: "iter_aux" "fn" "t" "node" =>
    if: "node" == "t" then (
      ()
    ) else (
      "fn" "node" ;;
      "iter_aux" "fn" "t" "node".{xdeque_next}
    ).

Definition xdeque_iter : val :=
  fun: "fn" "t" =>
    xdeque_iter_aux "fn" "t" "t".{xdeque_next}.
