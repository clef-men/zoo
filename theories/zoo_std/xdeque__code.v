Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.xdeque__types.
Require Import zoo.options.

Definition xdeque٠create : val :=
  fun: <> =>
    let: "t" := { (), (), () } in
    "t" <-{xdeque_prev} "t" ;;
    "t" <-{xdeque_next} "t" ;;
    "t".

Definition xdeque٠is_empty : val :=
  fun: "t" =>
    "t".{xdeque_next} == "t".

Definition xdeque٠link : val :=
  fun: "node1" "node2" =>
    "node1" <-{xdeque_next} "node2" ;;
    "node2" <-{xdeque_prev} "node1".

Definition xdeque٠insert : val :=
  fun: "prev" "node" "next" =>
    xdeque٠link "prev" "node" ;;
    xdeque٠link "node" "next".

Definition xdeque٠push_front : val :=
  fun: "t" "front" =>
    xdeque٠insert "t" "front" "t".{xdeque_next}.

Definition xdeque٠push_back : val :=
  fun: "t" "back" =>
    xdeque٠insert "t".{xdeque_prev} "back" "t".

Definition xdeque٠pop_front : val :=
  fun: "t" =>
    if: xdeque٠is_empty "t" then (
      §None
    ) else (
      let: "old_front" := "t".{xdeque_next} in
      let: "front" := "old_front".{xdeque_next} in
      xdeque٠link "t" "front" ;;
      ‘Some( "old_front" )
    ).

Definition xdeque٠pop_back : val :=
  fun: "t" =>
    if: xdeque٠is_empty "t" then (
      §None
    ) else (
      let: "old_back" := "t".{xdeque_prev} in
      let: "back" := "old_back".{xdeque_prev} in
      xdeque٠link "back" "t" ;;
      ‘Some( "old_back" )
    ).

Definition xdeque٠remove : val :=
  fun: "node" =>
    let: "prev" := "node".{xdeque_prev} in
    let: "next" := "node".{xdeque_next} in
    xdeque٠link "prev" "next".

Definition xdeque٠iter_aux : val :=
  rec: "iter_aux" "fn" "t" "node" =>
    if: "node" == "t" then (
      ()
    ) else (
      "fn" "node" ;;
      "iter_aux" "fn" "t" "node".{xdeque_next}
    ).

Definition xdeque٠iter : val :=
  fun: "fn" "t" =>
    xdeque٠iter_aux "fn" "t" "t".{xdeque_next}.
