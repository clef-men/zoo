Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.array.
Require Import zoo_std.bqueue__types.
Require Import zoo.options.

Definition bqueue٠create : val :=
  fun: "cap" =>
    { "cap", array٠unsafe_make "cap" (), 0, 0 }.

Definition bqueue٠size : val :=
  fun: "t" =>
    "t".{back} - "t".{front}.

Definition bqueue٠is_empty : val :=
  fun: "t" =>
    bqueue٠size "t" == 0.

Definition bqueue٠unsafe_get : val :=
  fun: "t" "i" =>
    array٠unsafe_cget "t".{data} ("t".{front} + "i").

Definition bqueue٠unsafe_set : val :=
  fun: "t" "i" "v" =>
    array٠unsafe_cset "t".{data} ("t".{front} + "i") "v".

Definition bqueue٠push : val :=
  fun: "t" "v" =>
    let: "front" := "t".{front} in
    let: "back" := "t".{back} in
    if: "front" + "t".{capacity} == "back" then (
      false
    ) else (
      array٠unsafe_cset "t".{data} "back" "v" ;;
      "t" <-{back} "back" + 1 ;;
      true
    ).

Definition bqueue٠pop_front : val :=
  fun: "t" =>
    let: "front" := "t".{front} in
    let: "back" := "t".{back} in
    if: "front" == "back" then (
      §None
    ) else (
      let: "data" := "t".{data} in
      let: "v" := array٠unsafe_cget "data" "front" in
      array٠unsafe_cset "data" "front" () ;;
      "t" <-{front} "front" + 1 ;;
      ‘Some( "v" )
    ).

Definition bqueue٠pop_back : val :=
  fun: "t" =>
    let: "front" := "t".{front} in
    let: "back" := "t".{back} in
    if: "front" == "back" then (
      §None
    ) else (
      let: "data" := "t".{data} in
      let: "back" := "back" - 1 in
      let: "v" := array٠unsafe_cget "data" "back" in
      array٠unsafe_cset "data" "back" () ;;
      "t" <-{back} "back" ;;
      ‘Some( "v" )
    ).
