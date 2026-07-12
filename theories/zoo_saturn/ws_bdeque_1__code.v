Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.array.
Require Import zoo_std.domain.
Require Import zoo.program_logic.identifier.
Require Import zoo_saturn.ws_bdeque_1__types.
Require Import zoo.options.

Definition ws_bdeque_1٠create : val :=
  fun: "cap" =>
    { "cap", 1, 1, 1, array٠unsafe_make "cap" (), Proph }.

Definition ws_bdeque_1٠capacity : val :=
  fun: "t" =>
    "t".{capacity}.

Definition ws_bdeque_1٠size : val :=
  fun: "t" =>
    "t".{back} - "t".{front}.

Definition ws_bdeque_1٠is_empty : val :=
  fun: "t" =>
    ws_bdeque_1٠size "t" == 0.

Definition ws_bdeque_1٠front_cached : val :=
  fun: "t" =>
    let: "front" := "t".{front} in
    "t" <-{front_cache} "front" ;;
    "front".

Definition ws_bdeque_1٠push : val :=
  fun: "t" "v" =>
    let: "back" := "t".{back} in
    let: "data" := "t".{data} in
    let: "cap" := array٠size "data" in
    let: "front" := "t".{front_cache} in
    if:
      "back" < "front" + "cap" or "front" < ws_bdeque_1٠front_cached "t"
    then (
      array٠unsafe_cset "data" "back" "v" ;;
      "t" <-{back} "back" + 1 ;;
      true
    ) else (
      false
    ).

Definition ws_bdeque_1٠steal : val :=
  rec: "steal" "t" =>
    let: "id" := Id in
    let: "front" := "t".{front} in
    let: "back" := "t".{back} in
    if: "back" ≤ "front" then (
      §None
    ) else (
      let: "data" := "t".{data} in
      let: "v" := array٠unsafe_cget "data" "front" in
      if:
        Resolve
          (CAS "t".[front] "front" ("front" + 1))
          "t".{proph}
          ("front", "id")
      then (
        ‘Some( "v" )
      ) else (
        domain٠yield () ;;
        "steal" "t"
      )
    ).

Definition ws_bdeque_1٠pop₀ : val :=
  fun: "t" "id" "back" =>
    let: "front" := "t".{front} in
    if: "back" < "front" then (
      "t" <-{back} "front" ;;
      §None
    ) else if: "front" < "back" then (
      ‘Some( array٠unsafe_cget "t".{data} "back" )
    ) else (
      "t" <-{front_cache} "front" + 1 ;;
      let: "won" :=
        Resolve
          (CAS "t".[front] "front" ("front" + 1))
          "t".{proph}
          ("front", "id")
      in
      "t" <-{back} "front" + 1 ;;
      if: "won" then (
        ‘Some( array٠unsafe_cget "t".{data} "front" )
      ) else (
        §None
      )
    ).

Definition ws_bdeque_1٠pop : val :=
  fun: "t" =>
    let: "id" := Id in
    let: "back" := "t".{back} - 1 in
    "t" <-{back} "back" ;;
    ws_bdeque_1٠pop₀ "t" "id" "back".
