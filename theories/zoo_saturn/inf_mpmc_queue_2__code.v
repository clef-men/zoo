From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  inf_array
  int
  optional
  domain.
From zoo Require Import
  identifier.
From zoo_saturn Require Import
  inf_mpmc_queue_2__types.
From zoo Require Import
  options.

Definition inf_mpmc_queue_2٠create : val :=
  fun: <> =>
    { inf_array٠create §Nothing, 0, 0, Proph }.

Definition inf_mpmc_queue_2٠size : val :=
  rec: "size" "t" =>
    let: "front" := "t".{front} in
    let: "proph" := Proph in
    let: "back" := "t".{back} in
    if:
      (let: "@tmp" := "t".{front} in
       Resolve Skip "proph" "@tmp" ;;
       "@tmp")
      ==
      "front"
    then (
      int٠positive_part ("back" - "front")
    ) else (
      "size" "t"
    ).

Definition inf_mpmc_queue_2٠is_empty : val :=
  fun: "t" =>
    inf_mpmc_queue_2٠size "t" == 0.

Definition inf_mpmc_queue_2٠push : val :=
  rec: "push" "t" "v" =>
    let: "id" := Id in
    let: "i" := FAA "t".[back] 1 in
    if:
      ~
      inf_array٠cas_resolve
        "t".{data}
        "i"
        §Nothing
        ‘Something( "v" )
        "t".{proph}
        ("i", "id")
    then (
      "push" "t" "v"
    ).

Definition inf_mpmc_queue_2٠pop : val :=
  rec: "pop" "t" =>
    let: "id" := Id in
    let: "i" := FAA "t".[front] 1 in
    match:
      inf_array٠xchg_resolve
        "t".{data}
        "i"
        §Anything
        "t".{proph}
        ("i", "id")
    with
    | Nothing =>
        domain٠yield () ;;
        "pop" "t"
    | Anything =>
        Fail
    | Something "v" =>
        "v"
    end.
