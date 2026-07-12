Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.chain.
Require Import zoo_std.queue_1__types.
Require Import zoo.options.

Definition queue_1٠create : val :=
  fun: <> =>
    let: "front" := { (), () } in
    { "front", "front" }.

Definition queue_1٠is_empty : val :=
  fun: "t" =>
    "t".{front} == "t".{back}.

Definition queue_1٠push : val :=
  fun: "t" "v" =>
    let: "back" := "t".{back} in
    let: "new_back" := { (), () } in
    "back" <-{chain_next} "new_back" ;;
    "back" <-{chain_data} "v" ;;
    "t" <-{back} "new_back".

Definition queue_1٠pop : val :=
  fun: "t" =>
    if: queue_1٠is_empty "t" then (
      §None
    ) else (
      let: "front" := "t".{front} in
      "t" <-{front} "front".{chain_next} ;;
      let: "v" := "front".{chain_data} in
      ‘Some( "v" )
    ).
