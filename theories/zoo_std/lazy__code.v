From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  mutex.
From zoo_std Require Import
  lazy__types.
From zoo Require Import
  options.

Definition lazy٠make : val :=
  fun: "fn" =>
    ref ‘Unset( "fn" ).

Definition lazy٠return : val :=
  fun: "res" =>
    ref ‘Set( "res" ).

Definition lazy٠is_set : val :=
  fun: "t" =>
    match: !"t" with
    | Set <> =>
        true
    |_ =>
        false
    end.

Definition lazy٠is_unset : val :=
  fun: "t" =>
    ~ lazy٠is_set "t".

Definition lazy٠get : val :=
  rec: "get" "t" =>
    match: !"t" with
    | Set "res" =>
        "res"
    | Setting "mtx" =>
        mutex٠synchronize "mtx" ;;
        "get" "t"
    | Unset "fn" as "state" =>
        let: "mtx" := mutex٠create_lock () in
        if: CAS "t".[contents] "state" ‘Setting( "mtx" ) then (
          let: "res" := "fn" () in
          "t" <- ‘Set( "res" ) ;;
          mutex٠unlock "mtx" ;;
          "res"
        ) else (
          mutex٠unlock "mtx" ;;
          "get" "t"
        )
    end.
