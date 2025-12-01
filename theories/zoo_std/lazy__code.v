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

Definition lazy_make : val :=
  fun: "fn" =>
    ref ‘Unset( "fn" ).

Definition lazy_return : val :=
  fun: "res" =>
    ref ‘Set( "res" ).

Definition lazy_is_set : val :=
  fun: "t" =>
    match: !"t" with
    | Set <> =>
        #true
    |_ =>
        #false
    end.

Definition lazy_is_unset : val :=
  fun: "t" =>
    ~ lazy_is_set "t".

Definition lazy_get : val :=
  rec: "get" "t" =>
    match: !"t" with
    | Set "res" =>
        "res"
    | Setting "mtx" =>
        mutex_synchronize "mtx" ;;
        "get" "t"
    | Unset "fn" as "state" =>
        let: "mtx" := mutex_create_lock () in
        if: CAS "t".[contents] "state" ‘Setting( "mtx" ) then (
          let: "res" := "fn" () in
          "t" <- ‘Set( "res" ) ;;
          mutex_unlock "mtx" ;;
          "res"
        ) else (
          mutex_unlock "mtx" ;;
          "get" "t"
        )
    end.
