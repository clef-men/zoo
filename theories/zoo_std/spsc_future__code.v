From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  condition
  mutex.
From zoo_std Require Import
  spsc_future__types.
From zoo Require Import
  options.

Definition spsc_future_create : val :=
  fun: <> =>
    { §None, mutex_create (), condition_create () }.

Definition spsc_future_set : val :=
  fun: "t" "v" =>
    mutex_protect "t".{mutex} (fun: <> => "t" <-{result} ‘Some( "v" )) ;;
    condition_notify "t".{condition}.

Definition spsc_future_try_get : val :=
  fun: "t" =>
    "t".{result}.

Definition spsc_future_get : val :=
  fun: "t" =>
    match: spsc_future_try_get "t" with
    | Some "v" =>
        mutex_synchronize "t".{mutex} ;;
        "v"
    | None =>
        let: "mtx" := "t".{mutex} in
        let: "cond" := "t".{condition} in
        mutex_protect
          "mtx"
          (fun: <> =>
             condition_wait_while
               "cond"
               "mtx"
               (fun: <> => "t".{result} == §None)) ;;
        match: "t".{result} with
        | Some "v" =>
            "v"
        | None =>
            Fail
        end
    end.

Definition spsc_future_is_set : val :=
  fun: "t" =>
    spsc_future_try_get "t" != §None.
