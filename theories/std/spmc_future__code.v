From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo Require Import
  mutex
  condition.
From zoo.std Require Import
  spmc_future__types.
From zoo Require Import
  options.

Definition spmc_future_create : val :=
  fun: <> =>
    { §None, mutex_create (), condition_create () }.

Definition spmc_future_set : val :=
  fun: "t" "v" =>
    mutex_protect "t".{mutex} (fun: <> => "t" <-{result} ‘Some( "v" )) ;;
    condition_notify_all "t".{condition}.

Definition spmc_future_try_get : val :=
  fun: "t" =>
    "t".{result}.

Definition spmc_future_get : val :=
  fun: "t" =>
    match: spmc_future_try_get "t" with
    | Some "v" =>
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

Definition spmc_future_is_set : val :=
  fun: "t" =>
    match: spmc_future_try_get "t" with
    | None =>
        #false
    | Some <> =>
        #true
    end.
