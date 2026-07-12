Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.condition.
Require Import zoo_std.mutex.
Require Import zoo_parabs.waiter__types.
Require Import zoo.options.

Definition waiter٠create : val :=
  fun: <> =>
    { mutex٠create (), condition٠create (), false }.

Definition waiter٠notify : val :=
  fun: "t" =>
    mutex٠lock "t".{mutex} ;;
    if: "t".{flag} then (
      mutex٠unlock "t".{mutex} ;;
      false
    ) else (
      "t" <-{flag} true ;;
      mutex٠unlock "t".{mutex} ;;
      condition٠notify "t".{condition} ;;
      true
    ).

Definition waiter٠prepare_wait : val :=
  fun: "t" =>
    mutex٠protect "t".{mutex} (fun: <> => "t" <-{flag} false).

Definition waiter٠cancel_wait : val :=
  fun: "t" =>
    mutex٠protect "t".{mutex}
      (fun: <> =>
         if: "t".{flag} then (
           false
         ) else (
           "t" <-{flag} true ;;
           true
         )).

Definition waiter٠commit_wait : val :=
  fun: "t" =>
    mutex٠protect "t".{mutex}
      (fun: <> =>
         condition٠wait_until
           "t".{condition}
           "t".{mutex}
           (fun: <> => "t".{flag})).
